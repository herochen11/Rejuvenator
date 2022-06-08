#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#define CLEAN					(-1)
#define INVALID					(-2)
#define FBL_NOT_IN_LIST			(-3)		//* mean this block is not in the free block list
#define MAXBLOCK 				128			// 2^6
#define BYTE_PER_PAGE 			64
#define PAGE_PER_BLOCK 			64
#define DISK_BYTE_SIZE 			(MAXBLOCK*PAGE_PER_BLOCK*BYTE_PER_PAGE) // 512KB
#define BLOCK_BYTE_SIZE 		(PAGE_PER_BLOCK*BYTE_PER_PAGE)			
#define MAX_ERASE_CNT			100

#define SC_CACHE_SIZE			100

typedef int	 flash_size_t;

/*
	flash memory
*/ 
flash_size_t InvalidPageCnt[MAXBLOCK];		//* the number of invalid pages in each block
flash_size_t ValidPageCnt[MAXBLOCK];		//* the number of valid pages in each block
flash_size_t CleanPageCnt[MAXBLOCK];		//* the number of clean pages in each block
flash_size_t BlockEraseCnt[MAXBLOCK];		//* the number of earse count of each block
// flash_size_t CurrentFreeBlockID;			//* Point to current free block ID. If the garbage collection is called, this value will always be -1.
flash_size_t **FlashMemory;  //* -1: clean, -3: invalid, other : the LBA is stored in this page
flash_size_t PageMappingTable[PAGE_PER_BLOCK*MAXBLOCK];	 //* LBA to PBA, assume 1-to-1 mapping, -1 means no mapping
flash_size_t LowFreeBlockList[MAXBLOCK];		//* the free block list array
flash_size_t HighFreeBlockList[MAXBLOCK];		//* the free block list array  	
flash_size_t LowFreeBlockListHead;
flash_size_t LowFreeBlockListTail;
flash_size_t HighFreeBlockListHead;
flash_size_t HighFreeBlockListTail;	


/*
	Rejuvenator block list
*/ 
flash_size_t Tau = 16;
flash_size_t M;
flash_size_t MinWear = 0;
flash_size_t MaxWear = 0;
flash_size_t LowCleanBlockCnt, HighCleanBlockCnt;
flash_size_t HighBlockCnt, LowBlockCnt;
flash_size_t CleanBlockCnt;
flash_size_t BeginOfBlockListOffset[MAX_ERASE_CNT+1] = {0};		// The begin offset of "erase count" in the RejuBlockList.
flash_size_t EndOfBlockListOffset[MAX_ERASE_CNT+1] = {0};	    // The end offset of "erase count" in the RejuBlockList.
flash_size_t OffsetInBlockList[MAXBLOCK] = {0};					//The offset of "BlockID" in the RejuBlockList. 
flash_size_t RejuBlockList[MAXBLOCK];		
flash_size_t HighActiveBlockPtr, LowActiveBlockPtr;
flash_size_t HighActivePagePtr, LowActivePagePtr;



/***************************************/	
/*		Beg of Second Chance Cache 	   */
/***************************************/

/*@ predicate Unique{L}(int *a, integer size) =
  @ \forall integer i,j; 0 <= i < j < size && a[i]!=-1 && a[j]!=-1 ==> a[i] != a[j] ;
  @*/

flash_size_t Cache[SC_CACHE_SIZE] 		= {-1};
flash_size_t ChanceArr[SC_CACHE_SIZE] 	= {0};
flash_size_t ChancePtr = 0; // index in ChanceArr
flash_size_t CacheSize = SC_CACHE_SIZE;

/*@ requires 0 < CacheSize < 2147483645 && page >= 0;
    requires \valid(  Cache+(0..CacheSize-1) );
    requires Unique(Cache, CacheSize);
    requires \valid(  ChanceArr+(0..CacheSize-1) );
    assigns ChanceArr[0..CacheSize-1];
    ensures Unique(Cache, size);
*/
// update ChanceArr if page exist, return if page exist
int find_and_update(flash_size_t page)
{ 
	int i;
    /*@loop invariant 0 <= i <= CacheSize;
       loop invariant \forall integer j; j <= CacheSize-1 ==> ChanceArr[j]==0 ^^ ChanceArr[j]==1;
       loop assigns i;
     */
    for (i=0; i<CacheSize; i++) {
        if (Cache[i]==page) {
            ChanceArr[i] = 1;
            return 1;
        }
    }
    return 0;
}

/*@ requires 0 < CacheSize < 2147483645 && page >= 0;
    requires CacheSize-1 >= ChancePtr >= 0;
    requires \valid( Cache+(0..Cachesize-1) );
    requires Unique(Cache,Cachesize);
    assigns Cache[0..CacheSize-1];
    assigns ChancePtr[0..CacheSize-1];
   
    ensures \exists integer i;  Cache[i]==page; 
    ensures Unique(Cache,CacheSize);
    ensures 0 <= ChancePtr <= CacheSize-1; 	
*/
// find an entry of no chance, replace it with page, update ChanceArr
void replace_and_update(flash_size_t page)
{
	int idx = ChancePtr;
	/*@ loop assigns Cache[0..CacheSize-1];
        loop assigns idx;
        loop assigns ChanceArr[0..CacheSize-1];
        loop invariant 0 <= idx <= CacheSize-1;
	*/
	while (1) {
	    if (ChanceArr[idx]==0) {
            Cache[idx] = page;
            ChancePtr = (idx+1)%CacheSize;
			return;
        }
        ChanceArr[idx] = 0;
        ChancePtr = (idx+1)%CacheSize;
    }
}


// called when referencing page
void updateCache(flash_size_t page){
	int exist = find_and_update(page);
	if( !exist )
		replace_and_update(page);
}

/***************************************/	
/*		End of Second Chance Cache 	   */
/***************************************/


// currently brute force, traverse cache once
int FTLIsHotPage(flash_size_t page){
	assert(page > 0);
	for(int i=0; i<CacheSize; ++i){
		if(Cache[i]==page) 
			return 1;
	}
	return 0;
}

int LBAtoPBA(flash_size_t lba){
	return PageMappingTable[lba];
}

//* copy the content of page from "pba" to destination block and page.
//******* Update FlashMemory ******* //
void copyPage(flash_size_t pba, flash_size_t dst_block,flash_size_t dst_page){
	flash_size_t src_block = pba/PAGE_PER_BLOCK; 
	flash_size_t src_page =  (pba % PAGE_PER_BLOCK)/BYTE_PER_PAGE;
	FlashMemory[dst_block][dst_page] = FlashMemory[src_block][src_page];
}

int FTLIsValidPage(flash_size_t pba){
	flash_size_t blockId = pba/PAGE_PER_BLOCK; 
	flash_size_t offset =  (pba % PAGE_PER_BLOCK)/BYTE_PER_PAGE;
	if(FlashMemory[blockId][offset] != INVALID && FlashMemory[blockId][offset] != CLEAN)
		return 1;
	else 
		return 0;
}

//* invalidate page p
//******* update FlashMemory ******* //
void FTLInvalidatePage(flash_size_t pba){
	flash_size_t block = pba/PAGE_PER_BLOCK; 
	flash_size_t page =  (pba % PAGE_PER_BLOCK)/BYTE_PER_PAGE;
	FlashMemory[block][page] = INVALID;	
}

//******** Update LowActiveBlockPtr, LowActivePagePtr, HighActiveBlockPtr, HighActivePagePtr, LowFreeBlockListHead, HighFreeBlockListHead *******//
// pre-condition : 
// 	LowActivePagePtr < PAGE_PER_BLOCK or LowCleanBlockCnt > 1;
//  LowFreeBlockListHead < MAXBLOCK && LowFreeBlockListTail < MAXBLOCK;
//  LowActiveBlockPtr == LowFreeBlockList[LowFreeBlockListHead];
//  \assigns LowActiveBlockPtr, LowFreeBlockListHead, LowCleanBlockCnt, LowActivePagePtr;
//
// post-condition:
//	case1 \old(LowActivePagePtr) >= PAGE_PER_BLOCK  ==> 
// 		LowActivePagePtr==0 && LowCleanBlockCnt==\old(LowCleanBlockCnt)-1
// 		case1.1 \old(LowFreeBlockListHead)+1 >= MAXBLOCK ==> LowFreeBlockListHead==0;
// 		case1.2 \old(LowFreeBlockListHead)+1 < MAXBLOCK ==> LowFreeBlockListHead==\old(LowFreeBlockListHead)+1;
//  case2 \old(LowActivePagePtr) < PAGE_PER_BLOCK  ==> 
// 		LowActivePagePtr==\old(LowActivePagePtr) && LowCleanBlockCnt==\old(LowCleanBlockCnt) &&
// 		LowFreeBlockListHead==\old(LowFreeBlockListHead) 
// 
//  LowActiveBlockPtr == LowFreeBlockList[LowFreeBLockListHead] ;
//  
void FTLUpdateActivePtr(){
	// update LowActivePtr
	// LowActiveBlockPtr = LowFreeBlockList[LowFreeBlockListHead];
	if( LowActivePagePtr >= PAGE_PER_BLOCK )
	{
		LowActivePagePtr = 0;
		LowFreeBlockListHead++;
		LowCleanBlockCnt--;
		//FIXME
		// case1 :      head      tail
		//		   [0 0 0 1 1 1 1 1 0 0 0] 			
		//
		// case2 : 	  tail 			head
		//		   [1 1 0 0 0 0 0 0 0 1 1]
		if(LowFreeBlockListHead > LowFreeBlockListTail && 
		   LowFreeBlockListHead >= MAXBLOCK){
			LowFreeBlockListHead = 0;
		}
		LowActiveBlockPtr = LowFreeBlockList[LowFreeBlockListHead];


		// if(LowFreeBlockListHead < MAXBLOCK && LowFreeBlockListHead <= LowFreeBlockListTail) 
		// {
		// 	LowActiveBlockPtr = LowFreeBlockList[LowFreeBlockListHead];
		// }
		// else if (LowFreeBlockListHead >= MAXBLOCK && LowFreeBlockListHead <= LowFreeBlockListTail)
		// {	
		// 	LowFreeBlockListHead = 0;
		// 	LowActiveBlockPtr = LowFreeBlockList[LowFreeBlockListHead];
		// }
		// else // Head > Tail
		// {
		// 	printf("Error: No free block in lowered numbered list\n");
		// 	exit(1);
		// }

	}

	// update HighActivePtr
	if( MaxWear <= MinWear + M )  //This condition means all blocks are in lower numbered list
	{
		HighActiveBlockPtr = LowActiveBlockPtr;
		HighActivePagePtr = LowActivePagePtr;
	}
	else
	{ 
		HighActiveBlockPtr = HighFreeBlockList[HighFreeBlockListHead];
		if( HighActivePagePtr >= PAGE_PER_BLOCK )
		{
			HighActivePagePtr = 0;
			HighFreeBlockListHead++;
			HighCleanBlockCnt--;

			if(HighFreeBlockListHead > HighFreeBlockListTail && 
			   HighFreeBlockListHead >= MAXBLOCK){
				HighFreeBlockListHead = 0;
			}
			HighActiveBlockPtr = HighFreeBlockList[HighFreeBlockListHead];

			// if(HighFreeBlockListHead < MAXBLOCK && HighFreeBlockListHead <= HighFreeBlockListTail)
			// {
			// 	HighActiveBlockPtr = HighFreeBlockList[HighFreeBlockListHead];
			// }
			// else if(HighFreeBlockListHead >= MAXBLOCK && HighFreeBlockListHead <= HighFreeBlockListTail)
			// {	
			// 	HighFreeBlockListHead = 0;
			// 	HighActiveBlockPtr = HighFreeBlockList[HighFreeBlockListHead];
			// }
			// else
			// {
			// 	printf("Error: No free block in higher numbered list\n");
			// 	exit(1);
			// }

		}

	}
}

// update Page mapping table, if PMT entry (lba, pba1) => (bla, pba2)
//******* Update PageMappintTable, FlashMemory *******//
void FTLUpdatePageTable(flash_size_t pba, flash_size_t new_block, flash_size_t new_page){
	flash_size_t old_block = pba/PAGE_PER_BLOCK; 
	flash_size_t old_page =  (pba % PAGE_PER_BLOCK)/BYTE_PER_PAGE;

	PageMappingTable[FlashMemory[old_block][old_page]] = new_block * BLOCK_BYTE_SIZE + new_page * BYTE_PER_PAGE;
	//FlashMemory[new_block][new_page] =  FlashMemory[old_block][old_page];
}

void UpdateRejuParameter(){
	//TODO
	//update Tau
	M = Tau/2;
}

void InitFlashMemory(){

	FlashMemory = (flash_size_t**) malloc(sizeof(flash_size_t*)*MAXBLOCK);
	for( int i=0; i < MAXBLOCK; i++)
	{
		FlashMemory[i] = (flash_size_t *)malloc(sizeof(flash_size_t)*PAGE_PER_BLOCK);
		memset(FlashMemory[i],CLEAN,sizeof(flash_size_t)*PAGE_PER_BLOCK);	//* initialize the content of each page: means there is nothing in any page initially.
	}

	memset(PageMappingTable, -1, sizeof(PageMappingTable));
	memset(ValidPageCnt, 0, sizeof(ValidPageCnt));
	memset(InvalidPageCnt, 0, sizeof(InvalidPageCnt));
	memset(BlockEraseCnt, 0, sizeof(BlockEraseCnt));

	for(flash_size_t i=0; i<MAXBLOCK; i++){
		CleanPageCnt[i] = PAGE_PER_BLOCK;
		LowFreeBlockList[i] = i;
		HighFreeBlockList[i] = FBL_NOT_IN_LIST;
	}
	LowFreeBlockListHead = 0;
	LowFreeBlockListTail = MAXBLOCK-1;
	HighFreeBlockListHead = -1;
	HighFreeBlockListTail = -1;
	//CurrentFreeBlockID = 0;
}

void InitRejuBlockList(){
	// put all blocks in block list with erase_cnt = 0
	for(flash_size_t i=0; i<MAXBLOCK; ++i){
        RejuBlockList[i] = i;
		OffsetInBlockList[i] = i; 
	}
	
	// if BeginOfBlockListOffset[cnt] > EndOfBlockListOffset[cnt]
	// there is no block in cnt.    #cnt : the erase count
	BeginOfBlockListOffset[0] = 0;
	EndOfBlockListOffset[0] = MAXBLOCK-1;
	for(flash_size_t i=1; i<MAX_ERASE_CNT; ++i){ 
		BeginOfBlockListOffset[i] = MAXBLOCK;
		EndOfBlockListOffset[i] = MAXBLOCK-1;
	}
	LowCleanBlockCnt = LowBlockCnt = MAXBLOCK;
	HighCleanBlockCnt = HighBlockCnt = 0;
	CleanBlockCnt = MAXBLOCK;
	MinWear = MaxWear = 0;
	M = Tau/2;
}

//update FreeBlockList
void PutFreeBlock(flash_size_t BlockID)
{

	if(	BlockEraseCnt[BlockID] > M )
	{	
		if(HighBlockCnt == 0)  //the first block that put into the high numbered list
		{
			HighFreeBlockListHead = 0;
		}
		
		if( (HighFreeBlockListTail + 1) == MAXBLOCK)
			HighFreeBlockListTail = 0;
		else 
			HighFreeBlockListTail++;
		HighFreeBlockList[HighFreeBlockListTail] = BlockID;
	}
	else
	{	
		if( (LowFreeBlockListTail + 1) == MAXBLOCK)
			LowFreeBlockListTail = 0;
		else 
			LowFreeBlockListTail++;
		LowFreeBlockList[LowFreeBlockListTail] = BlockID;
	} 
}

void FTLEraseOneBlock(flash_size_t BlockID){
	assert(BlockID < MAXBLOCK);
	// physically erase this Block
	for(flash_size_t i=0; i<PAGE_PER_BLOCK; ++i)
		FlashMemory[BlockID][i] = CLEAN;
	
	InvalidPageCnt[BlockID] = 0;
	ValidPageCnt[BlockID] = 0;
	CleanPageCnt[BlockID] = PAGE_PER_BLOCK;
	flash_size_t eraseCnt = BlockEraseCnt[BlockID];
	if(eraseCnt == MAX_ERASE_CNT) return;

	//move the erase block to head of next erase count list
	flash_size_t pos = OffsetInBlockList[BlockID]; 		//the offset of the block in the RejuBlockList
	flash_size_t end = EndOfBlockListOffset[eraseCnt];  // the end offset of the "erasecnt" in the RejuBlockList
	assert(pos <= end);
	flash_size_t swappedBlock = RejuBlockList[end];
	RejuBlockList[end] = BlockID;
	RejuBlockList[pos] = swappedBlock;

	//update erase count and BlockListOffset
	++BlockEraseCnt[BlockID];			
	--EndOfBlockListOffset[eraseCnt];		
	--BeginOfBlockListOffset[eraseCnt+1];

	//put the block into free block list..
	PutFreeBlock(BlockID);
	
	//update minwear and maxwear
	if(BlockEraseCnt[BlockID]  > MaxWear) MaxWear = eraseCnt;
	if(EndOfBlockListOffset[MinWear] == -1) MinWear++;
	assert((MaxWear - MinWear) <= Tau );

	if(eraseCnt+1 > M)
		++HighCleanBlockCnt;
	else	
		++LowCleanBlockCnt;	
	
	++ CleanBlockCnt;
	
}


void FTLGarbageCollection(){
	// find victim block with maximum cleaning efficiency in the lower numbered list
	flash_size_t minValidPageCnt = PAGE_PER_BLOCK+1;
	flash_size_t victimBlock = -1;
	for(flash_size_t i=MinWear; i<M; ++i){  //min_wear to min_wear + M  
		flash_size_t begin = BeginOfBlockListOffset[i];
		flash_size_t end = EndOfBlockListOffset[i];
		if(end==MAXBLOCK) continue; // empty list in RejBlockList
		for(; begin <= end; ++begin){
			flash_size_t b = RejuBlockList[begin];
			if( ValidPageCnt[b] < minValidPageCnt /*&& LowFreeBlockList[b] == FBL_NOT_IN_LIST*/){ //TODO: check the block is not in free block list
				minValidPageCnt = ValidPageCnt[b];
				victimBlock = b;
			}
		}
	}
	assert(victimBlock != -1);

	//live page copy
	flash_size_t physicalOffset = victimBlock*BLOCK_BYTE_SIZE; //physical offset in the memory 
	flash_size_t bOffset = physicalOffset; //the offest in the victim block (unit is page)
	for(flash_size_t p=bOffset; p+=BYTE_PER_PAGE; p<bOffset + BLOCK_BYTE_SIZE){
		if( !FTLIsValidPage(p) ) continue;
		FTLUpdateActivePtr(); 
		if( FTLIsHotPage(p) ){
			copyPage(p, LowActiveBlockPtr, LowActivePagePtr);
			FTLUpdatePageTable(p, LowActiveBlockPtr, LowActivePagePtr);
			LowActivePagePtr++;
		}
		else{
			copyPage(p, HighActiveBlockPtr, HighActivePagePtr);
			FTLUpdatePageTable(p, HighActiveBlockPtr, HighActivePagePtr);
			HighActivePagePtr++;
		}	
		FTLInvalidatePage(p);	
	}

	//erase block
	FTLEraseOneBlock(victimBlock);
	UpdateRejuParameter();

}

int main()
{
	InitFlashMemory();
	InitRejuBlockList();
}
