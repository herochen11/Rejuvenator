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
flash_size_t LowCleanBlockCnt;
flash_size_t HighCleanBlockCnt;
flash_size_t CleanBlockCnt;
flash_size_t BeginOfBlockListOffset[MAX_ERASE_CNT+1] = {0};		// The begin offset of "erase count" in the RejuBlockList.
flash_size_t EndOfBlockListOffset[MAX_ERASE_CNT+1] = {0};	    // The end offset of "erase count" in the RejuBlockList.
flash_size_t OffsetInBlockList[MAXBLOCK] = {0};					//The offset of "BlockID" in the RejuBlockList. 
flash_size_t RejuBlockList[MAXBLOCK];		
flash_size_t HighActiveBlockPtr, LowActiveBlockPtr;
flash_size_t HighActivePagePtr, LowActivePagePtr;

/*
	Second Chance LRU
*/
int FTLIsHotPage(flash_size_t addr){
	assert(addr > 0);
	return 1;
}

// assume pba1 and pba2 are both byte addr. pba is physical block address.
void copyPage(flash_size_t pba, flash_size_t dst_block,flash_size_t dst_page){
	flash_size_t src_block = pba/PAGE_PER_BLOCK; 
	flash_size_t src_page =  (pba % PAGE_PER_BLOCK)/BYTE_PER_PAGE;
	FlashMemory[dst_block][dst_page] = FlashMemory[src_block][src_page];
}

int LBAtoPBA(flash_size_t lba){
	return PageMappingTable[lba];
}

int FTLIsValidPage(flash_size_t pba){
	flash_size_t blockId = pba/PAGE_PER_BLOCK; 
	flash_size_t offset =  (pba % PAGE_PER_BLOCK)/BYTE_PER_PAGE;
	if(FlashMemory[blockId][offset] != INVALID && FlashMemory[blockId][offset] != CLEAN)
		return 1;
	else 
		return 0;
}

// invalidate page p
// its block = p/PAGE_PER_BLOCk/BYTE_PER_PAGE
// update invalid page of block
void FTLInvalidatePage(flash_size_t pba){
	flash_size_t block = pba/PAGE_PER_BLOCK; 
	flash_size_t page =  (pba % PAGE_PER_BLOCK)/BYTE_PER_PAGE;
	FlashMemory[block][page] = INVALID;	
}

void FTLValidatePage(flash_size_t block, flash_size_t page){
	FlashMemory[block][page] = block;	
}

void FTLUpdateActivePtr(){
	// update LowActivePtr
	LowActiveBlockPtr = LowFreeBlockList[LowFreeBlockListHead];
	if( LowActivePagePtr >= PAGE_PER_BLOCK )
	{
		LowActivePagePtr = 0;
		LowFreeBlockListHead++;
		if(LowFreeBlockListHead < MAXBLOCK)
		{
			LowActiveBlockPtr = LowFreeBlockList[LowFreeBlockListHead];
		}
		else
		{	
			LowFreeBlockListHead = 0;
			LowActiveBlockPtr = LowFreeBlockList[LowFreeBlockListHead];
		}

	}

	// update HighActivePtr
	if( MaxWear <= M )  //This condition means all blocks are in lower numbered list
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
			if(HighFreeBlockListHead < MAXBLOCK)
			{
				HighActiveBlockPtr = HighFreeBlockList[HighFreeBlockListHead];
			}
			else
			{	
				HighFreeBlockListHead = 0;
				HighActiveBlockPtr = HighFreeBlockList[HighFreeBlockListHead];
			}

		}

	}
}

// update Page mapping table, if PMT entry (lba, pba1) => (bla, pba2)
void FTLUpdatePageTable(flash_size_t pba, flash_size_t new_block, flash_size_t new_page){
	flash_size_t old_block = pba/PAGE_PER_BLOCK; 
	flash_size_t old_page =  (pba % PAGE_PER_BLOCK)/BYTE_PER_PAGE;

	PageMappingTable[FlashMemory[old_block][old_page]] = new_block * BLOCK_BYTE_SIZE + new_page * BYTE_PER_PAGE;
	FlashMemory[new_block][new_page] =  FlashMemory[old_block][old_page];
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
	LowCleanBlockCnt = MAXBLOCK;
	HighCleanBlockCnt = 0;
	CleanBlockCnt = MAXBLOCK;
	MinWear = MaxWear = 0;
	M = Tau/2;
}


void PutFreeBlock(flash_size_t BlockID)
{

	if(	BlockEraseCnt[BlockID] > M )
	{	
		if(HighCleanBlockCnt == 0)
		{
			HighFreeBlockListHead = 0;
			HighFreeBlockList[HighFreeBlockListHead] = BlockID;
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
			if( ValidPageCnt[b] < minValidPageCnt && LowFreeBlockList[b] == FBL_NOT_IN_LIST){
				minValidPageCnt = ValidPageCnt[b];
				victimBlock = b;
			}
		}

	assert(victimBlock != -1);

	//live page copy
	flash_size_t physicalOffset = victimBlock*BLOCK_BYTE_SIZE; //physical offset in the memory 
	flash_size_t bOffset = 0; //the offest in the victim block (unit is page)
	for(flash_size_t p=bOffset; p+=BYTE_PER_PAGE; p<bOffset + BLOCK_BYTE_SIZE){
		if( !FTLIsValidPage(p) ) continue;
		FTLUpdateActivePtr();
		if( FTLIsHotPage(p) ){
			copyPage(p, LowActiveBlockPtr, LowActivePagePtr);
			FTLValidatePage(LowActiveBlockPtr, LowActivePagePtr);
			FTLUpdatePageTable(p, LowActiveBlockPtr, LowActivePagePtr);
			LowActivePagePtr++;
		}
		else{
			copyPage(p, HighActiveBlockPtr, HighActivePagePtr);
			FTLValidatePage(HighActiveBlockPtr, HighActivePagePtr);
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
