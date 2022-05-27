#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#define FBL_NOT_IN_LIST			(-2)		//* mean this block is not in the free block list
#define MAXBLOCK 				128			// 2^6
#define BYTE_PER_PAGE 			64
#define PAGE_PER_BLOCK 			64
#define DISK_BYTE_SIZE 			(MAXBLOCK*PAGE_PER_BLOCK*BYTE_PER_PAGE) // 512KB
#define BLOCK_BYTE_SIZE 		(PAGE_PER_BLOCK*BYTE_PER_PAGE)			
#define MAX_ERASE_CNT			100
typedef int	 flash_size_t;

char* Memory;



flash_size_t InvalidPageCnt[MAXBLOCK] = {0};	//* store the number of invalid pages in each block
flash_size_t ValidPageCnt[MAXBLOCK] = {0};		//* store the number of valid pages in each block
flash_size_t FreeBlockList[MAXBLOCK] = {-2};	//* the free block list array
flash_size_t CurrentFreeBlockID = -1;			//* Point to current free block ID. If the garbage collection is called, this value will always be -1.

// LPN to PPN, assume 1-to-1 mapping, -1 means no mapping
flash_size_t PageMappingTable[PAGE_PER_BLOCK*MAXBLOCK]	= {-1};	


// rejuvenator block list
flash_size_t Tau = 16;
flash_size_t MinWear = 0;
flash_size_t MaxWear = 16;
flash_size_t LowCleanBlockCnt;
flash_size_t HighCleanBlockCnt;
flash_size_t CleanBlockCnt;
flash_size_t M;
flash_size_t BeginOfBlockListOffset[MAX_ERASE_CNT] = {0};		// if BeginOfBlockListOffset[cnt] > EndOfBlockListOffset[cnt]
flash_size_t EndOfBlockListOffset[MAX_ERASE_CNT] = {0};			// there is no block in cnt.    #cnt : the erase count
flash_size_t OffsetInBlockList[MAXBLOCK] = {0};
flash_size_t EraseCnt[MAXBLOCK] = {0};
flash_size_t RejuBlockList[MAXBLOCK]= {-1}; 
//flash_size_t RejuBlockList[MAX_ERASE_CNT][MAXBLOCK]= {-1}; //the index of RejuBlockList indeicate the erase count

flash_size_t HighActivePtr, LowActivePtr;

// assume p1 and p2 are both byte addr
void copyPage(flash_size_t p1, flash_size_t p2){
	for(flash_size_t i=0; i<BYTE_PER_PAGE; ++i){
		Memory[p2+i] = Memory[p1+i];
	}
}

int FTLIsHotPage(flash_size_t addr){
	assert(addr > 0);
	return 1;
}

int LBAtoPBA(){}

int PBAtoLBA(){}

int FTLIsValidPage(flash_size_t p){
	return 1;
}

// update HighActivePtr and LowActivePtr
    void FTLUpdateActivePtr(){

}


// invalidate page p
// its block = p/PAGE_PER_BLOCk/BYTE_PER_PAGE
// update invalid page of block
void FTLInvalidatePage(flash_size_t p){
	
}

void FTLValidatePage(flash_size_t p){

}

// update Page mapping table, if PMT entry (e, p1) => (e, p2)
void FTLUpdatePageTable(flash_size_t p1, flash_size_t p2){

}

int FTLIsValidPage(flash_size_t p){
	return 1;
}


void RejuInitBlockList(){
	// put all blocks in block list with erase_cnt = 0
	for(flash_size_t i=0; i<MAXBLOCK; ++i){
        RejuBlockList[i] = i;
		//RejuBlockList[0][i] = i;
	}
 
	EndOfBlockListOffset[0] = MAXBLOCK-1;
	for(flash_size_t i=1; i<MAX_ERASE_CNT; ++i){
		BeginOfBlockListOffset[i] = MAXBLOCK;
		EndOfBlockListOffset[i] = MAXBLOCK-1;
	}
	LowCleanBlockCnt = MAXBLOCK;
	HighCleanBlockCnt = 0;
	CleanBlockCnt = MAXBLOCK;
	M = (MaxWear+MinWear)/2;
}

//* ****************************************************************
//* Erase one block
//* ****************************************************************
void FTLEraseOneBlock(flash_size_t BlockID){
	assert(BlockID < MAXBLOCK);
	// physically erase this Block
	flash_size_t bOffset = BlockID*BLOCK_BYTE_SIZE;
	for(flash_size_t i=bOffset; i<BLOCK_BYTE_SIZE; ++i)
		Memory[i] = 0;

	// then ...

	InvalidPageCnt[BlockID] = 0;
	ValidPageCnt[BlockID] = 0;
	flash_size_t eraseCnt = EraseCnt[BlockID];
	if(eraseCnt == MAX_ERASE_CNT) return;

	flash_size_t pos = OffsetInBlockList[BlockID];
	flash_size_t end = EndOfBlockListOffset[eraseCnt]; // end offset
	assert(pos <= end);
	flash_size_t swappedBlock = RejuBlockList[end];
	RejuBlockList[end] = BlockID;
	RejuBlockList[pos] = swappedBlock;
	++EraseCnt[BlockID];
	assert(EndOfBlockListOffset[eraseCnt] > 0);
	--EndOfBlockListOffset[eraseCnt];
	--BeginOfBlockListOffset[eraseCnt+1];

	if(eraseCnt+1 >= M)
		++HighCleanBlockCnt;
	else	
		++LowCleanBlockCnt;
	++ CleanBlockCnt;
	//updateRejuParameter
}

//# ****************************************************************
//# Do garbage collection to reclaim one more free block if there is no free block in the free block list
//# dynamic wear leveling: using cost-benefit strategy for its GC->
//# (free page=0, live page=-1, dead page = 1) while the sum over every page is larger than 0, erase the block.
//# Always reclaim the first block that has the maximal number of invalid pages
//# ****************************************************************
void FTLGarbageCollection()
{
	// find victim block with maximum cleaning efficiency in the lower numbered list 
	// that is, the block with minimum valid page
	flash_size_t minValidPageCnt = PAGE_PER_BLOCK+1;
	flash_size_t victimBlock = -1;
	for(flash_size_t i=0; i<M; ++i){  
		flash_size_t j = BeginOfBlockListOffset[i];
		flash_size_t end = EndOfBlockListOffset[i];
		if(end==MAXBLOCK) continue; // empty list in RejBlockList
		for(; j <= end; ++j){
			flash_size_t b = RejuBlockList[j];
			if( ValidPageCnt[b] < minValidPageCnt ){
				minValidPageCnt = ValidPageCnt[b];
				victimBlock = b;
			}
		}
	}

	//NOTE  clean block can be victim block ?
	if(victimBlock==-1) return;

	flash_size_t bOffset = victimBlock*BLOCK_BYTE_SIZE;
	for(flash_size_t p=bOffset; p+=BYTE_PER_PAGE; p<bOffset + BLOCK_BYTE_SIZE){
		if( ! FTLIsValidPage(p) ) continue;
		FTLUpdateActivePtr();
		if( FTLIsHotPage(p) ){
			copyPage(p, LowActivePtr);
			FTLValidatePage(LowActivePtr);
			//update 
			// NOTE How to check which LPN map to p
		}
		else{
			copyPage(p, HighActivePtr);
			FTLValidatePage(HighActivePtr);
			//update 
		}
		
		FTLInvalidatePage(p);
		
	}

	//erase block
	++LowCleanBlockCnt;
	++CleanBlockCnt;

}



int main()
{
	Memory = (char*) malloc( DISK_BYTE_SIZE * sizeof(char) );
	memset(Memory, 0, DISK_BYTE_SIZE);
	return 0;
}
