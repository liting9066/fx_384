#include <stdio.h>
#include <stdlib.h>
#include <memory.h>
#include <assert.h>
#include <time.h>


typedef unsigned short UINT32;
typedef unsigned char UINT8;
typedef unsigned long long UINT64;
typedef long long INT64;
typedef UINT64 tKeccakLane;

#define KeccakReferences
#define maxNrRounds 24
#define reducedRound 3
#define nrLanes 25
#define index(x, y) (((x)%5)+5*((y)%5))
#define KeccakP1600_stateSizeInBytes    200
#define MIN(a, b) ((a) < (b) ? (a) : (b))
#define HASHES_CAP (1<<17)

static tKeccakLane KeccakRoundConstants[maxNrRounds];
static unsigned int KeccakRhoOffsets[nrLanes];

void KeccakP1600_InitializeRoundConstants(void);
void KeccakP1600_InitializeRhoOffsets(void);
static int LFSR86540(UINT8 *LFSR);




/*******  initialization functions ************/


void KeccakP1600_Initialize(void *state)
{
    memset(state, 0, 1600/8);
}

void KeccakP1600_StaticInitialize(void)
{
    if (sizeof(tKeccakLane) != 8) {
        printf("tKeccakLane should be 64-bit wide\n");
        
    }
    KeccakP1600_InitializeRoundConstants();
    KeccakP1600_InitializeRhoOffsets();
}


static int LFSR86540(UINT8 *LFSR)
{
    int result = ((*LFSR) & 0x01) != 0;
    if (((*LFSR) & 0x80) != 0)
    /* Primitive polynomial over GF(2): x^8+x^6+x^5+x^4+1 */
        (*LFSR) = ((*LFSR) << 1) ^ 0x71;
    else
        (*LFSR) <<= 1;
    return result;
}

void KeccakP1600_InitializeRoundConstants(void)
{
    UINT8 LFSRstate = 0x01;
    unsigned int i, j, bitPosition;
    
    for(i=0; i<maxNrRounds; i++) {
        KeccakRoundConstants[i] = 0;
        for(j=0; j<7; j++) {
            bitPosition = (1<<j)-1; /* 2^j-1 */
            if (LFSR86540(&LFSRstate))
                KeccakRoundConstants[i] ^= (tKeccakLane)1<<bitPosition;
        }
    }
}

void KeccakP1600_InitializeRhoOffsets(void)
{
    unsigned int x, y, t, newX, newY;
    
    KeccakRhoOffsets[index(0, 0)] = 0;
    x = 1;
    y = 0;
    for(t=0; t<24; t++) {
        KeccakRhoOffsets[index(x, y)] = ((t+1)*(t+2)/2) % 64;
        newX = (0*x+1*y) % 5;
        newY = (2*x+3*y) % 5;
        x = newX;
        y = newY;
    }
}




/******* 5 operation functions ************/


#define ROL64(a, offset) ((offset != 0) ? ((((tKeccakLane)a) << offset) ^ (((tKeccakLane)a) >> (64-offset))) : a)

static void theta(tKeccakLane *A)
{
    unsigned int x, y;
    tKeccakLane C[5], D[5];
    
    for(x=0; x<5; x++) {
        C[x] = 0;
        for(y=0; y<5; y++)
            C[x] ^= A[index(x, y)];
    }
    for(x=0; x<5; x++)
        D[x] = ROL64(C[(x+1)%5], 1) ^ C[(x+4)%5];
    for(x=0; x<5; x++)
        for(y=0; y<5; y++)
            A[index(x, y)] ^= D[x];
}

static void rho(tKeccakLane *A)
{
    unsigned int x, y;
    
    for(x=0; x<5; x++) for(y=0; y<5; y++)
        A[index(x, y)] = ROL64(A[index(x, y)], KeccakRhoOffsets[index(x, y)]);
}

static void pi(tKeccakLane *A)
{
    unsigned int x, y;
    tKeccakLane tempA[25];
    
    for(x=0; x<5; x++) for(y=0; y<5; y++)
        tempA[index(x, y)] = A[index(x, y)];
    for(x=0; x<5; x++) for(y=0; y<5; y++)
        A[index(0*x+1*y, 2*x+3*y)] = tempA[index(x, y)];
}

static void chi(tKeccakLane *A)
{
    unsigned int x, y;
    tKeccakLane C[5];
    
    for(y=0; y<5; y++) {
        for(x=0; x<5; x++)
            C[x] = A[index(x, y)] ^ ((~A[index(x+1, y)]) & A[index(x+2, y)]);
        for(x=0; x<5; x++)
            A[index(x, y)] = C[x];
    }
}

static void iota(tKeccakLane *A, unsigned int indexRound)
{
    A[index(0, 0)] ^= KeccakRoundConstants[indexRound];
}


void KeccakP1600Round(tKeccakLane *state, unsigned int indexRound)
{

    theta(state);  
    rho(state);
	pi(state);
	/*
	if(indexRound == 1){
	    for(int i = 0; i < 25 ; i++){
	        printf("%016lx\n", state[i]);
	    }
	    printf("\n");
	}
	*/
	chi(state);
	iota(state, indexRound);

}

void KeccakF1600Permute(tKeccakLane *state, unsigned int nRounds){
    for (int n = 0; n < nRounds; n++) {
        KeccakP1600Round(state, n);
    }
}


void getState(tKeccakLane state[25], UINT64 constraints[12], UINT64 guess){
    KeccakP1600_Initialize(state);
    UINT64 value = 0;
    int mapping[12] = {0, 1, 2, 3, 4, 5, 7, 10, 11, 12, 13, 29};
    for(int i = 0 ; i < 12; i++){
        UINT64 w = guess & constraints[i];

        w = (w) ^ (w >> 32);
	    w = (w) ^ (w >> 16);
		w = (w) ^ (w >> 8);
		w = (w) ^ (w >> 4);
		w = (w) ^ (w >> 2);
		w = (w) ^ (w >> 1);
		if(w & (UINT64) 1){
		    value ^= ((UINT64)1L << mapping[i]);
		}        
    }
    
    value ^= guess;
    UINT64 input_diff[25] = {0x0080000000000000, 0x0040000000000000, 0x0               , 0x0, 0x0,
                             0x0080000000000000, 0x0               , 0x0000000000200000, 0x0, 0x0,
                             0x0               , 0x0040000000000000, 0x0000000000200000, 0x0, 0x0,
                             0x0               , 0x0               , 0x0               , 0x0, 0x0,
                             0x0               , 0x0               , 0x0               , 0x0, 0x0};
    for(int i = 0; i < 13; i++){
        UINT64 css = (value >> (4 * i)) & 0xFL;
        for(int j = 0 ; j < 16 ; j++){
            state[i] ^= (css << (4 * j));
        } 
        
        state[i] ^= input_diff[i];
        //printf("%016lx\n", state[i]);
    }
    
    //printf("\n");
    
    

    
}



int main(){
	printf("parse and verify\n");
	tKeccakLane state[25]; 
   
	KeccakP1600_StaticInitialize(); 
	
	int idxs[83] = {0, 18, 20, 24, 38, 40, -1,
             1, 8, 21, 28, 41, 45, 48, -1, 
             2, 6, 9, 22, 42, 49, 100, -1, 
             3, 17, 23, 27, 37, 43, -1,
             4, 17, 24, 37, 44 ,100, -1,
             5, 16, 17, 25, 27, 37, 45, 100, -1,
             7, 16, 20, 27, 36, 47, 100, -1,
             10, 17, 30, 37, 50, -1,
             11, 18, 31, 38, 51, -1,
             12, 16, 17, 27, 32, 37, 100, -1,
             13, 18, 24, 33, 38, 100, -1,
             29, -1};
    UINT64 constraints[12]= {0,0,0,0,0,0,0,0,0,0,0,0};
    int r = 0;
    
    for(int i = 0; i < 83; i++){
        if(idxs[i] != -1 && idxs[i] != 100){
            constraints[r] ^= ((UINT64)1L << idxs[i]);
        }else if(idxs[i] == 100){
            constraints[r] ^= ((UINT64)1L << 63);
        }else{
            r++;
        }
    }
    
    printf("r:%d\n",r);
    for(int i = 0; i < r ; i++){
        printf("%016llx\n", constraints[i]);
    }
    

    UINT64 guess;
	
	
	guess = 0x800800010840c140;

    getState(state, constraints, guess);
    
    printf("init state:\n");
    for(int x = 0; x < 5; x++){
    	for(int y = 0; y < 5; y++){
    		printf("%016llx ", state[x*5+y]);
    	}
    	printf("\n");
    }
    
    
    KeccakF1600Permute(state, 3);
    
    printf("degist:\n");
    for(int x = 0; x < 6; x++){
    	
    	printf("%016llx ", state[x]);
    	
    	printf("\n");
    }    

	guess = 0x8008000185548200;
	

    getState(state, constraints, guess);
    
    printf("init state:\n");
    for(int x = 0; x < 5; x++){
    	for(int y = 0; y < 5; y++){
    		printf("%016llx ", state[x*5+y]);
    	}
    	printf("\n");
    }

    KeccakF1600Permute(state, 3);
    
    printf("degist:\n");
    for(int x = 0; x < 6; x++){
    	
    	printf("%016llx ", state[x]);
    	
    	printf("\n");
    }    


}
