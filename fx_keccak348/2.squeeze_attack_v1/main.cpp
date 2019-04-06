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

/****************** memory for hashes *****************************/

#define PREC -1
#define SUCC 1
#define EQUAL 0
#define CHECK_EQ(a, b) {if (a != b) {printf("EQ does not hold!\n"); abort();}}
#define CHECK_NN(p) {if (p == NULL) { printf("Found null pointer!\n"); abort(); }}

#define CHECK_GE(a, b) {if (a < b) {printf("GE does not hold!\n"); abort();}}
#define CHECK_GT(a, b) {if (a <= b) {printf("GT does not hold!\n"); abort();}}

#define CHECK_LE(a, b) {if (a > b) {printf("LE does not hold!\n"); abort();}}
#define CHECK_LT(a, b) {if (a >= b) {printf("LT does not hold!\n"); abort();}}
#define CHECK_NE(a, b) {if (a == b) {printf("NE does not hold!\n"); abort();}}


struct output_t{
    UINT64 guess;
    tKeccakLane state[6];    
};

struct hashes_t{
    int block_len;
    output_t *hashes;

};

void hashes_calloc(int hashes_idx, hashes_t* hashes){
    hashes[hashes_idx].block_len = 0;
    hashes[hashes_idx].hashes = (output_t*) calloc (HASHES_CAP, sizeof (output_t));
}



void hashes_realloc(int hashes_idx, hashes_t* hashes, int cap){

    hashes[hashes_idx].block_len = 0;
    hashes[hashes_idx].hashes = (output_t*) realloc (hashes[hashes_idx].hashes, cap * sizeof (output_t));
}


void print_hashes(int hashes_idx, hashes_t* hashes){
    printf("hashes_idx:%d\n", hashes_idx);
    //hashes_t hash_block = hashes[hashes_idx];
    int len = hashes[hashes_idx].block_len;
    printf("block_len:%d\n",len);
    for(int i = 0; i < len; i++){
        //output_t output = hashes[hashes_idx].hashes[i];
        printf("%d. guess:%016llx\n", i, hashes[hashes_idx].hashes[i].guess);
        printf("%016llx %016llx %016llx %06llx %016llx %016llx\n\n", hashes[hashes_idx].hashes[i].state[0], hashes[hashes_idx].hashes[i].state[1], hashes[hashes_idx].hashes[i].state[2], hashes[hashes_idx].hashes[i].state[3], hashes[hashes_idx].hashes[i].state[4], hashes[hashes_idx].hashes[i].state[5]);
    }
    
}


void output_add(int hashes_idx, int output_idx, hashes_t* hashes, UINT64 guess, tKeccakLane state[25]){
    //printf("hashes_idx:%d\n",hashes_idx);
    //printf("output_idx:%d\n", output_idx);
    //hashes_t hash_block = hashes[hashes_idx];
    //output_t output = hashes[hashes_idx].hashes[output_idx];
    hashes[hashes_idx].block_len ++;
    //printf("block_len:%d\n", hashes[hashes_idx].block_len);
    hashes[hashes_idx].hashes[output_idx].guess = guess;
    for(int i = 0; i < 6; i++){
        hashes[hashes_idx].hashes[output_idx].state[i] = state[i];
        //printf("%016llx %016llx %016llx %06llx %016llx %016llx\n\n", state[0], state[1], state[2], state[3], state[4], state[5]);
    }
    

}

static inline int hash_compare(output_t *tempA, const UINT64 a, output_t *tempB, const UINT64 b){

    CHECK_NN(tempA)
    CHECK_NN(tempB)
    CHECK_GE(a, 0)
    CHECK_GE(b, 0)
    //CHECK_NE(a, b)
	for(int i = 0; i < 6; i ++){
		if(tempA[a].state[i] < tempB[b].state[i]){
			
			return PREC;
		}
		if(tempA[a].state[i] > tempB[b].state[i]){
			
			return SUCC;
		}
	
	}
	printf("find collisions!\nguess1:%016llx\nguess2:%016llx\n ", tempA[a].guess, tempB[b].guess);
	FILE *f = fopen("collision.txt","a+");
	
	fprintf(f, "find collisions!\nguess1:%016llx\nguess2:%016llx\n ", tempA[a].guess, tempB[b].guess);
	
	fclose(f);
	
	return EQUAL;
}


static inline int hash_compare(output_t *temp, const UINT64 a, const UINT64 b){

    CHECK_NN(temp)
    CHECK_GE(a, 0)
    CHECK_GE(b, 0)
    CHECK_NE(a, b)
	for(int i = 0; i < 6; i ++){
		if(temp[a].state[i] < temp[b].state[i]){
			
			return PREC;
		}
		if(temp[a].state[i] > temp[b].state[i]){
			
			return SUCC;
		}
	
	}
	printf("find collisions!\nguess1:%016llx\nguess2:%016llx\n ", temp[a].guess, temp[b].guess);
	FILE *f = fopen("collision.txt","a+");
	
	fprintf(f, "find collisions!\nguess1:%016llx\nguess2:%016llx\n ", temp[a].guess, temp[b].guess);
	
	fclose(f);
	return EQUAL;
}

void copy_output(output_t *des, output_t *src){
	
	des->guess = src->guess;
	for(int i = 0; i < 6; i++){
	
		des->state[i] = src->state[i];
	
	}
	
}


void _hash_block_quicksort(output_t* temp, long start, long end){

    CHECK_NN(temp)
	CHECK_GE(start, 0)
    CHECK_GE(end, 0)
    CHECK_LT(start, end)
    
	//printf("start:%ld, end:%ld\n", start, end);
    long first = start, last = end;
    output_t tt;
    
    
    // find position for pivot
    while (first < last) {
        //printf("first:%ld, last:%ld\n", first, last);
        while (first < last) {
            if (hash_compare(temp, first, last) == PREC){
                last--;
            }else if(hash_compare(temp, first, last) == EQUAL){
            	exit(0);
            }
            else{
                break;
            }
        }
        //printf("first:%ld, last:%ld\n", first, last);
        
        if (first != last) {
            //tt = temp[last];
            //temp[last] = temp[first];
            //temp[first] = tt;
            copy_output(&tt, &(temp[last]));
            copy_output(&(temp[last]),&(temp[first]));
            copy_output(&(temp[first]),&tt);
            
            first++;
        }
        
        
        while (first < last) {
            if (hash_compare(temp, first, last) == PREC){
                first++;
            }else if(hash_compare(temp, first, last) == EQUAL){
            	exit(0);
            }	
            else{
                break;
            }
        }
        
       // printf("first:%ld, last:%ld\n", first, last);
        if (first != last) {
            //tt = temp[first];
            //temp[first] = temp[last];
            //temp[last] = tt;
            
            copy_output(&tt, &(temp[first]));
            copy_output(&(temp[first]),&(temp[last]));
            copy_output(&(temp[last]),&tt);
            last--;
        }
    }
    
    CHECK_EQ(first, last)
    
    
    //recursive quick sort
    if (start < first - 1){
    	//printf("--start:%ld, first:%ld\n",start, first);
        _hash_block_quicksort(temp, start, first - 1);
    }

    
    if (last + 1 < end){
    	//printf("--last:%ld, end:%ld\n",last, end);
        _hash_block_quicksort(temp, last + 1, end);    
    }

}

void hash_block_quicksort(int hashes_idx, hashes_t* hashes){
    
	 if (hashes[hashes_idx].block_len > 1){
	 	
        _hash_block_quicksort(hashes[hashes_idx].hashes, 0, hashes[hashes_idx].block_len - 1);
     }
}


void hash_block_merge2(int hashes_idx0, int hashes_idx1, hashes_t* hash_arr, int block_len){
	
	//printf("start merge 2\n");
	output_t *hashes_m = (output_t*) calloc (2 * block_len, sizeof(output_t));
	
	int n = 0;
	int p0 = 0, p1 = 0;
	while(p0 < block_len && p1 < block_len){
		if(hash_compare(hash_arr[hashes_idx0].hashes, p0, hash_arr[hashes_idx1].hashes, p1) == PREC){
			hashes_m[n].guess = hash_arr[hashes_idx0].hashes[p0].guess;
			for(int i = 0 ;i < 6; i++){
				hashes_m[n].state[i] = hash_arr[hashes_idx0].hashes[p0].state[i]; 
			}
			p0++;
			n++;
		}else if(hash_compare(hash_arr[hashes_idx0].hashes, p0, hash_arr[hashes_idx1].hashes, p1) == SUCC){
			hashes_m[n].guess = hash_arr[hashes_idx1].hashes[p1].guess;
			for(int i = 0 ;i < 6; i++){
				hashes_m[n].state[i] = hash_arr[hashes_idx1].hashes[p1].state[i]; 
			}
			p1++;
			n++;
		}else{
			printf("find collisions!\n");
			exit(0);
		
		}
	
	}
	while(p0 < block_len){
		hashes_m[n].guess = hash_arr[hashes_idx0].hashes[p0].guess;
		for(int i = 0 ;i < 6; i++){
			hashes_m[n].state[i] = hash_arr[hashes_idx0].hashes[p0].state[i]; 
		}
		p0++;
		n++;
	
	}
	
	while(p1 < block_len){
		hashes_m[n].guess = hash_arr[hashes_idx1].hashes[p1].guess;
		for(int i = 0 ;i < 6; i++){
			hashes_m[n].state[i] = hash_arr[hashes_idx1].hashes[p1].state[i]; 
		}
		p1++;
		n++;
	
	}
	
	//printf("finish merge\n");
	int max,min;
	if(hashes_idx0 < hashes_idx1){
		min = hashes_idx0;
		max = hashes_idx1;
	}else{
		max = hashes_idx0;
		min = hashes_idx1;
	}
	
	//free the hashes[max]
	//printf("free hashes max\n");
	free(hash_arr[max].hashes);
	hash_arr[max].block_len = 0;
	//free(hash_arr[max]);
	
	//copy the merge hashes to hashes[min]
	//printf("realloc to hashes min\n");
	hashes_realloc(min, hash_arr, n);
	
	//printf("copy to hashes min\n");
	for(int i = 0 ;i < n; i++){
		//printf("%d.\n",i);
		hash_arr[min].hashes[i].guess = hashes_m[i].guess;
		for(int j = 0 ;j < 6; j++){
			hash_arr[min].hashes[i].state[j] = hashes_m[i].state[j]; 
			//printf("m %016llx\n",hashes_m[i].state[j]);
		}
	}
	hash_arr[min].block_len = n;
	
	//printf("the result of merge 2\n");
	//print_hashes(min, hash_arr);
	//return n;
}

//return the new block length
int hash_block_merge_all(hashes_t* hashes, int hashes_len){
    if(hashes_len <= 0){
    	//printf("no merge\n");
    	return hashes_len+1;
    }
/*
    printf("old block length : ");
    for(int i = 0; i < hashes_len+1; i++){
    	printf("%d |", hashes[i].block_len);
    }
    printf("\n");
	printf("hashes_len : %d \n", hashes_len);
  */
    for(int i = hashes_len; i > 0; i--){
    	if(hashes[i].block_len == hashes[i - 1].block_len){
    	 //merge
    	 	hash_block_merge2(i-1, i, hashes, hashes[i].block_len);
    	}
    }
    
    //remove null hashes_array and update the hashes_len;
    int new_hashes_len = 0;    
    for(int i = 0; i < hashes_len + 1; i ++){
		if(new_hashes_len < i){
			if(hashes[i].block_len > 0){
				//copy hashes[i] to hashes[new_hashes_len]
				hashes[new_hashes_len].block_len = hashes[i].block_len;
				hashes[new_hashes_len].hashes = hashes[i].hashes;
				//clear hashes[i]
				
				hashes[i].block_len = 0;
				free(hashes[i].hashes);
				new_hashes_len++;
			}
		}else if(new_hashes_len == i && hashes[i].block_len > 0){
			new_hashes_len++;
		}
    
    }
    printf("new hash len : %d\n",new_hashes_len);
    printf("new block length : ");
    for(int i = 0; i < new_hashes_len+1; i++){
    	printf("%d |", hashes[i].block_len);
    }
    printf("\n");
    
    return new_hashes_len;
}



/*
bool find_collision(tKeccakLane state[25], int hashes_idx, hashes_t* hashes, UINT64 guess){
    bool found = false;
    for(int hi = 0; hi < hashes_idx; hi++){
        for(int bi = 0; bi < hashes[hi].block_len; bi++){
            bool flag = true;
            for(int si = 0; si < 6 ; si++){
                if(hashes[hi].hashes[bi].state[si] == state[si]){
                    continue;
                }else{
                    flag = false;
                    break;
                }
            }
            if(flag){
                printf("We find collision!!!!\n");
                printf("guess1:%016llx\nguess2:%016llx\n", guess, hashes[hi].hashes[bi].guess);
                found = true;
            }
        }
        if(found){
            break;
        }
    }
    return found;
    
}
*/




int main(){

    


    printf("hello 384\n");
    tKeccakLane state[25]; 
   
	KeccakP1600_StaticInitialize(); 

	/*
	x0+x18+x20+x24+x38+x40,
    x1+x8+x21+x28+x41+x45+x48,
    x2+x6+x9+x22+x42+x49+1,
    x3+x17+x23+x27+x37+x43,
    x4+x17+x24+x37+x44+1,
    x5+x16+x17+x25+x27+x37+x45+1,
    x7+x16+x20+x27+x36+x47+1,
    x10+x17+x30+x37+x50,
    x11+x18+x31+x38+x51,
    x12+x16+x17+x27+x32+x37+1,12
    x13+x18+x24+x33+x38+1,
    x29.
	 */ 
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
    
    
    
    
    hashes_t *hashes = (hashes_t*) calloc(1024, sizeof(hashes_t));
    int hashes_idx = 0, output_idx = 0;
    hashes_calloc(hashes_idx, hashes);
    
    clock_t tstart,tend;
    tstart = clock();
    
    
    for(UINT64 i = 0; i < (1<<23); i++){
        if(i %(1<<21) == 0){
            printf("*************** i:%lld *****************\n",i);
        }
        UINT64 guess = 1L << 63;
        guess ^= ((i & 1) << 6);
        guess ^= ((i & 0x06L) << 7);
        guess ^= ((i & 0x3FFF8L) << 11);
        guess ^= ((i & 0xFFFC0000L) << 12);
        guess ^= (1L << 51);

        getState(state, constraints, guess);
        tKeccakLane state_copy[25];
        KeccakF1600Permute(state, 3);
        
        if(output_idx == (HASHES_CAP)){
            //order the hash block
            hash_block_quicksort(hashes_idx, hashes);
            
            	//print_hashes(hashes_idx, hashes);
            //printf("hashes_idx:%d\n", hashes_idx);
            //merge the existing blocks
            
            int new_hashes_len = hash_block_merge_all(hashes, hashes_idx);
            hashes_idx = new_hashes_len - 1;
            
            hashes_idx ++;
            if(hashes_idx== 1024){
                printf("the capacity is not enough!");
                exit(0);
            }
            
            output_idx = 0;
            
                        
            //todo calloc new hashes block
            hashes_calloc(hashes_idx, hashes);
            
        }
        
        bool flag = false;
        //bool flag = find_collision(state, hashes_idx, hashes, guess);
        if(!flag){
            output_add(hashes_idx, output_idx, hashes, guess, state);
            output_idx++;
        }else{
        	printf("flag is true\n");
            break;
        }
    }
    
    //final order and merge
    hash_block_quicksort(hashes_idx, hashes);
            
    //print_hashes(hashes_idx, hashes);
    
    int hashes_len = hash_block_merge_all(hashes, hashes_idx);
    printf("hashes length:%d\n", hashes_len);
    //print_hashes(0, hashes);
    
    tend = clock();
    
    printf("run time:%.03f s\n", (double)(tend-tstart)/CLOCKS_PER_SEC);
    //print_hashes(hashes_idx, hashes);
    
    return 0;
}
