
#include "operation.h"

int main(int argc, const char * argv[])
{
   
    
    //generate equations of the first stage
    //FILE* f = fopen("../data/equ_files/equations_pre.txt","w+");
    FILE* f = fopen("equations.txt", "w+");
    bool vars[Five * Five]={1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0};  //1 means this lane is unknown,0 means constants
    UINT64 value[Five][Five];
    for (int i = 0 ; i < Five; i++) {
        for (int j = 0 ; j < Five; j++) {
            value[i][j] = 0;
        }
    }
    
    char state[Five][Five][LANE][equLength];
    initState(state, value);    
    initVars_sym(state, vars, 4);
    UINT64 sum2[Five] = {2,2,2,2,2};
    theta(state, sum2);
    rho(state);
    pi(state);
    
    UINT64 input_diff[25] = {0x0080000000000000, 0x0               , 0x0000000000000001, 0x0, 0x0,
                             0x0               , 0x0               , 0x0               , 0x0, 0x0,
                             0x0080000000000000, 0x0000000008000000, 0x0               , 0x0, 0x0,
                             0x0               , 0x0000000008000000, 0x0000000000000001, 0x0, 0x0,
                             0x0               , 0x0               , 0x0               , 0x0, 0x0};
                             
    UINT64 output_diff[25] = {0x0080000000000001, 0x0               , 0x0000000000000001, 0x0, 0x0,
                             0x0               , 0x0               , 0x0               , 0x0, 0x0,
                             0x0080000000000000, 0x0000000008000000, 0x0               , 0x0, 0x0,
                             0x0               , 0x0000000008000000, 0x0000000000000001, 0x0, 0x0,
                             0x0               , 0x0               , 0x0               , 0x0, 0x0};
    for(int y = 0 ; y < 5; y++ ){
        for(int z = 0; z < 64; z++){
            bool i_d[5];
            bool o_d[5];
            for(int x = 0; x < 5; x++){
                i_d[x] = (input_diff[y * 5 + x] >> z) & (UINT64)1L;
                o_d[x] = (output_diff[y * 5 + x] >> z) & (UINT64)1L;

            }
            //printf("input diff:%d %d %d %d %d\n", i_d[0], i_d[1], i_d[2], i_d[3], i_d[4]);
            //printf("output diff:%d %d %d %d %d\n\n", o_d[0], o_d[1], o_d[2], o_d[3], o_d[4]); 
            if(i_d[0]==0 && i_d[1] == 0 && i_d[2] == 0 && i_d[3] == 0 && i_d[4] == 0){
                continue;
            }
            for(int x = 0; x < 5; x++){
                bool cons = i_d[x] ^ i_d[MODFive(x+2)] ^ (i_d[MODFive(x+1)] & i_d[MODFive(x+2)]) ^ o_d[x];
                if(i_d[MODFive(x+1)]){
                    printOneEqu(state[MODFive(x+2)][y][z]);
                }
                if(i_d[MODFive(x+2)]){
                    if(i_d[MODFive(x+1)]){
                        printf(" + ");
                    }
                    printOneEqu(state[MODFive(x+1)][y][z]);                    
                }
                if(cons){
                    printf(" + 1");
                }
                if(i_d[MODFive(x+1)] | i_d[MODFive(x+2)] | cons){
                    printf(",\n");
                }
            }
        }
    }
    
    
    
    //printAllState(state);
    
    fclose(f);
    printf("hello 384\n");    
    
    /*
    
    char state[Five][Five][LANE][equLength];
    UINT64 value[Five][Five];
    bool vars[Five * Five]={1,0,1,0,0,1,0,1,0,0,1,0,1,0,0,1,0,1,0,0,0,0,0,0,0};  //1 means this lane is unknown,0 means constants
    UINT64 sum0[Five] = {1,0,0,0,1};  //2 means the sum has variables. The values are the bitwise sum of two CP.
    UINT64 sum1[Five] = {2,2,2,0,1};
    UINT64 sum2[Five] = {2,2,2,2,2};

    for (int i = 0 ; i < Five; i++) {
        for (int j = 0 ; j < Five; j++) {
            value[i][j] = 0;
        }
    }
    
    value[0][1] = UINT64_MAX;
    value[0][3] = UINT64_MAX;
    
    
    //initial
    initState(state, value);
    initVars(state, vars);

    
    //the first round
    
    //write 128 linear equations
    writeSumOf2CPs(f, state, sum0, 0);
    
    theta(state, sum0);
    rho(state);
    pi(state);
    chi(state);
    iota(state, 0);

    // the second round
    
    //write 256 linear equations
    writeSumOf2CPs(f, state, sum0, 1);
    rho(state);
    pi(state);
    chi(state);
    iota(state, 1);

    //the third round
    theta(state, sum2);
    rho(state);
    pi(state);
    
    //write 64 equations of guessing values of 32 pairs
    writeGuessEquations(f, state, 600);
    
    chi(state);
    iota(state, 2);

    //129 constraints
    for (int z = 0; z < LANE; z++) {
        int p34 = 0;

        while (state[3][4][z][p34] != ':') {
            p34++;
        }
        state[3][4][z][p34++] = '+';
        int p33 = 0;
        while (state[3][3][z][p33] != ':') {
            state[3][4][z][p34++] = state[3][3][z][p33++];

        }
        state[3][4][z][p34++] = '+';
        state[3][4][z][p34++] = '1';
        state[3][4][z][p34++] = ':';
        int p44 = 0;
        
        while (state[4][4][z][p44] != ':') {
            p44++;
        }
        state[4][4][z][p44++] = '+';
        int p43 = 0;
        while (state[4][3][z][p43] != ':') {
            state[4][4][z][p44++] = state[4][3][z][p43++];
            
        }
        state[4][4][z][p44++] = '+';
        state[4][4][z][p44++] = '1';
        state[4][4][z][p44++] = ':';

    }

    int p24 = 0;
    while(state[2][4][63][p24] != ':'){
        p24++;
    }
    state[2][4][63][p24++] = '+';
    int p23 = 0;
    while(state[2][3][63][p23] != ':'){
        state[2][4][63][p24++] = state[2][3][63][p23++];
    }
    state[2][4][63][p24++] = ':';



    
    //write 129 quadratic equations
    writeEquations(f, state);
*/    
    return 0;
}

