#ifndef GenKeccakEquations_config_h
#define GenKeccakEquations_config_h


#define KeccakReference

#define Five 5
#define LANE 64  //length of a lane
#define L 224     //length of output

#define B (LANE * 25)  //width of permutation
#define C (L * 2)      //capacity
#define R (B - C)      //range


#define maxNrRounds 24

#define index(x, y) (((x)%5)+5*((y)%5))
#define MODFive(x)  ((x+5)%5)
#define MODLane(x)  ((x+LANE)%LANE)


#define equLength 4000
#define UINT64_MAX ULLONG_MAX

typedef unsigned long long UINT64;
typedef UINT64 tKeccakLane;

static const tKeccakLane KeccakRoundConstants[maxNrRounds] =
{
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
};

static const unsigned int KeccakRhoOffsets[25] =
{
    0,  1, 62, 28, 27, 36, 44,  6, 55, 20,  3, 10, 43, 25, 39, 41, 45, 15, 21,  8, 18,  2, 61, 56, 14
};

#endif
