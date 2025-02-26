#include <stdlib.h>
#include <memory.h>
#include <stddef.h>
#include <stdio.h>


#define SHA256_H
#define SHA256_BLOCK_SIZE 32


#define ROTLEFT(a,b) (((a) << (b)) | ((a) >> (32-(b))))
#define ROTRIGHT(a,b) (((a) >> (b)) | ((a) << (32-(b))))

#define CH(x,y,z) (((x) & (y)) ^ (~(x) & (z)))
#define MAJ(x,y,z) (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))
#define EP0(x) (ROTRIGHT(x,2) ^ ROTRIGHT(x,13) ^ ROTRIGHT(x,22))
#define EP1(x) (ROTRIGHT(x,6) ^ ROTRIGHT(x,11) ^ ROTRIGHT(x,25))
#define SIG0(x) (ROTRIGHT(x,7) ^ ROTRIGHT(x,18) ^ ((x) >> 3))
#define SIG1(x) (ROTRIGHT(x,17) ^ ROTRIGHT(x,19) ^ ((x) >> 10))

static const unsigned int k[64] = {
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
};


void sha256_transform(unsigned char data[64], unsigned int datalen, unsigned long long bitlen, unsigned int state[8], unsigned char data1[], unsigned int hash[8], unsigned int check[200])
{
    unsigned int a, b, c, d, e, f, g, h, i, j, t1, t2, m[64];

    for (i = 0; i < 16; ++i)
	m[i] = data1[i];
    for (i=16; i < 64; ++i)
	m[i] = SIG1(m[i - 2]) + m[i - 7] + SIG0(m[i - 15]) + m[i - 16];

    a = state[0];
    b = state[1];
    c = state[2];
    d = state[3];
    e = state[4];
    f = state[5];
    g = state[6];
    h = state[7];
    
    check[0] = a;
    check[1] = e;

    for (i = 0; i < 18; ++i) {
        t1 = h + EP1(e) + CH(e,f,g) + k[i] + m[i];
        t2 = EP0(a) + MAJ(a,b,c);
        h = g;
        g = f;
        f = e;
        e = d + t1;
        d = c;
        c = b;
        b = a;
        a = t1 + t2;
        // сохраняем промежуточные значения регистров на каждом шаге
        check[8*i] = a;
        check[8*i+1] = b;
        check[8*i+2] = c;
        check[8*i+3] = d;
        check[8*i+4] = e;
        check[8*i+5] = f;
        check[8*i+6] = g;
        check[8*i+7] = h;
    }

    state[0] += a;
    state[1] += b;
    state[2] += c;
    state[3] += d;
    state[4] += e;
    state[5] += f;
    state[6] += g;
    state[7] += h;
    
    hash[0] = state[0];
    hash[1] = state[1];
    hash[2] = state[2];
    hash[3] = state[3];
    hash[4] = state[4];
    hash[5] = state[5];
    hash[6] = state[6];
    hash[7] = state[7];
}

int main() {
    
    // collisitions
    unsigned int input1[16];
    unsigned int input2[16];
    
    unsigned int hash1[8];
    unsigned int hash2[8];
    
    unsigned int m_copy1[64];
    unsigned int m_copy2[64];
    
    
    unsigned char text[64];
    unsigned int hash[8];
    unsigned int check1[200];
    unsigned int check2[200];
    
    unsigned char data[64];
    unsigned int datalen = 0;
    unsigned long long bitlen = 0;
    unsigned int state[8];
    state[0] = 0x6a09e667;
    state[1] = 0xbb67ae85;
    state[2] = 0x3c6ef372;
    state[3] = 0xa54ff53a;
    state[4] = 0x510e527f;
    state[5] = 0x9b05688c;
    state[6] = 0x1f83d9ab;
    state[7] = 0x5be0cd19;
    
    
    __CPROVER_bool is_diff=0;
    for (int i=0; i<64; i++) {
      if (input1[i] != input2[i]) {
          is_diff=1;
      }
    }
    __CPROVER_assume(is_diff==1);


    sha256_transform(data, datalen, bitlen, state, input1, hash1, check1);
//    printf("%x,",hash1[0]);
//    printf("%x,",hash1[1]);
//    printf("%x,",hash1[2]);
//    printf("%x,",hash1[3]);
//    printf("%x,",hash1[4]);
//    printf("%x,",hash1[5]);
//    printf("%x,",hash1[6]);
//    printf("%x\n",hash1[7]);
    


    datalen = 0;
    bitlen = 0;
    state[0] = 0x6a09e667;
    state[1] = 0xbb67ae85;
    state[2] = 0x3c6ef372;
    state[3] = 0xa54ff53a;
    state[4] = 0x510e527f;
    state[5] = 0x9b05688c;
    state[6] = 0x1f83d9ab;
    state[7] = 0x5be0cd19;
    
    sha256_transform(data, datalen, bitlen, state, input2, hash2, check2);
//    printf("%x,",hash2[0]);
//    printf("%x,",hash2[1]);
//    printf("%x,",hash2[2]);
//    printf("%x,",hash2[3]);
//    printf("%x,",hash2[4]);
//    printf("%x,",hash2[5]);
//    printf("%x,",hash2[6]);
//    printf("%x\n",hash2[7]);
    
    // дифференциальные пути
//    for (int i = 0; i < 160; ++i) {
//        if ((i != 24) && (i != 28) && (i != 33) && (i != 36) && (i != 37) && (i != 42) && (i != 44) && (i != 45) && (i != 46) && (i != 51) && (i != 53) && (i != 54) && (i != 55) && (i != 60) && (i != 62) && (i != 63) && (i != 69) && (i != 71) && (i != 78) && (i != 87)) {
//            __CPROVER_assume(check1[i] - check2[i] == 0);
//        }
//    }
    
//    for (int i = 0; i < 19; ++i) {
//        if ((i != 3) && (i != 4) && (i != 5) && (i != 6) && (i != 8) && (i != 11)) {
//            __CPROVER_assume(m_copy1[i] - m_copy2[i] == 0);
//        }
//    }
    
//    __CPROVER_assume(check1[24] - check2[24] == 0x27f42515);
//
//    __CPROVER_assume(check1[28] - check2[28] == 0x27f42515);
//
//    __CPROVER_assume(check1[33] - check2[33] == 0x27f42515);
//
//    __CPROVER_assume(check1[36] - check2[36] == 0xb1c0627b);
//
//    __CPROVER_assume(check1[37] - check2[37] == 0x27f42515);
//
//    __CPROVER_assume(check1[42] - check2[42] == 0x27f42515);
//
//    __CPROVER_assume(check1[44] - check2[44] == 0x27f42515);
//
//    __CPROVER_assume(check1[45] - check2[45] == 0xb1c0627b);
//
//    __CPROVER_assume(check1[46] - check2[46] == 0x27f42515);
//
//    __CPROVER_assume(check1[51] - check2[51] == 0x27f42515);
//
//    __CPROVER_assume(check1[53] - check2[53] == 0x27f42515);
//
//    __CPROVER_assume(check1[54] - check2[54] == 0xb1c0627b);
//
//    __CPROVER_assume(check1[55] - check2[55] == 0x27f42515);
//
//    __CPROVER_assume(check1[60] - check2[60] == 0x27f42515);
//
//    __CPROVER_assume(check1[62] - check2[62] == 0x27f42515);
//
//    __CPROVER_assume(check1[63] - check2[63] == 0xb1c0627b);
//
//    __CPROVER_assume(check1[69] - check2[69] == 0x27f42515);
//
//    __CPROVER_assume(check1[71] - check2[71] == 0x27f42515);
//
//    __CPROVER_assume(check1[78] - check2[78] == 0x27f42515);
//
//    __CPROVER_assume(check1[87] - check2[87] == 0x27f42515);
    
//    __CPROVER_assume(m_copy1[3] - m_copy2[3] == 0x27f42515);
//    
//    __CPROVER_assume(m_copy1[4] - m_copy2[4] == 0xbde9c6f8);
//    
//    __CPROVER_assume(m_copy1[5] - m_copy2[5] == 0x4180045d);
//    
//    __CPROVER_assume(m_copy1[6] - m_copy2[6] == 0xbde9c6f8);
//    
//    __CPROVER_assume(m_copy1[8] - m_copy2[8] == 0xbde9c6f8);
//    
//    __CPROVER_assume(m_copy1[11] - m_copy2[11] == 0x27f42515);
    
    
    

//    __CPROVER_assume(check1[0]-check2[0] == 1); // a
    __CPROVER_assume(check1[4]-check2[4] == 1); // e
//    __CPROVER_assume(check1[2]-check2[2] < 10000000);
//    __CPROVER_assume(check1[3]-check2[3] < 10000000);
//    __CPROVER_assume(check1[4]-check2[4] < 10000000);
//    __CPROVER_assume(check1[5]-check2[5] < 10000000);
    // 3 раунд
//    __CPROVER_assume(check1[6]-check2[6] == 0x27f42515);
//    __CPROVER_assume(check1[7]-check2[7] == 0x27f42515);
//    // 4 раунд
//    __CPROVER_assume(check1[9]-check2[9] == 0xb1c0627b);
//    __CPROVER_assume(check1[35]-check2[35] == 1);
    for (int i=0; i<8; i++) {
      __CPROVER_assume(hash1[i] == hash2[i]);
    }
//    
//    unsigned int a, b, c, d, e, f, g, h, i, j, t1, t2, m[64];
//
//    for (i = 0, j = 0; i < 16; ++i, j += 4)
//        m[i] = (text[j] << 24) | (text[j + 1] << 16) | (text[j + 2] << 8) | (text[j + 3]);
//    for ( ; i < 64; ++i)
//        m[i] = SIG1(m[i - 2]) + m[i - 7] + SIG0(m[i - 15]) + m[i - 16];
//
//    a = state[0];
//    b = state[1];
//    c = state[2];
//    d = state[3];
//    e = state[4];
//    f = state[5];
//    g = state[6];
//    h = state[7];
//
//    for (i = 0; i < 18; ++i) {
//        t1 = h + EP1(e) + CH(e,f,g) + k[i] + m[i];
//        t2 = EP0(a) + MAJ(a,b,c);
//        h = g;
//        g = f;
//        f = e;
//        e = d + t1;
//        d = c;
//        c = b;
//        b = a;
//        a = t1 + t2;
//    }
//
//    state[0] += a;
//    state[1] += b;
//    state[2] += c;
//    state[3] += d;
//    state[4] += e;
//    state[5] += f;
//    state[6] += g;
//    state[7] += h;
//    
//    hash[0] = state[0];
//    hash[1] = state[1];
//    hash[2] = state[2];
//    hash[3] = state[3];
//    hash[4] = state[4];
//    hash[5] = state[5];
//    hash[6] = state[6];
//    hash[7] = state[7];
//    
//
////    for (int i = 0; i < 64; ++i)
////        text[i] == 0;
////    for (int i = 0; i < 64; ++i)
////        __CPROVER_assume(text[i] == 0);
//    
//    sha256_transform(data, datalen, bitlen, state, text, hash);
//    printf("%u\n", hash[0]);
//    printf("%u\n", hash[1]);
//    printf("%u\n", hash[2]);
//    printf("%u\n", hash[3]);
//    printf("%u\n", hash[4]);
//    printf("%u\n", hash[5]);
//    printf("%u\n", hash[6]);
//    printf("%u\n", hash[7]);
//    __CPROVER_assume(hash[0] == 2483249910);
//    __CPROVER_assume(hash[1] == 3995522096);
//    __CPROVER_assume(hash[2] == 2637359785);
//    __CPROVER_assume(hash[3] == 1559760337);
//    __CPROVER_assume(hash[4] == 3157087739);
//    __CPROVER_assume(hash[5] == 1420970160);
//    __CPROVER_assume(hash[6] == 839713255);
//    __CPROVER_assume(hash[7] == 2579320905);
    __CPROVER_assert(0,"test");
    return 0;
}
