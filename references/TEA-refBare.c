#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#define __STDC_FORMAT_MACROS

void encrypt_F(uint32_t *v, uint32_t *k)
{
    uint32_t v0 = v[0], v1 = v[1], sum=0, i;
    uint32_t delta=0x9E3779B9;         /* key schedule constant */
    uint32_t k0=k[0], k1=k[1], k2=k[2], k3=k[3]; /* cache key */
    for (i=0; i<32; i++) {             /* basic cycle start */
        sum += delta;
        v0 += ((v1<<4) + k0) ^ (v1 + sum) ^ ((v1>>5) + k1);
        v1 += ((v0<<4) + k2) ^ (v0 + sum) ^ ((v0>>5) + k3);
    }                                  /* end cycle */
    v[0]=v0; v[1]=v1;

}
