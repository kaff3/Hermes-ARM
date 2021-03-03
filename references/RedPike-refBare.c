#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#define __STDC_FORMAT_MACROS


 #define CONST 0x9E3779B9
 #define ROUNDS 16
 
 #define ROTL(X, R) (((X) << ((R) & 31)) | ((X) >> (32 - ((R) & 31))))
 #define ROTR(X, R) (((X) >> ((R) & 31)) | ((X) << (32 - ((R) & 31))))
 
 void encrypt(uint32_t * x, const uint32_t * k)
 {
   unsigned int i;
   uint32_t rk0 = k[0];
   uint32_t rk1 = k[1];
 
   for (i = 0; i < ROUNDS; i++)
   {
     rk0 += CONST;
     rk1 -= CONST;
 
     x[0] ^= rk0;
     x[0] += x[1];
     x[0] = ROTL(x[0], x[1]);
 
     x[1] = ROTR(x[1], x[0]);
     x[1] -= x[0];
     x[1] ^= rk1;
   }
 
   rk0 = x[0]; x[0] = x[1]; x[1] = rk0;
 }

