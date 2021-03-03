#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#define __STDC_FORMAT_MACROS

#define ROTL(X, R) (((X) << ((R) & 31)) | ((X) >> (32 - ((R) & 31))))
#define ROTR(X, R) (((X) >> ((R) & 31)) | ((X) << (32 - ((R) & 31))))

#define r 12

void encrypt(uint32_t pt[], uint32_t S[])
{
   uint32_t i, A = pt[0] + S[0], B = pt[1] + S[1];
   
   for (i = 1; i <= r; i++)
   {
      A = ROTL(A ^ B, B) + S[2*i];
      B = ROTL(B ^ A, A) + S[2*i + 1];
   }
   pt[0] = A; pt[1] = B;
}

