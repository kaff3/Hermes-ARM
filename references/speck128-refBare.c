#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#define __STDC_FORMAT_MACROS

#define ROR(x, r) ((x >> r) | (x << (64 - r)))
#define ROL(x, r) ((x << r) | (x >> (64 - r)))
#define R(x, y, k)\
  (x = ROR(x, 8), x += y, x ^= k, y = ROL(y, 3), y ^= x)
#define ROUNDS 32

void encrypt(uint64_t ct[2], uint64_t const K[2])
{
   uint64_t y = ct[0], x = ct[1], b = K[0], a = K[1];

   R(x, y, b);
   for (int i = 0; i < ROUNDS - 1; i++) {
      R(a, b, i);
      R(x, y, b);
   }

   ct[0] = y;
   ct[1] = x;
}
