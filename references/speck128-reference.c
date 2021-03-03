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


int countTokens(char line[])
{
  int count = 0, i = 0;

  while (line[i] != '\n' && line[i] != 0) {
    while (line[i] == ' ') i++;
    count++;
    while (line[i] != ' ' && line[i] != '\n' && line[i] != 0) i++;
  }
  return count;
}



int main() {
  char *line, *c;
  int i;
  uint64_t *ct;
  uint64_t *K;


  line = (char *)malloc(2048);
  scanf("%[^\n]%*c\n",line);
  c = line; int sizeOf_ct = countTokens(line);
  ct = (uint64_t *) malloc(sizeof(uint64_t )*sizeOf_ct);
  for (i = 0; i < sizeOf_ct; i++) {
    while (*c == ' ') c++;
    sscanf(c, "%"SCNu64"", &ct[i]);
    while (*c != ' ' && *c != '\n' && *c != 0) c++;
  }

  scanf("%[^\n]%*c\n",line);
  c = line; int sizeOf_K = countTokens(line);
  K = (uint64_t *) malloc(sizeof(uint64_t )*sizeOf_K);
  for (i = 0; i < sizeOf_K; i++) {
    while (*c == ' ') c++;
    sscanf(c, "%"SCNu64"", &K[i]);
    while (*c != ' ' && *c != '\n' && *c != 0) c++;
  }

  for (i = 0; i < 100000000; i++)
    encrypt(ct, K);

  for (i = 0; i < sizeOf_ct; i++) {
    printf("0x%"PRIx64" ", ct[i]);
  }
  printf("\n");

  for (i = 0; i < sizeOf_K; i++) {
    printf("0x%"PRIx64" ", K[i]);
  }
  printf("\n");


}
