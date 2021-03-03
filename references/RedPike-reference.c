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
  uint32_t *v;
  uint32_t *k;


  line = (char *)malloc(2048);
  scanf("%[^\n]%*c\n",line);
  c = line; int sizeOf_v = countTokens(line);
  v = (uint32_t *) malloc(sizeof(uint32_t )*sizeOf_v);
  for (i = 0; i < sizeOf_v; i++) {
    while (*c == ' ') c++;
    sscanf(c, "%"SCNu32"", &v[i]);
    while (*c != ' ' && *c != '\n' && *c != 0) c++;
  }

  scanf("%[^\n]%*c\n",line);
  c = line; int sizeOf_k = countTokens(line);
  k = (uint32_t *) malloc(sizeof(uint32_t )*sizeOf_k);
  for (i = 0; i < sizeOf_k; i++) {
    while (*c == ' ') c++;
    sscanf(c, "%"SCNu32"", &k[i]);
    while (*c != ' ' && *c != '\n' && *c != 0) c++;
  }

  for (i = 0; i < 100000000; i++)
    encrypt(v, k);

  for (i = 0; i < sizeOf_v; i++) {
    printf("0x%"PRIx32" ", v[i]);
  }
  printf("\n");

  for (i = 0; i < sizeOf_k; i++) {
    printf("0x%"PRIx32" ", k[i]);
  }
  printf("\n");


}
