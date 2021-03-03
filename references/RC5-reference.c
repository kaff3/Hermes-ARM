#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#define __STDC_FORMAT_MACROS

#define ROTL(X, R) (((X) << ((R) & 31)) | ((X) >> (32 - ((R) & 31))))

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
