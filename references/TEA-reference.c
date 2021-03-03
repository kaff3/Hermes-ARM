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
    encrypt_F(v, k);

  for (i = 0; i < sizeOf_v; i++) {
    printf("0x%"PRIx32" ", v[i]);
  }
  printf("\n");

  for (i = 0; i < sizeOf_k; i++) {
    printf("0x%"PRIx32" ", k[i]);
  }
  printf("\n");


}
