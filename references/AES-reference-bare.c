/**
  This is free and unencumbered software released into the public domain.

  Anyone is free to copy, modify, publish, use, compile, sell, or
  distribute this software, either in source code form or as a compiled
  binary, for any purpose, commercial or non-commercial, and by any
  means.

  In jurisdictions that recognize copyright laws, the author or authors
  of this software dedicate any and all copyright interest in the
  software to the public domain. We make this dedication for the benefit
  of the public at large and to the detriment of our heirs and
  successors. We intend this dedication to be an overt act of
  relinquishment in perpetuity of all present and future rights to this
  software under copyright law.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
  IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR
  OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
  ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
  OTHER DEALINGS IN THE SOFTWARE.

  For more information, please refer to <http://unlicense.org/> */

/* simplified from code by odzhan at https://github.com/odzhan/aes_dust */

#include <stdio.h>
#include <string.h>
#include <stdint.h>

#include <inttypes.h>

typedef uint8_t u8;
typedef int8_t s8;

typedef uint32_t u32;

 #define R(X, R) (((X) >> ((R) & 31)) | ((X) << (32 - ((R) & 31))))

// Multiplication over GF(2**8)
#define M(x)(((x)<<1)^((-((x)>>7))&0x1b))

void aes_ecb(void *mk, void *data, u8 sbox[], u8 M0x3[]) {
  u8 a,b,c,d,i,j,t,w,x[16],k[16],rc=1,*s=(u8*)data;
      
  // copy 128-bit plain text + 128-bit master key to x
  for(i=0;i<16;i++) {
    x[i]=s[i], k[i]=((u8*)mk)[i];
  }
  
  for(;;) {
    // AddRoundKey
    for(i=0;i<16;i++) {
      s[i]=x[i]^k[i];
    }
    // if round 11, stop
    if(rc==108)break;
    // AddConstant
    k[0]^=rc; rc=M(rc);
    // ExpandKey
    for(i=0;i<4;i++) {
      k[i]^=sbox[k[12+((i-3)&3)]];
    }
    for(i=0;i<12;i++) {
      k[i+4]^=k[i];
    }
    // SubBytes and ShiftRows
    for(w=i=0;i<16;i++) {
      ((u8*)x)[w]=sbox[((u8*)s)[i]],w=(w-3)&15;
    }
    // if not round 11
    if(rc!=108) {
      // MixColumns
      for(i=0;i<16;i+=4) {
	a=x[i],b=x[i+1],c=x[i+2],d=x[i+3];
	  x[i] ^= M0x3[a^b] ^ c ^ d;
	  x[i+1] ^= M0x3[b^c] ^ a ^ d;
	  x[i+2] ^= M0x3[c^d] ^ a ^ b;
	  x[i+3] ^= M0x3[a^d] ^ b ^ c;
      }
    }
  }
}
