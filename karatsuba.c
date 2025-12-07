#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <stdint.h>

typedef struct {
  uint32_t msb;
  uint64_t lower;
} uint65_t;

uint65_t karatsuba(uint32_t x, uint32_t y, uint64_t z) {
  uint16_t x1 = x >> 16;
  uint16_t x2 = x & 0xffff;
  uint16_t y1 = y >> 16;
  uint16_t y2 = y & 0xffff;
  uint32_t z1 = z >> 32;
  uint32_t z2 = z & 0xffffffff;

  uint32_t midx = (uint32_t)x2 - (uint32_t)x1; // Bit#(17)
  uint32_t midy = (uint32_t)y1 - (uint32_t)y2; // Bit#(17)
  uint64_t midz = (uint64_t)z1 + (uint64_t)z2; // Bit#(33)

  uint16_t midx_sign = midx >> 16; // pack(replicate(msb(midx)))
  uint16_t midy_sign = midy >> 16; // pack(replicate(msb(midy)))
  uint16_t midx_val = midx; // midx[15:0]
  uint16_t midy_val = midy; // midy[15:0]
  uint16_t adj = -((midy_sign & midx_val) + (midx_sign & midy_val));

  // recursive call
  uint64_t high = (uint64_t)x1 * (uint64_t)y1 + (uint64_t)z1; // Bit#(33)
  uint64_t low = (uint64_t)x2 * (uint64_t)y2 + (uint64_t)z2; // Bit#(33)
  uint32_t mid = (uint32_t)midx_val * (uint32_t)midy_val + ((uint32_t)adj << 16); // Bit#(32)
  int32_t mid_correct = (int32_t)midx * (int32_t)midy;
  if (mid != (uint32_t)mid_correct)
    printf("midx: %d, midy: %d, midx_sign: %x, midy_sign: %x, mid: %u, mid_correct: %d\n",
            (int32_t)midx, (int32_t)midy, midx_sign, midy_sign, mid, mid_correct);

  uint64_t mid_ = (midx_sign ^ midy_sign && midx && midy ? (uint64_t)(-1) << 32 : 0) | mid; // signExtend to Bit#(33)
  mid_ += low + high - midz;
  uint64_t mid__correct = (uint64_t)x1 * (uint64_t)y2 + (uint64_t) x2 * (uint64_t) y1;
  if (mid_ != mid__correct)
    printf("mid_: %llu, mid__correct: %llu\n", mid_, mid__correct);
  mid_ += low >> 16;
  high += (uint32_t)(mid_ >> 16);

  uint65_t ret;
  ret.msb = (uint32_t)(high >> 32);
  ret.lower = ((uint64_t)high << 32) | ((mid_ & 0xffff) << 16) | (low & 0xffff);
  return ret;
}

int main () {
  uint32_t x, y;
  uint64_t z, mult, diff_lower;
  uint65_t karatsuba_out, correct;
  char diff_msb;

  srand(time(NULL));

  for (int i = 0; i < 100000000; ++ i) {
    x = rand() & 0xffff;
    x = x << 16;
    x |= rand() & 0xffff;
    y = rand() & 0xffff;
    y = y << 16;
    x |= rand() & 0xffff;
    z = rand();
    z = z << 32;
    z |= rand();

    karatsuba_out = karatsuba(x, y, z);
    mult = (uint64_t)x * (uint64_t)y;
    correct.msb = z && (mult >= -z);
    correct.lower = mult + z;
    diff_msb = karatsuba_out.msb ^ correct.msb;
    diff_lower = karatsuba_out.lower ^ correct.lower;
    if (diff_msb || diff_lower) {
      if (correct.msb > 0) {
        printf("msb is 1\n");
      }
      printf("x: %u, y: %u, z: %llu, diff_msb: %c, diff_lower: %llx\n",
              x, y, z, diff_msb ? '1' : '0', diff_lower);
    }
  }
  return 0;
}
