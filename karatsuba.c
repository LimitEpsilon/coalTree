#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <stdint.h>

char *to_binary(uint64_t x) {
  char* ret;
  ret = malloc(65 * sizeof(char));
  ret[64] = 0;
  for (int i = 63; i >= 0; --i) {
    ret[i] = '0' + (char)(x & 1);
    x = x >> 1;
  }

  return ret;
}
uint64_t karatsuba(uint32_t x, uint32_t y, uint64_t z) {
  uint16_t x1 = x >> 16;
  uint16_t x2 = x & 0xffff;
  uint16_t y1 = y >> 16;
  uint16_t y2 = y & 0xffff;
  uint32_t z1 = z >> 32;
  uint32_t z2 = z & 0xffffffff;

  uint32_t midx = (uint32_t)x2 - (uint32_t)x1; // Bit#(17)
  uint32_t midy = (uint32_t)y1 - (uint32_t)y2; // Bit#(17)
  uint32_t midz = z1 + z2; // Bit#(32)

  uint16_t midx_sign = midx >> 16; // pack(replicate(msb(midx)))
  uint16_t midy_sign = midy >> 16; // pack(replicate(msb(midy)))
  uint16_t midx_val = midx; // midx[15:0]
  uint16_t midy_val = midy; // midy[15:0]
  uint16_t adj = -((midy_sign & midx_val) + (midx_sign & midy_val));

  // recursive call
  uint64_t high = x1 * y1 + z1; // Bit#(33)
  uint64_t low = x2 * y2 + z2; // Bit#(33)
  uint32_t mid = (uint32_t)midx_val * (uint32_t)midy_val + ((uint32_t)adj << 16); // Bit#(33)
  printf("midx_sign: %x, midy_sign: %x, mid: %d, mid_correct: %d\n",
          midx_sign, midy_sign, (int32_t)mid, (int32_t)midx * (int32_t)midy);

  mid += low + high - midz;
  uint64_t mid_ = (uint64_t)mid + (uint64_t)(low >> 16);
  high += (uint32_t)(mid_ >> 16);
  return ((uint64_t)high << 32) | ((mid_ & 0xffff) << 16) | (low & 0xffff);
}

int main () {
  uint32_t x, y;
  uint64_t z;
  srand(time(NULL));

  x = 0xffff0001;
  y = 0xffff0001;
  z = rand();

  uint64_t karatsuba_out = karatsuba(x, y, -z);
  uint64_t correct = (uint64_t)x * (uint64_t)y - z;
  printf("x: %u, y: %u, diff: %s\n", x, y, to_binary(karatsuba_out ^ correct));
  return 0;
}
