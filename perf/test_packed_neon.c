/* Explicit packed integer NEON builtin checks; no speed measurement.
   INRIA Non-Commercial License Agreement, as in this repository. */
#include <stdio.h>
#ifndef USE_NEON
#define USE_NEON 0
#endif
#ifndef TEST_ROUNDS
#define TEST_ROUNDS 1000000U
#endif

typedef unsigned long long u64;

/* Explicit declarations also let the default-off assembly check verify that
   these names remain ordinary external functions when not registered. */
extern u64 __builtin_cc_neon_add_u32x2(u64, u64);
extern u64 __builtin_cc_neon_sub_u32x2(u64, u64);
extern u64 __builtin_cc_neon_mul_u32x2(u64, u64);

u64 scalar_add(u64 a, u64 b) {
  unsigned lo = (unsigned)a + (unsigned)b;
  unsigned hi = (unsigned)(a >> 32) + (unsigned)(b >> 32);
  return (u64)hi << 32 | lo;
}
u64 scalar_sub(u64 a, u64 b) {
  unsigned lo = (unsigned)a - (unsigned)b;
  unsigned hi = (unsigned)(a >> 32) - (unsigned)(b >> 32);
  return (u64)hi << 32 | lo;
}
u64 scalar_mul(u64 a, u64 b) {
  unsigned lo = (unsigned)a * (unsigned)b;
  unsigned hi = (unsigned)(a >> 32) * (unsigned)(b >> 32);
  return (u64)hi << 32 | lo;
}

u64 packed_add(u64 a, u64 b) {
#if USE_NEON
  return __builtin_cc_neon_add_u32x2(a,b);
#else
  return scalar_add(a,b);
#endif
}
u64 packed_sub(u64 a, u64 b) {
#if USE_NEON
  return __builtin_cc_neon_sub_u32x2(a,b);
#else
  return scalar_sub(a,b);
#endif
}
u64 packed_mul(u64 a, u64 b) {
#if USE_NEON
  return __builtin_cc_neon_mul_u32x2(a,b);
#else
  return scalar_mul(a,b);
#endif
}

volatile u64 packed_sink;
volatile double fp_seed[20];

/* All 20 floating-point arguments remain live across the integer builtin.
   F16/F17 are allocatable registers, so the advertised scratch clobbers must
   keep their live values elsewhere. Exact binary fractions avoid rounding
   ambiguities between the two compilers. */
double live_fp(u64 a, u64 b,
  double d0,double d1,double d2,double d3,double d4,
  double d5,double d6,double d7,double d8,double d9,
  double d10,double d11,double d12,double d13,double d14,
  double d15,double d16,double d17,double d18,double d19) {
  d0+=fp_seed[0]; d1+=fp_seed[1]; d2+=fp_seed[2]; d3+=fp_seed[3];
  d4+=fp_seed[4]; d5+=fp_seed[5]; d6+=fp_seed[6]; d7+=fp_seed[7];
  d8+=fp_seed[8]; d9+=fp_seed[9]; d10+=fp_seed[10]; d11+=fp_seed[11];
  d12+=fp_seed[12]; d13+=fp_seed[13]; d14+=fp_seed[14]; d15+=fp_seed[15];
  d16+=fp_seed[16]; d17+=fp_seed[17]; d18+=fp_seed[18]; d19+=fp_seed[19];
#if USE_NEON
  packed_sink = __builtin_cc_neon_add_u32x2(a,b);
#else
  packed_sink = scalar_add(a,b);
#endif
  return d0+d1+d2+d3+d4+d5+d6+d7+d8+d9+
         d10+d11+d12+d13+d14+d15+d16+d17+d18+d19;
}

u64 state = 0x6a09e667f3bcc909ULL;
u64 next_random(void) {
  state = state * 6364136223846793005ULL + 1442695040888963407ULL;
  return state;
}

int test_pair(u64 a, u64 b, u64 *hash) {
  u64 x = packed_add(a,b), y = packed_sub(a,b), z = packed_mul(a,b);
  if (x != scalar_add(a,b) || y != scalar_sub(a,b) || z != scalar_mul(a,b)) return 1;
  *hash = (*hash * 0x100000001b3ULL) ^ x;
  *hash = (*hash * 0x100000001b3ULL) ^ y;
  *hash = (*hash * 0x100000001b3ULL) ^ z;
  return 0;
}

int main(void) {
  static const u64 edge[] = {0ULL,1ULL,2ULL,0xffffffffULL,0x100000000ULL,
    0x7fffffff80000000ULL,0x800000007fffffffULL,0xffffffff00000000ULL,
    0xffffffffffffffffULL};
  unsigned i,j;
  u64 hash = 0xcbf29ce484222325ULL;
  for (i=0;i<9;i++) for (j=0;j<9;j++)
    if (test_pair(edge[i],edge[j],&hash)) return 1;
  for (i=0;i<TEST_ROUNDS;i++) {
    u64 a=next_random(), b=next_random();
    if (test_pair(a,b,&hash)) return 2;
  }
  for (i=0;i<17;i++) {
    double k=(double)i * 0.25;
    double got=live_fp(i,0xffffffffULL,k+0.25,k+0.5,k+0.75,k+1.0,k+1.25,
      k+1.5,k+1.75,k+2.0,k+2.25,k+2.5,k+2.75,k+3.0,k+3.25,k+3.5,k+3.75,
      k+4.0,k+4.25,k+4.5,k+4.75,k+5.0);
    if (got != 20.0*k+52.5 || packed_sink != scalar_add(i,0xffffffffULL)) return 3;
  }
  printf("%u %016llx\n", TEST_ROUNDS+81U,hash);
  return 0;
}
