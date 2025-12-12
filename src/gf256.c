#include <stddef.h>

#define GF_POLY 0x11d  /* GF(2^8) 생성 다항식 x^8 + x^4 + x^3 + x + 1 */

/* 로그/지수 테이블: 곱셈과 역원을 빠르게 하기 위해 사전 계산 */
static unsigned char gf_log_tbl[256];
static unsigned char gf_exp_tbl[512]; /* 오버플로우 처리 위해 2배 길이 */
static int gf_tables_ready = 0;

/* GF(256) 테이블 초기화: 원시 원소를 계속 곱하면서 log/exp 테이블 채움 */
void gf256_init(void) {
  if (gf_tables_ready) return;
  unsigned short x = 1;
  for (int i = 0; i < 255; ++i) {
    gf_exp_tbl[i] = (unsigned char)x;
    gf_log_tbl[x] = (unsigned char)i;
    x <<= 1;
    if (x & 0x100) x ^= GF_POLY; /* 8비트 넘치면 생성다항식으로 모듈로 연산 */
  }
  /* 지수 테이블을 한 바퀴 더 복사해 덧셈 결과를 그대로 인덱싱 가능하게 함 */
  for (int i = 255; i < 512; ++i) {
    gf_exp_tbl[i] = gf_exp_tbl[i - 255];
  }
  gf_tables_ready = 1;
}

/* GF256 덧셈: XOR */
unsigned char gf256_add(unsigned char a, unsigned char b) {
  return (unsigned char)(a ^ b);
}

/* GF256 곱셈: log/exp 테이블을 활용해 빠르게 계산 */
unsigned char gf256_mul(unsigned char a, unsigned char b) {
  if (!gf_tables_ready) gf256_init();
  if (a == 0 || b == 0) return 0;
  unsigned short idx = (unsigned short)gf_log_tbl[a] + (unsigned short)gf_log_tbl[b];
  return gf_exp_tbl[idx];
}

/* GF256 역원: a^(−1) = exp(255 − log(a)) */
unsigned char gf256_inv(unsigned char a) {
  if (!gf_tables_ready) gf256_init();
  if (a == 0) return 0;
  return gf_exp_tbl[255 - gf_log_tbl[a]];
}
