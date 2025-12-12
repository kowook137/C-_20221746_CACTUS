#include <stdio.h>
#include <string.h> // 사용 헤더파일은 stdio, string 두 개. 텍스트 파일을 읽고 처리하는 것과 기본적인 함수를 위해 사용.
#define PATH_SEP '\\'

#define MAX_PATH_LEN 512

/* gf256.c 에 정의한 함수 호출: RS 연산의 기본 덧셈/곱셈/역원 */
void          gf256_init(void);
unsigned char gf256_add(unsigned char a, unsigned char b);
unsigned char gf256_mul(unsigned char a, unsigned char b);
unsigned char gf256_inv(unsigned char a);

/* ---------- Reed-Solomon 오류정정 부호 ---------- */
typedef struct {
  unsigned short n, k;  /* n <= 255 */
  unsigned char  alpha; /* primitive element */
  void*          enc_matrix;
} rs_code_t;

/* Reed Solomon 코드 중 n = 10, k = 6 사용 (샤드 10개 중 6개만 있으면 복구) */
#define RS_N 10
#define RS_K 6
#define RS_BLOCK_SIZE 65536u
#define SYM_MAX ((RS_BLOCK_SIZE + RS_K - 1) / RS_K)
static const char* INPUT_PATH  = "secret.txt";
static const char* SHARDS_DIR  = "shards";
static const char* OUTPUT_PATH = "shards\\restored.txt";

/* 미리 고정하여 할당한 버퍼. 발표 ppt에서 동적 메모리 할당으로 개선 가능하다고 명시한 부분*/
static unsigned char enc_matrix[(RS_N - RS_K) * RS_K];
static unsigned char in_block[RS_BLOCK_SIZE];
static unsigned char data_syms[RS_K * (size_t)SYM_MAX];
static unsigned char parity_syms[(RS_N - RS_K) * (size_t)SYM_MAX];
static unsigned char avail_syms[RS_K * (size_t)SYM_MAX];
static unsigned char recovered[RS_K * (size_t)SYM_MAX];

/* α^exp 값을 GF256 곱셈 반복으로 계산 (반더몬드 행렬 계수 산출) */
static unsigned char gf256_pow_elem(unsigned char base, unsigned short exp) {
  unsigned char result = 1;
  while (exp) {
    if (exp & 1) result = gf256_mul(result, base);
    base = gf256_mul(base, base);
    exp >>= 1;
  }
  return result;
}

/* k×k 계수 행렬을 가우스 소거로 역행렬로 만들기, 아래는 가우스 소거법의 구현*/
static int invert_matrix(const unsigned char* in, unsigned char* out, unsigned short k) {
  if (k == 0 || k > RS_K) return -1;
  unsigned char tmp[RS_K * RS_K];
  memcpy(tmp, in, k * k);
  memset(out, 0, k * k);
  for (unsigned short i = 0; i < k; ++i) out[i * k + i] = 1;

  for (unsigned short col = 0; col < k; ++col) {
    unsigned short pivot = col;
    while (pivot < k && tmp[pivot * k + col] == 0) ++pivot;
    if (pivot == k) { return -1; }
    if (pivot != col) {
      for (unsigned short c = 0; c < k; ++c) {
        unsigned char t = tmp[col * k + c];
        tmp[col * k + c] = tmp[pivot * k + c];
        tmp[pivot * k + c] = t;
        t = out[col * k + c];
        out[col * k + c] = out[pivot * k + c];
        out[pivot * k + c] = t;
      }
    }
    unsigned char inv_pivot = gf256_inv(tmp[col * k + col]);
    for (unsigned short c = 0; c < k; ++c) {
      tmp[col * k + c] = gf256_mul(tmp[col * k + c], inv_pivot);
      out[col * k + c] = gf256_mul(out[col * k + c], inv_pivot);
    }
    for (unsigned short row = 0; row < k; ++row) {
      if (row == col) continue;
      unsigned char factor = tmp[row * k + col];
      if (factor == 0) continue;
      for (unsigned short c = 0; c < k; ++c) {
        tmp[row * k + c] = gf256_add(tmp[row * k + c],
                                     gf256_mul(factor, tmp[col * k + c]));
        out[row * k + c] = gf256_add(out[row * k + c],
                                     gf256_mul(factor, out[col * k + c]));
      }
    }
  }
  return 0;
}

/* RS 생성행렬(패리티 부분) 채우기: enc_matrix[r][c] = α^(shard_id*c) */
static int rs_code_init(rs_code_t* code, unsigned short n, unsigned short k) {
  if (!code) return -1;
  if (k == 0 || n == 0 || k > n || n > 255) return -1;
  gf256_init();
  code->n = n; code->k = k; code->alpha = 0x02;
  unsigned short parity = n - k;
  if (parity == 0) { code->enc_matrix = NULL; return 0; }
  unsigned char* m = enc_matrix;
  for (unsigned short r = 0; r < parity; ++r) {
    unsigned short shard_id = (unsigned short)(k + r);
    for (unsigned short c = 0; c < k; ++c) {
      unsigned short exp = (unsigned short)(shard_id * c);
      m[r * k + c] = gf256_pow_elem(code->alpha, exp);
    }
  }
  code->enc_matrix = m;
  return 0;
}

/* 데이터 심볼 k개를 패리티 (n−k)개로 확장 (행렬 곱) */
static int rs_encode_block(const rs_code_t* code,
                           const unsigned char* data_syms,
                           unsigned char* parity_syms,
                           unsigned int sym_cnt) {
  if (!code || !data_syms || !parity_syms) return -1;
  unsigned short k = code->k;                                       /* 데이터 샤드 개수 */
  unsigned short parity = (unsigned short)(code->n - code->k);      /* 패리티 샤드 개수 */
  const unsigned char* m = (const unsigned char*)code->enc_matrix;  /* 반더몬드 계수 행렬 (패리티×데이터) */
  if (parity == 0) return 0;
  for (unsigned short r = 0; r < parity; ++r) {                     /* 패리티 샤드 r */
    for (unsigned int s = 0; s < sym_cnt; ++s) {                    /* 심볼 인덱스 s */
      unsigned char acc = 0;                                        /* 선형결합 누산기 */
      for (unsigned short c = 0; c < k; ++c) {                      /* 데이터 샤드 c */
        unsigned char coeff = m[r * k + c];                         /* 계수행렬 요소 */
        unsigned char sym = data_syms[(size_t)c * sym_cnt + s];     /* 데이터 심볼 */
        acc = gf256_add(acc, gf256_mul(coeff, sym));                /* 계수*심볼 누적 */
      }
      parity_syms[(size_t)r * sym_cnt + s] = acc;                   /* 패리티 심볼 저장 */
    }
  }
  return 0;
}

/* 남은 샤드 k개로 원본 데이터 심볼 복구 (계수 행렬 역행렬 적용) */
static int rs_recover_block(const rs_code_t* code,
                            const unsigned short* avail_ids,
                            const unsigned char*  avail_syms,
                            unsigned char*        out_data,
                            unsigned int          sym_cnt) {
  if (!code || !avail_ids || !avail_syms || !out_data) return -1;
  unsigned short k = code->k;
  if (k == 0) return -1;
  if (k > RS_K) return -1;
  unsigned char mat[RS_K * RS_K];
  unsigned char inv[RS_K * RS_K];
  for (unsigned short row = 0; row < k; ++row) {                    /* 사용 가능한 샤드마다 */
    unsigned short shard_id = avail_ids[row];                       /* 샤드 ID */
    for (unsigned short col = 0; col < k; ++col) {
      if (shard_id < k) mat[row * k + col] = (col == shard_id) ? 1 : 0; /* 데이터 샤드는 단위행렬 */
      else mat[row * k + col] = gf256_pow_elem(code->alpha, (unsigned short)(shard_id * col)); /* 패리티 샤드는 계수 계산 */
    }
  }
  if (invert_matrix(mat, inv, k) != 0) { return -1; }               /* 계수행렬 역행렬 구하기 */
  for (unsigned short d = 0; d < k; ++d) {                          /* 복구할 데이터 샤드 d */
    for (unsigned int s = 0; s < sym_cnt; ++s) {                    /* 심볼 인덱스 s */
      unsigned char acc = 0;
      for (unsigned short j = 0; j < k; ++j) {                      /* 사용한 샤드 j */
        unsigned char coeff = inv[d * k + j];                       /* 역행렬 계수 */
        unsigned char sym = avail_syms[(size_t)j * sym_cnt + s];    /* 사용 샤드의 심볼 */
        acc = gf256_add(acc, gf256_mul(coeff, sym));                /* 계수*심볼 누적 */
      }
      out_data[(size_t)d * sym_cnt + s] = acc;                      /* d번째 데이터 샤드 심볼 복구 */
    }
  }
  return 0;
}

/* ---------- CACTUS 프로젝트 명령어 구현 ---------- */
typedef struct {
  const char*      input;
  const char*      out_dir;
  unsigned short   n, k;
  unsigned int     block_size;
  const char*      ext;
} rs_pack_opts_t;

#pragma pack(push, 1)
typedef struct {
  char     magic[4];   
  unsigned char  ver;
  unsigned short n, k;
  unsigned short shard_id;
  unsigned int   block_id;
  unsigned int   block_bytes;
  unsigned int   payload_len;
} rs_shard_hdr_t;
#pragma pack(pop)

/* 샤드 헤더 유효성 검사: 매직값, 버전, n/k, shard_id, 범위 체크 */
static int hdr_valid(const rs_shard_hdr_t* h, unsigned short expect_n, unsigned short expect_k) {
  if (!h) return 0;                                     /* 포인터 NULL 검사 */
  if (memcmp(h->magic, "RSAR", 4) != 0) return 0;       /* 매직 문자열 일치 확인 */
  if (h->ver != 1) return 0;                            /* 버전 1만 허용 */
  if (h->k == 0 || h->n == 0 || h->k > h->n) return 0;  /* k/n 범위 체크 */
  if (h->shard_id >= h->n) return 0;                    /* shard_id 범위 체크 */
  if (expect_n && h->n != expect_n) return 0;           /* 기대 n과 불일치 */
  if (expect_k && h->k != expect_k) return 0;           /* 기대 k와 불일치 */
  return 1;
}

static const char* base_name(const char* path) {
  const char* p = strrchr(path, PATH_SEP);
  return p ? (p + 1) : path;
}

static void shard_path(char* out, size_t out_sz, const char* dir, const char* fname, unsigned short shard_id, const char* ext) {
  snprintf(out, out_sz, "%s%c%s.part_%03u%s", dir, PATH_SEP, fname, (unsigned)shard_id, ext ? ext : ".txt");
}

/* 입력 파일을 읽고 RS 부호화 후 개별 샤드 파일로 저장
   - blk: 입력 파일을 block_size 단위로 순차 처리
   - bytes_this: 이번 블록 바이트 수
   - base_len / extra: k로 균등 분할할 때 기본 길이와 나머지
   - sym_cnt: 각 심볼(열)의 길이 = base_len(+1)
   - data_syms[k][sym_cnt], parity_syms[n-k][sym_cnt] 버퍼에 채운 뒤 헤더와 함께 파일로 기록 */
int rs_cmd_pack(const rs_pack_opts_t* opts) {
  if (!opts || !opts->input || opts->n == 0 || opts->k == 0 || opts->k > opts->n) return 1; /* 필수 입력/파라미터 검사 */
  unsigned int block_size = opts->block_size ? opts->block_size : 65536;

  FILE* in = NULL;
  if (fopen_s(&in, opts->input, "rb") != 0 || !in) return 1; /* 입력 파일 열기 실패 시 종료 */

  rs_code_t code;
  if (rs_code_init(&code, opts->n, opts->k) != 0) { fclose(in); return 1; }

  FILE* shard_fp[RS_N] = {0};

  const char* base = base_name(opts->input);
  char pathbuf[MAX_PATH_LEN];
  for (unsigned short i = 0; i < opts->n; ++i) {
    shard_path(pathbuf, sizeof(pathbuf), opts->out_dir ? opts->out_dir : ".", base, i, opts->ext ? opts->ext : ".txt");
    if (fopen_s(&shard_fp[i], pathbuf, "wb") != 0 || !shard_fp[i]) { /* 샤드 파일 열기 실패 시 정리 후 종료 */
      fclose(in);
      for (unsigned short j = 0; j <= i; ++j) if (shard_fp[j]) fclose(shard_fp[j]);
      return 1;
    }
  }

  unsigned int blk = 0;
  int failed = 0;
  while (1) {
    size_t got = fread(in_block, 1, block_size, in); /* 블록 단위 읽기 */
    if (got == 0) break;                              /* 더 이상 읽을 데이터가 없으면 종료 */
    unsigned int bytes_this = (unsigned int)got;               /* 이번 블록 원본 바이트 수 */
    unsigned int base_len = bytes_this / opts->k;              /* k개로 균등 분할한 기본 길이 */
    unsigned int extra = bytes_this % opts->k;                 /* 나머지(앞쪽 샤드가 +1 바이트씩 가짐) */
    unsigned int sym_cnt = base_len + (extra ? 1u : 0u);       /* 한 열(sym) 길이 */
    if (sym_cnt == 0) sym_cnt = 1;                             /* 빈 블록 방지 */
    if (sym_cnt > SYM_MAX) { fprintf(stderr, "pack: block too large\n"); failed = 1; break; } /* 정적 버퍼 한계 초과 */

    /* 데이터 심볼 배열을 0으로 초기화 후 원본을 k개로 나눠 채움 */
    memset(data_syms, 0, (size_t)opts->k * sym_cnt);           /* 데이터 심볼 버퍼 초기화 */
    const unsigned char* src = in_block;
    for (unsigned short s = 0; s < opts->k; ++s) {
      unsigned int len = base_len + (s < extra ? 1u : 0u);     /* shard s가 가져갈 길이 */
      memcpy(data_syms + (size_t)s * sym_cnt, src, len);       /* data_syms[s][0..len) 채움 */
      src += len;                                              /* 다음 조각 위치로 이동 */
    }

    if (opts->n > opts->k) {
      if (rs_encode_block(&code, data_syms, parity_syms, sym_cnt) != 0) { break; } /* 패리티 생성 실패 시 중단 */
    }

    /* 각 샤드 s에 대해 헤더와 payload(데이터 또는 패리티) 기록 */
    for (unsigned short s = 0; s < opts->n; ++s) {
      const unsigned char* payload;
      unsigned int plen;
      if (s < opts->k) { plen = base_len + (s < extra ? 1u : 0u); payload = data_syms + (size_t)s * sym_cnt; }
      else { plen = sym_cnt; payload = parity_syms + (size_t)(s - opts->k) * sym_cnt; }
      rs_shard_hdr_t hdr;
      memcpy(hdr.magic, "RSAR", 4);
      hdr.ver = 1;
      hdr.n = opts->n;
      hdr.k = opts->k;
      hdr.shard_id = s;
      hdr.block_id = blk;
      hdr.block_bytes = bytes_this;
      hdr.payload_len = plen;
      fwrite(&hdr, 1, sizeof(hdr), shard_fp[s]);
      if (plen > 0) fwrite(payload, 1, plen, shard_fp[s]);
    }
  }

  for (unsigned short s = 0; s < opts->n; ++s) if (shard_fp[s]) fclose(shard_fp[s]);
  fclose(in);
  if (!failed) printf("pack complete: %u shards written\n", (unsigned)opts->n);
  return failed ? 1 : 0;
}

/* 샤드 파일 중 남아있는 것들을 모아 원본을 복구
   - kept: 실제 열 수 있는 샤드 파일 개수 (헤더 검사까지 통과)
   - 각 루프에서 blk 번호에 맞는 샤드 헤더/페이로드를 읽어 avail_syms[]에 모음
   - avail_ids[]: 현재 사용된 샤드의 shard_id 목록 (길이 RS_K)
   - sym_cnt: 이번 블록에서 한 열이 가지는 바이트 길이
   - recovered[]: 역연산 결과로 얻은 데이터 심볼 k개를 담는 버퍼
   - base_len/extra를 이용해 recovered를 원래 순서대로 out에 기록 */
int rs_cmd_unpack(const char* shards_dir, const char* output_path) {
  if (!shards_dir || !output_path) return 1;

  FILE* shard_fp[RS_N] = {0};                          /* 열어둔 샤드 파일 포인터 */
  unsigned short ref_n = RS_N, ref_k = RS_K;           /* 기대하는 n, k */
  size_t kept = 0;                                     /* 헤더 검증까지 통과한 샤드 수 */
  char pathbuf[MAX_PATH_LEN];
  for (unsigned short i = 0; i < RS_N; ++i) {
    snprintf(pathbuf, sizeof(pathbuf), "%s%c%s.part_%03u.txt", shards_dir, PATH_SEP, base_name(INPUT_PATH), i);
    FILE* fp = NULL;
    if (fopen_s(&fp, pathbuf, "rb") != 0 || !fp) continue;                /* 샤드 파일이 없으면 스킵 */
    rs_shard_hdr_t hdr;
    if (fread(&hdr, 1, sizeof(hdr), fp) != sizeof(hdr)) { fclose(fp); continue; } /* 헤더 읽기 실패 */
    if (!hdr_valid(&hdr, ref_n, ref_k) || hdr.shard_id != i) { fclose(fp); continue; } /* 매직/버전/n/k/순번 검증 */
    fseek(fp, 0, SEEK_SET);                                              /* 다시 처음부터 읽도록 되감기 */
    shard_fp[kept] = fp;                                                 /* 사용 가능한 샤드로 등록 */
    ++kept;
  }
  if (kept < RS_K) {
    fprintf(stderr, "unpack: usable shards %zu below k=%u\n", kept, (unsigned)RS_K);
    for (size_t i = 0; i < kept; ++i) if (shard_fp[i]) fclose(shard_fp[i]);
    return 1;
  }

  rs_code_t code;
  if (rs_code_init(&code, ref_n, ref_k) != 0) {
    for (size_t i = 0; i < kept; ++i) if (shard_fp[i]) fclose(shard_fp[i]);
    return 1;
  }

  FILE* out = NULL;
  if (fopen_s(&out, output_path, "wb") != 0 || !out) {
    perror("unpack: fopen output");
    for (size_t i = 0; i < kept; ++i) if (shard_fp[i]) fclose(shard_fp[i]);
    return 1;
  }

  unsigned short avail_ids[RS_K];
  unsigned int blk = 0; /* 블록 번호 (0부터 증가) */
  int status = 0;

  while (1) {
    unsigned int block_bytes = 0; /* 이번 블록의 총 바이트 수 (첫 샤드 헤더 기준으로 고정) */
    unsigned int sym_cnt = 0;     /* 한 열의 길이 = ceil(block_bytes / k) */
    size_t used = 0;              /* 이번 블록에서 실제로 사용한 샤드 수 */

    for (size_t i = 0; i < kept && used < RS_K; ++i) {
      if (!shard_fp[i]) continue;                                   /* 이미 닫힌 샤드면 스킵 */
      rs_shard_hdr_t hdr;
      size_t got_hdr = fread(&hdr, 1, sizeof(hdr), shard_fp[i]);     /* 헤더 읽기 */
      if (got_hdr == 0) { fclose(shard_fp[i]); shard_fp[i] = NULL; continue; } /* EOF 시 닫고 스킵 */
      if (got_hdr != sizeof(hdr) || !hdr_valid(&hdr, ref_n, ref_k) || hdr.block_id != blk) { fclose(shard_fp[i]); shard_fp[i] = NULL; continue; } /* 헤더 검증 실패 */
      if (hdr.block_bytes == 0) { fclose(shard_fp[i]); shard_fp[i] = NULL; continue; } /* 빈 블록이면 스킵 */
      block_bytes = block_bytes ? block_bytes : hdr.block_bytes;     /* 첫 블록 크기 기억 */
      if (hdr.block_bytes != block_bytes) { fclose(shard_fp[i]); shard_fp[i] = NULL; continue; } /* 블록 크기 불일치 */
      sym_cnt = (block_bytes + ref_k - 1) / ref_k;
      if (sym_cnt == 0) sym_cnt = 1;
      if (sym_cnt > SYM_MAX) { fclose(shard_fp[i]); shard_fp[i] = NULL; status = 1; break; } /* 버퍼 초과 */
      if (hdr.payload_len > sym_cnt) { fclose(shard_fp[i]); shard_fp[i] = NULL; continue; } /* 페이로드 길이 이상 */

      /* 샤드 i의 payload를 avail_syms[used] 위치에 복사 */
      size_t rd = fread(avail_syms + (size_t)used * sym_cnt, 1, hdr.payload_len, shard_fp[i]); /* payload를 avail_syms[used] 위치에 적재 */
      if (rd != hdr.payload_len) { fclose(shard_fp[i]); shard_fp[i] = NULL; continue; }
      if (hdr.payload_len < sym_cnt) memset(avail_syms + (size_t)used * sym_cnt + hdr.payload_len, 0, sym_cnt - hdr.payload_len);
      avail_ids[used] = hdr.shard_id;
      ++used;
    }

    if (status != 0) break;
    if (used == 0) break; /* 읽을 수 있는 샤드가 더 없으면 종료 */
    if (used < RS_K) { fprintf(stderr, "unpack: block %u missing shards\n", blk); status = 1; break; }

    /* k개 샤드로 역연산 수행 → recovered 버퍼에 데이터 심볼 k개 채움 */
    if (rs_recover_block(&code, avail_ids, avail_syms, recovered, sym_cnt) != 0) { status = 1; break; }
    unsigned int base_len = block_bytes / ref_k; /* 각 데이터 샤드의 기본 길이 */
    unsigned int extra = block_bytes % ref_k;    /* 앞에서 extra개 샤드는 1바이트씩 더 가짐 */
    /* recovered에 담긴 각 데이터 샤드 s를 길이(len)만큼 순서대로 파일에 기록 */
    for (unsigned short s = 0; s < ref_k; ++s) {
      unsigned int len = base_len + (s < extra ? 1u : 0u); /* 샤드 s의 실제 길이 */
      fwrite(recovered + (size_t)s * sym_cnt, 1, len, out); /* 샤드 s를 출력 파일에 이어쓰기 */
    }
    ++blk;
  }

  fclose(out);
  for (size_t i = 0; i < kept; ++i) if (shard_fp[i]) fclose(shard_fp[i]);
  return status;
}

/* ---------- Interactive mode ---------- */
/* 개행 제거 유틸 */
static void trim_newline(char* s) {
  if (!s) return;
  size_t len = strlen(s);
  if (len && s[len - 1] == '\n') s[len - 1] = '\0';
}

/*입력(gets_s) */
static int read_line(char* buf, size_t buf_sz) {
  if (!buf || buf_sz == 0) return -1;
  if (!gets_s(buf, buf_sz)) return -1;
  trim_newline(buf);
  return 0;
}

/* 문자열 복사 */
static void copy_str(char* dst, size_t dst_sz, const char* src) {
  if (!dst || dst_sz == 0 || !src) return;
  strcpy_s(dst, dst_sz, src);
}

/* 모드 1: 터미널에서 텍스트를 입력받아 secret.txt → 샤드 파일 생성 */
static int interactive_pack(void) {
  char secret[4096];
  printf("Enter secret (single line, will be saved to %s):\n> ", INPUT_PATH);
  if (read_line(secret, sizeof(secret)) != 0) return 1;
  FILE* f = NULL;
  if (fopen_s(&f, INPUT_PATH, "wb") != 0 || !f) { perror("write secret"); return 1; }
  fputs(secret, f);
  fclose(f);

  rs_pack_opts_t opts = { INPUT_PATH, SHARDS_DIR, RS_N, RS_K, RS_BLOCK_SIZE, ".txt" };
  return rs_cmd_pack(&opts);
}

/* 모드 2: shards 디렉터리에서 복구하여 restored.txt 생성 */
static int interactive_unpack(void) {
  printf("Unpacking from %s to %s...\n", SHARDS_DIR, OUTPUT_PATH);
  return rs_cmd_unpack(SHARDS_DIR, OUTPUT_PATH);
}

/* 메뉴 제공: 1) pack 2) unpack */
int main(int argc, char** argv) {
  (void)argc; (void)argv;
  printf("Interactive mode:\n 1) pack (enter secret → shards)\n 2) unpack (shards → restored)\nSelect [1/2]: ");
  int sel = 0;
  if (scanf_s("%d", &sel) != 1) return 1;
  /* 남은 개행 문자를 버퍼에서 제거 */
  int c; while ((c = getchar()) != '\n' && c != EOF) {}
  if (sel == 1) return interactive_pack();
  if (sel == 2) return interactive_unpack();
  return 1;
}
