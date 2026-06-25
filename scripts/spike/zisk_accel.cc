// zisk_accel.cc — SPIKE extension replicating ziskemu's custom-CSR crypto
// accelerators, so the codegen stateless_guest ELF runs on SPIKE byte-for-byte
// identically to ziskemu. Goal: speed (no per-run ROM transpile).
//
// The guest triggers each accelerator with `csrrs x0, <csr>, <rsX>` where the
// rsX register holds a param pointer. SPIKE routes the csrrs to a registered
// csr_t whose unlogged_write(val) gets val = (old_csr | rsX) = rsX (old=0).
//
// MVP accelerators (run on every non-precompile block):
//   0x800  Keccak-f[1600]  : a0 -> 25*u64 state (200B), permute IN-PLACE
//   0x802  arith256_mod    : t0 -> 5 ptrs {a,b,c,module,d}, each ->4*u64 LE;
//                            d = (a*b + c) mod module  (write 4*u64 to *d)
//   0x805  sha256 compress : a0 -> 2 ptrs {state(4*u64=8*u32), input(64B block)};
//                            standard SHA-256 compression, state IN-PLACE
//
// Precompile-only CSRs (0x806-0x80d bn254/bls12 curve/arith, 0x819
// blake2b-round, etc.) are TODO — blocks needing them are on the guest's
// conservative-reject frontier unless their lower-level field ops are
// implemented here. Adding one = another AccelCsr subclass.
//
// All multi-limb values are little-endian arrays of u64 (zisk convention).

#include <sys/syscall.h>
#include "extension.h"
#include "processor.h"
#include "mmu.h"
#if defined(__APPLE__)
#include <boost/multiprecision/cpp_int.hpp>
#else
#include <openssl/bn.h>
#endif
#include <cstdint>
#include <cstring>
#if !defined(__APPLE__)
#include <memory>
#endif
#include <vector>

#if defined(__APPLE__)
using boost::multiprecision::uint512_t;
using boost::multiprecision::cpp_int;
#endif

// ---- guest-memory helpers (via the processor MMU) --------------------------
static inline uint64_t gload(processor_t* p, reg_t addr) {
  return p->get_mmu()->load<uint64_t>(addr);
}
static inline void gstore(processor_t* p, reg_t addr, uint64_t v) {
  p->get_mmu()->store<uint64_t>(addr, v);
}
#if !defined(__APPLE__)
struct bn_deleter { void operator()(BIGNUM* v) const { BN_free(v); } };
struct bn_ctx_deleter { void operator()(BN_CTX* v) const { BN_CTX_free(v); } };
using bn_ptr = std::unique_ptr<BIGNUM, bn_deleter>;
using bn_ctx_ptr = std::unique_ptr<BN_CTX, bn_ctx_deleter>;

static bn_ptr make_bn() { return bn_ptr(BN_new()); }
static bn_ctx_ptr make_ctx() { return bn_ctx_ptr(BN_CTX_new()); }
#endif
// read/write n little-endian u64 limbs at addr
#if defined(__APPLE__)
static uint512_t read_bigint(processor_t* p, reg_t addr, int n) {
  uint512_t acc = 0;
  for (int i = n - 1; i >= 0; --i) { acc <<= 64; acc |= gload(p, addr + 8 * i); }
  return acc;
}
static void write_bigint(processor_t* p, reg_t addr, uint512_t v, int n) {
  for (int i = 0; i < n; ++i) {
    uint64_t limb = (uint64_t)(v & 0xffffffffffffffffULL);
    gstore(p, addr + 8 * i, limb);
    v >>= 64;
  }
}
#else
// Read/write n little-endian u64 limbs as a positive BIGNUM.
static bn_ptr read_bigint(processor_t* p, reg_t addr, int n) {
  std::vector<uint8_t> be((size_t)n * 8);
  for (int i = 0; i < n; ++i) {
    uint64_t limb = gload(p, addr + 8 * i);
    size_t off = (size_t)(n - 1 - i) * 8;
    for (int j = 0; j < 8; ++j) be[off + j] = (uint8_t)(limb >> (56 - 8 * j));
  }
  return bn_ptr(BN_bin2bn(be.data(), (int)be.size(), nullptr));
}
static void write_bigint(processor_t* p, reg_t addr, const BIGNUM* v, int n) {
  std::vector<uint8_t> be((size_t)n * 8);
  BN_bn2binpad(v, be.data(), (int)be.size());
  for (int i = 0; i < n; ++i) {
    size_t off = (size_t)(n - 1 - i) * 8;
    uint64_t limb = 0;
    for (int j = 0; j < 8; ++j) limb = (limb << 8) | be[off + j];
    gstore(p, addr + 8 * i, limb);
  }
}
#endif

// ---- Keccak-f[1600] (standard, public-domain constants) --------------------
static const uint64_t KECCAK_RC[24] = {
  0x0000000000000001ULL,0x0000000000008082ULL,0x800000000000808aULL,0x8000000080008000ULL,
  0x000000000000808bULL,0x0000000080000001ULL,0x8000000080008081ULL,0x8000000000008009ULL,
  0x000000000000008aULL,0x0000000000000088ULL,0x0000000080008009ULL,0x000000008000000aULL,
  0x000000008000808bULL,0x800000000000008bULL,0x8000000000008089ULL,0x8000000000008003ULL,
  0x8000000000008002ULL,0x8000000000000080ULL,0x000000000000800aULL,0x800000008000000aULL,
  0x8000000080008081ULL,0x8000000000008080ULL,0x0000000080000001ULL,0x8000000080008008ULL};
static const int KECCAK_ROT[24] = {1,3,6,10,15,21,28,36,45,55,2,14,27,41,56,8,25,43,62,18,39,61,20,44};
static const int KECCAK_PI[24]  = {10,7,11,17,18,3,5,16,8,21,24,4,15,23,19,13,12,2,20,14,22,9,6,1};
static inline uint64_t rotl64(uint64_t x, int n){ return (x<<n)|(x>>(64-n)); }
static void keccakf(uint64_t st[25]) {
  for (int round = 0; round < 24; ++round) {
    uint64_t bc[5];
    for (int i=0;i<5;++i) bc[i]=st[i]^st[i+5]^st[i+10]^st[i+15]^st[i+20];
    for (int i=0;i<5;++i){ uint64_t t=bc[(i+4)%5]^rotl64(bc[(i+1)%5],1);
      for (int j=0;j<25;j+=5) st[j+i]^=t; }
    uint64_t t=st[1];
    for (int i=0;i<24;++i){ int j=KECCAK_PI[i]; uint64_t tmp=st[j];
      st[j]=rotl64(t,KECCAK_ROT[i]); t=tmp; }
    for (int j=0;j<25;j+=5){ uint64_t b[5];
      for(int i=0;i<5;++i) b[i]=st[j+i];
      for(int i=0;i<5;++i) st[j+i]^=(~b[(i+1)%5])&b[(i+2)%5]; }
    st[0]^=KECCAK_RC[round];
  }
}

// ---- SHA-256 compression (standard FIPS 180-4) -----------------------------
static const uint32_t SHA256_K[64] = {
  0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
  0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
  0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
  0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
  0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
  0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
  0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
  0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2};
static inline uint32_t rotr32(uint32_t x,int n){return (x>>n)|(x<<(32-n));}
static void sha256_compress(uint32_t st[8], const uint8_t block[64]) {
  uint32_t w[64];
  for (int i=0;i<16;++i)
    w[i]=((uint32_t)block[4*i]<<24)|((uint32_t)block[4*i+1]<<16)|
         ((uint32_t)block[4*i+2]<<8)|((uint32_t)block[4*i+3]);
  for (int i=16;i<64;++i){
    uint32_t s0=rotr32(w[i-15],7)^rotr32(w[i-15],18)^(w[i-15]>>3);
    uint32_t s1=rotr32(w[i-2],17)^rotr32(w[i-2],19)^(w[i-2]>>10);
    w[i]=w[i-16]+s0+w[i-7]+s1;
  }
  uint32_t a=st[0],b=st[1],c=st[2],d=st[3],e=st[4],f=st[5],g=st[6],h=st[7];
  for (int i=0;i<64;++i){
    uint32_t S1=rotr32(e,6)^rotr32(e,11)^rotr32(e,25);
    uint32_t ch=(e&f)^((~e)&g);
    uint32_t t1=h+S1+ch+SHA256_K[i]+w[i];
    uint32_t S0=rotr32(a,2)^rotr32(a,13)^rotr32(a,22);
    uint32_t maj=(a&b)^(a&c)^(b&c);
    uint32_t t2=S0+maj;
    h=g;g=f;f=e;e=d+t1;d=c;c=b;b=a;a=t1+t2;
  }
  st[0]+=a;st[1]+=b;st[2]+=c;st[3]+=d;st[4]+=e;st[5]+=f;st[6]+=g;st[7]+=h;
}

// ---- secp256k1 affine point ops (CSR 0x803 add, 0x804 double) --------------
// Field prime p = 2^256 - 2^32 - 977. Points are affine x||y, each 4 LE u64.
// The guest software wrapper handles infinity / p1==±p2 / y==0; the accelerator
// assumes finite, on-curve, distinct points (matches ziskemu's naked formula).
#if defined(__APPLE__)
static const cpp_int SECP_P("0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F");
static inline cpp_int fmod(cpp_int x){ x %= SECP_P; if (x < 0) x += SECP_P; return x; }
static inline cpp_int finv(const cpp_int& a){ return powm(fmod(a), SECP_P - 2, SECP_P); }
static cpp_int rd256(processor_t* p, reg_t a){
  cpp_int v = 0; for (int i = 3; i >= 0; --i){ v <<= 64; v |= (cpp_int)gload(p, a + 8*i); } return v;
}
static void wr256(processor_t* p, reg_t a, cpp_int v){
  v = fmod(v);
  for (int i = 0; i < 4; ++i){ uint64_t l = (v & (cpp_int)0xffffffffffffffffULL).convert_to<uint64_t>();
    gstore(p, a + 8*i, l); v >>= 64; }
}
#else
static const BIGNUM* secp_p() {
  static BIGNUM* p = nullptr;
  if (!p) BN_hex2bn(&p, "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F");
  return p;
}
static bn_ptr fmod_bn(const BIGNUM* x, BN_CTX* ctx) {
  bn_ptr r = make_bn();
  BN_nnmod(r.get(), x, secp_p(), ctx);
  return r;
}
static bn_ptr fsub(const BIGNUM* a, const BIGNUM* b, BN_CTX* ctx) {
  bn_ptr r = make_bn();
  BN_mod_sub(r.get(), a, b, secp_p(), ctx);
  return r;
}
static bn_ptr fmul(const BIGNUM* a, const BIGNUM* b, BN_CTX* ctx) {
  bn_ptr r = make_bn();
  BN_mod_mul(r.get(), a, b, secp_p(), ctx);
  return r;
}
static bn_ptr finv(const BIGNUM* a, BN_CTX* ctx) {
  bn_ptr aa = fmod_bn(a, ctx);
  return bn_ptr(BN_mod_inverse(nullptr, aa.get(), secp_p(), ctx));
}
static bn_ptr rd256(processor_t* p, reg_t a) { return read_bigint(p, a, 4); }
static void wr256(processor_t* p, reg_t a, const BIGNUM* v, BN_CTX* ctx) {
  bn_ptr vv = fmod_bn(v, ctx);
  write_bigint(p, a, vv.get(), 4);
}

#endif

// ---- BLS12-381 Fp2 ops (CSR 0x80e/0x80f/0x810) -----------------------------
// Fp2 elements are c0 || c1, each 6 little-endian u64 limbs. The operation
// mutates f1 in-place: f1 += f2, f1 -= f2, or f1 *= f2 over u^2 = -1.
#if defined(__APPLE__)
static const cpp_int BLS12_P(
  "0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf"
  "6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab");
static inline cpp_int bls_mod(cpp_int x){ x %= BLS12_P; if (x < 0) x += BLS12_P; return x; }
static inline cpp_int bls_inv(const cpp_int& a){ return powm(bls_mod(a), BLS12_P - 2, BLS12_P); }
static cpp_int rd_limbs(processor_t* p, reg_t a, int n) {
  cpp_int v = 0;
  for (int i = n - 1; i >= 0; --i) { v <<= 64; v |= (cpp_int)gload(p, a + 8*i); }
  return v;
}
static void wr_limbs(processor_t* p, reg_t a, cpp_int v, int n) {
  v = bls_mod(v);
  for (int i = 0; i < n; ++i) {
    uint64_t l = (v & (cpp_int)0xffffffffffffffffULL).convert_to<uint64_t>();
    gstore(p, a + 8*i, l);
    v >>= 64;
  }
}
#else
static const BIGNUM* bls12_p() {
  static BIGNUM* p = nullptr;
  if (!p) BN_hex2bn(&p,
      "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf"
      "6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab");
  return p;
}
static bn_ptr bls_add(const BIGNUM* a, const BIGNUM* b, BN_CTX* ctx) {
  bn_ptr r = make_bn();
  BN_mod_add(r.get(), a, b, bls12_p(), ctx);
  return r;
}
static bn_ptr bls_sub(const BIGNUM* a, const BIGNUM* b, BN_CTX* ctx) {
  bn_ptr r = make_bn();
  BN_mod_sub(r.get(), a, b, bls12_p(), ctx);
  return r;
}
static bn_ptr bls_mul(const BIGNUM* a, const BIGNUM* b, BN_CTX* ctx) {
  bn_ptr r = make_bn();
  BN_mod_mul(r.get(), a, b, bls12_p(), ctx);
  return r;
}
static bn_ptr bls_inv(const BIGNUM* a, BN_CTX* ctx) {
  return bn_ptr(BN_mod_inverse(nullptr, a, bls12_p(), ctx));
}
#endif

// ---- BN254 (alt_bn128) field ops (CSR 0x806/0x807 curve, 0x808-0x80a Fp2) ---
// Field prime p = 21888242871839275222246405745257275088548364400416034343698204186575808495617.
// Curve G1 points are affine x||y, each 4 LE u64 (BN254 is 254-bit; fits 256 bits).
// Fp2 = Fp[u]/(u^2+1): elements c0||c1, each 4 LE u64 (32 bytes per component).
#if defined(__APPLE__)
static const cpp_int BN254_P("0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47");
static inline cpp_int bn254_mod(cpp_int x){ x %= BN254_P; if (x < 0) x += BN254_P; return x; }
static inline cpp_int bn254_inv(const cpp_int& a){ return powm(bn254_mod(a), BN254_P - 2, BN254_P); }
static void wr_limbs254(processor_t* p, reg_t a, cpp_int v, int n) {
  v = bn254_mod(v);
  for (int i = 0; i < n; ++i) {
    uint64_t l = (v & (cpp_int)0xffffffffffffffffULL).convert_to<uint64_t>();
    gstore(p, a + 8*i, l);
    v >>= 64;
  }
}
#else
static const BIGNUM* bn254_p() {
  static BIGNUM* p = nullptr;
  if (!p) BN_hex2bn(&p, "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47");
  return p;
}
static bn_ptr bn254_add(const BIGNUM* a, const BIGNUM* b, BN_CTX* ctx) {
  bn_ptr r = make_bn(); BN_mod_add(r.get(), a, b, bn254_p(), ctx); return r;
}
static bn_ptr bn254_sub(const BIGNUM* a, const BIGNUM* b, BN_CTX* ctx) {
  bn_ptr r = make_bn(); BN_mod_sub(r.get(), a, b, bn254_p(), ctx); return r;
}
static bn_ptr bn254_mul(const BIGNUM* a, const BIGNUM* b, BN_CTX* ctx) {
  bn_ptr r = make_bn(); BN_mod_mul(r.get(), a, b, bn254_p(), ctx); return r;
}
static bn_ptr bn254_inv(const BIGNUM* a, BN_CTX* ctx) {
  return bn_ptr(BN_mod_inverse(nullptr, a, bn254_p(), ctx));
}
#endif

// ---- accelerator CSR base --------------------------------------------------
class accel_csr_t : public csr_t {
 public:
  accel_csr_t(processor_t* p, reg_t addr): csr_t(p, addr) {}
  void verify_permissions(insn_t, bool) const override {}   // always allow
  reg_t read() const noexcept override { return 0; }
};

// 0x800: Keccak-f[1600] in place on 25*u64 at param.
class keccak_csr_t : public accel_csr_t {
 public:
  using accel_csr_t::accel_csr_t;
  bool unlogged_write(const reg_t param) noexcept override {
    uint64_t st[25];
    for (int i=0;i<25;++i) st[i]=gload(proc, param + 8*i);
    keccakf(st);
    for (int i=0;i<25;++i) gstore(proc, param + 8*i, st[i]);
    return false;
  }
};

// 0x802: arith256_mod  d = (a*b + c) mod module.  param -> 5 ptrs (LE 4*u64 each).
class arith256_csr_t : public accel_csr_t {
 public:
  using accel_csr_t::accel_csr_t;
  bool unlogged_write(const reg_t param) noexcept override {
    reg_t pa=gload(proc,param+0), pb=gload(proc,param+8), pc=gload(proc,param+16);
    reg_t pm=gload(proc,param+24), pd=gload(proc,param+32);
#if defined(__APPLE__)
    uint512_t a=read_bigint(proc,pa,4), b=read_bigint(proc,pb,4);
    uint512_t c=read_bigint(proc,pc,4), m=read_bigint(proc,pm,4);
    uint512_t d = (a*b + c) % m;          // module is guaranteed nonzero by guest
    write_bigint(proc, pd, d, 4);
#else
    bn_ctx_ptr ctx = make_ctx();
    bn_ptr a=read_bigint(proc,pa,4), b=read_bigint(proc,pb,4);
    bn_ptr c=read_bigint(proc,pc,4), m=read_bigint(proc,pm,4);
    bn_ptr ab = make_bn(), sum = make_bn(), d = make_bn();
    BN_mul(ab.get(), a.get(), b.get(), ctx.get());
    BN_add(sum.get(), ab.get(), c.get());
    BN_mod(d.get(), sum.get(), m.get(), ctx.get()); // module is guaranteed nonzero by guest
    write_bigint(proc, pd, d.get(), 4);
#endif
    return false;
  }
};

// 0x805: SHA-256 compress one block.  param -> 2 ptrs {state(4*u64=8*u32), input(64B)}.
class sha256_csr_t : public accel_csr_t {
 public:
  using accel_csr_t::accel_csr_t;
  bool unlogged_write(const reg_t param) noexcept override {
    reg_t pstate=gload(proc,param+0), pin=gload(proc,param+8);
    uint32_t st[8];
    for (int i=0;i<4;++i){ uint64_t w=gload(proc,pstate+8*i);
      st[2*i]=(uint32_t)w; st[2*i+1]=(uint32_t)(w>>32); }   // LE-host u64 -> 2*u32
    uint8_t block[64];
    for (int i=0;i<8;++i){ uint64_t w=gload(proc,pin+8*i);
      memcpy(block+8*i,&w,8); }                              // raw bytes
    sha256_compress(st, block);
    for (int i=0;i<4;++i){ uint64_t w=((uint64_t)st[2*i+1]<<32)|st[2*i];
      gstore(proc,pstate+8*i,w); }
    return false;
  }
};

// 0x804: secp256k1 point double, in-place on the 8-limb point (x||y) at param (t0).
class secp_dbl_csr_t : public accel_csr_t {
 public:
  using accel_csr_t::accel_csr_t;
  bool unlogged_write(const reg_t param) noexcept override {
#if defined(__APPLE__)
    cpp_int x = rd256(proc, param), y = rd256(proc, param + 32);
    cpp_int s  = fmod(3 * x % SECP_P * x % SECP_P * finv(2 * y) % SECP_P);
    cpp_int xr = fmod(s * s - 2 * x);
    cpp_int yr = fmod(s * (x - xr) - y);
    wr256(proc, param, xr); wr256(proc, param + 32, yr);
#else
    bn_ctx_ptr ctx = make_ctx();
    bn_ptr x = rd256(proc, param), y = rd256(proc, param + 32);
    bn_ptr three = make_bn(), two = make_bn();
    BN_set_word(three.get(), 3);
    BN_set_word(two.get(), 2);
    bn_ptr x2 = fmul(x.get(), x.get(), ctx.get());
    bn_ptr num = fmul(three.get(), x2.get(), ctx.get());
    bn_ptr denom = fmul(two.get(), y.get(), ctx.get());
    bn_ptr inv = finv(denom.get(), ctx.get());
    bn_ptr slope = fmul(num.get(), inv.get(), ctx.get());
    bn_ptr slope2 = fmul(slope.get(), slope.get(), ctx.get());
    bn_ptr two_x = fmul(two.get(), x.get(), ctx.get());
    bn_ptr xr = fsub(slope2.get(), two_x.get(), ctx.get());
    bn_ptr x_minus_xr = fsub(x.get(), xr.get(), ctx.get());
    bn_ptr sy = fmul(slope.get(), x_minus_xr.get(), ctx.get());
    bn_ptr yr = fsub(sy.get(), y.get(), ctx.get());
    wr256(proc, param, xr.get(), ctx.get()); wr256(proc, param + 32, yr.get(), ctx.get());
#endif
    return false;
  }
};

// 0x803: secp256k1 point add. param (t0) -> {ptr p1, ptr p2}; result in-place on *p1.
class secp_add_csr_t : public accel_csr_t {
 public:
  using accel_csr_t::accel_csr_t;
  bool unlogged_write(const reg_t param) noexcept override {
    reg_t p1 = gload(proc, param + 0), p2 = gload(proc, param + 8);
#if defined(__APPLE__)
    cpp_int x1 = rd256(proc, p1), y1 = rd256(proc, p1 + 32);
    cpp_int x2 = rd256(proc, p2), y2 = rd256(proc, p2 + 32);
    cpp_int s  = fmod((y2 - y1) * finv(x2 - x1));
    cpp_int xr = fmod(s * s - x1 - x2);
    cpp_int yr = fmod(s * (x1 - xr) - y1);
    wr256(proc, p1, xr); wr256(proc, p1 + 32, yr);
#else
    bn_ctx_ptr ctx = make_ctx();
    bn_ptr x1 = rd256(proc, p1), y1 = rd256(proc, p1 + 32);
    bn_ptr x2 = rd256(proc, p2), y2 = rd256(proc, p2 + 32);
    bn_ptr dy = fsub(y2.get(), y1.get(), ctx.get());
    bn_ptr dx = fsub(x2.get(), x1.get(), ctx.get());
    bn_ptr inv = finv(dx.get(), ctx.get());
    bn_ptr slope = fmul(dy.get(), inv.get(), ctx.get());
    bn_ptr slope2 = fmul(slope.get(), slope.get(), ctx.get());
    bn_ptr tmp = fsub(slope2.get(), x1.get(), ctx.get());
    bn_ptr xr = fsub(tmp.get(), x2.get(), ctx.get());
    bn_ptr x1_minus_xr = fsub(x1.get(), xr.get(), ctx.get());
    bn_ptr sy = fmul(slope.get(), x1_minus_xr.get(), ctx.get());
    bn_ptr yr = fsub(sy.get(), y1.get(), ctx.get());
    wr256(proc, p1, xr.get(), ctx.get()); wr256(proc, p1 + 32, yr.get(), ctx.get());
#endif
    return false;
  }
};

class bls12_fp2_csr_t : public accel_csr_t {
 public:
  enum op_t { add, sub, mul };
  bls12_fp2_csr_t(processor_t* p, reg_t addr, op_t op): accel_csr_t(p, addr), op(op) {}
  bool unlogged_write(const reg_t param) noexcept override {
    reg_t f1 = gload(proc, param + 0), f2 = gload(proc, param + 8);
#if defined(__APPLE__)
    cpp_int a0 = rd_limbs(proc, f1, 6), a1 = rd_limbs(proc, f1 + 48, 6);
    cpp_int b0 = rd_limbs(proc, f2, 6), b1 = rd_limbs(proc, f2 + 48, 6);
    cpp_int r0 = 0, r1 = 0;
    if (op == add) {
      r0 = a0 + b0;
      r1 = a1 + b1;
    } else if (op == sub) {
      r0 = a0 - b0;
      r1 = a1 - b1;
    } else {
      r0 = a0 * b0 - a1 * b1;
      r1 = a0 * b1 + a1 * b0;
    }
    wr_limbs(proc, f1, r0, 6);
    wr_limbs(proc, f1 + 48, r1, 6);
#else
    bn_ctx_ptr ctx = make_ctx();
    bn_ptr a0 = read_bigint(proc, f1, 6), a1 = read_bigint(proc, f1 + 48, 6);
    bn_ptr b0 = read_bigint(proc, f2, 6), b1 = read_bigint(proc, f2 + 48, 6);
    bn_ptr r0, r1;
    if (op == add) {
      r0 = bls_add(a0.get(), b0.get(), ctx.get());
      r1 = bls_add(a1.get(), b1.get(), ctx.get());
    } else if (op == sub) {
      r0 = bls_sub(a0.get(), b0.get(), ctx.get());
      r1 = bls_sub(a1.get(), b1.get(), ctx.get());
    } else {
      bn_ptr a0b0 = bls_mul(a0.get(), b0.get(), ctx.get());
      bn_ptr a1b1 = bls_mul(a1.get(), b1.get(), ctx.get());
      bn_ptr a0b1 = bls_mul(a0.get(), b1.get(), ctx.get());
      bn_ptr a1b0 = bls_mul(a1.get(), b0.get(), ctx.get());
      r0 = bls_sub(a0b0.get(), a1b1.get(), ctx.get());
      r1 = bls_add(a0b1.get(), a1b0.get(), ctx.get());
    }
    write_bigint(proc, f1, r0.get(), 6);
    write_bigint(proc, f1 + 48, r1.get(), 6);
#endif
    return false;
  }
  private:
   op_t op;
 };

// 0x80b: Arith384Mod  d = (a*b + c) mod module.  param -> 5 ptrs (LE 6*u64 each).
// Generic 384-bit modular arithmetic; module is parameter-supplied. Mirrors
// arith256_csr_t widened from 4 to 6 limbs (768-bit exact intermediate).
class arith384_csr_t : public accel_csr_t {
 public:
  using accel_csr_t::accel_csr_t;
  bool unlogged_write(const reg_t param) noexcept override {
    reg_t pa=gload(proc,param+0), pb=gload(proc,param+8), pc=gload(proc,param+16);
    reg_t pm=gload(proc,param+24), pd=gload(proc,param+32);
#if defined(__APPLE__)
    uint512_t a=read_bigint(proc,pa,6), b=read_bigint(proc,pb,6);
    uint512_t c=read_bigint(proc,pc,6), m=read_bigint(proc,pm,6);
    uint512_t d = (a*b + c) % m;
    write_bigint(proc, pd, d, 6);
#else
    bn_ctx_ptr ctx = make_ctx();
    bn_ptr a=read_bigint(proc,pa,6), b=read_bigint(proc,pb,6);
    bn_ptr c=read_bigint(proc,pc,6), m=read_bigint(proc,pm,6);
    bn_ptr ab = make_bn(), sum = make_bn(), d = make_bn();
    BN_mul(ab.get(), a.get(), b.get(), ctx.get());
    BN_add(sum.get(), ab.get(), c.get());
    BN_nnmod(d.get(), sum.get(), m.get(), ctx.get());
    write_bigint(proc, pd, d.get(), 6);
#endif
    return false;
  }
};

// 0x80c: BLS12-381 affine point add.  param -> {ptr p1, ptr p2}; result in-place on *p1.
// Points are 96-byte records: x (6 LE u64) at +0, y (6 LE u64) at +48.
// Requires x1 != x2 (infinity / equal-x / doubling handled by guest wrappers).
class bls12_curve_add_csr_t : public accel_csr_t {
 public:
  using accel_csr_t::accel_csr_t;
  bool unlogged_write(const reg_t param) noexcept override {
    reg_t p1 = gload(proc, param + 0), p2 = gload(proc, param + 8);
#if defined(__APPLE__)
    cpp_int x1 = rd_limbs(proc, p1, 6), y1 = rd_limbs(proc, p1 + 48, 6);
    cpp_int x2 = rd_limbs(proc, p2, 6), y2 = rd_limbs(proc, p2 + 48, 6);
    cpp_int s  = bls_mod((y2 - y1) * bls_inv(x2 - x1));
    cpp_int xr = bls_mod(s * s - x1 - x2);
    cpp_int yr = bls_mod(s * (x1 - xr) - y1);
    wr_limbs(proc, p1, xr, 6); wr_limbs(proc, p1 + 48, yr, 6);
#else
    bn_ctx_ptr ctx = make_ctx();
    bn_ptr x1 = read_bigint(proc, p1, 6), y1 = read_bigint(proc, p1 + 48, 6);
    bn_ptr x2 = read_bigint(proc, p2, 6), y2 = read_bigint(proc, p2 + 48, 6);
    bn_ptr dy = bls_sub(y2.get(), y1.get(), ctx.get());
    bn_ptr dx = bls_sub(x2.get(), x1.get(), ctx.get());
    bn_ptr inv = bls_inv(dx.get(), ctx.get());
    bn_ptr slope = bls_mul(dy.get(), inv.get(), ctx.get());
    bn_ptr slope2 = bls_mul(slope.get(), slope.get(), ctx.get());
    bn_ptr tmp = bls_sub(slope2.get(), x1.get(), ctx.get());
    bn_ptr xr = bls_sub(tmp.get(), x2.get(), ctx.get());
    bn_ptr x1_minus_xr = bls_sub(x1.get(), xr.get(), ctx.get());
    bn_ptr sy = bls_mul(slope.get(), x1_minus_xr.get(), ctx.get());
    bn_ptr yr = bls_sub(sy.get(), y1.get(), ctx.get());
    write_bigint(proc, p1, xr.get(), 6); write_bigint(proc, p1 + 48, yr.get(), 6);
#endif
    return false;
  }
};

// 0x80d: BLS12-381 affine point double, in-place on the 96-byte point at param.
// Requires y != 0 (infinity handled by the guest wrapper).
class bls12_curve_dbl_csr_t : public accel_csr_t {
 public:
  using accel_csr_t::accel_csr_t;
  bool unlogged_write(const reg_t param) noexcept override {
#if defined(__APPLE__)
    cpp_int x = rd_limbs(proc, param, 6), y = rd_limbs(proc, param + 48, 6);
    cpp_int s  = bls_mod(3 * x * x * bls_inv(2 * y));
    cpp_int xr = bls_mod(s * s - 2 * x);
    cpp_int yr = bls_mod(s * (x - xr) - y);
    wr_limbs(proc, param, xr, 6); wr_limbs(proc, param + 48, yr, 6);
#else
    bn_ctx_ptr ctx = make_ctx();
    bn_ptr x = read_bigint(proc, param, 6), y = read_bigint(proc, param + 48, 6);
    bn_ptr three = make_bn(), two = make_bn();
    BN_set_word(three.get(), 3);
    BN_set_word(two.get(), 2);
    bn_ptr x2 = bls_mul(x.get(), x.get(), ctx.get());
    bn_ptr num = bls_mul(three.get(), x2.get(), ctx.get());
    bn_ptr denom = bls_mul(two.get(), y.get(), ctx.get());
    bn_ptr inv = bls_inv(denom.get(), ctx.get());
    bn_ptr slope = bls_mul(num.get(), inv.get(), ctx.get());
    bn_ptr slope2 = bls_mul(slope.get(), slope.get(), ctx.get());
    bn_ptr two_x = bls_mul(two.get(), x.get(), ctx.get());
    bn_ptr xr = bls_sub(slope2.get(), two_x.get(), ctx.get());
    bn_ptr x_minus_xr = bls_sub(x.get(), xr.get(), ctx.get());
    bn_ptr sy = bls_mul(slope.get(), x_minus_xr.get(), ctx.get());
    bn_ptr yr = bls_sub(sy.get(), y.get(), ctx.get());
    write_bigint(proc, param, xr.get(), 6); write_bigint(proc, param + 48, yr.get(), 6);
#endif
    return false;
  }
};

// ---- BLAKE2b round (CSR 0x819) ---------------------------------------------
// RFC 7693 BLAKE2b F-function round: one pass of the G mixing function over
// the 8 MIX_TABLE index sets, using SIGMA[index] to select message words.
// The guest software wrapper (zkvm_blake2f) builds the v = h||IV working
// vector, applies the t/f flags, and calls this CSR once per round with
// index = round mod 10; the CSR mutates the 16-word v vector in place.
static const unsigned int BLAKE2B_SIGMA[10][16] = {
  { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,10,11,12,13,14,15},
  {14,10, 4, 8, 9,15,13, 6, 1,12, 0, 2,11, 7, 5, 3},
  {11, 8,12, 0, 5, 2,15,13,10,14, 3, 6, 7, 1, 9, 4},
  { 7, 9, 3, 1,13,12,11,14, 2, 6, 5,10, 4, 0,15, 8},
  { 9, 0, 5, 7, 2, 4,10,15,14, 1,11,12, 6, 8, 3,13},
  { 2,12, 6,10, 0,11, 8, 3, 4,13, 7, 5,15,14, 1, 9},
  {12, 5, 1,15,14,13, 4,10, 0, 7, 6, 3, 9, 2, 8,11},
  {13,11, 7,14,12, 1, 3, 9, 5, 0,15, 4, 8, 6, 2,10},
  { 6,15,14, 9,11, 3, 0, 8,12, 2,13, 7, 1, 4,10, 5},
  {10, 2, 8, 4, 7, 6, 1, 5,15,11, 9,14, 3,12,13, 0},
};
// MIX_TABLE[i] = (a, b, c, d) index sets: rows 0..3 are columns, 4..7 diagonals.
static const unsigned int BLAKE2B_MIX[8][4] = {
  { 0, 4, 8,12},{ 1, 5, 9,13},{ 2, 6,10,14},{ 3, 7,11,15},
  { 0, 5,10,15},{ 1, 6,11,12},{ 2, 7, 8,13},{ 3, 4, 9,14},
};
static inline uint64_t rotr64(uint64_t x, int n){ return (x>>n)|(x<<(64-n)); }
// One G invocation: mixes v[a..d] with message words x, y (RFC 7693, BLAKE2b).
static inline void blake2b_g(uint64_t v[16], int a, int b, int c, int d,
                             uint64_t x, uint64_t y) {
  v[a] += v[b] + x;
  v[d]  = rotr64(v[d] ^ v[a], 32);
  v[c] += v[d];
  v[b]  = rotr64(v[b] ^ v[c], 24);
  v[a] += v[b] + y;
  v[d]  = rotr64(v[d] ^ v[a], 16);
  v[c] += v[d];
  v[b]  = rotr64(v[b] ^ v[c], 63);
}
// 0x819: one BLAKE2b round.  param = {index, &state, &input}; index in [0,10),
// state and input each point at 16 LE u64 words. State (the v working vector)
// is permuted in place; input (the message block) is read-only.
class blake2b_round_csr_t : public accel_csr_t {
 public:
  using accel_csr_t::accel_csr_t;
  bool unlogged_write(const reg_t param) noexcept override {
    uint64_t index = gload(proc, param + 0);
    reg_t pstate = gload(proc, param + 8);
    reg_t pinput = gload(proc, param + 16);
    uint64_t v[16], m[16];
    for (int i = 0; i < 16; ++i) {
      v[i] = gload(proc, pstate + 8 * i);
      m[i] = gload(proc, pinput + 8 * i);
    }
    const unsigned int* s = BLAKE2B_SIGMA[index % 10];
    for (int i = 0; i < 8; ++i) {
      blake2b_g(v, BLAKE2B_MIX[i][0], BLAKE2B_MIX[i][1],
                   BLAKE2B_MIX[i][2], BLAKE2B_MIX[i][3],
                m[s[2*i]], m[s[2*i + 1]]);
    }
    for (int i = 0; i < 16; ++i) gstore(proc, pstate + 8 * i, v[i]);
    return false;
  }
};

// 0x806: BN254 (alt_bn128) affine point add.  param -> {ptr p1, ptr p2};
// result in-place on *p1. Points are 64-byte records: x (4 LE u64) at +0,
// y (4 LE u64) at +32. Requires x1 != x2 (infinity / equal-x / doubling
// handled by guest wrappers). Mirrors secp_add_csr_t over the BN254 prime.
class bn254_curve_add_csr_t : public accel_csr_t {
 public:
  using accel_csr_t::accel_csr_t;
  bool unlogged_write(const reg_t param) noexcept override {
    reg_t p1 = gload(proc, param + 0), p2 = gload(proc, param + 8);
#if defined(__APPLE__)
    cpp_int x1 = rd_limbs(proc, p1, 4), y1 = rd_limbs(proc, p1 + 32, 4);
    cpp_int x2 = rd_limbs(proc, p2, 4), y2 = rd_limbs(proc, p2 + 32, 4);
    cpp_int s  = bn254_mod((y2 - y1) * bn254_inv(x2 - x1));
    cpp_int xr = bn254_mod(s * s - x1 - x2);
    cpp_int yr = bn254_mod(s * (x1 - xr) - y1);
    wr_limbs254(proc, p1, xr, 4); wr_limbs254(proc, p1 + 32, yr, 4);
#else
    bn_ctx_ptr ctx = make_ctx();
    bn_ptr x1 = read_bigint(proc, p1, 4), y1 = read_bigint(proc, p1 + 32, 4);
    bn_ptr x2 = read_bigint(proc, p2, 4), y2 = read_bigint(proc, p2 + 32, 4);
    bn_ptr dy = bn254_sub(y2.get(), y1.get(), ctx.get());
    bn_ptr dx = bn254_sub(x2.get(), x1.get(), ctx.get());
    bn_ptr inv = bn254_inv(dx.get(), ctx.get());
    bn_ptr slope = bn254_mul(dy.get(), inv.get(), ctx.get());
    bn_ptr slope2 = bn254_mul(slope.get(), slope.get(), ctx.get());
    bn_ptr tmp = bn254_sub(slope2.get(), x1.get(), ctx.get());
    bn_ptr xr = bn254_sub(tmp.get(), x2.get(), ctx.get());
    bn_ptr x1_minus_xr = bn254_sub(x1.get(), xr.get(), ctx.get());
    bn_ptr sy = bn254_mul(slope.get(), x1_minus_xr.get(), ctx.get());
    bn_ptr yr = bn254_sub(sy.get(), y1.get(), ctx.get());
    write_bigint(proc, p1, xr.get(), 4); write_bigint(proc, p1 + 32, yr.get(), 4);
#endif
    return false;
  }
};

// 0x807: BN254 affine point double, in-place on the 64-byte point at param.
// Requires y != 0 (infinity handled by the guest wrapper).
class bn254_curve_dbl_csr_t : public accel_csr_t {
 public:
  using accel_csr_t::accel_csr_t;
  bool unlogged_write(const reg_t param) noexcept override {
#if defined(__APPLE__)
    cpp_int x = rd_limbs(proc, param, 4), y = rd_limbs(proc, param + 32, 4);
    cpp_int s  = bn254_mod(3 * x * x * bn254_inv(2 * y));
    cpp_int xr = bn254_mod(s * s - 2 * x);
    cpp_int yr = bn254_mod(s * (x - xr) - y);
    wr_limbs254(proc, param, xr, 4); wr_limbs254(proc, param + 32, yr, 4);
#else
    bn_ctx_ptr ctx = make_ctx();
    bn_ptr x = read_bigint(proc, param, 4), y = read_bigint(proc, param + 32, 4);
    bn_ptr three = make_bn(), two = make_bn();
    BN_set_word(three.get(), 3);
    BN_set_word(two.get(), 2);
    bn_ptr x2 = bn254_mul(x.get(), x.get(), ctx.get());
    bn_ptr num = bn254_mul(three.get(), x2.get(), ctx.get());
    bn_ptr denom = bn254_mul(two.get(), y.get(), ctx.get());
    bn_ptr inv = bn254_inv(denom.get(), ctx.get());
    bn_ptr slope = bn254_mul(num.get(), inv.get(), ctx.get());
    bn_ptr slope2 = bn254_mul(slope.get(), slope.get(), ctx.get());
    bn_ptr two_x = bn254_mul(two.get(), x.get(), ctx.get());
    bn_ptr xr = bn254_sub(slope2.get(), two_x.get(), ctx.get());
    bn_ptr x_minus_xr = bn254_sub(x.get(), xr.get(), ctx.get());
    bn_ptr sy = bn254_mul(slope.get(), x_minus_xr.get(), ctx.get());
    bn_ptr yr = bn254_sub(sy.get(), y.get(), ctx.get());
    write_bigint(proc, param, xr.get(), 4); write_bigint(proc, param + 32, yr.get(), 4);
#endif
    return false;
  }
};

// 0x808/0x809/0x80a: BN254 Fp2 add/sub/mul over Fp[u]/(u^2+1).
// param -> {&f1, &f2}; result in-place on *f1. Each Fp2 element is 64 bytes:
// c0 (4 LE u64) at +0, c1 (4 LE u64) at +32. Mirrors bls12_fp2_csr_t over the
// BN254 prime (4 limbs per component instead of 6).
class bn254_fp2_csr_t : public accel_csr_t {
 public:
  enum op_t { add, sub, mul };
  bn254_fp2_csr_t(processor_t* p, reg_t addr, op_t op): accel_csr_t(p, addr), op(op) {}
  bool unlogged_write(const reg_t param) noexcept override {
    reg_t f1 = gload(proc, param + 0), f2 = gload(proc, param + 8);
#if defined(__APPLE__)
    cpp_int a0 = rd_limbs(proc, f1, 4), a1 = rd_limbs(proc, f1 + 32, 4);
    cpp_int b0 = rd_limbs(proc, f2, 4), b1 = rd_limbs(proc, f2 + 32, 4);
    cpp_int r0 = 0, r1 = 0;
    if (op == add) {
      r0 = a0 + b0;
      r1 = a1 + b1;
    } else if (op == sub) {
      r0 = a0 - b0;
      r1 = a1 - b1;
    } else {
      r0 = a0 * b0 - a1 * b1;
      r1 = a0 * b1 + a1 * b0;
    }
    wr_limbs254(proc, f1, r0, 4);
    wr_limbs254(proc, f1 + 32, r1, 4);
#else
    bn_ctx_ptr ctx = make_ctx();
    bn_ptr a0 = read_bigint(proc, f1, 4), a1 = read_bigint(proc, f1 + 32, 4);
    bn_ptr b0 = read_bigint(proc, f2, 4), b1 = read_bigint(proc, f2 + 32, 4);
    bn_ptr r0, r1;
    if (op == add) {
      r0 = bn254_add(a0.get(), b0.get(), ctx.get());
      r1 = bn254_add(a1.get(), b1.get(), ctx.get());
    } else if (op == sub) {
      r0 = bn254_sub(a0.get(), b0.get(), ctx.get());
      r1 = bn254_sub(a1.get(), b1.get(), ctx.get());
    } else {
      bn_ptr a0b0 = bn254_mul(a0.get(), b0.get(), ctx.get());
      bn_ptr a1b1 = bn254_mul(a1.get(), b1.get(), ctx.get());
      bn_ptr a0b1 = bn254_mul(a0.get(), b1.get(), ctx.get());
      bn_ptr a1b0 = bn254_mul(a1.get(), b0.get(), ctx.get());
      r0 = bn254_sub(a0b0.get(), a1b1.get(), ctx.get());
      r1 = bn254_add(a0b1.get(), a1b0.get(), ctx.get());
    }
    write_bigint(proc, f1, r0.get(), 4);
    write_bigint(proc, f1 + 32, r1.get(), 4);
#endif
    return false;
  }
 private:
  op_t op;
};

// Stub for accelerator CSRs not yet implemented: logs the CSR + param once so
// we can see which a given block needs, instead of silently raising illegal-insn.
class unimpl_csr_t : public accel_csr_t {
 public:
  using accel_csr_t::accel_csr_t;
  bool unlogged_write(const reg_t param) noexcept override {
    fprintf(stderr, "[zisk_accel] UNIMPLEMENTED CSR 0x%llx param=0x%llx\n",
            (unsigned long long)address, (unsigned long long)param);
    return false;
  }
};

// ---- extension -------------------------------------------------------------
class zisk_accel_t : public extension_t {
 public:
  const char* name() const override { return "zisk_accel"; }
  std::vector<insn_desc_t> get_instructions(const processor_t&) override { return {}; }
  std::vector<disasm_insn_t*> get_disasms(const processor_t*) override { return {}; }
  std::vector<csr_t_p> get_csrs(processor_t& p) const override {
    std::vector<csr_t_p> v = {
      std::make_shared<keccak_csr_t>(&p, 0x800),
      std::make_shared<arith256_csr_t>(&p, 0x802),
      std::make_shared<secp_add_csr_t>(&p, 0x803),
      std::make_shared<secp_dbl_csr_t>(&p, 0x804),
      std::make_shared<sha256_csr_t>(&p, 0x805),
      std::make_shared<bls12_fp2_csr_t>(&p, 0x80e, bls12_fp2_csr_t::add),
      std::make_shared<bls12_fp2_csr_t>(&p, 0x80f, bls12_fp2_csr_t::sub),
      std::make_shared<bls12_fp2_csr_t>(&p, 0x810, bls12_fp2_csr_t::mul),
      std::make_shared<blake2b_round_csr_t>(&p, 0x819),
      std::make_shared<arith384_csr_t>(&p, 0x80b),
      std::make_shared<bls12_curve_add_csr_t>(&p, 0x80c),
      std::make_shared<bls12_curve_dbl_csr_t>(&p, 0x80d),
      std::make_shared<bn254_curve_add_csr_t>(&p, 0x806),
      std::make_shared<bn254_curve_dbl_csr_t>(&p, 0x807),
      std::make_shared<bn254_fp2_csr_t>(&p, 0x808, bn254_fp2_csr_t::add),
      std::make_shared<bn254_fp2_csr_t>(&p, 0x809, bn254_fp2_csr_t::sub),
      std::make_shared<bn254_fp2_csr_t>(&p, 0x80a, bn254_fp2_csr_t::mul),
    };
    // All accelerator CSRs are now implemented — no stubs remain.
    return v;
  }
};

REGISTER_EXTENSION(zisk_accel, [](){ return new zisk_accel_t; })

// Factory so the custom driver (spike_run) can instantiate the extension
// directly, without loading the .so via --extlib.
extension_t* make_zisk_accel_extension() { return new zisk_accel_t; }
