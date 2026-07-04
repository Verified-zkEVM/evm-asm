/-
  EvmAsm.Codegen.Programs.ModexpBackend

  Pure-RV64 implementation of the MODEXP precompile (EIP-198) backend,
  replacing the deterministic safe-fail stub. Computes `(base^exp) mod modulus`
  for arbitrary-precision operands using schoolbook multiplication and binary
  long division.

  Length domain: the backend statically sizes for up to 2048 bytes / 256 limbs
  per operand, but this is unreachable headroom. The precompile dispatcher
  (`Programs.Modexp`, `modexpReadLengthAsm`) enforces the EIP-7823 cap and
  rejects any base/exp/modulus length > 1024 bytes BEFORE routing here, so the
  reachable maximum is 1024 bytes = 128 limbs. The `<= 2048` validation and the
  2048-byte staging arenas below are dead-defensive; they are consistent with
  (never narrower than) the dispatcher cap, so they cannot cause a false-accept.
-/

namespace EvmAsm.Codegen

/-- Static maximum number of 64-bit limbs for the staging arenas (2048 bytes /
    8). This is headroom only: the dispatcher's EIP-7823 cap (1024 bytes) means
    the reachable maximum is 128 limbs, so this constant OVERSTATES the live
    domain and must not be used as the domain bound in any correctness proof.
    Currently referenced nowhere (kept for documentation of the arena sizes). -/
def modexpBnMaxLimbs : Nat := 256

/-- Scratch data section for the BigNum modexp backend. -/
def emitModexpBnScratchData : String :=
  ".balign 8\n" ++
  "modexp_bn_base:\n" ++ "  .zero 2048\n" ++
  "modexp_bn_exp:\n" ++ "  .zero 2048\n" ++
  "modexp_bn_mod:\n" ++ "  .zero 2048\n" ++
  "modexp_bn_result:\n" ++ "  .zero 2048\n" ++
  "modexp_bn_product:\n" ++ "  .zero 4096\n" ++
  "modexp_bn_remainder:\n" ++ "  .zero 2056\n"

/-- All helper functions concatenated (cmpge, sub, mul, binmod, be_to_le,
    le_to_be, iszero). Each is a global function using only t-regs internally
    (except binmod which saves s2/s3/s4/ra). -/
def modexpBnHelpers : String :=
  -- modexp_be_to_le(a0=src, a1=len, a2=dst, a3=max_fill)
  ".globl modexp_be_to_le\n" ++ "modexp_be_to_le:\n" ++
  "  mv t0, a2\n" ++ "  mv t1, a3\n" ++
  ".Lmbtl_zero:\n" ++ "  beqz t1, .Lmbtl_copy_setup\n" ++
  "  sd zero, 0(t0)\n" ++ "  addi t0, t0, 8\n" ++ "  addi t1, t1, -8\n" ++
  "  j .Lmbtl_zero\n" ++
  ".Lmbtl_copy_setup:\n" ++ "  beqz a1, .Lmbtl_done\n" ++
  "  add t0, a0, a1\n" ++ "  addi t0, t0, -1\n" ++
  "  mv t1, a2\n" ++ "  mv t2, a1\n" ++
  ".Lmbtl_copy:\n" ++ "  beqz t2, .Lmbtl_done\n" ++
  "  lbu t3, 0(t0)\n" ++ "  sb t3, 0(t1)\n" ++
  "  addi t0, t0, -1\n" ++ "  addi t1, t1, 1\n" ++ "  addi t2, t2, -1\n" ++
  "  j .Lmbtl_copy\n" ++
  ".Lmbtl_done:\n" ++ "  ret\n" ++
  -- modexp_le_to_be(a0=src_limbs, a1=n_limbs, a2=dst, a3=dst_len)
  ".globl modexp_le_to_be\n" ++ "modexp_le_to_be:\n" ++
  "  mv t0, a2\n" ++ "  mv t1, a3\n" ++
  ".Lmltb_zero:\n" ++ "  beqz t1, .Lmltb_setup\n" ++
  "  sb zero, 0(t0)\n" ++ "  addi t0, t0, 1\n" ++ "  addi t1, t1, -1\n" ++
  "  j .Lmltb_zero\n" ++
  ".Lmltb_setup:\n" ++ "  li t0, 0\n" ++ "  slli t1, a1, 3\n" ++
  ".Lmltb_loop:\n" ++ "  beq t0, t1, .Lmltb_done\n" ++
  "  add t2, a0, t0\n" ++ "  lbu t3, 0(t2)\n" ++
  "  sub t4, a3, t0\n" ++ "  addi t4, t4, -1\n" ++
  "  bltz t4, .Lmltb_skip\n" ++
  "  add t5, a2, t4\n" ++ "  sb t3, 0(t5)\n" ++
  ".Lmltb_skip:\n" ++ "  addi t0, t0, 1\n" ++ "  j .Lmltb_loop\n" ++
  ".Lmltb_done:\n" ++ "  ret\n" ++
  -- modexp_iszero(a0=ptr, a1=n_limbs) → a0=1 if zero
  ".globl modexp_iszero\n" ++ "modexp_iszero:\n" ++
  "  li t0, 0\n" ++
  ".Lmiz_loop:\n" ++ "  beq t0, a1, .Lmiz_yes\n" ++
  "  slli t1, t0, 3\n" ++ "  add t2, a0, t1\n" ++ "  ld t2, 0(t2)\n" ++
  "  bnez t2, .Lmiz_no\n" ++
  "  addi t0, t0, 1\n" ++ "  j .Lmiz_loop\n" ++
  ".Lmiz_no:\n" ++ "  li a0, 0\n" ++ "  ret\n" ++
  ".Lmiz_yes:\n" ++ "  li a0, 1\n" ++ "  ret\n" ++
  -- modexp_cmpge(a0=ptr_a, a1=ptr_b, a2=n) → a0=1 if a>=b
  ".globl modexp_cmpge\n" ++ "modexp_cmpge:\n" ++
  "  li t0, 1\n" ++ "  addi t1, a2, -1\n" ++
  ".Lmcmp_loop:\n" ++ "  bltz t1, .Lmcmp_done\n" ++
  "  slli t2, t1, 3\n" ++
  "  add t3, a0, t2\n" ++ "  ld t4, 0(t3)\n" ++
  "  add t3, a1, t2\n" ++ "  ld t5, 0(t3)\n" ++
  "  bltu t4, t5, .Lmcmp_lt\n" ++
  "  beq t4, t5, .Lmcmp_eq\n" ++
  "  li t0, 1\n" ++ "  j .Lmcmp_done\n" ++
  ".Lmcmp_eq:\n" ++ "  addi t1, t1, -1\n" ++ "  j .Lmcmp_loop\n" ++
  ".Lmcmp_lt:\n" ++ "  li t0, 0\n" ++
  ".Lmcmp_done:\n" ++ "  mv a0, t0\n" ++ "  ret\n" ++
  -- modexp_sub(a0=ptr_a, a1=ptr_b, a2=n) → a -= b in place
  ".globl modexp_sub\n" ++ "modexp_sub:\n" ++
  "  li t0, 0\n" ++ "  li t3, 0\n" ++
  ".Lmsub_loop:\n" ++ "  beq t0, a2, .Lmsub_done\n" ++
  "  slli t1, t0, 3\n" ++ "  add t4, a0, t1\n" ++ "  add t5, a1, t1\n" ++
  "  ld t1, 0(t4)\n" ++ "  ld t2, 0(t5)\n" ++
  "  sub t6, t1, t3\n" ++ "  sltu a5, t1, t3\n" ++
  "  sub a6, t6, t2\n" ++ "  sltu a7, t6, t2\n" ++
  "  or t3, a5, a7\n" ++ "  sd a6, 0(t4)\n" ++
  "  addi t0, t0, 1\n" ++ "  j .Lmsub_loop\n" ++
  ".Lmsub_done:\n" ++ "  ret\n" ++
  -- modexp_mul(a0=ptr_a, a1=na, a2=ptr_b, a3=nb, a4=ptr_prod)
  ".globl modexp_mul\n" ++ "modexp_mul:\n" ++
  -- Zero prod (na+nb)*8
  "  mv t0, a4\n" ++ "  add t1, a1, a3\n" ++ "  slli t1, t1, 3\n" ++
  ".Lmmul_zero:\n" ++ "  beqz t1, .Lmmul_outer\n" ++
  "  sd zero, 0(t0)\n" ++ "  addi t0, t0, 8\n" ++ "  addi t1, t1, -8\n" ++
  "  j .Lmmul_zero\n" ++
  ".Lmmul_outer:\n" ++ "  li t0, 0\n" ++
  ".Lmmul_i:\n" ++ "  beq t0, a1, .Lmmul_done\n" ++
  "  slli t1, t0, 3\n" ++ "  add t1, t1, a0\n" ++ "  ld t1, 0(t1)\n" ++
  "  li t3, 0\n" ++ "  li t4, 0\n" ++
  ".Lmmul_j:\n" ++ "  beq t4, a3, .Lmmul_carry\n" ++
  "  add t5, t0, t4\n" ++ "  slli t5, t5, 3\n" ++ "  add t5, t5, a4\n" ++
  "  slli t6, t4, 3\n" ++ "  add t6, t6, a2\n" ++ "  ld t6, 0(t6)\n" ++
  "  mulhu a6, t1, t6\n" ++ "  mul a7, t1, t6\n" ++
  "  ld a5, 0(t5)\n" ++ "  add a7, a7, a5\n" ++ "  sltu t2, a7, a5\n" ++
  "  add a6, a6, t2\n" ++
  "  add a7, a7, t3\n" ++ "  sltu t2, a7, t3\n" ++ "  add a6, a6, t2\n" ++
  "  sd a7, 0(t5)\n" ++ "  mv t3, a6\n" ++
  "  addi t4, t4, 1\n" ++ "  j .Lmmul_j\n" ++
  ".Lmmul_carry:\n" ++
  "  add t5, t0, a3\n" ++ "  slli t5, t5, 3\n" ++ "  add t5, t5, a4\n" ++
  "  ld t6, 0(t5)\n" ++ "  add t6, t6, t3\n" ++ "  sd t6, 0(t5)\n" ++
  "  addi t0, t0, 1\n" ++ "  j .Lmmul_i\n" ++
  ".Lmmul_done:\n" ++ "  ret\n" ++
  -- modexp_binmod(a0=ptr_a, a1=na, a2=ptr_m, a3=nm, a4=ptr_r)
  -- r = a mod m. Uses modexp_bn_remainder scratch. Saves s2/s3/s4/s5/ra.
  -- Bit counter in s5 (NOT t2 — cmpge/sub clobber t2).
  ".globl modexp_binmod\n" ++ "modexp_binmod:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd s2, 0(sp)\n" ++ "  sd s3, 8(sp)\n" ++
  "  sd s4, 16(sp)\n" ++ "  sd s5, 24(sp)\n" ++ "  sd ra, 32(sp)\n" ++
  "  mv s2, a2\n" ++ "  mv s3, a3\n" ++ "  mv s4, a0\n" ++
  -- Zero remainder (nm+1)*8
  "  la t0, modexp_bn_remainder\n" ++
  "  addi t1, s3, 1\n" ++ "  slli t1, t1, 3\n" ++
  ".Lmbinm_zero:\n" ++ "  beqz t1, .Lmbinm_main\n" ++
  "  sd zero, 0(t0)\n" ++ "  addi t0, t0, 8\n" ++ "  addi t1, t1, -8\n" ++
  "  j .Lmbinm_zero\n" ++
  ".Lmbinm_main:\n" ++
  "  slli t1, a1, 6\n" ++ "  addi s5, t1, -1\n" ++
  ".Lmbinm_bit:\n" ++ "  bltz s5, .Lmbinm_finish\n" ++
  -- Shift remainder left 1 (nm+1 limbs), carry LOW→HIGH
  "  la t0, modexp_bn_remainder\n" ++
  "  li t3, 0\n" ++ "  li t4, 0\n" ++
  ".Lmbinm_shift:\n" ++
  "  addi t5, s3, 1\n" ++ "  beq t4, t5, .Lmbinm_bring\n" ++
  "  slli t5, t4, 3\n" ++ "  add t5, t0, t5\n" ++
  "  ld t6, 0(t5)\n" ++ "  srli a5, t6, 63\n" ++
  "  slli t6, t6, 1\n" ++ "  or t6, t6, t3\n" ++
  "  sd t6, 0(t5)\n" ++ "  mv t3, a5\n" ++
  "  addi t4, t4, 1\n" ++ "  j .Lmbinm_shift\n" ++
  -- Bring in bit s5 of a
  ".Lmbinm_bring:\n" ++
  "  srli t4, s5, 6\n" ++ "  andi t5, s5, 63\n" ++
  "  slli t6, t4, 3\n" ++ "  add t6, t6, s4\n" ++ "  ld t6, 0(t6)\n" ++
  "  srl t6, t6, t5\n" ++ "  andi t6, t6, 1\n" ++
  "  ld t5, 0(t0)\n" ++ "  or t5, t5, t6\n" ++ "  sd t5, 0(t0)\n" ++
  -- Check remainder >= m
  "  slli t4, s3, 3\n" ++ "  add t4, t0, t4\n" ++ "  ld t4, 0(t4)\n" ++
  "  bnez t4, .Lmbinm_sub\n" ++
  "  mv a0, t0\n" ++ "  mv a1, s2\n" ++ "  mv a2, s3\n" ++
  "  jal ra, modexp_cmpge\n" ++
  "  beqz a0, .Lmbinm_next\n" ++
  ".Lmbinm_sub:\n" ++
  "  la t0, modexp_bn_remainder\n" ++
  "  mv a0, t0\n" ++ "  mv a1, s2\n" ++ "  mv a2, s3\n" ++
  "  jal ra, modexp_sub\n" ++
  "  la t0, modexp_bn_remainder\n" ++
  "  slli t4, s3, 3\n" ++ "  add t4, t0, t4\n" ++ "  sd zero, 0(t4)\n" ++
  ".Lmbinm_next:\n" ++ "  addi s5, s5, -1\n" ++ "  j .Lmbinm_bit\n" ++
  ".Lmbinm_finish:\n" ++
  -- Copy remainder[0..nm-1] → r
  "  la t0, modexp_bn_remainder\n" ++ "  li t4, 0\n" ++
  ".Lmbinm_copy:\n" ++ "  beq t4, s3, .Lmbinm_done\n" ++
  "  slli t5, t4, 3\n" ++
  "  add t6, t0, t5\n" ++ "  ld a5, 0(t6)\n" ++
  "  add t6, a4, t5\n" ++ "  sd a5, 0(t6)\n" ++
  "  addi t4, t4, 1\n" ++ "  j .Lmbinm_copy\n" ++
  ".Lmbinm_done:\n" ++
  "  ld s2, 0(sp)\n" ++ "  ld s3, 8(sp)\n" ++
  "  ld s4, 16(sp)\n" ++ "  ld s5, 24(sp)\n" ++ "  ld ra, 32(sp)\n" ++
  "  addi sp, sp, 40\n" ++ "  ret\n"

/-- Full implementation of `zkvm_modexp`.

    ABI: a0=base(BE), a1=Blen, a2=exp(BE), a3=Elen, a4=mod(BE), a5=Mlen,
    a6=output. Returns a0=0 (ok) or a0=-1 (err).

    Square-and-multiply with schoolbook mul and binary long division. -/
def zkvmModexpBackendImpl : String :=
  modexpBnHelpers ++ "\n" ++
  ".globl zkvm_modexp\n" ++ "zkvm_modexp:\n" ++
  -- Save all inputs in s-regs before any jal call
  "  addi sp, sp, -128\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp)\n" ++     -- base_ptr
  "  sd s1, 16(sp)\n" ++    -- Blen
  "  sd s2, 24(sp)\n" ++    -- exp_ptr
  "  sd s3, 32(sp)\n" ++    -- Elen
  "  sd s4, 40(sp)\n" ++    -- mod_ptr
  "  sd s5, 48(sp)\n" ++    -- Mlen
  "  sd s6, 56(sp)\n" ++    -- output_ptr
  "  sd s7, 64(sp)\n" ++    -- nm (modulus limbs)
  "  sd s8, 72(sp)\n" ++    -- nb (base limbs)
  "  sd s9, 80(sp)\n" ++    -- ne (exp limbs)
  "  sd s10, 88(sp)\n" ++   -- exp bit position state
  "  sd s11, 96(sp)\n" ++
  "  mv s0, a0\n" ++ "  mv s1, a1\n" ++ "  mv s2, a2\n" ++
  "  mv s3, a3\n" ++ "  mv s4, a4\n" ++ "  mv s5, a5\n" ++
  "  mv s6, a6\n" ++
  -- Validate lengths
  "  li t0, 2048\n" ++
  "  bltu t0, s1, .Lmexp_err\n" ++
  "  bltu t0, s3, .Lmexp_err\n" ++
  "  bltu t0, s5, .Lmexp_err\n" ++
  -- nm = ceil(Mlen / 8)
  "  addi t0, s5, 7\n" ++ "  srli s7, t0, 3\n" ++
  -- nb = ceil(Blen / 8)
  "  addi t0, s1, 7\n" ++ "  srli s8, t0, 3\n" ++
  -- ne = ceil(Elen / 8)
  "  addi t0, s3, 7\n" ++ "  srli s9, t0, 3\n" ++
  -- Edge case: Mlen == 0 → output nothing, return 0
  "  beqz s5, .Lmexp_ok\n" ++
  -- Parse modulus → modexp_bn_mod
  "  mv a0, s4\n" ++ "  mv a1, s5\n" ++
  "  la a2, modexp_bn_mod\n" ++ "  li a3, 2048\n" ++
  "  jal ra, modexp_be_to_le\n" ++
  -- Check modulus == 0 → fill output with Mlen zeros
  "  la a0, modexp_bn_mod\n" ++ "  mv a1, s7\n" ++
  "  jal ra, modexp_iszero\n" ++
  "  bnez a0, .Lmexp_modzero\n" ++
  -- Parse base → modexp_bn_base
  "  mv a0, s0\n" ++ "  mv a1, s1\n" ++
  "  la a2, modexp_bn_base\n" ++ "  li a3, 2048\n" ++
  "  jal ra, modexp_be_to_le\n" ++
  -- Parse exp → modexp_bn_exp
  "  mv a0, s2\n" ++ "  mv a1, s3\n" ++
  "  la a2, modexp_bn_exp\n" ++ "  li a3, 2048\n" ++
  "  jal ra, modexp_be_to_le\n" ++
  -- Reduce base mod modulus: binmod(base, nb, mod, nm) → base
  "  la a0, modexp_bn_base\n" ++ "  mv a1, s8\n" ++
  "  la a2, modexp_bn_mod\n" ++ "  mv a3, s7\n" ++
  "  la a4, modexp_bn_base\n" ++
  "  jal ra, modexp_binmod\n" ++
  -- Result = 1 (set result[0] = 1, rest zero)
  "  la t0, modexp_bn_result\n" ++
  "  addi t1, s7, 1\n" ++ "  slli t1, t1, 3\n" ++
  ".Lmexp_res_zero:\n" ++ "  beqz t1, .Lmexp_res_one\n" ++
  "  sd zero, 0(t0)\n" ++ "  addi t0, t0, 8\n" ++ "  addi t1, t1, -8\n" ++
  "  j .Lmexp_res_zero\n" ++
  ".Lmexp_res_one:\n" ++
  "  la t0, modexp_bn_result\n" ++ "  li t1, 1\n" ++ "  sd t1, 0(t0)\n" ++
  -- Check exp == 0: if so, result = 1 mod modulus
  "  la a0, modexp_bn_exp\n" ++ "  mv a1, s9\n" ++
  "  jal ra, modexp_iszero\n" ++
  "  bnez a0, .Lmexp_format\n" ++
  -- Find highest set bit in exp: scan from MSB limb/bit down
  -- s10 = current bit index (global), start at ne*64-1
  "  slli s10, s9, 6\n" ++ "  addi s10, s10, -1\n" ++
  ".Lmexp_findbit:\n" ++
  "  bltz s10, .Lmexp_format\n" ++   -- exp is zero (shouldn't happen)
  -- Get exp bit at s10
  "  srli t0, s10, 6\n" ++           -- limb index
  "  andi t1, s10, 63\n" ++          -- bit
  "  slli t2, t0, 3\n" ++
  "  la t3, modexp_bn_exp\n" ++ "  add t3, t3, t2\n" ++
  "  ld t3, 0(t3)\n" ++
  "  srl t3, t3, t1\n" ++ "  andi t3, t3, 1\n" ++
  "  bnez t3, .Lmexp_sqmul\n" ++     -- found highest set bit
  "  addi s10, s10, -1\n" ++ "  j .Lmexp_findbit\n" ++
  -- Square-and-multiply loop from s10 down to 0
  ".Lmexp_sqmul:\n" ++
  -- result = result^2 mod modulus
  -- product = result * result
  "  la a0, modexp_bn_result\n" ++ "  mv a1, s7\n" ++
  "  la a2, modexp_bn_result\n" ++ "  mv a3, s7\n" ++
  "  la a4, modexp_bn_product\n" ++
  "  jal ra, modexp_mul\n" ++
  -- result = product mod modulus (product has 2*nm limbs)
  "  la a0, modexp_bn_product\n" ++
  "  li a1, 0\n" ++ "  add a1, s7, s7\n" ++  -- na = 2*nm
  "  la a2, modexp_bn_mod\n" ++ "  mv a3, s7\n" ++
  "  la a4, modexp_bn_result\n" ++
  "  jal ra, modexp_binmod\n" ++
  -- If exp bit s10 is set: result = result * base mod modulus
  "  srli t0, s10, 6\n" ++ "  andi t1, s10, 63\n" ++
  "  slli t2, t0, 3\n" ++
  "  la t3, modexp_bn_exp\n" ++ "  add t3, t3, t2\n" ++
  "  ld t3, 0(t3)\n" ++
  "  srl t3, t3, t1\n" ++ "  andi t3, t3, 1\n" ++
  "  beqz t3, .Lmexp_next_bit\n" ++
  -- product = result * base
  "  la a0, modexp_bn_result\n" ++ "  mv a1, s7\n" ++
  "  la a2, modexp_bn_base\n" ++ "  mv a3, s7\n" ++
  "  la a4, modexp_bn_product\n" ++
  "  jal ra, modexp_mul\n" ++
  -- result = product mod modulus
  "  la a0, modexp_bn_product\n" ++
  "  li a1, 0\n" ++ "  add a1, s7, s7\n" ++
  "  la a2, modexp_bn_mod\n" ++ "  mv a3, s7\n" ++
  "  la a4, modexp_bn_result\n" ++
  "  jal ra, modexp_binmod\n" ++
  ".Lmexp_next_bit:\n" ++
  "  addi s10, s10, -1\n" ++
  "  bgez s10, .Lmexp_sqmul\n" ++
  -- Format output: result (nm LE limbs) → output (Mlen BE bytes)
  ".Lmexp_format:\n" ++
  "  la a0, modexp_bn_result\n" ++ "  mv a1, s7\n" ++
  "  mv a2, s6\n" ++ "  mv a3, s5\n" ++
  "  jal ra, modexp_le_to_be\n" ++
  ".Lmexp_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lmexp_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp)\n" ++ "  ld s1, 16(sp)\n" ++
  "  ld s2, 24(sp)\n" ++ "  ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++ "  ld s5, 48(sp)\n" ++
  "  ld s6, 56(sp)\n" ++ "  ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++ "  ld s9, 80(sp)\n" ++
  "  ld s10, 88(sp)\n" ++ "  ld s11, 96(sp)\n" ++
  "  addi sp, sp, 128\n" ++
  "  ret\n" ++
  ".Lmexp_modzero:\n" ++
  -- Fill output with Mlen zeros
  "  mv t0, s6\n" ++ "  mv t1, s5\n" ++
  ".Lmexp_mz_loop:\n" ++ "  beqz t1, .Lmexp_ok\n" ++
  "  sb zero, 0(t0)\n" ++ "  addi t0, t0, 1\n" ++ "  addi t1, t1, -1\n" ++
  "  j .Lmexp_mz_loop\n" ++
  ".Lmexp_err:\n" ++
  "  li a0, -1\n" ++ "  j .Lmexp_ret\n"

end EvmAsm.Codegen
