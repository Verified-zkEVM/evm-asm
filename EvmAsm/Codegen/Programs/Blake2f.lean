/-
  EvmAsm.Codegen.Programs.Blake2f

  The EIP-152 BLAKE2F (0x09) compression kernel `zkvm_blake2f`,
  mirroring execution-specs `ethereum.crypto.blake2.Blake2b.compress`
  (RFC 7693 BLAKE2b F), backed by the ziskemu Blake2bRound accelerator:

    * SyscallBlake2bRound  csrs 0x819  (.4byte 0x81952073, a0 = param
      ptr).  param = {index, &state, &input}: ONE BLAKE2b round on the
      16-word working vector `state` with message words `input`, using
      SIGMA[index] (index = round mod 10, in [0,10)) — exactly the
      round function the F loop iterates (verified in /tmp/zisk
      precompiles/helpers/src/blake2/blake2b/round.rs).

  The kernel does the F scaffolding in software: build
  v = h || IV, v[12] ^= t0, v[13] ^= t1, v[14] ^= ~0 when f = 1, run
  `rounds` accelerator rounds (rounds is the attacker-controlled u32 —
  gas equal to it is charged upstream, so the loop bound is the actual
  value), then write h'[i] = h[i] ^ v[i] ^ v[i+8] back over the h
  buffer (the dispatch entry's success path emits those 64 bytes).

  All h/m/t reads and the h' write-back are BYTE accesses: the staged
  payload sits at frame offset +4, so the u64 words are only 4-aligned
  and the project forbids misaligned LD/SD.

  Kernel ABI (the `.L<tag>_blake2f` entry stages the 213-byte payload,
  charges `rounds` gas, and validates f <= 1 before the call):

    zkvm_blake2f(a0 = rounds (u32), a1 = h (64 B), a2 = m (128 B),
                 a3 = t (16 B), a4 = f (0/1))
      -> a0 = 0 always (no input can fail past the upstream gates);
         the updated h is written in place at a1.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- BLAKE2F data labels WITHOUT a `.section .data` header. -/
def blake2fDataFragment : String :=
  ".balign 8\n" ++
  -- RFC 7693 BLAKE2b IV
  "blk2_iv:\n" ++
  "  .quad 0x6a09e667f3bcc908, 0xbb67ae8584caa73b\n" ++
  "  .quad 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1\n" ++
  "  .quad 0x510e527fade682d1, 0x9b05688c2b3e6c1f\n" ++
  "  .quad 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179\n" ++
  -- 16-word working vector + 16 message words (accelerator operands)
  "blk2_v:\n  .zero 128\n" ++
  "blk2_m:\n  .zero 128\n" ++
  -- Blake2bRound {index, &state, &input} parameter block (index is
  -- rewritten every round)
  "blk2_params:\n" ++
  "  .quad 0, blk2_v, blk2_m\n"

/-- Load the little-endian u64 at byte pointer a0 (any alignment) into
    a0. Leaf; clobbers t0..t2. -/
def blk2LdLe64_prog : Program :=
  [ .LI .x5 (0 : Word),
    .ADDI .x6 .x10 (7 : BitVec 12),
    .LI .x7 (8 : Word),
    .SLLI .x5 .x5 (8 : BitVec 6),
    .LBU .x10 .x6 (0 : BitVec 12),
    .OR .x5 .x5 .x10,
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-20 : BitVec 13),
    .MV .x10 .x5,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def blake2fLdLe64Function : String :=
  "blk2_ld_le64:\n" ++ emitProgram blk2LdLe64_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blk2LdLe64_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem blake2fLdLe64Function_eq_prog :
    blake2fLdLe64Function = "blk2_ld_le64:\n" ++ emitProgram blk2LdLe64_prog := rfl

#guard blake2fLdLe64Function.startsWith "blk2_ld_le64:\n"
/-- Store a1 as a little-endian u64 at byte pointer a0 (any
    alignment). Leaf; clobbers t0..t2. -/
def blk2StLe64_prog : Program :=
  [ .MV .x5 .x11,
    .MV .x6 .x10,
    .LI .x7 (8 : Word),
    .ANDI .x11 .x5 (255 : BitVec 12),
    .SB .x6 .x11 (0 : BitVec 12),
    .SRLI .x5 .x5 (8 : BitVec 6),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-20 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def blake2fStLe64Function : String :=
  "blk2_st_le64:\n" ++ emitProgram blk2StLe64_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blk2StLe64_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem blake2fStLe64Function_eq_prog :
    blake2fStLe64Function = "blk2_st_le64:\n" ++ emitProgram blk2StLe64_prog := rfl

#guard blake2fStLe64Function.startsWith "blk2_st_le64:\n"
/-- Real BLAKE2F kernel (see the module docstring for the ABI). -/
def zkvmBlake2fRealFunction : String :=
  ".globl zkvm_blake2f\n" ++
  "zkvm_blake2f:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                      # rounds\n" ++
  "  mv s1, a1                      # h (64 B, byte access)\n" ++
  "  mv s2, a2                      # m (128 B, byte access)\n" ++
  "  mv s3, a3                      # t (16 B, byte access)\n" ++
  "  mv s4, a4                      # f flag (0/1)\n" ++
  -- v[0..8) = h
  "  li s5, 0\n" ++
  ".Lblk2_load_h:\n" ++
  "  slli t3, s5, 3\n" ++
  "  add a0, s1, t3\n" ++
  "  jal ra, blk2_ld_le64\n" ++
  "  la t3, blk2_v\n" ++
  "  slli t4, s5, 3\n" ++
  "  add t3, t3, t4\n" ++
  "  sd a0, 0(t3)\n" ++
  "  addi s5, s5, 1\n" ++
  "  li t3, 8\n" ++
  "  bne s5, t3, .Lblk2_load_h\n" ++
  -- v[8..16) = IV
  "  la t0, blk2_iv\n" ++
  "  la t1, blk2_v\n" ++
  "  addi t1, t1, 64\n" ++
  "  li t2, 8\n" ++
  ".Lblk2_load_iv:\n" ++
  "  ld t3, 0(t0)\n" ++
  "  sd t3, 0(t1)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lblk2_load_iv\n" ++
  -- v[12] ^= t0, v[13] ^= t1
  "  mv a0, s3\n" ++
  "  jal ra, blk2_ld_le64\n" ++
  "  la t3, blk2_v\n" ++
  "  ld t4, 96(t3)\n" ++
  "  xor t4, t4, a0\n" ++
  "  sd t4, 96(t3)\n" ++
  "  addi a0, s3, 8\n" ++
  "  jal ra, blk2_ld_le64\n" ++
  "  la t3, blk2_v\n" ++
  "  ld t4, 104(t3)\n" ++
  "  xor t4, t4, a0\n" ++
  "  sd t4, 104(t3)\n" ++
  -- v[14] ^= 0xff..ff when the final-block flag is set
  "  beqz s4, .Lblk2_no_final\n" ++
  "  la t3, blk2_v\n" ++
  "  ld t4, 112(t3)\n" ++
  "  not t4, t4\n" ++
  "  sd t4, 112(t3)\n" ++
  ".Lblk2_no_final:\n" ++
  -- m[0..16)
  "  li s5, 0\n" ++
  ".Lblk2_load_m:\n" ++
  "  slli t3, s5, 3\n" ++
  "  add a0, s2, t3\n" ++
  "  jal ra, blk2_ld_le64\n" ++
  "  la t3, blk2_m\n" ++
  "  slli t4, s5, 3\n" ++
  "  add t3, t3, t4\n" ++
  "  sd a0, 0(t3)\n" ++
  "  addi s5, s5, 1\n" ++
  "  li t3, 16\n" ++
  "  bne s5, t3, .Lblk2_load_m\n" ++
  -- `rounds` accelerator rounds, SIGMA index = round mod 10
  "  li s5, 0\n" ++
  ".Lblk2_round:\n" ++
  "  bgeu s5, s0, .Lblk2_finalize\n" ++
  "  li t0, 10\n" ++
  "  remu t1, s5, t0\n" ++
  "  la a0, blk2_params\n" ++
  "  sd t1, 0(a0)\n" ++
  "  .4byte 0x81952073              # csrs 0x819, a0 -> Blake2bRound\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lblk2_round\n" ++
  ".Lblk2_finalize:\n" ++
  -- h'[i] = h[i] ^ v[i] ^ v[i+8]
  "  li s5, 0\n" ++
  ".Lblk2_out:\n" ++
  "  slli t3, s5, 3\n" ++
  "  add a0, s1, t3\n" ++
  "  jal ra, blk2_ld_le64\n" ++
  "  la t3, blk2_v\n" ++
  "  slli t4, s5, 3\n" ++
  "  add t3, t3, t4\n" ++
  "  ld t5, 0(t3)\n" ++
  "  ld t6, 64(t3)\n" ++
  "  xor a1, t5, t6\n" ++
  "  xor a1, a1, a0\n" ++
  "  slli t3, s5, 3\n" ++
  "  add a0, s1, t3\n" ++
  "  jal ra, blk2_st_le64\n" ++
  "  addi s5, s5, 1\n" ++
  "  li t3, 8\n" ++
  "  bne s5, t3, .Lblk2_out\n" ++
  "  li a0, 0\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- The BLAKE2F kernel suite (self-contained: byte helpers + kernel). -/
def blake2fKernelFunctions : String :=
  blake2fLdLe64Function ++ "\n" ++
  blake2fStLe64Function ++ "\n" ++
  zkvmBlake2fRealFunction

/-- Probe: input at `0x40000008` = the raw 213-byte EIP-152 payload
    `rounds(be32) || h(64) || m(128) || t(16) || f(1)`. The h block is
    staged into a `.data` buffer (the ziskemu input region is not
    writable). Output: status u64 at OUTPUT+0, final h at OUTPUT+8. -/
def ziskBlake2fRealProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000008\n" ++
  -- rounds = BE32 at +0
  "  lbu t0, 0(s0)\n" ++
  "  slli t0, t0, 24\n" ++
  "  lbu t1, 1(s0)\n" ++
  "  slli t1, t1, 16\n" ++
  "  or t0, t0, t1\n" ++
  "  lbu t1, 2(s0)\n" ++
  "  slli t1, t1, 8\n" ++
  "  or t0, t0, t1\n" ++
  "  lbu t1, 3(s0)\n" ++
  "  or s1, t0, t1\n" ++
  -- stage h into the writable buffer
  "  la t0, blk2_probe_h\n" ++
  "  addi t1, s0, 4\n" ++
  "  li t2, 64\n" ++
  ".Lblk2_probe_stage:\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  sb t3, 0(t0)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lblk2_probe_stage\n" ++
  "  mv a0, s1\n" ++
  "  la a1, blk2_probe_h\n" ++
  "  addi a2, s0, 68\n" ++
  "  addi a3, s0, 196\n" ++
  "  lbu a4, 212(s0)\n" ++
  "  jal ra, zkvm_blake2f\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, blk2_probe_h\n" ++
  "  addi t0, t0, 8\n" ++
  "  li t2, 64\n" ++
  ".Lblk2_probe_out:\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  sb t3, 0(t0)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lblk2_probe_out\n" ++
  "  j .Lblk2_probe_done\n" ++
  blake2fKernelFunctions ++ "\n" ++
  ".Lblk2_probe_done:"

def ziskBlake2fRealProbeDataSection : String :=
  ".section .data\n" ++
  blake2fDataFragment ++
  "blk2_probe_h:\n  .zero 64\n"


end EvmAsm.Codegen
