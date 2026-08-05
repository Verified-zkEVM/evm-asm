/-
  EvmAsm.Codegen.Programs.Bls12Fq12

  BLS12-381 FQ12 polynomial machine + projective point/line layer for
  the EIP-2537 pairing precompile (0x0f), cloning the proven BN254
  recipe (Bn254Fq12 / Bn254Fq12Point, PR #8731).

  Mirrors py_ecc's `optimized_bls12_381_FQ12` (the field execution-specs
  computes BLS pairings in): FQ12 = Fp[w] / (w^12 - 2 w^6 + 2). An
  element is a 576-byte, 8-aligned buffer of 12 coefficients, each a
  48-byte little-endian Fp value (the `Arith384Mod` operand format).

  Every coefficient operation is ONE Arith384Mod call (csrs 0x80B,
  d = (a*b + c) mod p), exploiting the fused multiply-add:

    * mul accumulation:  acc[i+j] = a[i]*b[j] + acc[i+j]
    * reduction (k = 22..12):  acc[k-6] += 2*acc[k];
                               acc[k-12] += (p-2)*acc[k]
    * add:  d = (a*1 + b);  sub:  d = (b*(p-1) + a);  smul: d = (a*c + 0)

  `blq_pow` is the generic MSB-first square-and-multiply for the
  denominator inverse (x^(p^12 - 2), top bit 4568) and the final
  exponentiation (x^((p^12-1)/n), top bit 4313); exponents are baked
  LE-limb constants. Unlike BN254, the BLS Miller loop needs no
  Frobenius coordinate powers (py_ecc's extra lines are absent), so
  no x^p exponent is baked.

  A projective FQ12 point is X || Y || Z, 576 bytes each (1728 total);
  the identity has Z = 0. `blq_pt_double`/`blq_pt_add`/`blq_linefunc`
  port py_ecc `optimized_curve.double/add` and
  `optimized_pairing.linefunc` verbatim, computing through the static
  temp pool `blq_d0..blq_d9` so dst-aliases-src is safe.

  Labels are `blq_`-prefixed; depends on `Bls12Field`'s `blsf_le_p` /
  `blsf_le_zero` / `blsf_le_one` and `Bls12G2`'s `blsg2_pm1_le`.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.Bls12G2

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- FQ12-machine data labels WITHOUT a `.section .data` header. Exponent
    constants are LE u64 limbs, least-significant first. -/
def bls12Fq12DataFragment : String :=
  ".balign 8\n" ++
  -- (p^12 - 1) / n -- the final exponentiation (top bit 4313).
"blq_exp_final_le:\n" ++
"  .quad 0xC0BCB9B55DF57510, 0x25F98630E68BFB24\n" ++
"  .quad 0x4406FBC8FBD5F489, 0x8E2F8491D12191A0\n" ++
"  .quad 0x3E9D71650A6F8069, 0x226C2F011D4CAB80\n" ++
"  .quad 0x67F67C4717489119, 0xAF3F881BD88592D7\n" ++
"  .quad 0x1A67E49EEED2161D, 0xE5B78C7869AEB218\n" ++
"  .quad 0xF6539314043F7BBC, 0x73F62537F2701AAE\n" ++
"  .quad 0xAFF1C910E9622D2A, 0x6283313492CAA9D4\n" ++
"  .quad 0x2E2F3EC2BEA83D19, 0xA4C7E79FB02FAA73\n" ++
"  .quad 0x6C49637FD7961BE1, 0x08E88ADCE8817745\n" ++
"  .quad 0x35DE3F7A36399917, 0x9C1D9F7C31759C36\n" ++
"  .quad 0xFA9E13C24EA820B0, 0x3FC56947A403577D\n" ++
"  .quad 0xA4C1B6DCFC5CCEB7, 0x1BBD81367066BCA6\n" ++
"  .quad 0x0418A3EF0BC62775, 0x49BF9B71A9F9E010\n" ++
"  .quad 0x511291097DB60B17, 0x498345C6E5308F1C\n" ++
"  .quad 0x6D8823B19DADD7C2, 0x92004CEDD556952C\n" ++
"  .quad 0x4C6BEC3EC03EF195, 0x0A1FAD20044CE6AD\n" ++
"  .quad 0xC55D3109CD15948D, 0x334F46C02C3F0BD0\n" ++
"  .quad 0x3B5A62EB34C05739, 0x724538411D1676A5\n" ++
"  .quad 0x127A1B5AD0463434, 0x61A474C5C85B0129\n" ++
"  .quad 0x8DFC8E2886EF965E, 0x96532FEF459F1243\n" ++
"  .quad 0x40EE7169CDC10412, 0x9C40A68EB74BB22A\n" ++
"  .quad 0x25118790F4684D0B, 0x596BC293C8D4C01F\n" ++
"  .quad 0x1064837F27611212, 0x077FFB10BF24DDE4\n" ++
"  .quad 0xC49F570BCD2B01F3, 0x1A0C5BF24C374693\n" ++
"  .quad 0x350DA5359BC73AB6, 0xD2670D93E4D7ACDD\n" ++
"  .quad 0xD39099B86E1AB656, 0x19328148978E2B0D\n" ++
"  .quad 0xB113F414386B0E88, 0x07A0DCE2630D9AA4\n" ++
"  .quad 0xA927E7BB93753318, 0xE347AA68AD49466F\n" ++
"  .quad 0x1C0AD0D6106FEAF4, 0xC872EE83FF3A0F0F\n" ++
"  .quad 0x074E43B9A660835C, 0xC0AADFF5E9CFEE9A\n" ++
"  .quad 0x30698E8CC7DEADA9, 0xD1073776AB353F2C\n" ++
"  .quad 0x17848517BADC3A43, 0x7363BAA13F8D14A9\n" ++
"  .quad 0xD4977B3F7D4507D0, 0x496A1C0A89EE0193\n" ++
"  .quad 0xDCC825B7E1BDA9C0, 0x0000000002EE1DB5\n" ++
  -- p^12 - 2 -- the Fermat denominator inverse (top bit 4568).
"blq_exp_p12m2_le:\n" ++
"  .quad 0x62C744A55DF5750F, 0xD3B1E26013CB8C5F\n" ++
"  .quad 0xEDF5C811787440CA, 0x6C472B23FE0A4404\n" ++
"  .quad 0xA4F205EC6A671502, 0xFF7C1B6D6BDAC24A\n" ++
"  .quad 0xAB0A7E582A7B5E07, 0x99D2F0B43D8D1A60\n" ++
"  .quad 0xF31981D7D0E4E506, 0xA81C8D0F9FA5D596\n" ++
"  .quad 0xC1B96ABE4025A6BC, 0xF111F3E10DA00C2D\n" ++
"  .quad 0x93A3550E008D2706, 0x298AD0E0746A76C9\n" ++
"  .quad 0x7565667E0DF65084, 0xF431874BF14B35E3\n" ++
"  .quad 0x55EDA580C1C021E7, 0xCBAE5B811FF5F8C2\n" ++
"  .quad 0xAC58EB17C75F6BF9, 0xC1BDF2D5D1271A16\n" ++
"  .quad 0x1649649D9B6079A0, 0xC7EA012AB366245B\n" ++
"  .quad 0x23F2C2CAA01E2A99, 0x67CCBC9B6FD5E1CD\n" ++
"  .quad 0xDF58F8DA2146E4AF, 0xE4F3187883EBC03F\n" ++
"  .quad 0x2E494ECE31E1B32A, 0xC291EFE608C163FA\n" ++
"  .quad 0xCBEBBA45303BD69E, 0xBE58F5C703D2B80A\n" ++
"  .quad 0xA7AC121BA3CBFCAF, 0xE44083C2D0584BF5\n" ++
"  .quad 0xFEC4E94FC9C7B3FD, 0x2FF0CF2FFF40D6F9\n" ++
"  .quad 0x1F98D0BE6C414817, 0xA3F8EA390E9FF4BF\n" ++
"  .quad 0x4D9451D87EE67302, 0xD6DC5DEF93A5D633\n" ++
"  .quad 0x45602A826845A82D, 0xFE3C3B516ABF33B6\n" ++
"  .quad 0xBDDCF8763EE19D8F, 0xB6EA05C2DE805991\n" ++
"  .quad 0xFF9ABDCE2DC7C0A5, 0xF833BFDD0955D2F1\n" ++
"  .quad 0x93DA4CD7FB3141E2, 0x6B03F80C34146533\n" ++
"  .quad 0x37ACA6E6D99EB066, 0x1B327E40ACB32FE2\n" ++
"  .quad 0xAE8A4CE79FCDE8EA, 0x8F8472729AAAEDB4\n" ++
"  .quad 0x642E5A83FEF623C6, 0x37C65EFC47F57973\n" ++
"  .quad 0x9C0060FA5BA81813, 0x294967A4B8CB0CB2\n" ++
"  .quad 0x24034CC13376A888, 0x29ED98173E0C0DBA\n" ++
"  .quad 0x46370235EA4C49C8, 0x304A4B185DE305DA\n" ++
"  .quad 0x5C4965D638225B1D, 0x80755386AFB51863\n" ++
"  .quad 0x48629ECB062D9508, 0xC0733C38646D197B\n" ++
"  .quad 0xE83C9BDFCC1C6E6D, 0x90940D05E77956F9\n" ++
"  .quad 0x55B295CF4C5FA504, 0x95E0F7D136AE8028\n" ++
"  .quad 0x147DD8168333D204, 0x81765D291A5164A0\n" ++
"  .quad 0x3A38D4F9BD01E313, 0xB2F3F2D39221E38B\n" ++
"  .quad 0x7C9A83731C1814DE, 0x000000000153AFB4\n" ++
  -- Small scalar constants (48-byte LE Fp).
  "blq_le_2:\n  .quad 2, 0, 0, 0, 0, 0\n" ++
  "blq_le_3:\n  .quad 3, 0, 0, 0, 0, 0\n" ++
  "blq_le_4:\n  .quad 4, 0, 0, 0, 0, 0\n" ++
  "blq_le_8:\n  .quad 8, 0, 0, 0, 0, 0\n" ++
  -- p - 2 (the w^12 reduction fold multiplier, LE limbs).
  "blq_le_pm2:\n" ++
  "  .quad 0xb9feffffffffaaa9, 0x1eabfffeb153ffff\n" ++
  "  .quad 0x6730d2a0f6b0f624, 0x64774b84f38512bf\n" ++
  "  .quad 0x4b1ba7b6434bacd7, 0x1a0111ea397fe69a\n" ++
  -- Dynamic Arith384Mod parameter block {a, b, c, module, d}.
  "blq_arith_params:\n  .zero 40\n" ++
  -- Schoolbook product accumulator (23 x 48 B) and the pow temporary.
  ".balign 8\n" ++
  "blq_acc:\n  .zero 1104\n" ++
  "blq_powt:\n  .zero 576\n"

/-- FQ12 dst = a * b mod (w^12 - 2 w^6 + 2). a0 = dst, a1 = a, a2 = b.
    The product is composed in `blq_acc` and copied out, so dst may
    alias a/b; a may alias b (squaring). -/
def bls12Fq12MulFunction : String :=
  "blq_mul:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  la t0, blq_acc\n" ++
  "  li t1, 138\n" ++
  ".Lblq_mul_zero:\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .Lblq_mul_zero\n" ++
  "  li s3, 0                       # i\n" ++
  ".Lblq_mul_i:\n" ++
  "  li s4, 0                       # j\n" ++
  ".Lblq_mul_j:\n" ++
  "  slli t1, s3, 4\n" ++
  "  slli t5, s3, 5\n" ++
  "  add t1, t1, t5\n" ++
  "  add t1, s1, t1                 # &a[i]  (stride 48)\n" ++
  "  slli t2, s4, 4\n" ++
  "  slli t5, s4, 5\n" ++
  "  add t2, t2, t5\n" ++
  "  add t2, s2, t2                 # &b[j]\n" ++
  "  add t3, s3, s4\n" ++
  "  slli t5, t3, 4\n" ++
  "  slli t3, t3, 5\n" ++
  "  add t3, t3, t5\n" ++
  "  la t4, blq_acc\n" ++
  "  add t3, t4, t3                 # &acc[i+j]\n" ++
  "  la t0, blq_arith_params\n" ++
  "  sd t1, 0(t0)\n" ++
  "  sd t2, 8(t0)\n" ++
  "  sd t3, 16(t0)\n" ++
  "  la t1, blsf_le_p\n" ++
  "  sd t1, 24(t0)\n" ++
  "  sd t3, 32(t0)\n" ++
  "  mv a0, t0\n" ++
  "  .4byte 0x80b52073              # acc[i+j] = a[i]*b[j] + acc[i+j]\n" ++
  "  addi s4, s4, 1\n" ++
  "  li t0, 12\n" ++
  "  bne s4, t0, .Lblq_mul_j\n" ++
  "  addi s3, s3, 1\n" ++
  "  li t0, 12\n" ++
  "  bne s3, t0, .Lblq_mul_i\n" ++
  -- Cascading reduction by w^12 = 2 w^6 - 2, high coefficient first so
  -- the k-6 fold lands before that slot is itself reduced.
  "  li s3, 22                      # k\n" ++
  ".Lblq_mul_red:\n" ++
  "  la t4, blq_acc\n" ++
  "  slli t1, s3, 4\n" ++
  "  slli t5, s3, 5\n" ++
  "  add t1, t1, t5\n" ++
  "  add t1, t4, t1                 # &acc[k]\n" ++
  "  addi t2, s3, -6\n" ++
  "  slli t5, t2, 4\n" ++
  "  slli t2, t2, 5\n" ++
  "  add t2, t2, t5\n" ++
  "  add t2, t4, t2                 # &acc[k-6]\n" ++
  "  la t0, blq_arith_params\n" ++
  "  sd t1, 0(t0)\n" ++
  "  la t3, blq_le_2\n" ++
  "  sd t3, 8(t0)\n" ++
  "  sd t2, 16(t0)\n" ++
  "  la t3, blsf_le_p\n" ++
  "  sd t3, 24(t0)\n" ++
  "  sd t2, 32(t0)\n" ++
  "  mv a0, t0\n" ++
  "  .4byte 0x80b52073              # acc[k-6] += 2*acc[k]\n" ++
  "  la t4, blq_acc\n" ++
  "  li t5, 48\n" ++
  "  mul t1, s3, t5\n" ++
  "  add t1, t4, t1                 # &acc[k] (recompute)\n" ++
  "  addi t2, s3, -12\n" ++
  "  mul t2, t2, t5\n" ++
  "  add t2, t4, t2                 # &acc[k-12]\n" ++
  "  la t0, blq_arith_params\n" ++
  "  sd t1, 0(t0)\n" ++
  "  la t3, blq_le_pm2\n" ++
  "  sd t3, 8(t0)\n" ++
  "  sd t2, 16(t0)\n" ++
  "  la t3, blsf_le_p\n" ++
  "  sd t3, 24(t0)\n" ++
  "  sd t2, 32(t0)\n" ++
  "  mv a0, t0\n" ++
  "  .4byte 0x80b52073              # acc[k-12] += (p-2)*acc[k]\n" ++
  "  addi s3, s3, -1\n" ++
  "  li t0, 11\n" ++
  "  bne s3, t0, .Lblq_mul_red\n" ++
  "  la t0, blq_acc\n" ++
  "  mv t1, s0\n" ++
  "  li t2, 72\n" ++
  ".Lblq_mul_copy:\n" ++
  "  ld t3, 0(t0)\n" ++
  "  sd t3, 0(t1)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lblq_mul_copy\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- Coefficient-wise binary helper: a0 = dst, a1 = a, a2 = b, all FQ12.
    12-iteration loop with the given Arith384Mod operand order. -/
private def blq12LoopFunction (name aSlot bSlot cSlot : String) : String :=
  let slot (s : String) (reg : String) : String :=
    if s = "a" then "  sd t1, " ++ reg ++ "(t0)\n"
    else if s = "b" then "  sd t2, " ++ reg ++ "(t0)\n"
    else "  la t4, " ++ s ++ "\n  sd t4, " ++ reg ++ "(t0)\n"
  name ++ ":\n" ++
  "  li t5, 12\n" ++
  ".L" ++ name ++ "_loop:\n" ++
  "  mv t1, a1\n" ++
  "  mv t2, a2\n" ++
  "  la t0, blq_arith_params\n" ++
  slot aSlot "0" ++
  slot bSlot "8" ++
  slot cSlot "16" ++
  "  la t4, blsf_le_p\n" ++
  "  sd t4, 24(t0)\n" ++
  "  sd a0, 32(t0)\n" ++
  "  mv t6, a0\n" ++
  "  mv a0, t0\n" ++
  "  .4byte 0x80b52073\n" ++
  "  addi a0, t6, 48\n" ++
  "  addi a1, a1, 48\n" ++
  "  addi a2, a2, 48\n" ++
  "  addi t5, t5, -1\n" ++
  "  bnez t5, .L" ++ name ++ "_loop\n" ++
  "  ret"

/-- FQ12 dst = a + b (coefficient-wise d = (a*1 + b)). Aliasing allowed. -/
def bls12Fq12AddFunction : String :=
  blq12LoopFunction "blq_add" "a" "blsf_le_one" "b"

/-- FQ12 dst = a - b (coefficient-wise d = (b*(p-1) + a)). Aliasing allowed. -/
def bls12Fq12SubFunction : String :=
  blq12LoopFunction "blq_sub" "b" "blsg2_pm1_le" "a"

/-- FQ12 dst = a * s for a 48-byte LE Fp scalar at a2 (coefficient-wise
    d = (a*s + 0)). Aliasing allowed; pass the scalar CELL in a2. -/
def blqSmul_prog : Program :=
  [ .LI .x30 (12 : Word),
    .AUIPC .x5 (laHi GuestAddrs.blq_arith_params (GuestAddrs.blq_smul + 4)),
    .ADDI .x5 .x5 (laLo GuestAddrs.blq_arith_params (GuestAddrs.blq_smul + 4)),
    .SD .x5 .x11 (0 : BitVec 12),
    .SD .x5 .x12 (8 : BitVec 12),
    .AUIPC .x29 (laHi GuestAddrs.blsf_le_zero (GuestAddrs.blq_smul + 20)),
    .ADDI .x29 .x29 (laLo GuestAddrs.blsf_le_zero (GuestAddrs.blq_smul + 20)),
    .SD .x5 .x29 (16 : BitVec 12),
    .AUIPC .x29 (laHi GuestAddrs.blsf_le_p (GuestAddrs.blq_smul + 32)),
    .ADDI .x29 .x29 (laLo GuestAddrs.blsf_le_p (GuestAddrs.blq_smul + 32)),
    .SD .x5 .x29 (24 : BitVec 12),
    .SD .x5 .x10 (32 : BitVec 12),
    .MV .x31 .x10,
    .MV .x10 .x5,
    .CSRS (2059 : BitVec 12) .x10,
    .ADDI .x10 .x31 (48 : BitVec 12),
    .ADDI .x11 .x11 (48 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .BNE .x30 .x0 (-68 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blqSmul_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blqSmul_relocs : RelocTable :=
  [ (1, .la .x5 "blq_arith_params"),
    (5, .la .x29 "blsf_le_zero"),
    (8, .la .x29 "blsf_le_p") ]

def bls12Fq12SMulFunction : String :=
  "blq_smul:\n" ++ emitProgramR blqSmul_prog blqSmul_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blqSmul_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12Fq12SMulFunction_eq_prog :
    bls12Fq12SMulFunction = "blq_smul:\n" ++ emitProgramR blqSmul_prog blqSmul_relocs := rfl

#guard bls12Fq12SMulFunction.startsWith "blq_smul:\n"
#guard blqSmul_prog.length = 20
/-- Copy a 576-byte FQ12 value: a0 = src, a1 = dst. -/
def blqCopy_prog : Program :=
  [ .LI .x7 (72 : Word),
    .LD .x28 .x10 (0 : BitVec 12),
    .SD .x11 .x28 (0 : BitVec 12),
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x11 .x11 (8 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-20 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bls12Fq12CopyFunction : String :=
  "blq_copy:\n" ++ emitProgram blqCopy_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blqCopy_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bls12Fq12CopyFunction_eq_prog :
    bls12Fq12CopyFunction = "blq_copy:\n" ++ emitProgram blqCopy_prog := rfl

#guard bls12Fq12CopyFunction.startsWith "blq_copy:\n"
#guard blqCopy_prog.length = 8
/-- Zero a 576-byte FQ12 value at a0. -/
def blqZero_prog : Program :=
  [ .LI .x7 (72 : Word),
    .SD .x10 .x0 (0 : BitVec 12),
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-12 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bls12Fq12ZeroFunction : String :=
  "blq_zero:\n" ++ emitProgram blqZero_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blqZero_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bls12Fq12ZeroFunction_eq_prog :
    bls12Fq12ZeroFunction = "blq_zero:\n" ++ emitProgram blqZero_prog := rfl

#guard bls12Fq12ZeroFunction.startsWith "blq_zero:\n"
#guard blqZero_prog.length = 6
/-- Set the FQ12 at a0 to one (coefficient 0 = 1, rest 0). -/
def blqSetOne_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .MV .x8 .x10,
    .JAL .x1 (jalOff GuestAddrs.blq_zero (GuestAddrs.blq_set_one + 16)),
    .LI .x5 (1 : Word),
    .SD .x8 .x5 (0 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blqSetOne_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blqSetOne_relocs : RelocTable :=
  [ (4, .jal .x1 "blq_zero") ]

def bls12Fq12SetOneFunction : String :=
  "blq_set_one:\n" ++ emitProgramR blqSetOne_prog blqSetOne_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blqSetOne_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12Fq12SetOneFunction_eq_prog :
    bls12Fq12SetOneFunction = "blq_set_one:\n" ++ emitProgramR blqSetOne_prog blqSetOne_relocs := rfl

#guard bls12Fq12SetOneFunction.startsWith "blq_set_one:\n"
#guard blqSetOne_prog.length = 11
/-- a0 = 1 iff the FQ12 values at a0/a1 are limb-identical (reduced). -/
def blqEq_prog : Program :=
  [ .LI .x5 (72 : Word),
    .BEQ .x5 .x0 (32 : BitVec 13),
    .LD .x6 .x10 (0 : BitVec 12),
    .LD .x7 .x11 (0 : BitVec 12),
    .BNE .x6 .x7 (28 : BitVec 13),
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x11 .x11 (8 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bls12Fq12EqFunction : String :=
  "blq_eq:\n" ++ emitProgram blqEq_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blqEq_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bls12Fq12EqFunction_eq_prog :
    bls12Fq12EqFunction = "blq_eq:\n" ++ emitProgram blqEq_prog := rfl

#guard bls12Fq12EqFunction.startsWith "blq_eq:\n"
#guard blqEq_prog.length = 13
/-- a0 = 1 iff the FQ12 value at a0 is zero. -/
def blqIsZero_prog : Program :=
  [ .LI .x5 (72 : Word),
    .LI .x6 (0 : Word),
    .BEQ .x5 .x0 (24 : BitVec 13),
    .LD .x7 .x10 (0 : BitVec 12),
    .OR .x6 .x6 .x7,
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .SLTIU .x10 .x6 (1 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bls12Fq12IsZeroFunction : String :=
  "blq_is_zero:\n" ++ emitProgram blqIsZero_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blqIsZero_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bls12Fq12IsZeroFunction_eq_prog :
    bls12Fq12IsZeroFunction = "blq_is_zero:\n" ++ emitProgram blqIsZero_prog := rfl

#guard bls12Fq12IsZeroFunction.startsWith "blq_is_zero:\n"
#guard blqIsZero_prog.length = 10
/-- FQ12 dst = base ^ exp, MSB-first square-and-multiply from bit a3
    down to 0. a0 = dst, a1 = base, a2 = exp (LE limbs), a3 = top bit
    index. dst must NOT alias base; clobbers `blq_powt` and `blq_acc`. -/
def blqPow_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.blq_set_one (GuestAddrs.blq_pow + 44)),
    .AUIPC .x10 (laHi GuestAddrs.blq_powt (GuestAddrs.blq_pow + 48)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blq_powt (GuestAddrs.blq_pow + 48)),
    .MV .x11 .x8,
    .MV .x12 .x8,
    .JAL .x1 (jalOff GuestAddrs.blq_mul (GuestAddrs.blq_pow + 64)),
    .AUIPC .x10 (laHi GuestAddrs.blq_powt (GuestAddrs.blq_pow + 68)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blq_powt (GuestAddrs.blq_pow + 68)),
    .MV .x11 .x8,
    .JAL .x1 (jalOff GuestAddrs.blq_copy (GuestAddrs.blq_pow + 80)),
    .SRLI .x5 .x19 (6 : BitVec 6),
    .SLLI .x5 .x5 (3 : BitVec 6),
    .ADD .x5 .x18 .x5,
    .LD .x6 .x5 (0 : BitVec 12),
    .ANDI .x7 .x19 (63 : BitVec 12),
    .SRL .x6 .x6 .x7,
    .ANDI .x6 .x6 (1 : BitVec 12),
    .BEQ .x6 .x0 (40 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.blq_powt (GuestAddrs.blq_pow + 116)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blq_powt (GuestAddrs.blq_pow + 116)),
    .MV .x11 .x8,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.blq_mul (GuestAddrs.blq_pow + 132)),
    .AUIPC .x10 (laHi GuestAddrs.blq_powt (GuestAddrs.blq_pow + 136)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blq_powt (GuestAddrs.blq_pow + 136)),
    .MV .x11 .x8,
    .JAL .x1 (jalOff GuestAddrs.blq_copy (GuestAddrs.blq_pow + 148)),
    .BEQ .x19 .x0 (12 : BitVec 13),
    .ADDI .x19 .x19 (-1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.blq_pow + 48) (GuestAddrs.blq_pow + 160)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blqPow_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blqPow_relocs : RelocTable :=
  [ (11, .jal .x1 "blq_set_one"),
    (12, .la .x10 "blq_powt"),
    (16, .jal .x1 "blq_mul"),
    (17, .la .x10 "blq_powt"),
    (20, .jal .x1 "blq_copy"),
    (29, .la .x10 "blq_powt"),
    (33, .jal .x1 "blq_mul"),
    (34, .la .x10 "blq_powt"),
    (37, .jal .x1 "blq_copy") ]

def bls12Fq12PowFunction : String :=
  "blq_pow:\n" ++ emitProgramR blqPow_prog blqPow_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blqPow_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12Fq12PowFunction_eq_prog :
    bls12Fq12PowFunction = "blq_pow:\n" ++ emitProgramR blqPow_prog blqPow_relocs := rfl

#guard bls12Fq12PowFunction.startsWith "blq_pow:\n"
#guard blqPow_prog.length = 48
/-- The FQ12 machine suite. Guest-linked BLS12 FQ12: `blq_add` unlinked
    (never-ref; mul ends `ret`); KEEP mul/sub/smul/copy/zero/set_one/eq/is_zero/pow. -/
def bls12Fq12CommonFunctions : String :=
  bls12Fq12MulFunction ++ "\n" ++
  bls12Fq12SubFunction ++ "\n" ++
  bls12Fq12SMulFunction ++ "\n" ++
  bls12Fq12CopyFunction ++ "\n" ++
  bls12Fq12ZeroFunction ++ "\n" ++
  bls12Fq12SetOneFunction ++ "\n" ++
  bls12Fq12EqFunction ++ "\n" ++
  bls12Fq12IsZeroFunction ++ "\n" ++
  bls12Fq12PowFunction

end EvmAsm.Codegen
