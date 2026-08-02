/-
  EvmAsm.Codegen.Programs.Bn254Fq12

  BN254 FQ12 polynomial machine for the alt_bn128 ecPairing precompile
  (0x08), bead evm-asm-fhsxz.2.4.2.62.10.1 layer 2.

  Mirrors py_ecc's `optimized_bn128_FQ12` (the field execution-specs
  computes pairings in): FQ12 = Fp[w] / (w^12 - 18 w^6 + 82). An element
  is a 384-byte, 8-aligned buffer of 12 coefficients, each a 32-byte
  little-endian Fp value (the `Arith256Mod` operand format).

  Every coefficient operation is ONE Arith256Mod call (csrs 0x802,
  d = (a*b + c) mod p), exploiting the fused multiply-add:

    * mul accumulation:  acc[i+j] = a[i]*b[j] + acc[i+j]
    * reduction (k = 22..12):  acc[k-6] += 18*acc[k];
                               acc[k-12] += (p-82)*acc[k]
    * add:  d = (a*1 + b);  sub:  d = (b*(p-1) + a);  smul: d = (a*c + 0)

  `bnq_pow` is the generic MSB-first square-and-multiply used for the
  Frobenius coordinate powers (x^p), the denominator inverse
  (x^(p^12 - 2)), and the final exponentiation (x^((p^12-1)/n)); the
  exponents are baked LE-limb constants.

  Labels are `bnq_`-prefixed; depends on `Bn254Field`'s `bnf_le_p` /
  `bnf_le_zero` / `bnf_le_one`, `Bn254Fp2`'s `bnp_arith_params` scratch
  and `bnp_p_minus_1_le`.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.Bn254Fp2

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- FQ12-machine data labels WITHOUT a `.section .data` header. Exponent
    constants are LE u64 limbs, least-significant first. -/
def bn254Fq12DataFragment : String :=
  ".balign 8\n" ++
  -- (p^12 - 1) / n — the final exponentiation (2790 bits, top bit 2789).
  "bnq_exp_final_le:\n" ++
  "  .quad 0x86964B64CA86F120, 0x40A4EFB7E54523A4\n" ++
  "  .quad 0x837FA97896E84ABB, 0x361102B6B9B2B918\n" ++
  "  .quad 0xC0DE81DEF35692DA, 0xBE04C7E8A6C3C760\n" ++
  "  .quad 0xD766F9C9D570BB7F, 0xC230974D83561841\n" ++
  "  .quad 0x5BBA1668C3BE69A3, 0x7F3811C410526294\n" ++
  "  .quad 0x29BAEE7DDADDA71C, 0xBF813B8D145DA900\n" ++
  "  .quad 0x641BBADF423F9A2C, 0xA80BB4EA44EACC5E\n" ++
  "  .quad 0xCD65664814FDE37C, 0x4A0364B9580291D2\n" ++
  "  .quad 0xEE93DFB10826F0DD, 0x6B42DB8DC5514724\n" ++
  "  .quad 0xBB10CF430B0F3785, 0x40494E406F804216\n" ++
  "  .quad 0x55CFE107ACF3AAFB, 0x2088EC80E0EBAE87\n" ++
  "  .quad 0x846A3ED011A337A0, 0x48A45A4A1E3A5195\n" ++
  "  .quad 0xE5664568DFC50E16, 0xAB6A41294C0CC4EB\n" ++
  "  .quad 0x82D0D602D268C7DA, 0x6668449AED3CC48A\n" ++
  "  .quad 0x5062CD0FB2015DFC, 0x7F2940A8B1DDB3D1\n" ++
  "  .quad 0x77F5B63A2A226448, 0xFEF0781361E443AE\n" ++
  "  .quad 0xF977870E88D5C6C8, 0x790364A61F676BAA\n" ++
  "  .quad 0x5887E72ECEADDEA3, 0x1377E563A09A1B70\n" ++
  "  .quad 0x0C54EFEE1BD8C3B2, 0x3EC3D15AD524D8F7\n" ++
  "  .quad 0xDAF15466B2383A5D, 0xE1E30A73BB94FEC0\n" ++
  "  .quad 0x6A1C71015F3F7BE2, 0x842D43BF6369B1FF\n" ++
  "  .quad 0x20FDDADF107D20BC, 0x0000002F4B6DC970\n" ++
  -- p^12 - 2 — the Fermat denominator inverse (3044 bits, top bit 3043).
  "bnq_exp_p12m2_le:\n" ++
  "  .quad 0xC1D4E2D2CA86F11F, 0x41BF0E6B068AAFDB\n" ++
  "  .quad 0x23C5B159F8E334F7, 0xDB3F4157D4F4C1A6\n" ++
  "  .quad 0x5D1390D0AD44CDE3, 0xBDE30EC3AC19E53A\n" ++
  "  .quad 0xE967B77365ACBFB6, 0xDDDC3CD5778AB175\n" ++
  "  .quad 0x149DDA742C67F3EB, 0x00FFB72D2B1BD509\n" ++
  "  .quad 0x2092F07CAAE3590D, 0x5954B6865C929F15\n" ++
  "  .quad 0xBF03A7EAC45865CA, 0x6ACC85FF3050D845\n" ++
  "  .quad 0x04F734402C7E9C87, 0xFAFFDCD3E420AF5F\n" ++
  "  .quad 0x39B9E7C33466EBC5, 0x9A6BDF0BE72B9BB6\n" ++
  "  .quad 0xA4E3B43978298046, 0x27A80E4DBD46D78C\n" ++
  "  .quad 0xFBB3D91BE7B7FF49, 0xABADE6714D68AA10\n" ++
  "  .quad 0xB5914D60D8B15012, 0xDD600BA556C2761C\n" ++
  "  .quad 0xC93A85CCB6522FBA, 0x0B409DD086EAC626\n" ++
  "  .quad 0x382EE9C8E530232F, 0x1CE1C9500AA55B90\n" ++
  "  .quad 0xCC2713BF84C279D9, 0xEAA7A4A16D1A05DC\n" ++
  "  .quad 0x1A7AA25767C1CEC5, 0x219B8A10DDBE1123\n" ++
  "  .quad 0xA523759E261408AC, 0xE5FF67475F1F3ADD\n" ++
  "  .quad 0xC90EFB9439CBA604, 0x11CBB900DAD55C8D\n" ++
  "  .quad 0xB8EC71A82A5FA888, 0xD2CCF14141D6F9A0\n" ++
  "  .quad 0x4DACF90E8E139C69, 0x380FDB292B696A8D\n" ++
  "  .quad 0x1046AB2684B00EB6, 0x4DB41B22A5B9BA9F\n" ++
  "  .quad 0xC1E6C4BCFEAA38D3, 0x4BF43F7F5933D90D\n" ++
  "  .quad 0x7F447128E8041DA4, 0x2CC29793FA9C753A\n" ++
  "  .quad 0x5AB6DF1836F1770C, 0x00000008F0AC8ADC\n" ++
  -- p (the Frobenius coordinate-power exponent, 254 bits, top bit 253)
  -- and the group order n (the G2 subgroup-check scalar, 254 bits).
  "bnq_exp_p_le:\n" ++
  "  .quad 0x3C208C16D87CFD47, 0x97816A916871CA8D\n" ++
  "  .quad 0xB85045B68181585D, 0x30644E72E131A029\n" ++
  "bnq_order_le:\n" ++
  "  .quad 0x43E1F593F0000001, 0x2833E84879B97091\n" ++
  "  .quad 0xB85045B68181585D, 0x30644E72E131A029\n" ++
  -- Small scalar constants (LE Fp).
  "bnq_le_18:\n" ++
  "  .quad 18, 0, 0, 0\n" ++
  "bnq_le_pm82:\n" ++
  "  .quad 0x3C208C16D87CFCF5, 0x97816A916871CA8D\n" ++
  "  .quad 0xB85045B68181585D, 0x30644E72E131A029\n" ++
  "bnq_le_pm9:\n" ++
  "  .quad 0x3C208C16D87CFD3E, 0x97816A916871CA8D\n" ++
  "  .quad 0xB85045B68181585D, 0x30644E72E131A029\n" ++
  "bnq_le_2:\n  .quad 2, 0, 0, 0\n" ++
  "bnq_le_3:\n  .quad 3, 0, 0, 0\n" ++
  "bnq_le_4:\n  .quad 4, 0, 0, 0\n" ++
  "bnq_le_8:\n  .quad 8, 0, 0, 0\n" ++
  -- The twist curve constant b2 = 3/(9+u) in Fp2 (LE c0 || c1).
  "bnq_twist_b2_le:\n" ++
  "  .quad 0x3267E6DC24A138E5, 0xB5B4C5E559DBEFA3\n" ++
  "  .quad 0x81BE18991BE06AC3, 0x2B149D40CEB8AAAE\n" ++
  "  .quad 0xE4A2BD0685C315D2, 0xA74FA084E52D1852\n" ++
  "  .quad 0xCD2CAFADEED8FDF4, 0x009713B03AF0FED4\n" ++
  -- Schoolbook product accumulator (23 coefficients) and the pow
  -- square/multiply temporary.
  ".balign 8\n" ++
  "bnq_acc:\n  .zero 736\n" ++
  "bnq_powt:\n  .zero 384\n"

/-- FQ12 dst = a * b mod (w^12 - 18 w^6 + 82). a0 = dst, a1 = a, a2 = b.
    dst must NOT alias a or b (the product is composed in `bnq_acc` and
    copied out, but a/b are read interleaved with acc writes only —
    aliasing a/b with dst is fine; aliasing with bnq_acc is not, which
    static buffers never do). a may alias b (squaring). -/
def bn254Fq12MulFunction : String :=
  "bnq_mul:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  la t0, bnq_acc\n" ++
  "  li t1, 92\n" ++
  ".Lbnq_mul_zero:\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .Lbnq_mul_zero\n" ++
  "  li s3, 0                       # i\n" ++
  ".Lbnq_mul_i:\n" ++
  "  li s4, 0                       # j\n" ++
  ".Lbnq_mul_j:\n" ++
  "  slli t1, s3, 5\n" ++
  "  add t1, s1, t1                 # &a[i]\n" ++
  "  slli t2, s4, 5\n" ++
  "  add t2, s2, t2                 # &b[j]\n" ++
  "  add t3, s3, s4\n" ++
  "  slli t3, t3, 5\n" ++
  "  la t4, bnq_acc\n" ++
  "  add t3, t4, t3                 # &acc[i+j]\n" ++
  "  la t0, bnp_arith_params\n" ++
  "  sd t1, 0(t0)\n" ++
  "  sd t2, 8(t0)\n" ++
  "  sd t3, 16(t0)\n" ++
  "  la t1, bnf_le_p\n" ++
  "  sd t1, 24(t0)\n" ++
  "  sd t3, 32(t0)\n" ++
  "  .4byte 0x8022a073              # acc[i+j] = a[i]*b[j] + acc[i+j]\n" ++
  "  addi s4, s4, 1\n" ++
  "  li t0, 12\n" ++
  "  bne s4, t0, .Lbnq_mul_j\n" ++
  "  addi s3, s3, 1\n" ++
  "  li t0, 12\n" ++
  "  bne s3, t0, .Lbnq_mul_i\n" ++
  -- Cascading reduction by w^12 = 18 w^6 - 82, high coefficient first so
  -- the k-6 fold lands before that slot is itself reduced.
  "  li s3, 22                      # k\n" ++
  ".Lbnq_mul_red:\n" ++
  "  la t4, bnq_acc\n" ++
  "  slli t1, s3, 5\n" ++
  "  add t1, t4, t1                 # &acc[k]\n" ++
  "  addi t2, s3, -6\n" ++
  "  slli t2, t2, 5\n" ++
  "  add t2, t4, t2                 # &acc[k-6]\n" ++
  "  la t0, bnp_arith_params\n" ++
  "  sd t1, 0(t0)\n" ++
  "  la t3, bnq_le_18\n" ++
  "  sd t3, 8(t0)\n" ++
  "  sd t2, 16(t0)\n" ++
  "  la t3, bnf_le_p\n" ++
  "  sd t3, 24(t0)\n" ++
  "  sd t2, 32(t0)\n" ++
  "  .4byte 0x8022a073              # acc[k-6] += 18*acc[k]\n" ++
  "  addi t2, s3, -12\n" ++
  "  slli t2, t2, 5\n" ++
  "  add t2, t4, t2                 # &acc[k-12]\n" ++
  "  la t0, bnp_arith_params\n" ++
  "  sd t1, 0(t0)\n" ++
  "  la t3, bnq_le_pm82\n" ++
  "  sd t3, 8(t0)\n" ++
  "  sd t2, 16(t0)\n" ++
  "  la t3, bnf_le_p\n" ++
  "  sd t3, 24(t0)\n" ++
  "  sd t2, 32(t0)\n" ++
  "  .4byte 0x8022a073              # acc[k-12] += (p-82)*acc[k]\n" ++
  "  addi s3, s3, -1\n" ++
  "  li t0, 11\n" ++
  "  bne s3, t0, .Lbnq_mul_red\n" ++
  "  la t0, bnq_acc\n" ++
  "  mv t1, s0\n" ++
  "  li t2, 48\n" ++
  ".Lbnq_mul_copy:\n" ++
  "  ld t3, 0(t0)\n" ++
  "  sd t3, 0(t1)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lbnq_mul_copy\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- Coefficient-wise binary helper: a0 = dst, a1 = a, a2 = b, all FQ12.
    Emits a 12-iteration loop with the given Arith256Mod operand order
    `aSlot`/`bSlot`/`cSlot` (each "a"/"b"/"c"/<const label>). -/
private def bnq12LoopFunction (name aSlot bSlot cSlot : String) : String :=
  let slot (s : String) (reg : String) : String :=
    if s = "a" then "  sd t1, " ++ reg ++ "(t0)\n"
    else if s = "b" then "  sd t2, " ++ reg ++ "(t0)\n"
    else "  la t4, " ++ s ++ "\n  sd t4, " ++ reg ++ "(t0)\n"
  name ++ ":\n" ++
  "  li t5, 12\n" ++
  ".L" ++ name ++ "_loop:\n" ++
  "  mv t1, a1\n" ++
  "  mv t2, a2\n" ++
  "  la t0, bnp_arith_params\n" ++
  slot aSlot "0" ++
  slot bSlot "8" ++
  slot cSlot "16" ++
  "  la t4, bnf_le_p\n" ++
  "  sd t4, 24(t0)\n" ++
  "  sd a0, 32(t0)\n" ++
  "  .4byte 0x8022a073\n" ++
  "  addi a0, a0, 32\n" ++
  "  addi a1, a1, 32\n" ++
  "  addi a2, a2, 32\n" ++
  "  addi t5, t5, -1\n" ++
  "  bnez t5, .L" ++ name ++ "_loop\n" ++
  "  ret"

/-- FQ12 dst = a + b (coefficient-wise d = (a*1 + b)). Aliasing allowed. -/
def bn254Fq12AddFunction : String :=
  bnq12LoopFunction "bnq_add" "a" "bnf_le_one" "b"

/-- FQ12 dst = a - b (coefficient-wise d = (b*(p-1) + a)). Aliasing allowed. -/
def bn254Fq12SubFunction : String :=
  bnq12LoopFunction "bnq_sub" "b" "bnp_p_minus_1_le" "a"

/-- FQ12 dst = a * s for a 32-byte LE Fp scalar at a2 (coefficient-wise
    d = (a*s + 0)). Aliasing allowed. NOTE: a2 is the SCALAR pointer and
    is advanced past in lockstep but re-staged per iteration via t2 —
    so pass the scalar cell, not an FQ12. -/
def bnqSmul_prog : Program :=
  [ .LI .x30 (12 : Word),
    .AUIPC .x5 (laHi GuestAddrs.bnp_arith_params (GuestAddrs.bnq_smul + 4)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bnp_arith_params (GuestAddrs.bnq_smul + 4)),
    .SD .x5 .x11 (0 : BitVec 12),
    .SD .x5 .x12 (8 : BitVec 12),
    .AUIPC .x29 (laHi GuestAddrs.bnf_le_zero (GuestAddrs.bnq_smul + 20)),
    .ADDI .x29 .x29 (laLo GuestAddrs.bnf_le_zero (GuestAddrs.bnq_smul + 20)),
    .SD .x5 .x29 (16 : BitVec 12),
    .AUIPC .x29 (laHi GuestAddrs.bnf_le_p (GuestAddrs.bnq_smul + 32)),
    .ADDI .x29 .x29 (laLo GuestAddrs.bnf_le_p (GuestAddrs.bnq_smul + 32)),
    .SD .x5 .x29 (24 : BitVec 12),
    .SD .x5 .x10 (32 : BitVec 12),
    .CSRS (2050 : BitVec 12) .x5,
    .ADDI .x10 .x10 (32 : BitVec 12),
    .ADDI .x11 .x11 (32 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .BNE .x30 .x0 (-60 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bnqSmul_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bnqSmul_relocs : RelocTable :=
  [ (1, .la .x5 "bnp_arith_params"),
    (5, .la .x29 "bnf_le_zero"),
    (8, .la .x29 "bnf_le_p") ]

def bn254Fq12SMulFunction : String :=
  "bnq_smul:\n" ++ emitProgramR bnqSmul_prog bnqSmul_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bnqSmul_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bn254Fq12SMulFunction_eq_prog :
    bn254Fq12SMulFunction = "bnq_smul:\n" ++ emitProgramR bnqSmul_prog bnqSmul_relocs := rfl

#guard bn254Fq12SMulFunction.startsWith "bnq_smul:\n"
#guard bnqSmul_prog.length = 18
/-- Copy a 384-byte FQ12 value: a0 = src, a1 = dst. -/
def bnqCopy_prog : Program :=
  [ .LI .x7 (48 : Word),
    .LD .x28 .x10 (0 : BitVec 12),
    .SD .x11 .x28 (0 : BitVec 12),
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x11 .x11 (8 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-20 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bn254Fq12CopyFunction : String :=
  "bnq_copy:\n" ++ emitProgram bnqCopy_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bnqCopy_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254Fq12CopyFunction_eq_prog :
    bn254Fq12CopyFunction = "bnq_copy:\n" ++ emitProgram bnqCopy_prog := rfl

#guard bn254Fq12CopyFunction.startsWith "bnq_copy:\n"
#guard bnqCopy_prog.length = 8
/-- Zero a 384-byte FQ12 value at a0. -/
def bnqZero_prog : Program :=
  [ .LI .x7 (48 : Word),
    .SD .x10 .x0 (0 : BitVec 12),
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-12 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bn254Fq12ZeroFunction : String :=
  "bnq_zero:\n" ++ emitProgram bnqZero_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bnqZero_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254Fq12ZeroFunction_eq_prog :
    bn254Fq12ZeroFunction = "bnq_zero:\n" ++ emitProgram bnqZero_prog := rfl

#guard bn254Fq12ZeroFunction.startsWith "bnq_zero:\n"
#guard bnqZero_prog.length = 6
/-- Set the FQ12 at a0 to one (coefficient 0 = 1, rest 0). -/
def bnqSetOne_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .MV .x8 .x10,
    .JAL .x1 (jalOff GuestAddrs.bnq_zero (GuestAddrs.bnq_set_one + 16)),
    .LI .x5 (1 : Word),
    .SD .x8 .x5 (0 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bnqSetOne_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bnqSetOne_relocs : RelocTable :=
  [ (4, .jal .x1 "bnq_zero") ]

def bn254Fq12SetOneFunction : String :=
  "bnq_set_one:\n" ++ emitProgramR bnqSetOne_prog bnqSetOne_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bnqSetOne_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bn254Fq12SetOneFunction_eq_prog :
    bn254Fq12SetOneFunction = "bnq_set_one:\n" ++ emitProgramR bnqSetOne_prog bnqSetOne_relocs := rfl

#guard bn254Fq12SetOneFunction.startsWith "bnq_set_one:\n"
#guard bnqSetOne_prog.length = 11
/-- a0 = 1 iff the FQ12 values at a0/a1 are limb-identical (reduced). -/
def bnqEq_prog : Program :=
  [ .LI .x5 (48 : Word),
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

def bn254Fq12EqFunction : String :=
  "bnq_eq:\n" ++ emitProgram bnqEq_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bnqEq_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254Fq12EqFunction_eq_prog :
    bn254Fq12EqFunction = "bnq_eq:\n" ++ emitProgram bnqEq_prog := rfl

#guard bn254Fq12EqFunction.startsWith "bnq_eq:\n"
#guard bnqEq_prog.length = 13
/-- a0 = 1 iff the FQ12 value at a0 is zero. -/
def bnqIsZero_prog : Program :=
  [ .LI .x5 (48 : Word),
    .LI .x6 (0 : Word),
    .BEQ .x5 .x0 (24 : BitVec 13),
    .LD .x7 .x10 (0 : BitVec 12),
    .OR .x6 .x6 .x7,
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .SLTIU .x10 .x6 (1 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bn254Fq12IsZeroFunction : String :=
  "bnq_is_zero:\n" ++ emitProgram bnqIsZero_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bnqIsZero_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254Fq12IsZeroFunction_eq_prog :
    bn254Fq12IsZeroFunction = "bnq_is_zero:\n" ++ emitProgram bnqIsZero_prog := rfl

#guard bn254Fq12IsZeroFunction.startsWith "bnq_is_zero:\n"
#guard bnqIsZero_prog.length = 10
/-- FQ12 dst = base ^ exp, MSB-first square-and-multiply from bit a3
    down to 0. a0 = dst, a1 = base, a2 = exp (LE limbs), a3 = top bit
    index. dst must NOT alias base; clobbers `bnq_powt` and (via
    bnq_mul) `bnq_acc`. -/
def bnqPow_prog : Program :=
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
    .JAL .x1 (jalOff GuestAddrs.bnq_set_one (GuestAddrs.bnq_pow + 44)),
    .AUIPC .x10 (laHi GuestAddrs.bnq_powt (GuestAddrs.bnq_pow + 48)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bnq_powt (GuestAddrs.bnq_pow + 48)),
    .MV .x11 .x8,
    .MV .x12 .x8,
    .JAL .x1 (jalOff GuestAddrs.bnq_mul (GuestAddrs.bnq_pow + 64)),
    .AUIPC .x10 (laHi GuestAddrs.bnq_powt (GuestAddrs.bnq_pow + 68)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bnq_powt (GuestAddrs.bnq_pow + 68)),
    .MV .x11 .x8,
    .JAL .x1 (jalOff GuestAddrs.bnq_copy (GuestAddrs.bnq_pow + 80)),
    .SRLI .x5 .x19 (6 : BitVec 6),
    .SLLI .x5 .x5 (3 : BitVec 6),
    .ADD .x5 .x18 .x5,
    .LD .x6 .x5 (0 : BitVec 12),
    .ANDI .x7 .x19 (63 : BitVec 12),
    .SRL .x6 .x6 .x7,
    .ANDI .x6 .x6 (1 : BitVec 12),
    .BEQ .x6 .x0 (40 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.bnq_powt (GuestAddrs.bnq_pow + 116)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bnq_powt (GuestAddrs.bnq_pow + 116)),
    .MV .x11 .x8,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.bnq_mul (GuestAddrs.bnq_pow + 132)),
    .AUIPC .x10 (laHi GuestAddrs.bnq_powt (GuestAddrs.bnq_pow + 136)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bnq_powt (GuestAddrs.bnq_pow + 136)),
    .MV .x11 .x8,
    .JAL .x1 (jalOff GuestAddrs.bnq_copy (GuestAddrs.bnq_pow + 148)),
    .BEQ .x19 .x0 (12 : BitVec 13),
    .ADDI .x19 .x19 (-1 : BitVec 12),
    .JAL .x0 (-112 : BitVec 21),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bnqPow_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bnqPow_relocs : RelocTable :=
  [ (11, .jal .x1 "bnq_set_one"),
    (12, .la .x10 "bnq_powt"),
    (16, .jal .x1 "bnq_mul"),
    (17, .la .x10 "bnq_powt"),
    (20, .jal .x1 "bnq_copy"),
    (29, .la .x10 "bnq_powt"),
    (33, .jal .x1 "bnq_mul"),
    (34, .la .x10 "bnq_powt"),
    (37, .jal .x1 "bnq_copy") ]

def bn254Fq12PowFunction : String :=
  "bnq_pow:\n" ++ emitProgramR bnqPow_prog bnqPow_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bnqPow_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bn254Fq12PowFunction_eq_prog :
    bn254Fq12PowFunction = "bnq_pow:\n" ++ emitProgramR bnqPow_prog bnqPow_relocs := rfl

#guard bn254Fq12PowFunction.startsWith "bnq_pow:\n"
#guard bnqPow_prog.length = 48

/-- The FQ12 machine suite (requires `bn254FieldDataFragment` +
    `bn254Fp2DataFragment` + `bn254Fq12DataFragment`). Guest-linked: `bnq_add`
    unlinked (never-ref; mul ends `ret`); KEEP mul/sub/smul/copy/zero/set_one/
    eq/is_zero/pow. -/
def bn254Fq12CommonFunctions : String :=
  bn254Fq12MulFunction ++ "\n" ++
  bn254Fq12SubFunction ++ "\n" ++
  bn254Fq12SMulFunction ++ "\n" ++
  bn254Fq12CopyFunction ++ "\n" ++
  bn254Fq12ZeroFunction ++ "\n" ++
  bn254Fq12SetOneFunction ++ "\n" ++
  bn254Fq12EqFunction ++ "\n" ++
  bn254Fq12IsZeroFunction ++ "\n" ++
  bn254Fq12PowFunction

/-- Probe: input = a (384 B, 12 LE coeffs) || b (384 B) || mode (u64).
    mode 0/1: dst = a*b, output 256-byte window = coeffs 0..7 / 8..11.
    mode 2/3: dst = a^p (the Frobenius coordinate power), same split. -/
def ziskBn254Fq12OpsProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000008\n" ++
  "  ld s2, 768(s0)                 # mode\n" ++
  "  andi t0, s2, 2\n" ++
  "  bnez t0, .Lbnq_probe_pow\n" ++
  "  la a0, bnq_probe_res\n" ++
  "  mv a1, s0\n" ++
  "  addi a2, s0, 384\n" ++
  "  jal ra, bnq_mul\n" ++
  "  j .Lbnq_probe_out\n" ++
  ".Lbnq_probe_pow:\n" ++
  "  la a0, bnq_probe_res\n" ++
  "  mv a1, s0\n" ++
  "  la a2, bnq_exp_p_le\n" ++
  "  li a3, 253\n" ++
  "  jal ra, bnq_pow\n" ++
  ".Lbnq_probe_out:\n" ++
  "  la t0, bnq_probe_res\n" ++
  "  andi t1, s2, 1\n" ++
  "  beqz t1, .Lbnq_probe_lo\n" ++
  "  addi t0, t0, 256\n" ++
  ".Lbnq_probe_lo:\n" ++
  "  li t1, 0xa0010000\n" ++
  "  li t2, 32\n" ++
  ".Lbnq_probe_copy:\n" ++
  "  ld t3, 0(t0)\n" ++
  "  sd t3, 0(t1)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lbnq_probe_copy\n" ++
  "  j .Lbnq_probe_done\n" ++
  bn254Fp2CommonFunctions ++ "\n" ++
  bn254Fq12CommonFunctions ++ "\n" ++
  ".Lbnq_probe_done:"

def ziskBn254Fq12OpsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBn254Fq12OpsProbePrologue
  dataAsm     :=
    bn254Fp2DataSection ++
    bn254Fq12DataFragment ++
    ".balign 8\n" ++
    "bnq_probe_res:\n  .zero 384\n"
}

end EvmAsm.Codegen
