/-
  EvmAsm.Codegen.Programs.Bls12Kzg

  The EIP-4844 KZG point-evaluation (0x0a) kernel `zkvm_kzg_point_eval`,
  mirroring execution-specs `ethereum.crypto.kzg.verify_kzg_proof`:

    X_minus_z = [tau]_2 + ((n - z) mod n) * G2
    P_minus_y = C + ((n - y) mod n) * G1
    verified  = (e(P_minus_y, -G2) * e(proof, X_minus_z) == 1)

  built ON TOP of the proven BLS12-381 suites: `blsg_*` G1 helpers
  (Bls12G1), `blsg2_*` Fp/Fp2/G2 helpers (Bls12G2), and the EIP-2537
  `zkvm_bls12_pairing` kernel (Bls12Pairing) — the two computed pairs
  are encoded back into a 768-byte EIP-2537 wire buffer and verified by
  the existing pairing kernel (its decode/subgroup checks re-validate
  the constructed points; both inputs are subgroup members whenever the
  commitment/proof pass KeyValidate, so the redundant checks only cost
  steps, never change the verdict).

  New ground covered here (the wire format of 0x0a is NOT EIP-2537):

    * 48-byte COMPRESSED G1 decompression for the commitment and proof
      (py_ecc `decompress_G1` + `KeyValidate`): flag bits c/b/a at the
      top of byte 0, x < p, y = (x^3 + 4)^((p+1)/4) with the quadratic
      residue check (p = 3 mod 4), the a_flag sign select, the exact
      `0xc0 || 0^47` infinity encoding, and the REAL order-n subgroup
      check on finite points;
    * z/y canonicality (`bytes_to_bls_field` asserts value < n) and the
      (n - v) mod n scalar negation via one Arith384Mod call
      (d = v * (n-1) mod n);
    * the trusted-setup constant `KZG_SETUP_G2_MONOMIAL_1` (kzg.py),
      pre-decompressed via py_ecc `signature_to_G2` and baked as an
      LE-limb affine point (`blsk_tau2_le`), plus the constant -G2
      generator already in wire form for the first pair.

  Kernel ABI (dispatch entry `.L<tag>_kzg_point_eval` stages the
  192-byte payload and checks the versioned hash before the call):

    zkvm_kzg_point_eval(a0 = commitment (48 B compressed),
                        a1 = z (32 B BE), a2 = y (32 B BE),
                        a3 = proof (48 B compressed),
                        a4 = verified byte ptr)
      -> a0 = 0 ok (verified byte = 1 iff the proof checks out),
         a0 = 1 invalid encoding / non-canonical scalar
                (execution-specs KZGProofError -> precompile failure;
                 verified byte = 0 i.e. proof-false is ALSO
                 KZGProofError, decided by the caller).

  All labels are `blsk_`-prefixed. The generated constants come from
  py_ecc via execution-specs/.venv (see scripts/codegen-zisk-bls12-
  kzg-check.sh) — regenerate rather than hand-edit.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.Bls12Pairing

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- KZG data labels WITHOUT a `.section .data` header (appended after
    the field/G1/G2/pairing fragments). -/
def bls12KzgDataFragment : String :=
  ".balign 8\n" ++
  -- (p+1)/4 as 48-byte BE: the sqrt exponent for p = 3 mod 4
  "blsk_qp1d4_be:\n" ++
  "  .byte 0x06,0x80,0x44,0x7a,0x8e,0x5f,0xf9,0xa6\n" ++
  "  .byte 0x92,0xc6,0xe9,0xed,0x90,0xd2,0xeb,0x35\n" ++
  "  .byte 0xd9,0x1d,0xd2,0xe1,0x3c,0xe1,0x44,0xaf\n" ++
  "  .byte 0xd9,0xcc,0x34,0xa8,0x3d,0xac,0x3d,0x89\n" ++
  "  .byte 0x07,0xaa,0xff,0xff,0xac,0x54,0xff,0xff\n" ++
  "  .byte 0xee,0x7f,0xbf,0xff,0xff,0xff,0xea,0xab\n" ++
  -- (p+1)/2 as 48-byte BE: y >= (p+1)/2 iff (2y)//p = 1 (the a_flag)
  "blsk_phalf_be:\n" ++
  "  .byte 0x0d,0x00,0x88,0xf5,0x1c,0xbf,0xf3,0x4d\n" ++
  "  .byte 0x25,0x8d,0xd3,0xdb,0x21,0xa5,0xd6,0x6b\n" ++
  "  .byte 0xb2,0x3b,0xa5,0xc2,0x79,0xc2,0x89,0x5f\n" ++
  "  .byte 0xb3,0x98,0x69,0x50,0x7b,0x58,0x7b,0x12\n" ++
  "  .byte 0x0f,0x55,0xff,0xff,0x58,0xa9,0xff,0xff\n" ++
  "  .byte 0xdc,0xff,0x7f,0xff,0xff,0xff,0xd5,0x56\n" ++
  -- group order n (= BLS_MODULUS) and n-1 as LE limbs for the
  -- Arith384Mod scalar negation d = (v * (n-1) + 0) mod n
  ".balign 8\n" ++
  "blsk_n_le:\n" ++
  "  .quad 0xffffffff00000001, 0x53bda402fffe5bfe, 0x3339d80809a1d805\n" ++
  "  .quad 0x73eda753299d7d48, 0x0000000000000000, 0x0000000000000000\n" ++
  "blsk_nm1_le:\n" ++
  "  .quad 0xffffffff00000000, 0x53bda402fffe5bfe, 0x3339d80809a1d805\n" ++
  "  .quad 0x73eda753299d7d48, 0x0000000000000000, 0x0000000000000000\n" ++
  -- G1 generator as a compact 96-byte BE point (blsg_scalar_mul base)
  "blsk_g1gen_be:\n" ++
  "  .byte 0x17,0xf1,0xd3,0xa7,0x31,0x97,0xd7,0x94\n" ++
  "  .byte 0x26,0x95,0x63,0x8c,0x4f,0xa9,0xac,0x0f\n" ++
  "  .byte 0xc3,0x68,0x8c,0x4f,0x97,0x74,0xb9,0x05\n" ++
  "  .byte 0xa1,0x4e,0x3a,0x3f,0x17,0x1b,0xac,0x58\n" ++
  "  .byte 0x6c,0x55,0xe8,0x3f,0xf9,0x7a,0x1a,0xef\n" ++
  "  .byte 0xfb,0x3a,0xf0,0x0a,0xdb,0x22,0xc6,0xbb\n" ++
  "  .byte 0x08,0xb3,0xf4,0x81,0xe3,0xaa,0xa0,0xf1\n" ++
  "  .byte 0xa0,0x9e,0x30,0xed,0x74,0x1d,0x8a,0xe4\n" ++
  "  .byte 0xfc,0xf5,0xe0,0x95,0xd5,0xd0,0x0a,0xf6\n" ++
  "  .byte 0x00,0xdb,0x18,0xcb,0x2c,0x04,0xb3,0xed\n" ++
  "  .byte 0xd0,0x3c,0xc7,0x44,0xa2,0x88,0x8a,0xe4\n" ++
  "  .byte 0x0c,0xaa,0x23,0x29,0x46,0xc5,0xe7,0xe1\n" ++
  -- G2 generator as a 192-byte LE affine point (x.c0,x.c1,y.c0,y.c1)
  ".balign 8\n" ++
  "blsk_g2gen_le:\n" ++
  "  .quad 0xd48056c8c121bdb8, 0x0bac0326a805bbef, 0xb4510b647ae3d177\n" ++
  "  .quad 0xc6e47ad4fa403b02, 0x260805272dc51051, 0x024aa2b2f08f0a91\n" ++
  "  .quad 0xe5ac7d055d042b7e, 0x334cf11213945d57, 0xb5da61bbdc7f5049\n" ++
  "  .quad 0x596bd0d09920b61a, 0x7dacd3a088274f65, 0x13e02b6052719f60\n" ++
  "  .quad 0xe193548608b82801, 0x923ac9cc3baca289, 0x6d429a695160d12c\n" ++
  "  .quad 0xadfd9baa8cbdd3a7, 0x8cc9cdc6da2e351a, 0x0ce5d527727d6e11\n" ++
  "  .quad 0xaaa9075ff05f79be, 0x3f370d275cec1da1, 0x267492ab572e99ab\n" ++
  "  .quad 0xcb3e287e85a763af, 0x32acd2b02bc28b99, 0x0606c4a02ea734cc\n" ++
  -- KZG_SETUP_G2_MONOMIAL_1 ([tau]_2, kzg.py:62) pre-decompressed via
  -- py_ecc signature_to_G2, as a 192-byte LE affine point
  "blsk_tau2_le:\n" ++
  "  .quad 0xc98edada20c1def2, 0x087041de621000ed, 0xa36851477ba4c60b\n" ++
  "  .quad 0x3926c911cceceac9, 0x734429b7b38608e2, 0x185cbfee53492714\n" ++
  "  .quad 0xafaaab24f3499f72, 0x2914e5870cb452d2, 0x1009a2ce615ac53d\n" ++
  "  .quad 0x26187075cbfbefa8, 0x843bc287230af389, 0x15bfd7dd8cdeb128\n" ++
  "  .quad 0xee689bfbbb832a99, 0x4ce26d105941f383, 0xe82451a496a9c979\n" ++
  "  .quad 0x131569490e28de18, 0xd7d5ee8599d1fca2, 0x014353bdb96b626d\n" ++
  "  .quad 0x23048ef30d0a154f, 0x9495346f3d7ac9cd, 0xda5ed1ba9bfa0789\n" ++
  "  .quad 0xef79de09fc63671f, 0x03432fcae0181b4b, 0x1666c54b0a325295\n" ++
  -- -G2 generator as a constant 256-byte EIP-2537 wire record (the
  -- first pair's G2 side, py_ecc neg(G2))
  "blsk_negg2_wire:\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x02,0x4a,0xa2,0xb2,0xf0,0x8f,0x0a,0x91\n" ++
  "  .byte 0x26,0x08,0x05,0x27,0x2d,0xc5,0x10,0x51\n" ++
  "  .byte 0xc6,0xe4,0x7a,0xd4,0xfa,0x40,0x3b,0x02\n" ++
  "  .byte 0xb4,0x51,0x0b,0x64,0x7a,0xe3,0xd1,0x77\n" ++
  "  .byte 0x0b,0xac,0x03,0x26,0xa8,0x05,0xbb,0xef\n" ++
  "  .byte 0xd4,0x80,0x56,0xc8,0xc1,0x21,0xbd,0xb8\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x13,0xe0,0x2b,0x60,0x52,0x71,0x9f,0x60\n" ++
  "  .byte 0x7d,0xac,0xd3,0xa0,0x88,0x27,0x4f,0x65\n" ++
  "  .byte 0x59,0x6b,0xd0,0xd0,0x99,0x20,0xb6,0x1a\n" ++
  "  .byte 0xb5,0xda,0x61,0xbb,0xdc,0x7f,0x50,0x49\n" ++
  "  .byte 0x33,0x4c,0xf1,0x12,0x13,0x94,0x5d,0x57\n" ++
  "  .byte 0xe5,0xac,0x7d,0x05,0x5d,0x04,0x2b,0x7e\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x0d,0x1b,0x3c,0xc2,0xc7,0x02,0x78,0x88\n" ++
  "  .byte 0xbe,0x51,0xd9,0xef,0x69,0x1d,0x77,0xbc\n" ++
  "  .byte 0xb6,0x79,0xaf,0xda,0x66,0xc7,0x3f,0x17\n" ++
  "  .byte 0xf9,0xee,0x38,0x37,0xa5,0x50,0x24,0xf7\n" ++
  "  .byte 0x8c,0x71,0x36,0x32,0x75,0xa7,0x5d,0x75\n" ++
  "  .byte 0xd8,0x6b,0xab,0x79,0xf7,0x47,0x82,0xaa\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x13,0xfa,0x4d,0x4a,0x0a,0xd8,0xb1,0xce\n" ++
  "  .byte 0x18,0x6e,0xd5,0x06,0x17,0x89,0x21,0x3d\n" ++
  "  .byte 0x99,0x39,0x23,0x06,0x6d,0xdd,0xaf,0x10\n" ++
  "  .byte 0x40,0xbc,0x3f,0xf5,0x9f,0x82,0x5c,0x78\n" ++
  "  .byte 0xdf,0x74,0xf2,0xd7,0x54,0x67,0xe2,0x5e\n" ++
  "  .byte 0x0f,0x55,0xf8,0xa0,0x0f,0xa0,0x30,0xed\n" ++
  -- Arith384Mod parameter block for the scalar negation (in-place d=a
  -- is accelerator-safe, same as the dst-aliasing Fp helpers)
  "blsk_negn_params:\n" ++
  "  .quad blsk_scal_le, blsk_nm1_le, blsf_le_zero, blsk_n_le, blsk_scal_le\n" ++
  -- Fp scratch (48 B LE each) for the decompression sqrt
  ".balign 8\n" ++
  "blsk_x_le:\n  .zero 48\n" ++
  "blsk_rhs_le:\n  .zero 48\n" ++
  "blsk_y_le:\n  .zero 48\n" ++
  "blsk_t_le:\n  .zero 48\n" ++
  "blsk_powacc:\n  .zero 48\n" ++
  -- scalar staging: 48-byte BE (16-byte zero pad + 32-byte value) + LE
  "blsk_scal_be:\n  .zero 48\n" ++
  "blsk_scal_le:\n  .zero 48\n" ++
  -- decoded/computed points
  "blsk_c:\n  .zero 96\n" ++        -- commitment (compact BE)
  "blsk_pr:\n  .zero 96\n" ++       -- proof (compact BE)
  "blsk_t1g1:\n  .zero 96\n" ++     -- ((n-y) mod n) * G1
  "blsk_sum_g1:\n  .zero 96\n" ++   -- P_minus_y
  "blsk_sg2:\n  .zero 192\n" ++     -- ((n-z) mod n) * G2 (LE)
  "blsk_xz_g2:\n  .zero 192\n" ++   -- X_minus_z (LE)
  -- the two EIP-2537 wire pairs handed to zkvm_bls12_pairing
  "blsk_pair_in:\n  .zero 768\n"

/-- Fp d = a^((p+1)/4) mod p on LE cells: a0 = a (reduced), a1 = d
    (must not alias `blsk_powacc`). MSB-first square-and-multiply over
    `blsk_qp1d4_be`, one Arith384Mod per step (the `blsg2_fp_inv`
    recipe with the sqrt exponent). -/
def blskFpPowQ14_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .AUIPC .x10 (laHi GuestAddrs.blsf_le_one (GuestAddrs.blsk_fp_pow_q14 + 36)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_le_one (GuestAddrs.blsk_fp_pow_q14 + 36)),
    .AUIPC .x11 (laHi GuestAddrs.blsk_powacc (GuestAddrs.blsk_fp_pow_q14 + 44)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsk_powacc (GuestAddrs.blsk_fp_pow_q14 + 44)),
    .LI .x12 (6 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsk_fp_pow_q14 + 56)),
    .LI .x18 (0 : Word),
    .LI .x5 (48 : Word),
    .BGEU .x18 .x5 (104 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.blsk_qp1d4_be (GuestAddrs.blsk_fp_pow_q14 + 72)),
    .ADDI .x5 .x5 (laLo GuestAddrs.blsk_qp1d4_be (GuestAddrs.blsk_fp_pow_q14 + 72)),
    .ADD .x5 .x5 .x18,
    .LBU .x19 .x5 (0 : BitVec 12),
    .LI .x20 (128 : Word),
    .BEQ .x20 .x0 (72 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.blsk_powacc (GuestAddrs.blsk_fp_pow_q14 + 96)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsk_powacc (GuestAddrs.blsk_fp_pow_q14 + 96)),
    .AUIPC .x11 (laHi GuestAddrs.blsk_powacc (GuestAddrs.blsk_fp_pow_q14 + 104)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsk_powacc (GuestAddrs.blsk_fp_pow_q14 + 104)),
    .AUIPC .x12 (laHi GuestAddrs.blsk_powacc (GuestAddrs.blsk_fp_pow_q14 + 112)),
    .ADDI .x12 .x12 (laLo GuestAddrs.blsk_powacc (GuestAddrs.blsk_fp_pow_q14 + 112)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp_mul (GuestAddrs.blsk_fp_pow_q14 + 120)),
    .AND .x5 .x19 .x20,
    .BEQ .x5 .x0 (28 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.blsk_powacc (GuestAddrs.blsk_fp_pow_q14 + 132)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsk_powacc (GuestAddrs.blsk_fp_pow_q14 + 132)),
    .MV .x11 .x8,
    .AUIPC .x12 (laHi GuestAddrs.blsk_powacc (GuestAddrs.blsk_fp_pow_q14 + 144)),
    .ADDI .x12 .x12 (laLo GuestAddrs.blsk_powacc (GuestAddrs.blsk_fp_pow_q14 + 144)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp_mul (GuestAddrs.blsk_fp_pow_q14 + 152)),
    .SRLI .x20 .x20 (1 : BitVec 6),
    .JAL .x0 (-68 : BitVec 21),
    .ADDI .x18 .x18 (1 : BitVec 12),
    .JAL .x0 (-104 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.blsk_powacc (GuestAddrs.blsk_fp_pow_q14 + 172)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsk_powacc (GuestAddrs.blsk_fp_pow_q14 + 172)),
    .MV .x11 .x9,
    .LI .x12 (6 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsk_fp_pow_q14 + 188)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blskFpPowQ14_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blskFpPowQ14_relocs : RelocTable :=
  [ (9, .la .x10 "blsf_le_one"),
    (11, .la .x11 "blsk_powacc"),
    (14, .jal .x1 "blsf_copy_quads"),
    (18, .la .x5 "blsk_qp1d4_be"),
    (24, .la .x10 "blsk_powacc"),
    (26, .la .x11 "blsk_powacc"),
    (28, .la .x12 "blsk_powacc"),
    (30, .jal .x1 "blsg2_fp_mul"),
    (33, .la .x10 "blsk_powacc"),
    (36, .la .x12 "blsk_powacc"),
    (38, .jal .x1 "blsg2_fp_mul"),
    (43, .la .x10 "blsk_powacc"),
    (47, .jal .x1 "blsf_copy_quads") ]

def bls12KzgFpPowQ14Function : String :=
  "blsk_fp_pow_q14:\n" ++ emitProgramR blskFpPowQ14_prog blskFpPowQ14_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blskFpPowQ14_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12KzgFpPowQ14Function_eq_prog :
    bls12KzgFpPowQ14Function = "blsk_fp_pow_q14:\n" ++ emitProgramR blskFpPowQ14_prog blskFpPowQ14_relocs := rfl

#guard bls12KzgFpPowQ14Function.startsWith "blsk_fp_pow_q14:\n"
#guard blskFpPowQ14_prog.length = 56
/-- a0 = 1 iff the a2-byte big-endian integer at a0 is strictly less
    than the one at a1. Leaf (generic sibling of `blsg_lt_p`). -/
def blskLtBe_prog : Program :=
  [ .MV .x5 .x10,
    .MV .x6 .x11,
    .MV .x7 .x12,
    .BEQ .x7 .x0 (44 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .LBU .x29 .x6 (0 : BitVec 12),
    .BLTU .x28 .x29 (24 : BitVec 13),
    .BLTU .x29 .x28 (28 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bls12KzgLtBeFunction : String :=
  "blsk_lt_be:\n" ++ emitProgram blskLtBe_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blskLtBe_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bls12KzgLtBeFunction_eq_prog :
    bls12KzgLtBeFunction = "blsk_lt_be:\n" ++ emitProgram blskLtBe_prog := rfl

#guard bls12KzgLtBeFunction.startsWith "blsk_lt_be:\n"
#guard blskLtBe_prog.length = 16
/-- Decompress one 48-byte compressed G1 point (py_ecc `decompress_G1`
    + the `validate_kzg_g1` infinity rule): a0 = input bytes (any
    alignment), a1 = compact 96-byte BE output. Returns a0 = 0 (valid
    finite), 1 (the exact `0xc0 || 0^47` infinity, output zeroed), or
    2 (invalid: c_flag 0, non-canonical infinity, x >= p, or x^3 + 4
    not a square). The caller does the order-n subgroup check. -/
def bls12KzgDecompressG1Function : String :=
  "blsk_decompress_g1:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  lbu s2, 0(s0)                  # flag byte: c/b/a at bits 7/6/5\n" ++
  "  andi t0, s2, 0x80\n" ++
  "  beqz t0, .Lblsk_dec_bad        # c_flag must be 1\n" ++
  "  andi t0, s2, 0x40\n" ++
  "  beqz t0, .Lblsk_dec_finite\n" ++
  "  li t0, 0xc0\n" ++
  "  bne s2, t0, .Lblsk_dec_bad     # infinity needs a_flag = 0\n" ++
  "  addi a0, s0, 1\n" ++
  "  li a1, 47\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  beqz a0, .Lblsk_dec_bad        # infinity needs a zero payload\n" ++
  "  mv a0, s1\n" ++
  "  jal ra, blsg_zero96            # compact infinity = (0,0)\n" ++
  "  li a0, 1\n" ++
  "  j .Lblsk_dec_ret\n" ++
  ".Lblsk_dec_finite:\n" ++
  -- x = input with the 3 flag bits masked off, staged into out[0..48)
  "  mv t1, s0\n" ++
  "  mv t2, s1\n" ++
  "  li t0, 48\n" ++
  ".Lblsk_dec_copyx:\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  sb t3, 0(t2)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t0, t0, -1\n" ++
  "  bnez t0, .Lblsk_dec_copyx\n" ++
  "  lbu t3, 0(s1)\n" ++
  "  andi t3, t3, 0x1f\n" ++
  "  sb t3, 0(s1)\n" ++
  "  mv a0, s1\n" ++
  "  jal ra, blsg_lt_p\n" ++
  "  beqz a0, .Lblsk_dec_bad        # x >= p\n" ++
  "  mv a0, s1\n" ++
  "  la a1, blsk_x_le\n" ++
  "  jal ra, blsg_be_to_le\n" ++
  -- rhs = x^3 + 4 (blsg2_b_le's first 48 LE bytes are the constant 4)
  "  la a0, blsk_x_le\n" ++
  "  la a1, blsk_x_le\n" ++
  "  la a2, blsk_rhs_le\n" ++
  "  jal ra, blsg2_fp_mul           # x^2\n" ++
  "  la a0, blsk_rhs_le\n" ++
  "  la a1, blsk_x_le\n" ++
  "  la a2, blsk_rhs_le\n" ++
  "  jal ra, blsg2_fp_mul           # x^3\n" ++
  "  la a0, blsk_rhs_le\n" ++
  "  la a1, blsg2_b_le\n" ++
  "  la a2, blsk_rhs_le\n" ++
  "  jal ra, blsg2_fp_add           # x^3 + 4\n" ++
  -- y = rhs^((p+1)/4); on-curve iff y^2 = rhs (p = 3 mod 4)
  "  la a0, blsk_rhs_le\n" ++
  "  la a1, blsk_y_le\n" ++
  "  jal ra, blsk_fp_pow_q14\n" ++
  "  la a0, blsk_y_le\n" ++
  "  la a1, blsk_y_le\n" ++
  "  la a2, blsk_t_le\n" ++
  "  jal ra, blsg2_fp_mul\n" ++
  "  la a0, blsk_t_le\n" ++
  "  la a1, blsk_rhs_le\n" ++
  "  li a2, 48\n" ++
  "  jal ra, blsg2_eq_n\n" ++
  "  beqz a0, .Lblsk_dec_bad        # x^3 + 4 is not a square\n" ++
  -- sign select: flip y unless (y >= (p+1)/2) == a_flag
  "  la a0, blsk_y_le\n" ++
  "  addi a1, s1, 48\n" ++
  "  jal ra, blsg_le_to_be\n" ++
  "  addi a0, s1, 48\n" ++
  "  la a1, blsk_phalf_be\n" ++
  "  li a2, 48\n" ++
  "  jal ra, blsk_lt_be             # 1 iff y < (p+1)/2\n" ++
  "  xori t0, a0, 1                 # t0 = (2y)//p\n" ++
  "  srli t1, s2, 5\n" ++
  "  andi t1, t1, 1                 # t1 = a_flag\n" ++
  "  beq t0, t1, .Lblsk_dec_signok\n" ++
  "  la a0, blsk_y_le\n" ++
  "  la a1, blsg2_pm1_le\n" ++
  "  la a2, blsk_y_le\n" ++
  "  jal ra, blsg2_fp_mul           # y = p - y\n" ++
  "  la a0, blsk_y_le\n" ++
  "  addi a1, s1, 48\n" ++
  "  jal ra, blsg_le_to_be\n" ++
  ".Lblsk_dec_signok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lblsk_dec_ret\n" ++
  ".Lblsk_dec_bad:\n" ++
  "  li a0, 2\n" ++
  ".Lblsk_dec_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- Canonicality gate + scalar negation: a0 = 32-byte BE field element
    v. Returns a0 = 0 with `blsk_scal_be` = (n - v) mod n as a 48-byte
    BE value (16-byte zero pad), or a0 = 1 when v >= n
    (`bytes_to_bls_field` assertion failure). -/
def bls12KzgNegScalarFunction : String :=
  "blsk_neg_scalar:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp)\n" ++
  "  mv s0, a0\n" ++
  "  la a1, blsg_n_be\n" ++
  "  li a2, 32\n" ++
  "  jal ra, blsk_lt_be\n" ++
  "  beqz a0, .Lblsk_negs_bad       # v >= BLS_MODULUS\n" ++
  "  la t1, blsk_scal_be\n" ++
  "  li t0, 16\n" ++
  ".Lblsk_negs_pad:\n" ++
  "  sb zero, 0(t1)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t0, t0, -1\n" ++
  "  bnez t0, .Lblsk_negs_pad\n" ++
  "  mv t2, s0\n" ++
  "  li t0, 32\n" ++
  ".Lblsk_negs_copy:\n" ++
  "  lbu t3, 0(t2)\n" ++
  "  sb t3, 0(t1)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t0, t0, -1\n" ++
  "  bnez t0, .Lblsk_negs_copy\n" ++
  "  la a0, blsk_scal_be\n" ++
  "  la a1, blsk_scal_le\n" ++
  "  jal ra, blsg_be_to_le\n" ++
  "  la a0, blsk_negn_params\n" ++
  "  .4byte 0x80b52073              # d = (v*(n-1) + 0) mod n = (n-v) mod n\n" ++
  "  la a0, blsk_scal_le\n" ++
  "  la a1, blsk_scal_be\n" ++
  "  jal ra, blsg_le_to_be\n" ++
  "  li a0, 0\n" ++
  "  j .Lblsk_negs_ret\n" ++
  ".Lblsk_negs_bad:\n" ++
  "  li a0, 1\n" ++
  ".Lblsk_negs_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- Encode a compact 96-byte BE G1 point (a0) as a 128-byte EIP-2537
    wire record at a1 (zero pads written; (0,0) stays all-zero). Leaf;
    byte ops, so alignment is free. -/
def blskG1Wire_prog : Program :=
  [ .LI .x5 (0 : Word),
    .SLLI .x6 .x5 (6 : BitVec 6),
    .ADD .x6 .x11 .x6,
    .LI .x7 (16 : Word),
    .SB .x6 .x0 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-12 : BitVec 13),
    .SLLI .x7 .x5 (4 : BitVec 6),
    .SLLI .x28 .x5 (5 : BitVec 6),
    .ADD .x7 .x7 .x28,
    .ADD .x7 .x10 .x7,
    .LI .x28 (48 : Word),
    .LBU .x29 .x7 (0 : BitVec 12),
    .SB .x6 .x29 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .BNE .x28 .x0 (-20 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .LI .x6 (2 : Word),
    .BNE .x5 .x6 (-80 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bls12KzgG1WireFunction : String :=
  "blsk_g1_wire:\n" ++ emitProgram blskG1Wire_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blskG1Wire_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bls12KzgG1WireFunction_eq_prog :
    bls12KzgG1WireFunction = "blsk_g1_wire:\n" ++ emitProgram blskG1Wire_prog := rfl

#guard bls12KzgG1WireFunction.startsWith "blsk_g1_wire:\n"
#guard blskG1Wire_prog.length = 23
/-- Encode a 192-byte LE G2 point (a0) as a 256-byte EIP-2537 wire
    record at a1 (zero pads written; all-zero stays all-zero). -/
def blskG2Wire_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .LI .x18 (0 : Word),
    .SLLI .x5 .x18 (6 : BitVec 6),
    .ADD .x6 .x9 .x5,
    .LI .x7 (16 : Word),
    .SB .x6 .x0 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-12 : BitVec 13),
    .SLLI .x5 .x18 (4 : BitVec 6),
    .SLLI .x7 .x18 (5 : BitVec 6),
    .ADD .x5 .x5 .x7,
    .ADD .x10 .x8 .x5,
    .SLLI .x5 .x18 (6 : BitVec 6),
    .ADD .x11 .x9 .x5,
    .ADDI .x11 .x11 (16 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.blsg_le_to_be (GuestAddrs.blsk_g2_wire + 88)),
    .ADDI .x18 .x18 (1 : BitVec 12),
    .LI .x5 (4 : Word),
    .BNE .x18 .x5 (-68 : BitVec 13),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blskG2Wire_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blskG2Wire_relocs : RelocTable :=
  [ (22, .jal .x1 "blsg_le_to_be") ]

def bls12KzgG2WireFunction : String :=
  "blsk_g2_wire:\n" ++ emitProgramR blskG2Wire_prog blskG2Wire_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blskG2Wire_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12KzgG2WireFunction_eq_prog :
    bls12KzgG2WireFunction = "blsk_g2_wire:\n" ++ emitProgramR blskG2Wire_prog blskG2Wire_relocs := rfl

#guard bls12KzgG2WireFunction.startsWith "blsk_g2_wire:\n"
#guard blskG2Wire_prog.length = 32
/-- Real KZG point-evaluation kernel (see the module docstring for the
    ABI and the verify_kzg_proof equation). -/
def zkvmKzgPointEvalRealFunction : String :=
  ".globl zkvm_kzg_point_eval\n" ++
  "zkvm_kzg_point_eval:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                      # commitment (48 B compressed)\n" ++
  "  mv s1, a1                      # z (32 B BE)\n" ++
  "  mv s2, a2                      # y (32 B BE)\n" ++
  "  mv s3, a3                      # proof (48 B compressed)\n" ++
  "  mv s4, a4                      # verified byte ptr\n" ++
  -- commitment: decompress + KeyValidate subgroup check on finite points
  "  mv a0, s0\n" ++
  "  la a1, blsk_c\n" ++
  "  jal ra, blsk_decompress_g1\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lblsk_kzg_invalid\n" ++
  "  bnez a0, .Lblsk_kzg_c_ok       # exact infinity: validate_kzg_g1 accepts\n" ++
  "  la a0, blsk_c\n" ++
  "  jal ra, blsg_subgroup_g1\n" ++
  "  beqz a0, .Lblsk_kzg_invalid\n" ++
  ".Lblsk_kzg_c_ok:\n" ++
  "  mv a0, s3\n" ++
  "  la a1, blsk_pr\n" ++
  "  jal ra, blsk_decompress_g1\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lblsk_kzg_invalid\n" ++
  "  bnez a0, .Lblsk_kzg_pr_ok\n" ++
  "  la a0, blsk_pr\n" ++
  "  jal ra, blsg_subgroup_g1\n" ++
  "  beqz a0, .Lblsk_kzg_invalid\n" ++
  ".Lblsk_kzg_pr_ok:\n" ++
  -- X_minus_z = [tau]_2 + ((n - z) mod n) * G2
  "  mv a0, s1\n" ++
  "  jal ra, blsk_neg_scalar\n" ++
  "  bnez a0, .Lblsk_kzg_invalid    # z >= BLS_MODULUS\n" ++
  "  la a0, blsk_scal_be\n" ++
  "  addi a0, a0, 16\n" ++
  "  li a1, 32\n" ++
  "  la a2, blsk_g2gen_le\n" ++
  "  la a3, blsk_sg2\n" ++
  "  jal ra, blsg2_scalar_mul\n" ++
  "  la a0, blsk_tau2_le\n" ++
  "  la a1, blsk_sg2\n" ++
  "  la a2, blsk_xz_g2\n" ++
  "  jal ra, blsg2_point_add\n" ++
  -- P_minus_y = C + ((n - y) mod n) * G1
  "  mv a0, s2\n" ++
  "  jal ra, blsk_neg_scalar\n" ++
  "  bnez a0, .Lblsk_kzg_invalid    # y >= BLS_MODULUS\n" ++
  "  la a0, blsk_scal_be\n" ++
  "  addi a0, a0, 16\n" ++
  "  li a1, 32\n" ++
  "  la a2, blsk_g1gen_be\n" ++
  "  la a3, blsk_t1g1\n" ++
  "  jal ra, blsg_scalar_mul\n" ++
  "  la a0, blsk_c\n" ++
  "  la a1, blsk_t1g1\n" ++
  "  la a2, blsk_sum_g1\n" ++
  "  jal ra, blsg_point_add\n" ++
  -- wire pairs (P_minus_y, -G2) and (proof, X_minus_z); every byte of
  -- the 768-byte buffer is written, so no zero pass is needed
  "  la a0, blsk_sum_g1\n" ++
  "  la a1, blsk_pair_in\n" ++
  "  jal ra, blsk_g1_wire\n" ++
  "  la a0, blsk_negg2_wire\n" ++
  "  la a1, blsk_pair_in\n" ++
  "  addi a1, a1, 128\n" ++
  "  li a2, 32\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  la a0, blsk_pr\n" ++
  "  la a1, blsk_pair_in\n" ++
  "  addi a1, a1, 384\n" ++
  "  jal ra, blsk_g1_wire\n" ++
  "  la a0, blsk_xz_g2\n" ++
  "  la a1, blsk_pair_in\n" ++
  "  addi a1, a1, 512\n" ++
  "  jal ra, blsk_g2_wire\n" ++
  "  la a0, blsk_pair_in\n" ++
  "  li a1, 2\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, zkvm_bls12_pairing\n" ++
  "  bnez a0, .Lblsk_kzg_invalid    # unreachable on the constructed input\n" ++
  "  li a0, 0\n" ++
  "  j .Lblsk_kzg_ret\n" ++
  ".Lblsk_kzg_invalid:\n" ++
  "  li a0, 1\n" ++
  ".Lblsk_kzg_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- The KZG kernel suite, ON TOP of the blsg_/blsg2_ suites and the
    pairing kernel (Bls12G1/Bls12G2/Bls12Pairing), which dispatcher
    closures already link. -/
def bls12KzgKernelFunctions : String :=
  bls12KzgFpPowQ14Function ++ "\n" ++
  bls12KzgLtBeFunction ++ "\n" ++
  bls12KzgDecompressG1Function ++ "\n" ++
  bls12KzgNegScalarFunction ++ "\n" ++
  bls12KzgG1WireFunction ++ "\n" ++
  bls12KzgG2WireFunction ++ "\n" ++
  zkvmKzgPointEvalRealFunction

/-- Probe: input at `0x40000008` = z(32) || y(32) || commitment(48) ||
    proof(48), 160 bytes. Output: status u64 at OUTPUT+0, verified byte
    at OUTPUT+8. -/
def ziskBls12KzgPointEvalRealProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000008\n" ++
  "  addi a0, s0, 64\n" ++
  "  mv a1, s0\n" ++
  "  addi a2, s0, 32\n" ++
  "  addi a3, s0, 112\n" ++
  "  li a4, 0xa0010008\n" ++
  "  jal ra, zkvm_kzg_point_eval\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lblsk_kzg_probe_done\n" ++
  bls12G1PrecompileFunctions ++ "\n" ++
  bls12G2PrecompileFunctions ++ "\n" ++
  bls12PairingKernelFunctions ++ "\n" ++
  bls12KzgKernelFunctions ++ "\n" ++
  ".Lblsk_kzg_probe_done:"

def ziskBls12KzgPointEvalRealProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBls12KzgPointEvalRealProbePrologue
  dataAsm     :=
    bls12G2DataSection ++
    bls12PairingAllDataFragments ++
    bls12KzgDataFragment
}

end EvmAsm.Codegen
