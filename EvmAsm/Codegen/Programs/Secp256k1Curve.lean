/-
  EvmAsm.Codegen.Programs.Secp256k1Curve

  Codegen-only affine secp256k1 curve helpers for staged software public-key
  recovery. Points are 64-byte big-endian affine records: x || y.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Secp256k1Field

namespace EvmAsm.Codegen

open EvmAsm.Rv64

private def generatorPointAsm : String :=
  "  .byte 0x79,0xbe,0x66,0x7e,0xf9,0xdc,0xbb,0xac\n" ++
  "  .byte 0x55,0xa0,0x62,0x95,0xce,0x87,0x0b,0x07\n" ++
  "  .byte 0x02,0x9b,0xfc,0xdb,0x2d,0xce,0x28,0xd9\n" ++
  "  .byte 0x59,0xf2,0x81,0x5b,0x16,0xf8,0x17,0x98\n" ++
  "  .byte 0x48,0x3a,0xda,0x77,0x26,0xa3,0xc4,0x65\n" ++
  "  .byte 0x5d,0xa4,0xfb,0xfc,0x0e,0x11,0x08,0xa8\n" ++
  "  .byte 0xfd,0x17,0xb4,0x48,0xa6,0x85,0x54,0x19\n" ++
  "  .byte 0x9c,0x47,0xd0,0x8f,0xfb,0x10,0xd4,0xb8\n"

private def generator2PointAsm : String :=
  "  .byte 0xc6,0x04,0x7f,0x94,0x41,0xed,0x7d,0x6d\n" ++
  "  .byte 0x30,0x45,0x40,0x6e,0x95,0xc0,0x7c,0xd8\n" ++
  "  .byte 0x5c,0x77,0x8e,0x4b,0x8c,0xef,0x3c,0xa7\n" ++
  "  .byte 0xab,0xac,0x09,0xb9,0x5c,0x70,0x9e,0xe5\n" ++
  "  .byte 0x1a,0xe1,0x68,0xfe,0xa6,0x3d,0xc3,0x39\n" ++
  "  .byte 0xa3,0xc5,0x84,0x19,0x46,0x6c,0xea,0xee\n" ++
  "  .byte 0xf7,0xf6,0x32,0x65,0x32,0x66,0xd0,0xe1\n" ++
  "  .byte 0x23,0x64,0x31,0xa9,0x50,0xcf,0xe5,0x2a\n"

def secp256k1CurveDataSection : String :=
  secp256k1FieldDataSection ++
  ".balign 8\n" ++
  "secp256k1_generator:\n" ++
  generatorPointAsm ++
  ".balign 8\n" ++
  "secp256k1_generator_2:\n" ++
  generator2PointAsm ++
  ".balign 8\n" ++
  "secc_slope:\n  .zero 32\n" ++
  "secc_den:\n  .zero 32\n" ++
  "secc_inv:\n  .zero 32\n" ++
  "secc_tmp0:\n  .zero 32\n" ++
  "secc_tmp1:\n  .zero 32\n" ++
  "secc_tmp2:\n  .zero 32\n"

/-- Double an affine point. a0=input x||y, a1=output x||y. Returns 1 for infinity. -/
def secp256k1PointDoubleFunction : String :=
  "secp256k1_point_double:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  addi a0, s0, 32\n" ++
  "  jal ra, secf_is_zero32\n" ++
  "  beqz a0, .Lsecc_double_finite\n" ++
  "  mv a0, s1\n" ++
  "  jal ra, secf_zero32\n" ++
  "  addi a0, s1, 32\n" ++
  "  jal ra, secf_zero32\n" ++
  "  li a0, 1\n" ++
  "  j .Lsecc_double_ret\n" ++
  ".Lsecc_double_finite:\n" ++
  "  mv a0, s0\n" ++
  "  la a2, secc_tmp0\n" ++
  "  jal ra, secf_square_mod_p     # tmp0 = x^2\n" ++
  "  la a0, secc_tmp0\n" ++
  "  mv a1, a0\n" ++
  "  la a2, secc_tmp1\n" ++
  "  jal ra, secf_add_mod_p        # tmp1 = 2*x^2\n" ++
  "  la a0, secc_tmp1\n" ++
  "  la a1, secc_tmp0\n" ++
  "  la a2, secc_tmp0\n" ++
  "  jal ra, secf_add_mod_p        # tmp0 = 3*x^2\n" ++
  "  addi a0, s0, 32\n" ++
  "  mv a1, a0\n" ++
  "  la a2, secc_den\n" ++
  "  jal ra, secf_add_mod_p        # den = 2*y\n" ++
  "  la a0, secc_den\n" ++
  "  la a1, secc_inv\n" ++
  "  jal ra, secf_inv_mod_p\n" ++
  "  bnez a0, .Lsecc_double_inf\n" ++
  "  la a0, secc_tmp0\n" ++
  "  la a1, secc_inv\n" ++
  "  la a2, secc_slope\n" ++
  "  jal ra, secf_mul_mod_p        # slope\n" ++
  "  la a0, secc_slope\n" ++
  "  la a2, secc_tmp0\n" ++
  "  jal ra, secf_square_mod_p     # slope^2\n" ++
  "  la a0, secc_tmp0\n" ++
  "  mv a1, s0\n" ++
  "  la a2, secc_tmp0\n" ++
  "  jal ra, secf_sub_mod_p\n" ++
  "  la a0, secc_tmp0\n" ++
  "  mv a1, s0\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, secf_sub_mod_p        # out.x = slope^2 - 2*x\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, secc_tmp0\n" ++
  "  jal ra, secf_sub_mod_p        # tmp0 = x - out.x\n" ++
  "  la a0, secc_slope\n" ++
  "  la a1, secc_tmp0\n" ++
  "  la a2, secc_tmp1\n" ++
  "  jal ra, secf_mul_mod_p\n" ++
  "  la a0, secc_tmp1\n" ++
  "  addi a1, s0, 32\n" ++
  "  addi a2, s1, 32\n" ++
  "  jal ra, secf_sub_mod_p        # out.y\n" ++
  "  li a0, 0\n" ++
  "  j .Lsecc_double_ret\n" ++
  ".Lsecc_double_inf:\n" ++
  "  mv a0, s1\n" ++
  "  jal ra, secf_zero32\n" ++
  "  addi a0, s1, 32\n" ++
  "  jal ra, secf_zero32\n" ++
  "  li a0, 1\n" ++
  ".Lsecc_double_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- Add two affine points. a0=P, a1=Q, a2=out. Returns 1 for infinity. -/
def secp256k1PointAddFunction : String :=
  "secp256k1_point_add:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, secf_eq32\n" ++
  "  beqz a0, .Lsecc_add_distinct_x\n" ++
  "  addi a0, s0, 32\n" ++
  "  addi a1, s1, 32\n" ++
  "  jal ra, secf_eq32\n" ++
  "  beqz a0, .Lsecc_add_inf\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, secp256k1_point_double\n" ++
  "  j .Lsecc_add_ret\n" ++
  ".Lsecc_add_distinct_x:\n" ++
  "  addi a0, s1, 32\n" ++
  "  addi a1, s0, 32\n" ++
  "  la a2, secc_tmp0\n" ++
  "  jal ra, secf_sub_mod_p        # y2-y1\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s0\n" ++
  "  la a2, secc_den\n" ++
  "  jal ra, secf_sub_mod_p        # x2-x1\n" ++
  "  la a0, secc_den\n" ++
  "  la a1, secc_inv\n" ++
  "  jal ra, secf_inv_mod_p\n" ++
  "  bnez a0, .Lsecc_add_inf\n" ++
  "  la a0, secc_tmp0\n" ++
  "  la a1, secc_inv\n" ++
  "  la a2, secc_slope\n" ++
  "  jal ra, secf_mul_mod_p\n" ++
  "  la a0, secc_slope\n" ++
  "  la a2, secc_tmp1\n" ++
  "  jal ra, secf_square_mod_p\n" ++
  "  la a0, secc_tmp1\n" ++
  "  mv a1, s0\n" ++
  "  la a2, secc_tmp1\n" ++
  "  jal ra, secf_sub_mod_p\n" ++
  "  la a0, secc_tmp1\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, secf_sub_mod_p        # out.x\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s2\n" ++
  "  la a2, secc_tmp1\n" ++
  "  jal ra, secf_sub_mod_p        # x1-out.x\n" ++
  "  la a0, secc_slope\n" ++
  "  la a1, secc_tmp1\n" ++
  "  la a2, secc_tmp2\n" ++
  "  jal ra, secf_mul_mod_p\n" ++
  "  la a0, secc_tmp2\n" ++
  "  addi a1, s0, 32\n" ++
  "  addi a2, s2, 32\n" ++
  "  jal ra, secf_sub_mod_p\n" ++
  "  li a0, 0\n" ++
  "  j .Lsecc_add_ret\n" ++
  ".Lsecc_add_inf:\n" ++
  "  mv a0, s2\n" ++
  "  jal ra, secf_zero32\n" ++
  "  addi a0, s2, 32\n" ++
  "  jal ra, secf_zero32\n" ++
  "  li a0, 1\n" ++
  ".Lsecc_add_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 40\n" ++
  "  ret"

def secp256k1CurveCommonFunctions : String :=
  secp256k1FieldCommonFunctions ++ "\n" ++
  secp256k1PointDoubleFunction ++ "\n" ++
  secp256k1PointAddFunction

def ziskSecp256k1CurvePointOpsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la a0, secp256k1_generator\n" ++
  "  li a1, 0xa0010008\n" ++
  "  jal ra, secp256k1_point_double\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la a0, secp256k1_generator\n" ++
  "  la a1, secp256k1_generator\n" ++
  "  li a2, 0xa0010050\n" ++
  "  jal ra, secp256k1_point_add\n" ++
  "  li t0, 0xa0010048\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsecc_probe_done\n" ++
  secp256k1CurveCommonFunctions ++ "\n" ++
  ".Lsecc_probe_done:"

def ziskSecp256k1CurvePointOpsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSecp256k1CurvePointOpsPrologue
  dataAsm     := secp256k1CurveDataSection
}

private def secp256k1ZiskLittleLimbPointData : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "secp256k1_zisk_g_add:\n" ++
  "  .quad 0x59f2815b16f81798\n" ++
  "  .quad 0x029bfcdb2dce28d9\n" ++
  "  .quad 0x55a06295ce870b07\n" ++
  "  .quad 0x79be667ef9dcbbac\n" ++
  "  .quad 0x9c47d08ffb10d4b8\n" ++
  "  .quad 0xfd17b448a6855419\n" ++
  "  .quad 0x5da4fbfc0e1108a8\n" ++
  "  .quad 0x483ada7726a3c465\n" ++
  "secp256k1_zisk_g_add_rhs:\n" ++
  "  .quad 0x59f2815b16f81798\n" ++
  "  .quad 0x029bfcdb2dce28d9\n" ++
  "  .quad 0x55a06295ce870b07\n" ++
  "  .quad 0x79be667ef9dcbbac\n" ++
  "  .quad 0x9c47d08ffb10d4b8\n" ++
  "  .quad 0xfd17b448a6855419\n" ++
  "  .quad 0x5da4fbfc0e1108a8\n" ++
  "  .quad 0x483ada7726a3c465\n" ++
  "secp256k1_zisk_g_dbl:\n" ++
  "  .quad 0x59f2815b16f81798\n" ++
  "  .quad 0x029bfcdb2dce28d9\n" ++
  "  .quad 0x55a06295ce870b07\n" ++
  "  .quad 0x79be667ef9dcbbac\n" ++
  "  .quad 0x9c47d08ffb10d4b8\n" ++
  "  .quad 0xfd17b448a6855419\n" ++
  "  .quad 0x5da4fbfc0e1108a8\n" ++
  "  .quad 0x483ada7726a3c465\n" ++
  ".balign 8\n" ++
  "secp256k1_zisk_add_args:\n" ++
  "  .quad secp256k1_zisk_g_add\n" ++
  "  .quad secp256k1_zisk_g_add_rhs\n"

private def secp256k1ZiskAddDblProbePrologue
    (addSymbol dblSymbol : String) : String :=
  "  li sp, 0xa0050000\n" ++
  "  la a0, secp256k1_zisk_add_args\n" ++
  "  jal ra, " ++ addSymbol ++ "\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, secp256k1_zisk_g_add\n" ++
  "  li t2, 8\n" ++
  "  addi t0, t0, 8\n" ++
  ".Lsecp256k1_zisk_copy_add:\n" ++
  "  ld t3, 0(t1)\n" ++
  "  sd t3, 0(t0)\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lsecp256k1_zisk_copy_add\n" ++
  "  la a0, secp256k1_zisk_g_dbl\n" ++
  "  jal ra, " ++ dblSymbol ++ "\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, secp256k1_zisk_g_dbl\n" ++
  "  li t2, 8\n" ++
  "  addi t0, t0, 8\n" ++
  ".Lsecp256k1_zisk_copy_dbl:\n" ++
  "  ld t3, 0(t1)\n" ++
  "  sd t3, 0(t0)\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lsecp256k1_zisk_copy_dbl\n"

def ziskSecp256k1AddDblSyscallProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := secp256k1ZiskAddDblProbePrologue
    "syscall_secp256k1_add" "syscall_secp256k1_dbl"
  dataAsm     := secp256k1ZiskLittleLimbPointData
}

def ziskSecp256k1AddDblOpcodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := secp256k1ZiskAddDblProbePrologue
    "_opcode_secp256k1_add" "_opcode_secp256k1_dbl"
  dataAsm     := secp256k1ZiskLittleLimbPointData
}

end EvmAsm.Codegen
