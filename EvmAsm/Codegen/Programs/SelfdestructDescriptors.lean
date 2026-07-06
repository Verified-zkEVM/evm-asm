/-
  EvmAsm.Codegen.Programs.SelfdestructDescriptors

  SELFDESTRUCT descriptor builders for post-state-root replay.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Mpt

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## selfdestruct_delete_descriptor

    Build one `mpt_state_root_ins` account-delete descriptor from a canonical
    20-byte account address. This is the descriptor shape needed for EIP-6780
    deletion of contracts created and selfdestructed in the same transaction.

    Calling convention:
      a0 = 20-byte account address ptr
      a1 = descriptor out ptr (40 bytes)
      a2 = path out ptr (64 bytes)

    Descriptor layout:
      +0 path ptr
      +8 path length = 64
      +16 value ptr = 0
      +24 value length = 0
      +32 mode = 2 (delete)

    a0 returns 0. -/
def selfdestructDeleteDescriptorFunction : String :=
  "selfdestruct_delete_descriptor:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  mv s0, a1                   # descriptor out\n" ++
  "  mv s1, a2                   # path out\n" ++
  "  li a1, 20\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, mpt_account_path_nibbles\n" ++
  "  sd s1, 0(s0)\n" ++
  "  li t0, 64\n" ++
  "  sd t0, 8(s0)\n" ++
  "  sd zero, 16(s0)\n" ++
  "  sd zero, 24(s0)\n" ++
  "  li t0, 2\n" ++
  "  sd t0, 32(s0)\n" ++
  "  li a0, 0\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-! ## selfdestruct_transfer_descriptors

    Build the account-rewrite descriptors for already-staged
    `selfdestruct_balance_transfer` output. The later deletion descriptor
    helper remains responsible for EIP-6780 same-transaction account deletion.

    Calling convention:
      a0 = origin 20-byte address ptr
      a1 = beneficiary 20-byte address ptr
      a2 = `selfdestruct_balance_transfer` output base
      a3 = same-address flag
      a4 = origin-created-in-tx flag
      a5 = descriptor out ptr
      a6 = path arena out ptr
      a7 = descriptor count out ptr

    Transfer output layout:
      +0 origin result account length
      +8 beneficiary result account length
      +16 origin result account bytes
      +128 beneficiary result account bytes

    Descriptor layout matches `mpt_state_root_ins`.
      +0 path ptr | +8 path length | +16 value ptr | +24 value length | +32 mode

    The helper emits:
      * different beneficiary: 2 modify descriptors, origin then beneficiary;
      * same non-created account: 1 no-op descriptor, preserving path visibility;
      * same created account: 1 modify descriptor for the burned balance followed
        by 1 delete descriptor for the same account; final compaction should let
        the delete descriptor win.

    a0 returns 0. -/
def selfdestructTransferDescriptorsFunction : String :=
  "selfdestruct_transfer_descriptors:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp)\n" ++
  "  sd s6, 56(sp)\n" ++
  "  sd s7, 64(sp)\n" ++
  "  mv s0, a2                   # transfer output base\n" ++
  "  mv s1, a3                   # same-address flag\n" ++
  "  mv s2, a4                   # created-in-tx flag\n" ++
  "  mv s3, a5                   # descriptor cursor\n" ++
  "  mv s4, a6                   # path cursor\n" ++
  "  mv s5, a7                   # out_count ptr\n" ++
  "  mv s6, a1                   # beneficiary address ptr\n" ++
  "  mv s7, a0                   # origin address ptr\n" ++
  "  mv a2, s4\n" ++
  "  li a1, 20\n" ++
  "  jal ra, mpt_account_path_nibbles\n" ++
  "  sd s4, 0(s3)\n" ++
  "  li t0, 64\n" ++
  "  sd t0, 8(s3)\n" ++
  "  addi t0, s0, 16\n" ++
  "  sd t0, 16(s3)\n" ++
  "  ld t0, 0(s0)\n" ++
  "  sd t0, 24(s3)\n" ++
  "  li t0, 0\n" ++
  "  beqz s1, .Lsdtd_origin_mode_ready\n" ++
  "  bnez s2, .Lsdtd_origin_mode_ready\n" ++
  "  li t0, 3                    # same non-created account: net no-op\n" ++
  ".Lsdtd_origin_mode_ready:\n" ++
  "  sd t0, 32(s3)\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s5)\n" ++
  "  beqz s1, .Lsdtd_beneficiary_desc\n" ++
  "  bnez s2, .Lsdtd_delete_desc\n" ++
  "  j .Lsdtd_ok\n" ++
  ".Lsdtd_beneficiary_desc:\n" ++
  "  addi s3, s3, 40\n" ++
  "  addi s4, s4, 64\n" ++
  "  mv a0, s6                   # beneficiary address ptr\n" ++
  "  li a1, 20\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, mpt_account_path_nibbles\n" ++
  "  sd s4, 0(s3)\n" ++
  "  li t0, 64\n" ++
  "  sd t0, 8(s3)\n" ++
  "  addi t0, s0, 128\n" ++
  "  sd t0, 16(s3)\n" ++
  "  ld t0, 8(s0)\n" ++
  "  sd t0, 24(s3)\n" ++
  "  sd zero, 32(s3)\n" ++
  "  li t0, 2\n" ++
  "  sd t0, 0(s5)\n" ++
  "  j .Lsdtd_ok\n" ++
  ".Lsdtd_delete_desc:\n" ++
  "  addi s3, s3, 40\n" ++
  "  addi s4, s4, 64\n" ++
  "  mv a0, s7                   # same-tx-created origin address ptr\n" ++
  "  mv a1, s3                   # delete descriptor out\n" ++
  "  mv a2, s4                   # delete path out\n" ++
  "  jal ra, selfdestruct_delete_descriptor\n" ++
  "  li t0, 2\n" ++
  "  sd t0, 0(s5)\n" ++
  ".Lsdtd_ok:\n" ++
  "  li a0, 0\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp)\n" ++
  "  ld s6, 56(sp)\n" ++
  "  ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_selfdestruct_delete_descriptor`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  20-byte account address
    Output layout:
      OUTPUT+0    descriptor (40 bytes)
      OUTPUT+40   path (64 nibble bytes)
      OUTPUT+248  status -/
def ziskSelfdestructDeleteDescriptorPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  addi a0, t0, 8              # 20-byte account address\n" ++
  "  li a1, 0xa0010000           # descriptor\n" ++
  "  li a2, 0xa0010028           # path\n" ++
  "  jal ra, selfdestruct_delete_descriptor\n" ++
  "  li t0, 0xa00100f8\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsddd_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  mptAccountPathNibblesFunction ++ "\n" ++
  selfdestructDeleteDescriptorFunction ++ "\n" ++
  ".Lsddd_pdone:"

def ziskSelfdestructDeleteDescriptorProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSelfdestructDeleteDescriptorPrologue
  dataAsm     := ziskMptAccountPathNibblesDataSection
}

/-- `zisk_selfdestruct_transfer_descriptors`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8   origin address (20 bytes)
      +28  beneficiary address (20 bytes)
      +48  same-address flag (u64)
      +56  origin-created-in-tx flag (u64)
      +64  origin result RLP length (u64)
      +72  beneficiary result RLP length (u64)
      +80  origin result RLP bytes, fixed 96-byte probe slot
      +176 beneficiary result RLP bytes, fixed 96-byte probe slot
    Output layout:
      OUTPUT+0    status
      OUTPUT+8    descriptor count
      OUTPUT+16   descriptors (2 x 40 bytes)
      OUTPUT+96   paths (2 x 64 bytes)
      OUTPUT+248  duplicate status -/
def ziskSelfdestructTransferDescriptorsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  addi a0, t0, 8              # origin address\n" ++
  "  addi a1, t0, 28             # beneficiary address\n" ++
  "  ld a3, 48(t0)               # same-address flag\n" ++
  "  ld a4, 56(t0)               # created-in-tx flag\n" ++
  "  li a2, 0xa0020000           # synthetic transfer output\n" ++
  "  ld t1, 64(t0)\n" ++
  "  sd t1, 0(a2)\n" ++
  "  ld t1, 72(t0)\n" ++
  "  sd t1, 8(a2)\n" ++
  "  addi t2, a2, 16\n" ++
  "  addi t3, t0, 80\n" ++
  "  li t4, 96\n" ++
  ".Lsdtdp_copy_origin:\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb t5, 0(t2)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lsdtdp_copy_origin\n" ++
  "  addi t2, a2, 128\n" ++
  "  addi t3, t0, 176\n" ++
  "  li t4, 96\n" ++
  ".Lsdtdp_copy_beneficiary:\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb t5, 0(t2)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lsdtdp_copy_beneficiary\n" ++
  "  li a5, 0xa0010010           # descriptors\n" ++
  "  li a6, 0xa0010060           # paths\n" ++
  "  li a7, 0xa0010008           # count\n" ++
  "  jal ra, selfdestruct_transfer_descriptors\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  li t0, 0xa00100f8\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsdtd_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  mptAccountPathNibblesFunction ++ "\n" ++
  selfdestructDeleteDescriptorFunction ++ "\n" ++
  selfdestructTransferDescriptorsFunction ++ "\n" ++
  ".Lsdtd_pdone:"

def ziskSelfdestructTransferDescriptorsDataSection : String :=
  ziskMptAccountPathNibblesDataSection ++ "\n" ++
  ".balign 8\n" ++
  ".section .data\n" ++
  ".balign 16\n" ++
  ".org 0x20000\n" ++
  "sdtd_transfer_output:\n" ++
  "  .zero 192\n"

def ziskSelfdestructTransferDescriptorsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSelfdestructTransferDescriptorsPrologue
  dataAsm     := ziskSelfdestructTransferDescriptorsDataSection
}

end EvmAsm.Codegen
