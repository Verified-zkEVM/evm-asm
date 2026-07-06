/-
  EvmAsm.Codegen.Programs.BlockVerdictModeledSystem

  Small block-verdict helper split out for the file-size hard cap.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bsr_apply_modeled_system_post_fields

    Apply tx-level BAL balance/nonce post-fields to an already-recorded system
    account descriptor. Storage changes stay with the explicit EIP-2935/EIP-4788
    replay in BlockVerdict, avoiding duplicate state-trie descriptors for the
    same system contract while still honoring SELFDESTRUCT value transfers to
    that account.

    a0 = AccountChanges ptr   a1 = AccountChanges len   a2 = descriptor index
    a0 (output) = 0 ok / 1 parse or rewrite failure. -/
def bsrApplyModeledSystemPostFields_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.baap_bal (GuestAddrs.bsr_apply_modeled_system_post_fields + 52)),
    .ADDI .x12 .x12 (laLo GuestAddrs.baap_bal (GuestAddrs.bsr_apply_modeled_system_post_fields + 52)),
    .AUIPC .x13 (laHi GuestAddrs.baap_bal_len (GuestAddrs.bsr_apply_modeled_system_post_fields + 60)),
    .ADDI .x13 .x13 (laLo GuestAddrs.baap_bal_len (GuestAddrs.bsr_apply_modeled_system_post_fields + 60)),
    .AUIPC .x14 (laHi GuestAddrs.baap_nonce (GuestAddrs.bsr_apply_modeled_system_post_fields + 68)),
    .ADDI .x14 .x14 (laLo GuestAddrs.baap_nonce (GuestAddrs.bsr_apply_modeled_system_post_fields + 68)),
    .AUIPC .x15 (laHi GuestAddrs.baap_nonce_len (GuestAddrs.bsr_apply_modeled_system_post_fields + 76)),
    .ADDI .x15 .x15 (laLo GuestAddrs.baap_nonce_len (GuestAddrs.bsr_apply_modeled_system_post_fields + 76)),
    .JAL .x1 (jalOff GuestAddrs.bal_account_post_fields (GuestAddrs.bsr_apply_modeled_system_post_fields + 84)),
    .BNE .x10 .x0 (240 : BitVec 13),
    .SLLI .x5 .x18 (5 : BitVec 6),
    .SLLI .x6 .x18 (3 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .AUIPC .x6 (laHi GuestAddrs.bsr_changes (GuestAddrs.bsr_apply_modeled_system_post_fields + 104)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bsr_changes (GuestAddrs.bsr_apply_modeled_system_post_fields + 104)),
    .ADD .x21 .x6 .x5,
    .LD .x19 .x21 (16 : BitVec 12),
    .LD .x20 .x21 (24 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.baap_nonce_len (GuestAddrs.bsr_apply_modeled_system_post_fields + 124)),
    .ADDI .x5 .x5 (laLo GuestAddrs.baap_nonce_len (GuestAddrs.bsr_apply_modeled_system_post_fields + 124)),
    .LD .x5 .x5 (0 : BitVec 12),
    .LI .x6 (-1 : Word),
    .BEQ .x5 .x6 (72 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x20,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.baap_nonce (GuestAddrs.bsr_apply_modeled_system_post_fields + 156)),
    .ADDI .x13 .x13 (laLo GuestAddrs.baap_nonce (GuestAddrs.bsr_apply_modeled_system_post_fields + 156)),
    .MV .x14 .x5,
    .AUIPC .x15 (laHi GuestAddrs.baap_tmp (GuestAddrs.bsr_apply_modeled_system_post_fields + 168)),
    .ADDI .x15 .x15 (laLo GuestAddrs.baap_tmp (GuestAddrs.bsr_apply_modeled_system_post_fields + 168)),
    .AUIPC .x16 (laHi GuestAddrs.baap_tmp_len (GuestAddrs.bsr_apply_modeled_system_post_fields + 176)),
    .ADDI .x16 .x16 (laLo GuestAddrs.baap_tmp_len (GuestAddrs.bsr_apply_modeled_system_post_fields + 176)),
    .JAL .x1 (jalOff GuestAddrs.account_set_uint_field (GuestAddrs.bsr_apply_modeled_system_post_fields + 184)),
    .BNE .x10 .x0 (140 : BitVec 13),
    .AUIPC .x19 (laHi GuestAddrs.baap_tmp (GuestAddrs.bsr_apply_modeled_system_post_fields + 192)),
    .ADDI .x19 .x19 (laLo GuestAddrs.baap_tmp (GuestAddrs.bsr_apply_modeled_system_post_fields + 192)),
    .AUIPC .x5 (laHi GuestAddrs.baap_tmp_len (GuestAddrs.bsr_apply_modeled_system_post_fields + 200)),
    .ADDI .x5 .x5 (laLo GuestAddrs.baap_tmp_len (GuestAddrs.bsr_apply_modeled_system_post_fields + 200)),
    .LD .x20 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.baap_bal_len (GuestAddrs.bsr_apply_modeled_system_post_fields + 212)),
    .ADDI .x5 .x5 (laLo GuestAddrs.baap_bal_len (GuestAddrs.bsr_apply_modeled_system_post_fields + 212)),
    .LD .x5 .x5 (0 : BitVec 12),
    .LI .x6 (-1 : Word),
    .BEQ .x5 .x6 (72 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x20,
    .LI .x12 (1 : Word),
    .AUIPC .x13 (laHi GuestAddrs.baap_bal (GuestAddrs.bsr_apply_modeled_system_post_fields + 244)),
    .ADDI .x13 .x13 (laLo GuestAddrs.baap_bal (GuestAddrs.bsr_apply_modeled_system_post_fields + 244)),
    .MV .x14 .x5,
    .AUIPC .x15 (laHi GuestAddrs.baap_tmp2 (GuestAddrs.bsr_apply_modeled_system_post_fields + 256)),
    .ADDI .x15 .x15 (laLo GuestAddrs.baap_tmp2 (GuestAddrs.bsr_apply_modeled_system_post_fields + 256)),
    .AUIPC .x16 (laHi GuestAddrs.baap_tmp2_len (GuestAddrs.bsr_apply_modeled_system_post_fields + 264)),
    .ADDI .x16 .x16 (laLo GuestAddrs.baap_tmp2_len (GuestAddrs.bsr_apply_modeled_system_post_fields + 264)),
    .JAL .x1 (jalOff GuestAddrs.account_set_uint_field (GuestAddrs.bsr_apply_modeled_system_post_fields + 272)),
    .BNE .x10 .x0 (52 : BitVec 13),
    .AUIPC .x19 (laHi GuestAddrs.baap_tmp2 (GuestAddrs.bsr_apply_modeled_system_post_fields + 280)),
    .ADDI .x19 .x19 (laLo GuestAddrs.baap_tmp2 (GuestAddrs.bsr_apply_modeled_system_post_fields + 280)),
    .AUIPC .x5 (laHi GuestAddrs.baap_tmp2_len (GuestAddrs.bsr_apply_modeled_system_post_fields + 288)),
    .ADDI .x5 .x5 (laLo GuestAddrs.baap_tmp2_len (GuestAddrs.bsr_apply_modeled_system_post_fields + 288)),
    .LD .x20 .x5 (0 : BitVec 12),
    .LD .x10 .x21 (16 : BitVec 12),
    .MV .x11 .x19,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.mset_memcpy (GuestAddrs.bsr_apply_modeled_system_post_fields + 312)),
    .SD .x21 .x20 (24 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bsrApplyModeledSystemPostFields_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bsrApplyModeledSystemPostFields_relocs : RelocTable :=
  [ (13, .la .x12 "baap_bal"),
    (15, .la .x13 "baap_bal_len"),
    (17, .la .x14 "baap_nonce"),
    (19, .la .x15 "baap_nonce_len"),
    (21, .jal .x1 "bal_account_post_fields"),
    (26, .la .x6 "bsr_changes"),
    (31, .la .x5 "baap_nonce_len"),
    (39, .la .x13 "baap_nonce"),
    (42, .la .x15 "baap_tmp"),
    (44, .la .x16 "baap_tmp_len"),
    (46, .jal .x1 "account_set_uint_field"),
    (48, .la .x19 "baap_tmp"),
    (50, .la .x5 "baap_tmp_len"),
    (53, .la .x5 "baap_bal_len"),
    (61, .la .x13 "baap_bal"),
    (64, .la .x15 "baap_tmp2"),
    (66, .la .x16 "baap_tmp2_len"),
    (68, .jal .x1 "account_set_uint_field"),
    (70, .la .x19 "baap_tmp2"),
    (72, .la .x5 "baap_tmp2_len"),
    (78, .jal .x1 "mset_memcpy") ]

def bsrApplyModeledSystemPostFieldsFunction : String :=
  "bsr_apply_modeled_system_post_fields:\n" ++ emitProgramR bsrApplyModeledSystemPostFields_prog bsrApplyModeledSystemPostFields_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bsrApplyModeledSystemPostFields_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bsrApplyModeledSystemPostFieldsFunction_eq_prog :
    bsrApplyModeledSystemPostFieldsFunction = "bsr_apply_modeled_system_post_fields:\n" ++ emitProgramR bsrApplyModeledSystemPostFields_prog bsrApplyModeledSystemPostFields_relocs := rfl

#guard bsrApplyModeledSystemPostFieldsFunction.startsWith "bsr_apply_modeled_system_post_fields:\n"
#guard bsrApplyModeledSystemPostFields_prog.length = 92
end EvmAsm.Codegen
