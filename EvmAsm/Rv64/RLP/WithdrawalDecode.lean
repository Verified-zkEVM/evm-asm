/-
  EvmAsm.Rv64.RLP.WithdrawalDecode

  A verified, strict, single-pass walk-based drop-in for the codegen guest
  `withdrawal_decode`: parse an RLP withdrawal `[index, validator_index, address, amount]`
  and write the 48-byte struct. Unlike the existing assembly (four `rlp_list_nth_item`
  re-scans), this makes one left-to-right pass with `rlp_walk_init` + `rlp_walk_next` +
  strict `rlp_content_to_u64`, and is proved to coincide with the strict pure
  `EvmAsm.EL.decodeWithdrawal`.

  `withdrawal_decode` is the first **non-leaf** verified routine: it preserves callee-saved
  registers across the calls, so it uses a stack frame (modeled as `↦ₘ` cells), and invokes
  the verified leaves via `cpsCallWithin`.

  Built block-by-block: each segment is a `cpsTripleWithin` proved here and composed.
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.CPSCall
import EvmAsm.Rv64.RLP.WalkDecodeBridge

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64

/-- **Prologue.** Push a 32-byte frame, save `ra` and callee-saved `s0/s1/s2`, and move the
    output-struct pointer (`a2`) into `s0`. Registers: `sp = x2`, `ra = x1`, `s0 = x8`,
    `s1 = x9`, `s2 = x18`, `a2 = x12`. -/
def wd_prologue : List Instr :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),   -- addi sp, sp, -32
    .SD .x2 .x1 (0 : BitVec 12),        -- sd ra, 0(sp)
    .SD .x2 .x8 (8 : BitVec 12),        -- sd s0, 8(sp)
    .SD .x2 .x9 (16 : BitVec 12),       -- sd s1, 16(sp)
    .SD .x2 .x18 (24 : BitVec 12),      -- sd s2, 24(sp)
    .MV .x8 .x12 ]                       -- mv s0, a2

/-- `CodeReq` of the prologue at `base`. -/
def wd_prologue_code (base : Word) : CodeReq := CodeReq.ofProg base wd_prologue

theorem wd_prologue_length : wd_prologue.length = 6 := rfl

/-- The prologue saves `ra`/`s0`/`s1`/`s2` into the freshly-pushed frame and sets `s0` to the
    output-struct pointer, reaching `base + 24` (the first instruction after the prologue). -/
theorem wd_prologue_spec (base sp0 raVal s0Old s1Old s2Old structPtr m0 m1 m2 m3 : Word) :
    cpsTripleWithin 6 base (base + 24) (wd_prologue_code base)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
        (.x18 ↦ᵣ s2Old) ** (.x12 ↦ᵣ structPtr) **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ m0) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ m1) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ m2) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ m3))
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) ** (.x1 ↦ᵣ raVal) **
        (.x8 ↦ᵣ structPtr) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x12 ↦ᵣ structPtr) **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ raVal) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ s0Old) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ s1Old) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 24) ↦ₘ s2Old)) := by
  have hadd := addi_spec_gen_same_within .x2 sp0 (-32 : BitVec 12) base (by decide)
  have hsd0 := sd_spec_gen_within .x2 .x1 (sp0 + signExtend12 (-32 : BitVec 12)) raVal m0
    (0 : BitVec 12) (base + 4)
  have hsd1 := sd_spec_gen_within .x2 .x8 (sp0 + signExtend12 (-32 : BitVec 12)) s0Old m1
    (8 : BitVec 12) (base + 8)
  have hsd2 := sd_spec_gen_within .x2 .x9 (sp0 + signExtend12 (-32 : BitVec 12)) s1Old m2
    (16 : BitVec 12) (base + 12)
  have hsd3 := sd_spec_gen_within .x2 .x18 (sp0 + signExtend12 (-32 : BitVec 12)) s2Old m3
    (24 : BitVec 12) (base + 16)
  have hmv := mv_spec_gen_within .x8 .x12 structPtr s0Old (base + 20) (by decide)
  simp only [signExtend12_0] at hsd0
  runBlock hadd hsd0 hsd1 hsd2 hsd3 hmv

end EvmAsm.Rv64.RLP
