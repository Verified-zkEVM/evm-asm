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
import EvmAsm.Rv64.RLP.ContentToU64
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.RLP.WalkDecodeBridge

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

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

/-- **Call block: `rlp_content_to_u64`.** A `jal ra` at `callerPC` into the verified
    `rlp_content_to_u64` (appended at `calleeEntry = callerPC + sext offset`) decodes the
    `len`-byte content at `srcBase + srcOff` and returns to `callerPC + 4` with the 4-way status
    result. Establishes the `cpsCallWithin` pattern the scalar-field blocks reuse. -/
theorem wd_call_content_to_u64
    (callerPC calleeEntry srcBase vOld t0Old t2Old t3Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat) (offset : BitVec 21)
    (hoffset : callerPC + signExtend21 offset = calleeEntry)
    (halign : (callerPC + 4) &&& ~~~1 = callerPC + 4)
    (hdisj : (CodeReq.singleton callerPC (.JAL .x1 offset)).Disjoint
      (rlp_content_to_u64_code calleeEntry))
    (hlen64 : len < 2 ^ 64) (hsalign : srcBase.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length) (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true) :
    cpsTripleWithin (1 + (7 * len + 11)) callerPC (callerPC + 4)
      ((CodeReq.singleton callerPC (.JAL .x1 offset)).union (rlp_content_to_u64_code calleeEntry))
      ((.x1 ↦ᵣ vOld) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
         (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x7 ↦ᵣ t2Old) **
         (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes))
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (callerPC + 4)) ** bytesRegion srcBase srcBytes) **
       (fun h =>
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
            ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
         (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
            (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0⌝) h))) := by
  have hcallee := rlp_content_to_u64_spec_within calleeEntry srcBase (callerPC + 4) t0Old t2Old
    t3Old srcBytes srcOff len hlen64 hsalign hslen hsover hsvalid
  -- `cpsCallWithin` fixes the expected callee `Pre = (x1 ↦ callerPC+4) ** Prest` from the goal;
  -- reorder the callee's precondition (`x1` is mid-list) to that form via `xperm_hyp`.
  exact cpsCallWithin offset hoffset halign (by pcFree) hdisj
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => hp) hcallee)

end EvmAsm.Rv64.RLP
