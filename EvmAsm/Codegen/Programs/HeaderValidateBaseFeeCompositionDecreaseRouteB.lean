/-
  Decrease-route composition toward the Route-B K73 contract (#12346 item 2b).

  The increasing arm ships a fully-composed entry-to-return theorem
  (`k73_increase_entry_status_div_zero_to_return_general_spec_within`).  The
  decreasing arm only ships seams.  This file assembles them bottom-up:

    entry            (20, premise-free)              K73 .. K73 + 88
    mul call/status  (needs deployed mul callee)     K73 + 88 .. K73 + 96
    div pair         (premise-free, htargetPos)      K73 + 96 .. K73 + 128
    branch x20=0     (premise-free)                  K73 + 128 .. K73 + 176
    div-to-sub       (premise-free modulo ABI facts) K73 + 176 .. K73 + 224
    borrow branch                                    K73 + 224 .. K73 + 228
    tails            (symbolic raIn, saved-generic)  K73 + 228/+276 .. raIn

  Everything here composes already-proven seams; no new instruction is
  interpreted.  The borrow branch below is the only machine-level piece that
  was missing entirely: the decrease subtract's overflow test at K73 + 224
  branches on the callee borrow register against x0.
-/

/-
  Decrease-route Route-B junction casts and wrapper-vocab adapter (#12346 item 2b).
-/

import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeEntry
import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeSpec
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeMulNativeContract
import EvmAsm.Codegen.Programs.U256MulU64Be.Arith
import EvmAsm.Codegen.Proofs.U256BeFlatTriples
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpecCore
import EvmAsm.Rv64.BitAux
import EvmAsm.Rv64.Tactics.XPermCert
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeCompositionDecreaseWholeRoute

namespace EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec hiding K73
open EvmAsm.Codegen.HeaderValidateBaseFeeSpec
open EvmAsm.Codegen.U256DivU64BeSAsm
open EvmAsm.Codegen.U256SubBeSAsm
open EvmAsm.Codegen.HeaderValidateBaseFeeMulNativeContract

/-- The subtract's written bytes at `Expected`: the base minus the twice-
    halved accumulator image.  Defined as one token (body identical to the
    inline spelling inside `k73_decr_sub_return_post`) so the content cast
    can be stated without quadruple-spelling the quotient windows. -/
private def k73_decr_sub_bytes (baseBytes : List (BitVec 8)) (deltaV target : Word)
    (outWin : List (BitVec 8)) : List (BitVec 8) :=
  u256SubBeBytes baseBytes
    (u256DivU64BeQuotBytes
      (u256DivU64BeQuotBytes (k73_decr_img2 baseBytes deltaV outWin)
        (k73_decr_img2 baseBytes deltaV outWin) target)
      (u256DivU64BeQuotBytes (k73_decr_img2 baseBytes deltaV outWin)
        (k73_decr_img2 baseBytes deltaV outWin) target) 8)
    (u256DivU64BeQuotBytes
      (u256DivU64BeQuotBytes (k73_decr_img2 baseBytes deltaV outWin)
        (k73_decr_img2 baseBytes deltaV outWin) target)
      (u256DivU64BeQuotBytes (k73_decr_img2 baseBytes deltaV outWin)
        (k73_decr_img2 baseBytes deltaV outWin) target) 8)

/-- The wrapper-world ambient carried through the decrease route: the
    `hvbfFrame` save slots, the header region, and ownership of every register
    the machine route's exits leave unclaimed but `k73PostOwn` /
    `k73FailurePost` demand.  Top-level def, not a body-local let (certificate
    tactics fail on let-zeta free variables). -/
private def k73_decr_piggyback (wspH old8 headerPtr : Word)
    (headerBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  frameSlotsSaved hvbfFrame wspH (hvbfSaved (H + 40) old8) **
    bytesRegion headerPtr headerBytes **
    regOwn .x13 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** F

/-- Pointwise content swap of an `Expected` window (uses `▸`; `rw` fails
    under implicit transparency). -/
private theorem decr_br_cast {le le' : List (BitVec 8)} {Z : Assertion}
    (heq : le = le') :
    ∀ q : PartialState, ((bytesRegion Expected le ** Z) q) →
      ((bytesRegion Expected le' ** Z) q) :=
  fun _ hp => heq ▸ hp

/-- Success-arm junction cast: the fall exit of the decrease route (status
    `0`, output = the subtract's written bytes) yields the Route-B success
    arm `k73PostOwn` with `Expected` pinned at the spec's written image.
    `hcast` is the arithmetic identity `k73_decr_sub_bytes = hvbfWrittenImage`
    (discharged at the adapter from `k73_decr_machine_bytes_eq_written`). -/
private theorem k73_decr_sub_return_routeB_succ
    (wspH wspK headerPtr parentPtr v9 old18 v19 v20 gasLimit gasUsed target : Word)
    (parentBytes outWin headerBytes : List (BitVec 8)) (Frest : Assertion)
    (hcast : k73_decr_sub_bytes parentBytes (target - gasUsed) target outWin
      = hvbfWrittenImage gasLimit gasUsed parentBytes) :
    ∀ s : PartialState,
      (k73_decr_sub_return_post wspH wspK (H + 40) target parentPtr Expected
        gasUsed headerPtr v9 old18 v19 v20 parentBytes outWin
        (k73_decr_piggyback wspH old8 headerPtr headerBytes Frest)
        (0 : Word)) s →
      (((.x1 ↦ᵣ (H + 40)) ** k73PostOwn wspH wspK headerPtr v9 old18 target
        v19 v20 gasUsed parentPtr parentBytes
        (hvbfWrittenImage gasLimit gasUsed parentBytes) headerBytes
        (H + 40) old8
        (regOwns u256SubBeInPlaceScratch **
          EvmAsm.Codegen.U256MulU64Be.frameSlots
            (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
            parentPtr Expected target (target - gasUsed) (0 : Word) **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
            (k73_decr_img1 parentBytes (target - gasUsed)) **
          regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
          regOwn .x20 ** Frest)) s) := by
  intro s hp
  -- Unfold the exit (`regsAt` into its six pins, the sub-bytes token) and
  -- regroup: the three register pins and the output window up front.
  have hEq1 : (k73_decr_sub_return_post wspH wspK (H + 40) target parentPtr Expected
      gasUsed headerPtr v9 old18 v19 v20 parentBytes outWin
      (k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) (0 : Word)) =
      ((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ Expected) **
        (.x12 ↦ᵣ Expected) **
        bytesRegion Expected
          (k73_decr_sub_bytes parentBytes (target - gasUsed) target outWin) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwns u256SubBeInPlaceScratch **
        bytesRegion parentPtr parentBytes **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
          (k73_decr_img1 parentBytes (target - gasUsed)) **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) := by
    simp only [k73_decr_sub_return_post, k73Frame, regsAt_cons, regsAt_nil,
      k73Saved, sepConj_emp_right', k73_decr_sub_bytes]
    xperm_cert_eq
  have hp1 : (((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ Expected) **
        (.x12 ↦ᵣ Expected) **
        bytesRegion Expected
          (k73_decr_sub_bytes parentBytes (target - gasUsed) target outWin) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwns u256SubBeInPlaceScratch **
        bytesRegion parentPtr parentBytes **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
          (k73_decr_img1 parentBytes (target - gasUsed)) **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) s) :=
    hEq1 ▸ hp
  -- Lifts: x10, x11, x12 (positions 2, 3, 4 under the x2 head).
  have hc10 := decr_under_id (B := (.x2 ↦ᵣ wspH))
    (decr_sep_pin_lift (r := Reg.x10) (v := (0 : Word))) s hp1
  have hc11 := decr_under_id (B := (.x2 ↦ᵣ wspH))
    (decr_under_id (B := regOwn .x10)
      (decr_sep_pin_lift (r := Reg.x11) (v := Expected))) s hc10
  have hc12 := decr_under_id (B := (.x2 ↦ᵣ wspH))
    (decr_under_id (B := regOwn .x10)
      (decr_under_id (B := regOwn .x11)
        (decr_sep_pin_lift (r := Reg.x12) (v := Expected)))) s hc11
  -- Window content cast: the subtract's bytes are the spec's written image.
  have hcbr := decr_under_id (B := (.x2 ↦ᵣ wspH))
    (decr_under_id (B := regOwn .x10)
      (decr_under_id (B := regOwn .x11)
        (decr_under_id (B := regOwn .x12)
          (decr_br_cast hcast)))) s hc12
  -- Finale: permutation into the unfolded `k73PostOwn` spelling.
  have hEq2 :
      ((.x2 ↦ᵣ wspH) ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
        bytesRegion Expected (hvbfWrittenImage gasLimit gasUsed parentBytes) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwns u256SubBeInPlaceScratch **
        bytesRegion parentPtr parentBytes **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
          (k73_decr_img1 parentBytes (target - gasUsed)) **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) =
      (((.x1 ↦ᵣ (H + 40)) ** k73PostOwn wspH wspK headerPtr v9 old18 target
        v19 v20 gasUsed parentPtr parentBytes
        (hvbfWrittenImage gasLimit gasUsed parentBytes) headerBytes
        (H + 40) old8
        (regOwns u256SubBeInPlaceScratch **
          EvmAsm.Codegen.U256MulU64Be.frameSlots
            (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
            parentPtr Expected target (target - gasUsed) (0 : Word) **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
            (k73_decr_img1 parentBytes (target - gasUsed)) **
          regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
          regOwn .x20 ** Frest))) := by
    dsimp only [k73PostOwn, tailRest, tailRestCore, k73_decr_piggyback]
    xperm_cert_eq
  exact hEq2 ▸ hcbr


/-- Borrow-failure junction cast: the borrow-taken exit (routed through the
    shared failure epilogue, status `1`) yields the Route-B failure arm with
    the subtract's written bytes as the scratch image. -/
private theorem k73_decr_sub_return_routeB_fail
    (wspH wspK headerPtr parentPtr v9 old18 v19 v20 _gasLimit gasUsed target : Word)
    (parentBytes outWin headerBytes : List (BitVec 8)) (Frest : Assertion) :
    ∀ s : PartialState,
      (k73_decr_sub_return_post wspH wspK (H + 40) target parentPtr Expected
        gasUsed headerPtr v9 old18 v19 v20 parentBytes outWin
        (k73_decr_piggyback wspH old8 headerPtr headerBytes Frest)
        (1 : Word)) s →
      (((.x1 ↦ᵣ (H + 40)) ** (fun u => ∃ (status : Word)
        (scratchBytes : List (BitVec 8)),
        status ≠ (0 : Word) ∧
        k73FailurePost wspH wspK headerPtr v9 old18 target v19 v20 gasUsed
          parentPtr status parentBytes scratchBytes headerBytes
          (H + 40) old8
          (regOwns u256SubBeInPlaceScratch **
            EvmAsm.Codegen.U256MulU64Be.frameSlots
              (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
              parentPtr Expected target (target - gasUsed) (0 : Word) **
            bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
              (k73_decr_img1 parentBytes (target - gasUsed)) **
            regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
            regOwn .x20 ** Frest) u)) s) := by
  intro s hp
  have hEq1 : (k73_decr_sub_return_post wspH wspK (H + 40) target parentPtr Expected
      gasUsed headerPtr v9 old18 v19 v20 parentBytes outWin
      (k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) (1 : Word)) =
      ((.x2 ↦ᵣ wspH) ** (.x11 ↦ᵣ Expected) ** (.x12 ↦ᵣ Expected) **
        bytesRegion Expected
          (k73_decr_sub_bytes parentBytes (target - gasUsed) target outWin) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns u256SubBeInPlaceScratch **
        bytesRegion parentPtr parentBytes **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
          (k73_decr_img1 parentBytes (target - gasUsed)) **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) := by
    simp only [k73_decr_sub_return_post, k73Frame, regsAt_cons, regsAt_nil,
      k73Saved, sepConj_emp_right', k73_decr_sub_bytes]
    xperm_cert_eq
  have hp1 : (((.x2 ↦ᵣ wspH) ** (.x11 ↦ᵣ Expected) ** (.x12 ↦ᵣ Expected) **
        bytesRegion Expected
          (k73_decr_sub_bytes parentBytes (target - gasUsed) target outWin) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns u256SubBeInPlaceScratch **
        bytesRegion parentPtr parentBytes **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
          (k73_decr_img1 parentBytes (target - gasUsed)) **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) s) :=
    hEq1 ▸ hp
  have hc11 := decr_under_id (B := (.x2 ↦ᵣ wspH))
    (decr_sep_pin_lift (r := Reg.x11) (v := Expected)) s hp1
  have hc12 := decr_under_id (B := (.x2 ↦ᵣ wspH))
    (decr_under_id (B := regOwn .x11)
      (decr_sep_pin_lift (r := Reg.x12) (v := Expected))) s hc11
  have hEq2 :
      ((.x2 ↦ᵣ wspH) ** regOwn .x11 ** regOwn .x12 **
        bytesRegion Expected
          (k73_decr_sub_bytes parentBytes (target - gasUsed) target outWin) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns u256SubBeInPlaceScratch **
        bytesRegion parentPtr parentBytes **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
          (k73_decr_img1 parentBytes (target - gasUsed)) **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) =
      (((.x1 ↦ᵣ (H + 40)) ** k73FailurePost wspH wspK headerPtr v9 old18 target
        v19 v20 gasUsed parentPtr (1 : Word) parentBytes
        (k73_decr_sub_bytes parentBytes (target - gasUsed) target outWin)
        headerBytes (H + 40) old8
        (regOwns u256SubBeInPlaceScratch **
          EvmAsm.Codegen.U256MulU64Be.frameSlots
            (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
            parentPtr Expected target (target - gasUsed) (0 : Word) **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
            (k73_decr_img1 parentBytes (target - gasUsed)) **
          regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
          regOwn .x20 ** Frest))) := by
    dsimp only [k73FailurePost, tailRest, tailRestScratch, tailRestCore,
      k73_decr_piggyback]
    xperm_cert_eq
  obtain ⟨sa, sb, had, hud, hx1, hFP⟩ := hEq2 ▸ hc12
  exact ⟨sa, sb, had, hud, hx1, ⟨(1 : Word),
    k73_decr_sub_bytes parentBytes (target - gasUsed) target outWin, by decide,
    hFP⟩⟩


/-- Multiply-overflow failure junction cast: the mul-status taken exit
    (routed through the shared failure epilogue, status `1`) yields the
    Route-B failure arm with the multiply's output image as the scratch
    bytes; the overflow window's existential index is fixed and its window
    atoms join the absorbed junk. -/
private theorem k73_decr_mulfail_routeB_fail
    (wspH wspK headerPtr parentPtr v9 old18 v19 v20 _gasLimit gasUsed target : Word)
    (parentBytes outWin headerBytes : List (BitVec 8)) (Frest : Assertion) :
    ∀ s : PartialState,
      (k73_decr_mulfail_taken_post wspH wspK (H + 40) target parentPtr Expected
        gasUsed headerPtr v9 old18 v19 v20 parentBytes outWin
        (k73_decr_piggyback wspH old8 headerPtr headerBytes Frest)) s →
      (((.x1 ↦ᵣ (H + 40)) ** (fun u => ∃ (status : Word)
        (scratchBytes : List (BitVec 8)) (k : Nat),
        status ≠ (0 : Word) ∧
        k73FailurePost wspH wspK headerPtr v9 old18 target v19 v20 gasUsed
          parentPtr status parentBytes scratchBytes headerBytes
          (H + 40) old8
          (EvmAsm.Codegen.U256MulU64Be.frameSlots
              (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
              parentPtr Expected target (target - gasUsed) (0 : Word) **
            k73MulOverflowCoreNoStatus
              (k73_decr_img1 parentBytes (target - gasUsed)) k **
            regOwn .x13 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 **
            regOwn .x19 ** regOwn .x20 ** regOwn .x14 ** regOwn .x15 **
            regOwn .x16 ** regOwn .x17 ** Frest) u)) s) := by
  intro s hp
  have hEq1 : (k73_decr_mulfail_taken_post wspH wspK (H + 40) target parentPtr
      Expected gasUsed headerPtr v9 old18 v19 v20 parentBytes outWin
      (k73_decr_piggyback wspH old8 headerPtr headerBytes Frest)) =
      ((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        k73_decr_mulfail_win wspK (target - gasUsed) target parentPtr Expected
          parentBytes outWin **
        EvmAsm.Codegen.U256MulU64Be.mulTailExtra parentPtr (target - gasUsed)
          Expected parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) := by
    simp only [k73_decr_mulfail_taken_post, k73Frame, regsAt_cons, regsAt_nil,
      k73Saved, sepConj_emp_right', k73_decr_mulfail_junk, k73_decr_ghole,
      EvmAsm.Codegen.U256MulU64Be.mulTailExtra]
    xperm_cert_eq
  have hp1 : (((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        k73_decr_mulfail_win wspK (target - gasUsed) target parentPtr Expected
          parentBytes outWin **
        EvmAsm.Codegen.U256MulU64Be.mulTailExtra parentPtr (target - gasUsed)
          Expected parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) s) :=
    hEq1 ▸ hp
  -- Fix the overflow window's existential index.
  have hp2 : (((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        (fun u => ∃ k,
          (U256MulU64Be.frameSlots
              (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
              parentPtr Expected target (target - gasUsed) (0 : Word) **
            bytesRegion Expected
              (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
            k73MulOverflowCoreNoStatus
              (k73_decr_img1 parentBytes (target - gasUsed)) k) u) **
        EvmAsm.Codegen.U256MulU64Be.mulTailExtra parentPtr (target - gasUsed)
          Expected parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) s) := hp1
  -- Rotate the existential window to the front, then crack it in one step.
  have hrot : ((        (.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        (fun u => ∃ k,
          (U256MulU64Be.frameSlots
              (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
              parentPtr Expected target (target - gasUsed) (0 : Word) **
            bytesRegion Expected
              (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
            k73MulOverflowCoreNoStatus
              (k73_decr_img1 parentBytes (target - gasUsed)) k) u) **
        EvmAsm.Codegen.U256MulU64Be.mulTailExtra parentPtr (target - gasUsed)
          Expected parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) =
      ((fun u => ∃ k,
          (U256MulU64Be.frameSlots
              (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
              parentPtr Expected target (target - gasUsed) (0 : Word) **
            bytesRegion Expected
              (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
            k73MulOverflowCoreNoStatus
              (k73_decr_img1 parentBytes (target - gasUsed)) k) u) **
        (        (.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        EvmAsm.Codegen.U256MulU64Be.mulTailExtra parentPtr (target - gasUsed)
          Expected parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest))) := by
    xperm_cert_eq
  obtain ⟨k, hk⟩ := (sepConj_exists_left s).mp (hrot ▸ hp2)
  -- Bridge the folded mulTailExtra token to its expanded atoms.
  have hE : ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
        parentPtr Expected target (target - gasUsed) (0 : Word) **
      bytesRegion Expected (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
      k73MulOverflowCoreNoStatus
        (k73_decr_img1 parentBytes (target - gasUsed)) k) **
      (.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      frameSlotsSaved k73Frame wspK
        (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
      EvmAsm.Codegen.U256MulU64Be.mulTailExtra parentPtr (target - gasUsed)
        Expected parentBytes **
      regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) =
      (U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
        parentPtr Expected target (target - gasUsed) (0 : Word) **
      bytesRegion Expected (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
      k73MulOverflowCoreNoStatus
        (k73_decr_img1 parentBytes (target - gasUsed)) k **
      (.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      frameSlotsSaved k73Frame wspK
        (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
      bytesRegion parentPtr parentBytes **
      (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (target - gasUsed)) **
      (.x12 ↦ᵣ Expected) ** regOwn .x13 ** regOwn .x29 ** regOwn .x30 **
      regOwn .x31 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
      regOwn .x20 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) := by
    dsimp only [EvmAsm.Codegen.U256MulU64Be.mulTailExtra]
    xperm_cert_eq
  have hkEq : ((        U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion Expected (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
        k73MulOverflowCoreNoStatus
          (k73_decr_img1 parentBytes (target - gasUsed)) k **
                (.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        bytesRegion parentPtr parentBytes **
        (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (target - gasUsed)) **
        (.x12 ↦ᵣ Expected) ** regOwn .x13 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) =
      ((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion Expected (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
        k73MulOverflowCoreNoStatus
          (k73_decr_img1 parentBytes (target - gasUsed)) k **
        (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (target - gasUsed)) **
        (.x12 ↦ᵣ Expected) ** regOwn .x13 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** bytesRegion parentPtr parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest)) := by
    xperm_cert_eq
  have hk0X := by
    have hk' := hk
    rw [hE] at hk'
    exact hk'
  have hk0 : (((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion Expected (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
        k73MulOverflowCoreNoStatus
          (k73_decr_img1 parentBytes (target - gasUsed)) k **
        (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (target - gasUsed)) **
        (.x12 ↦ᵣ Expected) ** regOwn .x13 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** bytesRegion parentPtr parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) s)  := by
    have hx := hk0X
    rw [hkEq] at hx
    exact hx
  have hEqR : ((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion Expected (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
        k73MulOverflowCoreNoStatus
          (k73_decr_img1 parentBytes (target - gasUsed)) k **
        (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (target - gasUsed)) **
        (.x12 ↦ᵣ Expected) ** regOwn .x13 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** bytesRegion parentPtr parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) =
      ((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (target - gasUsed)) **
        (.x12 ↦ᵣ Expected) **
        U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion Expected (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
        k73MulOverflowCoreNoStatus
          (k73_decr_img1 parentBytes (target - gasUsed)) k **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        regOwn .x13 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        bytesRegion parentPtr parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) := by
    xperm_cert_eq
  have hk1 : (((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (target - gasUsed)) **
        (.x12 ↦ᵣ Expected) **
        U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion Expected (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
        k73MulOverflowCoreNoStatus
          (k73_decr_img1 parentBytes (target - gasUsed)) k **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        regOwn .x13 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        bytesRegion parentPtr parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) s) :=
    hEqR ▸ hk0
  have hc7 := decr_under_id (B := (.x2 ↦ᵣ wspH))
    (decr_under_id (B := (.x10 ↦ᵣ 1))
      (decr_under_id (B := (.x0 ↦ᵣ (0 : Word)))
        (decr_sep_pin_lift (r := Reg.x7) (v := (0 : Word))))) s hk1
  have hc11 := decr_under_id (B := (.x2 ↦ᵣ wspH))
    (decr_under_id (B := (.x10 ↦ᵣ 1))
      (decr_under_id (B := (.x0 ↦ᵣ (0 : Word)))
        (decr_under_id (B := regOwn .x7)
          (decr_sep_pin_lift (r := Reg.x11) (v := (target - gasUsed)))))) s hc7
  have hc12 := decr_under_id (B := (.x2 ↦ᵣ wspH))
    (decr_under_id (B := (.x10 ↦ᵣ 1))
      (decr_under_id (B := (.x0 ↦ᵣ (0 : Word)))
        (decr_under_id (B := regOwn .x7)
          (decr_under_id (B := regOwn .x11)
            (decr_sep_pin_lift (r := Reg.x12) (v := Expected)))))) s hc11
  have hEq2 :
      ((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 **
        U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion Expected (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
        k73MulOverflowCoreNoStatus
          (k73_decr_img1 parentBytes (target - gasUsed)) k **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        regOwn .x13 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        bytesRegion parentPtr parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) =
      (((.x1 ↦ᵣ (H + 40)) ** k73FailurePost wspH wspK headerPtr v9 old18 target
        v19 v20 gasUsed parentPtr (1 : Word) parentBytes
        (k73_decr_img2 parentBytes (target - gasUsed) outWin) headerBytes
        (H + 40) old8
        (U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        k73MulOverflowCoreNoStatus
          (k73_decr_img1 parentBytes (target - gasUsed)) k **
        regOwn .x13 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** Frest))) := by
    dsimp only [k73FailurePost, tailRest, tailRestScratch, tailRestCore,
      k73_decr_piggyback]
    xperm_cert_eq
  obtain ⟨sa, sb, had, hud, hx1, hFP⟩ := hEq2 ▸ hc12
  exact ⟨sa, sb, had, hud, hx1, ⟨(1 : Word),
    k73_decr_img2 parentBytes (target - gasUsed) outWin, k, by decide,
    hFP⟩⟩


/- ## Wrapper-vocabulary Route-B adapter for the decrease route (#12346 residual 2b)

The three machine exits (multiply-overflow failure, borrow failure, success)
are folded into the single `k73RouteBCallPost` disjunction whose `F` slot is
`k73_decr_outj`: the junk every decrease exit genuinely leaves behind (the
subtract/multiply scratch-register ownerships, the multiply scratch frame, the
accumulator image) and the caller's ambient `F`.  The multiply-overflow arm's
proof-artifact step index `k` is eliminated because `k73MulOverflowCoreNoStatus`
pins `x5`/`x6` to `k`-dependent *values*; lifting those pins to ownership
(`regIs_implies_regOwn`) makes the arm `k`-free and lands exactly on the
`regOwns u256SubBeInPlaceScratch` the unified junk demands. -/

/-- The wrapper-world atoms the decrease machine route consumes at entry but
    the wrapper premise (`k73PreRest`) supplies beyond its fixed atoms. -/
private def k73_decr_env (wspK : Word) (f0 f1 f2 f3 f4 f5 : Word)
    (accWin : List (BitVec 8)) (F : Assertion) : Assertion :=
  regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
    EvmAsm.Codegen.U256MulU64Be.frameSlots
      (wspK + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
    bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accWin **
    regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
    regOwn .x13 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** F

/-- The unified decrease-route junk: every exit leaves these atoms behind and
    nothing more; the caller's ambient `F` rides at the tail. -/
private def k73_decr_outj (wspK _headerPtr parentPtr _v9 _old18 _v19 _v20 gasUsed
    target : Word) (parentBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  regOwns u256SubBeInPlaceScratch **
    EvmAsm.Codegen.U256MulU64Be.frameSlots
      (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
      parentPtr Expected target (target - gasUsed) (0 : Word) **
    bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
      (k73_decr_img1 parentBytes (target - gasUsed)) **
    regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 ** F

/-- A two-way branch whose taken and fall exits are the *same* point (both
    legs have already returned) is a triple with disjunctive post. -/
private theorem k73_decr_branch_to_triple {n : Nat} {entry pt : Word}
    {cr : CodeReq} {P Qt Qf : Assertion}
    (h : cpsBranchWithin n entry cr P pt Qt pt Qf) :
    cpsTripleWithin n entry pt cr P (fun s => Qt s ∨ Qf s) := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hbranch⟩ := h R hR s hcr hPR hpc
  refine ⟨k, hk, s', hstep, ?_⟩
  rcases hbranch with ⟨hpc', hQR⟩ | ⟨hpc', hQR⟩
  · obtain ⟨hst, hcomp, hhold⟩ := hQR
    exact ⟨hpc', hst, hcomp, decr_or_left_lift _ hhold⟩
  · obtain ⟨hst, hcomp, hhold⟩ := hQR
    exact ⟨hpc', hst, hcomp, decr_or_right_lift _ hhold⟩

/-- The multiply-overflow failure arm carries a proof-artifact `k` (the
    overflow window's step index).  `k73MulOverflowCoreNoStatus` pins `x5` and
    `x6` to `k`-dependent values; lifting those pins to ownership makes the
    arm `k`-free with junk exactly `k73_decr_outj`'s body. -/
private theorem k73_decr_mulfail_arm_unify
    (wspH wspK headerPtr parentPtr v9 old18 v19 v20 _gasLimit gasUsed target : Word)
    (parentBytes _outWin headerBytes : List (BitVec 8)) (F : Assertion) :
    ∀ s : PartialState,
      ((.x1 ↦ᵣ (H + 40)) ** (fun u => ∃ (status : Word)
        (scratchBytes : List (BitVec 8)) (k : Nat),
        status ≠ (0 : Word) ∧
        k73FailurePost wspH wspK headerPtr v9 old18 target v19 v20 gasUsed
          parentPtr status parentBytes scratchBytes headerBytes
          (H + 40) old8
          (EvmAsm.Codegen.U256MulU64Be.frameSlots
              (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
              parentPtr Expected target (target - gasUsed) (0 : Word) **
            k73MulOverflowCoreNoStatus
              (k73_decr_img1 parentBytes (target - gasUsed)) k **
            regOwn .x13 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 **
            regOwn .x19 ** regOwn .x20 ** regOwn .x14 ** regOwn .x15 **
            regOwn .x16 ** regOwn .x17 ** F) u)) s →
      (((.x1 ↦ᵣ (H + 40)) ** (fun u => ∃ (status : Word)
        (scratchBytes : List (BitVec 8)),
        status ≠ (0 : Word) ∧
        k73FailurePost wspH wspK headerPtr v9 old18 target v19 v20 gasUsed
          parentPtr status parentBytes scratchBytes headerBytes
          (H + 40) old8
          (regOwns u256SubBeInPlaceScratch **
            EvmAsm.Codegen.U256MulU64Be.frameSlots
              (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
              parentPtr Expected target (target - gasUsed) (0 : Word) **
            bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
              (k73_decr_img1 parentBytes (target - gasUsed)) **
            regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
            regOwn .x20 ** F) u)) s) := by
  intro s hp
  obtain ⟨sa, sb, had, hud, hx1, harm⟩ := hp
  obtain ⟨st, scr, k, hne, hFP⟩ := harm
  refine ⟨sa, sb, had, hud, hx1, ⟨st, scr, hne, ?_⟩⟩
  dsimp only [k73FailurePost, tailRest, tailRestScratch, tailRestCore,
    k73MulOverflowCoreNoStatus] at hFP ⊢
  have hR : ∀ q : PartialState,
      ((EvmAsm.Codegen.U256MulU64Be.frameSlots
          (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        (((.x5 ↦ᵣ (EvmAsm.Codegen.U256MulU64Be.accBase +
              BitVec.ofNat 64 (32 + k))) **
          (.x6 ↦ᵣ BitVec.ofNat 64 (8 - k)) **
          regOwn .x28 **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
            (k73_decr_img1 parentBytes (target - gasUsed))) **
        (regOwn .x13 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 **
          regOwn .x19 ** regOwn .x20 ** regOwn .x14 ** regOwn .x15 **
          regOwn .x16 ** regOwn .x17 ** F))) q) →
      ((regOwns u256SubBeInPlaceScratch **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
          (k73_decr_img1 parentBytes (target - gasUsed)) **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
        regOwn .x20 ** F) q) := by
    intro q hq
    have t1 := decr_under_id
      (B := EvmAsm.Codegen.U256MulU64Be.frameSlots
        (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
        parentPtr Expected target (target - gasUsed) (0 : Word))
      (decr_sep_pair_congr
        (decr_sep_pin_lift (r := Reg.x5)
          (v := EvmAsm.Codegen.U256MulU64Be.accBase + BitVec.ofNat 64 (32 + k)))
        (fun _ h => h)) q hq
    have t2 := decr_under_id
      (B := EvmAsm.Codegen.U256MulU64Be.frameSlots
        (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
        parentPtr Expected target (target - gasUsed) (0 : Word))
      (decr_sep_pair_congr
        (decr_sep_pair_congr (fun _ h => h)
          (decr_sep_pin_lift (r := Reg.x6) (v := BitVec.ofNat 64 (8 - k))))
        (fun _ h => h)) q t1
    have hE : ((EvmAsm.Codegen.U256MulU64Be.frameSlots
          (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        ((regOwn .x5 ** (regOwn .x6 ** (regOwn .x28 **
            bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
              (k73_decr_img1 parentBytes (target - gasUsed))))) **
          (regOwn .x13 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 **
            regOwn .x19 ** regOwn .x20 ** regOwn .x14 ** regOwn .x15 **
            regOwn .x16 ** regOwn .x17 ** F))) =
        (regOwns u256SubBeInPlaceScratch **
          EvmAsm.Codegen.U256MulU64Be.frameSlots
            (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 92)
            parentPtr Expected target (target - gasUsed) (0 : Word) **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
            (k73_decr_img1 parentBytes (target - gasUsed)) **
          regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
          regOwn .x20 ** F)) := by
      simp only [u256SubBeInPlaceScratch, regOwns_cons, regOwns_nil,
        sepConj_emp_right']
      xperm_cert_eq
    exact hE ▸ t2

  have hc := decr_under_id (B := ((.x2 ↦ᵣ wspH))) (decr_under_id (B := ((.x8 ↦ᵣ headerPtr))) (decr_under_id (B := ((.x10 ↦ᵣ st))) (decr_under_id (B := (regOwn .x11)) (decr_under_id (B := ((.x0 ↦ᵣ (0 : Word)))) (decr_under_id (B := (frameSlotsSaved hvbfFrame wspH (hvbfSaved (H + 40) old8))) (decr_under_id (B := ((.x9 ↦ᵣ v9))) (decr_under_id (B := ((.x18 ↦ᵣ old18))) (decr_under_id (B := ((.x19 ↦ᵣ v19))) (decr_under_id (B := ((.x20 ↦ᵣ v20))) (decr_under_id (B := (regOwn .x12)) (decr_under_id (B := (regOwn .x13)) (decr_under_id (B := (regOwn .x5)) (decr_under_id (B := (regOwn .x6)) (decr_under_id (B := (regOwn .x7)) (decr_under_id (B := (regOwn .x28)) (decr_under_id (B := (regOwn .x29)) (decr_under_id (B := (regOwn .x30)) (decr_under_id (B := (regOwn .x31)) (decr_under_id (B := (frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20))) (decr_under_id (B := (bytesRegion headerPtr headerBytes)) (decr_under_id (B := (bytesRegion parentPtr parentBytes)) (decr_under_id (B := (bytesRegion Expected scr)) (hR))))))))))))))))))))))) sb hFP
  exact hc


/-- The whole nonzero-decrease route, assembled in the wrapper's vocabulary:
    from `k73PreRest` at the wrapper's stack frame to the Route-B callee post
    `k73RouteBCallPost`.  The success arm pins the expected buffer at
    `hvbfWrittenImage`; both failure flavours fold into the existential
    failure arm; the fixed exit junk rides in the trailing `F` slot as
    `k73_decr_outj`. -/
theorem k73_decr_route_adapter {cr : CodeReq}
    (spH spK old8 headerPtr gasLimit gasUsed parentPtr : Word)
    (v9 old18 v19 v20 : Word)
    (parentBytes expectedBytes headerBytes accWin : List (BitVec 8))
    (f0 f1 f2 f3 f4 f5 : Word) (F : Assertion)
    (hspK : spK = spH + signExtend12 (-56 : BitVec 12))
    (hne : gasUsed ≠ gasLimit >>> 1)
    (hnotlt : ¬ (gasLimit >>> 1).toNat < gasUsed.toNat)
    (hnonzero : gasUsed ≠ 0)
    (hret : ((H + 40 : Word) &&& ~~~(1 : Word)) = H + 40)
    (hF : F.pcFree)
    (htargetPos : 0 < (gasLimit >>> 1).toNat)
    (hleTarget : (gasLimit >>> 1).toNat ≤ 2 ^ 56)
    (hMulFit : EvmAsm.Stateless.SpecRef.bytesBEtoNat parentBytes *
      ((gasLimit >>> 1) - gasUsed).toNat < 2 ^ 256)
    (hlenP : parentBytes.length = 32)
    (hExpectedLen : expectedBytes.length = 32)
    (hlenAcc : accWin.length = 40)
    (halignA : parentPtr.toNat % 8 = 0)
    (hoverA : parentPtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ j, j < 32 →
      isValidByteAccess (parentPtr + BitVec.ofNat 64 j) = true)
    (halignOut : Expected.toNat % 8 = 0)
    (hoverOut : Expected.toNat + 32 < 2 ^ 64)
    (hvalidOut : ∀ j, j < 32 →
      isValidByteAccess (Expected + BitVec.ofNat 64 j) = true)
    (hdisj : parentPtr.toNat + 32 ≤ Expected.toNat ∨
      Expected.toNat + 32 ≤ parentPtr.toNat)
    (hrw : RwRegion.wf ⟨Expected, 32⟩)
    (hroBase : Region.wf ⟨parentPtr, parentBytes⟩)
    (hszDiv1 :
      4 * ((u256DivU64BeInPlaceFn Expected (gasLimit >>> 1)
        (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)).body.size + 1)
        ≤ 2 ^ 64)
    (hszDiv2 :
      4 * ((u256DivU64BeInPlaceFn Expected 8
        (u256DivU64BeQuotBytes
          (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
          (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
          (gasLimit >>> 1))).body.size
          + 1)
        ≤ 2 ^ 64)
    (hszSub :
      4 * ((u256SubBeInPlaceFn parentPtr Expected parentBytes
        (u256DivU64BeQuotBytes
          (u256DivU64BeQuotBytes
            (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
            (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
            (gasLimit >>> 1))
          (u256DivU64BeQuotBytes
            (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
            (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
            (gasLimit >>> 1))
          8)).body.size + 1)
        ≤ 2 ^ 64)
    (hk73Mono : ∀ a i, wholeCode a = some i → cr a = some i) :
    cpsTripleWithin
      ((20 + 3852 + 9) +
        (((((10 +
              (u256DivU64BeInPlaceFn Expected (gasLimit >>> 1)
                (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)).body.steps +
            (u256DivU64BeInPlaceFn Expected 8
              (u256DivU64BeQuotBytes
                (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
                (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
                (gasLimit >>> 1))).body.steps +
          1) +
          (1 + (5 + (u256SubBeInPlaceFn parentPtr Expected parentBytes
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes
                (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
                (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
                (gasLimit >>> 1))
              (u256DivU64BeQuotBytes
                (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
                (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
                (gasLimit >>> 1))
              8)).body.steps))) + 1) + 9) + 10))
      K73 (H + 40) cr
      ((.x1 ↦ᵣ (H + 40)) ** k73PreRest spH spK headerPtr v9 old18 v19 v20
        gasLimit gasUsed parentPtr parentBytes expectedBytes headerBytes
        (H + 40) old8
        (k73_decr_env spK f0 f1 f2 f3 f4 f5 accWin F))
      ((.x1 ↦ᵣ (H + 40)) ** k73RouteBCallPost spH spK (H + 40) old8 headerPtr
        v9 old18 (gasLimit >>> 1) v19 v20 gasUsed gasLimit parentPtr
        parentBytes headerBytes
        (k73_decr_outj spK headerPtr parentPtr v9 old18 v19 v20 gasUsed
          (gasLimit >>> 1) parentBytes F)) := by
  have hGenv : (k73_decr_piggyback spH old8 headerPtr headerBytes F).pcFree := by
    dsimp only [k73_decr_piggyback]
    pcf
    exact hF
  have ht2 : (gasLimit >>> 1).toNat = gasLimit.toNat / 2 := rfl
  have hne' : gasUsed.toNat ≠ (gasLimit >>> 1).toNat :=
    fun h => hne (BitVec.eq_of_toNat_eq h)
  have hdecr : gasUsed.toNat < gasLimit.toNat / 2 := by omega
  have halenA2 :
      ((k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)).length = 32 := by
    rw [k73_decr_img2]
    exact EvmAsm.Codegen.U256MulU64Be.copyState_len _ _ 32 hExpectedLen
  have hvalA2 :
      EvmAsm.Crypto.beBytesToNat (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
        = (EvmAsm.Crypto.beBytesToNat parentBytes *
            ((gasLimit >>> 1) - gasUsed).toNat) % 2 ^ 256 :=
    EvmAsm.Codegen.U256MulU64Be.beBytesToNat_mulOutput parentBytes expectedBytes ((gasLimit >>> 1) - gasUsed)
      hlenP hExpectedLen
  have hcast : k73_decr_sub_bytes parentBytes ((gasLimit >>> 1) - gasUsed)
      (gasLimit >>> 1) expectedBytes
      = hvbfWrittenImage gasLimit gasUsed parentBytes :=
    k73_decr_machine_bytes_eq_written rfl hdecr htargetPos hleTarget hlenP
      halenA2 hMulFit hvalA2
  have hw := k73_decrease_route_machine_spec_within spH spK (H + 40) gasLimit
    gasUsed (gasLimit >>> 1) parentPtr Expected headerPtr v9 old18 v19 v20
    f0 f1 f2 f3 f4 f5 parentBytes accWin expectedBytes
    (k73_decr_piggyback spH old8 headerPtr headerBytes F)
    hspK rfl hne hnotlt hnonzero hGenv hret hlenP hlenAcc hExpectedLen
    halignA hoverA hvalidA halignOut hoverOut hvalidOut htargetPos hdisj hrw
    hroBase hszDiv1 hszDiv2 hszSub
  have htri := k73_decr_branch_to_triple hw
  have htriC := cpsTripleWithin_extend_code hk73Mono htri
  have hpreEq :
      ((.x1 ↦ᵣ (H + 40)) ** k73PreRest spH spK headerPtr v9 old18 v19 v20
          gasLimit gasUsed parentPtr parentBytes expectedBytes headerBytes
          (H + 40) old8 (k73_decr_env spK f0 f1 f2 f3 f4 f5 accWin F)) =
      k73HeadPre spH spK (H + 40) gasLimit gasUsed parentPtr Expected
        headerPtr v9 old18 v19 v20 parentBytes expectedBytes
        (EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spK + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accWin **
        k73_decr_ghole spK
          (regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
            k73_decr_piggyback spH old8 headerPtr headerBytes F)) := by
    dsimp only [k73HeadPre, k73PreRest]
    dsimp only [k73_decr_env, k73_decr_ghole, k73_decr_piggyback]
    xperm
  refine cpsTripleWithin_weaken (fun s hp => hpreEq ▸ hp) (fun s hq => ?_) htriC
  rcases hq with hm | hs0
  · rcases hm with hm | hs1
    · have hM := k73_decr_mulfail_routeB_fail spH spK headerPtr parentPtr v9
        old18 v19 v20 gasLimit gasUsed (gasLimit >>> 1) parentBytes expectedBytes
        headerBytes F s hm
      have hMu := k73_decr_mulfail_arm_unify spH spK headerPtr parentPtr v9
        old18 v19 v20 gasLimit gasUsed (gasLimit >>> 1) parentBytes expectedBytes
        headerBytes F s hM
      obtain ⟨sa, sb, had, hud, hx1, harm⟩ := hMu
      exact ⟨sa, sb, had, hud, hx1, Or.inr harm⟩
    · have hB := k73_decr_sub_return_routeB_fail spH spK headerPtr parentPtr v9
        old18 v19 v20 gasLimit gasUsed (gasLimit >>> 1) parentBytes expectedBytes
        headerBytes F s hs1
      obtain ⟨sa, sb, had, hud, hx1, harm⟩ := hB
      exact ⟨sa, sb, had, hud, hx1, Or.inr harm⟩
  · have hS := k73_decr_sub_return_routeB_succ spH spK headerPtr parentPtr v9
      old18 v19 v20 gasLimit gasUsed (gasLimit >>> 1) parentBytes expectedBytes
      headerBytes F hcast s hs0
    obtain ⟨sa, sb, had, hud, hx1, hPO⟩ := hS
    exact ⟨sa, sb, had, hud, hx1, Or.inl hPO⟩


/-- CONSTRUCTED non-vacuity inhabitance of the decrease Route-B adapter
    (adopted standard for #12346: a finished route does not count until a
    closed-proposition witness exists - an unsatisfiable premise cannot admit
    a constructed witness, so this check catches the vacuity class by
    construction rather than by vigilance).  Concrete literals: the
    corollary-family stack pair `spH - spK = 56`, decrease guard family
    `gasLimit = 10000`, `gasUsed = 2500` (target `(10000 >>> 1) = 5000 >
    2500`, nonzero), zero scratch windows, empty ambience, `cr = wholeCode`.
    Discharged by direct application - no hypotheses, no sorry. -/
theorem k73_decr_route_adapter_inhabited :
    cpsTripleWithin
      ((20 + 3852 + 9) +
        (((((10 +
              (u256DivU64BeInPlaceFn Expected ((10000 : Word) >>> 1)
                (k73_decr_img2 (List.replicate 32 0) (((10000 : Word) >>> 1) - (2500 : Word)) (List.replicate 32 0))).body.steps +
            (u256DivU64BeInPlaceFn Expected 8
              (u256DivU64BeQuotBytes
                (k73_decr_img2 (List.replicate 32 0) (((10000 : Word) >>> 1) - (2500 : Word)) (List.replicate 32 0))
                (k73_decr_img2 (List.replicate 32 0) (((10000 : Word) >>> 1) - (2500 : Word)) (List.replicate 32 0))
                ((10000 : Word) >>> 1))).body.steps +
          1) +
          (1 + (5 + (u256SubBeInPlaceFn (0x200100 : Word) Expected (List.replicate 32 0)
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes
                (k73_decr_img2 (List.replicate 32 0) (((10000 : Word) >>> 1) - (2500 : Word)) (List.replicate 32 0))
                (k73_decr_img2 (List.replicate 32 0) (((10000 : Word) >>> 1) - (2500 : Word)) (List.replicate 32 0))
                ((10000 : Word) >>> 1))
              (u256DivU64BeQuotBytes
                (k73_decr_img2 (List.replicate 32 0) (((10000 : Word) >>> 1) - (2500 : Word)) (List.replicate 32 0))
                (k73_decr_img2 (List.replicate 32 0) (((10000 : Word) >>> 1) - (2500 : Word)) (List.replicate 32 0))
                ((10000 : Word) >>> 1))
              8)).body.steps))) + 1) + 9) + 10))
      K73 (H + 40) wholeCode
      ((.x1 ↦ᵣ (H + 40)) ** k73PreRest (0xa0050038 : Word) (0xa0050000 : Word) (0x200000 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        (10000 : Word) (2500 : Word) (0x200100 : Word) (List.replicate 32 0) (List.replicate 32 0) (List.replicate 32 0)
        (H + 40) (0 : Word)
        (k73_decr_env (0xa0050000 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (List.replicate 40 0) empAssertion))
      ((.x1 ↦ᵣ (H + 40)) ** k73RouteBCallPost (0xa0050038 : Word) (0xa0050000 : Word) (H + 40) (0 : Word) (0x200000 : Word)
        (0 : Word) (0 : Word) ((10000 : Word) >>> 1) (0 : Word) (0 : Word) (2500 : Word) (10000 : Word) (0x200100 : Word)
        (List.replicate 32 0) (List.replicate 32 0)
        (k73_decr_outj (0xa0050000 : Word) (0x200000 : Word) (0x200100 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (2500 : Word)
          ((10000 : Word) >>> 1) (List.replicate 32 0) empAssertion)) :=
  k73_decr_route_adapter (cr := wholeCode)
    (0xa0050038 : Word) (0xa0050000 : Word) (0 : Word) (0x200000 : Word)
    (10000 : Word) (2500 : Word) (0x200100 : Word)
    (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    (List.replicate 32 0) (List.replicate 32 0) (List.replicate 32 0)
    (List.replicate 40 0)
    (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    empAssertion
    (hspK := by decide)
    (hne := by decide)
    (hnotlt := by decide)
    (hnonzero := by decide)
    (hret := by unfold H; rfl)
    (hF := by pcf)
    (htargetPos := by decide)
    (hleTarget := by decide)
    (hMulFit := by decide)
    (hlenP := by simp)
    (hExpectedLen := by simp)
    (hlenAcc := by simp)
    (halignA := by decide)
    (hoverA := by decide)
    (hvalidA := by intro j _; interval_cases j <;> decide)
    (halignOut := by decide)
    (hoverOut := by decide)
    (hvalidOut := by intro j _; interval_cases j <;> decide)
    (hdisj := by decide)
    (hrw := by decide)
    (hroBase := by
      refine ⟨?_, ?_, ?_⟩
      · decide
      · decide
      · intro k hk
        have hk32 : k < 32 := by simpa using hk
        interval_cases k <;> decide)
    (hszDiv1 := by simp only [k73_decr_img2, u256DivU64BeInPlaceFn]; decide)
    (hszDiv2 := by simp only [k73_decr_img2, u256DivU64BeInPlaceFn]; decide)
    (hszSub := by simp only [k73_decr_img2, u256SubBeInPlaceFn]; decide)
    (fun _ _ h => h)

end EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute
