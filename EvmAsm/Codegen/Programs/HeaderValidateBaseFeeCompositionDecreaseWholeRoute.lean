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
  Decrease-route return assembly (#12346 item 2b).
-/

import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeEntry
import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeSpec
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeMulNativeContract
import EvmAsm.Codegen.Programs.U256MulU64Be.Arith
import EvmAsm.Codegen.Proofs.U256BeFlatTriples
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpecCore
import EvmAsm.Rv64.BitAux
import EvmAsm.Rv64.Tactics.XPermCert
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeCompositionDecreaseRoute

namespace EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec hiding K73
open EvmAsm.Codegen.HeaderValidateBaseFeeSpec
open EvmAsm.Codegen.U256DivU64BeSAsm
open EvmAsm.Codegen.U256SubBeSAsm
open EvmAsm.Codegen.HeaderValidateBaseFeeMulNativeContract

open EvmAsm.Codegen.U256MulU64Be in
/-- Entry composed into the multiply stage with the callee contract
discharged from the deployed flat whole-routine triple through the native
asymmetric shape (`k73_mul_status_branch_native_spec_within`): the scratch
windows are owned premises at `accWin` / `outWin`, the image lists thread
into both branch exits, and no new caller precondition appears. -/
theorem k73_decrease_entry_status_native_discharged
    (sp0 spH raIn gasLimit gasUsed target basePtr outPtr : Word)
    (v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accWin outWin : List (BitVec 8)) (G : Assertion)
    (hsp : spH = sp0 + signExtend12 (-56 : BitVec 12))
    (htarget : target = gasLimit >>> 1)
    (hne : gasUsed ≠ target)
    (hnotlt : ¬ target.toNat < gasUsed.toNat)
    (hnonzero : gasUsed ≠ 0)
    (hG : G.pcFree)
    (hlenA : baseBytes.length = 32)
    (hlenAcc : accWin.length = 40)
    (houtW : outWin.length = 32)
    (halignA : basePtr.toNat % 8 = 0)
    (hoverA : basePtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ j, j < 32 →
      isValidByteAccess (basePtr + BitVec.ofNat 64 j) = true)
    (halignOut : outPtr.toNat % 8 = 0)
    (hoverOut : outPtr.toNat + 32 < 2 ^ 64)
    (hvalidOut : ∀ j, j < 32 →
      isValidByteAccess (outPtr + BitVec.ofNat 64 j) = true) :
    cpsBranchWithin (20 + 3852) K73 wholeCode
      (k73HeadPre sp0 spH raIn gasLimit gasUsed basePtr outPtr
        v8 v9 v18 v19 v20 baseBytes outWin
        (EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accWin ** G))
      (K73 + 276)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73DecreaseMulCarryRest spH raIn basePtr outPtr target
            (target - gasUsed) v8 v9 v18 v19 v20 baseBytes
            (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes (target - gasUsed) 32)
            (EvmAsm.Codegen.U256MulU64Be.copyState
              (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes (target - gasUsed) 32)
              outWin 32) G **
          regOwn .x10)
      (K73 + 96)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73DecreaseMulCarryRest spH raIn basePtr outPtr target
            (target - gasUsed) v8 v9 v18 v19 v20 baseBytes
            (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes (target - gasUsed) 32)
            (EvmAsm.Codegen.U256MulU64Be.copyState
              (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes (target - gasUsed) 32)
              outWin 32) G **
          regOwn .x10) := by
  have hFamb :
      (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G).pcFree := by
    pcf
    exact hG
  have hretCall : ((K73 + 92 : Word) &&& ~~~(1 : Word)) = K73 + 92 :=
    EvmAsm.Rv64.BitAux.word_add_even_andn_one (by decide) (by decide)
  have hcallee := mulWhole_spec
    (F := frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G)
    hFamb baseBytes accWin outWin hlenA hlenAcc houtW
    spH (K73 + 92) basePtr outPtr target (target - gasUsed) (0 : Word)
    basePtr (target - gasUsed) outPtr outPtr
    f0 f1 f2 f3 f4 f5 halignA hoverA hvalidA halignOut hoverOut hvalidOut
    hretCall
  have htwin := k73_mul_status_branch_native_spec_within
    spH raIn target (target - gasUsed) basePtr outPtr v8 v9 v18 v19 v20
    f0 f1 f2 f3 f4 f5 baseBytes accWin outWin G hG hcallee
  have hFext :
      (EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accWin ** G).pcFree := by
    pcf
    exact hG
  have hentry := k73_decrease_nonzero_entry_to_mul_spec_within
    sp0 spH raIn gasLimit gasUsed target basePtr outPtr
    v8 v9 v18 v19 v20 baseBytes outWin
    (EvmAsm.Codegen.U256MulU64Be.frameSlots
      (spH + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
      bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accWin ** G)
    hsp htarget hne hnotlt hnonzero hFext
  exact cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by
      dsimp only [k73MulPreNoRa]
      sep_perm hp) hentry htwin

/-! `regsOwnAt k73Frame` written as the flat ownership chain (the fold's
    trailing unit is not a definitional equality, so callers bridge through
    this lemma instead of `rfl`). -/
private theorem k73_regsOwnAt_k73Frame_flat :
    regsOwnAt k73Frame =
      (regOwn .x1 ** regOwn .x8 ** regOwn .x9 **
        regOwn .x18 ** regOwn .x19 ** regOwn .x20) := by
  simp [k73Frame, regsOwnAt_cons, regsOwnAt_nil, sepConj_emp_right']

/-- Outer overflow failure returning to the caller: the multiply stage exit
    at K73 + 276 (multiply carry junk carried in `P`) runs the shared
    `li x10, 1` plus epilogue tail.  The source pins the registers the
    epilogue overwrites (`w8..w20` are the mid-body values the multiply left,
    supplied by the feeder window); the proof lifts them to ownerships since
    the tail machinery only needs to own what it rewrites.  Values reloaded
    from the frame land per `k73Saved`, and the junk `P` rides through
    untouched. -/
theorem k73_decrease_mulfail_outer_return_spec_within
    (sp0 spH raIn v8 v9 v18 v19 v20 w8 w9 w18 w19 w20 : Word) (P : Assertion)
    (hsp : spH + signExtend12 (56 : BitVec 12) = sp0)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hP : P.pcFree) :
    cpsTripleWithin 9 (K73 + 276) raIn wholeCode
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 92)) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ w8) ** (.x9 ↦ᵣ w9) ** (.x18 ↦ᵣ w18) **
        (.x19 ↦ᵣ w19) ** (.x20 ↦ᵣ w20) ** regOwn .x10 ** P)
      ((.x2 ↦ᵣ sp0) ** regsAt k73Frame (k73Saved raIn v8 v9 v18 v19 v20) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) ** P) := by
  have hsavedU : (k73Saved raIn v8 v9 v18 v19 v20) .x1 = raIn := rfl
  have hPi : (((.x0 : Reg) ↦ᵣ (0 : Word)) ** P).pcFree := by
    pcf
    exact hP
  have ht := k73_failure_tail_spec_within sp0 spH raIn
    (k73Saved raIn v8 v9 v18 v19 v20) ((.x0 ↦ᵣ (0 : Word)) ** P)
    hsp hret hsavedU hPi
  -- Flat spelling of the shared failure-tail premise.
  have htFlat :
      cpsTripleWithin 9 (K73 + 276) raIn wholeCode
        ((.x2 ↦ᵣ spH) ** (regOwn .x1 ** regOwn .x8 ** regOwn .x9 **
            regOwn .x18 ** regOwn .x19 ** regOwn .x20) **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          regOwn .x10 ** (.x0 ↦ᵣ (0 : Word)) ** P)
        ((.x2 ↦ᵣ sp0) ** regsAt k73Frame (k73Saved raIn v8 v9 v18 v19 v20) **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) ** P) :=
    cpsTripleWithin_weaken
      (fun _ hp => by
        rw [k73_regsOwnAt_k73Frame_flat]
        xperm_hyp hp)
      (fun _ hq => hq) ht
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun _ hq => hq) htFlat
  -- Lift the incoming pins to the ownerships the tail machinery consumes,
  -- deepest first (each tower descends the chain heads to its pin).
  have c20 :
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 92)) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ w8) ** (.x9 ↦ᵣ w9) ** (.x18 ↦ᵣ w18) **
        (.x19 ↦ᵣ w19) ** regOwn .x20 ** regOwn .x10 ** P) s :=
    decr_under_id (decr_under_id (decr_under_id (decr_under_id (decr_under_id
      (decr_under_id (decr_under_id (decr_under_id
        (decr_sep_pin_lift (r := Reg.x20) (v := w20))))))))) s hp
  have c19 :
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 92)) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ w8) ** (.x9 ↦ᵣ w9) ** (.x18 ↦ᵣ w18) **
        regOwn .x19 ** regOwn .x20 ** regOwn .x10 ** P) s :=
    decr_under_id (decr_under_id (decr_under_id (decr_under_id (decr_under_id
      (decr_under_id (decr_under_id
        (decr_sep_pin_lift (r := Reg.x19) (v := w19)))))))) s c20
  have c18 :
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 92)) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ w8) ** (.x9 ↦ᵣ w9) **
        regOwn .x18 ** regOwn .x19 ** regOwn .x20 ** regOwn .x10 ** P) s :=
    decr_under_id (decr_under_id (decr_under_id (decr_under_id (decr_under_id
      (decr_under_id
        (decr_sep_pin_lift (r := Reg.x18) (v := w18))))))) s c19
  have c9 :
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 92)) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ w8) ** regOwn .x9 ** regOwn .x18 **
        regOwn .x19 ** regOwn .x20 ** regOwn .x10 ** P) s :=
    decr_under_id (decr_under_id (decr_under_id (decr_under_id (decr_under_id
      (decr_sep_pin_lift (r := Reg.x9) (v := w9)))))) s c18
  have c8 :
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 92)) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x2 ↦ᵣ spH) ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 **
        regOwn .x19 ** regOwn .x20 ** regOwn .x10 ** P) s :=
    decr_under_id (decr_under_id (decr_under_id (decr_under_id
      (decr_sep_pin_lift (r := Reg.x8) (v := w8))))) s c9
  -- Regroup with the link-register pin at the head ...
  have egrpa :
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 92)) **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          (.x2 ↦ᵣ spH) ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 **
          regOwn .x19 ** regOwn .x20 ** regOwn .x10 ** P)) =
      (((.x1 ↦ᵣ (K73 + 92)) ** ((.x2 ↦ᵣ spH) **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
          regOwn .x20 ** regOwn .x10 ** (.x0 ↦ᵣ (0 : Word)) ** P))) := by
    xperm_cert_eq
  have hx1 : ((.x1 ↦ᵣ (K73 + 92)) ** ((.x2 ↦ᵣ spH) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
      regOwn .x20 ** regOwn .x10 ** (.x0 ↦ᵣ (0 : Word)) ** P)) s := egrpa ▸ c8
  -- ... lift the pin to an ownership (the value is dead: the epilogue
  -- reloads `x1` from the saved slot, and `hsavedU` pins that to `raIn`) ...
  have hl : (regOwn .x1 ** ((.x2 ↦ᵣ spH) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
      regOwn .x20 ** regOwn .x10 ** (.x0 ↦ᵣ (0 : Word)) ** P)) s :=
    decr_sep_pin_lift _ hx1
  -- ... and finish by pure permutation against the flat tail premise.
  exact (by xperm_cert_eq :
    ((regOwn .x1 ** ((.x2 ↦ᵣ spH) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
      regOwn .x20 ** regOwn .x10 ** (.x0 ↦ᵣ (0 : Word)) ** P))) =
    (((.x2 ↦ᵣ spH) ** (regOwn .x1 ** regOwn .x8 ** regOwn .x9 **
        regOwn .x18 ** regOwn .x19 ** regOwn .x20) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      regOwn .x10 ** (.x0 ↦ᵣ (0 : Word)) ** P))) ▸ hl

/-- An existential projection never owns the program counter when no
    instance does: eliminate the binder on the holding state and reuse the
    witness-level fact.  Stated over the bare `∀` form because generalized
    field notation on a lambda head resolves `pcFree` against `Function`,
    not `Assertion`. -/
private theorem k73_pcFree_exists {A : Nat → Assertion}
    (hW : ∀ k, (A k).pcFree) :
    ∀ h, ((fun s => ∃ k, (A k) s : Assertion) h) → h.pc = none := by
  intro h hs
  obtain ⟨k, hk⟩ := hs
  exact hW k h hk

/-- Computed multiply accumulator image on the decrease arm (40 bytes). -/
def k73_decr_img1 (baseBytes : List (BitVec 8)) (delta : Word) :
    List (BitVec 8) :=
  EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32

/-- Computed multiply output image on the decrease arm: the low 32 bytes of
    the accumulator copied over the initial window; independent of that
    window's content. -/
def k73_decr_img2 (baseBytes : List (BitVec 8)) (delta : Word)
    (outWin : List (BitVec 8)) : List (BitVec 8) :=
  EvmAsm.Codegen.U256MulU64Be.copyState (k73_decr_img1 baseBytes delta)
    outWin 32

/-- The whole-route ambient envelope for this arm: the wrapper-world
    register ownerships that the carry rest does not already speak about,
    kept as one opaque token so permutation certificates match.  Deliberately
    pin-free: at K73 entry the machine stack pointer is `sp0` (`k73HeadPre`
    pins `.x2 ↦ sp0`), and at every return the shared epilogue rewrites it to
    `sp0`; a `x2` claim here would make the premise unsatisfiable.  The
    mid-body `.x2 ↦ spH` fact is extracted from the multiply epilogue window
    by `k73_decr_mulfail_twinfeed` instead. -/
def k73_decr_ghole (_spH : Word) (G : Assertion) : Assertion :=
  regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 ** G

/-- Memory-visible leftovers of any multiply-stage outcome: the scratch-frame
    dwords, the output window, and the overflow core (whose `x5/x6/x28`
    claims persist - the shared epilogue loads only `x1, x8..x20` and
    rewrites `x2`).  Deliberately free of the multiply epilogue's `.x2` pin
    and of its `x8..x20` pins: the epilogue reloads those registers from the
    frame, so mid-body register claims must not survive into exit junk. -/
def k73_decr_mulfail_win (spH deltaV target basePtr outPtr : Word)
    (baseBytes outWin : List (BitVec 8)) : Assertion :=
  fun s => ∃ k,
    (U256MulU64Be.frameSlots (spH + signExtend12 (-48 : BitVec 12)) (K73 + 92)
        basePtr outPtr target deltaV (0 : Word) **
      bytesRegion outPtr (k73_decr_img2 baseBytes deltaV outWin) **
      k73MulOverflowCoreNoStatus (k73_decr_img1 baseBytes deltaV) k) s

/-- The ambient junk carried through the outer failure leg: tail extras,
    overflow window, caller ambience. -/
def k73_decr_mulfail_junk (spH deltaV target basePtr outPtr : Word)
    (baseBytes outWin : List (BitVec 8)) (Grest : Assertion) : Assertion :=
  EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr deltaV outPtr baseBytes **
    k73_decr_mulfail_win spH deltaV target basePtr outPtr baseBytes outWin **
    Grest

/-- Feed the mul-stage carry exit into the shared failure epilogue.  The
    mid-body `.x2 ↦ spH` fact rides INSIDE the multiply epilogue window (its
    `spNew + signExtend12 48` value reduces to `spH`); the epilogue's other
    register claims pass through as pins over the feeder values; and only the
    memory-visible leftovers survive as junk (`k73_decr_mulfail_win`), since
    the shared epilogue reloads the callee-saved registers from the frame and
    rewrites `x2` to `sp0`. -/
private theorem k73_decr_mulfail_twinfeed
    (spH raIn basePtr outPtr target deltaV v8 v9 v18 v19 v20 : Word)
    (baseBytes outWin : List (BitVec 8)) (Grest : Assertion) :
    ∀ s : PartialState,
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73DecreaseMulCarryRest spH raIn basePtr outPtr target deltaV
          v8 v9 v18 v19 v20 baseBytes
          (k73_decr_img1 baseBytes deltaV)
          (k73_decr_img2 baseBytes deltaV outWin)
          (k73_decr_ghole spH Grest) ** regOwn .x10) s →
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 92)) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
        (.x18 ↦ᵣ target) ** (.x19 ↦ᵣ deltaV) ** (.x20 ↦ᵣ (0 : Word)) **
        regOwn .x10 **
        (U256MulU64Be.mulTailExtra basePtr deltaV outPtr baseBytes **
          k73_decr_mulfail_win spH deltaV target basePtr outPtr
            baseBytes outWin **
          (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
            regOwn .x20 ** Grest))) s := by
  have hsp48 :
      (spH + signExtend12 (-48 : BitVec 12)) + signExtend12 (48 : BitVec 12) =
        spH := by
    have h1 : signExtend12 (-48 : BitVec 12) =
        (18446744073709551568 : Word) := by decide
    have h2 : signExtend12 (48 : BitVec 12) = (48 : Word) := by decide
    rw [h1, h2]
    bv_omega
  intro s hp
  -- Flatten the carry rest (the ghole token unfolds to plain ownerships);
  -- the image tokens stay folded so every later spelling matches.
  dsimp only [k73DecreaseMulCarryRest, k73_decr_ghole] at hp
  -- Pull the existential window out of the chain.
  have hpW :
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 92)) **
            frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
            U256MulU64Be.mulTailExtra basePtr deltaV outPtr baseBytes) **
          ((fun u => ∃ k,
              (k73MulEpilogueNoRa (spH + signExtend12 (-48 : BitVec 12))
                  (K73 + 92) basePtr outPtr target deltaV (0 : Word) **
                bytesRegion outPtr (k73_decr_img2 baseBytes deltaV outWin) **
                k73MulOverflowCoreNoStatus
                  (k73_decr_img1 baseBytes deltaV) k) u) **
            (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
              regOwn .x20 ** Grest ** regOwn .x10))) s := by
    xperm_hyp hp
  have hpE :
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 92)) **
            frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
            U256MulU64Be.mulTailExtra basePtr deltaV outPtr baseBytes) **
          ((fun u =>
              ∃ k,
                ((k73MulEpilogueNoRa (spH + signExtend12 (-48 : BitVec 12))
                      (K73 + 92) basePtr outPtr target deltaV (0 : Word) **
                    bytesRegion outPtr
                      (k73_decr_img2 baseBytes deltaV outWin) **
                    k73MulOverflowCoreNoStatus
                      (k73_decr_img1 baseBytes deltaV) k) **
                  (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
                    regOwn .x20 ** Grest ** regOwn .x10)) u))) s :=
    sepConj_mono_right
      (fun h' hq => (sepConj_exists_left h').mp hq) s hpW
  obtain ⟨k, hk⟩ := sepConj_exists_right s hpE
  -- Reduce the epilogue's `x2` pin value to `spH`.
  dsimp only [k73MulEpilogueNoRa] at hk
  rw [hsp48] at hk
  -- Regroup once: the fixed-`k` memory window moves into the junk slot where
  -- the existential re-wrap happens (every later split stays inside the
  -- original partition tree, so no cross-block recombination is needed).
  have hkFlat :
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 92)) **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
          (.x18 ↦ᵣ target) ** (.x19 ↦ᵣ deltaV) **
          (.x20 ↦ᵣ (0 : Word)) ** regOwn .x10 **
          (U256MulU64Be.mulTailExtra basePtr deltaV outPtr baseBytes **
            (((U256MulU64Be.frameSlots (spH + signExtend12 (-48 : BitVec 12))
                  (K73 + 92) basePtr outPtr target deltaV (0 : Word)) **
                (bytesRegion outPtr
                    (k73_decr_img2 baseBytes deltaV outWin) **
                  k73MulOverflowCoreNoStatus
                    (k73_decr_img1 baseBytes deltaV) k)) **
              (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
                regOwn .x20 ** Grest)))) s := by
    have hEq :
        ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 92)) **
              frameSlotsSaved k73Frame spH
                (k73Saved raIn v8 v9 v18 v19 v20) **
              U256MulU64Be.mulTailExtra basePtr deltaV outPtr baseBytes) **
            ((((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
                    (.x18 ↦ᵣ target) ** (.x19 ↦ᵣ deltaV) **
                    (.x20 ↦ᵣ (0 : Word)) **
                    U256MulU64Be.frameSlots
                      (spH + signExtend12 (-48 : BitVec 12)) (K73 + 92)
                      basePtr outPtr target deltaV (0 : Word)) **
                  (bytesRegion outPtr
                      (k73_decr_img2 baseBytes deltaV outWin) **
                    k73MulOverflowCoreNoStatus
                      (k73_decr_img1 baseBytes deltaV) k)) **
              (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
                regOwn .x20 ** (Grest ** regOwn .x10)))) =
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 92)) **
            frameSlotsSaved k73Frame spH
              (k73Saved raIn v8 v9 v18 v19 v20) **
            (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
            (.x18 ↦ᵣ target) ** (.x19 ↦ᵣ deltaV) **
            (.x20 ↦ᵣ (0 : Word)) ** regOwn .x10 **
            (U256MulU64Be.mulTailExtra basePtr deltaV outPtr baseBytes **
              (((U256MulU64Be.frameSlots
                    (spH + signExtend12 (-48 : BitVec 12)) (K73 + 92)
                    basePtr outPtr target deltaV (0 : Word)) **
                  (bytesRegion outPtr
                      (k73_decr_img2 baseBytes deltaV outWin) **
                    k73MulOverflowCoreNoStatus
                      (k73_decr_img1 baseBytes deltaV) k)) **
                (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
                  regOwn .x20 ** Grest)))) := by
      xperm_cert_eq
    exact hEq ▸ hk
  -- Re-wrap the fixed-`k` window existentially: single-layer rebuilds, each
  -- split a sibling of an original one, and the witness state already
  -- separates the window group from the ownership tail.
  obtain ⟨u1, u2, hd1, hu1, hx0, r1⟩ := hkFlat
  obtain ⟨u3, u4, hd3, hu3, hx1, r2⟩ := r1
  obtain ⟨u5, u6, hd5, hu5, hFSS, r3⟩ := r2
  obtain ⟨u7, u8, hd7, hu7, hx2, r4⟩ := r3
  obtain ⟨u9, u10, hd9, hu9, hp8, r5⟩ := r4
  obtain ⟨u11, u12, hd11, hu11, hp9, r6⟩ := r5
  obtain ⟨u13, u14, hd13, hu13, hp18, r7⟩ := r6
  obtain ⟨u15, u16, hd15, hu15, hp19, r8⟩ := r7
  obtain ⟨u17, u18, hd17, hu17, hp20, r9⟩ := r8
  obtain ⟨u19, u20, hd19, hu19, ho10, r10⟩ := r9
  obtain ⟨u21, u22, hd21, hu21, hT, r11⟩ := r10
  obtain ⟨u23, u24, hd23, hu23, hWinG, hOwnG⟩ := r11
  exact ⟨u1, u2, hd1, hu1, hx0, ⟨u3, u4, hd3, hu3, hx1,
    ⟨u5, u6, hd5, hu5, hFSS, ⟨u7, u8, hd7, hu7, hx2,
    ⟨u9, u10, hd9, hu9, hp8, ⟨u11, u12, hd11, hu11, hp9,
    ⟨u13, u14, hd13, hu13, hp18, ⟨u15, u16, hd15, hu15, hp19,
    ⟨u17, u18, hd17, hu17, hp20, ⟨u19, u20, hd19, hu19, ho10,
    ⟨u21, u22, hd21, hu21, hT, ⟨u23, u24, hd23, hu23,
      ⟨k, hWinG⟩, hOwnG⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩


/-- The outer multiply-overflow failure leg, from whole-route entry to the
    shared-epilogue return: charges the native-discharge corollary onto
    `k73_decrease_mulfail_outer_return_spec_within`, leaving every leftover
    atom of the carry rest inside the junk abbreviation. -/
theorem k73_decr_mulfail_entry_to_return_spec_within
    (sp0 spH raIn gasLimit gasUsed target basePtr outPtr : Word)
    (v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accWin outWin : List (BitVec 8)) (Grest : Assertion)
    (hsp : spH = sp0 + signExtend12 (-56 : BitVec 12))
    (htarget : target = gasLimit >>> 1)
    (hne : gasUsed ≠ target)
    (hnotlt : ¬ target.toNat < gasUsed.toNat)
    (hnonzero : gasUsed ≠ 0)
    (hG : Grest.pcFree)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hlenA : baseBytes.length = 32)
    (hlenAcc : accWin.length = 40)
    (houtW : outWin.length = 32)
    (halignA : basePtr.toNat % 8 = 0)
    (hoverA : basePtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ j, j < 32 →
      isValidByteAccess (basePtr + BitVec.ofNat 64 j) = true)
    (halignOut : outPtr.toNat % 8 = 0)
    (hoverOut : outPtr.toNat + 32 < 2 ^ 64)
    (hvalidOut : ∀ j, j < 32 →
      isValidByteAccess (outPtr + BitVec.ofNat 64 j) = true) :
    cpsBranchWithin (20 + 3852 + 9) K73 wholeCode
      (k73HeadPre sp0 spH raIn gasLimit gasUsed basePtr outPtr
        v8 v9 v18 v19 v20 baseBytes outWin
        (EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accWin **
          k73_decr_ghole spH Grest))
      raIn
      ((.x2 ↦ᵣ sp0) ** regsAt k73Frame (k73Saved raIn v8 v9 v18 v19 v20) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        k73_decr_mulfail_junk spH (target - gasUsed) target basePtr outPtr
          baseBytes outWin (k73_decr_ghole spH Grest))
      (K73 + 96)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73DecreaseMulCarryRest spH raIn basePtr outPtr target
          (target - gasUsed) v8 v9 v18 v19 v20 baseBytes
          (k73_decr_img1 baseBytes (target - gasUsed))
          (k73_decr_img2 baseBytes (target - gasUsed) outWin)
          (k73_decr_ghole spH Grest) **
        regOwn .x10) := by
  have hGH :
      ((k73_decr_ghole spH Grest)).pcFree := by
    pcf
    exact hG
  have hciii := k73_decrease_entry_status_native_discharged
    sp0 spH raIn gasLimit gasUsed target basePtr outPtr
    v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 baseBytes accWin outWin
    (k73_decr_ghole spH Grest)
    hsp htarget hne hnotlt hnonzero hGH hlenA hlenAcc houtW
    halignA hoverA hvalidA halignOut hoverOut hvalidOut
  -- Re-typed at the statement's image-token spelling so the final combinator
  -- unifies against the goal syntactically.
  have hciiiT : cpsBranchWithin (20 + 3852) K73 wholeCode
      (k73HeadPre sp0 spH raIn gasLimit gasUsed basePtr outPtr
        v8 v9 v18 v19 v20 baseBytes outWin
        (EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accWin **
          k73_decr_ghole spH Grest))
      (K73 + 276)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73DecreaseMulCarryRest spH raIn basePtr outPtr target
          (target - gasUsed) v8 v9 v18 v19 v20 baseBytes
          (k73_decr_img1 baseBytes (target - gasUsed))
          (k73_decr_img2 baseBytes (target - gasUsed) outWin)
          (k73_decr_ghole spH Grest) ** regOwn .x10)
      (K73 + 96)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73DecreaseMulCarryRest spH raIn basePtr outPtr target
          (target - gasUsed) v8 v9 v18 v19 v20 baseBytes
          (k73_decr_img1 baseBytes (target - gasUsed))
          (k73_decr_img2 baseBytes (target - gasUsed) outWin)
          (k73_decr_ghole spH Grest) ** regOwn .x10) := hciii
  -- pcFree of the junk parameter: standard atoms plus one existential window.
  have hTEpc :
      (EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr (target - gasUsed)
        outPtr baseBytes).pcFree := by
    dsimp only [EvmAsm.Codegen.U256MulU64Be.mulTailExtra]
    pcf
  have hWinpc :
      (k73_decr_mulfail_win spH (target - gasUsed) target basePtr outPtr
        baseBytes outWin).pcFree :=
    k73_pcFree_exists (A := fun k =>
        (U256MulU64Be.frameSlots (spH + signExtend12 (-48 : BitVec 12))
            (K73 + 92) basePtr outPtr target (target - gasUsed) (0 : Word) **
          bytesRegion outPtr
            (k73_decr_img2 baseBytes (target - gasUsed) outWin) **
          k73MulOverflowCoreNoStatus
            (k73_decr_img1 baseBytes (target - gasUsed)) k))
      (fun k => by pcf)
  have hPjunk :
      (k73_decr_mulfail_junk spH (target - gasUsed) target basePtr outPtr
        baseBytes outWin (k73_decr_ghole spH Grest)).pcFree :=
    pcFree_sepConj hTEpc (pcFree_sepConj hWinpc hGH)
  -- The twin, run at the junk parameter.
  have hspF : spH + signExtend12 (56 : BitVec 12) = sp0 := by
    have hx : signExtend12 (56 : BitVec 12) = (56 : Word) := by decide
    rw [hsp, hx]
    have hy : signExtend12 (-56 : BitVec 12) =
        (18446744073709551560 : Word) := by decide
    rw [hy]
    bv_omega
  have htwin := k73_decrease_mulfail_outer_return_spec_within
    sp0 spH raIn v8 v9 v18 v19 v20
    basePtr outPtr target (target - gasUsed) (0 : Word)
    (k73_decr_mulfail_junk spH (target - gasUsed) target basePtr outPtr
      baseBytes outWin (k73_decr_ghole spH Grest)) hspF hret hPjunk
  -- Premise alignment: the feeder extracts the epilogue's `.x2` pin and
  -- register pins from the carry-rest window and re-wraps the fixed-`k`
  -- memory junk existentially (see `k73_decr_mulfail_twinfeed`).
  have htf := k73_decr_mulfail_twinfeed spH raIn basePtr outPtr target
    (target - gasUsed) v8 v9 v18 v19 v20 baseBytes outWin Grest
  have htw' := cpsTripleWithin_weaken (fun s hp => htf s hp)
    (fun _ hq => hq) htwin
  exact cpsBranchWithin_seq_cpsTripleWithin_taken_same_cr hciiiT htw'

/-- The divide-scratch ownerships ride in the corollary's ambient parameter,
    so the ghole envelope over the enriched environment equals the fall leg's
    `regOwns [.x14..x17] ** H` token spelling.  Both sides are pin-free: the
    `.x2 ↦ spH` fact lives inside the carry-rest window mid-body (where
    `sp = spH` genuinely) and is re-derived by the fall leg's own frame
    machinery, never claimed at a return exit. -/
private theorem k73_decr_ghole_env_eq (spH : Word) (G : Assertion) :
    (k73_decr_ghole spH
        (regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** G)) =
      (regOwns [.x14, .x15, .x16, .x17] **
        (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
          regOwn .x20 ** G)) := by
  simp only [k73_decr_ghole, regOwns_cons, regOwns_nil, sepConj_emp_right']
  xperm_cert_eq

/-- Subtractor-return post, shared by the borrow-failure taken exit and the
    success fall exit (status 1 / 0). -/
def k73_decr_sub_return_post
    (sp0 spH raIn target basePtr outPtr gasUsed v8 v9 v18 v19 v20 : Word)
    (baseBytes outWin : List (BitVec 8)) (Genv : Assertion) (status : Word) :
    Assertion :=
  (.x2 ↦ᵣ sp0) ** regsAt k73Frame (k73Saved raIn v8 v9 v18 v19 v20) **
    frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
    (.x10 ↦ᵣ status) **
    (.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
    regOwns u256SubBeInPlaceScratch **
    bytesRegion outPtr
      (u256SubBeBytes baseBytes
        (u256DivU64BeQuotBytes
          (u256DivU64BeQuotBytes
            (k73_decr_img2 baseBytes (target - gasUsed) outWin)
            (k73_decr_img2 baseBytes (target - gasUsed) outWin) target)
          (u256DivU64BeQuotBytes
            (k73_decr_img2 baseBytes (target - gasUsed) outWin)
            (k73_decr_img2 baseBytes (target - gasUsed) outWin) target)
          8)
        (u256DivU64BeQuotBytes
          (u256DivU64BeQuotBytes
            (k73_decr_img2 baseBytes (target - gasUsed) outWin)
            (k73_decr_img2 baseBytes (target - gasUsed) outWin) target)
          (u256DivU64BeQuotBytes
            (k73_decr_img2 baseBytes (target - gasUsed) outWin)
            (k73_decr_img2 baseBytes (target - gasUsed) outWin) target)
          8)) **
    bytesRegion basePtr baseBytes **
    EvmAsm.Codegen.U256MulU64Be.frameSlots
      (spH + signExtend12 (-48 : BitVec 12)) (K73 + 92)
      basePtr outPtr target (target - gasUsed) (0 : Word) **
    bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
      (k73_decr_img1 baseBytes (target - gasUsed)) **
    (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
      regOwn .x20 ** Genv)

/-- Multiply-overflow failure post (the taken exit of the mul-status branch,
    routed through the shared failure epilogue). -/
def k73_decr_mulfail_taken_post
    (sp0 spH raIn target basePtr outPtr gasUsed v8 v9 v18 v19 v20 : Word)
    (baseBytes outWin : List (BitVec 8)) (Genv : Assertion) : Assertion :=
  (.x2 ↦ᵣ sp0) ** regsAt k73Frame (k73Saved raIn v8 v9 v18 v19 v20) **
    frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
    (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
    k73_decr_mulfail_junk spH (target - gasUsed) target basePtr outPtr
      baseBytes outWin
      (k73_decr_ghole spH
        (regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** Genv))

/-! Whole nonzero-decrease route: the mul-status branch is extended past its
    not-taken exit (the fall leg into the divider/subtractor chain) with the
    mul-overflow taken exit retargeted through the shared failure epilogue.
    All divider window claims are threaded at the computed image lists
    (`mulState` / `copyState`), so the divider quotient premises speak about
    exactly the bytes the multiply leaves behind. -/
theorem k73_decrease_route_machine_spec_within
    (sp0 spH raIn gasLimit gasUsed target basePtr outPtr : Word)
    (v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accWin outWin : List (BitVec 8)) (Genv : Assertion)
    (hsp : spH = sp0 + signExtend12 (-56 : BitVec 12))
    (htarget : target = gasLimit >>> 1)
    (hne : gasUsed ≠ target)
    (hnotlt : ¬ target.toNat < gasUsed.toNat)
    (hnonzero : gasUsed ≠ 0)
    (hG : Genv.pcFree)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hlenA : baseBytes.length = 32)
    (hlenAcc : accWin.length = 40)
    (houtW : outWin.length = 32)
    (halignA : basePtr.toNat % 8 = 0)
    (hoverA : basePtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ j, j < 32 →
      isValidByteAccess (basePtr + BitVec.ofNat 64 j) = true)
    (halignOut : outPtr.toNat % 8 = 0)
    (hoverOut : outPtr.toNat + 32 < 2 ^ 64)
    (hvalidOut : ∀ j, j < 32 →
      isValidByteAccess (outPtr + BitVec.ofNat 64 j) = true)
    (htargetPos : 0 < target.toNat)
    (hdisj : basePtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ basePtr.toNat)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroBase : Region.wf ⟨basePtr, baseBytes⟩)
    (hszDiv1 :
      4 * ((u256DivU64BeInPlaceFn outPtr target
        (k73_decr_img2 baseBytes (target - gasUsed) outWin)).body.size + 1)
        ≤ 2 ^ 64)
    (hszDiv2 :
      4 * ((u256DivU64BeInPlaceFn outPtr 8
        (u256DivU64BeQuotBytes
          (k73_decr_img2 baseBytes (target - gasUsed) outWin)
          (k73_decr_img2 baseBytes (target - gasUsed) outWin) target)).body.size
          + 1)
        ≤ 2 ^ 64)
    (hszSub :
      4 * ((u256SubBeInPlaceFn basePtr outPtr baseBytes
        (u256DivU64BeQuotBytes
          (u256DivU64BeQuotBytes
            (k73_decr_img2 baseBytes (target - gasUsed) outWin)
            (k73_decr_img2 baseBytes (target - gasUsed) outWin) target)
          (u256DivU64BeQuotBytes
            (k73_decr_img2 baseBytes (target - gasUsed) outWin)
            (k73_decr_img2 baseBytes (target - gasUsed) outWin) target)
          8)).body.size + 1)
        ≤ 2 ^ 64) :
    cpsBranchWithin ((20 + 3852 + 9) +
        (((((10 +
              (u256DivU64BeInPlaceFn outPtr target
                (k73_decr_img2 baseBytes (target - gasUsed) outWin)).body.steps +
            (u256DivU64BeInPlaceFn outPtr 8
              (u256DivU64BeQuotBytes
                (k73_decr_img2 baseBytes (target - gasUsed) outWin)
                (k73_decr_img2 baseBytes (target - gasUsed) outWin)
                target)).body.steps +
          1) +
          (1 + (5 + (u256SubBeInPlaceFn basePtr outPtr baseBytes
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes
                (k73_decr_img2 baseBytes (target - gasUsed) outWin)
                (k73_decr_img2 baseBytes (target - gasUsed) outWin) target)
              (u256DivU64BeQuotBytes
                (k73_decr_img2 baseBytes (target - gasUsed) outWin)
                (k73_decr_img2 baseBytes (target - gasUsed) outWin) target)
              8)).body.steps))) + 1) + 9) + 10))
      K73 wholeCode
      (k73HeadPre sp0 spH raIn gasLimit gasUsed basePtr outPtr
        v8 v9 v18 v19 v20 baseBytes outWin
        (EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accWin **
        k73_decr_ghole spH
          (regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** Genv)))
      raIn
      (fun st =>
        ((k73_decr_mulfail_taken_post sp0 spH raIn target basePtr outPtr
            gasUsed v8 v9 v18 v19 v20 baseBytes outWin Genv) st ∨
          (k73_decr_sub_return_post sp0 spH raIn target basePtr outPtr gasUsed
            v8 v9 v18 v19 v20 baseBytes outWin Genv (1 : Word)) st))
      raIn
      (k73_decr_sub_return_post sp0 spH raIn target basePtr outPtr gasUsed
        v8 v9 v18 v19 v20 baseBytes outWin Genv (0 : Word)) := by
  have hspF : spH + signExtend12 (56 : BitVec 12) = sp0 := by
    have hx : signExtend12 (56 : BitVec 12) = (56 : Word) := by decide
    rw [hsp, hx]
    have hy : signExtend12 (-56 : BitVec 12) =
        (18446744073709551560 : Word) := by decide
    rw [hy]
    bv_omega
  have hGr :
      (regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** Genv).pcFree := by
    pcf
    exact hG
  have hHp :
      (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
        regOwn .x20 ** Genv).pcFree := by
    pcf
    exact hG
  have hlenI2 :
      (k73_decr_img2 baseBytes (target - gasUsed) outWin).length = 32 :=
    EvmAsm.Codegen.U256MulU64Be.copyState_len _ _ 32 houtW
  have hfall := k73_decrease_mul_fall_to_return_spec_within
    sp0 spH raIn basePtr outPtr target gasUsed v8 v9 v18 v19 v20
    baseBytes (k73_decr_img1 baseBytes (target - gasUsed))
      (k73_decr_img2 baseBytes (target - gasUsed) outWin)
    (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
      regOwn .x20 ** Genv)
    hHp hrw hroBase hlenA hlenI2 hoverA hoverOut hdisj htargetPos
    hszDiv1 hszDiv2 hszSub hspF hret
  have hperm : ∀ h : PartialState,
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73DecreaseMulCarryRest spH raIn basePtr outPtr target
          (target - gasUsed) v8 v9 v18 v19 v20 baseBytes
          (k73_decr_img1 baseBytes (target - gasUsed))
          (k73_decr_img2 baseBytes (target - gasUsed) outWin)
          (k73_decr_ghole spH
            (regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** Genv)) **
        regOwn .x10) h →
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73DecreaseMulCarryRest spH raIn basePtr outPtr target
          (target - gasUsed) v8 v9 v18 v19 v20 baseBytes
          (k73_decr_img1 baseBytes (target - gasUsed))
          (k73_decr_img2 baseBytes (target - gasUsed) outWin)
          (regOwns [.x14, .x15, .x16, .x17] **
            (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
              regOwn .x20 ** Genv)) ** regOwn .x10) h := by
    intro h hp
    rw [k73_decr_ghole_env_eq] at hp
    exact hp
  have hmf := k73_decr_mulfail_entry_to_return_spec_within
    sp0 spH raIn gasLimit gasUsed target basePtr outPtr
    v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 baseBytes accWin outWin
    (regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** Genv)
    hsp htarget hne hnotlt hnonzero hGr hret hlenA hlenAcc houtW
    halignA hoverA hvalidA halignOut hoverOut hvalidOut
  exact cpsBranchWithin_seq_cpsBranchWithin_with_perm_same_cr hmf hperm hfall
    (fun _ hp => Or.inl hp) (fun _ hp => Or.inr hp)

/-- CONSTRUCTED non-vacuity inhabitance of the native-discharge corollary
    (adopted standard for #12346: a whole-route theorem does not count until a
    closed-proposition witness exists at corollary level - an unsatisfiable
    premise cannot admit a constructed witness, so this check catches the
    vacuity class by construction rather than by vigilance).  Concrete
    literals: `sp0 - spH = 56`, decrease guard family `target = 5000 >
    gasUsed = 2500`, `gasLimit = 10000`, zero scratch windows, empty
    ambience.  Discharged by direct application - no hypotheses, no sorry. -/
theorem k73_decr_entry_status_native_inhabited :
    cpsBranchWithin (20 + 3852) K73 wholeCode
      (k73HeadPre (0xa0050038 : Word) 0xa0050000 0 10000 2500 0xa0000000
        0xa0000100 0 0 0 0 0 (List.replicate 32 0) (List.replicate 32 0)
        (EvmAsm.Codegen.U256MulU64Be.frameSlots
          (0xa0050000 + signExtend12 (-48 : BitVec 12)) 0 0 0 0 0 0 **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
            (List.replicate 40 0) ** empAssertion))
      (K73 + 276)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73DecreaseMulCarryRest 0xa0050000 0 0xa0000000 0xa0000100 5000
            (5000 - 2500 : Word) 0 0 0 0 0 (List.replicate 32 0)
            (EvmAsm.Codegen.U256MulU64Be.mulState (List.replicate 32 0)
              (5000 - 2500 : Word) 32)
            (EvmAsm.Codegen.U256MulU64Be.copyState
              (EvmAsm.Codegen.U256MulU64Be.mulState (List.replicate 32 0)
                (5000 - 2500 : Word) 32) (List.replicate 32 0) 32)
            empAssertion **
          regOwn .x10)
      (K73 + 96)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73DecreaseMulCarryRest 0xa0050000 0 0xa0000000 0xa0000100 5000
            (5000 - 2500 : Word) 0 0 0 0 0 (List.replicate 32 0)
            (EvmAsm.Codegen.U256MulU64Be.mulState (List.replicate 32 0)
              (5000 - 2500 : Word) 32)
            (EvmAsm.Codegen.U256MulU64Be.copyState
              (EvmAsm.Codegen.U256MulU64Be.mulState (List.replicate 32 0)
                (5000 - 2500 : Word) 32) (List.replicate 32 0) 32)
            empAssertion **
          regOwn .x10) := by
  exact k73_decrease_entry_status_native_discharged
    (0xa0050038 : Word) 0xa0050000 0 10000 2500 5000 0xa0000000 0xa0000100
    0 0 0 0 0 0 0 0 0 0 0
    (List.replicate 32 0) (List.replicate 40 0) (List.replicate 32 0)
    empAssertion
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by pcf)
    (by simp) (by simp) (by simp)
    (by decide) (by decide)
    (by intro j _; interval_cases j <;> decide)
    (by decide) (by decide)
    (by intro j _; interval_cases j <;> decide)

/-! ### Route-B junction casts

    The whole-route exits live in machine vocabulary; the wrapper's Route-B
    contract (`k73RouteBCallPost` / `k73PostOwn` / `k73FailurePost`) lives in
    wrapper vocabulary.  Each cast is a pointwise implication from one exit
    instance to its Route-B arm.  The wrapper-world atoms the machine route
    never speaks about (`hvbfFrame` save slots, the header region, ownership
    of `x5/x6/x7/x13/x28..x31`) ride through every seam inside the ambient
    `Genv` instantiation - the piggyback below - exactly like the equal-route
    adapter's `k73_piggyback`.  Exit atoms with no Route-B home (the subtract
    scratch ownerships, the multiply scratch frame, the accumulator window,
    the restored-register ownerships) are absorbed into the trailing `F`
    slot, which the discharger instantiates freely. -/
end EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute
