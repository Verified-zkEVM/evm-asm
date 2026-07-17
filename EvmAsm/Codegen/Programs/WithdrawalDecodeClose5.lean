/-
  `withdrawalDecode_prog` caller-contract composition, part 5 — the CONT side
  and the whole-program close.

  Close4 finished every parse-failure exit (`wdK34FailArm`, `wdK20FailArm`,
  `wdFailArm`).  This module supplies the mirror image on the continue side:

    * `wdContReshape` — the cont analog of `wdK34FailPre`: a K34 field call's
      `k34ContPost` (status `0`, success payload) reshaped into the shared
      register/frame bundle each downstream stage consumes, weakening the saved
      frame (`savedFrame → frameSlotsOwn`) and keeping the freshly-written output
      cell together with the pinned field `Result`.
    * the merge-chain backbone stitching the four field stages, the length
      check and the copy loop into a single `WB+32 → raIn` triple; and
    * the top-level `withdrawal_decode_spec_within = wdPrologue ;; backbone`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.WithdrawalDecodeClose4

namespace EvmAsm.Codegen.WithdrawalDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpFieldToU64SAsm

/-! ## CONT-side reshape (K34 boundary)

    A K34 field call's continue exit (`k34ContPost`, status `0`) keeps a success
    payload with a genuine field decode.  The reshape below lines that payload up
    with the shared field-stage register/frame layout: the saved frame weakens to
    the merely-owned slots (`savedFrameK34_own`), and the payload's temporaries
    reappear as the next stage's `regIs`/`regOwn` cells.  The freshly-written
    output cell (`saved.s1 ↦ ov`) and the pinned per-field `Result` are carried
    forward so the whole-program success post can assemble `Decoded`. -/

/-- The shared cont-boundary bundle: the register/frame state a downstream field
    stage consumes, together with the just-written output cell and the pinned
    field `Result`.  The saved frame has already been weakened to `frameSlotsOwn`
    and the scratch stack retained as `stackFree newSp 8`. -/
def wdContBundle (spW newSp listBase raRet offset len v12 x5 ss ov : Word)
    (outer : Saved) (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  (.x1 ↦ᵣ raRet) ** (.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
  frameSlotsOwn frame newSp ** (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
  (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** stackFree newSp 8 **
  (.x5 ↦ᵣ x5) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ ss) ** (.x12 ↦ᵣ v12) **
  regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
  (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) ** (saved.s1 ↦ₘ ov) **
  (⌜Result bytes listBase listLen index (0 : Word) ov⌝ : Assertion)

set_option maxRecDepth 8000 in
/-- CONT reshape: a K34 field call's peeled `k34ContPost` body (a status-`0`
    success payload) reshapes into `wdContBundle`.  Weaken the saved frame to
    `frameSlotsOwn` and permute; the field `Result`, the written output cell
    `saved.s1 ↦ ov` and the temporaries all carry through unchanged.  Generic
    over the field index — the backbone instantiates it at boundaries 0→1, 1→2,
    2→3. -/
theorem wdContReshape (spW newSp listBase raRet offset len v12 x5 ss ov : Word)
    (outer : Saved) (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : ∀ h,
    ((.x1 ↦ᵣ raRet) **
     (((.x2 ↦ᵣ spW) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
       savedFrame newSp outer) **
      successPayload newSp listBase offset len v12 x5 ss (0 : Word) ov saved
        bytes listLen index)) h →
    wdContBundle spW newSp listBase raRet offset len v12 x5 ss ov outer saved bytes
      listLen index h := by
  intro h hp
  unfold successPayload at hp
  have hp2 := sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (savedFrameK34_own newSp outer))))) h hp
  unfold wdContBundle
  xperm_hyp hp2

#print axioms wdContReshape

end EvmAsm.Codegen.WithdrawalDecodeSpec
