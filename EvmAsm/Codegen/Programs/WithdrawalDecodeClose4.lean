/-
  `withdrawalDecode_prog` caller-contract composition, part 4 — the final close.

  This module threads the four field stages, the length check, and the address
  copy loop into the whole-program caller contract
  `withdrawal_decode_spec_within`, routing every parse-failure exit through the
  common failure tail (`wdFailEpi`) and the all-fields-ok exit through the
  success tail (`wdSuccessEpi`).

  The composition is inside-out: per-boundary reshape lemmas line up each
  stage's continue-post with the next stage's pre (and each fail-post with the
  failure tail), and a thin final compose stitches the reshaped pieces via
  `cpsBranchWithin_merge_same_cr`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.WithdrawalDecodeClose3

namespace EvmAsm.Codegen.WithdrawalDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpFieldToU64SAsm

/-! ## Whole-program post-condition pieces -/

/-- The registers/slots common to both the success and the failure return:
    the restored caller registers (`x2/x1/x8/x9/x18`) and the four withdrawal
    saved slots (`spW..spW+24`), exactly `wdEpiCore`'s non-`G` post. -/
def wdCommon (sp0 spW wra cs0 cs1 cs2 : Word) : Assertion :=
  (.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ wra) ** (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) **
  (.x18 ↦ᵣ cs2) ** (spW ↦ₘ wra) ** ((spW + 8) ↦ₘ cs0) **
  ((spW + 16) ↦ₘ cs1) ** ((spW + 24) ↦ₘ cs2)

theorem pcFree_wdCommon (sp0 spW wra cs0 cs1 cs2 : Word) :
    (wdCommon sp0 spW wra cs0 cs1 cs2).pcFree := by
  unfold wdCommon
  repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj

/-- The clobbered temporaries left owned on return, together with the three
    callee-saved registers `x19/x20/x21` (holding the caller's `s3/s4/s5`, which
    the RLP callees preserve) and the zero register.  Common to both returns. -/
def wdScratch (s3 s4 s5 : Word) : Assertion :=
  (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
  regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
  regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))

theorem pcFree_wdScratch (s3 s4 s5 : Word) : (wdScratch s3 s4 s5).pcFree := by
  unfold wdScratch
  repeat' first | exact pcFree_regIs | exact pcFree_regOwn | apply pcFree_sepConj

/-- The mutable leftover after a failure return: the whole 48-byte output struct
    (contents forgotten, only ownership retained), the input region, the four
    data cells, the clobbered temporaries, and the reclaimed 12-cell scratch
    stack. -/
def wdFailLeftover (spW outBase listBase s3 s4 s5 : Word) (bytes : List (BitVec 8)) :
    Assertion :=
  fun h => ∃ (o0 o1 o3 woff wlen roff rlen : Word) (addr20 pad4 : List (BitVec 8)),
    ((outBase ↦ₘ o0) ** ((outBase + 8) ↦ₘ o1) **
     bytesRegion (outBase + 16) addr20 ** bytesRegion (outBase + 36) pad4 **
     ((outBase + 40) ↦ₘ o3) ** bytesRegion listBase bytes **
     (wdOffsetAddr ↦ₘ woff) ** (wdLengthAddr ↦ₘ wlen) **
     (offsetCell ↦ₘ roff) ** (lengthCell ↦ₘ rlen) ** stackFree spW 12 **
     wdScratch s3 s4 s5) h

/-- The output-struct leftover after a success return, each cell tied to the
    genuinely decoded field value (`outputSuccess`), plus the untouched input
    region, the two data cells (still holding the address offset/length), the
    clobbered temporaries, and the reclaimed scratch stack. -/
def wdSuccessOut (spW outBase listBase s3 s4 s5 v0 v1 v3 o2 l2 : Word)
    (bytes oldAddr pad4 : List (BitVec 8)) : Assertion :=
  fun h => ∃ (roff rlen : Word),
    (outputSuccess outBase v0 v1 v3 o2 bytes oldAddr pad4 **
     bytesRegion listBase bytes ** (wdOffsetAddr ↦ₘ o2) ** (wdLengthAddr ↦ₘ l2) **
     (offsetCell ↦ₘ roff) ** (lengthCell ↦ₘ rlen) ** stackFree spW 12 **
     wdScratch s3 s4 s5) h

/-- The whole-program post: `a0 = 0` with the genuine decoded output struct, or
    `a0 = 1` with a witnessed `DecodeFailure` and the owned leftover. -/
def wdWholePost (sp0 spW wra cs0 cs1 cs2 outBase listBase s3 s4 s5 : Word)
    (listLen : Nat) (bytes oldAddr pad4 : List (BitVec 8)) : Assertion :=
  fun h =>
    (∃ (v0 v1 v3 o2 l2 : Word),
      ((⌜Decoded bytes listBase listLen v0 v1 v3 o2 l2⌝ : Assertion) **
       ((.x10 ↦ᵣ (0 : Word)) ** wdCommon sp0 spW wra cs0 cs1 cs2 **
        wdSuccessOut spW outBase listBase s3 s4 s5 v0 v1 v3 o2 l2 bytes oldAddr pad4)) h) ∨
    (((⌜DecodeFailure bytes listBase listLen⌝ : Assertion) **
      ((.x10 ↦ᵣ (1 : Word)) ** wdCommon sp0 spW wra cs0 cs1 cs2 **
       wdFailLeftover spW outBase listBase s3 s4 s5 bytes)) h)

/-! ## Scratch-stack reconcile (K34 boundary)

    The whole-program pre owns `stackFree spW 12` (cells `spW-8 … spW-96`).  A
    K34 field call allocates its own frame at `newSp = spW - 32`, using the top
    cell `spW-8` framed off plus `frameSlotsOwn frame newSp` (3 cells
    `spW-16, spW-24, spW-32`) and `stackFree newSp 8` (cells `spW-40 … spW-96`).  These
    two shapes hold the same 12 owned cells. -/

/-- Assemble a K34 field call's reclaimed scratch back into `stackFree spW 12`. -/
theorem wdStack12_of_k34 (spW newSp : Word)
    (hnewSp : newSp = spW + signExtend12 (-32 : BitVec 12)) : ∀ h,
    (memOwn (spW - BitVec.ofNat 64 8) **
     frameSlotsOwn frame newSp ** stackFree newSp 8) h →
    stackFree spW 12 h := by
  intro h hp
  have hse : signExtend12 (-32 : BitVec 12) = (0xFFFFFFFFFFFFFFE0 : Word) := by decide
  subst hnewSp
  rw [hse] at hp
  simp only [frameSlotsOwn, frame, List.foldr, sepConj_emp_right',
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at hp
  simp only [stackFree] at hp ⊢
  simp only [sepConj_emp_right', Nat.reduceMul, Nat.reduceAdd] at hp ⊢
  -- normalise every K34-frame cell address to the canonical `spW - N#64` form
  rw [show spW + (18446744073709551584 : Word) + (0 : Word)
        = spW - BitVec.ofNat 64 32 from by bv_omega,
      show spW + (18446744073709551584 : Word) + (8 : Word)
        = spW - BitVec.ofNat 64 24 from by bv_omega,
      show spW + (18446744073709551584 : Word) + (16 : Word)
        = spW - BitVec.ofNat 64 16 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 64
        = spW - BitVec.ofNat 64 96 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 56
        = spW - BitVec.ofNat 64 88 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 48
        = spW - BitVec.ofNat 64 80 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 40
        = spW - BitVec.ofNat 64 72 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 32
        = spW - BitVec.ofNat 64 64 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 24
        = spW - BitVec.ofNat 64 56 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 16
        = spW - BitVec.ofNat 64 48 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 8
        = spW - BitVec.ofNat 64 40 from by bv_omega] at hp
  xperm_hyp hp

#print axioms wdStack12_of_k34

/-- The K34 boundary reconcile absorbing the saved frame: a K34 field call's
    `savedFrame` (3 saved slots) plus its `stackFree newSp 8` and the framed-off
    top cell reassemble into `stackFree spW 12`. -/
theorem wdStack12_of_k34_saved (spW newSp : Word) (outer : Saved)
    (hnewSp : newSp = spW + signExtend12 (-32 : BitVec 12)) : ∀ h,
    (memOwn (spW - BitVec.ofNat 64 8) **
     savedFrame newSp outer ** stackFree newSp 8) h →
    stackFree spW 12 h := by
  intro h hp
  refine wdStack12_of_k34 spW newSp hnewSp h ?_
  exact sepConj_mono_right (sepConj_mono_left (savedFrameK34_own newSp outer)) h hp

#print axioms wdStack12_of_k34_saved

/-- Carve a K34 field call's scratch shape out of `stackFree spW 12` (the reverse
    of `wdStack12_of_k34`, used on the continue/forward path). -/
theorem wdStack12_to_k34 (spW newSp : Word)
    (hnewSp : newSp = spW + signExtend12 (-32 : BitVec 12)) : ∀ h,
    stackFree spW 12 h →
    (memOwn (spW - BitVec.ofNat 64 8) **
     frameSlotsOwn frame newSp ** stackFree newSp 8) h := by
  intro h hp
  have hse : signExtend12 (-32 : BitVec 12) = (0xFFFFFFFFFFFFFFE0 : Word) := by decide
  subst hnewSp
  rw [hse]
  simp only [frameSlotsOwn, frame, List.foldr, sepConj_emp_right',
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]
  simp only [stackFree] at hp ⊢
  simp only [sepConj_emp_right', Nat.reduceMul, Nat.reduceAdd] at hp ⊢
  rw [show spW + (18446744073709551584 : Word) + (0 : Word)
        = spW - BitVec.ofNat 64 32 from by bv_omega,
      show spW + (18446744073709551584 : Word) + (8 : Word)
        = spW - BitVec.ofNat 64 24 from by bv_omega,
      show spW + (18446744073709551584 : Word) + (16 : Word)
        = spW - BitVec.ofNat 64 16 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 64
        = spW - BitVec.ofNat 64 96 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 56
        = spW - BitVec.ofNat 64 88 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 48
        = spW - BitVec.ofNat 64 80 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 40
        = spW - BitVec.ofNat 64 72 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 32
        = spW - BitVec.ofNat 64 64 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 24
        = spW - BitVec.ofNat 64 56 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 16
        = spW - BitVec.ofNat 64 48 from by bv_omega,
      show spW + (18446744073709551584 : Word) - BitVec.ofNat 64 8
        = spW - BitVec.ofNat 64 40 from by bv_omega]
  xperm_hyp hp

#print axioms wdStack12_to_k34

/-- The four deep scratch cells `stackFree spW 8` leaves free out of the whole
    12-cell region (used at the K20 field-2 boundary). -/
def wdStackK20Deep (spW : Word) : Assertion :=
  memOwn (spW - BitVec.ofNat 64 96) ** memOwn (spW - BitVec.ofNat 64 88) **
  memOwn (spW - BitVec.ofNat 64 80) ** memOwn (spW - BitVec.ofNat 64 72)

theorem pcFree_wdStackK20Deep (spW : Word) : (wdStackK20Deep spW).pcFree := by
  unfold wdStackK20Deep
  repeat' first | exact pcFree_memOwn | apply pcFree_sepConj

/-- Assemble a K20 field call's reclaimed scratch back into `stackFree spW 12`. -/
theorem wdStack12_of_k20 (spW : Word) : ∀ h,
    (wdStackK20Deep spW ** stackFree spW 8) h → stackFree spW 12 h := by
  intro h hp
  simp only [stackFree, wdStackK20Deep] at hp ⊢
  xperm_hyp hp

#print axioms wdStack12_of_k20

/-- Carve a K20 field call's scratch shape out of `stackFree spW 12`. -/
theorem wdStack12_to_k20 (spW : Word) : ∀ h,
    stackFree spW 12 h → (wdStackK20Deep spW ** stackFree spW 8) h := by
  intro h hp
  simp only [stackFree, wdStackK20Deep] at hp ⊢
  xperm_hyp hp

#print axioms wdStack12_to_k20

/-- Weaken the value-carrying temporaries `x5/x11/x12` (regIs) into ownership,
    folding the callee residue into `wdScratch`.  The `x19/x20/x21` callee-saved
    values and the remaining already-owned temporaries pass through unchanged.
    This is the common "(c) weaken regIs→regOwn" step of every fail-arm reshape. -/
theorem wdScratch_of_regs (s3 s4 s5 x5v x11v x12v : Word) : ∀ h,
    ((.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** (.x5 ↦ᵣ x5v) **
     regOwn .x6 ** regOwn .x7 ** (.x11 ↦ᵣ x11v) ** (.x12 ↦ᵣ x12v) ** regOwn .x13 **
     regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     (.x0 ↦ᵣ (0 : Word))) h →
    wdScratch s3 s4 s5 h := by
  intro h hp
  unfold wdScratch
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono (regIs_implies_regOwn .x5)
            (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono (regIs_implies_regOwn .x11)
                (sepConj_mono_left (regIs_implies_regOwn .x12))))))))
        h hp

#print axioms wdScratch_of_regs

/-! ## Generic `DecodeFailure` witness extraction

    Both K34 fail sub-cases (a success payload with a nonzero wrapper status, or
    the failure payload with status `1`) pin a callee `Result`.  Fusing that with
    the nonzero-status fact yields a `DecodeFailure` via whichever constructor the
    field maps to (supplied as `mkDF`).  Parametric over the field index and the
    constructor — the three K34 fail arms (fields 0/1/3) instantiate it. -/
theorem wdK34FailDF (spW newSp listBase oldOffset oldLen raRet : Word)
    (outer : Saved) (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (mkDF : ∀ (status v : Word), status ≠ (0 : Word) →
      EvmAsm.Codegen.RlpFieldToU64SAsm.Result bytes listBase listLen index status v →
      DecodeFailure bytes listBase listLen) :
    ∀ h, k34FailPost spW newSp listBase oldOffset oldLen raRet outer saved bytes
      listLen index h → DecodeFailure bytes listBase listLen := by
  intro h hp
  unfold k34FailPost at hp
  rcases hp with ⟨offset, len, v12, x5, ss, ws, ov, hs⟩ | ⟨v11, v12, hf⟩
  · obtain ⟨hnz, hrest⟩ := (sepConj_pure_left h).1 hs
    obtain ⟨_, hb, _, _, _, hB⟩ := hrest
    obtain ⟨_, hd, _, _, _, hSucc⟩ := hB
    unfold EvmAsm.Codegen.RlpFieldToU64SAsm.successPayload at hSucc
    exact mkDF ws ov hnz ((sepConj_pure_right hd).1 hSucc).2
  · obtain ⟨_, hb, _, _, _, hB⟩ := hf
    obtain ⟨_, hd, _, _, _, hFail⟩ := hB
    unfold EvmAsm.Codegen.RlpFieldToU64SAsm.failurePayload at hFail
    exact mkDF 1 0 (by decide) ((sepConj_pure_right hd).1 hFail).2

#print axioms wdK34FailDF

/-- The field-2 (K20) fail post pins a `Result` with a nonzero status; casing it
    forces the `fail` constructor (status `1`), exposing the `Failure` that the
    `DecodeFailure.field2List` arm needs.  The `ok` (status `0`) case contradicts
    the pinned nonzero fact. -/
theorem wdK20FailDF (spW listBase oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) :
    ∀ h, k20FailPost spW listBase oldOffset oldLen saved bytes listLen h →
      DecodeFailure bytes listBase listLen := by
  intro h hp
  unfold k20FailPost at hp
  obtain ⟨status, offset, len, v11, v12, hp⟩ := hp
  obtain ⟨⟨hres, hnz⟩, _⟩ := (sepConj_pure_left h).1 hp
  cases hres with
  | ok o l hok => exact absurd rfl hnz
  | fail hfail => exact DecodeFailure.field2List hfail

#print axioms wdK20FailDF

/-! ## Failure-tail arm -/

set_option maxRecDepth 8000 in
/-- The common failure tail `WB+212 → wra`, generic over the (owned) `x10` value
    on entry, the pre-restore register values, and the preserved footprint `G0`. -/
theorem wdFailEpiRO (sp0 spW wra cs0 cs1 cs2 x1old x8old x9old x18old : Word)
    (G0 : Assertion) (hG0 : G0.pcFree)
    (hspW : spW = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : wra &&& ~~~(1 : Word) = wra) :
    cpsTripleWithin 7 (WB + 212) wra fullCode
      (((.x2 ↦ᵣ spW) ** (.x1 ↦ᵣ x1old) ** (.x8 ↦ᵣ x8old) ** (.x9 ↦ᵣ x9old) **
        (.x18 ↦ᵣ x18old) ** (spW ↦ₘ wra) ** ((spW + 8) ↦ₘ cs0) **
        ((spW + 16) ↦ₘ cs1) ** ((spW + 24) ↦ₘ cs2) ** G0) ** regOwn .x10)
      (((.x10 ↦ᵣ (1 : Word)) ** wdCommon sp0 spW wra cs0 cs1 cs2) ** G0) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v10 => ?_)
  have h := wdFailEpi sp0 spW wra cs0 cs1 cs2 x1old x8old x9old x18old v10 G0 hG0 hspW hret
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => ?_) h
  unfold wdCommon
  xperm_hyp hq

#print axioms wdFailEpiRO

theorem pcFree_wdFailLeftover (spW outBase listBase s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) :
    (wdFailLeftover spW outBase listBase s3 s4 s5 bytes).pcFree := by
  intro h hp
  obtain ⟨_, _, _, _, _, _, _, _, _, hbody⟩ := hp
  revert h hbody
  show Assertion.pcFree _
  repeat' first
    | exact pcFree_memIs | exact bytesRegion_pcFree _ _ | exact pcFree_stackFree _ _
    | exact pcFree_wdScratch _ _ _ | apply pcFree_sepConj

#print axioms pcFree_wdFailLeftover

set_option maxRecDepth 8000 in
/-- Generic fail arm: from any reshaped fail-pre — the restored-caller registers
    and stack slots plus `⌜DecodeFailure⌝ ** wdFailLeftover` as the preserved
    footprint `G0`, and an owned `x10` — the failure tail (`WB+212 → wra`) lands
    the whole-program failure post.  Every fail arm (K34 fields 0/1/3, K20
    field-2 list, length-check) reduces to this after its own PRE reshape. -/
theorem wdFailArm (sp0 spW wra cs0 cs1 cs2 x1old x8old x9old x18old
      outBase listBase s3 s4 s5 : Word)
    (bytes oldAddr pad4 : List (BitVec 8)) (listLen : Nat)
    (hspW : spW = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : wra &&& ~~~(1 : Word) = wra) :
    cpsTripleWithin 7 (WB + 212) wra fullCode
      (((.x2 ↦ᵣ spW) ** (.x1 ↦ᵣ x1old) ** (.x8 ↦ᵣ x8old) ** (.x9 ↦ᵣ x9old) **
        (.x18 ↦ᵣ x18old) ** (spW ↦ₘ wra) ** ((spW + 8) ↦ₘ cs0) **
        ((spW + 16) ↦ₘ cs1) ** ((spW + 24) ↦ₘ cs2) **
        ((⌜DecodeFailure bytes listBase listLen⌝ : Assertion) **
         wdFailLeftover spW outBase listBase s3 s4 s5 bytes)) ** regOwn .x10)
      (wdWholePost sp0 spW wra cs0 cs1 cs2 outBase listBase s3 s4 s5 listLen bytes
        oldAddr pad4) := by
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => Or.inr ?_)
    (wdFailEpiRO sp0 spW wra cs0 cs1 cs2 x1old x8old x9old x18old
      ((⌜DecodeFailure bytes listBase listLen⌝ : Assertion) **
        wdFailLeftover spW outBase listBase s3 s4 s5 bytes)
      (pcFree_sepConj pcFree_pure (pcFree_wdFailLeftover _ _ _ _ _ _ _)) hspW hret)
  -- hq : ((x10↦1 ** wdCommon) ** (⌜DF⌝ ** wdFailLeftover)) h
  -- goal : (⌜DF⌝ ** (x10↦1 ** wdCommon ** wdFailLeftover)) h
  xperm_hyp hq

#print axioms wdFailArm

end EvmAsm.Codegen.WithdrawalDecodeSpec
