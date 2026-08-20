/-
  EvmAsm.Codegen.Programs.HeaderValidatePostMergeRound

  The GENERIC K67 loop round for `header_validate_post_merge`: one iteration
  of the 15-field header walk at [14] (`K + 56`), composed from
  `k67LoopCall` (the `rlp_walk_next` call), the status dispatch at [17], and
  the five ok-path arms (`k67LoopContO/Cont1/Cont7/Diff/Exit`), against the
  fuel-indexed invariant `k67FuelInv`.

  The invariant ties the fuel index to the walked cursor via `cycleFuel` and
  records the walked `StrictPrefix` plus the two captures the post-loop
  compares need (field 1 ommers end/length, field 7 zero-length difficulty).
  The round contract is `K67RoundContract` with a uniform 101-step bound
  (90 for the call, 1 for the dispatch, at most 10 for an arm); the fold
  `k67LoopFold` is `k67MeasureThreeExitLoop_of_round`.

  Cursor-at-end is handled by `k67LoopCallEnd` (the
  `rlp_walk_next_end_spec_within` path): the walk reports status 2 and the
  dispatch routes to the status-4 station, so the round's case split is on
  `cur < bytes.length`, not on the walk outcome alone.
-/

import EvmAsm.Codegen.Programs.HeaderValidatePostMergeLoopCloseClean
import EvmAsm.Codegen.Programs.HeaderValidatePostMergeLoopWitness
import EvmAsm.Codegen.Programs.RlpListNthItemSAsmBase

namespace EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpWalkNextStrictFuel
open EvmAsm.Codegen.RlpListNthItemSAsm

/-! ## §1  Two-way normalized walk outcome -/

/-- The 2-way normalized `rlp_walk_next` outcome at the K67 call site:
    status-0 success (`rlpWalkNextOk`) or a nonzero-status failure carrying
    the generic `WalkFailure`.  Mirror of `hesrNextNorm`. -/
def k67NextNorm (base endPtr : Word) (bytes : List (BitVec 8)) (off : Nat) :
    Assertion := fun h =>
  rlpWalkNextOk (base + BitVec.ofNat 64 off) endPtr bytes off h ∨
    (∃ status : Word,
      (((.x10 ↦ᵣ (base + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜status ≠ (0 : Word) ∧
          RlpListNthItemSAsm.WalkFailure bytes off
            (base + BitVec.ofNat 64 off) endPtr⌝) h))

/-- Every raw outcome disjunct implies the 2-way normalized form. -/
theorem k67NextOutcome_to_norm (base endPtr : Word) (bytes : List (BitVec 8))
    (off : Nat) :
    ∀ h, k67NextOutcome base endPtr bytes off h →
      k67NextNorm base endPtr bytes off h := by
  intro h hout
  unfold k67NextOutcome at hout
  rcases hout with hOk | hb2 | hb3 | hb4 | hb5 | hb6
  · exact Or.inl hOk
  · refine Or.inr ⟨2, ?_⟩
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)) h hb2
    exact fun h' ⟨he, hP⟩ => ⟨he, by decide, Or.inl hP⟩
  · refine Or.inr ⟨3, ?_⟩
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)) h hb3
    exact fun h' ⟨he, hP⟩ => ⟨he, by decide, Or.inr hP⟩
  · refine Or.inr ⟨4, ?_⟩
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)) h hb4
    exact fun h' ⟨he, hP⟩ => ⟨he, by decide, Or.inr hP⟩
  · refine Or.inr ⟨5, ?_⟩
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)) h hb5
    exact fun h' ⟨he, hP⟩ => ⟨he, by decide, Or.inr hP⟩
  · refine Or.inr ⟨6, ?_⟩
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)) h hb6
    exact fun h' ⟨he, hP⟩ => ⟨he, by decide, Or.inr hP⟩

/-- Case-split a disjunctive precondition of an N-branch (the
    `cpsBranchWithin_pre_or` twin for `cpsNBranchWithin`). -/
theorem k67NBranch_pre_or {n : Nat} {entry : Word} {cr : CodeReq}
    {P1 P2 : Assertion} {exits : List (Word × Assertion)}
    (h1 : cpsNBranchWithin n entry cr P1 exits)
    (h2 : cpsNBranchWithin n entry cr P2 exits) :
    cpsNBranchWithin n entry cr (fun h => P1 h ∨ P2 h) exits := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, ha, hb, hd, hu, hor, hRb⟩ := hPR
  rcases hor with hP | hP
  · exact h1 R hR s hcr ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc
  · exact h2 R hR s hcr ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc

/-! ## §2  Fuel-indexed loop invariant -/

/-- The fuel-indexed K67 loop invariant at the loop header (`K + 56`): the
    walk has consumed `i ≤ 14` fields, the durable cursor sits at offset
    `cur ≤ bytes.length`, `j` is the cursor measure, and the walked
    `StrictPrefix` is recorded together with the ommers capture (field 1,
    available from `i ≥ 2`) and the zero-length difficulty fact (field 7,
    available from `i ≥ 8`).  The window end is statically
    `base + ofNat bytes.length` (the caller hands the routine the exact
    header RLP as `bytes`). -/
def k67FuelInv (sp0 base omConst : Word) (bytes : List (BitVec 8))
    (startOff : Nat) (svals : Reg → Word) (v21 : Word) (j : Nat) :
    Assertion := fun h =>
  ∃ (i cur prevLen omEnd omLen : Nat),
    (k67LoopInv sp0 base (base + BitVec.ofNat 64 bytes.length) omConst bytes
        omEnd omLen (fun _ => cur) (fun _ => prevLen) i svals v21 **
      ⌜j = cycleFuel cur bytes.length ∧ cur ≤ bytes.length ∧ i ≤ 14 ∧
        RlpListNthItemSAsm.StrictPrefix bytes base
          (base + BitVec.ofNat 64 bytes.length) startOff i cur ∧
        (2 ≤ i → ∃ n1 l1 : Word,
          RlpListNthItemSAsm.StrictNthItem bytes base
            (base + BitVec.ofNat 64 bytes.length) 1 startOff n1 l1 ∧
          omEnd = (n1 - base).toNat ∧ omLen = l1.toNat) ∧
        (8 ≤ i → ∃ n7 : Word,
          RlpListNthItemSAsm.StrictNthItem bytes base
            (base + BitVec.ofNat 64 bytes.length) 7 startOff n7 0)⌝) h

/-! ## §3  Station posts -/

/-- Difficulty station post at `K + 604`: the walk consumed 7 fields and
    field 7 (difficulty) decoded with a NONZERO content length. -/
def k67Qdiff (sp0 base omConst : Word) (bytes : List (BitVec 8))
    (startOff : Nat) (svals : Reg → Word) (v21 : Word) : Assertion := fun h =>
  ∃ (cur omEnd omLen : Nat) (next7 len7 n1 l1 : Word)
    (v6 v7 v28 v29 v30 v31 : Word),
    (((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ next7) ** (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ len7) **
      (.x8 ↦ᵣ (base + BitVec.ofNat 64 omEnd)) **
      (.x9 ↦ᵣ BitVec.ofNat 64 omLen) **
      (.x18 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
      (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
      (.x20 ↦ᵣ (7 : Word)) ** (.x21 ↦ᵣ v21) **
      (.x5 ↦ᵣ (7 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes ** bytesRegion omConst (k67OmBytes)) **
      ⌜RlpListNthItemSAsm.StrictPrefix bytes base
          (base + BitVec.ofNat 64 bytes.length) startOff 7 cur ∧
        RlpListNthItemSAsm.StrictNthItem bytes base
          (base + BitVec.ofNat 64 bytes.length) 7 startOff next7 len7 ∧
        len7 ≠ (0 : Word) ∧
        RlpListNthItemSAsm.StrictNthItem bytes base
          (base + BitVec.ofNat 64 bytes.length) 1 startOff n1 l1 ∧
        omEnd = (n1 - base).toNat ∧ omLen = l1.toNat ∧
        cur ≤ bytes.length⌝) h

/-- Walk-failure station post at `K + 628`: the walker reported a nonzero
    status at field `i` with cursor offset `cur`. -/
def k67Qfail (sp0 base omConst : Word) (bytes : List (BitVec 8))
    (startOff : Nat) (svals : Reg → Word) (v21 : Word) : Assertion := fun h =>
  ∃ (i cur : Nat) (statusW v8 v9 v5 v6 v7 v28 v29 v30 v31 : Word),
    (((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
      (.x11 ↦ᵣ statusW) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
      (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
      (.x20 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ v21) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes ** bytesRegion omConst (k67OmBytes)) **
      ⌜statusW ≠ (0 : Word) ∧ i ≤ 14 ∧ cur ≤ bytes.length ∧
        RlpListNthItemSAsm.StrictPrefix bytes base
          (base + BitVec.ofNat 64 bytes.length) startOff i cur ∧
        RlpListNthItemSAsm.WalkFailure bytes cur
          (base + BitVec.ofNat 64 cur)
          (base + BitVec.ofNat 64 bytes.length)⌝) h

/-- Clean-exit station post at `K + 116`: all 15 fields walked; the post
    pins the field-14 (nonce) end cursor and content length in `x10`/`x12`
    and the field-1 (ommers) capture in `x8`/`x9`, ready for the post-loop
    byte compares. -/
def k67Qclean (sp0 base omConst : Word) (bytes : List (BitVec 8))
    (startOff : Nat) (svals : Reg → Word) (v21 : Word) : Assertion := fun h =>
  ∃ (cur14 : Nat) (next14 len14 n1 l1 n7 : Word)
    (v6 v7 v28 v29 v30 v31 : Word),
    (((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ len14) **
      (.x8 ↦ᵣ (base + BitVec.ofNat 64 (n1 - base).toNat)) **
      (.x9 ↦ᵣ BitVec.ofNat 64 l1.toNat) **
      (.x18 ↦ᵣ next14) **
      (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
      (.x20 ↦ᵣ (15 : Word)) ** (.x21 ↦ᵣ v21) **
      (.x5 ↦ᵣ (15 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes ** bytesRegion omConst (k67OmBytes)) **
      ⌜RlpListNthItemSAsm.StrictPrefix bytes base
          (base + BitVec.ofNat 64 bytes.length) startOff 15
          ((next14 - base).toNat) ∧
        RlpListNthItemSAsm.StrictNthItem bytes base
          (base + BitVec.ofNat 64 bytes.length) 1 startOff n1 l1 ∧
        RlpListNthItemSAsm.StrictNthItem bytes base
          (base + BitVec.ofNat 64 bytes.length) 7 startOff n7 0 ∧
        RlpListNthItemSAsm.StrictNthItem bytes base
          (base + BitVec.ofNat 64 bytes.length) 14 startOff next14 len14 ∧
        rlpItemDecode bytes cur14 (base + BitVec.ofNat 64 cur14)
          (base + BitVec.ofNat 64 bytes.length) next14 len14 ∧
        cur14 ≤ bytes.length ∧ (next14 - base).toNat ≤ bytes.length⌝) h

/-! ## §4  Cursor-at-end walk step -/

set_option maxRecDepth 4000 in
/-- The walk call when the cursor has already reached the window end:
    `rlp_walk_next` takes its early status-2 return
    (`rlp_walk_next_end_spec_within`, which needs no memory premises), and
    the status dispatch routes to the status-4 station at `K + 628`. -/
theorem k67LoopCallEnd
    (sp0 base omConst raVal v8 v9 v12 endPtr iW x10Old x11Old v21
      v5 v6 v7 v28 v29 v30 v31 : Word) (svals : Reg → Word)
    (bytes : List (BitVec 8)) (off : Nat)
    (h_end : ¬ BitVec.ult (base + BitVec.ofNat 64 off) endPtr = true) :
    cpsTripleWithin (2 + (1 + 4) + 1) (K + 56) (K + 628) fullCode
      ((.x1 ↦ᵣ raVal) ** (.x12 ↦ᵣ v12) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x13 ** regOwn .x14 **
        bytesRegion base bytes ** (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ (base + BitVec.ofNat 64 off)) ** (.x19 ↦ᵣ endPtr) **
        (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
        bytesRegion omConst (k67OmBytes))
      ((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ (base + BitVec.ofNat 64 off)) **
        (.x11 ↦ᵣ (2 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ (base + BitVec.ofNat 64 off)) ** (.x19 ↦ᵣ endPtr) **
        (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
        bytesRegion base bytes ** bytesRegion omConst (k67OmBytes) **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12)))) := by
  have h14 : cpsTripleWithin 1 (K + 56) (K + 56 + 4)
      (CodeReq.singleton (K + 56) (.MV .x10 .x18))
      ((.x18 ↦ᵣ (base + BitVec.ofNat 64 off)) ** (.x10 ↦ᵣ x10Old))
      ((.x18 ↦ᵣ (base + BitVec.ofNat 64 off)) **
        (.x10 ↦ᵣ (base + BitVec.ofNat 64 off))) :=
    mv_spec_gen_within .x10 .x18 (base + BitVec.ofNat 64 off) x10Old
      (K + 56) (by decide)
  have h15 : cpsTripleWithin 1 (K + 60) (K + 60 + 4)
      (CodeReq.singleton (K + 60) (.MV .x11 .x19))
      ((.x19 ↦ᵣ endPtr) ** (.x11 ↦ᵣ x11Old))
      ((.x19 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) :=
    mv_spec_gen_within .x11 .x19 endPtr x11Old (K + 60) (by decide)
  have h14C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 56) k67Prog 14 (.MV .x10 .x18)
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h14
  have h15C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 60) k67Prog 15 (.MV .x11 .x19)
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h15
  have hG14 : ((.x1 ↦ᵣ raVal) ** (.x12 ↦ᵣ v12) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ v8) ** regOwn .x13 **
      regOwn .x14 ** bytesRegion base bytes **
      (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x9 ↦ᵣ v9) **
      (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion omConst (k67OmBytes) ** (.x19 ↦ᵣ endPtr) **
      (.x11 ↦ᵣ x11Old)).pcFree := by
    repeat' first
      | exact pcFree_regIs | exact pcFree_memIs | exact pcFree_memOwn
      | exact pcFree_regOwn | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _ | exact bytesRegion_pcFree _ _
      | exact pcFree_emp
  have hG15 : ((.x1 ↦ᵣ raVal) ** (.x12 ↦ᵣ v12) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ v8) ** regOwn .x13 **
      regOwn .x14 ** bytesRegion base bytes **
      (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x9 ↦ᵣ v9) **
      (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion omConst (k67OmBytes) **
      (.x18 ↦ᵣ (base + BitVec.ofNat 64 off)) **
      (.x10 ↦ᵣ (base + BitVec.ofNat 64 off))).pcFree := by
    repeat' first
      | exact pcFree_regIs | exact pcFree_memIs | exact pcFree_memOwn
      | exact pcFree_regOwn | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _ | exact bytesRegion_pcFree _ _
      | exact pcFree_emp
  have h14F := cpsTripleWithin_frameR _ hG14 h14C
  have h15F := cpsTripleWithin_frameR _ hG15 h15C
  have hmv := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h14F h15F
  have hF : ((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ (base + BitVec.ofNat 64 off)) ** (.x19 ↦ᵣ endPtr) **
        (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) **
        regOwn .x13 ** regOwn .x14 **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
        bytesRegion omConst (k67OmBytes)).pcFree := by
    repeat' first
      | exact pcFree_regIs | exact pcFree_memIs | exact pcFree_memOwn
      | exact pcFree_regOwn | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _ | exact bytesRegion_pcFree _ _
      | exact pcFree_emp
  -- the end-of-window walk call at [16] (K + 64)
  have hend0 := rlp_walk_next_end_spec_within wnBase
    (base + BitVec.ofNat 64 off) endPtr (K + 68) v12 h_end
  have hG : ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      bytesRegion base bytes ** ((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ (base + BitVec.ofNat 64 off)) ** (.x19 ↦ᵣ endPtr) **
        (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) **
        regOwn .x13 ** regOwn .x14 **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
        bytesRegion omConst (k67OmBytes))).pcFree := by
    repeat' first
      | exact pcFree_regIs | exact pcFree_memIs | exact pcFree_memOwn
      | exact pcFree_regOwn | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _ | exact bytesRegion_pcFree _ _
      | exact pcFree_emp
  have hendF := cpsTripleWithin_frameR _ hG hend0
  have hend' := cpsTripleWithin_weaken
    (P' := (.x1 ↦ᵣ (K + 68)) **
      ((.x10 ↦ᵣ (base + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ endPtr) **
       (.x12 ↦ᵣ v12) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       bytesRegion base bytes ** ((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
         (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
         (.x18 ↦ᵣ (base + BitVec.ofNat 64 off)) ** (.x19 ↦ᵣ endPtr) **
         (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) **
         regOwn .x13 ** regOwn .x14 **
         frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
         bytesRegion omConst (k67OmBytes))))
    (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) hendF
  have hc := RlpWalkCallSAsm.rlp_walk_next_call_within (K + 64) wnBase raVal k67NextOffset
    (by repeat' first
      | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_memIs
      | exact pcFree_regOwn | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _)
    (by simp only [k67NextOffset, K, wnBase]; decide)
    (by simp only [K]; decide)
    (by
      simp only [K, wnBase]
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (fun a i hi =>
      CodeReq.union_split_mono
        (fun a' i' h' => k67_mono a' i'
          (CodeReq.ofProg_mem_at K (K + 64) k67Prog 16 (.JAL .x1 k67NextOffset)
            (by unfold K; bv_omega)
            (by rw [k67_length]; decide)
            rfl
            (by decide) a' i' h'))
        next_mono a i hi)
    hend'
  have hmv' : cpsTripleWithin (1 + 1) (K + 56) (K + 60 + 4)
      (CodeReq.ofProg K k67Prog)
      (((.x18 ↦ᵣ (base + BitVec.ofNat 64 off)) ** (.x10 ↦ᵣ x10Old)) **
        (.x1 ↦ᵣ raVal) ** (.x12 ↦ᵣ v12) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ v8) ** regOwn .x13 **
        regOwn .x14 ** bytesRegion base bytes **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** (.x9 ↦ᵣ v9) **
        (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
        bytesRegion omConst (k67OmBytes) ** (.x19 ↦ᵣ endPtr) **
        (.x11 ↦ᵣ x11Old))
      ((.x1 ↦ᵣ raVal) ** ((.x10 ↦ᵣ (base + BitVec.ofNat 64 off)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ v12) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion base bytes **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ (base + BitVec.ofNat 64 off)) ** (.x19 ↦ᵣ endPtr) **
        (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) **
        regOwn .x13 ** regOwn .x14 **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
        bytesRegion omConst (k67OmBytes))) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => by xperm_hyp hq) hmv
  have hmvF := cpsTripleWithin_extend_code k67_mono hmv'
  rw [show K + 60 + 4 = K + 64 from by bv_omega] at hmvF
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hmvF hc
  -- status dispatch: x11 = 2 ≠ 0, so BNE [17] takes to K + 628
  have hfail0 := k67LoopFail sp0 base omConst (base + BitVec.ofNat 64 off)
    endPtr (2 : Word) iW v8 v9 v21 v5 v6 v7 v28 v29 v30 v31 svals bytes
    (by decide)
  have hfail := cpsTripleWithin_frameR
    (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) pcFree_regIs hfail0
  have hseq2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hseq hfail
  have hn : (1 + 1) + (1 + 4) + 1 = 2 + (1 + 4) + 1 := by omega
  rw [hn] at hseq2
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq2

/-! ## §5  Pin-to-ownership conversion for invariant rebuild -/

/-- Convert the ten pinned scratch/pass-through registers of an arm
    postcondition into the `regOwn` chain the loop invariant carries.  The
    peel direction (own → pin) is `cpsNBranchWithin_of_forall_regIs_to_regOwn`;
    this is the pointwise rebuild direction used when re-establishing
    `k67LoopInv` at the loop-back edge. -/
theorem k67Pins10_to_regOwns :
    ∀ (v1 v5 v6 v7 v10 v11 v28 v29 v30 v31 : Word) h,
      ((.x1 ↦ᵣ v1) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)) h →
      (regOwn .x1 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x10 ** regOwn .x11 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31) h := by
  intro v1 v5 v6 v7 v10 v11 v28 v29 v30 v31 h hp
  obtain ⟨g0, g9, d0, u0, h1, hp⟩ := hp
  obtain ⟨g0', g8, d1, u1, h5, hp⟩ := hp
  obtain ⟨g1', g7', d2, u2, h6, hp⟩ := hp
  obtain ⟨g2', g6', d3, u3, h7, hp⟩ := hp
  obtain ⟨g3', g5', d4, u4, h10, hp⟩ := hp
  obtain ⟨g4', g4'', d5, u5, h11, hp⟩ := hp
  obtain ⟨g5'', g3'', d6, u6, h28, hp⟩ := hp
  obtain ⟨g6'', g2'', d7, u7, h29, hp⟩ := hp
  obtain ⟨g7'', g1'', d8, u8, h30, h31⟩ := hp
  exact ⟨g0, g9, d0, u0, ⟨v1, h1⟩,
    g0', g8, d1, u1, ⟨v5, h5⟩,
    g1', g7', d2, u2, ⟨v6, h6⟩,
    g2', g6', d3, u3, ⟨v7, h7⟩,
    g3', g5', d4, u4, ⟨v10, h10⟩,
    g4', g4'', d5, u5, ⟨v11, h11⟩,
    g5'', g3'', d6, u6, ⟨v28, h28⟩,
    g6'', g2'', d7, u7, ⟨v29, h29⟩,
    g7'', g1'', d8, u8, ⟨v30, h30⟩, ⟨v31, h31⟩⟩

/-- Two-pin analogue of `k67Pins10_to_regOwns`, used to turn the peeled
    `x13`/`x14` pins back into the `regOwn` atoms that the dispatch frame and
    the arm pre-shapes expect. -/
theorem k67Pins2_to_regOwns :
    ∀ (v13 v14 : Word) h,
      ((.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)) h →
      (regOwn .x13 ** regOwn .x14) h := by
  intro v13 v14 h hp
  obtain ⟨g0, g1, d0, u0, h13, h14⟩ := hp
  exact ⟨g0, g1, d0, u0, ⟨v13, h13⟩, ⟨v14, h14⟩⟩

/-! ## Continuations: `(K+72)` post-dispatch arms with child-invariant rebuild -/

/-- Shared post-dispatch register/memory state at `K+72` (the point after the
    `BNE x11, x0, +560` fall-through): the arm pre-shape of
    `k67LoopContO/Cont1/Cont7/Diff/Exit` with the stack pointer framed in and the
    `x8`/`x9` pass-throughs specialized to the loop invariant's `i ≤ 1` conditional
    values.  The pure walker facts travel as hypotheses of the continuation
    theorems, not in this assertion. -/
def k67ArmPre
    (sp0 base omConst endPtr : Word) (bytes : List (BitVec 8))
    (i cur omEnd omLen : Nat) (next lenW v21 v5 v6 v7 v28 v29 v30 v31 : Word)
    (svals : Reg → Word) : Assertion :=
  (.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ 0) ** (.x12 ↦ᵣ lenW) **
  (.x8 ↦ᵣ (if i ≤ 1 then base else base + BitVec.ofNat 64 omEnd)) **
  (.x9 ↦ᵣ (if i ≤ 1 then BitVec.ofNat 64 bytes.length else BitVec.ofNat 64 omLen)) **
  (.x18 ↦ᵣ (base + BitVec.ofNat 64 cur)) ** (.x19 ↦ᵣ endPtr) **
  (.x20 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ v21) **
  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
  regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ 0) **
  (.x2 ↦ᵣ (sp0 + signExtend12 (-48))) **
  frameSlotsSaved k67Frame (sp0 + signExtend12 (-48)) svals **
  bytesRegion base bytes ** bytesRegion omConst k67OmBytes

/-- Fold the per-pin conditional `x8`/`x9` pass-through values produced by the arm
    theorems into `k67LoopInv`'s single conditional atom. -/
theorem k67IfPair_fold (c : Prop) [Decidable c] (a b a' b' : Word) :
    ∀ h, ((.x8 ↦ᵣ (if c then a else b)) ** (.x9 ↦ᵣ (if c then a' else b'))) h →
      (if c then ((.x8 ↦ᵣ a) ** (.x9 ↦ᵣ a')) else ((.x8 ↦ᵣ b) ** (.x9 ↦ᵣ b'))) h := by
  intro h hp
  by_cases hc : c
  · simp only [if_pos hc] at hp ⊢; exact hp
  · simp only [if_neg hc] at hp ⊢; exact hp

/-- The four-exit list every continuation targets (the three stations plus the
    loop-back edge carrying a strictly smaller fuel child invariant). -/
def k67Exits4
    (sp0 base omConst : Word) (bytes : List (BitVec 8)) (startOff : Nat)
    (svals : Reg → Word) (v21 : Word) (j : Nat) :
    List (Word × Assertion) :=
  [ (K + 604, k67Qdiff sp0 base omConst bytes startOff svals v21),
    (K + 628, k67Qfail sp0 base omConst bytes startOff svals v21),
    (K + 116, k67Qclean sp0 base omConst bytes startOff svals v21),
    (K + 56, fun h => ∃ child, child < j ∧
      k67FuelInv sp0 base omConst bytes startOff svals v21 child h) ]

/-- Continuation for the "other" arm: at fields `i ∉ {1, 7, 14}` the loop body
    performs no capture and no exit; the child invariant at `i + 1` keeps the
    ommers pass-through values unchanged. -/
theorem k67RoundContO
    (sp0 base omConst : Word) (bytes : List (BitVec 8))
    (i cur omEnd omLen startOff j : Nat) (next lenW v21 v5 v6 v7 v28 v29 v30 v31 : Word)
    (svals : Reg → Word)
    (hio1 : BitVec.ofNat 64 i ≠ 1) (hio7 : BitVec.ofNat 64 i ≠ 7)
    (hio14 : BitVec.ofNat 64 i ≠ 14)
    (hj : j = cycleFuel cur bytes.length) (hcur : cur ≤ bytes.length) (hile : i ≤ 14)
    (hprefix : StrictPrefix bytes base (base + BitVec.ofNat 64 bytes.length) startOff i cur)
    (hcap1 : 2 ≤ i → ∃ n1 l1, StrictNthItem bytes base (base + BitVec.ofNat 64 bytes.length) 1
      startOff n1 l1 ∧ omEnd = (n1 - base).toNat ∧ omLen = l1.toNat)
    (hcap7 : 8 ≤ i → ∃ n7, StrictNthItem bytes base (base + BitVec.ofNat 64 bytes.length) 7
      startOff n7 0)
    (hdecode : rlpItemDecode bytes cur (base + BitVec.ofNat 64 cur)
      (base + BitVec.ofNat 64 bytes.length) next lenW)
    (hover9 : base.toNat + bytes.length + 9 < 2 ^ 64) :
    cpsNBranchWithin 10 (K + 72) fullCode
      (k67ArmPre sp0 base omConst (base + BitVec.ofNat 64 bytes.length) bytes i cur omEnd omLen
        next lenW v21 v5 v6 v7 v28 v29 v30 v31 svals)
      (k67Exits4 sp0 base omConst bytes startOff svals v21 j) := by
  have hni1 : i ≠ 1 := fun h => hio1 (by rw [h]; decide)
  have hni7 : i ≠ 7 := fun h => hio7 (by rw [h]; decide)
  have hni14 : i ≠ 14 := fun h => hio14 (by rw [h]; decide)
  obtain ⟨hnextE, hlt, hle, hprefix'⟩ :=
    StrictPrefix.step_bounds hprefix hdecode hcur hover9
  have harm := cpsTripleWithin_frameR (.x2 ↦ᵣ (sp0 + signExtend12 (-48))) pcFree_regIs
    (k67LoopContO sp0 base omConst (base + BitVec.ofNat 64 cur)
      (base + BitVec.ofNat 64 bytes.length) lenW (BitVec.ofNat 64 i) next v21
      v5 v6 v7 (if i ≤ 1 then base else base + BitVec.ofNat 64 omEnd)
      (if i ≤ 1 then BitVec.ofNat 64 bytes.length else BitVec.ofNat 64 omLen)
      v28 v29 v30 v31 bytes svals hio1 hio7 hio14)
  apply cpsNBranchWithin_mono_nSteps (show 8 ≤ 10 by omega)
  apply cpsNBranchWithin_of_triple
    (Q := fun h => ∃ child, child < j ∧
      k67FuelInv sp0 base omConst bytes startOff svals v21 child h)
    (by unfold k67Exits4
        repeat' first
          | apply List.Mem.head
          | apply List.Mem.tail)
  refine cpsTripleWithin_weaken (fun _ hp => by unfold k67ArmPre at hp; xperm_hyp hp)
    ?_ harm
  intro h hq
  refine ⟨cycleFuel ((next - base).toNat) bytes.length, ?_, ?_⟩
  · rw [hj]; exact cycleFuel_strict_of_advance hlt hle
  · refine ⟨i + 1, (next - base).toNat, lenW.toNat, omEnd, omLen, ?_⟩
    refine (sepConj_pure_right _).2 ⟨?_, ⟨rfl, hle, by omega, hprefix',
      fun h2 => hcap1 (by omega), fun h8 => hcap7 (by omega)⟩⟩
    unfold k67LoopInv
    simp only []
    simp only [show (i + 1 ≤ 1) ↔ (i ≤ 1) from by omega]
    rw [show BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 i + 1 from by bv_omega,
      show BitVec.ofNat 64 lenW.toNat = lenW from by bv_omega, ← hnextE]
    have hP : (((.x8 ↦ᵣ (if i ≤ 1 then base else base + BitVec.ofNat 64 omEnd)) **
        (.x9 ↦ᵣ (if i ≤ 1 then BitVec.ofNat 64 bytes.length else BitVec.ofNat 64 omLen)) **
        (.x12 ↦ᵣ lenW) ** (.x18 ↦ᵣ next) ** (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
        (.x20 ↦ᵣ (BitVec.ofNat 64 i + 1)) ** (.x21 ↦ᵣ v21) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ 0) **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48))) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48)) svals **
        bytesRegion base bytes ** bytesRegion omConst k67OmBytes) **
        ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ 15) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ 0) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
          (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))) h := by xperm_hyp hq
    have hconv := sepConj_mono_right
      (k67Pins10_to_regOwns (K + 68) 15 v6 v7 next 0 v28 v29 v30 v31) h hP
    have hsplit : (((.x12 ↦ᵣ lenW) ** (.x18 ↦ᵣ next) **
        (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
        (.x20 ↦ᵣ (BitVec.ofNat 64 i + 1)) ** (.x21 ↦ᵣ v21) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ 0) **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48))) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48)) svals **
        bytesRegion base bytes ** bytesRegion omConst k67OmBytes **
        (regOwn .x1 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x10 ** regOwn .x11 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31)) **
        ((.x8 ↦ᵣ (if i ≤ 1 then base else base + BitVec.ofNat 64 omEnd)) **
          (.x9 ↦ᵣ (if i ≤ 1 then BitVec.ofNat 64 bytes.length
            else BitVec.ofNat 64 omLen)))) h := by xperm_hyp hconv
    have hconv2 := sepConj_mono_right
      (k67IfPair_fold _ _ _ _ _) h hsplit
    xperm_hyp hconv2

/-- Continuation for field 1 (ommers): the loop body captures the field's end
    cursor and content length into `x8`/`x9`; the child invariant at `i = 2`
    records the capture via `StrictNthItem 1`. -/
theorem k67RoundCont1
    (sp0 base omConst : Word) (bytes : List (BitVec 8))
    (i cur omEnd omLen startOff j : Nat) (next lenW v21 v5 v6 v7 v28 v29 v30 v31 : Word)
    (svals : Reg → Word)
    (hi1 : BitVec.ofNat 64 i = 1)
    (hj : j = cycleFuel cur bytes.length) (hcur : cur ≤ bytes.length) (hile : i ≤ 14)
    (hprefix : StrictPrefix bytes base (base + BitVec.ofNat 64 bytes.length) startOff i cur)
    (hcap1 : 2 ≤ i → ∃ n1 l1, StrictNthItem bytes base (base + BitVec.ofNat 64 bytes.length) 1
      startOff n1 l1 ∧ omEnd = (n1 - base).toNat ∧ omLen = l1.toNat)
    (hcap7 : 8 ≤ i → ∃ n7, StrictNthItem bytes base (base + BitVec.ofNat 64 bytes.length) 7
      startOff n7 0)
    (hdecode : rlpItemDecode bytes cur (base + BitVec.ofNat 64 cur)
      (base + BitVec.ofNat 64 bytes.length) next lenW)
    (hover9 : base.toNat + bytes.length + 9 < 2 ^ 64) :
    cpsNBranchWithin 10 (K + 72) fullCode
      (k67ArmPre sp0 base omConst (base + BitVec.ofNat 64 bytes.length) bytes i cur omEnd omLen
        next lenW v21 v5 v6 v7 v28 v29 v30 v31 svals)
      (k67Exits4 sp0 base omConst bytes startOff svals v21 j) := by
  have hiE : i = 1 := by bv_omega
  subst hiE
  obtain ⟨hnextE, hlt, hle, hprefix'⟩ :=
    StrictPrefix.step_bounds hprefix hdecode hcur hover9
  have harm := cpsTripleWithin_frameR (.x2 ↦ᵣ (sp0 + signExtend12 (-48))) pcFree_regIs
    (k67LoopCont1 sp0 base omConst (base + BitVec.ofNat 64 cur)
      (base + BitVec.ofNat 64 bytes.length) lenW (BitVec.ofNat 64 1) next v21
      v5 v6 v7 base (BitVec.ofNat 64 bytes.length)
      v28 v29 v30 v31 bytes svals rfl)
  apply cpsNBranchWithin_mono_nSteps (show 10 ≤ 10 by omega)
  apply cpsNBranchWithin_of_triple
    (Q := fun h => ∃ child, child < j ∧
      k67FuelInv sp0 base omConst bytes startOff svals v21 child h)
    (by unfold k67Exits4
        apply List.Mem.tail; apply List.Mem.tail; apply List.Mem.tail
        apply List.Mem.head)
  refine cpsTripleWithin_weaken (fun _ hp => by
    unfold k67ArmPre at hp
    simp only [show (1 ≤ 1) ↔ True from by decide, if_true] at hp
    xperm_hyp hp) ?_ harm
  intro h hq
  refine ⟨cycleFuel ((next - base).toNat) bytes.length, ?_, ?_⟩
  · rw [hj]; exact cycleFuel_strict_of_advance hlt hle
  · refine ⟨2, (next - base).toNat, lenW.toNat, (next - base).toNat, lenW.toNat, ?_⟩
    refine (sepConj_pure_right _).2 ⟨?_, ⟨rfl, hle, by omega, hprefix',
      fun _ => ⟨next, lenW, StrictPrefix.select hprefix hdecode, rfl, rfl⟩,
      fun h8 => absurd h8 (by omega)⟩⟩
    unfold k67LoopInv
    simp only []
    simp only [show (2 ≤ 1) ↔ False from by decide, if_false]
    rw [show BitVec.ofNat 64 (1 + 1) = BitVec.ofNat 64 1 + 1 from by bv_omega,
      show BitVec.ofNat 64 lenW.toNat = lenW from by bv_omega, ← hnextE]
    have hP : (((.x8 ↦ᵣ next) ** (.x9 ↦ᵣ lenW) **
        (.x12 ↦ᵣ lenW) ** (.x18 ↦ᵣ next) ** (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
        (.x20 ↦ᵣ (BitVec.ofNat 64 1 + 1)) ** (.x21 ↦ᵣ v21) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ 0) **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48))) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48)) svals **
        bytesRegion base bytes ** bytesRegion omConst k67OmBytes) **
        ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ 15) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ 0) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
          (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))) h := by xperm_hyp hq
    have hconv := sepConj_mono_right
      (k67Pins10_to_regOwns (K + 68) 15 v6 v7 next 0 v28 v29 v30 v31) h hP
    xperm_hyp hconv

/-- Continuation for field 7 (difficulty) with a zero content length: the walk
    continues and the child invariant at `i = 8` records the zero-length
    difficulty via `StrictNthItem 7 … 0`. -/
theorem k67RoundCont7
    (sp0 base omConst : Word) (bytes : List (BitVec 8))
    (i cur omEnd omLen startOff j : Nat) (next lenW v21 v5 v6 v7 v28 v29 v30 v31 : Word)
    (svals : Reg → Word)
    (hi7 : BitVec.ofNat 64 i = 7) (hlen0 : lenW = 0)
    (hj : j = cycleFuel cur bytes.length) (hcur : cur ≤ bytes.length) (hile : i ≤ 14)
    (hprefix : StrictPrefix bytes base (base + BitVec.ofNat 64 bytes.length) startOff i cur)
    (hcap1 : 2 ≤ i → ∃ n1 l1, StrictNthItem bytes base (base + BitVec.ofNat 64 bytes.length) 1
      startOff n1 l1 ∧ omEnd = (n1 - base).toNat ∧ omLen = l1.toNat)
    (hcap7 : 8 ≤ i → ∃ n7, StrictNthItem bytes base (base + BitVec.ofNat 64 bytes.length) 7
      startOff n7 0)
    (hdecode : rlpItemDecode bytes cur (base + BitVec.ofNat 64 cur)
      (base + BitVec.ofNat 64 bytes.length) next lenW)
    (hover9 : base.toNat + bytes.length + 9 < 2 ^ 64) :
    cpsNBranchWithin 10 (K + 72) fullCode
      (k67ArmPre sp0 base omConst (base + BitVec.ofNat 64 bytes.length) bytes i cur omEnd omLen
        next lenW v21 v5 v6 v7 v28 v29 v30 v31 svals)
      (k67Exits4 sp0 base omConst bytes startOff svals v21 j) := by
  have hiE : i = 7 := by bv_omega
  subst hiE
  subst hlen0
  obtain ⟨hnextE, hlt, hle, hprefix'⟩ :=
    StrictPrefix.step_bounds hprefix hdecode hcur hover9
  have harm := cpsTripleWithin_frameR (.x2 ↦ᵣ (sp0 + signExtend12 (-48))) pcFree_regIs
    (k67LoopCont7 sp0 base omConst (base + BitVec.ofNat 64 cur)
      (base + BitVec.ofNat 64 bytes.length) 0 (BitVec.ofNat 64 7) next v21
      v5 v6 v7 (base + BitVec.ofNat 64 omEnd) (BitVec.ofNat 64 omLen)
      v28 v29 v30 v31 bytes svals rfl rfl)
  apply cpsNBranchWithin_mono_nSteps (show 9 ≤ 10 by omega)
  apply cpsNBranchWithin_of_triple
    (Q := fun h => ∃ child, child < j ∧
      k67FuelInv sp0 base omConst bytes startOff svals v21 child h)
    (by unfold k67Exits4
        repeat' first
          | apply List.Mem.head
          | apply List.Mem.tail)
  refine cpsTripleWithin_weaken (fun _ hp => by
    unfold k67ArmPre at hp
    simp only [show (7 ≤ 1) ↔ False from by decide, if_false] at hp
    xperm_hyp hp) ?_ harm
  intro h hq
  refine ⟨cycleFuel ((next - base).toNat) bytes.length, ?_, ?_⟩
  · rw [hj]; exact cycleFuel_strict_of_advance hlt hle
  · refine ⟨8, (next - base).toNat, (0 : Word).toNat, omEnd, omLen, ?_⟩
    refine (sepConj_pure_right _).2 ⟨?_, ⟨rfl, hle, by omega, hprefix',
      fun _ => hcap1 (by omega),
      fun _ => ⟨next, StrictPrefix.select hprefix hdecode⟩⟩⟩
    unfold k67LoopInv
    simp only []
    simp only [show (8 ≤ 1) ↔ False from by decide, if_false]
    rw [show BitVec.ofNat 64 (7 + 1) = BitVec.ofNat 64 7 + 1 from by bv_omega,
      show BitVec.ofNat 64 (0 : Word).toNat = 0 from by decide, ← hnextE]
    have hP : (((.x8 ↦ᵣ (base + BitVec.ofNat 64 omEnd)) ** (.x9 ↦ᵣ BitVec.ofNat 64 omLen) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x18 ↦ᵣ next) **
        (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
        (.x20 ↦ᵣ (BitVec.ofNat 64 7 + 1)) ** (.x21 ↦ᵣ v21) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ 0) **
        (.x2 ↦ᵣ (sp0 + signExtend12 (-48))) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48)) svals **
        bytesRegion base bytes ** bytesRegion omConst k67OmBytes) **
        ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ 15) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ 0) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
          (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))) h := by xperm_hyp hq
    have hconv := sepConj_mono_right
      (k67Pins10_to_regOwns (K + 68) 15 v6 v7 next 0 v28 v29 v30 v31) h hP
    xperm_hyp hconv

/-- Continuation for field 7 (difficulty) with a NONZERO content length: the
    loop exits to the status-1 station at `K + 604`. -/
theorem k67RoundDiff
    (sp0 base omConst : Word) (bytes : List (BitVec 8))
    (i cur omEnd omLen startOff j : Nat) (next lenW v21 v5 v6 v7 v28 v29 v30 v31 : Word)
    (svals : Reg → Word)
    (hi7 : BitVec.ofNat 64 i = 7) (hne : lenW ≠ 0)
    (_hj : j = cycleFuel cur bytes.length) (hcur : cur ≤ bytes.length) (hile : i ≤ 14)
    (hprefix : StrictPrefix bytes base (base + BitVec.ofNat 64 bytes.length) startOff i cur)
    (hcap1 : 2 ≤ i → ∃ n1 l1, StrictNthItem bytes base (base + BitVec.ofNat 64 bytes.length) 1
      startOff n1 l1 ∧ omEnd = (n1 - base).toNat ∧ omLen = l1.toNat)
    (hcap7 : 8 ≤ i → ∃ n7, StrictNthItem bytes base (base + BitVec.ofNat 64 bytes.length) 7
      startOff n7 0)
    (hdecode : rlpItemDecode bytes cur (base + BitVec.ofNat 64 cur)
      (base + BitVec.ofNat 64 bytes.length) next lenW)
    (_hover9 : base.toNat + bytes.length + 9 < 2 ^ 64) :
    cpsNBranchWithin 10 (K + 72) fullCode
      (k67ArmPre sp0 base omConst (base + BitVec.ofNat 64 bytes.length) bytes i cur omEnd omLen
        next lenW v21 v5 v6 v7 v28 v29 v30 v31 svals)
      (k67Exits4 sp0 base omConst bytes startOff svals v21 j) := by
  have hiE : i = 7 := by bv_omega
  subst hiE
  obtain ⟨n1, l1, hS1, homE, homL⟩ := hcap1 (by omega)
  have harm := k67LoopDiff sp0 base omConst (base + BitVec.ofNat 64 cur)
    (base + BitVec.ofNat 64 bytes.length) lenW (BitVec.ofNat 64 7) next v21
    v6 v7 v28 v29 v30 v31 (base + BitVec.ofNat 64 omEnd) (BitVec.ofNat 64 omLen)
    v5 bytes svals rfl hne
  apply cpsNBranchWithin_mono_nSteps (show 5 ≤ 10 by omega)
  apply cpsNBranchWithin_of_triple
    (Q := k67Qdiff sp0 base omConst bytes startOff svals v21)
    (by unfold k67Exits4; apply List.Mem.head)
  refine cpsTripleWithin_weaken (fun _ hp => by
    unfold k67ArmPre at hp
    simp only [show (7 ≤ 1) ↔ False from by decide, if_false] at hp
    xperm_hyp hp) ?_ harm
  intro h hq
  rw [show BitVec.ofNat 64 7 = (7 : Word) from by decide] at hq
  refine ⟨cur, omEnd, omLen, next, lenW, n1, l1, v6, v7, v28, v29, v30, v31, ?_⟩
  refine (sepConj_pure_right _).2 ⟨?_,
    ⟨hprefix, StrictPrefix.select hprefix hdecode, hne, hS1, homE, homL, hcur⟩⟩
  xperm_hyp hq

/-- Continuation for field 14 (nonce): the loop exits cleanly to the `K + 116`
    post-loop entry with the nonce end cursor in `x10` and content length in
    `x12`, and the ommers capture live in `x8`/`x9`. -/
theorem k67RoundExit
    (sp0 base omConst : Word) (bytes : List (BitVec 8))
    (i cur omEnd omLen startOff j : Nat) (next lenW v21 v5 v6 v7 v28 v29 v30 v31 : Word)
    (svals : Reg → Word)
    (hi14 : BitVec.ofNat 64 i = 14)
    (_hj : j = cycleFuel cur bytes.length) (hcur : cur ≤ bytes.length) (hile : i ≤ 14)
    (hprefix : StrictPrefix bytes base (base + BitVec.ofNat 64 bytes.length) startOff i cur)
    (hcap1 : 2 ≤ i → ∃ n1 l1, StrictNthItem bytes base (base + BitVec.ofNat 64 bytes.length) 1
      startOff n1 l1 ∧ omEnd = (n1 - base).toNat ∧ omLen = l1.toNat)
    (hcap7 : 8 ≤ i → ∃ n7, StrictNthItem bytes base (base + BitVec.ofNat 64 bytes.length) 7
      startOff n7 0)
    (hdecode : rlpItemDecode bytes cur (base + BitVec.ofNat 64 cur)
      (base + BitVec.ofNat 64 bytes.length) next lenW)
    (hover9 : base.toNat + bytes.length + 9 < 2 ^ 64) :
    cpsNBranchWithin 10 (K + 72) fullCode
      (k67ArmPre sp0 base omConst (base + BitVec.ofNat 64 bytes.length) bytes i cur omEnd omLen
        next lenW v21 v5 v6 v7 v28 v29 v30 v31 svals)
      (k67Exits4 sp0 base omConst bytes startOff svals v21 j) := by
  have hiE : i = 14 := by bv_omega
  subst hiE
  obtain ⟨hnextE, hlt, hle, hprefix'⟩ :=
    StrictPrefix.step_bounds hprefix hdecode hcur hover9
  obtain ⟨n1, l1, hS1, homE, homL⟩ := hcap1 (by omega)
  obtain ⟨n7, hS7⟩ := hcap7 (by omega)
  have harm := cpsTripleWithin_frameR (.x2 ↦ᵣ (sp0 + signExtend12 (-48))) pcFree_regIs
    (k67LoopExit sp0 base omConst (base + BitVec.ofNat 64 cur)
      (base + BitVec.ofNat 64 bytes.length) lenW (BitVec.ofNat 64 14) next v21
      v5 v6 v7 (base + BitVec.ofNat 64 omEnd) (BitVec.ofNat 64 omLen)
      v28 v29 v30 v31 bytes svals rfl)
  apply cpsNBranchWithin_mono_nSteps (show 8 ≤ 10 by omega)
  apply cpsNBranchWithin_of_triple
    (Q := k67Qclean sp0 base omConst bytes startOff svals v21)
    (by unfold k67Exits4
        repeat' first
          | apply List.Mem.head
          | apply List.Mem.tail)
  refine cpsTripleWithin_weaken (fun _ hp => by
    unfold k67ArmPre at hp
    simp only [show (14 ≤ 1) ↔ False from by decide, if_false] at hp
    xperm_hyp hp) ?_ harm
  intro h hq
  rw [homE, homL, show BitVec.ofNat 64 14 + 1 = 15 from by decide] at hq
  refine ⟨cur, next, lenW, n1, l1, n7, v6, v7, v28, v29, v30, v31, ?_⟩
  refine (sepConj_pure_right _).2 ⟨?_,
    ⟨hprefix', hS1, hS7, StrictPrefix.select hprefix hdecode, hdecode, hcur, hle⟩⟩
  xperm_hyp hq

/-! ## §7  The round contract -/

/-- One round of the field-scan loop: from the loop header at `K + 56` with
    loop state `k67FuelInv j`, control either continues at the header with a
    strictly smaller fuel, or reaches one of the three station PCs
    (difficulty reject `K + 604`, walk failure `K + 628`, clean exit
    `K + 116`).  One round costs at most 101 instructions
    (90 call + 1 dispatch + 10 for the longest arm, the `i = 1` capture). -/
def k67LoopRound
    (sp0 base omConst : Word) (bytes : List (BitVec 8))
    (startOff : Nat) (svals : Reg → Word) (v21 : Word)
    (hsalign : base.toNat % 8 = 0)
    (hover9 : base.toNat + bytes.length + 9 < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (base + BitVec.ofNat 64 k) = true)
    (j : Nat) :
    K67RoundContract j (k67FuelInv sp0 base omConst bytes startOff svals v21)
      (k67Qdiff sp0 base omConst bytes startOff svals v21)
      (k67Qfail sp0 base omConst bytes startOff svals v21)
      (k67Qclean sp0 base omConst bytes startOff svals v21) := by
  refine ⟨101, ?_⟩
  unfold k67FuelInv
  apply cpsNBranchWithin_exists_pre; intro i
  apply cpsNBranchWithin_exists_pre; intro cur
  apply cpsNBranchWithin_exists_pre; intro prevLen
  apply cpsNBranchWithin_exists_pre; intro omEnd
  apply cpsNBranchWithin_exists_pre; intro omLen
  apply cpsNBranchWithin_pure_pre
  rintro ⟨hj, hcur, hile, hprefix, hcap1, hcap7⟩
  refine cpsNBranchWithin_weaken_pre
    (P := (((.x12 ↦ᵣ BitVec.ofNat 64 prevLen) ** (.x0 ↦ᵣ (0 : Word)) **
      regOwn .x13 ** regOwn .x14 ** bytesRegion base bytes **
      (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
      (.x8 ↦ᵣ (if i ≤ 1 then base else base + BitVec.ofNat 64 omEnd)) **
      (.x9 ↦ᵣ (if i ≤ 1 then BitVec.ofNat 64 bytes.length
        else BitVec.ofNat 64 omLen)) **
      (.x18 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
      (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
      (.x20 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ v21) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion omConst (k67OmBytes) ** regOwn .x1) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31))
    (fun h hp => by
      unfold k67LoopInv at hp
      simp only [] at hp
      by_cases hc : i ≤ 1
      · simp only [if_pos hc] at hp ⊢
        xperm_hyp hp
      · simp only [if_neg hc] at hp ⊢
        xperm_hyp hp) ?_
  apply cpsNBranchWithin_of_forall_regIs_to_regOwn9
  intro v5 v6 v7 x10Old x11Old v28 v29 v30 v31
  apply cpsNBranchWithin_of_forall_regIs_to_regOwn_perm (r := .x1)
    (P := (((.x12 ↦ᵣ BitVec.ofNat 64 prevLen) ** (.x0 ↦ᵣ (0 : Word)) **
      regOwn .x13 ** regOwn .x14 ** bytesRegion base bytes **
      (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
      (.x8 ↦ᵣ (if i ≤ 1 then base else base + BitVec.ofNat 64 omEnd)) **
      (.x9 ↦ᵣ (if i ≤ 1 then BitVec.ofNat 64 bytes.length
        else BitVec.ofNat 64 omLen)) **
      (.x18 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
      (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
      (.x20 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ v21) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion omConst (k67OmBytes)) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ x10Old) **
      (.x11 ↦ᵣ x11Old) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)))
    (hpre := fun h hp => by xperm_hyp hp)
  intro raVal
  by_cases hoff : cur < bytes.length
  · -- cursor inside the window: run the walker call, then dispatch on x11.
    have hcall := k67LoopCall sp0 base omConst raVal
      (if i ≤ 1 then base else base + BitVec.ofNat 64 omEnd)
      (if i ≤ 1 then BitVec.ofNat 64 bytes.length else BitVec.ofNat 64 omLen)
      (BitVec.ofNat 64 prevLen) (base + BitVec.ofNat 64 bytes.length)
      (BitVec.ofNat 64 i) x10Old x11Old v21 v5 v6 v7 v28 v29 v30 v31 svals
      bytes cur hsalign hoff
      (fun _ _ hfit heq => by
        simp only [BitVec.ult, decide_eq_true_eq] at hfit
        refine ⟨by bv_omega, by bv_omega, hvalid _ (by bv_omega)⟩)
      (fun hb1 hb2 hfit => by
        simp only [BitVec.ult, decide_eq_true_eq] at hb1 hb2 hfit
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at hfit
        refine ⟨by bv_omega, by bv_omega, fun k hk => hvalid _ (by bv_omega)⟩)
      (fun hb1 hfit => by
        simp only [BitVec.ult, decide_eq_true_eq] at hb1 hfit
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at hfit
        refine ⟨by bv_omega, by bv_omega, fun k hk => hvalid _ (by bv_omega)⟩)
      (by omega) hvalid
    have hcallN : cpsTripleWithin (2 + (1 + 87)) (K + 56) (K + 68) fullCode
        ((((.x12 ↦ᵣ BitVec.ofNat 64 prevLen) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x13 ** regOwn .x14 ** bytesRegion base bytes **
          (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
          (.x8 ↦ᵣ (if i ≤ 1 then base else base + BitVec.ofNat 64 omEnd)) **
          (.x9 ↦ᵣ (if i ≤ 1 then BitVec.ofNat 64 bytes.length
            else BitVec.ofNat 64 omLen)) **
          (.x18 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
          (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
          (.x20 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ v21) **
          frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
          bytesRegion omConst (k67OmBytes)) **
          (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ x10Old) **
          (.x11 ↦ᵣ x11Old) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
          (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)) ** (.x1 ↦ᵣ raVal))
        (((.x1 ↦ᵣ (K + 68)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** regOwn .x13 ** regOwn .x14 **
          bytesRegion base bytes **
          (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
          (.x8 ↦ᵣ (if i ≤ 1 then base else base + BitVec.ofNat 64 omEnd)) **
          (.x9 ↦ᵣ (if i ≤ 1 then BitVec.ofNat 64 bytes.length
            else BitVec.ofNat 64 omLen)) **
          (.x18 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
          (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
          (.x20 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ v21) **
          frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
          bytesRegion omConst (k67OmBytes)) **
          k67NextNorm base (base + BitVec.ofNat 64 bytes.length) bytes cur) := by
      refine cpsTripleWithin_weaken ?_ ?_ hcall
      · intro h hp; xperm_hyp hp
      · intro h hq
        have hq' : (((.x1 ↦ᵣ (K + 68)) ** regOwn .x5 ** regOwn .x6 **
            regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x13 **
            regOwn .x14 ** bytesRegion base bytes **
            (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
            (.x8 ↦ᵣ (if i ≤ 1 then base
              else base + BitVec.ofNat 64 omEnd)) **
            (.x9 ↦ᵣ (if i ≤ 1 then BitVec.ofNat 64 bytes.length
              else BitVec.ofNat 64 omLen)) **
            (.x18 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
            (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
            (.x20 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ v21) **
            frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
              svals ** bytesRegion omConst (k67OmBytes)) **
            k67NextOutcome base (base + BitVec.ofNat 64 bytes.length) bytes
              cur) h := by xperm_hyp hq
        exact sepConj_mono_right
          (k67NextOutcome_to_norm base (base + BitVec.ofNat 64 bytes.length)
            bytes cur) h hq'
    have hnode : cpsNBranchWithin (1 + 10) (K + 68) fullCode
        (((.x1 ↦ᵣ (K + 68)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** regOwn .x13 ** regOwn .x14 **
          bytesRegion base bytes **
          (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
          (.x8 ↦ᵣ (if i ≤ 1 then base else base + BitVec.ofNat 64 omEnd)) **
          (.x9 ↦ᵣ (if i ≤ 1 then BitVec.ofNat 64 bytes.length
            else BitVec.ofNat 64 omLen)) **
          (.x18 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
          (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
          (.x20 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ v21) **
          frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
          bytesRegion omConst (k67OmBytes)) **
          k67NextNorm base (base + BitVec.ofNat 64 bytes.length) bytes cur)
        (k67Exits4 sp0 base omConst bytes startOff svals v21 j) := by
      refine cpsNBranchWithin_weaken_pre
        (P := fun h =>
          (((.x1 ↦ᵣ (K + 68)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) ** regOwn .x13 ** regOwn .x14 **
            bytesRegion base bytes **
            (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
            (.x8 ↦ᵣ (if i ≤ 1 then base
              else base + BitVec.ofNat 64 omEnd)) **
            (.x9 ↦ᵣ (if i ≤ 1 then BitVec.ofNat 64 bytes.length
              else BitVec.ofNat 64 omLen)) **
            (.x18 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
            (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
            (.x20 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ v21) **
            frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
              svals ** bytesRegion omConst (k67OmBytes)) **
            (fun h' => ∃ status : Word,
              ((.x10 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
                (.x11 ↦ᵣ status) ** (.x12 ↦ᵣ (0 : Word)) **
                ⌜status ≠ (0 : Word) ∧ RlpListNthItemSAsm.WalkFailure bytes
                  cur (base + BitVec.ofNat 64 cur)
                  (base + BitVec.ofNat 64 bytes.length)⌝) h')) h ∨
          (((.x1 ↦ᵣ (K + 68)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) ** regOwn .x13 ** regOwn .x14 **
            bytesRegion base bytes **
            (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
            (.x8 ↦ᵣ (if i ≤ 1 then base
              else base + BitVec.ofNat 64 omEnd)) **
            (.x9 ↦ᵣ (if i ≤ 1 then BitVec.ofNat 64 bytes.length
              else BitVec.ofNat 64 omLen)) **
            (.x18 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
            (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
            (.x20 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ v21) **
            frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
              svals ** bytesRegion omConst (k67OmBytes)) **
            rlpWalkNextOk (base + BitVec.ofNat 64 cur)
              (base + BitVec.ofNat 64 bytes.length) bytes cur) h)
        (fun h hp => by
          unfold k67NextNorm at hp
          exact (sepConj_or_split _ hp).symm) ?_
      apply k67NBranch_pre_or
      · -- walker reported failure: dispatch to the status-4 station.
        apply cpsNBranchWithin_weaken_pre (fun h hp =>
          sepConj_exists_right _ hp)
        apply cpsNBranchWithin_exists_pre; intro statusW
        refine cpsNBranchWithin_weaken_pre
          (P := (((.x1 ↦ᵣ (K + 68)) ** regOwn .x5 ** regOwn .x6 **
            regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x13 **
            regOwn .x14 ** bytesRegion base bytes **
            (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
            (.x8 ↦ᵣ (if i ≤ 1 then base
              else base + BitVec.ofNat 64 omEnd)) **
            (.x9 ↦ᵣ (if i ≤ 1 then BitVec.ofNat 64 bytes.length
              else BitVec.ofNat 64 omLen)) **
            (.x18 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
            (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
            (.x20 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ v21) **
            frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
              svals ** bytesRegion omConst (k67OmBytes) **
            (.x10 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
            (.x11 ↦ᵣ statusW) ** (.x12 ↦ᵣ (0 : Word))) **
            ⌜statusW ≠ 0 ∧ RlpListNthItemSAsm.WalkFailure bytes cur
              (base + BitVec.ofNat 64 cur)
              (base + BitVec.ofNat 64 bytes.length)⌝))
          (fun h hp => by
            extract_pure_deep hp
            refine (sepConj_pure_right _).2 ⟨?_, hp.1⟩
            have htail := hp.2
            xperm_hyp htail) ?_
        apply cpsNBranchWithin_pure_pre; rintro ⟨hne, hwf⟩
        refine cpsNBranchWithin_weaken_pre
          (P := (((.x1 ↦ᵣ (K + 68)) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion base bytes **
            (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
            (.x8 ↦ᵣ (if i ≤ 1 then base
              else base + BitVec.ofNat 64 omEnd)) **
            (.x9 ↦ᵣ (if i ≤ 1 then BitVec.ofNat 64 bytes.length
              else BitVec.ofNat 64 omLen)) **
            (.x18 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
            (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
            (.x20 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ v21) **
            frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
              svals ** bytesRegion omConst (k67OmBytes) **
            (.x10 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
            (.x11 ↦ᵣ statusW) ** (.x12 ↦ᵣ (0 : Word))) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
            regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x13 **
            regOwn .x14))
          (fun h hp => by xperm_hyp hp) ?_
        apply cpsNBranchWithin_of_forall_regIs_to_regOwn9
        intro v5' v6' v7' v28' v29' v30' v31' v13' v14'
        apply cpsNBranchWithin_mono_nSteps (show 1 ≤ 1 + 10 by omega)
        apply cpsNBranchWithin_of_triple
          (Q := k67Qfail sp0 base omConst bytes startOff svals v21)
          (by apply List.Mem.tail; apply List.Mem.head)
        refine cpsTripleWithin_weaken (fun h hp => by
          have h2 : (((.x1 ↦ᵣ (K + 68)) **
              (.x10 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
              (.x11 ↦ᵣ statusW) ** (.x12 ↦ᵣ (0 : Word)) **
              (.x8 ↦ᵣ (if i ≤ 1 then base
                else base + BitVec.ofNat 64 omEnd)) **
              (.x9 ↦ᵣ (if i ≤ 1 then BitVec.ofNat 64 bytes.length
                else BitVec.ofNat 64 omLen)) **
              (.x18 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
              (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
              (.x20 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ v21) **
              (.x5 ↦ᵣ v5') ** (.x6 ↦ᵣ v6') ** (.x7 ↦ᵣ v7') **
              (.x28 ↦ᵣ v28') ** (.x29 ↦ᵣ v29') ** (.x30 ↦ᵣ v30') **
              (.x31 ↦ᵣ v31') ** (.x0 ↦ᵣ (0 : Word)) **
              frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
                svals ** bytesRegion base bytes **
              bytesRegion omConst (k67OmBytes) **
              (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12)))) **
              ((.x13 ↦ᵣ v13') ** (.x14 ↦ᵣ v14'))) h := by xperm_hyp hp
          have hconv := sepConj_mono_right (k67Pins2_to_regOwns v13' v14')
            h h2
          xperm_hyp hconv) ?_
          (cpsTripleWithin_frameR _ pcFree_regIs
            (k67LoopFail sp0 base omConst (base + BitVec.ofNat 64 cur)
              (base + BitVec.ofNat 64 bytes.length) statusW
              (BitVec.ofNat 64 i)
              (if i ≤ 1 then base else base + BitVec.ofNat 64 omEnd)
              (if i ≤ 1 then BitVec.ofNat 64 bytes.length
                else BitVec.ofNat 64 omLen)
              v21 v5' v6' v7' v28' v29' v30' v31' svals bytes hne))
        intro h hq
        refine ⟨i, cur, statusW,
          if i ≤ 1 then base else base + BitVec.ofNat 64 omEnd,
          if i ≤ 1 then BitVec.ofNat 64 bytes.length
            else BitVec.ofNat 64 omLen,
          v5', v6', v7', v28', v29', v30', v31', ?_⟩
        refine (sepConj_pure_right _).2 ⟨?_, hne, hile, hcur, hprefix, hwf⟩
        xperm_hyp hq
      · -- walker decoded field `i`: dispatch not-taken, run the arm.
        apply cpsNBranchWithin_weaken_pre (fun h hp =>
          sepConj_exists_right _ hp)
        apply cpsNBranchWithin_exists_pre; intro next
        apply cpsNBranchWithin_weaken_pre (fun h hp =>
          sepConj_exists_right _ hp)
        apply cpsNBranchWithin_exists_pre; intro lenW
        refine cpsNBranchWithin_weaken_pre
          (P := (((.x1 ↦ᵣ (K + 68)) ** regOwn .x5 ** regOwn .x6 **
            regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x13 **
            regOwn .x14 ** bytesRegion base bytes **
            (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
            (.x8 ↦ᵣ (if i ≤ 1 then base
              else base + BitVec.ofNat 64 omEnd)) **
            (.x9 ↦ᵣ (if i ≤ 1 then BitVec.ofNat 64 bytes.length
              else BitVec.ofNat 64 omLen)) **
            (.x18 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
            (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
            (.x20 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ v21) **
            frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
              svals ** bytesRegion omConst (k67OmBytes) **
            (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW)) **
            ⌜rlpItemDecode bytes cur (base + BitVec.ofNat 64 cur)
              (base + BitVec.ofNat 64 bytes.length) next lenW⌝))
          (fun h hp => by
            extract_pure_deep hp
            refine (sepConj_pure_right _).2 ⟨?_, hp.1⟩
            have htail := hp.2
            xperm_hyp htail) ?_
        apply cpsNBranchWithin_pure_pre; intro hdecode
        refine cpsNBranchWithin_weaken_pre
          (P := (((.x1 ↦ᵣ (K + 68)) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion base bytes **
            (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
            (.x8 ↦ᵣ (if i ≤ 1 then base
              else base + BitVec.ofNat 64 omEnd)) **
            (.x9 ↦ᵣ (if i ≤ 1 then BitVec.ofNat 64 bytes.length
              else BitVec.ofNat 64 omLen)) **
            (.x18 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
            (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
            (.x20 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ v21) **
            frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
              svals ** bytesRegion omConst (k67OmBytes) **
            (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW)) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
            regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x13 **
            regOwn .x14))
          (fun h hp => by xperm_hyp hp) ?_
        apply cpsNBranchWithin_of_forall_regIs_to_regOwn9
        intro v5' v6' v7' v28' v29' v30' v31' v13' v14'
        let F : Assertion :=
          (.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ v5') ** (.x6 ↦ᵣ v6') ** (.x7 ↦ᵣ v7') **
            (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) **
            (.x8 ↦ᵣ (if i ≤ 1 then base else base + BitVec.ofNat 64 omEnd)) **
            (.x9 ↦ᵣ (if i ≤ 1 then BitVec.ofNat 64 bytes.length
              else BitVec.ofNat 64 omLen)) **
            (.x18 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
            (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
            (.x20 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ v21) **
            (.x28 ↦ᵣ v28') ** (.x29 ↦ᵣ v29') ** (.x30 ↦ᵣ v30') **
            (.x31 ↦ᵣ v31') ** regOwn .x13 ** regOwn .x14 **
            (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
            frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
              svals **
            bytesRegion base bytes ** bytesRegion omConst (k67OmBytes)
        have hF : F.pcFree := by
          dsimp [F]
          repeat' first
            | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
            | exact bytesRegion_pcFree _ _
            | exact pcFree_frameSlotsSaved _ _ _
            | apply pcFree_sepConj
        have hdisp := cpsTripleWithin_extend_code k67_mono
          (status0DispatchFrame F hF)
        have h72 : cpsNBranchWithin 10 (K + 72) fullCode
            (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) ** F)
            (k67Exits4 sp0 base omConst bytes startOff svals v21 j) := by
          by_cases hi1 : BitVec.ofNat 64 i = 1
          · exact cpsNBranchWithin_weaken_pre (fun h hp => by
              dsimp only [F] at hp; unfold k67ArmPre; xperm_hyp hp)
              (k67RoundCont1 sp0 base omConst bytes i cur omEnd omLen startOff
                j next lenW v21 v5' v6' v7' v28' v29' v30' v31' svals hi1 hj
                hcur hile hprefix hcap1 hcap7 hdecode hover9)
          · by_cases hi7 : BitVec.ofNat 64 i = 7
            · by_cases hlen0 : lenW = 0
              · exact cpsNBranchWithin_weaken_pre (fun h hp => by
                  dsimp only [F] at hp; unfold k67ArmPre; xperm_hyp hp)
                  (k67RoundCont7 sp0 base omConst bytes i cur omEnd omLen
                    startOff j next lenW v21 v5' v6' v7' v28' v29' v30' v31'
                    svals hi7 hlen0 hj hcur hile hprefix hcap1 hcap7 hdecode
                    hover9)
              · exact cpsNBranchWithin_weaken_pre (fun h hp => by
                  dsimp only [F] at hp; unfold k67ArmPre; xperm_hyp hp)
                  (k67RoundDiff sp0 base omConst bytes i cur omEnd omLen
                    startOff j next lenW v21 v5' v6' v7' v28' v29' v30' v31'
                    svals hi7 hlen0 hj hcur hile hprefix hcap1 hcap7 hdecode
                    hover9)
            · by_cases hi14 : BitVec.ofNat 64 i = 14
              · exact cpsNBranchWithin_weaken_pre (fun h hp => by
                  dsimp only [F] at hp; unfold k67ArmPre; xperm_hyp hp)
                  (k67RoundExit sp0 base omConst bytes i cur omEnd omLen
                    startOff j next lenW v21 v5' v6' v7' v28' v29' v30' v31'
                    svals hi14 hj hcur hile hprefix hcap1 hcap7 hdecode
                    hover9)
              · exact cpsNBranchWithin_weaken_pre (fun h hp => by
                  dsimp only [F] at hp; unfold k67ArmPre; xperm_hyp hp)
                  (k67RoundContO sp0 base omConst bytes i cur omEnd omLen
                    startOff j next lenW v21 v5' v6' v7' v28' v29' v30' v31'
                    svals hi1 hi7 hi14 hj hcur hile hprefix hcap1 hcap7
                    hdecode hover9)
        refine cpsTripleWithin_seq_cpsNBranchWithin_same_cr ?_ h72
        exact cpsTripleWithin_weaken (fun h hp => by
          have h2 : (((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ v5') ** (.x6 ↦ᵣ v6') **
              (.x7 ↦ᵣ v7') ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) **
              (.x12 ↦ᵣ lenW) **
              (.x8 ↦ᵣ (if i ≤ 1 then base
                else base + BitVec.ofNat 64 omEnd)) **
              (.x9 ↦ᵣ (if i ≤ 1 then BitVec.ofNat 64 bytes.length
                else BitVec.ofNat 64 omLen)) **
              (.x18 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
              (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
              (.x20 ↦ᵣ BitVec.ofNat 64 i) ** (.x21 ↦ᵣ v21) **
              (.x28 ↦ᵣ v28') ** (.x29 ↦ᵣ v29') ** (.x30 ↦ᵣ v30') **
              (.x31 ↦ᵣ v31') ** (.x0 ↦ᵣ (0 : Word)) **
              (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
              frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12))
                svals ** bytesRegion base bytes **
              bytesRegion omConst (k67OmBytes)) **
              ((.x13 ↦ᵣ v13') ** (.x14 ↦ᵣ v14'))) h := by xperm_hyp hp
          have hconv := sepConj_mono_right (k67Pins2_to_regOwns v13' v14')
            h h2
          xperm_hyp hconv) (fun h hq => hq) hdisp
    exact cpsTripleWithin_seq_cpsNBranchWithin_same_cr hcallN hnode
  · -- cursor at the window end: the walker's early status-2 return.
    have hcurE : cur = bytes.length := by omega
    have h_end : ¬ BitVec.ult (base + BitVec.ofNat 64 cur)
        (base + BitVec.ofNat 64 bytes.length) = true := by
      rw [hcurE]
      simp only [BitVec.ult, decide_eq_true_eq]
      exact Nat.lt_irrefl _
    have hstep := k67LoopCallEnd sp0 base omConst raVal
      (if i ≤ 1 then base else base + BitVec.ofNat 64 omEnd)
      (if i ≤ 1 then BitVec.ofNat 64 bytes.length else BitVec.ofNat 64 omLen)
      (BitVec.ofNat 64 prevLen) (base + BitVec.ofNat 64 bytes.length)
      (BitVec.ofNat 64 i) x10Old x11Old v21 v5 v6 v7 v28 v29 v30 v31 svals
      bytes cur h_end
    apply cpsNBranchWithin_mono_nSteps (show 2 + (1 + 4) + 1 ≤ 101 by omega)
    apply cpsNBranchWithin_of_triple
      (Q := k67Qfail sp0 base omConst bytes startOff svals v21)
      (by apply List.Mem.tail; apply List.Mem.head)
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) ?_ hstep
    intro h hq
    refine ⟨i, cur, 2,
      if i ≤ 1 then base else base + BitVec.ofNat 64 omEnd,
      if i ≤ 1 then BitVec.ofNat 64 bytes.length else BitVec.ofNat 64 omLen,
      v5, v6, v7, v28, v29, v30, v31, ?_⟩
    refine (sepConj_pure_right _).2 ⟨?_, by decide, hile, hcur, hprefix,
      Or.inl h_end⟩
    xperm_hyp hq

/-! ## §8  Measure fold -/

/-- The field-scan loop, folded: from the loop header at `K + 56` with loop
    state `k67FuelInv j`, control reaches one of the three stations within
    `101 * (j + 1)` instructions. -/
theorem k67LoopFold
    (sp0 base omConst : Word) (bytes : List (BitVec 8))
    (startOff : Nat) (svals : Reg → Word) (v21 : Word)
    (hsalign : base.toNat % 8 = 0)
    (hover9 : base.toNat + bytes.length + 9 < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (base + BitVec.ofNat 64 k) = true)
    (j : Nat) :
    cpsNBranchWithin (101 * (j + 1)) (K + 56) fullCode
      (k67FuelInv sp0 base omConst bytes startOff svals v21 j)
      [(K + 604, k67Qdiff sp0 base omConst bytes startOff svals v21),
        (K + 628, k67Qfail sp0 base omConst bytes startOff svals v21),
        (K + 116, k67Qclean sp0 base omConst bytes startOff svals v21)] :=
  k67MeasureThreeExitLoop_of_round 101
    (fun fuel => k67LoopRound sp0 base omConst bytes startOff svals v21
      hsalign hover9 hvalid fuel)
    (fun _ => Nat.le_refl 101) j
