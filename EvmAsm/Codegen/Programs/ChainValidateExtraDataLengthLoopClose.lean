/-
  Loop induction + whole-program caller contract for
  `chain_validate_extra_data_length`.

  `cvedlLoop` runs the guard/iteration from `C+68` for `N − i` remaining
  headers (induction on the fuel `N − i`, tying each iteration's K20 `Result`
  into the accumulating `hprefix`), and
  `chain_validate_extra_data_length_spec_within` glues the prologue in front.
-/

import EvmAsm.Codegen.Programs.ChainValidateExtraDataLengthLoop

namespace EvmAsm.Codegen.ChainValidateExtraDataLengthSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm

local macro "pcfx" : tactic =>
  `(tactic| repeat' first
      | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
      | exact pcFree_memIs | exact pcFree_memOwn | exact pcFree_emp | exact pcFree_pure
      | exact bytesRegion_pcFree _ _ | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_wordArray _ _ | exact pcFree_wordArrayFrom _ _ _ | unfold savedFrame)

/-- Step budget for the loop with `r = N − i` iterations remaining: each full
    iteration is `cvedlIter`'s cost, the exhausted guard + all-valid exit is
    `11`. -/
def cvedlLoopSteps : Nat → Nat
  | 0 => 11
  | r + 1 => (1 + (15 + 1 + nCall)) + (25 + cvedlLoopSteps r)

theorem cvedlLoopSteps_succ (r : Nat) :
    cvedlLoopSteps (r + 1) = (1 + (15 + 1 + nCall)) + (25 + cvedlLoopSteps r) := rfl

set_option maxRecDepth 8000 in
/-- The guard/loop from `C+68` entering iteration `i` (`i ≤ N`), with all
    earlier headers known valid-short.  On `i = N` the guard falls through to the
    all-valid exit; otherwise one `cvedlIter` runs and the induction hypothesis
    handles the rest (with `hprefix` extended by the freshly-decoded header). -/
theorem cvedlLoop (sp0 spC hdrBase lenBase validPtr firstBadPtr raIn : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (hN : lengths.length < 2 ^ 64)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hAllAlign : ∀ i, i < lengths.length → hdrOff lengths i % 8 = 0)
    (hAllLen : ∀ i, i < lengths.length → hdrOff lengths i ≤ bigBytes.length)
    (hAllSalign : ∀ i, i < lengths.length → (hdrBaseAt hdrBase lengths i).toNat % 8 = 0)
    (hAllBytes : ∀ i, i < lengths.length →
      lengths[i]! ≤ (bigBytes.drop (hdrOff lengths i)).length)
    (hAllNowrap : ∀ i, i < lengths.length →
      (hdrBaseAt hdrBase lengths i).toNat + lengths[i]! + 9 < 2 ^ 64)
    (hAllOver : ∀ i, i < lengths.length →
      (hdrBaseAt hdrBase lengths i).toNat + (bigBytes.drop (hdrOff lengths i)).length < 2 ^ 64)
    (hAllNz : ∀ i, i < lengths.length →
      0 < (bigBytes.drop (hdrOff lengths i)).length)
    (hAllValid : ∀ i, i < lengths.length → ∀ k, k < (bigBytes.drop (hdrOff lengths i)).length →
      isValidByteAccess (hdrBaseAt hdrBase lengths i + BitVec.ofNat 64 k) = true) :
    ∀ (f i : Nat), lengths.length - i ≤ f → i ≤ lengths.length →
      (∀ j, j < i → hdrValidShort hdrBase bigBytes lengths j) →
      cpsTripleWithin (cvedlLoopSteps (lengths.length - i)) (C + 68) raIn fullCode
        (LoopInv sp0 spC (spC + signExtend12 (-64 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths i)
        (cvedlPost sp0 spC (spC + signExtend12 (-64 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths) := by
  have hsf : savedFrame spC csaved =
      ((spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) := by
    unfold savedFrame; rw [hraSaved]
  -- All-valid exit reached at the guard when `i = N`.
  have base : (∀ j, j < lengths.length → hdrValidShort hdrBase bigBytes lengths j) →
      cpsTripleWithin (cvedlLoopSteps 0) (C + 68) raIn fullCode
        (LoopInv sp0 spC (spC + signExtend12 (-64 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths lengths.length)
        (cvedlPost sp0 spC (spC + signExtend12 (-64 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths) := by
    intro hpre
    -- Expose the two scratch registers overwritten by the exit block.
    refine cpsTripleWithin_weaken (fun h hp => by unfold LoopInv scratchRegs at hp; xperm_hyp hp)
      (fun _ hq => hq)
      (show cpsTripleWithin (cvedlLoopSteps 0) (C + 68) raIn fullCode
        ((((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
            (.x18 ↦ᵣ hdrBaseAt hdrBase lengths lengths.length) ** (.x19 ↦ᵣ validPtr) **
            (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 lengths.length) **
            savedFrame spC csaved ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
            payload hdrBase lenBase bigBytes lengths ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
            regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
            frameSlotsOwn listNthFrame (spC + signExtend12 (-64 : BitVec 12))) ** regOwn .x1) **
          regOwn .x10)
        (cvedlPost sp0 spC (spC + signExtend12 (-64 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths) from ?_)
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun o10 => ?_)
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
      (show cpsTripleWithin (cvedlLoopSteps 0) (C + 68) raIn fullCode
        (((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
            (.x18 ↦ᵣ hdrBaseAt hdrBase lengths lengths.length) ** (.x19 ↦ᵣ validPtr) **
            (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 lengths.length) **
            savedFrame spC csaved ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
            payload hdrBase lenBase bigBytes lengths ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
            regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
            frameSlotsOwn listNthFrame (spC + signExtend12 (-64 : BitVec 12)) **
            (.x10 ↦ᵣ o10)) ** regOwn .x1)
        (cvedlPost sp0 spC (spC + signExtend12 (-64 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths) from ?_)
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun o1 => ?_)
    -- Guard `beq x21 x8` taken (i = N).
    have hbeq := beq_spec_gen_within .x21 .x8 (168 : BitVec 13)
      (BitVec.ofNat 64 lengths.length) (BitVec.ofNat 64 lengths.length) (C + 68)
    have hbeqC := cpsBranchWithin_extend_code cvedl_mono
      (cpsBranchWithin_extend_code (cr' := cvedlCode)
        (CodeReq.ofProg_mem_at C (C + 68) cvedlProg 17 (.BEQ .x21 .x8 (168 : BitVec 13))
          (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) hbeq)
    have htaken := cpsBranchWithin_takenStripPure2 hbeqC (fun hp hq => by
      obtain ⟨_, _, _, _, _, hrest⟩ := hq
      exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
    rw [show (C + 68) + signExtend13 (168 : BitVec 13) = C + 236 from by
      rw [show signExtend13 (168 : BitVec 13) = (168 : Word) from by decide]; bv_omega] at htaken
    have htakenF := cpsTripleWithin_frameR
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x9 ↦ᵣ lenBase) **
        (.x18 ↦ᵣ hdrBaseAt hdrBase lengths lengths.length) ** (.x19 ↦ᵣ validPtr) **
        (.x20 ↦ᵣ firstBadPtr) ** (.x10 ↦ᵣ o10) ** (validPtr ↦ₘ (1 : Word)) **
        (firstBadPtr ↦ₘ (0 : Word)) ** payload hdrBase lenBase bigBytes lengths **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** frameSlotsOwn listNthFrame (spC + signExtend12 (-64 : BitVec 12)) **
        savedFrame spC csaved) (by unfold payload; pcfx) htaken
    have hallv := cpsTripleWithin_extend_code cvedl_mono
      (retAllValid sp0 spC raIn csaved
        (payload hdrBase lenBase bigBytes lengths ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn listNthFrame (spC + signExtend12 (-64 : BitVec 12)) **
          (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)))
        (by unfold payload; pcfx) o10 o1 (BitVec.ofNat 64 lengths.length) lenBase
        (hdrBaseAt hdrBase lengths lengths.length) validPtr firstBadPtr
        (BitVec.ofNat 64 lengths.length) hspC hraSaved hret)
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
      (cpsTripleWithin_seq_perm_same_cr (fun h hp => by rw [hsf] at hp; xperm_hyp hp)
        htakenF hallv)
    -- Assemble the all-valid post.
    refine Or.inl ?_
    unfold postAllValid commonRet
    refine (sepConj_pure_left h).mpr ⟨hpre, ?_⟩
    rw [hsf, hraSaved]
    xperm_hyp hq
  intro f
  induction f with
  | zero =>
    intro i hf hiN hpre
    have hi : i = lengths.length := by omega
    subst hi
    rw [Nat.sub_self]
    exact base hpre
  | succ f ih =>
    intro i hf hiN hpre
    rcases (by omega : i = lengths.length ∨ i < lengths.length) with hi | hi
    · subst hi; rw [Nat.sub_self]; exact base hpre
    · rw [show lengths.length - i = (lengths.length - (i + 1)) + 1 from by omega,
        cvedlLoopSteps_succ]
      exact cvedlIter sp0 spC hdrBase lenBase validPtr firstBadPtr raIn csaved bigBytes lengths i
        (cvedlLoopSteps (lengths.length - (i + 1))) hi hN hspC hraSaved hret
        (hAllAlign i hi) (hAllLen i hi) (hAllSalign i hi) (hAllBytes i hi) (hAllNowrap i hi)
        (hAllOver i hi) (hAllValid i hi) (hAllNz i hi) hpre
        (fun hpre' => ih (i + 1) (by omega) (by omega) hpre')


set_option maxRecDepth 8000 in
/-- **`chain_validate_extra_data_length` caller contract.**  The 69-instruction
    accessor iterates over `N = lengths.length` block headers, validating that
    every header's RLP field 12 (`extra_data`) parses with content length ≤ 32.
    Its three-way post pins the result: all-valid (`a0 = 0`, `*validPtr = 1`,
    every header valid-short), first-violation (`a0 = 0`, `*validPtr = 0`,
    `*firstBad = k`, header `k` long and all earlier valid-short), or first
    parse-failure (`a0 = 1`, `*firstBad = k`, header `k` fails RLP parse and all
    earlier valid-short) — each genuinely tied to K20's per-header `Result`. -/
theorem chain_validate_extra_data_length_spec_within
    (sp0 spC nWord lenBase hdrBase validPtr firstBadPtr raIn
      cs0 cs1 cs2 cs3 cs4 cs5 old5 : Word) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hnWord : nWord = BitVec.ofNat 64 lengths.length)
    (hN : lengths.length < 2 ^ 64)
    (hAllAlign : ∀ i, i < lengths.length → hdrOff lengths i % 8 = 0)
    (hAllLen : ∀ i, i < lengths.length → hdrOff lengths i ≤ bigBytes.length)
    (hAllSalign : ∀ i, i < lengths.length → (hdrBaseAt hdrBase lengths i).toNat % 8 = 0)
    (hAllBytes : ∀ i, i < lengths.length →
      lengths[i]! ≤ (bigBytes.drop (hdrOff lengths i)).length)
    (hAllNowrap : ∀ i, i < lengths.length →
      (hdrBaseAt hdrBase lengths i).toNat + lengths[i]! + 9 < 2 ^ 64)
    (hAllOver : ∀ i, i < lengths.length →
      (hdrBaseAt hdrBase lengths i).toNat + (bigBytes.drop (hdrOff lengths i)).length < 2 ^ 64)
    (hAllNz : ∀ i, i < lengths.length →
      0 < (bigBytes.drop (hdrOff lengths i)).length)
    (hAllValid : ∀ i, i < lengths.length → ∀ k, k < (bigBytes.drop (hdrOff lengths i)).length →
      isValidByteAccess (hdrBaseAt hdrBase lengths i + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (17 + cvedlLoopSteps lengths.length) C raIn fullCode
      (((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) **
          (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
          (.x10 ↦ᵣ nWord) ** (.x11 ↦ᵣ lenBase) ** (.x12 ↦ᵣ hdrBase) **
          (.x13 ↦ᵣ validPtr) ** (.x14 ↦ᵣ firstBadPtr) ** (.x5 ↦ᵣ old5) **
          (.x0 ↦ᵣ (0 : Word)) **
          memOwn spC ** memOwn (spC + 8) ** memOwn (spC + 16) ** memOwn (spC + 24) **
          memOwn (spC + 32) ** memOwn (spC + 40) ** memOwn (spC + 48) **
          memOwn validPtr ** memOwn firstBadPtr) **
        wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
        memOwn COff ** memOwn CLen ** memOwn IterPtr ** memOwn IterI **
        regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        frameSlotsOwn listNthFrame (spC + signExtend12 (-64 : BitVec 12)))
      (cvedlPost sp0 spC (spC + signExtend12 (-64 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr ⟨raIn, cs0, cs1, cs2, cs3, cs4, cs5⟩ bigBytes lengths) := by
  have h0 : hdrBaseAt hdrBase lengths 0 = hdrBase := by
    unfold hdrBaseAt hdrOff; simp
  have hsf : savedFrame spC (⟨raIn, cs0, cs1, cs2, cs3, cs4, cs5⟩ : Saved) =
      ((spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) ** ((spC + 24) ↦ₘ cs2) **
        ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5)) := by
    unfold savedFrame; rfl
  have hpro := cpsTripleWithin_frameR
    (wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
      memOwn COff ** memOwn CLen ** memOwn IterPtr ** memOwn IterI **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      frameSlotsOwn listNthFrame (spC + signExtend12 (-64 : BitVec 12)))
    (by pcfx)
    (cpsTripleWithin_extend_code cvedl_mono
      (cvedlPrologue sp0 spC nWord lenBase hdrBase validPtr firstBadPtr raIn
        cs0 cs1 cs2 cs3 cs4 cs5 old5 hspC))
  have hloop := cvedlLoop sp0 spC hdrBase lenBase validPtr firstBadPtr raIn
    ⟨raIn, cs0, cs1, cs2, cs3, cs4, cs5⟩ bigBytes lengths hN hspC rfl hret
    hAllAlign hAllLen hAllSalign hAllBytes hAllNowrap hAllOver hAllNz hAllValid
    lengths.length 0 (by omega) (by omega) (fun j hj => absurd hj (Nat.not_lt_zero j))
  rw [Nat.sub_zero] at hloop
  refine cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    unfold LoopInv payload scratchRegs
    rw [hsf, h0, show (BitVec.ofNat 64 0 : Word) = (0 : Word) from by decide]
    have hp1 : ((.x1 ↦ᵣ raIn) ** (.x5 ↦ᵣ (1 : Word)) **
        (.x10 ↦ᵣ BitVec.ofNat 64 lengths.length) **
        (.x11 ↦ᵣ lenBase) ** (.x12 ↦ᵣ hdrBase) ** (.x13 ↦ᵣ validPtr) ** (.x14 ↦ᵣ firstBadPtr) **
        ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
          (.x18 ↦ᵣ hdrBase) **
          (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ (0 : Word)) **
          (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) ** ((spC + 24) ↦ₘ cs2) **
          ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) **
          (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
          wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
          memOwn COff ** memOwn CLen ** memOwn IterPtr ** memOwn IterI **
          regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn listNthFrame (spC + signExtend12 (-64 : BitVec 12)))) h := by
      rw [hnWord] at hp; xperm_hyp hp
    have hp2 := sepConj_mono (regIs_implies_regOwn .x1) (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x10) (sepConj_mono (regIs_implies_regOwn .x11)
      (sepConj_mono (regIs_implies_regOwn .x12) (sepConj_mono (regIs_implies_regOwn .x13)
      (sepConj_mono (regIs_implies_regOwn .x14) (fun _ x => x))))))) h hp1
    xperm_hyp hp2) hpro hloop

/-! ## Anti-vacuity cover (#12471)

    The old `hAllSlack` (`lengths[i]! + 9 ≤ drop.length`) was unsatisfiable on every
    exact-fit nonempty blob (last index forces `L+9 ≤ L`). The repaired premise
    *set* of `chain_validate_extra_data_length_spec_within` is jointly inhabited
    on an exact-fit nonempty 8-aligned blob — the case the old premise excluded. -/

/-- Exact-fit nonempty cover: `lengths = [48, 48]`, `|bigBytes| = 96`, `hdrBase = MEM_START`.
    Lengths are 8-aligned so `hAllAlign`/`hAllSalign` hold (unlike `[50,50]`). -/
example :
    let lengths := [48, 48]
    let bigBytes : List (BitVec 8) := List.replicate 96 (0 : BitVec 8)
    let hdrBase : Word := BitVec.ofNat 64 MEM_START
    (∀ i, i < lengths.length → hdrOff lengths i % 8 = 0) ∧
    (∀ i, i < lengths.length → hdrOff lengths i ≤ bigBytes.length) ∧
    (∀ i, i < lengths.length → (hdrBaseAt hdrBase lengths i).toNat % 8 = 0) ∧
    (∀ i, i < lengths.length →
      lengths[i]! ≤ (bigBytes.drop (hdrOff lengths i)).length) ∧
    (∀ i, i < lengths.length →
      (hdrBaseAt hdrBase lengths i).toNat + lengths[i]! + 9 < 2 ^ 64) ∧
    (∀ i, i < lengths.length →
      (hdrBaseAt hdrBase lengths i).toNat + (bigBytes.drop (hdrOff lengths i)).length <
        2 ^ 64) ∧
    (∀ i, i < lengths.length → 0 < (bigBytes.drop (hdrOff lengths i)).length) ∧
    (∀ i, i < lengths.length → ∀ k, k < (bigBytes.drop (hdrOff lengths i)).length →
      isValidByteAccess (hdrBaseAt hdrBase lengths i + BitVec.ofNat 64 k) = true) := by
  -- Discharge each binder of the repaired set on this concrete exact-fit witness.
  refine ⟨?hAllAlign, ?hAllLen, ?hAllSalign, ?hAllBytes, ?hAllNowrap, ?hAllOver, ?hAllNz,
    ?hAllValid⟩
  · intro i hi; match i with
    | 0 => decide
    | 1 => decide
    | n + 2 => cases (Nat.not_lt_of_le (by omega : 2 ≤ n + 2) hi)
  · intro i hi; match i with
    | 0 => decide
    | 1 => decide
    | n + 2 => cases (Nat.not_lt_of_le (by omega : 2 ≤ n + 2) hi)
  · intro i hi; match i with
    | 0 => decide
    | 1 => decide
    | n + 2 => cases (Nat.not_lt_of_le (by omega : 2 ≤ n + 2) hi)
  · intro i hi; match i with
    | 0 => decide
    | 1 => decide
    | n + 2 => cases (Nat.not_lt_of_le (by omega : 2 ≤ n + 2) hi)
  · intro i hi; match i with
    | 0 => decide
    | 1 => decide
    | n + 2 => cases (Nat.not_lt_of_le (by omega : 2 ≤ n + 2) hi)
  · intro i hi; match i with
    | 0 => decide
    | 1 => decide
    | n + 2 => cases (Nat.not_lt_of_le (by omega : 2 ≤ n + 2) hi)
  · intro i hi; match i with
    | 0 => decide
    | 1 => decide
    | n + 2 => cases (Nat.not_lt_of_le (by omega : 2 ≤ n + 2) hi)
  · intro i hi k hk
    match i with
    | 0 =>
      have hk96 : k < 96 := by
        simpa [hdrOff] using hk
      have hsum :
          (hdrBaseAt (BitVec.ofNat 64 MEM_START) [48, 48] 0 + BitVec.ofNat 64 k).toNat =
            32 + k := by
        simp only [hdrBaseAt, hdrOff, List.take_zero, List.sum_nil, MEM_START]
        rw [BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega : 32 < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 32 + k < 2 ^ 64)]
      simp only [isValidByteAccess, isValidMemAddr, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq]
      refine Or.inl (Or.inl ?_)
      constructor
      · rw [hsum]; change 32 ≤ 32 + k; omega
      · rw [hsum]; change 32 + k ≤ 0x78000000; omega
    | 1 =>
      have hk48 : k < 48 := by
        simpa [hdrOff] using hk
      have hsum :
          (hdrBaseAt (BitVec.ofNat 64 MEM_START) [48, 48] 1 + BitVec.ofNat 64 k).toNat =
            80 + k := by
        simp only [hdrBaseAt, hdrOff, MEM_START]
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        simp only [List.take, List.sum_cons, List.sum_nil, Nat.add_zero]
        have hk64 : k < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt (by omega : 32 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 48 < 2 ^ 64)]
        change (80 % 2 ^ 64 + (BitVec.ofNat 64 k).toNat) % 2 ^ 64 = 80 + k
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 80 < 2 ^ 64), Nat.mod_eq_of_lt hk64,
          Nat.mod_eq_of_lt (by omega : 80 + k < 2 ^ 64)]
      simp only [isValidByteAccess, isValidMemAddr, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq]
      refine Or.inl (Or.inl ?_)
      constructor
      · rw [hsum]; change 32 ≤ 80 + k; omega
      · rw [hsum]; change 80 + k ≤ 0x78000000; omega
    | n + 2 => cases (Nat.not_lt_of_le (by omega : 2 ≤ n + 2) hi)

end EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
