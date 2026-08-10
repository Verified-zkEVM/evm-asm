/-
  Loop induction + whole-program caller contract for
  `chain_validate_blob_gas_used_multiple`.

  `cvbgmLoop` runs the guard/iteration from `D+68` for `N − i` remaining
  headers (induction on the fuel `N − i`, tying each iteration's K34 `Result`
  into the accumulating `hprefix`), and
  `chain_validate_blob_gas_used_multiple_spec_within` glues the prologue in
  front.
-/

import EvmAsm.Codegen.Programs.ChainValidateBlobGasMultipleLoop

namespace EvmAsm.Codegen.ChainValidateBlobGasMultipleSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm
  (Saved savedFrame savedVals listNthFrame regsAt_listNthFrame
   frameSlotsSaved_listNthFrame)
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
  (wordArray wordArrayFrom wordArray_split pcFree_wordArray pcFree_wordArrayFrom
   wordArrayFrom_append shiftLeft3_ofNat hdrOff hdrBaseAt hdrOff_succ hdrBaseAt_succ
   ofNat_ne_of_lt ofNat_succ_tie)

local macro "pcfx" : tactic =>
  `(tactic| repeat' first
      | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
      | exact pcFree_memIs | exact pcFree_memOwn | exact pcFree_emp | exact pcFree_pure
      | exact bytesRegion_pcFree _ _ | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_stackFree _ _
      | exact pcFree_wordArray _ _ | exact pcFree_wordArrayFrom _ _ _ | unfold savedFrame
      | unfold EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame)

/-- Step budget for the loop with `r = N − i` iterations remaining: each full
    iteration is `cvbgmIter`'s cost, the exhausted guard + all-valid exit is
    `11`. -/
def cvbgmLoopSteps (bytesLen : Nat) : Nat → Nat
  | 0 => 11
  | r + 1 => (1 + (13 + 1 + nCall bytesLen)) + (27 + cvbgmLoopSteps bytesLen r)

theorem cvbgmLoopSteps_succ (bytesLen r : Nat) :
    cvbgmLoopSteps bytesLen (r + 1) =
      (1 + (13 + 1 + nCall bytesLen)) + (27 + cvbgmLoopSteps bytesLen r) := rfl

set_option maxRecDepth 8000 in
/-- The guard/loop from `D+68` entering iteration `i` (`i ≤ N`), with all
    earlier headers known under-max.  On `i = N` the guard falls through to the
    all-valid exit; otherwise one `cvbgmIter` runs and the induction hypothesis
    handles the rest (with `hprefix` extended by the freshly-decoded header). -/
theorem cvbgmLoop (sp0 spC hdrBase lenBase validPtr firstBadPtr raIn : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (hN : lengths.length < 2 ^ 64)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hAllAlign : ∀ i, i < lengths.length → hdrOff lengths i % 8 = 0)
    (hAllLen : ∀ i, i < lengths.length → hdrOff lengths i ≤ bigBytes.length)
    (hAllSalign : ∀ i, i < lengths.length → (hdrBaseAt hdrBase lengths i).toNat % 8 = 0)
    (hAllSlack : ∀ i, i < lengths.length →
      lengths[i]! + 9 ≤ (bigBytes.drop (hdrOff lengths i)).length)
    (hAllOver : ∀ i, i < lengths.length →
      (hdrBaseAt hdrBase lengths i).toNat + (bigBytes.drop (hdrOff lengths i)).length < 2 ^ 64)
    (hAllValid : ∀ i, i < lengths.length → ∀ k, k < (bigBytes.drop (hdrOff lengths i)).length →
      isValidByteAccess (hdrBaseAt hdrBase lengths i + BitVec.ofNat 64 k) = true) :
    ∀ (f i : Nat), lengths.length - i ≤ f → i ≤ lengths.length →
      (∀ j, j < i → hdrMultiple hdrBase bigBytes lengths j) →
      cpsTripleWithin (cvbgmLoopSteps bigBytes.length (lengths.length - i)) (D + 68) raIn fullCode
        (LoopInv sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths i)
        (cvbgmPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths) := by
  have hsf : savedFrame spC csaved =
      ((spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) := by
    unfold savedFrame; rw [hraSaved]
  -- All-valid exit reached at the guard when `i = N`.
  have base : (∀ j, j < lengths.length → hdrMultiple hdrBase bigBytes lengths j) →
      cpsTripleWithin (cvbgmLoopSteps bigBytes.length 0) (D + 68) raIn fullCode
        (LoopInv sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths lengths.length)
        (cvbgmPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths) := by
    intro hpre
    refine cpsTripleWithin_weaken (fun h hp => by unfold LoopInv scratchRegs at hp; xperm_hyp hp)
      (fun _ hq => hq)
      (show cpsTripleWithin (cvbgmLoopSteps bigBytes.length 0) (D + 68) raIn fullCode
        ((((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
            (.x18 ↦ᵣ hdrBaseAt hdrBase lengths lengths.length) ** (.x19 ↦ᵣ validPtr) **
            (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 lengths.length) **
            savedFrame spC csaved ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
            payload hdrBase lenBase bigBytes lengths ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
            regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
            frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame
              (spC + signExtend12 (-32 : BitVec 12)) **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8) ** regOwn .x1) **
          regOwn .x10)
        (cvbgmPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths) from ?_)
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun o10 => ?_)
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
      (show cpsTripleWithin (cvbgmLoopSteps bigBytes.length 0) (D + 68) raIn fullCode
        (((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
            (.x18 ↦ᵣ hdrBaseAt hdrBase lengths lengths.length) ** (.x19 ↦ᵣ validPtr) **
            (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 lengths.length) **
            savedFrame spC csaved ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
            payload hdrBase lenBase bigBytes lengths ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
            regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
            frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame
              (spC + signExtend12 (-32 : BitVec 12)) **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
            (.x10 ↦ᵣ o10)) ** regOwn .x1)
        (cvbgmPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths) from ?_)
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun o1 => ?_)
    -- Guard `beq x21 x8` taken (i = N).
    have hbeq := beq_spec_gen_within .x21 .x8 (164 : BitVec 13)
      (BitVec.ofNat 64 lengths.length) (BitVec.ofNat 64 lengths.length) (D + 68)
    have hbeqC := cpsBranchWithin_extend_code cvbgm_mono
      (cpsBranchWithin_extend_code (cr' := cvbgmCode)
        (CodeReq.ofProg_mem_at D (D + 68) cvbgmProg 17 (.BEQ .x21 .x8 (164 : BitVec 13))
          (by bv_omega) (by rw [cvbgm_length]; decide) rfl (by rw [cvbgm_length]; decide)) hbeq)
    have htaken := cpsBranchWithin_takenStripPure2 hbeqC (fun hp hq => by
      obtain ⟨_, _, _, _, _, hrest⟩ := hq
      exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
    rw [show (D + 68) + signExtend13 (164 : BitVec 13) = D + 232 from by
      rw [show signExtend13 (164 : BitVec 13) = (164 : Word) from by decide]; bv_omega] at htaken
    have htakenF := cpsTripleWithin_frameR
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x9 ↦ᵣ lenBase) **
        (.x18 ↦ᵣ hdrBaseAt hdrBase lengths lengths.length) ** (.x19 ↦ᵣ validPtr) **
        (.x20 ↦ᵣ firstBadPtr) ** (.x10 ↦ᵣ o10) ** (validPtr ↦ₘ (1 : Word)) **
        (firstBadPtr ↦ₘ (0 : Word)) ** payload hdrBase lenBase bigBytes lengths **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame
          (spC + signExtend12 (-32 : BitVec 12)) **
        stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
        savedFrame spC csaved) (by unfold payload; pcfx) htaken
    have hallv := cpsTripleWithin_extend_code cvbgm_mono
      (retAllValid sp0 spC raIn csaved
        (payload hdrBase lenBase bigBytes lengths ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame
            (spC + signExtend12 (-32 : BitVec 12)) **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
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
        cvbgmLoopSteps_succ]
      have hiter := cvbgmIter sp0 spC hdrBase lenBase validPtr firstBadPtr raIn csaved bigBytes lengths i
        (cvbgmLoopSteps bigBytes.length (lengths.length - (i + 1))) hi hN hspC hraSaved hret
        (hAllAlign i hi) (hAllLen i hi) (hAllSalign i hi) (hAllSlack i hi) (hAllOver i hi)
        (hAllValid i hi) hpre
        (fun hpre' => ih (i + 1) (by omega) (by omega) hpre')
      have hdrop : (bigBytes.drop (hdrOff lengths i)).length ≤ bigBytes.length := by
        rw [List.length_drop]
        omega
      refine cpsTripleWithin_mono_nSteps (by unfold nCall; omega) hiter


set_option maxRecDepth 8000 in
/-- **`chain_validate_blob_gas_used_multiple` caller contract.**  The
    68-instruction accessor iterates over `N = lengths.length` block headers,
    validating that every header's RLP field 17 (`blob_gas_used`) decodes to a
    `u64` that is a multiple of `GAS_PER_BLOB = 131072 = 2^17`, checked via the
    low-bit mask `value &&& (GAS_PER_BLOB - 1) = value &&& 131071 = 0`.  Its
    three-way post pins the result: all-valid (`a0 = 0`, `*validPtr = 1`, every
    header a multiple), first-violation (`a0 = 0`, `*validPtr = 0`,
    `*firstBad = k`, header `k` not a multiple and all earlier multiples), or
    first parse-failure (`a0 = status`, `*firstBad = k`, header `k` fails the
    strict field-17 decode and all earlier multiples) — each genuinely tied to
    K34's per-header `Result`. -/
theorem chain_validate_blob_gas_used_multiple_spec_within
    (sp0 spC nWord lenBase hdrBase validPtr firstBadPtr raIn
      cs0 cs1 cs2 cs3 cs4 cs5 old5 : Word) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hnWord : nWord = BitVec.ofNat 64 lengths.length)
    (hN : lengths.length < 2 ^ 64)
    (hAllAlign : ∀ i, i < lengths.length → hdrOff lengths i % 8 = 0)
    (hAllLen : ∀ i, i < lengths.length → hdrOff lengths i ≤ bigBytes.length)
    (hAllSalign : ∀ i, i < lengths.length → (hdrBaseAt hdrBase lengths i).toNat % 8 = 0)
    (hAllSlack : ∀ i, i < lengths.length →
      lengths[i]! + 9 ≤ (bigBytes.drop (hdrOff lengths i)).length)
    (hAllOver : ∀ i, i < lengths.length →
      (hdrBaseAt hdrBase lengths i).toNat + (bigBytes.drop (hdrOff lengths i)).length < 2 ^ 64)
    (hAllValid : ∀ i, i < lengths.length → ∀ k, k < (bigBytes.drop (hdrOff lengths i)).length →
      isValidByteAccess (hdrBaseAt hdrBase lengths i + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (17 + cvbgmLoopSteps bigBytes.length lengths.length) D raIn fullCode
      (((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) **
          (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
          (.x10 ↦ᵣ nWord) ** (.x11 ↦ᵣ lenBase) ** (.x12 ↦ᵣ hdrBase) **
          (.x13 ↦ᵣ validPtr) ** (.x14 ↦ᵣ firstBadPtr) ** (.x5 ↦ᵣ old5) **
          (.x0 ↦ᵣ (0 : Word)) **
          memOwn spC ** memOwn (spC + 8) ** memOwn (spC + 16) ** memOwn (spC + 24) **
          memOwn (spC + 32) ** memOwn (spC + 40) ** memOwn (spC + 48) **
          memOwn validPtr ** memOwn firstBadPtr) **
        wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
        memOwn Field ** memOwn RfuOff ** memOwn RfuLen ** memOwn IterPtr ** memOwn IterI **
        regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
        stackFree (spC + signExtend12 (-32 : BitVec 12)) 8)
      (cvbgmPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr ⟨raIn, cs0, cs1, cs2, cs3, cs4, cs5⟩ bigBytes lengths) := by
  have h0 : hdrBaseAt hdrBase lengths 0 = hdrBase := by
    unfold hdrBaseAt hdrOff; simp
  have hsf : savedFrame spC (⟨raIn, cs0, cs1, cs2, cs3, cs4, cs5⟩ : Saved) =
      ((spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) ** ((spC + 24) ↦ₘ cs2) **
        ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5)) := by
    unfold savedFrame; rfl
  have hpro := cpsTripleWithin_frameR
    (wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
      memOwn Field ** memOwn RfuOff ** memOwn RfuLen ** memOwn IterPtr ** memOwn IterI **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
      stackFree (spC + signExtend12 (-32 : BitVec 12)) 8)
    (by pcfx)
    (cpsTripleWithin_extend_code cvbgm_mono
      (cvbgmPrologue sp0 spC nWord lenBase hdrBase validPtr firstBadPtr raIn
        cs0 cs1 cs2 cs3 cs4 cs5 old5 hspC))
  have hloop := cvbgmLoop sp0 spC hdrBase lenBase validPtr firstBadPtr raIn
    ⟨raIn, cs0, cs1, cs2, cs3, cs4, cs5⟩ bigBytes lengths hN hspC rfl hret
    hAllAlign hAllLen hAllSalign hAllSlack hAllOver hAllValid
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
          memOwn Field ** memOwn RfuOff ** memOwn RfuLen ** memOwn IterPtr ** memOwn IterI **
          regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame
            (spC + signExtend12 (-32 : BitVec 12)) **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8)) h := by
      rw [hnWord] at hp; xperm_hyp hp
    have hp2 := sepConj_mono (regIs_implies_regOwn .x1) (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x10) (sepConj_mono (regIs_implies_regOwn .x11)
      (sepConj_mono (regIs_implies_regOwn .x12) (sepConj_mono (regIs_implies_regOwn .x13)
      (sepConj_mono (regIs_implies_regOwn .x14) (fun _ x => x))))))) h hp1
    xperm_hyp hp2) hpro hloop


end EvmAsm.Codegen.ChainValidateBlobGasMultipleSpec
