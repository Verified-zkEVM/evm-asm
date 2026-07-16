/-
  Header-0 block + loop induction + whole-program caller contract for
  `chain_validate_increasing_timestamps`.

  The header-0 block [18-30] decodes header 0's field 11, saves it as the initial
  `prev` (`x21 = ts[0]`), and sets `x6 = base of header 1`, `x7 = 1`, entering the
  loop guard with `LoopInv 1` (whose `⌜hdrTsOk 0 ts[0]⌝` binds the threaded prev to
  the genuine decoded ts[0]).  `cvitLoop` runs the guard/iteration for the
  remaining `N − i` headers (fuel induction, tying each K34 `Result` into the
  accumulating cross-header `hprefix`).  The top-level `spec_within` glues the
  prologue + `BLTU x8, 2` (N<2 vacuous) + header-0 + loop.
-/

import EvmAsm.Codegen.Programs.ChainValidateIncreasingTimestampsLoop

namespace EvmAsm.Codegen.ChainValidateIncreasingTimestampsSpec

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

/-! ## Header-0 K34 call (instructions 18--23 + K34): arg setup ;; jal ;; callee

    From the `N ≥ 2` fall-through (`D+72`) to the header-0 return site (`D+96`),
    producing K34's `flatPost` for header 0 (`listBase = hdrBase`, no spill). -/

set_option maxRecDepth 8000 in
theorem cvitHdr0Call (spC hdrBase lenBase validPtr firstBadPtr x21val : Word) (L0 : Nat)
    (nN oldOut oldOff oldLen old14 oldX1 old5 o10 o11 o12 o13 : Word)
    (bytes : List (BitVec 8)) (csaved : Saved)
    (hsalign : hdrBase.toNat % 8 = 0)
    (hslack : L0 + 9 ≤ bytes.length)
    (hover : hdrBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (hdrBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (5 + 1 + nCall) (D + 72) (D + 96) fullCode
      ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) **
        (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ x21val) **
        (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ o10) ** (.x11 ↦ᵣ o11) ** (.x12 ↦ᵣ o12) ** (.x13 ↦ᵣ o13) **
        (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ oldX1) ** (.x0 ↦ᵣ (0 : Word)) **
        (lenBase ↦ₘ BitVec.ofNat 64 L0) **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
        stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
        (Ts ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        bytesRegion hdrBase bytes ** savedFrame spC csaved)
      ((.x1 ↦ᵣ LinkRA0) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase
          oldOff oldLen (⟨LinkRA0, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hdrBase, Ts, hdrBase, validPtr, firstBadPtr, x21val⟩ : Saved)
          bytes L0 11 **
        (lenBase ↦ₘ BitVec.ofNat 64 L0) ** savedFrame spC csaved) := by
  set calleeNewSp : Word := spC + signExtend12 (-32 : BitVec 12) with hcalleeNewSp
  have hsetup := cpsTripleWithin_extend_code cvit_mono
    (cvitHdr0Setup hdrBase lenBase L0 o10 o11 o12 o13)
  have hsetupF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) **
      (.x21 ↦ᵣ x21val) ** (.x5 ↦ᵣ old5) ** (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ oldX1) **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame calleeNewSp **
      stackFree calleeNewSp 8 **
      (Ts ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
      bytesRegion hdrBase bytes ** savedFrame spC csaved)
    (by pcfx) hsetup
  have hjal := jal_link_spec_within
    (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64
      (GuestAddrs.chain_validate_increasing_timestamps + 92)) (D + 92) oldX1
  rw [show (D + 92) + signExtend21 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64
      (GuestAddrs.chain_validate_increasing_timestamps + 92))
      = EvmAsm.Codegen.RlpFieldToU64SAsm.B from by decide,
    show (D + 92 + 4 : Word) = LinkRA0 from by
      change (D + 92 + 4 : Word) = D + 96; bv_omega] at hjal
  have hjalC := cpsTripleWithin_extend_code cvit_mono
    (cpsTripleWithin_extend_code (cr' := cvitCode)
      (CodeReq.ofProg_mem_at D (D + 92) cvitProg 23
        (.JAL .x1 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64
          (GuestAddrs.chain_validate_increasing_timestamps + 92))) (by bv_omega)
        (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) hjal)
  have hjalF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) **
      (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ x21val) ** (.x5 ↦ᵣ old5) **
      (.x10 ↦ᵣ hdrBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 L0) ** (.x12 ↦ᵣ (11 : Word)) **
      (.x13 ↦ᵣ Ts) ** (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame calleeNewSp **
      stackFree calleeNewSp 8 **
      (Ts ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
      bytesRegion hdrBase bytes ** (lenBase ↦ₘ BitVec.ofNat 64 L0) ** savedFrame spC csaved)
    (by pcfx) hjalC
  have hcallee0 := EvmAsm.Codegen.RlpFieldToU64SAsm.rlpFieldToU64_flat_spec_within
    spC calleeNewSp hdrBase (BitVec.ofNat 64 L0) (11 : Word) Ts oldOut oldOff oldLen old14
    (⟨LinkRA0, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved) hdrBase validPtr firstBadPtr
    x21val bytes L0 11
    hcalleeNewSp rfl (by decide) (by decide)
    hsalign hslack hover hvalid (by show LinkRA0 &&& ~~~(1 : Word) = LinkRA0; decide)
  have hcalleeC := cpsTripleWithin_extend_code k34_mono hcallee0
  have hcallee : cpsTripleWithin nCall EvmAsm.Codegen.RlpFieldToU64SAsm.B LinkRA0 fullCode
      (regOwn .x5 **
        ((.x1 ↦ᵣ LinkRA0) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
          (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ x21val) **
          (.x10 ↦ᵣ hdrBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 L0) ** (.x12 ↦ᵣ (11 : Word)) **
          (.x13 ↦ᵣ Ts) ** (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame calleeNewSp **
          stackFree calleeNewSp 8 ** bytesRegion hdrBase bytes **
          (Ts ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen)))
      ((.x1 ↦ᵣ LinkRA0) **
        EvmAsm.Codegen.RlpFieldToU64SAsm.flatPost spC calleeNewSp hdrBase oldOff oldLen
          (⟨LinkRA0, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64SAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64SAsm.B + 48, hdrBase, Ts, hdrBase, validPtr, firstBadPtr, x21val⟩ : Saved)
          bytes L0 11) :=
    cpsTripleWithin_weaken (fun h hp => by
      unfold EvmAsm.Codegen.RlpFieldToU64SAsm.flatPre EvmAsm.Codegen.RlpFieldToU64SAsm.wholeRest
      xperm_hyp hp) (fun _ hq => hq) hcalleeC
  have hcalleeF := cpsTripleWithin_frameR
    ((lenBase ↦ₘ BitVec.ofNat 64 L0) ** savedFrame spC csaved)
    (by pcfx) hcallee
  have hsj := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsetupF hjalF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => ?_) hsj hcalleeF)
  have hp' : ((.x5 ↦ᵣ old5) **
      ((.x1 ↦ᵣ LinkRA0) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
        (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ x21val) **
        (.x10 ↦ᵣ hdrBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 L0) ** (.x12 ↦ᵣ (11 : Word)) **
        (.x13 ↦ᵣ Ts) ** (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame calleeNewSp **
        stackFree calleeNewSp 8 ** bytesRegion hdrBase bytes **
        (Ts ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        (lenBase ↦ₘ BitVec.ofNat 64 L0) ** savedFrame spC csaved)) h := by
    xperm_hyp hp
  have hp'' := sepConj_mono (regIs_implies_regOwn .x5) (fun _ x => x) h hp'
  xperm_hyp hp''

#print axioms cvitHdr0Call

/-! ## Header-0 finish (instructions 25--30): save initial prev, set base_1, i:=1

    On the header-0 K34-success path (`D+100` → the loop guard `D+124`):
    `x21 := *cvit_ts` (the decoded `ts[0]`, the initial `prev`), `x5 := *lenBase`
    (`= lengths[0]`), `x6 := hdrBase + lengths[0]` (base of header 1), `x7 := 1`. -/

set_option maxRecDepth 8000 in
theorem cvitHdr0Finish (hdrBase lenBase ts0 : Word) (L0 : Nat) (old5 o6 o7 o21 : Word) :
    cpsTripleWithin 6 (D + 100) (D + 124) cvitCode
      ((.x5 ↦ᵣ old5) ** (.x21 ↦ᵣ o21) ** (.x6 ↦ᵣ o6) ** (.x7 ↦ᵣ o7) **
        (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (Ts ↦ₘ ts0) **
        (lenBase ↦ₘ BitVec.ofNat 64 L0))
      ((.x5 ↦ᵣ BitVec.ofNat 64 L0) ** (.x21 ↦ᵣ ts0) **
        (.x6 ↦ᵣ (hdrBase + BitVec.ofNat 64 L0)) ** (.x7 ↦ᵣ (1 : Word)) **
        (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (Ts ↦ₘ ts0) **
        (lenBase ↦ₘ BitVec.ofNat 64 L0)) := by
  have hla25 := la_materialize_within .x5 old5 (D + 100) Ts (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 100) cvitProg 25 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 100) Ts)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 104) cvitProg 26 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 100) Ts)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
  have s27 := ld_spec_gen_within .x21 .x5 Ts o21 ts0 (0 : BitVec 12) (D + 108) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show Ts + (0 : Word) = Ts from by bv_omega] at s27
  have s27' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 108) cvitProg 27 (.LD .x21 .x5 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s27
  have s28 := ld_spec_gen_within .x5 .x9 lenBase Ts (BitVec.ofNat 64 L0) (0 : BitVec 12) (D + 112) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show lenBase + (0 : Word) = lenBase from by bv_omega] at s28
  have s28' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 112) cvitProg 28 (.LD .x5 .x9 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s28
  have s29 := add_spec_gen_within .x6 .x18 .x5 hdrBase (BitVec.ofNat 64 L0) o6 (D + 116) (by decide)
  have s29' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 116) cvitProg 29 (.ADD .x6 .x18 .x5)
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s29
  have s30 := li_spec_gen_within .x7 o7 (1 : Word) (D + 120) (by decide)
  have s30' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 120) cvitProg 30 (.LI .x7 (1 : Word))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s30
  runBlock hla25 s27' s28' s29' s30'

#print axioms cvitHdr0Finish

/-! ## Loop induction (`D+124 → raIn`, entering iteration `i`, `1 ≤ i ≤ N`)

    Fuel induction on the remaining header count `N − i`.  On `i = N` the guard
    `beq x7, x8` is taken and the all-valid exit returns `postAllValid` (the
    accumulated `hprefix` carried inside `LoopInv` becomes the "every adjacent
    pair strictly increasing" witness).  Otherwise one `cvitIter` runs and the
    induction hypothesis handles the rest, threading the genuine `prevVal`. -/

/-- Step budget for the loop with `r = N − i` iterations remaining: each full
    iteration is `cvitIter`'s cost, the exhausted guard + all-valid exit is
    `11` (guard `1` + `retAllValid` `10`). -/
def cvitLoopSteps : Nat → Nat
  | 0 => 11
  | r + 1 => (1 + (16 + 1 + nCall)) + (24 + cvitLoopSteps r)

theorem cvitLoopSteps_succ (r : Nat) :
    cvitLoopSteps (r + 1) = (1 + (16 + 1 + nCall)) + (24 + cvitLoopSteps r) := rfl

set_option maxRecDepth 8000 in
theorem cvitLoop (sp0 spC hdrBase lenBase validPtr firstBadPtr raIn : Word)
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
    ∀ (f i : Nat), lengths.length - i ≤ f → 1 ≤ i → i ≤ lengths.length →
      cpsTripleWithin (cvitLoopSteps (lengths.length - i)) (D + 124) raIn fullCode
        (LoopInv sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths i)
        (cvitPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths) := by
  have hsf : savedFrame spC csaved =
      ((spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) := by
    unfold savedFrame; rw [hraSaved]
  -- All-valid exit reached at the guard when `i = N`.
  have base :
      cpsTripleWithin (cvitLoopSteps 0) (D + 124) raIn fullCode
        (LoopInv sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths lengths.length)
        (cvitPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths) := by
    unfold LoopInv
    refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun prevVal => ?_)
    refine cpsTripleWithin_pure_pre (fun hP => ?_)
    obtain ⟨_hprevOk, hprefix⟩ := hP
    -- Expose x1 / x10 (overwritten by the exit block) as concrete regs.
    refine cpsTripleWithin_weaken (fun h hp => by unfold payload scratchRegs at hp; xperm_hyp hp)
      (fun _ hq => hq)
      (show cpsTripleWithin (cvitLoopSteps 0) (D + 124) raIn fullCode
        ((((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
            (.x6 ↦ᵣ hdrBaseAt hdrBase lengths lengths.length) ** (.x18 ↦ᵣ hdrBase) **
            (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) **
            (.x7 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x21 ↦ᵣ prevVal) **
            savedFrame spC csaved ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
            wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
            memOwn Ts ** memOwn RfuOff ** memOwn RfuLen ** memOwn IterChild ** memOwn IterI **
            memOwn IterPrev ** regOwn .x5 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
            regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) **
            frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8) ** regOwn .x1) ** regOwn .x10)
        (cvitPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths) from ?_)
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun o10 => ?_)
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
      (show cpsTripleWithin (cvitLoopSteps 0) (D + 124) raIn fullCode
        (((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
            (.x6 ↦ᵣ hdrBaseAt hdrBase lengths lengths.length) ** (.x18 ↦ᵣ hdrBase) **
            (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) **
            (.x7 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x21 ↦ᵣ prevVal) **
            savedFrame spC csaved ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
            wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
            memOwn Ts ** memOwn RfuOff ** memOwn RfuLen ** memOwn IterChild ** memOwn IterI **
            memOwn IterPrev ** regOwn .x5 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
            regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) **
            frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 ** (.x10 ↦ᵣ o10)) ** regOwn .x1)
        (cvitPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths) from ?_)
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun o1 => ?_)
    -- Guard `beq x7 x8` taken (i = N).
    have hbeq := beq_spec_gen_within .x7 .x8 (204 : BitVec 13)
      (BitVec.ofNat 64 lengths.length) (BitVec.ofNat 64 lengths.length) (D + 124)
    have hbeqC := cpsBranchWithin_extend_code cvit_mono
      (cpsBranchWithin_extend_code (cr' := cvitCode)
        (CodeReq.ofProg_mem_at D (D + 124) cvitProg 31 (.BEQ .x7 .x8 (204 : BitVec 13))
          (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) hbeq)
    have htaken := cpsBranchWithin_takenStripPure2 hbeqC (fun hp hq => by
      obtain ⟨_, _, _, _, _, hrest⟩ := hq
      exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
    rw [show (D + 124) + signExtend13 (204 : BitVec 13) = D + 328 from by
      rw [show signExtend13 (204 : BitVec 13) = (204 : Word) from by decide]; bv_omega] at htaken
    have htakenF := cpsTripleWithin_frameR
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x9 ↦ᵣ lenBase) **
        (.x6 ↦ᵣ hdrBaseAt hdrBase lengths lengths.length) ** (.x18 ↦ᵣ hdrBase) **
        (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) ** (.x10 ↦ᵣ o10) **
        savedFrame spC csaved ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
        wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
        memOwn Ts ** memOwn RfuOff ** memOwn RfuLen ** memOwn IterChild ** memOwn IterI **
        memOwn IterPrev ** regOwn .x5 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
        stackFree (spC + signExtend12 (-32 : BitVec 12)) 8) (by pcfx) htaken
    have hallv := cpsTripleWithin_extend_code cvit_mono
      (retAllValid sp0 spC raIn csaved
        ((validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
          wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
          memOwn Ts ** memOwn RfuOff ** memOwn RfuLen ** memOwn IterChild ** memOwn IterI **
          memOwn IterPrev ** regOwn .x5 ** (.x6 ↦ᵣ hdrBaseAt hdrBase lengths lengths.length) **
          (.x7 ↦ᵣ BitVec.ofNat 64 lengths.length) ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8)
        (by pcfx) o10 o1 (BitVec.ofNat 64 lengths.length) lenBase hdrBase validPtr firstBadPtr
        prevVal hspC hraSaved hret)
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
      (cpsTripleWithin_seq_perm_same_cr (fun h hp => by rw [hsf] at hp; xperm_hyp hp)
        htakenF hallv)
    -- Assemble the all-valid post (the accumulated prefix witnesses every pair).
    refine Or.inl ?_
    unfold postAllValid commonRet payload
    refine (sepConj_pure_left h).mpr ⟨Or.inr hprefix, ?_⟩
    rw [hsf, hraSaved]
    have hp1 : ((.x6 ↦ᵣ hdrBaseAt hdrBase lengths lengths.length) **
        (.x7 ↦ᵣ BitVec.ofNat 64 lengths.length) **
        ((.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
          (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ csaved.s0) ** (.x9 ↦ᵣ csaved.s1) **
          (.x18 ↦ᵣ csaved.s2) ** (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) **
          (.x21 ↦ᵣ csaved.s5) **
          (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
          ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
          ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
          regOwn .x5 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64SAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
          wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
          memOwn Ts ** memOwn RfuOff ** memOwn RfuLen ** memOwn IterChild ** memOwn IterI **
          memOwn IterPrev)) h := by xperm_hyp hq
    have hp2 := sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7) (fun _ x => x)) h hp1
    xperm_hyp hp2
  -- Fuel induction on `N - i`.
  intro f
  induction f with
  | zero =>
    intro i hf _hi1 hiN
    have hi : i = lengths.length := by omega
    subst hi
    rw [Nat.sub_self]
    exact base
  | succ f ih =>
    intro i hf hi1 hiN
    rcases (by omega : i = lengths.length ∨ i < lengths.length) with hi | hi
    · subst hi; rw [Nat.sub_self]; exact base
    · rw [show lengths.length - i = (lengths.length - (i + 1)) + 1 from by omega,
        cvitLoopSteps_succ]
      exact cvitIter sp0 spC hdrBase lenBase validPtr firstBadPtr raIn csaved bigBytes lengths i
        (cvitLoopSteps (lengths.length - (i + 1))) hi1 hi hN hspC hraSaved hret
        (hAllAlign i hi) (hAllLen i hi) (hAllSalign i hi) (hAllSlack i hi) (hAllOver i hi)
        (hAllValid i hi)
        (fun _ => ih (i + 1) (by omega) (by omega) (by omega))

#print axioms cvitLoop

end EvmAsm.Codegen.ChainValidateIncreasingTimestampsSpec
