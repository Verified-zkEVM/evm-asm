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
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.ChainValidateOfflineAddrs

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
      | unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame)

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
    cpsTripleWithin (5 + 1 + nCall bytes.length) (D + 72) (D + 96) fullCode
      ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) **
        (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ x21val) **
        (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ o10) ** (.x11 ↦ᵣ o11) ** (.x12 ↦ᵣ o12) ** (.x13 ↦ᵣ o13) **
        (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ oldX1) ** (.x0 ↦ᵣ (0 : Word)) **
        (lenBase ↦ₘ BitVec.ofNat 64 L0) **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
        stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
        (Ts ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        bytesRegion hdrBase bytes ** savedFrame spC csaved)
      ((.x1 ↦ᵣ LinkRA0) **
        EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase
          oldOff oldLen (⟨LinkRA0, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B + 48, hdrBase, Ts, hdrBase, validPtr, firstBadPtr, x21val⟩ : Saved)
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
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame calleeNewSp **
      stackFree calleeNewSp 8 **
      (Ts ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
      bytesRegion hdrBase bytes ** savedFrame spC csaved)
    (by pcfx) hsetup
  have hjal := jal_link_spec_within
    (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64_strict
      (ChainValidateOfflineAddrs.chain_validate_increasing_timestamps + 92)) (D + 92) oldX1
  rw [show (D + 92) + signExtend21 (jalOff GuestAddrs.rlp_field_to_u64_strict
      (ChainValidateOfflineAddrs.chain_validate_increasing_timestamps + 92)) = EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B from by
    change BitVec.ofNat 64 ChainValidateOfflineAddrs.chain_validate_increasing_timestamps + BitVec.ofNat 64 92 + _ =
      BitVec.ofNat 64 GuestAddrs.rlp_field_to_u64_strict
    exact jalOff_correct_add GuestAddrs.rlp_field_to_u64_strict ChainValidateOfflineAddrs.chain_validate_increasing_timestamps 92
      (by decide) (by decide) (by decide) (by decide),
    show (D + 92 + 4 : Word) = LinkRA0 from by
      change (D + 92 + 4 : Word) = D + 96; bv_omega] at hjal
  have hjalC := cpsTripleWithin_extend_code cvit_mono
    (cpsTripleWithin_extend_code (cr' := cvitCode)
      (CodeReq.ofProg_mem_at D (D + 92) cvitProg 23
        (.JAL .x1 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64_strict
          (ChainValidateOfflineAddrs.chain_validate_increasing_timestamps + 92))) (by bv_omega)
        (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) hjal)
  have hjalF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) **
      (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ x21val) ** (.x5 ↦ᵣ old5) **
      (.x10 ↦ᵣ hdrBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 L0) ** (.x12 ↦ᵣ (11 : Word)) **
      (.x13 ↦ᵣ Ts) ** (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame calleeNewSp **
      stackFree calleeNewSp 8 **
      (Ts ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
      bytesRegion hdrBase bytes ** (lenBase ↦ₘ BitVec.ofNat 64 L0) ** savedFrame spC csaved)
    (by pcfx) hjalC
  have hcallee0 := EvmAsm.Codegen.RlpFieldToU64StrictSAsm.rlpFieldToU64_flat_spec_within
    spC calleeNewSp hdrBase (BitVec.ofNat 64 L0) (11 : Word) Ts oldOut oldOff oldLen old14
    (⟨LinkRA0, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved) hdrBase validPtr firstBadPtr
    x21val bytes L0 11
    hcalleeNewSp rfl (by decide) (by decide)
    hsalign hslack hover hvalid (by show LinkRA0 &&& ~~~(1 : Word) = LinkRA0; decide)
  have hcalleeC := cpsTripleWithin_extend_code k34_mono hcallee0
  have hcallee : cpsTripleWithin (nCall bytes.length) EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B LinkRA0 fullCode
      (regOwn .x5 **
        ((.x1 ↦ᵣ LinkRA0) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
          (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ x21val) **
          (.x10 ↦ᵣ hdrBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 L0) ** (.x12 ↦ᵣ (11 : Word)) **
          (.x13 ↦ᵣ Ts) ** (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame calleeNewSp **
          stackFree calleeNewSp 8 ** bytesRegion hdrBase bytes **
          (Ts ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen)))
      ((.x1 ↦ᵣ LinkRA0) **
        EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPost spC calleeNewSp hdrBase oldOff oldLen
          (⟨LinkRA0, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B + 48, hdrBase, Ts, hdrBase, validPtr, firstBadPtr, x21val⟩ : Saved)
          bytes L0 11) :=
    cpsTripleWithin_weaken (fun h hp => by
      unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPre EvmAsm.Codegen.RlpFieldToU64StrictSAsm.wholeRest
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
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame calleeNewSp **
        stackFree calleeNewSp 8 ** bytesRegion hdrBase bytes **
        (Ts ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        (lenBase ↦ₘ BitVec.ofNat 64 L0) ** savedFrame spC csaved)) h := by
    xperm_hyp hp
  have hp'' := sepConj_mono (regIs_implies_regOwn .x5) (fun _ x => x) h hp'
  xperm_hyp hp''


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


/-! ## Loop induction (`D+124 → raIn`, entering iteration `i`, `1 ≤ i ≤ N`)

    Fuel induction on the remaining header count `N − i`.  On `i = N` the guard
    `beq x7, x8` is taken and the all-valid exit returns `postAllValid` (the
    accumulated `hprefix` carried inside `LoopInv` becomes the "every adjacent
    pair strictly increasing" witness).  Otherwise one `cvitIter` runs and the
    induction hypothesis handles the rest, threading the genuine `prevVal`. -/

/-- Step budget for the loop with `r = N − i` iterations remaining: each full
    iteration is `cvitIter`'s cost, the exhausted guard + all-valid exit is
    `11` (guard `1` + `retAllValid` `10`). -/
def cvitLoopSteps (bytesLen : Nat) : Nat → Nat
  | 0 => 11
  | r + 1 => (1 + (16 + 1 + nCall bytesLen)) + (24 + cvitLoopSteps bytesLen r)

theorem cvitLoopSteps_succ (bytesLen r : Nat) :
    cvitLoopSteps bytesLen (r + 1) =
      (1 + (16 + 1 + nCall bytesLen)) + (24 + cvitLoopSteps bytesLen r) := rfl

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
      cpsTripleWithin (cvitLoopSteps bigBytes.length (lengths.length - i)) (D + 124) raIn fullCode
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
      cpsTripleWithin (cvitLoopSteps bigBytes.length 0) (D + 124) raIn fullCode
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
      (show cpsTripleWithin (cvitLoopSteps bigBytes.length 0) (D + 124) raIn fullCode
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
            frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8) ** regOwn .x1) ** regOwn .x10)
        (cvitPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths) from ?_)
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun o10 => ?_)
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
      (show cpsTripleWithin (cvitLoopSteps bigBytes.length 0) (D + 124) raIn fullCode
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
            frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
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
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
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
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
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
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
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
      have hiter := cvitIter sp0 spC hdrBase lenBase validPtr firstBadPtr raIn csaved bigBytes lengths i
        (cvitLoopSteps bigBytes.length (lengths.length - (i + 1))) hi1 hi hN hspC hraSaved hret
        (hAllAlign i hi) (hAllLen i hi) (hAllSalign i hi) (hAllSlack i hi) (hAllOver i hi)
        (hAllValid i hi)
        (fun _ => ih (i + 1) (by omega) (by omega) (by omega))
      have hdrop : (bigBytes.drop (hdrOff lengths i)).length ≤ bigBytes.length := by
        rw [List.length_drop]
        omega
      refine cpsTripleWithin_mono_nSteps (by unfold nCall; omega) hiter


/-! ## Header-0 flatPost normalization (K34 saved-ra = `LinkRA0`)

    The header-0 call links with `ra = LinkRA0` (`D+96`), so K34's restored saved
    frame carries `LinkRA0` rather than `LinkRA`.  `dispNorm0`/`flatPost_normalize0`
    are the `LinkRA0` analogues of `dispNorm`/`flatPost_normalize`; the saved-ra
    value is only ever framed through (erased by `k34SavedFrame_implies_frameSlotsOwn`
    at the point `LoopInv 1` is built), so it never reaches the post. -/

def dispNorm0 (spC calleeNewSp hbi hdrBase validPtr firstBadPtr nN lenBase prevVal
    value status : Word) (bytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
  (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) **
  (.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** (Ts ↦ₘ value) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  memOwn RfuOff ** memOwn RfuLen ** stackFree calleeNewSp 8 **
  bytesRegion hbi bytes **
  EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame calleeNewSp ⟨LinkRA0, nN, lenBase⟩

set_option maxRecDepth 8000 in
theorem flatPost_normalize0 (spC hbi hdrBase validPtr firstBadPtr nN lenBase prevVal
    oldOff oldLen : Word) (bytes : List (BitVec 8)) (Li : Nat) : ∀ h,
    (EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12)) hbi
      oldOff oldLen (⟨LinkRA0, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved)
      (⟨EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B + 48, hbi, Ts, hdrBase, validPtr, firstBadPtr, prevVal⟩ : Saved)
      bytes Li 11) h →
    (∃ status value,
      (dispNorm0 spC (spC + signExtend12 (-32 : BitVec 12)) hbi hdrBase validPtr firstBadPtr nN
          lenBase prevVal value status bytes **
        ⌜EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result bytes hbi Li 11 status value⌝) h) := by
  intro h hp
  unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPost at hp
  rcases hp with hs | hf
  · unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatSuccessReturned at hs
    obtain ⟨offset, len, v12, x5v, scalarStatus, wrapperStatus, outputValue, hs⟩ := hs
    unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.successPayload at hs
    refine ⟨wrapperStatus, outputValue, ?_⟩
    obtain ⟨h1, h2, hd, hu, hO, hP⟩ := hs
    obtain ⟨hBig, hRes⟩ := (sepConj_pure_right _).1 hP
    refine (sepConj_pure_right _).2 ⟨?_, hRes⟩
    have hOB : (_ ** _) h := ⟨h1, h2, hd, hu, hO, hBig⟩
    unfold dispNorm0
    have hp1 : ((RfuOff ↦ₘ offset) ** (RfuLen ↦ₘ len) ** (.x5 ↦ᵣ x5v) **
        (.x11 ↦ᵣ scalarStatus) ** (.x12 ↦ᵣ v12) **
        ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) **
          (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) **
          (.x10 ↦ᵣ wrapperStatus) ** (.x0 ↦ᵣ (0 : Word)) ** (Ts ↦ₘ outputValue) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 ** bytesRegion hbi bytes **
          EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
            ⟨LinkRA0, nN, lenBase⟩)) h := by xperm_hyp hOB
    have hp2 := sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
      (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12) (fun _ x => x))))) h hp1
    xperm_hyp hp2
  · unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatFailureReturned at hf
    obtain ⟨v11, v12, hf⟩ := hf
    unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.failurePayload at hf
    refine ⟨(1 : Word), (0 : Word), ?_⟩
    obtain ⟨h1, h2, hd, hu, hO, hP⟩ := hf
    obtain ⟨hBig, hRes⟩ := (sepConj_pure_right _).1 hP
    refine (sepConj_pure_right _).2 ⟨?_, hRes⟩
    have hOB : (_ ** _) h := ⟨h1, h2, hd, hu, hO, hBig⟩
    unfold dispNorm0
    have hp1 : ((RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) ** (.x11 ↦ᵣ v11) **
        (.x12 ↦ᵣ v12) **
        ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) **
          (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ prevVal) **
          (.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (Ts ↦ₘ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 ** bytesRegion hbi bytes **
          EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
            ⟨LinkRA0, nN, lenBase⟩)) h := by xperm_hyp hOB
    have hp2 := sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
      (sepConj_mono (regIs_implies_regOwn .x11) (sepConj_mono (regIs_implies_regOwn .x12)
        (fun _ x => x)))) h hp1
    xperm_hyp hp2


/-! ## Header-0 status dispatch (instruction 24 onward): tie header-0's `Result`

    From K34's header-0 `flatPost` at the `bne` return site (`D+96`) to the
    caller's post.  `bne x10, x0` [24] splits on the status: on parse-fail
    (`status ≠ 0`) it exits via `retParseFail` reporting index `0` (the
    zero-initialized `cvit_iter_i`); on success (`status = 0`) `cvitHdr0Finish`
    [25-30] saves the decoded `ts[0]` as the initial `prev`, sets `x6 = base of
    header 1`, `x7 = 1`, reaching `LoopInv 1` (whose `⌜hdrTsOk 0 ts[0]⌝` binds
    the threaded prev to the genuine decoded `ts[0]`) and the loop tail. -/

set_option maxRecDepth 8000 in
theorem cvitHdr0Dispatch
    (sp0 spC hdrBase lenBase validPtr firstBadPtr raIn x21val : Word) (L0 : Nat)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat)
    (oldOff oldLen : Word) (nTail : Nat)
    (hN2 : 2 ≤ lengths.length)
    (hL0 : L0 = lengths[0]!)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (htail : cpsTripleWithin nTail (D + 124) raIn fullCode
        (LoopInv sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths 1)
        (cvitPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths)) :
    cpsTripleWithin (22 + nTail) (D + 96) raIn fullCode
      ((.x1 ↦ᵣ LinkRA0) **
        EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPost spC (spC + signExtend12 (-32 : BitVec 12))
          hdrBase oldOff oldLen
          (⟨LinkRA0, BitVec.ofNat 64 lengths.length, lenBase⟩ :
            EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B + 48, hdrBase, Ts, hdrBase, validPtr,
            firstBadPtr, x21val⟩ : Saved)
          bigBytes L0 11 **
        (lenBase ↦ₘ BitVec.ofNat 64 L0) **
        wordArrayFrom lenBase 1 (lengths.drop 1) **
        (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
        (IterI ↦ₘ (0 : Word)) ** memOwn IterChild ** memOwn IterPrev **
        savedFrame spC csaved)
      (cvitPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths) := by
  subst hL0
  have hLen0 : lengths[0]! = lengths[0] := getElem!_pos lengths 0 (by omega)
  have hHB0 : hdrBaseAt hdrBase lengths 0 = hdrBase := by unfold hdrBaseAt hdrOff; simp
  have hdrop0 : bigBytes.drop (hdrOff lengths 0) = bigBytes := by unfold hdrOff; simp
  have hHB1 : hdrBaseAt hdrBase lengths 1 = hdrBase + BitVec.ofNat 64 lengths[0]! := by
    rw [show (1 : Nat) = 0 + 1 from rfl, hdrBaseAt_succ hdrBase lengths 0 (by omega), hHB0]
  have hsf : savedFrame spC csaved =
      ((spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) := by
    unfold savedFrame; rw [hraSaved]
  -- wordArray reassembly at index 0 (header 0 read `lenBase` but did not modify it).
  have hwa : wordArray lenBase lengths =
      ((lenBase ↦ₘ BitVec.ofNat 64 lengths[0]!) ** wordArrayFrom lenBase 1 (lengths.drop 1)) := by
    rw [wordArray_split lenBase lengths 0 (by omega),
      show BitVec.ofNat 64 (8 * 0) = (0 : Word) from by decide,
      show lenBase + (0 : Word) = lenBase from by bv_omega,
      show lengths.take 0 = ([] : List Nat) from rfl,
      show wordArrayFrom lenBase 0 ([] : List Nat) = empAssertion from rfl,
      ← hLen0, sepConj_emp_left']
  -- Normalize K34's flatPost, stripping the (status, value) existentials.
  refine cpsTripleWithin_weaken (fun h hp => ?hstrip) (fun _ hq => hq)
    (EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun status =>
      EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun value =>
        (show cpsTripleWithin (22 + nTail) (D + 96) raIn fullCode
          ((.x1 ↦ᵣ LinkRA0) **
            (dispNorm0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase hdrBase validPtr
                firstBadPtr (BitVec.ofNat 64 lengths.length) lenBase x21val value status bigBytes **
              ⌜EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result bigBytes hdrBase lengths[0]! 11 status value⌝) **
            (lenBase ↦ₘ BitVec.ofNat 64 lengths[0]!) **
            wordArrayFrom lenBase 1 (lengths.drop 1) **
            (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
            (IterI ↦ₘ (0 : Word)) ** memOwn IterChild ** memOwn IterPrev **
            savedFrame spC csaved)
          (cvitPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
            firstBadPtr csaved bigBytes lengths) from ?core))))
  case hstrip =>
    obtain ⟨s1, s2, hd, hu, hx1, s3, s4, hd2, hu2, hfp, hREST⟩ := hp
    obtain ⟨status, value, hnorm⟩ := flatPost_normalize0 spC hdrBase hdrBase validPtr firstBadPtr
      (BitVec.ofNat 64 lengths.length) lenBase x21val oldOff oldLen bigBytes lengths[0]! s3 hfp
    exact ⟨status, value, s1, s2, hd, hu, hx1, s3, s4, hd2, hu2, hnorm, hREST⟩
  case core =>
    refine cpsTripleWithin_weaken (fun h hp => ?hpull) (fun _ hq => hq)
      (cpsTripleWithin_pure_pre
        (P := EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result bigBytes hdrBase lengths[0]! 11 status value)
        (H := (.x1 ↦ᵣ LinkRA0) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
          (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) **
          (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ x21val) ** (.x10 ↦ᵣ status) **
          (.x0 ↦ᵣ (0 : Word)) ** (Ts ↦ₘ value) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
          bytesRegion hdrBase bigBytes **
          EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
            ⟨LinkRA0, BitVec.ofNat 64 lengths.length, lenBase⟩ **
          (lenBase ↦ₘ BitVec.ofNat 64 lengths[0]!) **
          wordArrayFrom lenBase 1 (lengths.drop 1) **
          (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
          (IterI ↦ₘ (0 : Word)) ** memOwn IterChild ** memOwn IterPrev **
          savedFrame spC csaved)
        (fun hResult => ?body))
    case hpull =>
      unfold dispNorm0 at hp
      xperm_hyp hp
    case body =>
      by_cases hstatus : status = 0
      · -- SUCCESS: `bne` not taken → header-0 finish → LoopInv 1 → loop tail.
        subst hstatus
        have hbne := bne_spec_gen_within .x10 .x0 (212 : BitVec 13) (0 : Word) (0 : Word) (D + 96)
        have hbneC := cpsBranchWithin_extend_code cvit_mono
          (cpsBranchWithin_extend_code (cr' := cvitCode)
            (CodeReq.ofProg_mem_at D (D + 96) cvitProg 24 (.BNE .x10 .x0 (212 : BitVec 13))
              (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) hbne)
        have hntaken := cpsBranchWithin_ntakenStripPure2 hbneC (fun hp hq => by
          obtain ⟨_, _, _, _, _, hrest⟩ := hq
          exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
        rw [show (D + 96 + 4 : Word) = D + 100 from by bv_omega] at hntaken
        set Rframe : Assertion :=
          ((.x1 ↦ᵣ LinkRA0) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
            (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) **
            (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ x21val) ** (Ts ↦ₘ value) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
            regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
            bytesRegion hdrBase bigBytes **
            EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
              ⟨LinkRA0, BitVec.ofNat 64 lengths.length, lenBase⟩ **
            (lenBase ↦ₘ BitVec.ofNat 64 lengths[0]!) **
            wordArrayFrom lenBase 1 (lengths.drop 1) **
            (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
            (IterI ↦ₘ (0 : Word)) ** memOwn IterChild ** memOwn IterPrev **
            savedFrame spC csaved) with hRframe
        have hntakenF := cpsTripleWithin_frameR Rframe (by rw [hRframe]; pcfx) hntaken
        refine cpsTripleWithin_weaken (fun h hp => by rw [hRframe]; xperm_hyp hp) (fun _ hq => hq)
          (cpsTripleWithin_mono_nSteps (show 1 + (6 + nTail) ≤ 22 + nTail by omega)
            (cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hntakenF ?hcont))
        -- The continuation `D+100 → raIn`: peel x5/x6/x7, finish, LoopInv 1, tail.
        rw [hRframe]
        refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
          (show cpsTripleWithin (6 + nTail) (D + 100) raIn fullCode
            (((.x1 ↦ᵣ LinkRA0) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
              (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) **
              (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ x21val) ** (.x10 ↦ᵣ (0 : Word)) **
              (.x0 ↦ᵣ (0 : Word)) ** (Ts ↦ₘ value) ** regOwn .x28 ** regOwn .x29 **
              regOwn .x30 ** regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
              stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              bytesRegion hdrBase bigBytes **
              EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                ⟨LinkRA0, BitVec.ofNat 64 lengths.length, lenBase⟩ **
              (lenBase ↦ₘ BitVec.ofNat 64 lengths[0]!) **
              wordArrayFrom lenBase 1 (lengths.drop 1) **
              (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
              (IterI ↦ₘ (0 : Word)) ** memOwn IterChild ** memOwn IterPrev **
              savedFrame spC csaved) **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
              regOwn .x13 ** regOwn .x14)
            (cvitPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
              firstBadPtr csaved bigBytes lengths) from ?_)
        refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_of_forall_regIs_to_regOwn7
          (fun v5 v6 v7 v11 v12 v13 v14 => ?_)
        have hfin := cpsTripleWithin_extend_code cvit_mono
          (cvitHdr0Finish hdrBase lenBase value lengths[0]! v5 v6 v7 x21val)
        have hfinF := cpsTripleWithin_frameR
          ((.x1 ↦ᵣ LinkRA0) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
            (.x19 ↦ᵣ validPtr) **
            (.x20 ↦ᵣ firstBadPtr) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** regOwn .x28 **
            regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
            bytesRegion hdrBase bigBytes **
            EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
              ⟨LinkRA0, BitVec.ofNat 64 lengths.length, lenBase⟩ **
            wordArrayFrom lenBase 1 (lengths.drop 1) **
            (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
            (IterI ↦ₘ (0 : Word)) ** memOwn IterChild ** memOwn IterPrev **
            savedFrame spC csaved) (by pcfx) hfin
        refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
          (cpsTripleWithin_seq_perm_same_cr (fun h hp => by
            unfold LoopInv payload scratchRegs
            rw [hsf, hwa, hHB1, show BitVec.ofNat 64 1 = (1 : Word) from by decide]
            refine ⟨value, (sepConj_pure_left h).mpr
              ⟨⟨by unfold hdrTsOk; rw [show (1 : Nat) - 1 = 0 from rfl, hdrop0, hHB0]; exact hResult,
                fun j hj1 hj => by omega⟩, ?_⟩⟩
            have hp1 : ((.x1 ↦ᵣ LinkRA0) ** (.x5 ↦ᵣ BitVec.ofNat 64 lengths[0]!) **
                (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
                (.x14 ↦ᵣ v14) ** (Ts ↦ₘ value) ** (IterI ↦ₘ (0 : Word)) **
                EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                  ⟨LinkRA0, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
                  (.x6 ↦ᵣ (hdrBase + BitVec.ofNat 64 lengths[0]!)) ** (.x18 ↦ᵣ hdrBase) **
                  (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x7 ↦ᵣ (1 : Word)) **
                  (.x21 ↦ᵣ value) **
                  (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                  ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                  ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                  (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
                  (lenBase ↦ₘ BitVec.ofNat 64 lengths[0]!) **
                  wordArrayFrom lenBase 1 (lengths.drop 1) **
                  bytesRegion hdrBase bigBytes **
                  memOwn RfuOff ** memOwn RfuLen ** memOwn IterChild ** memOwn IterPrev **
                  regOwn .x28 **
                  regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
                  stackFree (spC + signExtend12 (-32 : BitVec 12)) 8)) h := by
              rw [hsf] at hp; xperm_hyp hp
            have hp2 := sepConj_mono (regIs_implies_regOwn .x1)
              (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x10)
              (sepConj_mono (regIs_implies_regOwn .x11) (sepConj_mono (regIs_implies_regOwn .x12)
              (sepConj_mono (regIs_implies_regOwn .x13) (sepConj_mono (regIs_implies_regOwn .x14)
              (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
              (sepConj_mono (k34SavedFrame_implies_frameSlotsOwn _ _)
                (fun _ x => x)))))))))) h hp1
            xperm_hyp hp2) hfinF htail)
      · -- PARSE-FAIL: `bne` taken → retParseFail reporting index 0.
        refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
          (show cpsTripleWithin (22 + nTail) (D + 96) raIn fullCode
            (((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkRA0) ** (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) **
              (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ x21val) ** (Ts ↦ₘ value) **
              regOwn .x7 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              memOwn RfuOff ** memOwn RfuLen **
              stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              bytesRegion hdrBase bigBytes **
              EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                ⟨LinkRA0, BitVec.ofNat 64 lengths.length, lenBase⟩ **
              (lenBase ↦ₘ BitVec.ofNat 64 lengths[0]!) **
              wordArrayFrom lenBase 1 (lengths.drop 1) **
              (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
              (IterI ↦ₘ (0 : Word)) ** memOwn IterChild ** memOwn IterPrev **
              savedFrame spC csaved ** regOwn .x6) ** regOwn .x5)
            (cvitPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
              firstBadPtr csaved bigBytes lengths) from ?_)
        refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v5 => ?_)
        refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
          (show cpsTripleWithin (22 + nTail) (D + 96) raIn fullCode
            (((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkRA0) ** (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) **
              (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ x21val) ** (Ts ↦ₘ value) **
              (.x5 ↦ᵣ v5) ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
              regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              memOwn RfuOff ** memOwn RfuLen **
              stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              bytesRegion hdrBase bigBytes **
              EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                ⟨LinkRA0, BitVec.ofNat 64 lengths.length, lenBase⟩ **
              (lenBase ↦ₘ BitVec.ofNat 64 lengths[0]!) **
              wordArrayFrom lenBase 1 (lengths.drop 1) **
              (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
              (IterI ↦ₘ (0 : Word)) ** memOwn IterChild ** memOwn IterPrev **
              savedFrame spC csaved) ** regOwn .x6)
            (cvitPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
              firstBadPtr csaved bigBytes lengths) from ?_)
        refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v6 => ?_)
        have hbne := bne_spec_gen_within .x10 .x0 (212 : BitVec 13) status (0 : Word) (D + 96)
        have hbneC := cpsBranchWithin_extend_code cvit_mono
          (cpsBranchWithin_extend_code (cr' := cvitCode)
            (CodeReq.ofProg_mem_at D (D + 96) cvitProg 24 (.BNE .x10 .x0 (212 : BitVec 13))
              (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) hbne)
        have htaken := cpsBranchWithin_takenStripPure2 hbneC (fun hp hq => by
          obtain ⟨_, _, _, _, _, hrest⟩ := hq
          exact absurd ((sepConj_pure_right _).1 hrest).2 hstatus)
        rw [show (D + 96) + signExtend13 (212 : BitVec 13) = D + 308 from by
          rw [show signExtend13 (212 : BitVec 13) = (212 : Word) from by decide]; bv_omega] at htaken
        have htakenF := cpsTripleWithin_frameR
          ((.x1 ↦ᵣ LinkRA0) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
            (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) **
            (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ x21val) **
            (Ts ↦ₘ value) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** regOwn .x7 ** regOwn .x11 **
            regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
            bytesRegion hdrBase bigBytes **
            EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
              ⟨LinkRA0, BitVec.ofNat 64 lengths.length, lenBase⟩ **
            (lenBase ↦ₘ BitVec.ofNat 64 lengths[0]!) **
            wordArrayFrom lenBase 1 (lengths.drop 1) ** (validPtr ↦ₘ (1 : Word)) **
            (firstBadPtr ↦ₘ (0 : Word)) **
            (IterI ↦ₘ (0 : Word)) ** memOwn IterChild ** memOwn IterPrev **
            savedFrame spC csaved) (by pcfx) htaken
        have hpfC := cpsTripleWithin_extend_code cvit_mono
          (retParseFail sp0 spC raIn (0 : Word) firstBadPtr csaved
            ((.x0 ↦ᵣ (0 : Word)) ** (Ts ↦ₘ value) **
              regOwn .x7 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              memOwn RfuOff ** memOwn RfuLen **
              stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              bytesRegion hdrBase bigBytes **
              EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                ⟨LinkRA0, BitVec.ofNat 64 lengths.length, lenBase⟩ **
              (lenBase ↦ₘ BitVec.ofNat 64 lengths[0]!) **
              wordArrayFrom lenBase 1 (lengths.drop 1) ** (validPtr ↦ₘ (1 : Word)) **
              memOwn IterChild ** memOwn IterPrev)
            (by pcfx) LinkRA0 (BitVec.ofNat 64 lengths.length) lenBase hdrBase validPtr x21val
            status v5 v6 hspC hraSaved hret)
        have hcompose := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
          have hp1 : ((firstBadPtr ↦ₘ (0 : Word)) **
              ((.x20 ↦ᵣ firstBadPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ status) **
                (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ LinkRA0) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) **
                (.x21 ↦ᵣ x21val) ** (IterI ↦ₘ (0 : Word)) **
                (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                ((.x0 ↦ᵣ (0 : Word)) ** (Ts ↦ₘ value) ** regOwn .x7 ** regOwn .x11 **
                  regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
                  regOwn .x30 ** regOwn .x31 ** memOwn RfuOff ** memOwn RfuLen **
                  stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
                  bytesRegion hdrBase bigBytes **
                  EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
                    ⟨LinkRA0, BitVec.ofNat 64 lengths.length, lenBase⟩ **
                  (lenBase ↦ₘ BitVec.ofNat 64 lengths[0]!) **
                  wordArrayFrom lenBase 1 (lengths.drop 1) ** (validPtr ↦ₘ (1 : Word)) **
                  memOwn IterChild ** memOwn IterPrev))) h := by
            rw [hsf] at hp; xperm_hyp hp
          have hp2 := sepConj_mono_left memIs_implies_memOwn h hp1
          xperm_hyp hp2) htakenF hpfC
        refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
          (cpsTripleWithin_mono_nSteps (show 1 + 14 ≤ 22 + nTail by omega) hcompose)
        refine Or.inr (Or.inr ⟨0, status, ?_⟩)
        refine (sepConj_pure_left h).mpr
          ⟨⟨by omega, fun j hj1 hj => by omega,
            ⟨value, by rw [hdrop0, hHB0]; exact hResult, hstatus⟩⟩, ?_⟩
        unfold commonRet payload
        rw [hsf, hraSaved, show BitVec.ofNat 64 0 = (0 : Word) from by decide, hwa]
        have hp1 : ((.x5 ↦ᵣ IterI) ** (.x6 ↦ᵣ (0 : Word)) ** (Ts ↦ₘ value) **
            (IterI ↦ₘ (0 : Word)) **
            EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame (spC + signExtend12 (-32 : BitVec 12))
              ⟨LinkRA0, BitVec.ofNat 64 lengths.length, lenBase⟩ **
            ((.x10 ↦ᵣ status) ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
              (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ csaved.s0) ** (.x9 ↦ᵣ csaved.s1) **
              (.x18 ↦ᵣ csaved.s2) ** (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) **
              (.x21 ↦ᵣ csaved.s5) **
              (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
              ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
              ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
              (.x0 ↦ᵣ (0 : Word)) ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
              regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              memOwn RfuOff ** memOwn RfuLen **
              stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
              (lenBase ↦ₘ BitVec.ofNat 64 lengths[0]!) **
              wordArrayFrom lenBase 1 (lengths.drop 1) ** bytesRegion hdrBase bigBytes **
              memOwn IterChild ** memOwn IterPrev)) h := by xperm_hyp hq
        have hp2 := sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono
          (regIs_implies_regOwn .x6) (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn
          (sepConj_mono (k34SavedFrame_implies_frameSlotsOwn _ _) (fun _ x => x))))) h hp1
        xperm_hyp hp2


/-! ## Header-0 block (instructions 18--30): call ;; status dispatch

    From the `N ≥ 2` fall-through (`D+72`) to the caller's post: `cvitHdr0Call`
    decodes header 0's field 11 and `cvitHdr0Dispatch` splits on the status,
    reaching `LoopInv 1` (success) or `retParseFail` at index 0 (parse-fail). -/

set_option maxRecDepth 8000 in
theorem cvitHdr0Block
    (sp0 spC hdrBase lenBase validPtr firstBadPtr raIn x21val : Word) (L0 : Nat)
    (oldOut oldOff oldLen old14 oldX1 old5 o10 o11 o12 o13 : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) (nTail : Nat)
    (hN2 : 2 ≤ lengths.length)
    (hL0 : L0 = lengths[0]!)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hsalign : hdrBase.toNat % 8 = 0)
    (hslack : L0 + 9 ≤ bigBytes.length)
    (hover : hdrBase.toNat + bigBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bigBytes.length →
      isValidByteAccess (hdrBase + BitVec.ofNat 64 k) = true)
    (htail : cpsTripleWithin nTail (D + 124) raIn fullCode
        (LoopInv sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths 1)
        (cvitPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr csaved bigBytes lengths)) :
    cpsTripleWithin ((5 + 1 + nCall bigBytes.length) + (22 + nTail)) (D + 72) raIn fullCode
      ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
        (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ x21val) **
        (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ o10) ** (.x11 ↦ᵣ o11) ** (.x12 ↦ᵣ o12) ** (.x13 ↦ᵣ o13) **
        (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ oldX1) ** (.x0 ↦ᵣ (0 : Word)) **
        (lenBase ↦ₘ BitVec.ofNat 64 L0) **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
        stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
        (Ts ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        bytesRegion hdrBase bigBytes ** savedFrame spC csaved **
        wordArrayFrom lenBase 1 (lengths.drop 1) ** (validPtr ↦ₘ (1 : Word)) **
        (firstBadPtr ↦ₘ (0 : Word)) ** (IterI ↦ₘ (0 : Word)) **
        memOwn IterChild ** memOwn IterPrev)
      (cvitPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr csaved bigBytes lengths) := by
  have hcall := cvitHdr0Call spC hdrBase lenBase validPtr firstBadPtr x21val L0
    (BitVec.ofNat 64 lengths.length) oldOut oldOff oldLen old14 oldX1 old5 o10 o11 o12 o13
    bigBytes csaved hsalign hslack hover hvalid
  have hcallF := cpsTripleWithin_frameR
    (wordArrayFrom lenBase 1 (lengths.drop 1) ** (validPtr ↦ₘ (1 : Word)) **
      (firstBadPtr ↦ₘ (0 : Word)) ** (IterI ↦ₘ (0 : Word)) **
      memOwn IterChild ** memOwn IterPrev)
    (by pcfx) hcall
  have hdisp := cvitHdr0Dispatch sp0 spC hdrBase lenBase validPtr firstBadPtr raIn x21val L0
    csaved bigBytes lengths oldOff oldLen nTail hN2 hL0 hspC hraSaved hret htail
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcallF hdisp)


set_option maxRecDepth 8000 in
/-- **`chain_validate_increasing_timestamps` caller contract.**  The
    92-instruction cross-header accessor iterates over `N = lengths.length` block
    headers and validates that RLP field 11 (`timestamp`) is STRICTLY increasing
    across consecutive headers.  Its three-way post pins the verdict over the TRUE
    count: all-strictly-increasing (`a0 = 0`, `*validPtr = 1`, either `N < 2` or
    every adjacent pair `< N` strictly increasing), first-violation (`a0 = 0`,
    `*validPtr = 0`, `*firstBad = k`, pair `(k-1,k)` non-increasing and all earlier
    increasing), or first parse-failure (`a0 = status ≠ 0`, `*firstBad = k`, header
    `k` fails the field-11 u64 decode and all earlier increasing) — each header's
    timestamp genuinely decoded via K34's `Result`, and each `prev = ts[i-1]`
    threaded through `cvit_iter_prev` (`x21` in `LoopInv`).  Strict `>` matches the
    Yellow Paper `Hs > parent.Hs`. -/
theorem chain_validate_increasing_timestamps_spec_within
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
    cpsTripleWithin
      (17 + (1 + ((5 + 1 + nCall bigBytes.length) + (22 + cvitLoopSteps bigBytes.length (lengths.length - 1)))))
      D raIn fullCode
      (((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) **
          (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
          (.x10 ↦ᵣ nWord) ** (.x11 ↦ᵣ lenBase) ** (.x12 ↦ᵣ hdrBase) **
          (.x13 ↦ᵣ validPtr) ** (.x14 ↦ᵣ firstBadPtr) ** (.x5 ↦ᵣ old5) **
          (.x0 ↦ᵣ (0 : Word)) **
          memOwn spC ** memOwn (spC + 8) ** memOwn (spC + 16) ** memOwn (spC + 24) **
          memOwn (spC + 32) ** memOwn (spC + 40) ** memOwn (spC + 48) **
          memOwn validPtr ** memOwn firstBadPtr) **
        wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
        memOwn Ts ** memOwn RfuOff ** memOwn RfuLen ** memOwn IterChild **
        (IterI ↦ₘ (0 : Word)) ** memOwn IterPrev **
        regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
        stackFree (spC + signExtend12 (-32 : BitVec 12)) 8)
      (cvitPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
        firstBadPtr ⟨raIn, cs0, cs1, cs2, cs3, cs4, cs5⟩ bigBytes lengths) := by
  subst hnWord
  have hHB0 : hdrBaseAt hdrBase lengths 0 = hdrBase := by unfold hdrBaseAt hdrOff; simp
  have hdrop0 : bigBytes.drop (hdrOff lengths 0) = bigBytes := by unfold hdrOff; simp
  have hsf : savedFrame spC (⟨raIn, cs0, cs1, cs2, cs3, cs4, cs5⟩ : Saved) =
      ((spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) ** ((spC + 24) ↦ₘ cs2) **
        ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5)) := by
    unfold savedFrame; rfl
  have hult : (BitVec.ult (BitVec.ofNat 64 lengths.length) (2 : Word) = true) ↔
      lengths.length < 2 := by
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN,
      show (2 : Word).toNat = 2 from by decide]
  have hpro := cpsTripleWithin_extend_code cvit_mono
    (cvitPrologue sp0 spC (BitVec.ofNat 64 lengths.length) lenBase hdrBase validPtr firstBadPtr
      raIn cs0 cs1 cs2 cs3 cs4 cs5 old5 hspC)
  have hproF := cpsTripleWithin_frameR
    (wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
      memOwn Ts ** memOwn RfuOff ** memOwn RfuLen ** memOwn IterChild **
      (IterI ↦ₘ (0 : Word)) ** memOwn IterPrev **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
      stackFree (spC + signExtend12 (-32 : BitVec 12)) 8) (by pcfx) hpro
  -- Tail from the loop-comparand load (`D+68`): BLTU then header-0 or the N<2 exit.
  have htail :
      cpsTripleWithin (1 + ((5 + 1 + nCall bigBytes.length) + (22 + cvitLoopSteps bigBytes.length (lengths.length - 1))))
        (D + 68) raIn fullCode
        (((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
            (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) **
            (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ cs5) ** (.x10 ↦ᵣ BitVec.ofNat 64 lengths.length) **
            (.x11 ↦ᵣ lenBase) ** (.x12 ↦ᵣ hdrBase) ** (.x13 ↦ᵣ validPtr) **
            (.x14 ↦ᵣ firstBadPtr) ** (.x5 ↦ᵣ (2 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) ** ((spC + 24) ↦ₘ cs2) **
            ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) **
            (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word))) **
          wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
          memOwn Ts ** memOwn RfuOff ** memOwn RfuLen ** memOwn IterChild **
          (IterI ↦ₘ (0 : Word)) ** memOwn IterPrev **
          regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8)
        (cvitPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
          firstBadPtr ⟨raIn, cs0, cs1, cs2, cs3, cs4, cs5⟩ bigBytes lengths) := by
    by_cases hlt : lengths.length < 2
    · -- `N < 2`: BLTU taken → all-valid exit (vacuously increasing).
      have hbltu := bltu_spec_gen_within .x8 .x5 (260 : BitVec 13)
        (BitVec.ofNat 64 lengths.length) (2 : Word) (D + 68)
      have hbltuC := cpsBranchWithin_extend_code cvit_mono
        (cpsBranchWithin_extend_code (cr' := cvitCode)
          (CodeReq.ofProg_mem_at D (D + 68) cvitProg 17 (.BLTU .x8 .x5 (260 : BitVec 13))
            (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) hbltu)
      have htaken := cpsBranchWithin_takenStripPure2 hbltuC (fun hp hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact absurd (hult.2 hlt) ((sepConj_pure_right _).1 hrest).2)
      rw [show (D + 68) + signExtend13 (260 : BitVec 13) = D + 328 from by
        rw [show signExtend13 (260 : BitVec 13) = (260 : Word) from by decide]; bv_omega] at htaken
      have htakenF := cpsTripleWithin_frameR
        ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) **
          (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ cs5) **
          (.x10 ↦ᵣ BitVec.ofNat 64 lengths.length) **
          (.x11 ↦ᵣ lenBase) ** (.x12 ↦ᵣ hdrBase) ** (.x13 ↦ᵣ validPtr) ** (.x14 ↦ᵣ firstBadPtr) **
          (.x0 ↦ᵣ (0 : Word)) **
          (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) ** ((spC + 24) ↦ₘ cs2) **
          ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) **
          (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
          wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
          memOwn Ts ** memOwn RfuOff ** memOwn RfuLen ** memOwn IterChild **
          (IterI ↦ₘ (0 : Word)) ** memOwn IterPrev **
          regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8) (by pcfx) htaken
      have hallv := cpsTripleWithin_extend_code cvit_mono
        (retAllValid sp0 spC raIn ⟨raIn, cs0, cs1, cs2, cs3, cs4, cs5⟩
          ((.x5 ↦ᵣ (2 : Word)) ** (.x11 ↦ᵣ lenBase) ** (.x12 ↦ᵣ hdrBase) ** (.x13 ↦ᵣ validPtr) **
            (.x14 ↦ᵣ firstBadPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (1 : Word)) **
            (firstBadPtr ↦ₘ (0 : Word)) **
            wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
            memOwn Ts ** memOwn RfuOff ** memOwn RfuLen ** memOwn IterChild **
            (IterI ↦ₘ (0 : Word)) ** memOwn IterPrev **
            regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8)
          (by pcfx) (BitVec.ofNat 64 lengths.length) raIn (BitVec.ofNat 64 lengths.length) lenBase
          hdrBase validPtr firstBadPtr cs5 hspC rfl hret)
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
        (cpsTripleWithin_mono_nSteps
          (show 1 + 10 ≤ 1 + ((5 + 1 + nCall bigBytes.length) + (22 + cvitLoopSteps bigBytes.length (lengths.length - 1))) by
            unfold nCall; omega)
          (cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
            htakenF hallv))
      refine Or.inl ?_
      unfold postAllValid commonRet payload
      refine (sepConj_pure_left h).mpr ⟨Or.inl hlt, ?_⟩
      rw [hsf]
      have hp1 : ((.x5 ↦ᵣ (2 : Word)) ** (.x11 ↦ᵣ lenBase) ** (.x12 ↦ᵣ hdrBase) **
          (.x13 ↦ᵣ validPtr) ** (.x14 ↦ᵣ firstBadPtr) ** (IterI ↦ₘ (0 : Word)) **
          ((.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
            (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
            (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
            (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) ** ((spC + 24) ↦ₘ cs2) **
            ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) **
            regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) **
            frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
            stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
            wordArray lenBase lengths ** bytesRegion hdrBase bigBytes **
            memOwn Ts ** memOwn RfuOff ** memOwn RfuLen ** memOwn IterChild ** memOwn IterPrev)) h := by
        xperm_hyp hq
      have hp2 := sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12) (sepConj_mono (regIs_implies_regOwn .x13)
        (sepConj_mono (regIs_implies_regOwn .x14) (sepConj_mono memIs_implies_memOwn
          (fun _ x => x)))))) h hp1
      xperm_hyp hp2
    · -- `N ≥ 2`: BLTU not taken → header-0 block then the loop from `i = 1`.
      have hge : 2 ≤ lengths.length := by omega
      have hbltu := bltu_spec_gen_within .x8 .x5 (260 : BitVec 13)
        (BitVec.ofNat 64 lengths.length) (2 : Word) (D + 68)
      have hbltuC := cpsBranchWithin_extend_code cvit_mono
        (cpsBranchWithin_extend_code (cr' := cvitCode)
          (CodeReq.ofProg_mem_at D (D + 68) cvitProg 17 (.BLTU .x8 .x5 (260 : BitVec 13))
            (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) hbltu)
      have hntaken := cpsBranchWithin_ntakenStripPure2 hbltuC (fun hp hq => by
        obtain ⟨_, _, _, _, _, hrest⟩ := hq
        exact absurd (hult.1 ((sepConj_pure_right _).1 hrest).2) (by omega))
      rw [show (D + 68 + 4 : Word) = D + 72 from by bv_omega] at hntaken
      have hwa : wordArray lenBase lengths =
          ((lenBase ↦ₘ BitVec.ofNat 64 lengths[0]!) ** wordArrayFrom lenBase 1 (lengths.drop 1)) := by
        have hLen0 : lengths[0]! = lengths[0] := getElem!_pos lengths 0 (by omega)
        rw [wordArray_split lenBase lengths 0 (by omega),
          show BitVec.ofNat 64 (8 * 0) = (0 : Word) from by decide,
          show lenBase + (0 : Word) = lenBase from by bv_omega,
          show lengths.take 0 = ([] : List Nat) from rfl,
          show wordArrayFrom lenBase 0 ([] : List Nat) = empAssertion from rfl,
          ← hLen0, sepConj_emp_left']
      -- Base of the header-0 block precondition (wordArray whole, savedFrame folded).
      set BASE : Assertion :=
        ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
          (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ cs5) **
          (.x5 ↦ᵣ (2 : Word)) ** (.x10 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x11 ↦ᵣ lenBase) **
          (.x12 ↦ᵣ hdrBase) ** (.x13 ↦ᵣ validPtr) ** (.x14 ↦ᵣ firstBadPtr) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x1 ↦ᵣ raIn) ** (.x0 ↦ᵣ (0 : Word)) ** wordArray lenBase lengths **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 ** bytesRegion hdrBase bigBytes **
          savedFrame spC ⟨raIn, cs0, cs1, cs2, cs3, cs4, cs5⟩ **
          (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) ** (IterI ↦ₘ (0 : Word)) **
          memOwn IterChild ** memOwn IterPrev) with hBASE
      -- Peel the three K34 scratch cells (owned) into concrete inputs; run the block+loop.
      have hcont :
          cpsTripleWithin ((5 + 1 + nCall bigBytes.length) + (22 + cvitLoopSteps bigBytes.length (lengths.length - 1)))
            (D + 72) raIn fullCode
            (((BASE ** memOwn Ts) ** memOwn RfuOff) ** memOwn RfuLen)
            (cvitPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
              firstBadPtr ⟨raIn, cs0, cs1, cs2, cs3, cs4, cs5⟩ bigBytes lengths) := by
        refine cpsTripleWithin_of_forall_memIs_to_memOwn (fun oldLen => ?_)
        refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
          (show cpsTripleWithin ((5 + 1 + nCall bigBytes.length) + (22 + cvitLoopSteps bigBytes.length (lengths.length - 1)))
            (D + 72) raIn fullCode
            (((BASE ** (RfuLen ↦ₘ oldLen)) ** memOwn Ts) ** memOwn RfuOff)
            (cvitPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
              firstBadPtr ⟨raIn, cs0, cs1, cs2, cs3, cs4, cs5⟩ bigBytes lengths) from ?_)
        refine cpsTripleWithin_of_forall_memIs_to_memOwn (fun oldOff => ?_)
        refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
          (show cpsTripleWithin ((5 + 1 + nCall bigBytes.length) + (22 + cvitLoopSteps bigBytes.length (lengths.length - 1)))
            (D + 72) raIn fullCode
            (((BASE ** (RfuLen ↦ₘ oldLen)) ** (RfuOff ↦ₘ oldOff)) ** memOwn Ts)
            (cvitPost sp0 spC (spC + signExtend12 (-32 : BitVec 12)) hdrBase lenBase validPtr
              firstBadPtr ⟨raIn, cs0, cs1, cs2, cs3, cs4, cs5⟩ bigBytes lengths) from ?_)
        refine cpsTripleWithin_of_forall_memIs_to_memOwn (fun oldOut => ?_)
        have hblock := cvitHdr0Block sp0 spC hdrBase lenBase validPtr firstBadPtr raIn cs5
          lengths[0]! oldOut oldOff oldLen firstBadPtr raIn (2 : Word)
          (BitVec.ofNat 64 lengths.length) lenBase hdrBase validPtr
          ⟨raIn, cs0, cs1, cs2, cs3, cs4, cs5⟩ bigBytes lengths
          (cvitLoopSteps bigBytes.length (lengths.length - 1))
          hge rfl hspC rfl hret
          (by have := hAllSalign 0 (by omega); rwa [hHB0] at this)
          (by have := hAllSlack 0 (by omega); rwa [hdrop0] at this)
          (by have := hAllOver 0 (by omega); rwa [hHB0, hdrop0] at this)
          (by intro k hk; have := hAllValid 0 (by omega) k (by rw [hdrop0]; exact hk); rwa [hHB0] at this)
          (cvitLoop sp0 spC hdrBase lenBase validPtr firstBadPtr raIn
            ⟨raIn, cs0, cs1, cs2, cs3, cs4, cs5⟩ bigBytes lengths hN hspC rfl hret
            hAllAlign hAllLen hAllSalign hAllSlack hAllOver hAllValid
            lengths.length 1 (by omega) (by omega) (by omega))
        exact cpsTripleWithin_weaken (fun h hp => by rw [hBASE, hwa] at hp; xperm_hyp hp)
          (fun _ hq => hq) hblock
      -- Frame the BLTU with the rest of the D+72 state (cells, folded on entry to hcont).
      have hntakenF := cpsTripleWithin_frameR
        ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) **
          (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ cs5) ** (.x10 ↦ᵣ BitVec.ofNat 64 lengths.length) **
          (.x11 ↦ᵣ lenBase) ** (.x12 ↦ᵣ hdrBase) ** (.x13 ↦ᵣ validPtr) ** (.x14 ↦ᵣ firstBadPtr) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x1 ↦ᵣ raIn) ** (.x0 ↦ᵣ (0 : Word)) ** wordArray lenBase lengths **
          frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame (spC + signExtend12 (-32 : BitVec 12)) **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 ** bytesRegion hdrBase bigBytes **
          ((spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) ** ((spC + 24) ↦ₘ cs2) **
            ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5)) **
          (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) ** (IterI ↦ₘ (0 : Word)) **
          memOwn IterChild ** memOwn IterPrev **
          memOwn Ts ** memOwn RfuOff ** memOwn RfuLen) (by pcfx) hntaken
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
        (cpsTripleWithin_seq_perm_same_cr (fun h hp => by
          rw [hBASE]; rw [← hsf] at hp; xperm_hyp hp) hntakenF hcont)
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hproF htail)


end EvmAsm.Codegen.ChainValidateIncreasingTimestampsSpec
