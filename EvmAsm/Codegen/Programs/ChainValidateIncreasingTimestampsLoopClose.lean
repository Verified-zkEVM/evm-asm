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

end EvmAsm.Codegen.ChainValidateIncreasingTimestampsSpec
