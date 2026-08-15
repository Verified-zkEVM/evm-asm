/-
  EvmAsm.Codegen.Programs.HeaderFieldsGenericInit

  Extractor-parametric prologue + `rlp_walk_init` call + init-status dispatch,
  mirroring `hesrPrologue`/`hesrInitStep`/`hesrMarshalInitBundled`/`hesrInitDispatch`
  but abstracted over base/code/PCs/scratch-addresses and taking the first stage
  (`hfStageRec`) as a continuation hypothesis.

  Classical-3 axioms only; no `sorry`/`native_decide`/`bv_decide`.
-/
import EvmAsm.Codegen.Programs.HeaderFieldsGenericDispatch

namespace EvmAsm.Codegen.HeaderFieldsSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

/-- The caller-owned ambient carried across the walker calls (generic over the
    two scratch addresses): frame pointer + saved regs, saved frame, the two spill
    slots, and the output buffer. -/
def hfAmbient (newSp outPtr listBase listLen : Word) (saved : Saved)
    (outBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLen) ** (.x18 ↦ᵣ outPtr) **
  savedFrame newSp saved ** memOwn (newSp + 32) ** memOwn (newSp + 40) **
  bytesRegion outPtr outBytes

theorem pcFree_hfAmbient (newSp outPtr listBase listLen : Word) (saved : Saved)
    (outBytes : List (BitVec 8)) :
    (hfAmbient newSp outPtr listBase listLen saved outBytes).pcFree := by
  unfold hfAmbient savedFrame
  repeat' first
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact pcFree_memOwn

/-- The scratch-register + `ra` + input-region block the initializer leaves
    (generic over the init call's return address `retRa`). -/
def hfInitCommon (retRa listBase : Word) (bytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ retRa) ** bytesRegion listBase bytes

/-! ## Generic register moves [5]-[9] (`base+20 → base+40`) -/

theorem hfSetupMoves5 {code : CodeReq} (base : Word)
    (listBase listLen outPtr v8 v9 v18 : Word)
    (hc5 : ∀ a i, CodeReq.singleton (base + 20) (.MV .x8 .x10) a = some i → code a = some i)
    (hc6 : ∀ a i, CodeReq.singleton (base + 24) (.MV .x9 .x11) a = some i → code a = some i)
    (hc7 : ∀ a i, CodeReq.singleton (base + 28) (.MV .x18 .x12) a = some i → code a = some i)
    (hc8 : ∀ a i, CodeReq.singleton (base + 32) (.MV .x10 .x8) a = some i → code a = some i)
    (hc9 : ∀ a i, CodeReq.singleton (base + 36) (.MV .x11 .x9) a = some i → code a = some i) :
    cpsTripleWithin 5 (base + 20) (base + 40) code
      ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
       (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outPtr))
      ((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLen) ** (.x18 ↦ᵣ outPtr) **
       (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outPtr)) := by
  have h5 := mv_spec_gen_within .x8 .x10 listBase v8 (base + 20) (by decide)
  rw [show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at h5
  have e5 := cpsTripleWithin_extend_code hc5 h5
  have f5 := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outPtr))
    (by pcf) e5
  have h6 := mv_spec_gen_within .x9 .x11 listLen v9 (base + 24) (by decide)
  rw [show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at h6
  have e6 := cpsTripleWithin_extend_code hc6 h6
  have f6 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ v18) ** (.x10 ↦ᵣ listBase) ** (.x12 ↦ᵣ outPtr))
    (by pcf) e6
  have h7 := mv_spec_gen_within .x18 .x12 outPtr v18 (base + 28) (by decide)
  rw [show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at h7
  have e7 := cpsTripleWithin_extend_code hc7 h7
  have f7 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLen) ** (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen))
    (by pcf) e7
  have h8 := mv_spec_gen_within .x10 .x8 listBase listBase (base + 32) (by decide)
  rw [show (base + 32 : Word) + 4 = base + 36 from by bv_omega] at h8
  have e8 := cpsTripleWithin_extend_code hc8 h8
  have f8 := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ listLen) ** (.x18 ↦ᵣ outPtr) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outPtr))
    (by pcf) e8
  have h9 := mv_spec_gen_within .x11 .x9 listLen listLen (base + 36) (by decide)
  rw [show (base + 36 : Word) + 4 = base + 40 from by bv_omega] at h9
  have e9 := cpsTripleWithin_extend_code hc9 h9
  have f9 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outPtr) ** (.x10 ↦ᵣ listBase) ** (.x12 ↦ᵣ outPtr))
    (by pcf) e9
  have s56 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f5 f6
  have s567 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s56 f7
  have s5678 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s567 f8
  have s56789 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s5678 f9
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) s56789

/-! ## Generic prologue [0]-[9] (`base → base+40`) -/

set_option maxRecDepth 8000 in
theorem hfPrologue {code : CodeReq} (base sp0 newSp listBase listLen outPtr : Word) (saved : Saved)
    (h_newSp : newSp = sp0 + signExtend12 (-48 : BitVec 12))
    (hc0 : ∀ a i, CodeReq.singleton base (.ADDI .x2 .x2 (-48 : BitVec 12)) a = some i → code a = some i)
    (hstore : ∀ a i, CodeReq.ofProg (base + 4) (storeProg hxFrame) a = some i → code a = some i)
    (hc5 : ∀ a i, CodeReq.singleton (base + 20) (.MV .x8 .x10) a = some i → code a = some i)
    (hc6 : ∀ a i, CodeReq.singleton (base + 24) (.MV .x9 .x11) a = some i → code a = some i)
    (hc7 : ∀ a i, CodeReq.singleton (base + 28) (.MV .x18 .x12) a = some i → code a = some i)
    (hc8 : ∀ a i, CodeReq.singleton (base + 32) (.MV .x10 .x8) a = some i → code a = some i)
    (hc9 : ∀ a i, CodeReq.singleton (base + 36) (.MV .x11 .x9) a = some i → code a = some i) :
    cpsTripleWithin 10 base (base + 40) code
      ((.x2 ↦ᵣ sp0) ** regsAt hxFrame (savedVals saved) **
       frameSlotsOwn hxFrame newSp **
       (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outPtr))
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ saved.ra) ** savedFrame newSp saved **
       (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLen) ** (.x18 ↦ᵣ outPtr) **
       (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outPtr)) := by
  have ha0 := addi_spec_gen_same_within .x2 sp0 (-48 : BitVec 12) base (by decide)
  rw [← h_newSp] at ha0
  have ha := cpsTripleWithin_extend_code hc0 ha0
  have haF := cpsTripleWithin_frameR
    (regsAt hxFrame (savedVals saved) ** frameSlotsOwn hxFrame newSp **
      (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outPtr)) (by
      repeat' first
        | exact pcFree_regsAt _ _
        | exact pcFree_frameSlotsOwn _ _
        | apply pcFree_sepConj
        | exact pcFree_regIs) ha
  have hs0 := storeSeq_spec hxFrame newSp (savedVals saved) (base + 4) (by decide)
  have hs := cpsTripleWithin_extend_code hstore hs0
  rw [show base + 4 + BitVec.ofNat 64 (4 * hxFrame.length) = base + 20 from by
    simp [hxFrame]; bv_omega] at hs
  have hsF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outPtr)) (by
      repeat' first | apply pcFree_sepConj | exact pcFree_regIs) hs
  have hm := hfSetupMoves5 base listBase listLen outPtr saved.s0 saved.s1 saved.s2
    hc5 hc6 hc7 hc8 hc9
  have hmF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ saved.ra) ** savedFrame newSp saved) (by
      unfold savedFrame
      repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs) hm
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) haF hsF
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_hxFrame, frameSlotsSaved_hxFrame] at hp
    xperm_hyp hp) h01 hmF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) h012

/-! ## Generic init call step (`base+40 → base+44`) -/

set_option maxRecDepth 8000 in
theorem hfInitStep {code : CodeReq}
    (base : Word) (initOffset : BitVec 21)
    (listBase outPtr newSp oldRa v5 v6 v7 v28 v29 v30 v31 : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    (h_align : listBase.toNat % 8 = 0)
    (h_slack : listLenN + 9 ≤ headerBytes.length)
    (h_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hioff : (base + 40) + signExtend21 initOffset = wiBase)
    (halign : (base + 40 + 4) &&& ~~~(1 : Word) = base + 40 + 4)
    (hdisj : (CodeReq.singleton (base + 40) (.JAL .x1 initOffset)).Disjoint (rlp_walk_init_code wiBase))
    (hcode : ∀ a i,
      (CodeReq.singleton (base + 40) (.JAL .x1 initOffset)).union
        (rlp_walk_init_code wiBase) a = some i → code a = some i) :
    cpsTripleWithin (1 + 81) (base + 40) (base + 40 + 4) code
      ((.x1 ↦ᵣ oldRa) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLenN) **
         (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         hfAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes))
      (((hfInitCommon (base + 40 + 4) listBase headerBytes ** (.x0 ↦ᵣ (0 : Word))) **
         RlpListNthItemSAsm.initOutcome listBase headerBytes listLenN (by omega)) **
        hfAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes) := by
  have hoff : 0 < headerBytes.length := by omega
  have hwi := rlp_walk_init_spec_within wiBase listBase (base + 40 + 4)
    (BitVec.ofNat 64 listLenN) outPtr v5 v6 v7 v28 v29 v30 v31 headerBytes 0
    h_align hoff (by omega) (h_valid 0 hoff)
    (fun h_f8 _ => by
      have h_lo : ((headerBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.not_ult_le h_f8
        have h3 := (headerBytes[0]'hoff).isLt
        bv_omega
      omega)
    (fun h_f8 _ => by
      have h_lo : ((headerBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.not_ult_le h_f8
        have h3 := (headerBytes[0]'hoff).isLt
        bv_omega
      omega)
    (fun h_f8 _ => by
      intro k hk
      have h_lo : ((headerBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.not_ult_le h_f8
        have h3 := (headerBytes[0]'hoff).isLt
        bv_omega
      exact h_valid _ (by omega))
  rw [show listBase + BitVec.ofNat 64 0 = listBase from by bv_omega] at hwi
  have hwiA := cpsTripleWithin_frameR
    (hfAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes)
    (pcFree_hfAmbient _ _ _ _ _ _) hwi
  set Prest : Assertion :=
    ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLenN) **
     (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
     hfAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes) with hPrest
  set Q : Assertion :=
    ((hfInitCommon (base + 40 + 4) listBase headerBytes ** (.x0 ↦ᵣ (0 : Word))) **
      RlpListNthItemSAsm.initOutcome listBase headerBytes listLenN hoff) **
      hfAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes with hQ
  have hwi' : cpsTripleWithin 81 wiBase ((base + 40 + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code wiBase) ((.x1 ↦ᵣ (base + 40 + 4)) ** Prest) Q :=
    cpsTripleWithin_weaken
      (fun h hp => by rw [hPrest] at hp; xperm_hyp hp)
      (fun h hp => by
        rw [hQ]
        unfold hfInitCommon RlpListNthItemSAsm.initOutcome
        simp only [Nat.zero_add] at hp ⊢
        xperm_hyp hp) hwiA
  have hc := EvmAsm.Codegen.RlpWalkCallSAsm.rlp_walk_init_call_within
    (base + 40) wiBase oldRa initOffset (by
      rw [hPrest]
      repeat' first
        | exact bytesRegion_pcFree _ _
        | exact pcFree_hfAmbient _ _ _ _ _ _
        | apply pcFree_sepConj
        | exact pcFree_regIs) hioff halign hdisj hcode hwi'
  simpa [hPrest, hQ] using hc

/-! ## Generic init marshalling [12]-[15] (`base+48 → base+64`) -/

theorem hfMarshalInit {code : CodeReq} (base cursor endPtr newSp : Word)
    (hc0 : ∀ a i, CodeReq.singleton (base + 48) (.SD .x2 .x10 (32 : BitVec 12)) a = some i → code a = some i)
    (hc1 : ∀ a i, CodeReq.singleton (base + 52) (.SD .x2 .x11 (40 : BitVec 12)) a = some i → code a = some i)
    (hc2 : ∀ a i, CodeReq.singleton (base + 56) (.LD .x10 .x2 (32 : BitVec 12)) a = some i → code a = some i)
    (hc3 : ∀ a i, CodeReq.singleton (base + 60) (.LD .x11 .x2 (40 : BitVec 12)) a = some i → code a = some i) :
    cpsTripleWithin 4 (base + 48) (base + 64) code
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x2 ↦ᵣ newSp) **
       memOwn (newSp + 32) ** memOwn (newSp + 40))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x2 ↦ᵣ newSp) **
       ((newSp + 32) ↦ₘ cursor) ** ((newSp + 40) ↦ₘ endPtr)) := by
  have h12 := sd_spec_gen_own_within .x2 .x10 newSp cursor (32 : BitVec 12) (base + 48)
  rw [show newSp + signExtend12 (32 : BitVec 12) = newSp + 32 from by
        rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide],
      show (base + 48 : Word) + 4 = base + 52 from by bv_omega] at h12
  have e12 := cpsTripleWithin_extend_code hc0 h12
  have f12 := cpsTripleWithin_frameR ((.x11 ↦ᵣ endPtr) ** memOwn (newSp + 40)) (by
    repeat' first | exact pcFree_regIs | exact pcFree_memIs | exact pcFree_memOwn | apply pcFree_sepConj) e12
  have h13 := sd_spec_gen_own_within .x2 .x11 newSp endPtr (40 : BitVec 12) (base + 52)
  rw [show newSp + signExtend12 (40 : BitVec 12) = newSp + 40 from by
        rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide],
      show (base + 52 : Word) + 4 = base + 56 from by bv_omega] at h13
  have e13 := cpsTripleWithin_extend_code hc1 h13
  have f13 := cpsTripleWithin_frameR ((.x10 ↦ᵣ cursor) ** ((newSp + 32) ↦ₘ cursor)) (by
    repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) e13
  have h14 := ld_spec_gen_within .x10 .x2 newSp cursor cursor (32 : BitVec 12) (base + 56) (by decide)
  rw [show newSp + signExtend12 (32 : BitVec 12) = newSp + 32 from by
        rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide],
      show (base + 56 : Word) + 4 = base + 60 from by bv_omega] at h14
  have e14 := cpsTripleWithin_extend_code hc2 h14
  have f14 := cpsTripleWithin_frameR ((.x11 ↦ᵣ endPtr) ** ((newSp + 40) ↦ₘ endPtr)) (by
    repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) e14
  have h15 := ld_spec_gen_within .x11 .x2 newSp endPtr endPtr (40 : BitVec 12) (base + 60) (by decide)
  rw [show newSp + signExtend12 (40 : BitVec 12) = newSp + 40 from by
        rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide],
      show (base + 60 : Word) + 4 = base + 64 from by bv_omega] at h15
  have e15 := cpsTripleWithin_extend_code hc3 h15
  have f15 := cpsTripleWithin_frameR ((.x10 ↦ᵣ cursor) ** ((newSp + 32) ↦ₘ cursor)) (by
    repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) e15
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f12 f13
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f14
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 f15
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s3

/-- Bundled-entry wrapper for the init marshalling: from the init-phase ambient
    (`hfAmbient`) + the two folded scratch cells, seed the spill slots and re-fold
    to the walk-phase `hfWalkAmbient` + `hesrSpill` shape the first stage consumes. -/
theorem hfMarshalInitBundled {code : CodeReq}
    (base offAddr lenAddr cursor endPtr newSp listBase v9 outPtr : Word)
    (saved : Saved) (outBytes : List (BitVec 8)) (Fr : Assertion) (hFr : Fr.pcFree)
    (hc0 : ∀ a i, CodeReq.singleton (base + 48) (.SD .x2 .x10 (32 : BitVec 12)) a = some i → code a = some i)
    (hc1 : ∀ a i, CodeReq.singleton (base + 52) (.SD .x2 .x11 (40 : BitVec 12)) a = some i → code a = some i)
    (hc2 : ∀ a i, CodeReq.singleton (base + 56) (.LD .x10 .x2 (32 : BitVec 12)) a = some i → code a = some i)
    (hc3 : ∀ a i, CodeReq.singleton (base + 60) (.LD .x11 .x2 (40 : BitVec 12)) a = some i → code a = some i) :
    cpsTripleWithin 4 (base + 48) (base + 64) code
      (((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) **
        (hfAmbient newSp outPtr listBase v9 saved outBytes **
         hfScratchConst offAddr lenAddr ** Fr))
      (((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) **
        (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes **
         hesrSpill newSp cursor endPtr ** Fr)) := by
  have hm := hfMarshalInit base cursor endPtr newSp hc0 hc1 hc2 hc3
  have hmF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ outPtr) ** savedFrame newSp saved **
     bytesRegion outPtr outBytes ** hfScratchConst offAddr lenAddr ** Fr)
    (by repeat' first
      | exact hFr | exact bytesRegion_pcFree _ _ | exact pcFree_hfScratchConst _ _
      | unfold savedFrame | exact pcFree_regIs | exact pcFree_memIs | exact pcFree_memOwn
      | apply pcFree_sepConj) hm
  refine cpsTripleWithin_weaken
    (fun h hp => by unfold hfAmbient at hp; xperm_chunked hp)
    (fun h hq => by
      unfold hfWalkAmbient hesrAmbRegs hfAmbConst hesrSpill; xperm_chunked hq) hmF

/-! ## Generic init dispatch (`base+40 → ret`) -/

set_option maxRecDepth 8000 in
theorem hfInitDispatch {code : CodeReq} {nStage1 : Nat}
    (base offAddr lenAddr listBase outPtr newSp oldRa v5 v6 v7 v28 v29 v30 v31 : Word)
    (saved : Saved) (headerBytes outBytes : List (BitVec 8)) (listLenN index : Nat)
    (hnStage1 : 8 ≤ nStage1)
    (status1PC : Word) (initBneOff : BitVec 13) (initOffset : BitVec 21)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_slack : listLenN + 9 ≤ headerBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hioff : (base + 40) + signExtend21 initOffset = wiBase)
    (halign_i : (base + 40 + 4) &&& ~~~(1 : Word) = base + 40 + 4)
    (hdisj_i : (CodeReq.singleton (base + 40) (.JAL .x1 initOffset)).Disjoint (rlp_walk_init_code wiBase))
    (hcode_i : ∀ a i,
      (CodeReq.singleton (base + 40) (.JAL .x1 initOffset)).union
        (rlp_walk_init_code wiBase) a = some i → code a = some i)
    (hbne_t : base + 44 + signExtend13 initBneOff = status1PC)
    (hbnemem : ∀ a i, CodeReq.singleton (base + 44) (.BNE .x12 .x0 initBneOff) a = some i → code a = some i)
    (hmi0 : ∀ a i, CodeReq.singleton (base + 48) (.SD .x2 .x10 (32 : BitVec 12)) a = some i → code a = some i)
    (hmi1 : ∀ a i, CodeReq.singleton (base + 52) (.SD .x2 .x11 (40 : BitVec 12)) a = some i → code a = some i)
    (hmi2 : ∀ a i, CodeReq.singleton (base + 56) (.LD .x10 .x2 (32 : BitVec 12)) a = some i → code a = some i)
    (hmi3 : ∀ a i, CodeReq.singleton (base + 60) (.LD .x11 .x2 (40 : BitVec 12)) a = some i → code a = some i)
    (hs0 : ∀ a i, CodeReq.singleton status1PC (.LI .x10 (1 : Word)) a = some i → code a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (status1PC + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → code a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (status1PC + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → code a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (status1PC + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → code a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (status1PC + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → code a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (status1PC + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → code a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (status1PC + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → code a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (status1PC + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → code a = some i)
    (hstage1 : ∀ (cursorOff : Nat),
      RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff
        (listBase + BitVec.ofNat 64 listLenN) →
      ∀ w5 w6 w7 w28 w29 w30 w31,
      cpsTripleWithin nStage1 (base + 64) (saved.ra &&& ~~~(1 : Word)) code
        (((.x1 ↦ᵣ (base + 44)) **
          ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
           (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) ** (.x12 ↦ᵣ (0 : Word)) **
           (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
           (hfWalkAmbient offAddr lenAddr newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
            hesrSpill newSp (listBase + BitVec.ofNat 64 cursorOff)
              (listBase + BitVec.ofNat 64 listLenN)))) **
         (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) **
         (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
        (hfRetPost offAddr lenAddr newSp listBase outPtr saved headerBytes outBytes listLenN index
          (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
           memOwn (newSp + 32) **
           ((newSp + 40) ↦ₘ (listBase + BitVec.ofNat 64 listLenN)) ** empAssertion))) :
    cpsTripleWithin (1 + 81 + (1 + (4 + nStage1))) (base + 40) (saved.ra &&& ~~~(1 : Word)) code
      (((.x1 ↦ᵣ oldRa) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLenN) **
         (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         hfAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes)) **
        (memOwn offAddr ** memOwn lenAddr))
      (hfRetPost offAddr lenAddr newSp listBase outPtr saved headerBytes outBytes listLenN index
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
         memOwn (newSp + 32) ** memOwn (newSp + 40))) := by
  have hinit := hfInitStep base initOffset listBase outPtr newSp oldRa v5 v6 v7 v28 v29 v30 v31
    saved headerBytes outBytes listLenN h_src_align h_slack h_src_over h_src_valid
    hioff halign_i hdisj_i hcode_i
  have hinitF := cpsTripleWithin_frameR (memOwn offAddr ** memOwn lenAddr)
    (pcFree_sepConj pcFree_memOwn pcFree_memOwn) hinit
  have hinit' := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by
      exact sepConj_mono_left (sepConj_mono_left (sepConj_mono_right
        (RlpListNthItemSAsm.initOutcome_to_normalized listBase headerBytes listLenN index (by omega)
          h_slack h_src_over))) h hq)
    hinitF
  rw [show (base + 40 : Word) + 4 = base + 44 from by bv_omega] at hinit'
  have ha_t : (base + 44 : Word) + signExtend13 initBneOff = status1PC := hbne_t
  have ha_f : (base + 44 : Word) + 4 = base + 48 := by bv_omega
  have hdisp : cpsTripleWithin (1 + (4 + nStage1)) (base + 44) (saved.ra &&& ~~~(1 : Word)) code
      (((hfInitCommon (base + 44) listBase headerBytes ** (.x0 ↦ᵣ (0 : Word))) **
        RlpListNthItemSAsm.initNormalized listBase headerBytes listLenN index) **
        (hfAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
         hfScratchConst offAddr lenAddr))
      (hfRetPost offAddr lenAddr newSp listBase outPtr saved headerBytes outBytes listLenN index
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
         memOwn (newSp + 32) ** memOwn (newSp + 40))) := by
    -- FAIL arm
    have hFAIL : cpsTripleWithin (1 + (4 + nStage1)) (base + 44) (saved.ra &&& ~~~(1 : Word)) code
        (((hfInitCommon (base + 44) listBase headerBytes ** (.x0 ↦ᵣ (0 : Word))) **
          (fun h => ∃ status cursor endPtr,
            ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status) **
             ⌜status ≠ (0 : Word) ∧
               RlpListNthItemSAsm.Failure headerBytes listBase listLenN index⌝) h)) **
          (hfAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
           hfScratchConst offAddr lenAddr))
        (hfRetPost offAddr lenAddr newSp listBase outPtr saved headerBytes outBytes listLenN index
          (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
           memOwn (newSp + 32) ** memOwn (newSp + 40))) := by
      refine cpsTripleWithin_weaken
        (P := fun h => ∃ status cursor endPtr,
          (((hfInitCommon (base + 44) listBase headerBytes ** (.x0 ↦ᵣ (0 : Word))) **
            ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status) **
             ⌜status ≠ (0 : Word) ∧
               RlpListNthItemSAsm.Failure headerBytes listBase listLenN index⌝)) **
            (hfAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
             hfScratchConst offAddr lenAddr)) h)
        (fun h hp => by
          obtain ⟨h1, h2, hd, hu, hrf, hab⟩ := hp
          obtain ⟨ha, hb, hd', hu', hreg, hst⟩ := hrf
          obtain ⟨status, cursor, endPtr, hstatus⟩ := hst
          exact ⟨status, cursor, endPtr, ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hstatus⟩, hab⟩⟩)
        (fun _ h => h) ?_
      refine cpsTripleWithin_exists_pre_gen (fun status => ?_)
      refine cpsTripleWithin_exists_pre_gen (fun cursor => ?_)
      refine cpsTripleWithin_exists_pre_gen (fun endPtr => ?_)
      refine cpsTripleWithin_weaken
        (P := ⌜status ≠ (0 : Word) ∧
              RlpListNthItemSAsm.Failure headerBytes listBase listLenN index⌝ **
          (((.x12 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) **
            (hfInitCommon (base + 44) listBase headerBytes ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
             (hfAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
              hfScratchConst offAddr lenAddr))))
        (fun h hp => by xperm_chunked hp)
        (fun _ h => h) ?_
      refine cpsTripleWithin_pure_pre (fun hP => ?_)
      have hbne := bne_spec_gen_within .x12 .x0 initBneOff status (0 : Word) (base + 44)
      rw [ha_t, ha_f] at hbne
      have hbnee := cpsBranchWithin_extend_code hbnemem hbne
      have htk := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQf
        exact hP.1 ((sepConj_pure_right _).1 hQ).2)
      have htkF := cpsTripleWithin_frameR
        (hfInitCommon (base + 44) listBase headerBytes ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
         (hfAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hfScratchConst offAddr lenAddr))
        (by unfold hfInitCommon
            repeat' first
              | exact pcFree_hfScratchConst _ _ | exact pcFree_hfAmbient _ _ _ _ _ _
              | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn
              | exact pcFree_memIs | exact pcFree_memOwn | apply pcFree_sepConj) htk
      have hs1' := hfStatus1Bundled (code := code) status1PC newSp listBase (BitVec.ofNat 64 listLenN)
          outPtr cursor (base + 44) saved
          ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 **
           regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           bytesRegion listBase headerBytes ** memOwn (newSp + 32) ** memOwn (newSp + 40) **
           bytesRegion outPtr outBytes ** hfScratchConst offAddr lenAddr)
          (by repeat' first
            | exact pcFree_hfScratchConst _ _ | exact bytesRegion_pcFree _ _ | exact pcFree_regIs
            | exact pcFree_regOwn | exact pcFree_memIs | exact pcFree_memOwn | apply pcFree_sepConj)
          hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
      have s := cpsTripleWithin_seq_perm_same_cr
        (fun h hq => by
          unfold hfAmbient hfInitCommon at hq
          unfold hesrAmbRegs
          xperm_chunked hq) htkF hs1'
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => hp)
          (fun h hq => by
            refine ⟨(1 : Word), outBytes, (0 : Word), (0 : Word), ?_⟩
            refine (sepConj_pure_right h).2 ⟨?_, Or.inr (Or.inr ⟨rfl, hP.2⟩)⟩
            have hq2 : (((( .x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ saved.ra) **
                hesrAmbRegsRestored newSp saved) **
               (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x12 ↦ᵣ status) ** regOwn .x28 **
                regOwn .x29 ** hfScratchConst offAddr lenAddr ** (.x0 ↦ᵣ (0 : Word)) **
                bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
                ((.x11 ↦ᵣ endPtr) ** regOwn .x30 ** regOwn .x31 **
                 memOwn (newSp + 32) ** memOwn (newSp + 40))))) h := by
              xperm_chunked hq
            exact sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono (regIs_implies_regOwn .x12)
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right
                      (sepConj_mono (regIs_implies_regOwn .x11) (fun _ hh => hh))))))))))))
              h hq2) s)
    -- OK arm
    have hOK : cpsTripleWithin (1 + (4 + nStage1)) (base + 44) (saved.ra &&& ~~~(1 : Word)) code
        (((hfInitCommon (base + 44) listBase headerBytes ** (.x0 ↦ᵣ (0 : Word))) **
          (fun h => ∃ cursorOff endPtr,
            ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) ** (.x11 ↦ᵣ endPtr) **
             (.x12 ↦ᵣ (0 : Word)) **
             ⌜RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff
               endPtr⌝) h)) **
          (hfAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
           hfScratchConst offAddr lenAddr))
        (hfRetPost offAddr lenAddr newSp listBase outPtr saved headerBytes outBytes listLenN index
          (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
           memOwn (newSp + 32) ** memOwn (newSp + 40))) := by
      refine cpsTripleWithin_weaken
        (P := fun h => ∃ cursorOff endPtr,
          (((hfInitCommon (base + 44) listBase headerBytes ** (.x0 ↦ᵣ (0 : Word))) **
            ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) ** (.x11 ↦ᵣ endPtr) **
             (.x12 ↦ᵣ (0 : Word)) **
             ⌜RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff
               endPtr⌝)) **
            (hfAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
             hfScratchConst offAddr lenAddr)) h)
        (fun h hp => by
          obtain ⟨h1, h2, hd, hu, hrf, hab⟩ := hp
          obtain ⟨ha, hb, hd', hu', hreg, hok⟩ := hrf
          obtain ⟨cursorOff, endPtr, hw⟩ := hok
          exact ⟨cursorOff, endPtr, ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hw⟩, hab⟩⟩)
        (fun _ h => h) ?_
      refine cpsTripleWithin_exists_pre_gen (fun cursorOff => ?_)
      refine cpsTripleWithin_exists_pre_gen (fun endPtr => ?_)
      refine cpsTripleWithin_weaken
        (P := ⌜RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff
              endPtr⌝ **
          (((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
            (hfInitCommon (base + 44) listBase headerBytes **
             (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) ** (.x11 ↦ᵣ endPtr) **
             (hfAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
              hfScratchConst offAddr lenAddr))))
        (fun h hp => by xperm_chunked hp)
        (fun _ h => h) ?_
      refine cpsTripleWithin_pure_pre (fun hpayload => ?_)
      have hend : endPtr = listBase + BitVec.ofNat 64 listLenN := hpayload.end_eq
      subst hend
      have hbne := bne_spec_gen_within .x12 .x0 initBneOff (0 : Word) (0 : Word) (base + 44)
      rw [ha_t, ha_f] at hbne
      have hbnee := cpsBranchWithin_extend_code hbnemem hbne
      have hntk := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQt
        exact ((sepConj_pure_right _).1 hQ).2 rfl)
      have hntkF := cpsTripleWithin_frameR
        (hfInitCommon (base + 44) listBase headerBytes **
         (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
         (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) **
         (hfAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hfScratchConst offAddr lenAddr))
        (by unfold hfInitCommon
            repeat' first
              | exact pcFree_hfScratchConst _ _ | exact pcFree_hfAmbient _ _ _ _ _ _
              | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn
              | exact pcFree_memIs | exact pcFree_memOwn | apply pcFree_sepConj) hntk
      have hmi := hfMarshalInitBundled (code := code) base offAddr lenAddr
          (listBase + BitVec.ofNat 64 cursorOff) (listBase + BitVec.ofNat 64 listLenN) newSp
          listBase (BitVec.ofNat 64 listLenN) outPtr saved outBytes
          ((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** hfInitCommon (base + 44) listBase headerBytes)
          (by unfold hfInitCommon
              repeat' first
                | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn
                | apply pcFree_sepConj)
          hmi0 hmi1 hmi2 hmi3
      have hst1 := cpsTripleWithin_of_forall_regIs_to_regOwn7
        (hstage1 cursorOff hpayload)
      have hrec := cpsTripleWithin_seq_perm_same_cr
        (fun h hq => by unfold hfInitCommon at hq; xperm_chunked hq) hmi hst1
      have hrec' := cpsTripleWithin_weaken (fun _ hp => hp)
        (fun h hq => hfRetPost_frame_mono
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (fun h' hh => by rw [sepConj_emp_right'] at hh; exact memIs_implies_memOwn h' hh)))))
          h hq) hrec
      exact cpsTripleWithin_seq_perm_same_cr (fun h hq => by xperm_chunked hq) hntkF hrec'
    refine cpsTripleWithin_weaken
      (fun h hp => by
        obtain ⟨h1, h2, hd, hu, hrf, hab⟩ := hp
        obtain ⟨ha, hb, hd', hu', hreg, hnorm⟩ := hrf
        unfold RlpListNthItemSAsm.initNormalized at hnorm
        rcases hnorm with hok | hfail
        · exact Or.inl ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hok⟩, hab⟩
        · exact Or.inr ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hfail⟩, hab⟩)
      (fun _ h => h) (cpsTripleWithin_or_pre hOK hFAIL)
  refine cpsTripleWithin_seq_perm_same_cr ?_ hinit' hdisp
  intro h hq
  unfold hfScratchConst
  xperm_chunked hq


end EvmAsm.Codegen.HeaderFieldsSpec
