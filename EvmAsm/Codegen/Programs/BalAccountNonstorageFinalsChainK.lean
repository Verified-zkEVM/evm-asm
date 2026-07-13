/- Code-station outer composition for bal_account_nonstorage_finals. -/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainJ

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

/-- Reframe a successful code tuple `walk_init` for the continuation at
    `B + 652`. -/
theorem codeTupleInitOk_to_cont652Pre
    (aB newSp oB n5 v19 v20 s64 s72 : Word)
    (aLen tOff tSpanN : Nat) (acctBytes : List (BitVec 8))
    (G F : Assertion) :
    ∀ h,
      ((fieldInitPost aB tOff tSpanN acctBytes (B + 644 + 4) F **
        (((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
         ((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ s64) **
         ((newSp + 72) ↦ₘ s72) ** G **
         ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
         ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
         ((.x18 : Reg) ↦ᵣ oB))) h →
      (∃ cOff : Nat,
        (((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
            ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (tOff + tSpanN))) **
            ((.x2 : Reg) ↦ᵣ newSp) ** memOwn (newSp + 64) **
            memOwn (newSp + 72)) **
           (((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
            ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
            ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
            ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
            ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
            ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
            regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1 **
            bytesRegion aB acctBytes ** G ** F)) **
          ⌜FieldInitOk acctBytes tOff tSpanN cOff⌝) h)) := by
  intro h hp
  unfold fieldInitPost at hp
  obtain ⟨g1, g2, gd, gu, hInit, hfr⟩ := hp
  obtain ⟨cOff, hInit2⟩ := hInit
  obtain ⟨hregs, hok⟩ := (sepConj_pure_right g1).1 hInit2
  have hR := (⟨g1, g2, gd, gu, hregs, hfr⟩ :
    (((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
      ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (tOff + tSpanN))) **
      ((.x12 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
      regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) ** bytesRegion aB acctBytes ** F) **
     (((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
      ((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ s64) **
      ((newSp + 72) ↦ₘ s72) ** G **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB))) h))
  have hconv := sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn .x19)
      (sepConj_mono (regIs_implies_regOwn .x20)
        (sepConj_mono (fun _ x => x)
          (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn (fun _ x => x)))))) h hR
  have hconv2 := sepConj_mono
    (sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x)
        (sepConj_mono (fun _ x => x)
          (sepConj_mono (fun _ x => x)
            (sepConj_mono (fun _ x => x)
              (sepConj_mono (fun _ x => x)
                (sepConj_mono (fun _ x => x)
                  (sepConj_mono (fun _ x => x)
                    (sepConj_mono (fun _ x => x)
                      (sepConj_mono (fun _ x => x)
                        (sepConj_mono (fun _ x => x)
                          (sepConj_mono (regIs_implies_regOwn .x1)
                            (fun _ x => x)))))))))))))
    (fun _ x => x) h hconv
  refine ⟨cOff, (sepConj_pure_right h).2 ⟨?_, hok⟩⟩
  xperm_hyp hconv2

#print axioms codeTupleInitOk_to_cont652Pre

/-- Slots 159–160 (`B + 636 → B + 644`): move the last code tuple span into
    the tuple `rlp_walk_init` arguments, accepting owned destination regs. -/
theorem bansf_codeLoopExitMove159_own_spec (v19 v20 : Word) :
    cpsTripleWithin 2 (B + 636) (B + 644) bansfCR
      (((((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20)) **
        regOwn .x10 ** regOwn .x11))
      ((((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20)) **
       ((.x10 : Reg) ↦ᵣ v19) ** ((.x11 : Reg) ↦ᵣ v20)) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2
    (r1 := .x10) (r2 := .x11) (fun v10 v11 => ?_)
  have s1 := mv_spec_gen_within .x10 .x19 v19 v10 (B + 636) (by decide)
  rw [show (B + 636) + 4 = B + 640 from by bv_omega] at s1
  have s1L := liftCode (cr' := bansfCR) s1
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 636) bansfProg 159 (.MV .x10 .x19)
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h))
  have s2 := mv_spec_gen_within .x11 .x20 v20 v11 (B + 640) (by decide)
  rw [show (B + 640) + 4 = B + 644 from by bv_omega] at s2
  have s2L := liftCode (cr' := bansfCR) s2
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 640) bansfProg 160 (.MV .x11 .x20)
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h))
  have s1F := cpsTripleWithin_frameR
    (((.x20 : Reg) ↦ᵣ v20) ** ((.x11 : Reg) ↦ᵣ v11)) (by pcf) s1L
  have s2F := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ v19) ** ((.x10 : Reg) ↦ᵣ v19)) (by pcf) s2L
  have hc := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) s1F s2F
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) hc

#print axioms bansf_codeLoopExitMove159_own_spec


theorem bansf_codeStationCont636_spec (aB newSp oB : Word)
    (aLen fOff fSpanN : Nat) (n5 : Word) (b : BitVec 8)
    (acctBytes : List (BitVec 8)) (G F : Assertion)
    (hG : G.pcFree) (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hb : acctBytes[fOff]? = some b)
    (hne : fOff + listHeaderSize b ≠ fOff + fSpanN)
    (hoff0le : fOff + listHeaderSize b ≤ fOff + fSpanN)
    (hfE : fOff + fSpanN ≤ aLen) :
    cpsBranchWithin (7 * acctBytes.length + 291) (B + 636) bansfCR
      (fun h => ∃ n l : Word,
        (((((((.x19 : Reg) ↦ᵣ (n - l)) ** ((.x20 : Reg) ↦ᵣ l)) **
            regOwn .x10 ** regOwn .x11) **
           (((.x2 : Reg) ↦ᵣ newSp) **
            ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
            ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
            ((.x5 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
            ((.x6 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
            ((newSp + 48) ↦ₘ n5) **
            ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
            ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
            ((.x18 : Reg) ↦ᵣ oB) **

            ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
            ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            bytesRegion aB acctBytes ** G ** F)) **
          regOwn .x7 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** regOwn .x1) **
          ⌜LastItemAt acctBytes aB (aB + BitVec.ofNat 64 (fOff + fSpanN))
            (fOff + listHeaderSize b) n l⌝) h)
      (B + 736) (codeStationRej aB newSp oB aLen acctBytes G F)
      (B + 724)
        (codeStationPost aB newSp oB aLen fOff fSpanN n5 acctBytes G F) := by
  refine cpsBranchWithin_exists_pre (fun n => ?_)
  refine cpsBranchWithin_exists_pre (fun l => ?_)
  refine cpsBranchWithin_pure_pre_right (fun hlast => ?_)
  refine cpsBranchWithin_of_forall_regIs_to_regOwn7
    (fun v7 v12 v28 v29 v30 v31 vRa => ?_)
  obtain ⟨offT, hoffTle, hdecT⟩ := LastItemAt_decode hlast hoff0le (by omega)
  obtain ⟨hrepT, _, _⟩ := rlpItemDecode_spanStart hdecT hoffTle (by omega)
  rw [hrepT]
  have hmv := bansf_codeLoopExitMove159_own_spec (n - l) l
  let HM : Assertion :=
    ((.x2 : Reg) ↦ᵣ newSp) **
    ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
    ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
    ((.x5 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
    ((.x6 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
    ((newSp + 48) ↦ₘ n5) **
    ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
    ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
    ((.x18 : Reg) ↦ᵣ oB) **

    ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
    ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    ((.x7 : Reg) ↦ᵣ v7) ** ((.x12 : Reg) ↦ᵣ v12) **
    ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
    ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
    ((.x1 : Reg) ↦ᵣ vRa) ** bytesRegion aB acctBytes ** G ** F
  have hHM : HM.pcFree := by dsimp only [HM]; pcf; exact hG; exact hF
  have hmvF := cpsTripleWithin_frameR HM hHM hmv
  rw [hrepT] at hmvF
  have hfi := bansf_codeTupleInit161_spec aB aLen ((n - l - aB).toNat) l
    acctBytes (aB + BitVec.ofNat 64 (fOff + fSpanN))
    (aB + BitVec.ofNat 64 (fOff + fSpanN)) v7 v12 v28 v29 v30 v31 vRa
    F hF hsalign hslack hover hvalid (by omega)
  let HI : Assertion :=
    ((.x19 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((n - l - aB).toNat))) **
    ((.x20 : Reg) ↦ᵣ l) ** ((.x2 : Reg) ↦ᵣ newSp) **
    ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
    ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
    G **
    ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
    ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
    ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
    ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
    ((.x18 : Reg) ↦ᵣ oB)
  have hHI : HI.pcFree := by dsimp only [HI]; pcf; exact hG; pcf
  have hfiF := cpsBranchWithin_frameR HI hHI hfi
  have hfiW := cpsBranchWithin_weaken
    (Q_t' := codeStationRej aB newSp oB aLen acctBytes G F)
    (fun _ hp => hp)
    (fun h hq => codeTupleInitReject_to_stationRej aB newSp oB n5
      (aB + BitVec.ofNat 64 ((n - l - aB).toNat)) l
      (aB + BitVec.ofNat 64 (fOff + fSpanN))
      (aB + BitVec.ofNat 64 (fOff + fSpanN)) aLen acctBytes G F h
      (by dsimp only [HI] at hq; xperm_hyp hq))
    (fun _ hq => hq) hfiF
  have hcAll : cpsBranchWithin (7 * acctBytes.length + 205) (B + 652) bansfCR
      (fun h => ∃ cOff : Nat,
        (((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
            ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64
              ((n - l - aB).toNat + l.toNat))) **
            ((.x2 : Reg) ↦ᵣ newSp) ** memOwn (newSp + 64) **
            memOwn (newSp + 72)) **
           (((.x12 : Reg) ↦ᵣ (0 : Word)) **
            ((newSp + 48) ↦ₘ n5) **
            ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
            ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
            ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **

            ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
            ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
            regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1 **
            bytesRegion aB acctBytes ** G ** F)) **
          ⌜FieldInitOk acctBytes ((n - l - aB).toNat) l.toNat cOff⌝) h)
      (B + 736) (codeStationRej aB newSp oB aLen acctBytes G F)
      (B + 724)
        (codeStationPost aB newSp oB aLen fOff fSpanN n5 acctBytes G F) := by
    refine cpsBranchWithin_exists_pre (fun cOff => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hok => ?_)
    obtain ⟨b2, hb2, hceq2, _, hcle2⟩ := hok
    exact bansf_codeStationCont652_spec aB newSp oB aLen
      ((n - l - aB).toNat + l.toNat) cOff fOff fSpanN n5 acctBytes G F
      hG hF hsalign hslack hover hvalid (by omega) hcle2
      (fun iNext iLen vNext vLen hdecI hdecV =>
        FieldFinal.last b n l vNext vLen hb hne hlast
          ⟨b2, hb2, iNext, iLen, hceq2 ▸ hdecI, hdecV⟩)
  have hcFromInit := cpsBranchWithin_weaken
    (codeTupleInitOk_to_cont652Pre aB newSp oB n5
      (aB + BitVec.ofNat 64 ((n - l - aB).toNat)) l
      (aB + BitVec.ofNat 64 (fOff + fSpanN))
      (aB + BitVec.ofNat 64 (fOff + fSpanN)) aLen
      ((n - l - aB).toNat) l.toNat acctBytes G F)
    (fun _ hq => hq) (fun _ hq => hq) hcAll
  have hchain := cpsBranchWithin_chain_snd hfiW hcFromInit
  have hfull := cpsTripleWithin_seq_branch_same_cr hmvF
    (cpsBranchWithin_weaken (fun h hp => by dsimp only [HM, HI]; xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq) hchain)
  exact cpsBranchWithin_weaken (fun h hp => by dsimp only [HM]; xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_mono_nSteps (by omega) hfull)

#print axioms bansf_codeStationCont636_spec


end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
