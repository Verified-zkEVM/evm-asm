/-
  K67 post-loop merged station contracts and branch composition.
-/
import EvmAsm.Codegen.Programs.HeaderValidatePostMergePostLoopPhasesCore

namespace EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpWalkNextStrictFuel
open EvmAsm.Codegen.RlpListNthItemSAsm


/-! ## Merged post-loop N-branch -/

/-- Post-loop success post at the status-0 stub `K + 596`: the full
    pass-through state with the compare-scratch registers pinned to their
    final values, plus the semantic payload — nonce is eight zero bytes and
    the ommers hash content matches `k67OmBytes` (all in `getD` form, which is
    what the SpecRef bridge consumes). -/
def k67QOk (sp0 base omConst endPtr : Word) (bytes : List (BitVec 8))
    (next14 len14 omEndW omLenW : Word) (csIdx omIdx : Nat)
    (v29 v30 v31 v21 : Word) (svals : Reg → Word) : Assertion :=
  (((.x1 ↦ᵣ (K + 68)) **
    (.x5 ↦ᵣ ((GuestAddrs.empty_ommers_hash : Word))) **
    (.x6 ↦ᵣ (omEndW - omLenW)) **
    (.x7 ↦ᵣ ((k67OmBytes.getD 31 (0 : BitVec 8)).zeroExtend 64)) **
    (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
    (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) ** (.x18 ↦ᵣ next14) **
    (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) ** (.x21 ↦ᵣ v21) **
    (.x28 ↦ᵣ ((k67OmBytes.getD 31 (0 : BitVec 8)).zeroExtend 64)) **
    (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
    regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
    (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
    frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
    bytesRegion base bytes ** bytesRegion omConst (k67OmBytes)) **
  ⌜len14 = (8 : Word) ∧
    (∀ (k : Nat), k < 8 → bytes.getD (csIdx + k) (0 : BitVec 8) = 0) ∧
    omLenW = (32 : Word) ∧
    (∀ (k : Nat), k < 32 → bytes.getD (omIdx + k) (0 : BitVec 8) =
      k67OmBytes.getD k (0 : BitVec 8))⌝)

/-- Post-loop nonce-failure post at the status-2 stub `K + 612`:
    pass-through state with the scratch registers existentialized, plus the
    failure witness (bad length or a nonzero byte). -/
def k67QNonceFail (sp0 base omConst endPtr : Word) (bytes : List (BitVec 8))
    (next14 len14 omEndW omLenW : Word) (csIdx _omIdx : Nat)
    (v28 v29 v30 v31 v21 : Word) (svals : Reg → Word) : Assertion := fun h =>
  ∃ v5 v6 v7 : Word,
    (((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
      (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) ** (.x18 ↦ᵣ next14) **
      (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) ** (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes ** bytesRegion omConst (k67OmBytes)) **
    ⌜len14 ≠ (8 : Word) ∨
      ∃ (k : Nat), k < 8 ∧ bytes.getD (csIdx + k) (0 : BitVec 8) ≠ 0⌝) h

/-- Ommers-failure station post (`K + 620`): the ommers length gate failed or
    some ommers byte mismatched the pinned constant.  The clobbered registers
    are existential (`x28` included: the byte-fail path loads the constant into
    it, the length-gate path leaves it untouched). -/
def k67QOmmersFail (sp0 base omConst endPtr : Word) (bytes : List (BitVec 8))
    (next14 len14 omEndW omLenW : Word) (_csIdx omIdx : Nat)
    (v29 v30 v31 v21 : Word) (svals : Reg → Word) : Assertion := fun h =>
  ∃ v5 v6 v7 v28o : Word,
    (((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
      (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) ** (.x18 ↦ᵣ next14) **
      (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) ** (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28o) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes ** bytesRegion omConst (k67OmBytes)) **
    ⌜omLenW ≠ (32 : Word) ∨
      ∃ (k : Nat), k < 32 ∧ bytes.getD (omIdx + k) (0 : BitVec 8) ≠
        k67OmBytes.getD k (0 : BitVec 8)⌝) h

/-! ## Merged post-loop N-branch -/

theorem k67_getD_eq {bytes : List (BitVec 8)} {dflt : BitVec 8} {n : Nat}
    (hn : n < bytes.length) : bytes.getD n dflt = bytes[n]'hn := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
  rfl

/-- The whole post-loop region as one N-branch: from the loop-exit state at
    `K + 116`, control reaches the success station `K + 596`, the ommers
    station `K + 620`, or the nonce station `K + 612` within 124 instructions,
    with each station post carrying the semantic fact its exit test
    established. -/
theorem k67PostLoop (sp0 base omConst endPtr : Word)
    (bytes : List (BitVec 8))
    (next14 len14 omEndW omLenW v6 v7 v28 v29 v30 v31 v21 : Word)
    (svals : Reg → Word) (csIdx omIdx : Nat)
    (halign : base.toNat % 8 = 0)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k', k' < bytes.length →
      isValidByteAccess (base + BitVec.ofNat 64 k') = true)
    (hcsE14 : len14 = (8 : Word) → next14 - len14 = base + BitVec.ofNat 64 csIdx)
    (hib14 : len14 = (8 : Word) → csIdx + 8 ≤ bytes.length)
    (hib1 : omLenW = (32 : Word) → omIdx + 32 ≤ bytes.length)
    (hcsE1 : omLenW = (32 : Word) → omEndW - (32 : Word) = base + BitVec.ofNat 64 omIdx)
    (hvalid2 : ∀ (j' : Nat) (_hj' : j' < 32),
      isValidByteAccess (omConst + BitVec.ofNat 64 j') = true)
    (homC : omConst = ((GuestAddrs.empty_ommers_hash : Word)))
    (haddr8 : len14 = (8 : Word) → ∀ (j' : Nat) (_hj' : j' < 8),
      next14 - (8 : Word) + signExtend12 (BitVec.ofNat 12 j') =
        base + BitVec.ofNat 64 (csIdx + j'))
    (haddr32 : omLenW = (32 : Word) → ∀ (j' : Nat) (_hj' : j' < 32),
      omEndW - (32 : Word) + signExtend12 (BitVec.ofNat 12 j') =
        base + BitVec.ofNat 64 (omIdx + j'))
    (offsN offsO : Nat → BitVec 13)
    (htakenN : ∀ (j' : Nat) (_hj' : j' < 8),
      (K + BitVec.ofNat 64 (132 + 8 * j')) + signExtend13 (offsN j') =
        K + 612)
    (htakenO : ∀ (j' : Nat) (_hj' : j' < 32),
      (K + BitVec.ofNat 64 (212 + 12 * j') + 8) + signExtend13 (offsO j') =
        K + 620)
    (hlookLBUN : ∀ (j' : Nat) (hj' : j' < 8),
      k67Prog.get ⟨32 + 2 * j', by rw [k67_length]; omega⟩ =
        Instr.LBU .x7 .x6 (BitVec.ofNat 12 j'))
    (hlookBNEN : ∀ (j' : Nat) (hj' : j' < 8),
      k67Prog.get ⟨33 + 2 * j', by rw [k67_length]; omega⟩ =
        Instr.BNE .x7 .x0 (offsN j'))
    (hlookLBU1 : ∀ (j' : Nat) (hj' : j' < 32),
      k67Prog.get ⟨53 + 3 * j', by rw [k67_length]; omega⟩ =
        Instr.LBU .x7 .x6 (BitVec.ofNat 12 j'))
    (hlookLBU2 : ∀ (j' : Nat) (hj' : j' < 32),
      k67Prog.get ⟨54 + 3 * j', by rw [k67_length]; omega⟩ =
        Instr.LBU .x28 .x5 (BitVec.ofNat 12 j'))
    (hlookBNEO : ∀ (j' : Nat) (hj' : j' < 32),
      k67Prog.get ⟨55 + 3 * j', by rw [k67_length]; omega⟩ =
        Instr.BNE .x7 .x28 (offsO j')) :
    cpsNBranchWithin 124 (K + 116) fullCode
      (k67PLPre sp0 base omConst endPtr bytes next14 len14 omEndW omLenW
        v6 v7 v28 v29 v30 v31 v21 svals)
      [(K + 596, k67QOk sp0 base omConst endPtr bytes next14 len14 omEndW
          omLenW csIdx omIdx v29 v30 v31 v21 svals),
        (K + 620, k67QOmmersFail sp0 base omConst endPtr bytes next14 len14
          omEndW omLenW csIdx omIdx v29 v30 v31 v21 svals),
        (K + 612, k67QNonceFail sp0 base omConst endPtr bytes next14 len14
          omEndW omLenW csIdx omIdx v28 v29 v30 v31 v21 svals)] := by
  by_cases hlen : len14 = (8 : Word)
  · by_cases hz : ∀ k', k' < 8 →
        bytes.getD (csIdx + k') (0 : BitVec 8) = (0 : BitVec 8)
    · -- nonce clean: phase 1 into the K+192 gate, then phase 2.
      have hib14' := hib14 hlen
      have hzero8 : ∀ (j' : Nat) (hj' : j' < 8),
          bytes[csIdx + j']'(by omega) = (0 : BitVec 8) := by
        intro j' hj'
        have h1 := hz j' hj'
        rw [k67_getD_eq (by omega)] at h1
        exact h1
      have hpass := k67NoncePass sp0 base omConst endPtr bytes next14 len14
        omEndW omLenW v6 v7 v28 v29 v30 v31 v21 svals csIdx hlen (hcsE14 hlen)
        (hib14 hlen) halign hover hvalid hzero8 offsN (haddr8 hlen) hlookLBUN
        hlookBNEN
      have h1 : cpsNBranchWithin (3 + 2 * 8) (K + 116) fullCode
          (k67PLPre sp0 base omConst endPtr bytes next14 len14 omEndW omLenW
            v6 v7 v28 v29 v30 v31 v21 svals)
          [(K + 192, k67PLPreO sp0 base omConst endPtr bytes next14 len14
              omEndW omLenW (8 : Word) (next14 - len14) (0 : Word) v28 v29 v30
              v31 v21 svals),
            (K + 612, k67QNonceFail sp0 base omConst endPtr bytes next14 len14
              omEndW omLenW csIdx omIdx v28 v29 v30 v31 v21 svals)] := by
        apply cpsNBranchWithin_of_triple
          (Q := k67PLPreO sp0 base omConst endPtr bytes next14 len14 omEndW
            omLenW (8 : Word) (next14 - len14) (0 : Word) v28 v29 v30 v31 v21
            svals)
          (by apply List.Mem.head)
        exact cpsTripleWithin_weaken (fun _ hp => hp)
          (fun _ hq => by unfold k67PLPreO; xperm_hyp hq) hpass
      have h2 : cpsNBranchWithin 101 (K + 192) fullCode
          (k67PLPreO sp0 base omConst endPtr bytes next14 len14 omEndW omLenW
            (8 : Word) (next14 - len14) (0 : Word) v28 v29 v30 v31 v21 svals)
          [(K + 596, k67QOk sp0 base omConst endPtr bytes next14 len14 omEndW
              omLenW csIdx omIdx v29 v30 v31 v21 svals),
            (K + 620, k67QOmmersFail sp0 base omConst endPtr bytes next14 len14
              omEndW omLenW csIdx omIdx v29 v30 v31 v21 svals)] := by
        by_cases hlen1 : omLenW = (32 : Word)
        · by_cases hm : ∀ k', k' < 32 → bytes.getD (omIdx + k') (0 : BitVec 8) =
              k67OmBytes.getD k' (0 : BitVec 8)
          · have hib1' := hib1 hlen1
            -- all 32 ommers bytes match
            have hmatch32 : ∀ (j' : Nat) (hj' : j' < 32),
                bytes[omIdx + j']'(by omega) =
                  k67OmBytes[j']'(by
                    rw [show k67OmBytes.length = 32 from
                      ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]
                    omega) := by
              intro j' hj'
              have h1 := hm j' hj'
              rw [k67_getD_eq (by omega)] at h1
              rw [k67_getD_eq (by
                rw [show k67OmBytes.length = 32 from
                  ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]
                omega)] at h1
              exact h1
            have hpassO := k67OmmersPass sp0 base omConst endPtr bytes next14
              len14 omEndW omLenW omIdx (8 : Word) (next14 - len14) (0 : Word)
              v28 v29 v30 v31 v21 svals hlen1 homC (hcsE1 hlen1) (hib1 hlen1)
              halign hover hvalid hvalid2 hmatch32 offsO (haddr32 hlen1)
              hlookLBU1 hlookLBU2 hlookBNEO
            apply cpsNBranchWithin_mono_nSteps (show 5 + 3 * 32 ≤ 101 by omega)
            apply cpsNBranchWithin_of_triple
              (Q := k67QOk sp0 base omConst endPtr bytes next14 len14 omEndW
                omLenW csIdx omIdx v29 v30 v31 v21 svals)
              (by apply List.Mem.head)
            refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hpassO
            intro h hq
            have hconv : ((k67OmBytes[0 + 32 - 1]'(by
                  rw [show k67OmBytes.length = 32 from
                    ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]
                  omega)).zeroExtend 64) =
                ((k67OmBytes.getD 31 (0 : BitVec 8)).zeroExtend 64) := by
              rw [k67_getD_eq (by
                rw [show k67OmBytes.length = 32 from
                  ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]
                omega)]
            rw [hconv] at hq
            refine (sepConj_pure_right _).2 ⟨?_, hlen, hz, hlen1, hm⟩
            xperm_hyp hq
          · -- some ommers byte mismatches: take the minimal one
            have hib1' := hib1 hlen1
            haveI : DecidablePred (fun k' => k' < 32 ∧
                bytes.getD (omIdx + k') (0 : BitVec 8) ≠
                  k67OmBytes.getD k' (0 : BitVec 8)) := inferInstance
            obtain ⟨kw, hkw32, hwm⟩ : ∃ k', k' < 32 ∧
                bytes.getD (omIdx + k') (0 : BitVec 8) ≠
                  k67OmBytes.getD k' (0 : BitVec 8) := by
              have h1 := Classical.not_forall.mp hm
              obtain ⟨w, hw⟩ := h1
              have ⟨hw32, hwne⟩ := Classical.not_imp.mp hw
              exact ⟨w, hw32, hwne⟩
            have hW : ∃ k', k' < 32 ∧ bytes.getD (omIdx + k') (0 : BitVec 8) ≠
                k67OmBytes.getD k' (0 : BitVec 8) := ⟨kw, hkw32, hwm⟩
            let n := Nat.find hW
            have hnspec := Nat.find_spec hW
            have hn32 : n < 32 := hnspec.1
            have hpre : ∀ (j' : Nat) (hj' : j' < n),
                bytes[omIdx + j']'(by omega) =
                  k67OmBytes[j']'(by
                    rw [show k67OmBytes.length = 32 from
                      ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]
                    omega) := by
              intro j' hj'
              have hmin := Nat.find_min hW hj'
              have heq : bytes.getD (omIdx + j') (0 : BitVec 8) =
                  k67OmBytes.getD j' (0 : BitVec 8) :=
                of_not_not (fun hb => hmin ⟨by omega, hb⟩)
              rw [k67_getD_eq (by omega)] at heq
              rw [k67_getD_eq (by
                rw [show k67OmBytes.length = 32 from
                  ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]
                omega)] at heq
              exact heq
            have hbyte' : bytes[omIdx + n]'(by omega) ≠
                k67OmBytes[n]'(by
                  rw [show k67OmBytes.length = 32 from
                    ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]
                  omega) := by
              have h1 := hnspec.2
              rw [k67_getD_eq (by omega)] at h1
              rw [k67_getD_eq (by
                rw [show k67OmBytes.length = 32 from
                  ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]
                omega)] at h1
              exact h1
            have hbf := k67OmmersByteFail sp0 base omConst endPtr bytes next14
              len14 omEndW omLenW omIdx n (8 : Word) (next14 - len14)
              (0 : Word) v28 v29 v30 v31 v21 svals hlen1 homC (hcsE1 hlen1)
              (hib1 hlen1) halign hover hvalid hvalid2 hn32 hpre hbyte' offsO
              (haddr32 hlen1) htakenO hlookLBU1 hlookLBU2 hlookBNEO
            apply cpsNBranchWithin_mono_nSteps
              (show 5 + (3 * n + 3) ≤ 101 by omega)
            apply cpsNBranchWithin_of_triple
              (Q := k67QOmmersFail sp0 base omConst endPtr bytes next14 len14
                omEndW omLenW csIdx omIdx v29 v30 v31 v21 svals)
              (by apply List.Mem.tail; apply List.Mem.head)
            refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hbf
            intro h hq
            refine ⟨((GuestAddrs.empty_ommers_hash : Word)), omEndW - omLenW,
              ((bytes[omIdx + n]'(by omega)).zeroExtend 64),
              ((k67OmBytes[n]'(by
                rw [show k67OmBytes.length = 32 from
                  ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length]
                omega)).zeroExtend 64), ?_⟩
            refine (sepConj_pure_right _).2 ⟨?_,
              (Or.inr ⟨n, hnspec⟩ : omLenW ≠ (32 : Word) ∨
                ∃ (k : Nat), k < 32 ∧ bytes.getD (omIdx + k) (0 : BitVec 8) ≠
                  k67OmBytes.getD k (0 : BitVec 8))⟩
            xperm_hyp hq
        · -- ommers length gate fails
          have hlf := k67OmmersLenFail sp0 base omConst endPtr bytes next14
            len14 omEndW omLenW (8 : Word) (next14 - len14) (0 : Word) v28 v29
            v30 v31 v21 svals hlen1
          apply cpsNBranchWithin_mono_nSteps (show 2 ≤ 101 by omega)
          apply cpsNBranchWithin_of_triple
            (Q := k67QOmmersFail sp0 base omConst endPtr bytes next14 len14
              omEndW omLenW csIdx omIdx v29 v30 v31 v21 svals)
            (by apply List.Mem.tail; apply List.Mem.head)
          refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hlf
          intro h hq
          refine ⟨(32 : Word), next14 - len14, (0 : Word), v28, ?_⟩
          refine (sepConj_pure_right _).2 ⟨?_, Or.inl hlen1⟩
          xperm_hyp hq
      exact cpsNBranchWithin_mono_nSteps (show 3 + 2 * 8 + 101 ≤ 124 by omega)
        (cpsNBranchWithin_extend_head_nbranch h1 h2)
    · -- nonce length OK but some nonce byte nonzero: minimal witness.
      have hib14' := hib14 hlen
      haveI : DecidablePred (fun k' => k' < 8 ∧
          bytes.getD (csIdx + k') (0 : BitVec 8) ≠ (0 : BitVec 8)) :=
        inferInstance
      obtain ⟨kw, hkw8, hwm⟩ : ∃ k', k' < 8 ∧
          bytes.getD (csIdx + k') (0 : BitVec 8) ≠ (0 : BitVec 8) := by
        have h1 := Classical.not_forall.mp hz
        obtain ⟨w, hw⟩ := h1
        have ⟨hw8, hwne⟩ := Classical.not_imp.mp hw
        exact ⟨w, hw8, hwne⟩
      have hW : ∃ k', k' < 8 ∧ bytes.getD (csIdx + k') (0 : BitVec 8) ≠
          (0 : BitVec 8) := ⟨kw, hkw8, hwm⟩
      let n := Nat.find hW
      have hnspec := Nat.find_spec hW
      have hn8 : n < 8 := hnspec.1
      have hpre : ∀ (j' : Nat) (hj' : j' < n),
          bytes[csIdx + j']'(by omega) = (0 : BitVec 8) := by
        intro j' hj'
        have hmin := Nat.find_min hW hj'
        have heq : bytes.getD (csIdx + j') (0 : BitVec 8) = (0 : BitVec 8) :=
          of_not_not (fun hb => hmin ⟨by omega, hb⟩)
        rw [k67_getD_eq (by omega)] at heq
        exact heq
      have hbyte' : bytes[csIdx + n]'(by omega) ≠ (0 : BitVec 8) := by
        have h1 := hnspec.2
        rw [k67_getD_eq (by omega)] at h1
        exact h1
      have hbf := k67NonceByteFail sp0 base omConst endPtr bytes next14 len14
        omEndW omLenW v6 v7 v28 v29 v30 v31 v21 svals n csIdx hlen (hcsE14 hlen)
        (hib14 hlen) halign hover hvalid hn8 hpre hbyte' offsN (haddr8 hlen)
        htakenN hlookLBUN hlookBNEN
      apply cpsNBranchWithin_mono_nSteps (show 3 + (2 * n + 2) ≤ 124 by omega)
      apply cpsNBranchWithin_of_triple
        (Q := k67QNonceFail sp0 base omConst endPtr bytes next14 len14 omEndW
          omLenW csIdx omIdx v28 v29 v30 v31 v21 svals)
        (by apply List.Mem.tail; apply List.Mem.tail; apply List.Mem.head)
      refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hbf
      intro h hq
      refine ⟨(8 : Word), next14 - len14,
        ((bytes[csIdx + n]'(by omega)).zeroExtend 64), ?_⟩
      refine (sepConj_pure_right _).2 ⟨?_,
        (Or.inr ⟨n, hnspec⟩ : len14 ≠ (8 : Word) ∨
          ∃ (k : Nat), k < 8 ∧ bytes.getD (csIdx + k) (0 : BitVec 8) ≠ 0)⟩
      xperm_hyp hq
  · -- nonce length gate fails immediately
    have hlf := k67NonceLenFail sp0 base omConst endPtr bytes next14 len14
      omEndW omLenW v6 v7 v28 v29 v30 v31 v21 svals hlen
    apply cpsNBranchWithin_mono_nSteps (show 2 ≤ 124 by omega)
    apply cpsNBranchWithin_of_triple
      (Q := k67QNonceFail sp0 base omConst endPtr bytes next14 len14 omEndW
        omLenW csIdx omIdx v28 v29 v30 v31 v21 svals)
      (by apply List.Mem.tail; apply List.Mem.tail; apply List.Mem.head)
    refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hlf
    intro h hq
    refine ⟨(8 : Word), v6, v7, ?_⟩
    refine (sepConj_pure_right _).2 ⟨?_, Or.inl hlen⟩
    xperm_hyp hq


end EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec
