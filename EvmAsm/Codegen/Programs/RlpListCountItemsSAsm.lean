import EvmAsm.Codegen.Programs.RlpListCountItemsSAsmTail

namespace EvmAsm.Codegen.RlpListCountItemsSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

theorem cpsTripleWithin_of_forall_regIs_to_regOwn7
    {n : Nat} {entry exit_ : Word} {r1 r2 r3 r4 r5 r6 r7 : Reg}
    {P Q : Assertion} {cr : CodeReq}
    (h : ∀ v1 v2 v3 v4 v5 v6 v7, cpsTripleWithin n entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) **
       (r4 ↦ᵣ v4) ** (r5 ↦ᵣ v5) ** (r6 ↦ᵣ v6) ** (r7 ↦ᵣ v7)) Q) :
    cpsTripleWithin n entry exit_ cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 **
       regOwn r5 ** regOwn r6 ** regOwn r7) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨v3, hv3⟩, hO4⟩ := hO3
  obtain ⟨g8, g9, d5, u5, ⟨v4, hv4⟩, hO5⟩ := hO4
  obtain ⟨g10, g11, d6, u6, ⟨v5, hv5⟩, hO6⟩ := hO5
  obtain ⟨g12, g13, d7, u7, ⟨v6, hv6⟩, ⟨v7, hv7⟩⟩ := hO6
  exact h v1 v2 v3 v4 v5 v6 v7 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP0, g2, g3, d2, u2, hv1,
       g4, g5, d3, u3, hv2, g6, g7, d4, u4, hv3,
       g8, g9, d5, u5, hv4, g10, g11, d6, u6, hv5,
       g12, g13, d7, u7, hv6, hv7⟩, hRb⟩ hpc

theorem initializedToJoin (newSp listBase listLenW outPtr oldCount : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen : Nat)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (h_listLenW : listLenW = BitVec.ofNat 64 listLen)
    (h_align : listBase.toNat % 8 = 0)
    (h_slack : listLen + 9 ≤ bytes.length)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64)
    (h_valid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (85 + (93 * (listLen + 1) + 3)) (B + 32) (B + 92) code
      (((.x1 ↦ᵣ saved.ra) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) **
         (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion listBase bytes)) **
       initStable newSp listBase outPtr oldCount saved)
      (joined newSp listBase outPtr saved bytes listLen) := by
  have hi := initCallDispatchExact newSp listBase listLenW outPtr oldCount saved
    bytes listLen v5 v6 v7 v28 v29 v30 v31 h_listLenW h_align h_slack h_over
    h_valid
  exact cpsNBranchWithin_merge hi (fun ex hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hloop | hreject
    · subst ex
      exact scanAndTails newSp listBase outPtr oldCount saved bytes listLen
        h_align h_slack h_over h_valid
    · subst ex
      exact cpsTripleWithin_mono_nSteps (by omega)
        (failureTail newSp listBase outPtr oldCount saved bytes listLen))

theorem bodyToFinal (sp0 newSp listBase listLenW outPtr oldCount : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen : Nat)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (h_listLenW : listLenW = BitVec.ofNat 64 listLen)
    (h_align : listBase.toNat % 8 = 0)
    (h_slack : listLen + 9 ≤ bytes.length)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64)
    (h_valid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_newSp : newSp = sp0 + signExtend12 (-48 : BitVec 12))
    (h_ret : saved.ra &&& ~~~(1 : Word) = saved.ra) :
    cpsTripleWithin (85 + (93 * (listLen + 1) + 3) + 7)
      (B + 32) saved.ra code
      (((.x1 ↦ᵣ saved.ra) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) **
         (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion listBase bytes)) **
       initStable newSp listBase outPtr oldCount saved)
      (finalResult sp0 newSp listBase outPtr saved bytes listLen) := by
  exact cpsTripleWithin_seq_same_cr
    (initializedToJoin newSp listBase listLenW outPtr oldCount saved bytes listLen
      v5 v6 v7 v28 v29 v30 v31 h_listLenW h_align h_slack h_over h_valid)
    (joinToFinal sp0 newSp listBase outPtr saved bytes listLen h_newSp h_ret)

theorem bodyToFinalOwned (sp0 newSp listBase listLenW outPtr oldCount : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen : Nat)
    (h_listLenW : listLenW = BitVec.ofNat 64 listLen)
    (h_align : listBase.toNat % 8 = 0)
    (h_slack : listLen + 9 ≤ bytes.length)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64)
    (h_valid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_newSp : newSp = sp0 + signExtend12 (-48 : BitVec 12))
    (h_ret : saved.ra &&& ~~~(1 : Word) = saved.ra) :
    cpsTripleWithin (85 + (93 * (listLen + 1) + 3) + 7)
      (B + 32) saved.ra code
      (((.x1 ↦ᵣ saved.ra) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) **
         (.x12 ↦ᵣ outPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes)) **
       initStable newSp listBase outPtr oldCount saved)
      (finalResult sp0 newSp listBase outPtr saved bytes listLen) := by
  let P : Assertion :=
    ((.x1 ↦ᵣ saved.ra) ** (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) **
     (.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
     initStable newSp listBase outPtr oldCount saved)
  have hb : cpsTripleWithin (85 + (93 * (listLen + 1) + 3) + 7)
      (B + 32) saved.ra code
      (P ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (finalResult sp0 newSp listBase outPtr saved bytes listLen) :=
    cpsTripleWithin_of_forall_regIs_to_regOwn7
      (fun v5 v6 v7 v28 v29 v30 v31 =>
        cpsTripleWithin_weaken (fun h hp => by
          unfold P at hp
          xperm_hyp hp) (fun _ hp => hp)
          (bodyToFinal sp0 newSp listBase listLenW outPtr oldCount saved bytes
            listLen v5 v6 v7 v28 v29 v30 v31 h_listLenW h_align h_slack h_over
            h_valid h_newSp h_ret))
  exact cpsTripleWithin_weaken (fun h hp => by
    unfold P
    xperm_hyp hp) (fun _ hp => hp) hb

/-- Complete strict `rlp_list_count_items` ABI theorem.  Every assumption is
    static; success versus malformed input is returned only through `Result`. -/
theorem rlp_list_count_items_spec_within
    (sp0 newSp listBase listLenW outPtr oldCount : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen : Nat)
    (h_listLenW : listLenW = BitVec.ofNat 64 listLen)
    (h_align : listBase.toNat % 8 = 0)
    (h_slack : listLen + 9 ≤ bytes.length)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64)
    (h_valid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_newSp : newSp = sp0 + signExtend12 (-48 : BitVec 12))
    (h_ret : saved.ra &&& ~~~(1 : Word) = saved.ra) :
    cpsTripleWithin (8 + (85 + (93 * (listLen + 1) + 3) + 7))
      B saved.ra code
      ((.x2 ↦ᵣ sp0) ** regsAt countFrame (savedVals saved) **
       frameSlotsOwn countFrame newSp **
       entryRest listBase listLenW outPtr oldCount bytes)
      (finalResult sp0 newSp listBase outPtr saved bytes listLen) := by
  have hp := wrapperPrologue sp0 newSp listBase listLenW outPtr oldCount saved bytes
    h_newSp
  have hb := bodyToFinalOwned sp0 newSp listBase listLenW outPtr oldCount saved
    bytes listLen h_listLenW h_align h_slack h_over h_valid h_newSp h_ret
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp0 => by
    unfold setupPost entryRest at hp0
    unfold initStable
    xperm_hyp hp0) hp hb


end EvmAsm.Codegen.RlpListCountItemsSAsm
