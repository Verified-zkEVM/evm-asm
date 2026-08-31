/-
  K146 prefix-and-copy composition.

  `TxSigningHashLegacyPrefixCompose` reaches the copy-loop entry at H+296.
  This module feeds that postcondition to the deployed five-instruction copy
  loop and records the caller-owned destination slice explicitly.  The prefix
  output is a slice of `t155_buf`; the copy destination is the disjoint slice
  beginning 64 bytes later, so the small prefix-region bound is part of this
  caller-side geometry rather than an assertion about the transaction.
-/

import EvmAsm.Codegen.Programs.TxSigningHashLegacyPrefixCompose

namespace EvmAsm.Codegen.TxSigningHashLegacyPrefixCopyCompose

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.RlpEncodeUintBeSAsm
open EvmAsm.Codegen.SgMemcpySAsm
open EvmAsm.Codegen.TxSigningHashLegacySpec
open EvmAsm.Codegen.TxSigningHashLegacyCompose
open EvmAsm.Codegen.TxSigningHashLegacyCopySpec
open EvmAsm.Codegen.TxSigningHashLegacyLoopSpec
open EvmAsm.Codegen.TxSigningHashLegacyUintCompose
open EvmAsm.Codegen.TxSigningHashLegacyPrefixCompose
open EvmAsm.Codegen.TxSigningHashSpec
open EvmAsm.EL.RLP

def legacyPrefixCopyPost
    (chainId v21 : Word) (outBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  let n := (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length
  let chainLen : Word := BitVec.ofNat 64 n
  let payloadLen : Word := v21 + (chainLen + 2)
  let encOld : List (BitVec 8) :=
    RlpEncodeUintBeSAsm.reubOut (chainBytes chainId) ++
      legacyChainEncOld.drop n
  ((.x1 : Reg) ↦ᵣ (legacyPrefixJalPC + 4)) **
    ((.x10 : Reg) ↦ᵣ (0 : Word)) **
    ((.x11 : Reg) ↦ᵣ legacyPrefixOutPtr) **
    ((.x12 : Reg) ↦ᵣ legacyPrefixCellPtr) **
    ((.x7 : Reg) ↦ᵣ chainLen) **
    ((.x5 : Reg) ↦ᵣ
      (legacySuffixOutPtr + BitVec.ofNat 64 n)) **
    ((.x6 : Reg) ↦ᵣ
      (legacySuffixChainEncPtr + BitVec.ofNat 64 n)) **
    ((.x28 : Reg) ↦ᵣ (0 : Word)) **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    ((.x21 : Reg) ↦ᵣ v21) ** ((.x22 : Reg) ↦ᵣ payloadLen) **
    ((.x18 : Reg) ↦ᵣ chainId) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
    bytesRegion legacyLinkedChainEncPtr encOld **
    bytesRegion legacyPrefixOutPtr
      (tshPrefixApply outBytes payloadLen.toNat) **
    (legacyPrefixCellPtr ↦ₘ BitVec.ofNat 64
      (tshPrefixNH payloadLen.toNat)) **
    bytesRegion legacySuffixOutPtr (encOld.take n) ** F

/-! The K146 copy loop, composed from the prefix setup and its linked body. -/
theorem legacyPrefixSetupCopy_spec
    (chainId v21 : Word) (outBytes : List (BitVec 8)) (cellOld : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_out_len : 8 < outBytes.length)
    (h_out_end : outBytes.length ≤ 64)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (legacyPrefixOutPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin
      (8 + (1 + tshPrefixFuel) + 8 +
        ((RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length * (6 + 1) + 1))
      (legacyH + 228) (legacyH + 324) legacyFullCode
      (legacyChainUintPost chainId
          (bytesRegion legacyPrefixOutPtr outBytes **
            (legacyPrefixCellPtr ↦ₘ cellOld) **
            bytesRegion legacySuffixOutPtr
              (List.replicate
                (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length 0) ** F) **
        ((.x21 : Reg) ↦ᵣ v21) ** regOwn .x22)
      (legacyPrefixCopyPost chainId v21 outBytes F) := by
  let n : Nat := (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length
  let chainLen : Word := BitVec.ofNat 64 n
  let payloadLen : Word := v21 + (chainLen + 2)
  let encOld : List (BitVec 8) :=
    RlpEncodeUintBeSAsm.reubOut (chainBytes chainId) ++
      legacyChainEncOld.drop n
  let dstOld : List (BitVec 8) := List.replicate n (0 : BitVec 8)
  have hn_le : n ≤ 9 := by
    dsimp [n]
    have h := reubOut_length_le (chainBytes chainId) (by
      rw [chainBytes_length]
      decide)
    rw [chainBytes_length] at h
    omega
  have hn_src : n ≤ encOld.length := by
    dsimp [encOld]
    simp only [List.length_append, List.length_drop]
    omega
  have hn_bound : n < 18446744073709551616 := by omega
  have hs_over : legacySuffixChainEncPtr.toNat + n < 2 ^ 64 := by
    have h : legacySuffixChainEncPtr.toNat + 9 < 2 ^ 64 := by decide
    omega
  have hd_over : legacySuffixOutPtr.toNat + n < 2 ^ 64 := by
    have h : legacySuffixOutPtr.toNat + 9 < 2 ^ 64 := by decide
    omega
  have hs_valid : ∀ i, i < n →
      isValidByteAccess (legacySuffixChainEncPtr + BitVec.ofNat 64 i) = true := by
    intro i hi
    have hi8 : i ≤ 8 := by omega
    interval_cases i <;> decide
  have hd_valid : ∀ i, i < n →
      isValidByteAccess (legacySuffixOutPtr + BitVec.ofNat 64 i) = true := by
    intro i hi
    have hi8 : i ≤ 8 := by omega
    interval_cases i <;> decide
  have hwin : copyWin encOld dstOld n = encOld.take n := by
    apply copyWin_len_eq encOld dstOld n
    · simp [dstOld]
    · exact hn_src
  have hzero : (BitVec.ofNat 64 0 : Word) = 0 := by rfl
  have hdst_zero : legacySuffixOutPtr + (0 : Word) = legacySuffixOutPtr := by
    simp
  have hsrc_zero : legacySuffixChainEncPtr + (0 : Word) = legacySuffixChainEncPtr := by
    simp
  let Fcopy : Assertion := bytesRegion legacySuffixOutPtr dstOld ** F
  have hFcopy : Fcopy.pcFree := by
    have h_prefix_region_bound : outBytes.length ≤ 64 := h_out_end
    dsimp [Fcopy]
    pcf
    exact hF
  have hprefix := legacyPrefixSetupSuffix_spec chainId v21 outBytes cellOld
    Fcopy hFcopy h_out_len h_out_valid
  have hcopy := legacyCopy_callWithin
    legacySuffixChainEncPtr legacySuffixOutPtr n encOld dstOld
    (by simp [dstOld])
    (by decide) (by decide) hn_src hs_over hd_over hs_valid hd_valid hn_bound
  have hcopy' : cpsTripleWithin (n * (6 + 1) + 1)
      (legacyH + 296) (legacyH + 324) legacyFullCode
      (((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        copyInvCore legacySuffixChainEncPtr legacySuffixOutPtr n encOld dstOld n)
      (((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 0) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        copyInvCore legacySuffixChainEncPtr legacySuffixOutPtr n encOld dstOld 0) := by
    have hpc : legacyCopyBase + 28 = legacyH + 324 := by decide
    rw [hpc] at hcopy
    exact hcopy
  let Frest : Assertion :=
    ((.x1 : Reg) ↦ᵣ (legacyPrefixJalPC + 4)) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) **
      ((.x11 : Reg) ↦ᵣ legacyPrefixOutPtr) **
      ((.x12 : Reg) ↦ᵣ legacyPrefixCellPtr) **
      ((.x7 : Reg) ↦ᵣ chainLen) **
      regOwn .x29 ** regOwn .x30 **
      ((.x21 : Reg) ↦ᵣ v21) ** ((.x22 : Reg) ↦ᵣ payloadLen) **
      ((.x18 : Reg) ↦ᵣ chainId) **
      bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
      bytesRegion legacyPrefixOutPtr
        (tshPrefixApply outBytes payloadLen.toNat) **
      (legacyPrefixCellPtr ↦ₘ BitVec.ofNat 64
        (tshPrefixNH payloadLen.toNat)) ** F
  have hFrest : Frest.pcFree := by
    dsimp [Frest]
    pcf
    exact hF
  have hcopyF := cpsTripleWithin_frameR Frest hFrest hcopy'
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [legacyPrefixSuffixPost, Fcopy, Frest, copyInvCore,
        dstOld, encOld, chainLen, payloadLen, n, Nat.sub_self, hzero,
        hdst_zero, hsrc_zero, copyWin_zero] at hp ⊢
      xperm_hyp hp)
    hprefix hcopyF
  have hresult :
      cpsTripleWithin
        (8 + (1 + tshPrefixFuel) + 8 + (n * (6 + 1) + 1))
        (legacyH + 228) (legacyH + 324) legacyFullCode
        (legacyChainUintPost chainId
            (bytesRegion legacyPrefixOutPtr outBytes **
              (legacyPrefixCellPtr ↦ₘ cellOld) ** Fcopy) **
          ((.x21 : Reg) ↦ᵣ v21) ** regOwn .x22)
        (legacyPrefixCopyPost chainId v21 outBytes F) :=
    cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hq => by
      simp only [legacyPrefixCopyPost, Frest,
        copyInvCore, dstOld, encOld, chainLen, payloadLen, n, Nat.sub_zero, hzero] at hq ⊢
      rw [hwin] at hq
      xperm_hyp hq)
    hseq
  simpa [n, Fcopy, dstOld] using hresult

/-! A concrete, joint inhabitant for the composed precondition.  This is kept
    beside the composition rather than inferred from the individual callee
    premises: the chain, prefix, cell, and copy-slice resources all coexist in
    one partial state, and the prefix slice is deliberately nonempty. -/

private structure PrefixSatMem where
  a : Word
  v : Word
  valid : isValidDwordAccess a = true

private inductive PrefixSatAtom where
  | reg (r : Reg) (v : Word)
  | ownReg (r : Reg)
  | mem (m : PrefixSatMem)

private def prefixSatAtomAssertion : PrefixSatAtom → Assertion
  | .reg r v => r ↦ᵣ v
  | .ownReg r => regOwn r
  | .mem m => m.a ↦ₘ m.v

private def prefixSatAtomHeap : PrefixSatAtom → PartialState
  | .reg r v => PartialState.singletonReg r v
  | .ownReg r => PartialState.singletonReg r 0
  | .mem m => PartialState.singletonMem m.a m.v

private inductive PrefixSatResource where
  | reg (r : Reg)
  | mem (a : Word)
  deriving DecidableEq

private def prefixSatResource : PrefixSatAtom → PrefixSatResource
  | .reg r _ => .reg r
  | .ownReg r => .reg r
  | .mem m => .mem m.a

private theorem prefixSat_reg_reg_disjoint
    {r1 r2 : Reg} {v1 v2 : Word} (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint
      (PartialState.singletonReg r2 v2) := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r
  by_cases h : r = r1
  · subst r
    right
    simp [PartialState.singletonReg, hne]
  · left
    simp [PartialState.singletonReg, h]

private theorem prefixSat_mem_mem_disjoint
    {a1 a2 : Word} {v1 v2 : Word} (hne : a1 ≠ a2) :
    (PartialState.singletonMem a1 v1).Disjoint
      (PartialState.singletonMem a2 v2) := by
  refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro a
  by_cases h : a = a1
  · subst a
    right
    simp [PartialState.singletonMem, hne]
  · left
    simp [PartialState.singletonMem, h]

private theorem prefixSat_reg_mem_disjoint
    {r : Reg} {a v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem prefixSat_mem_reg_disjoint
    {r : Reg} {a v w : Word} :
    (PartialState.singletonMem a v).Disjoint
      (PartialState.singletonReg r w) :=
  prefixSat_reg_mem_disjoint.symm

private theorem prefixSat_heap_disjoint_of_resource_ne
    {x y : PrefixSatAtom}
    (h : prefixSatResource x ≠ prefixSatResource y) :
    (prefixSatAtomHeap x).Disjoint (prefixSatAtomHeap y) := by
  cases x <;> cases y
  · apply prefixSat_reg_reg_disjoint
    simpa [prefixSatResource] using h
  · apply prefixSat_reg_reg_disjoint
    simpa [prefixSatResource] using h
  · exact prefixSat_reg_mem_disjoint
  · apply prefixSat_reg_reg_disjoint
    simpa [prefixSatResource] using h
  · apply prefixSat_reg_reg_disjoint
    simpa [prefixSatResource] using h
  · exact prefixSat_reg_mem_disjoint
  · exact prefixSat_mem_reg_disjoint
  · exact prefixSat_mem_reg_disjoint
  · apply prefixSat_mem_mem_disjoint
    simpa [prefixSatResource] using h

private def prefixSatChainId : Word := 1
private def prefixSatOutBytes : List (BitVec 8) := List.replicate 16 0
private def prefixSatChainLen : Word := BitVec.ofNat 64 1
private def prefixSatEncBytes : List (BitVec 8) :=
  RlpEncodeUintBeSAsm.reubOut (chainBytes prefixSatChainId) ++
    legacyChainEncOld.drop 1
private def prefixSatSuffixBytes : List (BitVec 8) := List.replicate 1 0

private def prefixSatAtoms : List PrefixSatAtom :=
  [ .reg .x1 (legacyUintJalPC + 4)
  , .reg .x10 prefixSatChainLen
  , .reg .x11 (8 : Word)
  , .ownReg .x5
  , .ownReg .x6
  , .ownReg .x7
  , .ownReg .x28
  , .ownReg .x29
  , .ownReg .x30
  , .ownReg .x31
  , .reg .x18 prefixSatChainId
  , .reg .x12 legacyLinkedChainEncPtr
  , .reg .x0 (0 : Word)
  , .mem ⟨legacyLinkedChainPtr,
      packBytes (chainBytes prefixSatChainId), by decide⟩
  , .mem ⟨legacyLinkedChainEncPtr,
      packBytes (prefixSatEncBytes.take 8), by decide⟩
  , .mem ⟨legacyLinkedChainEncPtr + 8,
      packBytes ((prefixSatEncBytes.drop 8).take 8), by decide⟩
  , .mem ⟨legacyPrefixOutPtr,
      packBytes (prefixSatOutBytes.take 8), by decide⟩
  , .mem ⟨legacyPrefixOutPtr + 8,
      packBytes ((prefixSatOutBytes.drop 8).take 8), by decide⟩
  , .mem ⟨legacyPrefixCellPtr, (0 : Word), by decide⟩
  , .mem ⟨legacySuffixOutPtr,
      packBytes (prefixSatSuffixBytes.take 8), by decide⟩
  , .reg .x21 (0 : Word)
  , .ownReg .x22
  ]

private theorem prefixSatAtoms_resource_pairwise :
    prefixSatAtoms.Pairwise
      (fun x y => prefixSatResource x ≠ prefixSatResource y) := by
  unfold prefixSatAtoms prefixSatResource prefixSatChainId
    prefixSatChainLen prefixSatEncBytes
    prefixSatSuffixBytes prefixSatOutBytes
  decide

private def prefixSatHeapFold : PartialState :=
  prefixSatAtoms.foldr
    (fun x acc => (prefixSatAtomHeap x).union acc) PartialState.empty

private theorem prefixSat_hsat :
    (prefixSatAtoms.foldr
      (fun x acc => prefixSatAtomAssertion x ** acc) empAssertion)
      prefixSatHeapFold := by
  apply sepConj_foldr_satisfiable
    prefixSatAtomAssertion prefixSatAtomHeap prefixSatAtoms
  · intro x hx
    cases x with
    | reg r v => exact rfl
    | ownReg r => exact ⟨0, rfl⟩
    | mem m => exact ⟨rfl, m.valid⟩
  · exact List.Pairwise.imp
      (fun {_ _} h => prefixSat_heap_disjoint_of_resource_ne h)
      prefixSatAtoms_resource_pairwise

theorem legacyPrefixSetupCopy_pre_inhabited :
    ∃ h : PartialState,
      (legacyChainUintPost prefixSatChainId
          (bytesRegion legacyPrefixOutPtr prefixSatOutBytes **
            (legacyPrefixCellPtr ↦ₘ (0 : Word)) **
            bytesRegion legacySuffixOutPtr prefixSatSuffixBytes **
            empAssertion) **
        ((.x21 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x22) h := by
  refine ⟨prefixSatHeapFold, ?_⟩
  convert prefixSat_hsat using 1
  simp [legacyChainUintPost, prefixSatHeapFold, prefixSatAtoms,
    prefixSatAtomAssertion, prefixSatAtomHeap, prefixSatChainId,
    prefixSatChainLen, prefixSatEncBytes, prefixSatSuffixBytes,
    prefixSatOutBytes,
    legacyChainEncOld,
    bytesRegion, bytesRegionAux, packBytes, getByteAt, packDword,
    chainBytes, RlpEncodeUintBeSAsm.reubOut,
    RlpEncodeUintBeSAsm.reubStrip, encodeBytes,
    sepConj_emp_right', sepConj_assoc']

end EvmAsm.Codegen.TxSigningHashLegacyPrefixCopyCompose
