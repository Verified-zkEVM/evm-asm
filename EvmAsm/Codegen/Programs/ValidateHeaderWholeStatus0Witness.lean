/-
  Status-0 producer witness split from ValidateHeaderWholeWitness.
-/
import EvmAsm.Codegen.Programs.ValidateHeaderWholeWitness
import EvmAsm.Rv64.MemSat
import Batteries.Tactic.OpenPrivate
set_option maxRecDepth 8000
namespace EvmAsm.Codegen.ValidateHeaderWhole
open EvmAsm
open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.ValidateHeaderCompose
open EvmAsm.Codegen.ValidateHeaderInlineArms
open private numericFieldsOk bytesFieldsOk checkNumericFields decodeHeaderArm rlpBytes?
  getNChecked getBChecked from
  EvmAsm.Stateless.SpecRef.Stateless
-- `scalarItem` is no longer `private`: the exposed public body of
-- `headerToRlpItem` references it, and a public body may not mention a
-- private declaration. Plain `open` reaches it now.
open EvmAsm.Stateless.SpecRef (scalarItem)
open private hcoreHeaderRlp_length hcoreParentRlp_length hcoreParent_decodeHeader hcoreStatus0Assertion hcoreStatus0Assertion_eq_bytes hcoreStatus0HeaderRlp_length hcoreStatus0HeaderStruct_length hcoreStatus0HeaderStruct_relation hcoreStatus0Heap hcoreStatus0Heap_mem_outside hcoreStatus0MemAtom hcoreStatus0MemFold hcoreStatus0MemFold_eq hcoreStatus0MemFold_mem_of_ne_none hcoreStatus0MemFold_sat hcoreStatus0MemHeap hcoreStatus0MemHeapFold hcoreStatus0Sat hcoreStatus0StackFold hcoreStatus0StackMems hcoreStatus0_decodeHeader hcoreStatus0_validate_header hcoreWitnessAssertion hcoreWitnessAssertion_eq hcoreWitnessGRegion hcoreWitnessHeap hcoreWitnessHeap_mem_outside hcoreWitnessParentStruct_relation hcoreWitnessRegAtom hcoreWitnessRegFold hcoreWitnessRlpSat hcoreWitnessSat hcoreWitnessStackFold hcoreWitnessStackMems hcore_decodeHeaderArm_ok from
  EvmAsm.Codegen.Programs.ValidateHeaderWholeWitness
private theorem hcoreStatus0RlpSat :
    (bytesRegion hcoreWitnessHeader hcoreStatus0HeaderRlp).SatWithin
        131072 131720 ∧
      (bytesRegion hcoreWitnessParentRlp hcoreWitnessParentRlpBytes).SatWithin
        204800 205448 := by
  have hlen : hcoreStatus0HeaderRlp.length = 645 := hcoreStatus0HeaderRlp_length
  have hvalidHeader (k : Nat) (hk : k < 81) :
      isValidDwordAccess (hcoreWitnessHeader + BitVec.ofNat 64 (8 * k)) = true := by
    have hbase : hcoreWitnessHeader.toNat = 131072 := by rfl
    have hto :
        (hcoreWitnessHeader + BitVec.ofNat 64 (8 * k)).toNat =
          hcoreWitnessHeader.toNat + 8 * k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have hk64 : 8 * k < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hk64]
      have hsum : hcoreWitnessHeader.toNat + 8 * k < 2 ^ 64 := by
        rw [hbase]
        omega
      rw [Nat.mod_eq_of_lt hsum]
    apply isValidDwordAccess_of_toNat
    · rw [hto, hbase]
      omega
    · left
      constructor <;> rw [hto, hbase] <;> omega
  have h1 := satWithin_bytesRegion hcoreWitnessHeader hcoreStatus0HeaderRlp
    (fun k hk => by
      rw [hlen] at hk
      have hk81 : k < 81 := by omega
      exact hvalidHeader k hk81)
  have h1' :
      (bytesRegion hcoreWitnessHeader hcoreStatus0HeaderRlp).SatWithin
        131072 131720 := by
    simpa [hcoreWitnessHeader, hlen] using h1
  exact ⟨h1', hcoreWitnessRlpSat.2⟩

private theorem hcoreStatus0HeaderStructSat :
    (bytesRegion hcoreWitnessParent hcoreStatus0HeaderStruct).SatWithin
      196608 196752 := by
  have hlen : hcoreStatus0HeaderStruct.length = 144 :=
    hcoreStatus0HeaderStruct_length
  have hvalid (k : Nat) (hk : k < (hcoreStatus0HeaderStruct.length + 7) / 8) :
      isValidDwordAccess
        (hcoreWitnessParent + BitVec.ofNat 64 (8 * k)) = true := by
    have hk18 : k < 18 := by
      rw [hlen] at hk
      omega
    have hbase : hcoreWitnessParent.toNat = 196608 := by rfl
    have hto :
        (hcoreWitnessParent + BitVec.ofNat 64 (8 * k)).toNat =
          hcoreWitnessParent.toNat + 8 * k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have hk64 : 8 * k < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hk64]
      have hsum : hcoreWitnessParent.toNat + 8 * k < 2 ^ 64 := by
        rw [hbase]
        omega
      rw [Nat.mod_eq_of_lt hsum]
    apply isValidDwordAccess_of_toNat
    · rw [hto, hbase]
      omega
    · left
      constructor <;> rw [hto, hbase] <;> omega
  have h := satWithin_bytesRegion hcoreWitnessParent hcoreStatus0HeaderStruct hvalid
  simpa [hcoreWitnessParent, hlen] using h

private theorem hcoreWitnessParentStructSat :
    (bytesRegion hcoreWitnessParent2 hcoreWitnessParentStruct).SatWithin
      200704 200848 := by
  have hlen : hcoreWitnessParentStruct.length = 144 := by
    have hp : hcoreWitnessParentSpec.parentHash.length = 32 := by
      simp [hcoreWitnessParentSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
    have hs : hcoreWitnessParentSpec.stateRoot.length = 32 := by
      simp [hcoreWitnessParentSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
    simp [hcoreWitnessParentStruct, headerCoreStructBytes, hp, hs,
      EvmAsm.Stateless.SpecRef.natToBytesBE_length,
      EvmAsm.Stateless.SpecRef.natToBytesLE_length]
  have hvalid (k : Nat) (hk : k < (hcoreWitnessParentStruct.length + 7) / 8) :
      isValidDwordAccess
        (hcoreWitnessParent2 + BitVec.ofNat 64 (8 * k)) = true := by
    have hk18 : k < 18 := by
      rw [hlen] at hk
      omega
    have hbase : hcoreWitnessParent2.toNat = 200704 := by rfl
    have hto :
        (hcoreWitnessParent2 + BitVec.ofNat 64 (8 * k)).toNat =
          hcoreWitnessParent2.toNat + 8 * k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have hk64 : 8 * k < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hk64]
      have hsum : hcoreWitnessParent2.toNat + 8 * k < 2 ^ 64 := by
        rw [hbase]
        omega
      rw [Nat.mod_eq_of_lt hsum]
    apply isValidDwordAccess_of_toNat
    · rw [hto, hbase]
      omega
    · left
      constructor <;> rw [hto, hbase] <;> omega
  have h := satWithin_bytesRegion hcoreWitnessParent2 hcoreWitnessParentStruct hvalid
  simpa [hcoreWitnessParent2, hlen] using h

private theorem validateHeaderCoreStatus0Pre_nonempty_G :
    ∃ h : PartialState,
      validateHeaderCorePre hcoreWitnessParentSpec hcoreStatus0HeaderSpec
        hcoreWitnessSpC 0 hcoreWitnessHeader hcoreStatus0HeaderRlp.length
        hcoreStatus0HeaderRlp hcoreWitnessParentRlpBytes
        hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
        hcoreWitnessParentRlpBytes.length
        hcoreStatus0HeaderStruct hcoreWitnessParentStruct
        hcoreWitnessHeader hcoreStatus0HeaderRlp.length hcoreWitnessParent hcoreWitnessParent2
        hcoreWitnessParentRlp hcoreWitnessParentRlpBytes.length
        (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) h := by
  obtain ⟨h1sat, h2sat⟩ := hcoreStatus0RlpSat
  obtain ⟨h1, h1sat, h1within⟩ := h1sat
  obtain ⟨h2, h2sat, h2within⟩ := h2sat
  have h12disj : h1.Disjoint h2 := by
    refine ⟨fun _ => Or.inl (h1within.regs _), ?_,
      fun _ => Or.inl (h1within.code _), Or.inl h1within.pc,
      Or.inl h1within.publicValues, Or.inl h1within.privateInput,
      Or.inl h1within.inputBufBase⟩
    intro a
    by_cases h1none : h1.mem a = none
    · exact Or.inl h1none
    by_cases h2none : h2.mem a = none
    · exact Or.inr h2none
    have hin1 := h1within.mem a h1none
    have hin2 := h2within.mem a h2none
    omega
  have hrawsat :
      (bytesRegion hcoreWitnessHeader hcoreStatus0HeaderRlp **
        bytesRegion hcoreWitnessParentRlp hcoreWitnessParentRlpBytes)
        (h1.union h2) :=
    ⟨h1, h2, h12disj, rfl, h1sat, h2sat⟩
  have hdisj : hcoreStatus0Heap.Disjoint (h1.union h2) := by
    refine ⟨fun _ => Or.inr (by simp [PartialState.union,
          h1within.regs, h2within.regs]), ?_,
      fun _ => Or.inr (by simp [PartialState.union,
          h1within.code, h2within.code]),
      Or.inr (by simp [PartialState.union, h1within.pc, h2within.pc]),
      Or.inr (by simp [PartialState.union,
          h1within.publicValues, h2within.publicValues]), Or.inr (by simp [PartialState.union,
          h1within.privateInput, h2within.privateInput]), Or.inr (by simp [PartialState.union,
          h1within.inputBufBase, h2within.inputBufBase])⟩
    intro a
    by_cases hold : hcoreStatus0Heap.mem a = none
    · exact Or.inl hold
    by_cases h1none : h1.mem a = none
    · by_cases h2none : h2.mem a = none
      · exact Or.inr (by simp [PartialState.union, h1none, h2none])
      · have hout := hcoreStatus0Heap_mem_outside a hold
        have hin2 := h2within.mem a h2none
        omega
    · have hout := hcoreStatus0Heap_mem_outside a hold
      have hin1 := h1within.mem a h1none
      omega
  have hbase := show
      (hcoreStatus0Assertion **
        (bytesRegion hcoreWitnessHeader hcoreStatus0HeaderRlp **
          bytesRegion hcoreWitnessParentRlp hcoreWitnessParentRlpBytes))
        (hcoreStatus0Heap.union (h1.union h2)) from
    ⟨hcoreStatus0Heap, h1.union h2, hdisj, rfl, hcoreStatus0Sat, hrawsat⟩
  have hall :
      hcoreStatus0HeaderRlp.length = hcoreStatus0HeaderRlp.length ∧
      hcoreWitnessParentRlpBytes.length = hcoreWitnessParentRlpBytes.length ∧
      EvmAsm.Stateless.SpecRef._decode_header hcoreStatus0HeaderRlp =
        .ok hcoreStatus0HeaderSpec ∧
      EvmAsm.Stateless.SpecRef._decode_header hcoreWitnessParentRlpBytes =
        .ok hcoreWitnessParentSpec ∧
      headerCoreStructRelation hcoreStatus0HeaderStruct hcoreStatus0HeaderSpec ∧
      headerCoreStructRelation hcoreWitnessParentStruct hcoreWitnessParentSpec :=
    ⟨rfl, rfl, hcoreStatus0_decodeHeader, hcoreParent_decodeHeader,
      hcoreStatus0HeaderStruct_relation, hcoreWitnessParentStruct_relation⟩
  have h := (sepConj_pure_right _).2 ⟨hbase, hall⟩
  rw [hcoreStatus0Assertion_eq_bytes] at h
  refine ⟨hcoreStatus0Heap.union (h1.union h2), ?_⟩
  have hlenStatus : hcoreStatus0HeaderRlp.length = hcoreWitnessHeaderRlp.length := by
    rw [hcoreStatus0HeaderRlp_length, hcoreHeaderRlp_length]
  rw [hlenStatus] at h ⊢
  simp [hcoreWitnessRegFold, hcoreWitnessRegAtom, hcoreWitnessRegs,
    hcoreStatus0StackFold, hcoreStatus0StackMems,
    hcoreWitnessSpC, hcoreStatus0HeaderRlp_length, hcoreHeaderRlp_length,
    hcoreParentRlp_length, sepConj_emp_right', sepConj_assoc'] at h
  simp [validateHeaderCorePre, validateHeaderCoreFrame,
    hcoreWitnessSpC, hcoreWitnessHeader, hcoreWitnessParent,
    sepConj_assoc'] at h ⊢
  simp [hcoreStatus0HeaderRlp_length, hcoreHeaderRlp_length,
    hcoreParentRlp_length] at h ⊢
  xperm_hyp h

private def hcoreStatus0PostRegs : List (Reg × Word) :=
  [(.x10, 0), (.x2, hcoreWitnessSpC), (.x1, 0),
   (.x8, hcoreWitnessHeader),
   (.x9, BitVec.ofNat 64 hcoreStatus0HeaderRlp.length),
   (.x18, hcoreWitnessParent), (.x19, hcoreWitnessParent2),
   (.x20, hcoreWitnessParentRlp),
   (.x21, BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)]

private def hcoreStatus0PostRegHeap : (Reg × Word) → PartialState :=
  fun p => PartialState.singletonReg p.1 p.2

private def hcoreStatus0PostRegAtom : (Reg × Word) → Assertion :=
  fun p => p.1 ↦ᵣ p.2

private def hcoreStatus0PostRegFold : Assertion :=
  hcoreStatus0PostRegs.foldr
    (fun p acc => hcoreStatus0PostRegAtom p ** acc) empAssertion

private def hcoreStatus0PostRegHeapFold : PartialState :=
  hcoreStatus0PostRegs.foldr
    (fun p acc => (hcoreStatus0PostRegHeap p).union acc) PartialState.empty

private theorem hcoreStatus0PostRegFold_sat :
    hcoreStatus0PostRegFold hcoreStatus0PostRegHeapFold := by
  apply sepConj_foldr_satisfiable hcoreStatus0PostRegAtom
    hcoreStatus0PostRegHeap hcoreStatus0PostRegs
  · intro p hp
    rfl
  · have hd : hcoreStatus0PostRegs.Pairwise (fun p q => p.1 ≠ q.1) := by
      decide
    exact List.Pairwise.imp
      (fun {_ _} h =>
        EvmAsm.Codegen.ValidateHeaderCompose.routeInhabitantRegSingletonDisjoint h)
      hd

private theorem hcoreStatus0PostFold_cross :
    ∀ p ∈ hcoreStatus0PostRegs, ∀ q ∈ hcoreStatus0Mems,
      (hcoreStatus0PostRegHeap p).Disjoint (hcoreStatus0MemHeap q) := by
  intro p hp q hq
  unfold hcoreStatus0PostRegHeap hcoreStatus0MemHeap
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private def hcoreStatus0PostBaseAssertion : Assertion :=
  hcoreStatus0PostRegFold ** hcoreStatus0MemFold

private def hcoreStatus0PostBaseHeap : PartialState :=
  hcoreStatus0PostRegHeapFold.union hcoreStatus0MemHeapFold

private theorem hcoreStatus0PostBaseSat :
    hcoreStatus0PostBaseAssertion hcoreStatus0PostBaseHeap := by
  exact sepConj_foldr_cross_satisfiable hcoreStatus0PostRegAtom
    hcoreStatus0PostRegHeap hcoreStatus0PostRegs hcoreStatus0MemAtom
    hcoreStatus0MemHeap hcoreStatus0Mems hcoreStatus0PostRegFold_sat
    hcoreStatus0MemFold_sat hcoreStatus0PostFold_cross

private theorem hcoreStatus0PostAssertion_eq :
    hcoreStatus0PostBaseAssertion =
      (hcoreStatus0PostRegFold **
        (hcoreStatus0StackFold **
          (bytesRegion hcoreWitnessParent hcoreStatus0HeaderStruct **
            (bytesRegion hcoreWitnessParent2 hcoreWitnessParentStruct **
              (hcoreWitnessGAddr ↦ₘ packBytes hcoreWitnessGBytes))))) := by
  simp only [hcoreStatus0PostBaseAssertion, hcoreStatus0MemFold_eq]

private theorem hcoreStatus0PostAssertion_eq_bytes :
    hcoreStatus0PostBaseAssertion =
      (hcoreStatus0PostRegFold **
        (hcoreStatus0StackFold **
          (bytesRegion hcoreWitnessParent hcoreStatus0HeaderStruct **
            (bytesRegion hcoreWitnessParent2 hcoreWitnessParentStruct **
              bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes)))) := by
  rw [hcoreStatus0PostAssertion_eq]
  have hg : bytesRegion (262144 : Word) hcoreWitnessGBytes =
      ((262144 : Word) ↦ₘ packBytes hcoreWitnessGBytes) := by
    simpa [hcoreWitnessGAddr] using hcoreWitnessGRegion
  rw [← hg]

private theorem hcoreStatus0PostHeap_mem_outside
    (a : Word) (ha : hcoreStatus0PostBaseHeap.mem a ≠ none) :
    a.toNat < 131072 ∨
      (131720 ≤ a.toNat ∧ a.toNat < 204800) ∨
      205448 ≤ a.toNat := by
  have hmem : hcoreStatus0MemHeapFold.mem a ≠ none := by
    intro hm
    apply ha
    have hreg : hcoreStatus0PostRegHeapFold.mem a = none := by
      simp [hcoreStatus0PostRegHeapFold, hcoreStatus0PostRegHeap,
        hcoreStatus0PostRegs, PartialState.union, PartialState.singletonReg,
        PartialState.empty]
    simp [hcoreStatus0PostBaseHeap, PartialState.union, hreg, hm]
  obtain ⟨p, hp, hpa⟩ :=
    hcoreStatus0MemFold_mem_of_ne_none hcoreStatus0Mems a hmem
  rcases p with ⟨paddr, pval⟩
  subst a
  have hp' : (paddr, pval) ∈ hcoreStatus0Mems := hp
  simp [hcoreStatus0Mems, hcoreWitnessStructMems,
    hcoreStatus0HeaderRlp_length] at hp'
  repeat' first | rcases hp' with hp' | hp'
  all_goals norm_num

private def hcoreStatus0ScratchHeap : PartialState :=
  (PartialState.singletonReg .x14 0).union
    (PartialState.singletonReg .x15 0)

private theorem hcoreStatus0ScratchSat :
    regOwns [.x14, .x15] hcoreStatus0ScratchHeap := by
  simp only [regOwns]
  rw [sepConj_emp_right']
  refine ⟨PartialState.singletonReg .x14 0,
    PartialState.singletonReg .x15 0, ?_, rfl, ?_, ?_⟩
  · refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
      Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
    intro r
    by_cases hr14 : r = .x14
    · subst r
      simp [PartialState.singletonReg]
    · simp [PartialState.singletonReg, hr14]
  · exact ⟨0, by rfl⟩
  · exact ⟨0, by rfl⟩

private theorem validateHeaderCoreStatus0Post_nonempty_G :
    ∃ h : PartialState,
      validateHeaderCoreStatus0ProducerPost hcoreWitnessParentSpec
        hcoreStatus0HeaderSpec hcoreWitnessSpC 0 hcoreWitnessHeader
        hcoreStatus0HeaderRlp.length hcoreWitnessParent hcoreWitnessParent2
        hcoreWitnessParentRlp hcoreWitnessParentRlpBytes.length
        hcoreStatus0HeaderRlp hcoreWitnessParentRlpBytes
        hcoreStatus0HeaderStruct hcoreWitnessParentStruct 0 hcoreWitnessHeader
        (BitVec.ofNat 64 hcoreStatus0HeaderRlp.length)
        hcoreWitnessParent hcoreWitnessParent2
        hcoreWitnessParentRlp
        (BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)
        (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) h := by
  obtain ⟨h1sat, h2sat⟩ := hcoreStatus0RlpSat
  obtain ⟨h1, h1sat, h1within⟩ := h1sat
  obtain ⟨h2, h2sat, h2within⟩ := h2sat
  have h12disj : h1.Disjoint h2 := by
    refine ⟨fun _ => Or.inl (h1within.regs _), ?_,
      fun _ => Or.inl (h1within.code _), Or.inl h1within.pc,
      Or.inl h1within.publicValues, Or.inl h1within.privateInput,
      Or.inl h1within.inputBufBase⟩
    intro a
    by_cases h1none : h1.mem a = none
    · exact Or.inl h1none
    by_cases h2none : h2.mem a = none
    · exact Or.inr h2none
    have hin1 := h1within.mem a h1none
    have hin2 := h2within.mem a h2none
    omega
  have hrawsat :
      (bytesRegion hcoreWitnessHeader hcoreStatus0HeaderRlp **
        bytesRegion hcoreWitnessParentRlp hcoreWitnessParentRlpBytes)
        (h1.union h2) :=
    ⟨h1, h2, h12disj, rfl, h1sat, h2sat⟩
  have hdisj : hcoreStatus0PostBaseHeap.Disjoint (h1.union h2) := by
    refine ⟨fun _ => Or.inr (by simp [PartialState.union,
          h1within.regs, h2within.regs]), ?_,
      fun _ => Or.inr (by simp [PartialState.union,
          h1within.code, h2within.code]),
      Or.inr (by simp [PartialState.union, h1within.pc, h2within.pc]),
      Or.inr (by simp [PartialState.union,
          h1within.publicValues, h2within.publicValues]),
      Or.inr (by simp [PartialState.union,
          h1within.privateInput, h2within.privateInput]),
      Or.inr (by simp [PartialState.union,
          h1within.inputBufBase, h2within.inputBufBase])⟩
    intro a
    by_cases hold : hcoreStatus0PostBaseHeap.mem a = none
    · exact Or.inl hold
    by_cases h1none : h1.mem a = none
    · by_cases h2none : h2.mem a = none
      · exact Or.inr (by simp [PartialState.union, h1none, h2none])
      · have hout := hcoreStatus0PostHeap_mem_outside a hold
        have hin2 := h2within.mem a h2none
        omega
    · have hout := hcoreStatus0PostHeap_mem_outside a hold
      have hin1 := h1within.mem a h1none
      omega
  have hbase := show
      (hcoreStatus0PostBaseAssertion **
        (bytesRegion hcoreWitnessHeader hcoreStatus0HeaderRlp **
          bytesRegion hcoreWitnessParentRlp hcoreWitnessParentRlpBytes))
        (hcoreStatus0PostBaseHeap.union (h1.union h2)) from
    ⟨hcoreStatus0PostBaseHeap, h1.union h2, hdisj, rfl,
      hcoreStatus0PostBaseSat, hrawsat⟩
  have hall :
      EvmAsm.Stateless.SpecRef._decode_header hcoreStatus0HeaderRlp =
        .ok hcoreStatus0HeaderSpec ∧
      EvmAsm.Stateless.SpecRef._decode_header hcoreWitnessParentRlpBytes =
        .ok hcoreWitnessParentSpec ∧
      headerCoreStructRelation hcoreStatus0HeaderStruct hcoreStatus0HeaderSpec ∧
      headerCoreStructRelation hcoreWitnessParentStruct hcoreWitnessParentSpec :=
    ⟨hcoreStatus0_decodeHeader, hcoreParent_decodeHeader,
      hcoreStatus0HeaderStruct_relation, hcoreWitnessParentStruct_relation⟩
  have hstatus :
      validateHeaderStatusResult hcoreWitnessParentSpec hcoreStatus0HeaderSpec
        0 hcoreWitnessHeader hcoreStatus0HeaderRlp :=
    Or.inl ⟨rfl, hcoreStatus0_validate_header⟩
  have h := (sepConj_pure_right _).2 ⟨hbase, hall⟩
  have h' := (sepConj_pure_right _).2 ⟨h, hstatus⟩
  rw [hcoreStatus0PostAssertion_eq_bytes] at h'
  have hscratchDisj :
      (hcoreStatus0PostBaseHeap.union (h1.union h2)).Disjoint
        hcoreStatus0ScratchHeap := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r
      by_cases hr14 : r = .x14
      · subst r
        left
        have h1r := h1within.regs (.x14)
        have h2r := h2within.regs (.x14)
        simp [hcoreStatus0PostBaseHeap, hcoreStatus0PostRegHeapFold,
          hcoreStatus0PostRegHeap, hcoreStatus0PostRegs,
          hcoreStatus0MemHeapFold, hcoreStatus0MemHeap, hcoreStatus0Mems,
          hcoreWitnessStructMems, PartialState.singletonMem,
          PartialState.union,
          PartialState.singletonReg, PartialState.empty, h1r, h2r]
      · by_cases hr15 : r = .x15
        · subst r
          left
          have h1r := h1within.regs (.x15)
          have h2r := h2within.regs (.x15)
          simp [hcoreStatus0PostBaseHeap, hcoreStatus0PostRegHeapFold,
            hcoreStatus0PostRegHeap, hcoreStatus0PostRegs,
            hcoreStatus0MemHeapFold, hcoreStatus0MemHeap, hcoreStatus0Mems,
            hcoreWitnessStructMems, PartialState.singletonMem,
            PartialState.union,
            PartialState.singletonReg, PartialState.empty, h1r, h2r]
        · right
          simp [hcoreStatus0ScratchHeap, PartialState.union,
            PartialState.singletonReg, hr14, hr15]
    · intro a
      simp [hcoreStatus0PostBaseHeap, hcoreStatus0ScratchHeap,
        PartialState.union, PartialState.singletonReg]
    · intro a
      simp [hcoreStatus0PostBaseHeap, hcoreStatus0ScratchHeap,
        PartialState.union, PartialState.singletonReg]
    · simp [hcoreStatus0PostBaseHeap, hcoreStatus0ScratchHeap,
        PartialState.union, PartialState.singletonReg]
    · simp [hcoreStatus0PostBaseHeap, hcoreStatus0ScratchHeap,
        PartialState.union, PartialState.singletonReg]
    · simp [hcoreStatus0PostBaseHeap, hcoreStatus0ScratchHeap,
        PartialState.union, PartialState.singletonReg]
    · simp [hcoreStatus0PostBaseHeap, hcoreStatus0ScratchHeap,
        PartialState.union, PartialState.singletonReg]
  simp [hcoreStatus0PostRegFold, hcoreStatus0PostRegAtom,
    hcoreStatus0PostRegs, hcoreStatus0StackFold, hcoreStatus0StackMems,
    hcoreWitnessSpC, hcoreStatus0HeaderRlp_length,
    hcoreParentRlp_length, sepConj_emp_right', sepConj_assoc'] at h'
  refine ⟨(hcoreStatus0PostBaseHeap.union (h1.union h2)).union
      hcoreStatus0ScratchHeap, ?_⟩
  change (validateHeaderCorePost hcoreWitnessParentSpec hcoreStatus0HeaderSpec
      0 hcoreWitnessSpC 0 hcoreWitnessHeader hcoreStatus0HeaderRlp.length
      hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
      hcoreWitnessParentRlpBytes.length hcoreStatus0HeaderRlp
      hcoreWitnessParentRlpBytes hcoreStatus0HeaderStruct hcoreWitnessParentStruct
      0 hcoreWitnessHeader (BitVec.ofNat 64 hcoreStatus0HeaderRlp.length)
      hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
      (BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)
      (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) **
      regOwns [.x14, .x15])
      ((hcoreStatus0PostBaseHeap.union (h1.union h2)).union
        hcoreStatus0ScratchHeap)
  refine ⟨hcoreStatus0PostBaseHeap.union (h1.union h2),
    hcoreStatus0ScratchHeap, hscratchDisj, rfl, ?_, hcoreStatus0ScratchSat⟩
  simp [validateHeaderCorePost, validateHeaderCoreFrame,
    hcoreWitnessSpC, hcoreWitnessHeader, hcoreWitnessParent,
    sepConj_assoc'] at ⊢
  simp [hcoreStatus0HeaderRlp_length, hcoreParentRlp_length] at ⊢
  xperm_hyp h'

/- The unchanged core precondition and the status-0 producer postcondition
   are inhabited on the same concrete header package and non-empty ambient
   `bytesRegion`.  Keeping this conjunction explicit prevents the extra
   x14/x15 ownership from being treated as a merely conditional handoff. -/
theorem validateHeaderCoreStatus0_joint_nonempty_G :
    (∃ h : PartialState,
      validateHeaderCorePre hcoreWitnessParentSpec hcoreStatus0HeaderSpec
        hcoreWitnessSpC 0 hcoreWitnessHeader hcoreStatus0HeaderRlp.length
        hcoreStatus0HeaderRlp hcoreWitnessParentRlpBytes
        hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
        hcoreWitnessParentRlpBytes.length
        hcoreStatus0HeaderStruct hcoreWitnessParentStruct
        hcoreWitnessHeader hcoreStatus0HeaderRlp.length hcoreWitnessParent
        hcoreWitnessParent2 hcoreWitnessParentRlp
        hcoreWitnessParentRlpBytes.length
        (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) h) ∧
    (∃ h : PartialState,
      validateHeaderCoreStatus0ProducerPost hcoreWitnessParentSpec
        hcoreStatus0HeaderSpec hcoreWitnessSpC 0 hcoreWitnessHeader
        hcoreStatus0HeaderRlp.length hcoreWitnessParent hcoreWitnessParent2
        hcoreWitnessParentRlp hcoreWitnessParentRlpBytes.length
        hcoreStatus0HeaderRlp hcoreWitnessParentRlpBytes
        hcoreStatus0HeaderStruct hcoreWitnessParentStruct 0 hcoreWitnessHeader
        (BitVec.ofNat 64 hcoreStatus0HeaderRlp.length)
        hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
        (BitVec.ofNat 64 hcoreWitnessParentRlpBytes.length)
        (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) h) := by
  exact ⟨validateHeaderCoreStatus0Pre_nonempty_G,
    validateHeaderCoreStatus0Post_nonempty_G⟩

private theorem hcoreWitnessHeaderStruct_slice16 :
    (List.take 8 (List.drop 16 hcoreWitnessHeaderStruct)) =
      List.take 8 (List.drop 16 (headerCoreStructBytes hcoreWitnessHeaderSpec)) := by
  rfl

private theorem hcoreWitnessHeaderStruct_slice80 :
    (List.take 8 (List.drop 80 hcoreWitnessHeaderStruct)) =
      List.take 8 (List.drop 80 (headerCoreStructBytes hcoreWitnessHeaderSpec)) := by
  rfl

private theorem hcoreWitnessHeaderStruct_slice136 :
    (List.take 8 (List.drop 136 hcoreWitnessHeaderStruct)) =
      List.take 8 (List.drop 136 (headerCoreStructBytes hcoreWitnessHeaderSpec)) := by
  rfl

private theorem hcoreWitnessParentStruct_slice16 :
    (List.take 8 (List.drop 16 hcoreWitnessParentStruct)) =
      List.take 8 (List.drop 16 (headerCoreStructBytes hcoreWitnessParentSpec)) := by
  rfl

private theorem hcoreWitnessParentStruct_slice80 :
    (List.take 8 (List.drop 80 hcoreWitnessParentStruct)) =
      List.take 8 (List.drop 80 (headerCoreStructBytes hcoreWitnessParentSpec)) := by
  rfl

private theorem hcoreWitnessParentStruct_slice136 :
    (List.take 8 (List.drop 136 hcoreWitnessParentStruct)) =
      List.take 8 (List.drop 136 (headerCoreStructBytes hcoreWitnessParentSpec)) := by
  rfl

/- The concrete witness stores all 18 dwords of each 144-byte record.  Keep
the chunk equation parametric so simplification can normalize whichever
offset a framed `bytesRegion` exposes (not just the five offsets read by the
core body). -/
private theorem hcoreWitnessHeaderStruct_chunk (i : Nat) :
    List.take 8 (List.drop (8 * i) hcoreWitnessHeaderStruct) =
      List.take 8 (List.drop (8 * i)
        (headerCoreStructBytes hcoreWitnessHeaderSpec)) := by
  rfl

private theorem hcoreWitnessParentStruct_chunk (i : Nat) :
    List.take 8 (List.drop (8 * i) hcoreWitnessParentStruct) =
      List.take 8 (List.drop (8 * i)
        (headerCoreStructBytes hcoreWitnessParentSpec)) := by
  rfl

private theorem hcore_drop40_take8_append_of_len32
    {α : Type} (a b rest : List α)
    (ha : a.length = 32) (hb : b.length = 32) :
    List.take 8 (List.drop 40 (a ++ b ++ rest)) =
      List.take 8 (List.drop 8 (b ++ rest)) := by
  simp [List.drop_append, List.drop_eq_nil_of_le, ha, hb]

private theorem hcoreWitnessHeaderStruct_chunk40_rev :
    List.take 8 (List.drop 8
        (hcoreWitnessHeaderSpec.stateRoot ++
          EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.number ++
          EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.timestamp ++
          EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.gasLimit ++
          EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.gasUsed ++
          EvmAsm.Stateless.SpecRef.natToBytesBE 32 hcoreWitnessHeaderSpec.baseFeePerGas ++
          EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.blobGasUsed ++
          EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.excessBlobGas)) =
      List.take 8 (List.drop 40
        (headerCoreStructBytes hcoreWitnessHeaderSpec)) := by
  have hp : hcoreWitnessHeaderSpec.parentHash.length = 32 := by
    simp [hcoreWitnessHeaderSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
  have hs : hcoreWitnessHeaderSpec.stateRoot.length = 32 := by
    simp [hcoreWitnessHeaderSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
  symm
  simpa [headerCoreStructBytes] using
    (hcore_drop40_take8_append_of_len32
      hcoreWitnessHeaderSpec.parentHash hcoreWitnessHeaderSpec.stateRoot
      (EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.number ++
        EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.timestamp ++
        EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.gasLimit ++
        EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.gasUsed ++
        EvmAsm.Stateless.SpecRef.natToBytesBE 32 hcoreWitnessHeaderSpec.baseFeePerGas ++
        EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.blobGasUsed ++
        EvmAsm.Stateless.SpecRef.natToBytesLE 8 hcoreWitnessHeaderSpec.excessBlobGas)
      hp hs)

/-- The full core precondition is inhabited with a real, non-empty frame.

The frame is eight concrete bytes at `0x40000`, separated from all fourteen
register atoms and seven stack cells.  This is the primary non-vacuity witness;
it demonstrates that the abstract frame can carry content rather than merely
being instantiated with `empAssertion`. -/
theorem validateHeaderCorePre_nonempty_G :
    ∃ h : PartialState,
      validateHeaderCorePre hcoreWitnessParentSpec hcoreWitnessHeaderSpec
        hcoreWitnessSpC 0 hcoreWitnessHeader hcoreWitnessHeaderRlp.length
        hcoreWitnessHeaderRlp hcoreWitnessParentRlpBytes
        hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
        hcoreWitnessParentRlpBytes.length
        hcoreWitnessHeaderStruct hcoreWitnessParentStruct
        hcoreWitnessHeader hcoreWitnessHeaderRlp.length hcoreWitnessParent hcoreWitnessParent2
        hcoreWitnessParentRlp hcoreWitnessParentRlpBytes.length
        (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) h := by
  -- v4.33: a single `simpa` leaves the hypothesis' `List.take 8 (List.drop k ...)`
  -- windows unreduced while the goal's are fully reduced, so the closing `exact`
  -- (at reducible transparency) fails.  Simp the hypothesis on its own until it
  -- reaches the same normal form, then close at default transparency.
  obtain ⟨h1sat, h2sat⟩ := hcoreWitnessRlpSat
  obtain ⟨h1, h1sat, h1within⟩ := h1sat
  obtain ⟨h2, h2sat, h2within⟩ := h2sat
  have h12disj : h1.Disjoint h2 := by
    refine ⟨fun _ => Or.inl (h1within.regs _), ?_,
      fun _ => Or.inl (h1within.code _), Or.inl h1within.pc,
      Or.inl h1within.publicValues, Or.inl h1within.privateInput,
      Or.inl h1within.inputBufBase⟩
    intro a
    by_cases h1none : h1.mem a = none
    · exact Or.inl h1none
    by_cases h2none : h2.mem a = none
    · exact Or.inr h2none
    have hin1 := h1within.mem a h1none
    have hin2 := h2within.mem a h2none
    omega
  have hrawsat :
      (bytesRegion hcoreWitnessHeader hcoreWitnessHeaderRlp **
        bytesRegion hcoreWitnessParentRlp hcoreWitnessParentRlpBytes)
        (h1.union h2) :=
    ⟨h1, h2, h12disj, rfl, h1sat, h2sat⟩
  have hdisj : hcoreWitnessHeap.Disjoint (h1.union h2) := by
    refine ⟨fun _ => Or.inr (by simp [PartialState.union,
          h1within.regs, h2within.regs]), ?_,
      fun _ => Or.inr (by simp [PartialState.union,
          h1within.code, h2within.code]),
      Or.inr (by simp [PartialState.union, h1within.pc, h2within.pc]),
      Or.inr (by simp [PartialState.union,
          h1within.publicValues, h2within.publicValues]),
      Or.inr (by simp [PartialState.union,
          h1within.privateInput, h2within.privateInput]),
      Or.inr (by simp [PartialState.union,
          h1within.inputBufBase, h2within.inputBufBase])⟩
    intro a
    by_cases hold : hcoreWitnessHeap.mem a = none
    · exact Or.inl hold
    by_cases h1none : h1.mem a = none
    · by_cases h2none : h2.mem a = none
      · exact Or.inr (by simp [PartialState.union, h1none, h2none])
      · have hout := hcoreWitnessHeap_mem_outside a hold
        have hin2 := h2within.mem a h2none
        omega
    · have hout := hcoreWitnessHeap_mem_outside a hold
      have hin1 := h1within.mem a h1none
      omega
  have hbase := show
      (hcoreWitnessAssertion **
        (bytesRegion hcoreWitnessHeader hcoreWitnessHeaderRlp **
          bytesRegion hcoreWitnessParentRlp hcoreWitnessParentRlpBytes))
        (hcoreWitnessHeap.union (h1.union h2)) from
    ⟨hcoreWitnessHeap, h1.union h2, hdisj, rfl, hcoreWitnessSat, hrawsat⟩
  have hmap1 :
      List.map (fun i => BitVec.ofNat 8 (1 >>> (8 * i))) (List.range 8) =
        [1, 0, 0, 0, 0, 0, 0, 0] := by
    norm_num [List.map, List.range, List.range.loop]
    decide
  have hmap30000000 :
      List.map (fun i => BitVec.ofNat 8 (30000000 >>> (8 * i))) (List.range 8) =
        [128, 195, 201, 1, 0, 0, 0, 0] := by
    norm_num [List.map, List.range, List.range.loop]
    decide
  have hrel1 :
      EvmAsm.Stateless.SpecRef._decode_header hcoreWitnessHeaderRlp =
        .ok hcoreWitnessHeaderSpec := by
    let h := hcoreWitnessHeaderSpec
    let bs : List EvmAsm.Stateless.SpecRef.Bytes :=
      [h.parentHash, h.ommersHash, h.coinbase, h.stateRoot,
       h.transactionsRoot, h.receiptRoot, h.bloom,
       EvmAsm.EL.RLP.Nat.toBytesBE h.difficulty,
       EvmAsm.EL.RLP.Nat.toBytesBE h.number,
       EvmAsm.EL.RLP.Nat.toBytesBE h.gasLimit,
       EvmAsm.EL.RLP.Nat.toBytesBE h.gasUsed,
       EvmAsm.EL.RLP.Nat.toBytesBE h.timestamp,
       h.extraData, h.prevRandao, h.nonce,
       EvmAsm.EL.RLP.Nat.toBytesBE h.baseFeePerGas,
       h.withdrawalsRoot,
       EvmAsm.EL.RLP.Nat.toBytesBE h.blobGasUsed,
       EvmAsm.EL.RLP.Nat.toBytesBE h.excessBlobGas,
       h.parentBeaconBlockRoot, h.requestsHash, h.blockAccessListHash,
       EvmAsm.EL.RLP.Nat.toBytesBE h.slotNumber]
    have hitem : EvmAsm.Stateless.SpecRef.headerToRlpItem h =
        .list (bs.map EvmAsm.EL.RLP.RLPItem.bytes) := by
      simp [bs, h, hcoreWitnessHeaderSpec,
        EvmAsm.Stateless.SpecRef.headerToRlpItem, scalarItem]
    have hmap : (bs.map EvmAsm.EL.RLP.RLPItem.bytes).mapM rlpBytes? = some bs := by
      induction bs with
      | nil => rfl
      | cons head tail ih =>
          simp only [List.map_cons, List.mapM_cons, rlpBytes?]
          rw [ih]
          simp
    have hnum : EvmAsm.Stateless.SpecRef.validateHeaderWitness_numericFieldsOk bs = true := by
      change numericFieldsOk bs = true
      simp [numericFieldsOk, EvmAsm.Stateless.SpecRef.numericFieldWidths, getNChecked,
        EvmAsm.Stateless.SpecRef.decodeItemScalar, bs, h,
        hcoreWitnessHeaderSpec,
        EvmAsm.EL.RLP.Nat.toBytesBE, List.all, List.getD]; decide
    have hbytes : EvmAsm.Stateless.SpecRef.validateHeaderWitness_bytesFieldsOk true bs = true := by
      change bytesFieldsOk true bs = true
      simp [bytesFieldsOk,
        EvmAsm.Stateless.SpecRef.fixedBytesFieldWidths,
        EvmAsm.Stateless.SpecRef.currentForkBytesFieldWidths, getBChecked,
        EvmAsm.Stateless.SpecRef.decodeItemFixedBytes, bs, h, hcoreWitnessHeaderSpec,
        EvmAsm.Stateless.SpecRef.natToBytesBE_length,
        List.all, List.getD]; decide
    have hmk : EvmAsm.Stateless.SpecRef.mkHeaderFields true bs = h := by
      simp [EvmAsm.Stateless.SpecRef.mkHeaderFields, bs, h, hcoreWitnessHeaderSpec,
        EvmAsm.EL.RLP.Nat.fromBytesBE_toBytesBE]
    unfold hcoreWitnessHeaderRlp
    rw [hitem]
    have hlen : hcoreWitnessHeaderRlp.length = 645 := hcoreHeaderRlp_length
    have hfull := EvmAsm.EL.RLP.decodeFully_encode
      (.list (bs.map EvmAsm.EL.RLP.RLPItem.bytes))
      (by change hcoreWitnessHeaderRlp.length < 256 ^ 8; rw [hlen]; decide)
    simp only [EvmAsm.Stateless.SpecRef._decode_header, hfull, hmap]
    simp [bs, h, hcore_decodeHeaderArm_ok, hnum, hbytes, hmk]
  have hrel2 :
      EvmAsm.Stateless.SpecRef._decode_header hcoreWitnessParentRlpBytes =
        .ok hcoreWitnessParentSpec := by
    let h := hcoreWitnessParentSpec
    let bs : List EvmAsm.Stateless.SpecRef.Bytes :=
      [h.parentHash, h.ommersHash, h.coinbase, h.stateRoot,
       h.transactionsRoot, h.receiptRoot, h.bloom,
       EvmAsm.EL.RLP.Nat.toBytesBE h.difficulty,
       EvmAsm.EL.RLP.Nat.toBytesBE h.number,
       EvmAsm.EL.RLP.Nat.toBytesBE h.gasLimit,
       EvmAsm.EL.RLP.Nat.toBytesBE h.gasUsed,
       EvmAsm.EL.RLP.Nat.toBytesBE h.timestamp,
       h.extraData, h.prevRandao, h.nonce,
       EvmAsm.EL.RLP.Nat.toBytesBE h.baseFeePerGas,
       h.withdrawalsRoot,
       EvmAsm.EL.RLP.Nat.toBytesBE h.blobGasUsed,
       EvmAsm.EL.RLP.Nat.toBytesBE h.excessBlobGas,
       h.parentBeaconBlockRoot, h.requestsHash, h.blockAccessListHash,
       EvmAsm.EL.RLP.Nat.toBytesBE h.slotNumber]
    have hitem : EvmAsm.Stateless.SpecRef.headerToRlpItem h =
        .list (bs.map EvmAsm.EL.RLP.RLPItem.bytes) := by
      simp [bs, h, hcoreWitnessParentSpec,
        EvmAsm.Stateless.SpecRef.headerToRlpItem, scalarItem]
    have hmap : (bs.map EvmAsm.EL.RLP.RLPItem.bytes).mapM rlpBytes? = some bs := by
      induction bs with
      | nil => rfl
      | cons head tail ih =>
          simp only [List.map_cons, List.mapM_cons, rlpBytes?]
          rw [ih]
          simp
    have hnum : EvmAsm.Stateless.SpecRef.validateHeaderWitness_numericFieldsOk bs = true := by
      change numericFieldsOk bs = true
      simp [numericFieldsOk, EvmAsm.Stateless.SpecRef.numericFieldWidths, getNChecked,
        EvmAsm.Stateless.SpecRef.decodeItemScalar, bs, h,
        hcoreWitnessParentSpec,
        EvmAsm.EL.RLP.Nat.toBytesBE, List.all, List.getD]; decide
    have hbytes : EvmAsm.Stateless.SpecRef.validateHeaderWitness_bytesFieldsOk true bs = true := by
      change bytesFieldsOk true bs = true
      simp [bytesFieldsOk,
        EvmAsm.Stateless.SpecRef.fixedBytesFieldWidths,
        EvmAsm.Stateless.SpecRef.currentForkBytesFieldWidths, getBChecked,
        EvmAsm.Stateless.SpecRef.decodeItemFixedBytes, bs, h, hcoreWitnessParentSpec,
        EvmAsm.Stateless.SpecRef.natToBytesBE_length,
        List.all, List.getD]; decide
    have hmk : EvmAsm.Stateless.SpecRef.mkHeaderFields true bs = h := by
      simp [EvmAsm.Stateless.SpecRef.mkHeaderFields, bs, h, hcoreWitnessParentSpec,
        EvmAsm.EL.RLP.Nat.fromBytesBE_toBytesBE]
    unfold hcoreWitnessParentRlpBytes
    rw [hitem]
    have hlen : hcoreWitnessParentRlpBytes.length = 645 := hcoreParentRlp_length
    have hfull := EvmAsm.EL.RLP.decodeFully_encode
      (.list (bs.map EvmAsm.EL.RLP.RLPItem.bytes))
      (by change hcoreWitnessParentRlpBytes.length < 256 ^ 8; rw [hlen]; decide)
    simp only [EvmAsm.Stateless.SpecRef._decode_header, hfull, hmap]
    simp [bs, h, hcore_decodeHeaderArm_ok, hnum, hbytes, hmk]
  have h_with_rel1 :
      ((hcoreWitnessAssertion **
        (bytesRegion hcoreWitnessHeader hcoreWitnessHeaderRlp **
          bytesRegion hcoreWitnessParentRlp hcoreWitnessParentRlpBytes)) **
        ⌜EvmAsm.Stateless.SpecRef._decode_header hcoreWitnessHeaderRlp =
            .ok hcoreWitnessHeaderSpec⌝)
        (hcoreWitnessHeap.union (h1.union h2)) := by
    exact (sepConj_pure_right _).2 ⟨hbase, hrel1⟩
  have h_with_rel2 :
      (((hcoreWitnessAssertion **
        (bytesRegion hcoreWitnessHeader hcoreWitnessHeaderRlp **
          bytesRegion hcoreWitnessParentRlp hcoreWitnessParentRlpBytes)) **
        ⌜EvmAsm.Stateless.SpecRef._decode_header hcoreWitnessHeaderRlp =
            .ok hcoreWitnessHeaderSpec⌝) **
        ⌜EvmAsm.Stateless.SpecRef._decode_header hcoreWitnessParentRlpBytes =
            .ok hcoreWitnessParentSpec⌝)
        (hcoreWitnessHeap.union (h1.union h2)) := by
    exact (sepConj_pure_right _).2 ⟨h_with_rel1, hrel2⟩
  have hstruct1 :
      headerCoreStructRelation hcoreWitnessHeaderStruct hcoreWitnessHeaderSpec := by
    have hp : hcoreWitnessHeaderSpec.parentHash.length = 32 := by
      simp [hcoreWitnessHeaderSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
    have hs : hcoreWitnessHeaderSpec.stateRoot.length = 32 := by
      simp [hcoreWitnessHeaderSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
    refine ⟨?_, rfl⟩
    simp [hcoreWitnessHeaderStruct, headerCoreStructBytes,
      hp, hs,
      EvmAsm.Stateless.SpecRef.natToBytesBE_length,
      EvmAsm.Stateless.SpecRef.natToBytesLE_length]
  have hstruct2 :
      headerCoreStructRelation hcoreWitnessParentStruct hcoreWitnessParentSpec := by
    have hp : hcoreWitnessParentSpec.parentHash.length = 32 := by
      simp [hcoreWitnessParentSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
    have hs : hcoreWitnessParentSpec.stateRoot.length = 32 := by
      simp [hcoreWitnessParentSpec, EvmAsm.Stateless.SpecRef.natToBytesBE_length]
    refine ⟨?_, rfl⟩
    simp [hcoreWitnessParentStruct, headerCoreStructBytes,
      hp, hs,
      EvmAsm.Stateless.SpecRef.natToBytesBE_length,
      EvmAsm.Stateless.SpecRef.natToBytesLE_length]
  have hall :
      hcoreWitnessHeaderRlp.length = hcoreWitnessHeaderRlp.length ∧
      hcoreWitnessParentRlpBytes.length = hcoreWitnessParentRlpBytes.length ∧
      EvmAsm.Stateless.SpecRef._decode_header hcoreWitnessHeaderRlp =
        .ok hcoreWitnessHeaderSpec ∧
      EvmAsm.Stateless.SpecRef._decode_header hcoreWitnessParentRlpBytes =
        .ok hcoreWitnessParentSpec ∧
      headerCoreStructRelation hcoreWitnessHeaderStruct hcoreWitnessHeaderSpec ∧
      headerCoreStructRelation hcoreWitnessParentStruct hcoreWitnessParentSpec :=
    ⟨rfl, rfl, hrel1, hrel2, hstruct1, hstruct2⟩
  have h := (sepConj_pure_right _).2 ⟨hbase, hall⟩
  rw [hcoreWitnessAssertion_eq] at h
  refine ⟨hcoreWitnessHeap.union (h1.union h2), ?_⟩
  simp [hcoreWitnessRegFold, hcoreWitnessRegAtom, hcoreWitnessRegs,
    hcoreWitnessStackFold, hcoreWitnessStackMems,
    hcoreWitnessSpC, hcoreWitnessHeader, hcoreWitnessParent,
    sepConj_emp_right', sepConj_assoc'] at h
  simp [validateHeaderCorePre, validateHeaderCoreFrame,
    hcoreWitnessSpC, hcoreWitnessHeader, hcoreWitnessParent,
    sepConj_assoc'] at h ⊢
  xperm_hyp h

/-- The complete caller-side premise conjunction is inhabited with the
non-empty frame, including the stack-pointer relation, return-address
alignment, frame `pcFree`, and `validateHeaderCorePre` itself.  This is a
non-vacuity result only: the abstract `hcore` route premise is still
undischarged and has no semantic callers. -/
theorem validateHeaderCorePremises_nonempty_G :
    ∃ h : PartialState,
      hcoreWitnessSpC = hcoreWitnessSp0 + signExtend12 (-56 : BitVec 12) ∧
      ((0 : Word) &&& ~~~(1 : Word) = 0) ∧
      (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes).pcFree ∧
      validateHeaderCorePre hcoreWitnessParentSpec hcoreWitnessHeaderSpec
        hcoreWitnessSpC 0 hcoreWitnessHeader hcoreWitnessHeaderRlp.length
        hcoreWitnessHeaderRlp hcoreWitnessParentRlpBytes
        hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
        hcoreWitnessParentRlpBytes.length
        hcoreWitnessHeaderStruct hcoreWitnessParentStruct
        hcoreWitnessHeader hcoreWitnessHeaderRlp.length hcoreWitnessParent hcoreWitnessParent2
        hcoreWitnessParentRlp hcoreWitnessParentRlpBytes.length
        (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) h := by
  obtain ⟨h, hpre⟩ := validateHeaderCorePre_nonempty_G
  refine ⟨h, ?_, ?_, ?_, hpre⟩
  · decide
  · decide
  · exact bytesRegion_pcFree _ _

/-! ## Repaired-pre execution probe (#12715)

The concrete frame above uses the repaired `headerCoreStructRelation` rather
than an unconstrained cell at `thisStruct + 64`.  Four machine steps from the
core entry therefore execute the number/nonzero guard and the first three
loads; the post-state is at `H + 72` with the excess-blob status still zero.
This is an executable witness for the repaired pre, not a claim that the
abstract `hcore` route contract has already been proved.
-/

private def hcoreProbeRegHeap : (Reg × Word) → PartialState :=
  fun p => PartialState.singletonReg p.1 p.2

private def hcoreProbeMemHeap : (Word × Word) → PartialState :=
  fun p => PartialState.singletonMem p.1 p.2

private def hcoreProbeRegHeapFold : PartialState :=
  hcoreWitnessRegs.foldr
    (fun p acc => (hcoreProbeRegHeap p).union acc) PartialState.empty

private def hcoreProbeMemHeapFold : PartialState :=
  hcoreWitnessMems.foldr
    (fun p acc => (hcoreProbeMemHeap p).union acc) PartialState.empty

private def hcoreProbeHeap : PartialState :=
  hcoreProbeRegHeapFold.union hcoreProbeMemHeapFold

private def hcoreProbeState : MachineState where
  regs := fun r => (hcoreProbeHeap.regs r).getD 0
  mem := fun a => (hcoreProbeHeap.mem a).getD 0
  code := callerCode
  pc := H + 56

theorem validateHeaderCore_repairedPre_step4_pc :
    (stepN 4 hcoreProbeState).map MachineState.pc = some (H + 72) := by
  simp only [stepN, hcoreProbeState, Option.bind]
  simp [step, hcoreProbeHeap, hcoreProbeRegHeapFold, hcoreProbeMemHeapFold,
    hcoreProbeRegHeap, hcoreProbeMemHeap, hcoreWitnessRegs, hcoreWitnessMems,
    hcoreWitnessStructMems, hcoreWitnessHeaderStruct,
    hcoreWitnessParentStruct, headerCoreStructBytes,
    hcoreWitnessHeaderSpec, PartialState.union,
    PartialState.singletonReg, PartialState.singletonMem, PartialState.empty]
  decide

theorem validateHeaderCore_repairedPre_step4_status :
    (stepN 4 hcoreProbeState).map (fun s => s.getReg .x10) =
      some (262144 : Word) := by
  simp only [stepN, hcoreProbeState, Option.bind]
  simp [step, hcoreProbeHeap, hcoreProbeRegHeapFold, hcoreProbeMemHeapFold,
    hcoreProbeRegHeap, hcoreProbeMemHeap, hcoreWitnessRegs, hcoreWitnessMems,
    hcoreWitnessStructMems, hcoreWitnessHeaderStruct,
    hcoreWitnessParentStruct, headerCoreStructBytes,
    hcoreWitnessHeaderSpec, PartialState.union,
    PartialState.singletonReg, PartialState.singletonMem, PartialState.empty]
  decide

/-! The relation is sufficient to project the five scalar cells read by the
core body.  Its 144-byte length forces the two leading byte regions together
to occupy 64 bytes; the remaining chunks have fixed lengths, so no decoder
fact is needed for this projection itself. -/
theorem headerCoreStructRelation_five_reads
    (bs : List (BitVec 8)) (h : EvmAsm.Stateless.SpecRef.Header)
    (hrel : headerCoreStructRelation bs h) :
    (bs.drop 64).take 8 = EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.number ∧
    (bs.drop 72).take 8 = EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.timestamp ∧
    (bs.drop 80).take 8 = EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasLimit ∧
    (bs.drop 88).take 8 = EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasUsed ∧
    (bs.drop 136).take 8 = EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.excessBlobGas := by
  rcases hrel with ⟨hlen, rfl⟩
  have hsum : h.parentHash.length + h.stateRoot.length = 64 := by
    simp [headerCoreStructBytes] at hlen
    omega
  have hslice (pre rest : List (BitVec 8)) :
      ((h.parentHash ++ h.stateRoot ++ pre ++ rest).drop
        (h.parentHash.length + h.stateRoot.length + pre.length)).take 8 =
        rest.take 8 := by
    have hd := List.drop_append_length
      (l₁ := h.parentHash ++ h.stateRoot ++ pre) (l₂ := rest)
    simpa only [List.length_append, Nat.add_assoc, List.append_assoc] using
      congrArg (List.take 8) hd
  have hn := hslice []
    (EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.number ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.timestamp ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasLimit ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasUsed ++
      EvmAsm.Stateless.SpecRef.natToBytesBE 32 h.baseFeePerGas ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.blobGasUsed ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.excessBlobGas)
  have ht := hslice (EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.number)
    (EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.timestamp ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasLimit ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasUsed ++
      EvmAsm.Stateless.SpecRef.natToBytesBE 32 h.baseFeePerGas ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.blobGasUsed ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.excessBlobGas)
  have hgL := hslice
    (EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.number ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.timestamp)
    (EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasLimit ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasUsed ++
      EvmAsm.Stateless.SpecRef.natToBytesBE 32 h.baseFeePerGas ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.blobGasUsed ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.excessBlobGas)
  have hgU := hslice
    (EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.number ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.timestamp ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasLimit)
    (EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasUsed ++
      EvmAsm.Stateless.SpecRef.natToBytesBE 32 h.baseFeePerGas ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.blobGasUsed ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.excessBlobGas)
  have he := hslice
    (EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.number ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.timestamp ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasLimit ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasUsed ++
      EvmAsm.Stateless.SpecRef.natToBytesBE 32 h.baseFeePerGas ++
      EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.blobGasUsed)
    (EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.excessBlobGas)
  constructor
  · simpa [headerCoreStructBytes, hsum] using hn
  constructor
  · simpa [headerCoreStructBytes, hsum] using ht
  constructor
  · simpa [headerCoreStructBytes, hsum] using hgL
  constructor
  · simpa [headerCoreStructBytes, hsum] using hgU
  · -- `exact`, not `simpa using`: the two sides differ only by the reducible
    -- `SpecRef.Byte` synonym in the `List _` index, which v4.33's `simpa` will
    -- not unfold at reducible transparency.
    simp [headerCoreStructBytes, hsum] at he ⊢
    exact he

end EvmAsm.Codegen.ValidateHeaderWhole
