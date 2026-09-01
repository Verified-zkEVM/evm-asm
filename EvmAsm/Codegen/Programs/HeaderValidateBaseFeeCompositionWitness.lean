/-
  A concrete anti-vacuity witness for the K73 decrease composition (#12346).

  The table below is intentionally explicit.  It gives one joint state for
  the complete K73 precondition, including the K74 flat-frame registers and a
  non-empty caller-owned tail.  In particular, it checks the whole separating
  conjunction at once rather than proving independent atoms and composing
  them by inspection.
-/

import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeCompositionEqualDecrease

namespace EvmAsm.Codegen.HeaderValidateBaseFeeCompositionWitness

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec
open EvmAsm.Codegen.HeaderValidateBaseFeeSpec
open EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute

/-! The concrete ownership table used by `k73_decr_pre_inhabited`.

    Fixed registers are the values exposed by the K73 entry contract;
    `scratchOwnedRegs` are the K73-owned working registers, with x14--x17
    supplied by `k74FlatFrame`.  Fixed memory covers the K73 frame, saved
    frame, input/output regions, subtract scratch and multiply frame. -/

def k73_decr_witness_fixed_regs : List (Reg × Word) :=
  [(.x1, HeaderValidateBaseFeeSpec.H + 40), (.x2, 0xa0050038),
   (.x8, 0x200000), (.x9, 0), (.x18, 0), (.x19, 0), (.x20, 0),
   (.x10, 10000), (.x11, 2500), (.x12, 0x200100),
   (.x13, HeaderValidateBaseFeeSpec.Expected), (.x0, 0)]

def k73_decr_witness_owned_regs : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x14, .x15, .x16, .x17]

def k73_decr_witness_owned_mems : List Word :=
  [0xa0050000, 0xa0050008, 0xa0050010, 0xa0050018, 0xa0050020,
   0xa0050028, 0x300000]

def k73_decr_witness_fixed_mems : List (Word × Word) :=
  [(0xa0050038, HeaderValidateBaseFeeSpec.H + 40), (0xa0050040, 0),
   (0x200000, 0), (0x200008, 0), (0x200010, 0), (0x200018, 0),
   (0x200100, 0), (0x200108, 0), (0x200110, 0), (0x200118, 0),
   (HeaderValidateBaseFeeSpec.Expected, 0),
   (HeaderValidateBaseFeeSpec.Expected + 8, 0),
   (HeaderValidateBaseFeeSpec.Expected + 16, 0),
   (HeaderValidateBaseFeeSpec.Expected + 24, 0),
   (0xa004ffd0, 0), (0xa004ffd8, 0), (0xa004ffe0, 0),
   (0xa004ffe8, 0), (0xa004fff0, 0), (0xa004fff8, 0),
   (EvmAsm.Codegen.U256MulU64Be.accBase, 0),
   (EvmAsm.Codegen.U256MulU64Be.accBase + 8, 0),
   (EvmAsm.Codegen.U256MulU64Be.accBase + 8 + 8, 0),
   (EvmAsm.Codegen.U256MulU64Be.accBase + 8 + 8 + 8, 0),
   (EvmAsm.Codegen.U256MulU64Be.accBase + 8 + 8 + 8 + 8, 0)]

def k73_decr_witness_fixed_reg_heap : (Reg × Word) → PartialState :=
  fun p => PartialState.singletonReg p.1 p.2

def k73_decr_witness_owned_reg_heap : Reg → PartialState :=
  fun r => PartialState.singletonReg r 0

def k73_decr_witness_mem_heap : Word → PartialState :=
  fun a => PartialState.singletonMem a 0

def k73_decr_witness_fixed_mem_heap : (Word × Word) → PartialState :=
  fun p => PartialState.singletonMem p.1 p.2

def k73_decr_witness_fixed_reg_state : PartialState :=
  k73_decr_witness_fixed_regs.foldr
    (fun p acc => (k73_decr_witness_fixed_reg_heap p).union acc)
    PartialState.empty

def k73_decr_witness_owned_reg_state : PartialState :=
  k73_decr_witness_owned_regs.foldr
    (fun r acc => (k73_decr_witness_owned_reg_heap r).union acc)
    PartialState.empty

def k73_decr_witness_owned_mem_state : PartialState :=
  k73_decr_witness_owned_mems.foldr
    (fun a acc => (k73_decr_witness_mem_heap a).union acc)
    PartialState.empty

def k73_decr_witness_fixed_mem_state : PartialState :=
  k73_decr_witness_fixed_mems.foldr
    (fun p acc => (k73_decr_witness_fixed_mem_heap p).union acc)
    PartialState.empty

def k73_decr_witness_reg_state : PartialState :=
  k73_decr_witness_fixed_reg_state.union k73_decr_witness_owned_reg_state

def k73_decr_witness_mem_state : PartialState :=
  k73_decr_witness_owned_mem_state.union k73_decr_witness_fixed_mem_state

def k73_decr_witness_state : PartialState :=
  k73_decr_witness_reg_state.union k73_decr_witness_mem_state

private theorem singleton_reg_disjoint {r1 r2 : Reg} {v1 v2 : Word}
    (hne : r1 ≠ r2) :
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

private theorem singleton_reg_mem_disjoint {r : Reg} {v a : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a 0) := by
  refine ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl,
    fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem singleton_mem_disjoint {a1 a2 v1 v2 : Word}
    (hne : a1 ≠ a2) :
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

private theorem pair_assertion {P Q : Assertion} {hP hQ : PartialState}
    (hp : P hP) (hq : Q hQ) (hd : hP.Disjoint hQ) :
    (P ** Q) (hP.union hQ) :=
  ⟨hP, hQ, hd, rfl, hp, hq⟩

private theorem k73_decr_witness_fixed_regs_sat :
    (k73_decr_witness_fixed_regs.foldr
      (fun p acc => (p.1 ↦ᵣ p.2) ** acc) empAssertion)
      k73_decr_witness_fixed_reg_state := by
  apply sepConj_foldr_satisfiable
  · intro p hp
    simp [k73_decr_witness_fixed_reg_heap, regIs]
  · exact List.Pairwise.imp
      (fun {p q} hpq => singleton_reg_disjoint hpq) (by decide)

private theorem k73_decr_witness_owned_regs_sat :
    (k73_decr_witness_owned_regs.foldr
      (fun r acc => regOwn r ** acc) empAssertion)
      k73_decr_witness_owned_reg_state := by
  apply sepConj_foldr_satisfiable
  · intro r hr
    exact ⟨0, by simp [k73_decr_witness_owned_reg_heap, regIs]⟩
  · exact List.Pairwise.imp
      (fun {r1 r2} hpq => singleton_reg_disjoint hpq) (by decide)

private theorem k73_decr_witness_owned_mems_sat :
    (k73_decr_witness_owned_mems.foldr
      (fun a acc => memOwn a ** acc) empAssertion)
      k73_decr_witness_owned_mem_state := by
  apply sepConj_foldr_satisfiable
  · intro a ha
    exact ⟨0, rfl, by
      apply isValidDwordAccess_of_toNat
      · simp [k73_decr_witness_owned_mems] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      · simp [k73_decr_witness_owned_mems] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide⟩
  · exact List.Pairwise.imp
      (fun {a1 a2} hpq => singleton_mem_disjoint hpq) (by decide)

private theorem k73_decr_witness_fixed_mems_sat :
    (k73_decr_witness_fixed_mems.foldr
      (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion)
      k73_decr_witness_fixed_mem_state := by
  apply sepConj_foldr_satisfiable
  · intro p hp
    refine ⟨rfl, ?_⟩
    apply isValidDwordAccess_of_toNat
    · simp [k73_decr_witness_fixed_mems] at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · simp [k73_decr_witness_fixed_mems] at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · exact List.Pairwise.imp
      (fun {a1 a2} hpq => singleton_mem_disjoint hpq) (by decide)

private theorem k73_decr_witness_regs_sat :
    ((k73_decr_witness_fixed_regs.foldr
        (fun p acc => (p.1 ↦ᵣ p.2) ** acc) empAssertion) **
      (k73_decr_witness_owned_regs.foldr
        (fun r acc => regOwn r ** acc) empAssertion))
      k73_decr_witness_reg_state := by
  exact sepConj_foldr_cross_satisfiable
    (atomL := fun p : Reg × Word => p.1 ↦ᵣ p.2)
    (heapL := k73_decr_witness_fixed_reg_heap)
    (xs := k73_decr_witness_fixed_regs)
    (atomR := fun r : Reg => regOwn r)
    (heapR := k73_decr_witness_owned_reg_heap)
    (ys := k73_decr_witness_owned_regs)
    k73_decr_witness_fixed_regs_sat k73_decr_witness_owned_regs_sat (by
      intro p hp r hr
      apply singleton_reg_disjoint
      simp [k73_decr_witness_fixed_regs] at hp
      simp [k73_decr_witness_owned_regs] at hr
      aesop)

private theorem k73_decr_witness_mems_sat :
    ((k73_decr_witness_owned_mems.foldr
        (fun a acc => memOwn a ** acc) empAssertion) **
      (k73_decr_witness_fixed_mems.foldr
        (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion))
      k73_decr_witness_mem_state := by
  exact sepConj_foldr_cross_satisfiable
    (atomL := fun a : Word => memOwn a)
    (heapL := k73_decr_witness_mem_heap)
    (xs := k73_decr_witness_owned_mems)
    (atomR := fun p : Word × Word => p.1 ↦ₘ p.2)
    (heapR := k73_decr_witness_fixed_mem_heap)
    (ys := k73_decr_witness_fixed_mems)
    k73_decr_witness_owned_mems_sat k73_decr_witness_fixed_mems_sat (by
      intro a ha b hb
      apply singleton_mem_disjoint
      simp [k73_decr_witness_owned_mems] at ha
      simp [k73_decr_witness_fixed_mems] at hb
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)

private theorem k73_decr_witness_all_sat :
    (((k73_decr_witness_fixed_regs.foldr
        (fun p acc => (p.1 ↦ᵣ p.2) ** acc) empAssertion) **
      (k73_decr_witness_owned_regs.foldr
        (fun r acc => regOwn r ** acc) empAssertion)) **
      ((k73_decr_witness_owned_mems.foldr
        (fun a acc => memOwn a ** acc) empAssertion) **
      (k73_decr_witness_fixed_mems.foldr
        (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion)))
      k73_decr_witness_state := by
  exact pair_assertion k73_decr_witness_regs_sat k73_decr_witness_mems_sat (by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r
      right
      simp [k73_decr_witness_mem_state, k73_decr_witness_owned_mem_state,
        k73_decr_witness_fixed_mem_state, k73_decr_witness_owned_mems,
        k73_decr_witness_fixed_mems, k73_decr_witness_mem_heap,
        k73_decr_witness_fixed_mem_heap, PartialState.union,
        PartialState.empty, PartialState.singletonMem]
    · intro a
      left
      simp [k73_decr_witness_reg_state, k73_decr_witness_fixed_reg_state,
        k73_decr_witness_owned_reg_state, k73_decr_witness_fixed_regs,
        k73_decr_witness_owned_regs, k73_decr_witness_fixed_reg_heap,
        k73_decr_witness_owned_reg_heap, PartialState.union,
        PartialState.empty, PartialState.singletonReg]
    · intro a
      exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl)

/-- The complete decrease-arm precondition is jointly satisfiable.

    The witness uses 32-byte header/parent/output regions, a 40-byte
    multiply accumulator window, all K73/K74 frame cells, and the non-empty
    `memOwn 0x300000` tail.  Thus this is an inhabitance check for the exact
    applied precondition, not a per-atom or `emp` argument. -/
theorem k73_decr_pre_inhabited :
    ∃ s : PartialState,
      ((.x1 ↦ᵣ (HeaderValidateBaseFeeSpec.H + 40)) **
        k73PreRest (0xa0050038 : Word) (0xa0050000 : Word)
          (0x200000 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
          (10000 : Word) (2500 : Word) (0x200100 : Word)
          (List.replicate 32 0) (List.replicate 32 0) (List.replicate 32 0)
          (HeaderValidateBaseFeeSpec.H + 40) (0 : Word)
          (k73_decr_env (0xa0050000 : Word)
            (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
            (List.replicate 40 0) (memOwn 0x300000))) s := by
  refine ⟨k73_decr_witness_state, ?_⟩
  have hAll := k73_decr_witness_all_sat
  have hshape :
      ((.x1 ↦ᵣ (HeaderValidateBaseFeeSpec.H + 40)) **
        k73PreRest (0xa0050038 : Word) (0xa0050000 : Word)
          (0x200000 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
          (10000 : Word) (2500 : Word) (0x200100 : Word)
          (List.replicate 32 0) (List.replicate 32 0) (List.replicate 32 0)
          (HeaderValidateBaseFeeSpec.H + 40) (0 : Word)
          (k73_decr_env (0xa0050000 : Word)
            (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
            (List.replicate 40 0) (memOwn 0x300000))) =
      (((k73_decr_witness_fixed_regs.foldr
          (fun p acc => (p.1 ↦ᵣ p.2) ** acc) empAssertion) **
        (k73_decr_witness_owned_regs.foldr
          (fun r acc => regOwn r ** acc) empAssertion)) **
        ((k73_decr_witness_owned_mems.foldr
          (fun a acc => memOwn a ** acc) empAssertion) **
        (k73_decr_witness_fixed_mems.foldr
          (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion))) := by
    dsimp [k73PreRest, k73_decr_env, k74FlatFrame, frameSlotsOwn,
      frameSlotsSaved, EvmAsm.Codegen.HeaderBaseFeeSpec.k73Frame,
      hvbfFrame, hvbfSaved, EvmAsm.Codegen.U256MulU64Be.frameSlots,
      bytesRegion, bytesRegionAux, k73_decr_witness_fixed_regs,
      k73_decr_witness_owned_regs, k73_decr_witness_owned_mems,
      k73_decr_witness_fixed_mems]
    simp [sepConj_assoc', sepConj_emp_right', signExtend12,
      packBytes, getByteAt, packDword, GuestAddrs.hvbf_expected,
      GuestAddrs.u256m_acc]
    xperm_cert_eq
  exact hshape ▸ hAll

end EvmAsm.Codegen.HeaderValidateBaseFeeCompositionWitness
