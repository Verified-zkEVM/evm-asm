/-
  EvmAsm.Rv32.SepLogic

  Real separation logic with PartialState (partial register + memory + PC maps).

  Following Kennedy et al. (2013), we treat registers, memory locations, and the
  program counter as separable resources. An assertion is a predicate on partial
  states. The separating conjunction (P ** Q) holds when the partial state can be
  split into two disjoint sub-states satisfying P and Q respectively.

  The bridge to full machine states is via `holdsFor`: an assertion holds for a
  machine state when there exists a compatible partial state satisfying it.
-/

import EvmAsm.Rv32.Basic

namespace EvmAsm

-- ============================================================================
-- PartialState: partial register + memory + PC maps
-- ============================================================================

/-- A partial state tracks ownership of registers, memory, code, and optionally the PC.
    Each field is an option: `some v` means "we own this resource and it has value v",
    `none` means "we don't own this resource". -/
structure PartialState where
  regs : Reg → Option Word
  mem  : Addr → Option Word
  code : Addr → Option Instr := fun _ => none
  pc   : Option Word
  publicValues : Option (List (BitVec 8)) := none
  privateInput : Option (List (BitVec 8)) := none

namespace PartialState

/-- The empty partial state: owns nothing. -/
def empty : PartialState := ⟨fun _ => none, fun _ => none, fun _ => none, none, none, none⟩

/-- A partial state owning just one register. -/
def singletonReg (r : Reg) (v : Word) : PartialState where
  regs := fun r' => if r' == r then some v else none
  mem  := fun _ => none
  code := fun _ => none
  pc   := none
  publicValues := none
  privateInput := none

/-- A partial state owning just one memory cell. -/
def singletonMem (a : Addr) (v : Word) : PartialState where
  regs := fun _ => none
  mem  := fun a' => if a' == a then some v else none
  code := fun _ => none
  pc   := none
  publicValues := none
  privateInput := none

/-- A partial state owning just one code location. -/
def singletonCode (a : Addr) (i : Instr) : PartialState where
  regs := fun _ => none
  mem  := fun _ => none
  code := fun a' => if a' == a then some i else none
  pc   := none
  publicValues := none
  privateInput := none

/-- A partial state owning just the PC. -/
def singletonPC (v : Word) : PartialState where
  regs := fun _ => none
  mem  := fun _ => none
  code := fun _ => none
  pc   := some v
  publicValues := none
  privateInput := none

/-- A partial state owning just the public values. -/
def singletonPublicValues (vals : List (BitVec 8)) : PartialState where
  regs := fun _ => none
  mem  := fun _ => none
  code := fun _ => none
  pc   := none
  publicValues := some vals
  privateInput := none

/-- A partial state owning just the private input. -/
def singletonPrivateInput (vals : List (BitVec 8)) : PartialState where
  regs := fun _ => none
  mem  := fun _ => none
  code := fun _ => none
  pc   := none
  publicValues := none
  privateInput := some vals

/-- Two partial states are disjoint if they don't own the same resources. -/
def Disjoint (h1 h2 : PartialState) : Prop :=
  (∀ r, h1.regs r = none ∨ h2.regs r = none) ∧
  (∀ a, h1.mem a = none ∨ h2.mem a = none) ∧
  (∀ a, h1.code a = none ∨ h2.code a = none) ∧
  (h1.pc = none ∨ h2.pc = none) ∧
  (h1.publicValues = none ∨ h2.publicValues = none) ∧
  (h1.privateInput = none ∨ h2.privateInput = none)

/-- Merge two partial states (left-biased on each resource). -/
def union (h1 h2 : PartialState) : PartialState where
  regs := fun r => match h1.regs r with | some v => some v | none => h2.regs r
  mem  := fun a => match h1.mem a with | some v => some v | none => h2.mem a
  code := fun a => match h1.code a with | some v => some v | none => h2.code a
  pc   := match h1.pc with | some v => some v | none => h2.pc
  publicValues := match h1.publicValues with | some v => some v | none => h2.publicValues
  privateInput := match h1.privateInput with | some v => some v | none => h2.privateInput

/-- A partial state is compatible with a machine state if every owned
    resource has the correct value. -/
def CompatibleWith (h : PartialState) (s : MachineState) : Prop :=
  (∀ r v, h.regs r = some v → s.getReg r = v) ∧
  (∀ a v, h.mem a = some v → s.getMem a = v) ∧
  (∀ a i, h.code a = some i → s.code a = some i) ∧
  (∀ v, h.pc = some v → s.pc = v) ∧
  (∀ v, h.publicValues = some v → s.publicValues = v) ∧
  (∀ v, h.privateInput = some v → s.privateInput = v)

-- ============================================================================
-- Disjoint lemmas
-- ============================================================================

theorem Disjoint.symm {h1 h2 : PartialState} (hd : h1.Disjoint h2) :
    h2.Disjoint h1 := by
  obtain ⟨hr, hm, hc, hpc, hpv, hpi⟩ := hd
  exact ⟨fun r => (hr r).symm, fun a => (hm a).symm, fun a => (hc a).symm, hpc.symm, hpv.symm, hpi.symm⟩

theorem Disjoint_empty_left (h : PartialState) : empty.Disjoint h := by
  exact ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

theorem Disjoint_empty_right (h : PartialState) : h.Disjoint empty := by
  exact (Disjoint_empty_left h).symm

-- ============================================================================
-- Union lemmas
-- ============================================================================

theorem union_empty_left (h : PartialState) : empty.union h = h := by
  simp [union, empty]

theorem union_self (h : PartialState) : h.union h = h := by
  obtain ⟨regs, mem, code, pc, publicValues, privateInput⟩ := h
  simp only [union, PartialState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext r; cases regs r <;> rfl
  · funext a; cases mem a <;> rfl
  · funext a; cases code a <;> rfl
  · cases pc <;> rfl
  · cases publicValues <;> rfl
  · cases privateInput <;> rfl

theorem union_empty_right (h : PartialState) : h.union empty = h := by
  simp only [union, empty]
  obtain ⟨regs, mem, code, pc, publicValues, privateInput⟩ := h
  simp only [PartialState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext r; cases regs r <;> rfl
  · funext a; cases mem a <;> rfl
  · funext a; cases code a <;> rfl
  · cases pc <;> rfl
  · cases publicValues <;> rfl
  · cases privateInput <;> rfl

theorem union_comm_of_disjoint {h1 h2 : PartialState} (hd : h1.Disjoint h2) :
    h1.union h2 = h2.union h1 := by
  obtain ⟨hr, hm, hc, hpc, hpv, hpi⟩ := hd
  simp only [union, PartialState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext r
    cases hv1 : h1.regs r <;> cases hv2 : h2.regs r <;> simp
    · have := hr r; rw [hv1, hv2] at this; simp at this
  · funext a
    cases hv1 : h1.mem a <;> cases hv2 : h2.mem a <;> simp
    · have := hm a; rw [hv1, hv2] at this; simp at this
  · funext a
    cases hv1 : h1.code a <;> cases hv2 : h2.code a <;> simp
    · have := hc a; rw [hv1, hv2] at this; simp at this
  · cases hv1 : h1.pc <;> cases hv2 : h2.pc <;> simp
    · have := hpc; rw [hv1, hv2] at this; simp at this
  · cases hv1 : h1.publicValues <;> cases hv2 : h2.publicValues <;> simp
    · have := hpv; rw [hv1, hv2] at this; simp at this
  · cases hv1 : h1.privateInput <;> cases hv2 : h2.privateInput <;> simp
    · have := hpi; rw [hv1, hv2] at this; simp at this

-- ============================================================================
-- CompatibleWith lemmas
-- ============================================================================

theorem CompatibleWith_empty (s : MachineState) : empty.CompatibleWith s := by
  exact ⟨fun _ _ h => by simp [empty] at h, fun _ _ h => by simp [empty] at h,
         fun _ _ h => by simp [empty] at h, fun _ h => by simp [empty] at h,
         fun _ h => by simp [empty] at h, fun _ h => by simp [empty] at h⟩

theorem CompatibleWith_singletonReg (r : Reg) (v : Word) (s : MachineState) :
    (singletonReg r v).CompatibleWith s ↔ s.getReg r = v := by
  constructor
  · intro ⟨hr, _, _, _, _, _⟩
    have : (if r == r then some v else none) = some v := by simp
    exact hr r v this
  · intro heq
    refine ⟨fun r' v' h => ?_, fun _ _ h => by simp [singletonReg] at h,
            fun _ _ h => by simp [singletonReg] at h,
            fun _ h => by simp [singletonReg] at h,
            fun _ h => by simp [singletonReg] at h,
            fun _ h => by simp [singletonReg] at h⟩
    simp only [singletonReg] at h
    split at h
    · rename_i heq'; rw [beq_iff_eq] at heq'; subst heq'
      simp at h; rw [← h]; exact heq
    · simp at h

theorem CompatibleWith_singletonMem (a : Addr) (v : Word) (s : MachineState) :
    (singletonMem a v).CompatibleWith s ↔ s.getMem a = v := by
  constructor
  · intro ⟨_, hm, _, _, _, _⟩
    have : (if a == a then some v else none) = some v := by simp
    exact hm a v this
  · intro heq
    refine ⟨fun _ _ h => by simp [singletonMem] at h,
            fun a' v' h => ?_,
            fun _ _ h => by simp [singletonMem] at h,
            fun _ h => by simp [singletonMem] at h,
            fun _ h => by simp [singletonMem] at h,
            fun _ h => by simp [singletonMem] at h⟩
    simp only [singletonMem] at h
    split at h
    · rename_i heq'; rw [beq_iff_eq] at heq'; subst heq'
      simp at h; rw [← h]; exact heq
    · simp at h

theorem CompatibleWith_singletonPC (v : Word) (s : MachineState) :
    (singletonPC v).CompatibleWith s ↔ s.pc = v := by
  constructor
  · intro ⟨_, _, _, hpc, _, _⟩
    exact hpc v rfl
  · intro heq
    exact ⟨fun _ _ h => by simp [singletonPC] at h,
           fun _ _ h => by simp [singletonPC] at h,
           fun _ _ h => by simp [singletonPC] at h,
           fun v' h => by simp [singletonPC] at h; rw [← h]; exact heq,
           fun _ h => by simp [singletonPC] at h,
           fun _ h => by simp [singletonPC] at h⟩

theorem CompatibleWith_union {h1 h2 : PartialState} {s : MachineState}
    (hd : h1.Disjoint h2) :
    (h1.union h2).CompatibleWith s ↔ h1.CompatibleWith s ∧ h2.CompatibleWith s := by
  obtain ⟨hdr, hdm, hdc, hdpc, hdpv, hdpi⟩ := hd
  constructor
  · intro ⟨hr, hm, hc, hpc, hpv, hpi⟩
    constructor
    · refine ⟨fun r v hv => ?_, fun a v hv => ?_, fun a i hv => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
      · exact hr r v (by simp [union, hv])
      · exact hm a v (by simp [union, hv])
      · exact hc a i (by simp [union, hv])
      · exact hpc v (by simp [union, hv])
      · exact hpv v (by simp [union, hv])
      · exact hpi v (by simp [union, hv])
    · refine ⟨fun r v hv => ?_, fun a v hv => ?_, fun a i hv => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
      · have := hdr r
        rcases this with h1none | h2none
        · exact hr r v (by show (union h1 h2).regs r = some v; simp only [union]; rw [h1none]; exact hv)
        · rw [h2none] at hv; simp at hv
      · have := hdm a
        rcases this with h1none | h2none
        · exact hm a v (by show (union h1 h2).mem a = some v; simp only [union]; rw [h1none]; exact hv)
        · rw [h2none] at hv; simp at hv
      · have := hdc a
        rcases this with h1none | h2none
        · exact hc a i (by show (union h1 h2).code a = some i; simp only [union]; rw [h1none]; exact hv)
        · rw [h2none] at hv; simp at hv
      · rcases hdpc with h1none | h2none
        · exact hpc v (by show (union h1 h2).pc = some v; simp only [union]; rw [h1none]; exact hv)
        · rw [h2none] at hv; simp at hv
      · rcases hdpv with h1none | h2none
        · exact hpv v (by show (union h1 h2).publicValues = some v; simp only [union]; rw [h1none]; exact hv)
        · rw [h2none] at hv; simp at hv
      · rcases hdpi with h1none | h2none
        · exact hpi v (by show (union h1 h2).privateInput = some v; simp only [union]; rw [h1none]; exact hv)
        · rw [h2none] at hv; simp at hv
  · intro ⟨⟨hr1, hm1, hc1, hpc1, hpv1, hpi1⟩, ⟨hr2, hm2, hc2, hpc2, hpv2, hpi2⟩⟩
    refine ⟨fun r v hv => ?_, fun a v hv => ?_, fun a i hv => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
    · simp only [union] at hv
      cases h1r : h1.regs r <;> simp [h1r] at hv
      · exact hr2 r v hv
      · exact hr1 r v (by rw [← hv]; exact h1r)
    · simp only [union] at hv
      cases h1m : h1.mem a <;> simp [h1m] at hv
      · exact hm2 a v hv
      · exact hm1 a v (by rw [← hv]; exact h1m)
    · simp only [union] at hv
      cases h1c : h1.code a <;> simp [h1c] at hv
      · exact hc2 a i hv
      · exact hc1 a i (by rw [← hv]; exact h1c)
    · simp only [union] at hv
      cases h1pc : h1.pc <;> simp [h1pc] at hv
      · exact hpc2 v hv
      · exact hpc1 v (by rw [← hv]; exact h1pc)
    · simp only [union] at hv
      cases h1pv : h1.publicValues <;> simp [h1pv] at hv
      · exact hpv2 v hv
      · exact hpv1 v (by rw [← hv]; exact h1pv)
    · simp only [union] at hv
      cases h1pi : h1.privateInput <;> simp [h1pi] at hv
      · exact hpi2 v hv
      · exact hpi1 v (by rw [← hv]; exact h1pi)

end PartialState

-- ============================================================================
-- Assertion type
-- ============================================================================

/-- An assertion is a predicate on partial states. -/
def Assertion := PartialState → Prop

instance : Inhabited Assertion := ⟨fun _ => True⟩

-- ============================================================================
-- Basic Assertions
-- ============================================================================

/-- Register r holds value v. -/
def regIs (r : Reg) (v : Word) : Assertion :=
  fun h => h = PartialState.singletonReg r v

/-- Notation: r ↦ᵣ v means register r holds value v. -/
notation:50 r " ↦ᵣ " v => regIs r v

/-- Memory at address a holds value v. -/
def memIs (a : Addr) (v : Word) : Assertion :=
  fun h => h = PartialState.singletonMem a v

/-- Notation: a ↦ₘ v means memory at address a holds value v. -/
notation:50 a " ↦ₘ " v => memIs a v

/-- PC holds value v. -/
def pcIs (v : Word) : Assertion :=
  fun h => h = PartialState.singletonPC v

/-- Ownership of register r with unspecified value. -/
def regOwn (r : Reg) : Assertion := fun h => ∃ v, regIs r v h

/-- Ownership of memory at address a with unspecified value. -/
def memOwn (a : Addr) : Assertion := fun h => ∃ v, memIs a v h

/-- The empty assertion: owns no resources. -/
def empAssertion : Assertion := fun h => h = PartialState.empty

-- ============================================================================
-- Separating Conjunction
-- ============================================================================

/-- Separating conjunction: P ** Q holds on h when h can be split into
    two disjoint sub-states h1, h2 with P h1 and Q h2. -/
def sepConj (P Q : Assertion) : Assertion :=
  fun h => ∃ h1 h2, h1.Disjoint h2 ∧ h1.union h2 = h ∧ P h1 ∧ Q h2

/-- Notation: P ** Q is the separating conjunction. -/
infixr:35 " ** " => sepConj

/-- Separating implication (magic wand). -/
def sepImpl (P Q : Assertion) : Assertion :=
  fun h => ∀ h', h.Disjoint h' → P h' → Q (h.union h')

infixr:30 " -* " => sepImpl

-- ============================================================================
-- holdsFor: bridge from Assertion to MachineState
-- ============================================================================

/-- An assertion holds for a machine state when there exists a compatible
    partial state satisfying it. -/
def Assertion.holdsFor (P : Assertion) (s : MachineState) : Prop :=
  ∃ h : PartialState, h.CompatibleWith s ∧ P h

-- ============================================================================
-- pcFree: assertions that don't own the PC
-- ============================================================================

/-- An assertion is PC-free if it doesn't own/constrain the PC. -/
def Assertion.pcFree (P : Assertion) : Prop := ∀ h, P h → h.pc = none

-- ============================================================================
-- holdsFor simplification lemmas
-- ============================================================================

@[simp]
theorem holdsFor_regIs (r : Reg) (v : Word) (s : MachineState) :
    (regIs r v).holdsFor s ↔ s.getReg r = v := by
  simp only [Assertion.holdsFor, regIs]
  constructor
  · rintro ⟨h, hcompat, rfl⟩
    exact (PartialState.CompatibleWith_singletonReg r v s).mp hcompat
  · intro heq
    exact ⟨_, (PartialState.CompatibleWith_singletonReg r v s).mpr heq, rfl⟩

@[simp]
theorem holdsFor_memIs (a : Addr) (v : Word) (s : MachineState) :
    (memIs a v).holdsFor s ↔ s.getMem a = v := by
  simp only [Assertion.holdsFor, memIs]
  constructor
  · rintro ⟨h, hcompat, rfl⟩
    exact (PartialState.CompatibleWith_singletonMem a v s).mp hcompat
  · intro heq
    exact ⟨_, (PartialState.CompatibleWith_singletonMem a v s).mpr heq, rfl⟩

@[simp]
theorem holdsFor_pcIs (v : Word) (s : MachineState) :
    (pcIs v).holdsFor s ↔ s.pc = v := by
  simp only [Assertion.holdsFor, pcIs]
  constructor
  · rintro ⟨h, hcompat, rfl⟩
    exact (PartialState.CompatibleWith_singletonPC v s).mp hcompat
  · intro heq
    exact ⟨_, (PartialState.CompatibleWith_singletonPC v s).mpr heq, rfl⟩

@[simp]
theorem holdsFor_emp (s : MachineState) :
    empAssertion.holdsFor s ↔ True := by
  simp only [Assertion.holdsFor, empAssertion, iff_true]
  exact ⟨PartialState.empty, PartialState.CompatibleWith_empty s, rfl⟩

@[simp]
theorem holdsFor_regOwn (r : Reg) (s : MachineState) :
    (regOwn r).holdsFor s ↔ True := by
  simp only [iff_true, regOwn, Assertion.holdsFor]
  exact ⟨_, (PartialState.CompatibleWith_singletonReg r (s.getReg r) s).mpr rfl,
         s.getReg r, rfl⟩

@[simp]
theorem holdsFor_memOwn (a : Addr) (s : MachineState) :
    (memOwn a).holdsFor s ↔ True := by
  simp only [iff_true, memOwn, Assertion.holdsFor]
  exact ⟨_, (PartialState.CompatibleWith_singletonMem a (s.getMem a) s).mpr rfl,
         s.getMem a, rfl⟩

theorem regIs_implies_regOwn (r : Reg) (v : Word) :
    ∀ h, regIs r v h → regOwn r h := fun _ hp => ⟨v, hp⟩

theorem memIs_implies_memOwn (a : Addr) (v : Word) :
    ∀ h, memIs a v h → memOwn a h := fun _ hp => ⟨v, hp⟩

-- ============================================================================
-- holdsFor for sepConj of atoms
-- ============================================================================

private theorem singletonReg_disjoint_singletonReg {r1 r2 : Reg} {v1 v2 : Word}
    (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint (PartialState.singletonReg r2 v2) := by
  refine ⟨fun r => ?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  simp only [PartialState.singletonReg]
  by_cases h1 : r == r1
  · simp [h1]
    by_cases h2 : r == r2
    · exfalso
      have := beq_iff_eq.mp h1
      have := beq_iff_eq.mp h2
      exact hne (by rw [← ‹r = r1›, ← ‹r = r2›])
    · exact fun hr2 => h2 (beq_iff_eq.mpr hr2)
  · simp [h1]

theorem singletonReg_disjoint_imp_ne {r1 r2 : Reg} {v1 v2 : Word}
    (hd : (PartialState.singletonReg r1 v1).Disjoint (PartialState.singletonReg r2 v2)) :
    r1 ≠ r2 := by
  intro heq
  subst heq
  -- Both singletons claim ownership of the same register
  obtain ⟨hdr, _, _, _, _, _⟩ := hd
  have := hdr r1
  simp only [PartialState.singletonReg] at this
  simp only [beq_self_eq_true, ite_true] at this
  -- this says: some v1 = none ∨ some v2 = none, which is false
  cases this <;> simp_all

private theorem singletonReg_disjoint_singletonMem (r : Reg) (v : Word) (a : Addr) (w : Word) :
    (PartialState.singletonReg r v).Disjoint (PartialState.singletonMem a w) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

theorem holdsFor_sepConj_regIs_regIs {r1 r2 : Reg} {v1 v2 : Word} {s : MachineState}
    (hne : r1 ≠ r2) :
    ((regIs r1 v1) ** (regIs r2 v2)).holdsFor s ↔ s.getReg r1 = v1 ∧ s.getReg r2 = v2 := by
  constructor
  · rintro ⟨h, hcompat, h1, h2, hd, hunion, hp1, hp2⟩
    rw [regIs] at hp1 hp2; subst hp1; subst hp2
    rw [← hunion] at hcompat
    rw [PartialState.CompatibleWith_union hd] at hcompat
    exact ⟨(PartialState.CompatibleWith_singletonReg r1 v1 s).mp hcompat.1,
           (PartialState.CompatibleWith_singletonReg r2 v2 s).mp hcompat.2⟩
  · intro ⟨h1, h2⟩
    have hd := singletonReg_disjoint_singletonReg hne (v1 := v1) (v2 := v2)
    exact ⟨_, (PartialState.CompatibleWith_union hd).mpr
      ⟨(PartialState.CompatibleWith_singletonReg r1 v1 s).mpr h1,
       (PartialState.CompatibleWith_singletonReg r2 v2 s).mpr h2⟩,
      _, _, hd, rfl, rfl, rfl⟩

theorem holdsFor_sepConj_regIs_memIs {r : Reg} {v : Word} {a : Addr} {w : Word}
    {s : MachineState} :
    ((regIs r v) ** (memIs a w)).holdsFor s ↔ s.getReg r = v ∧ s.getMem a = w := by
  constructor
  · rintro ⟨h, hcompat, h1, h2, hd, hunion, hp1, hp2⟩
    rw [regIs] at hp1; rw [memIs] at hp2; subst hp1; subst hp2
    rw [← hunion] at hcompat
    rw [PartialState.CompatibleWith_union hd] at hcompat
    exact ⟨(PartialState.CompatibleWith_singletonReg r v s).mp hcompat.1,
           (PartialState.CompatibleWith_singletonMem a w s).mp hcompat.2⟩
  · intro ⟨h1, h2⟩
    have hd := singletonReg_disjoint_singletonMem r v a w
    exact ⟨_, (PartialState.CompatibleWith_union hd).mpr
      ⟨(PartialState.CompatibleWith_singletonReg r v s).mpr h1,
       (PartialState.CompatibleWith_singletonMem a w s).mpr h2⟩,
      _, _, hd, rfl, rfl, rfl⟩

-- ============================================================================
-- holdsFor projection for sepConj
-- ============================================================================

/-- If (P ** Q) holds for s, then P holds for s. -/
theorem holdsFor_sepConj_elim_left {P Q : Assertion} {s : MachineState}
    (h : (P ** Q).holdsFor s) : P.holdsFor s := by
  obtain ⟨hp, hcompat, h1, h2, hd, hunion, hp1, _⟩ := h
  rw [← hunion] at hcompat
  exact ⟨h1, (PartialState.CompatibleWith_union hd).mp hcompat |>.1, hp1⟩

/-- If (P ** Q) holds for s, then Q holds for s. -/
theorem holdsFor_sepConj_elim_right {P Q : Assertion} {s : MachineState}
    (h : (P ** Q).holdsFor s) : Q.holdsFor s := by
  obtain ⟨hp, hcompat, h1, h2, hd, hunion, _, hq2⟩ := h
  rw [← hunion] at hcompat
  exact ⟨h2, (PartialState.CompatibleWith_union hd).mp hcompat |>.2, hq2⟩

-- ============================================================================
-- pcFree lemmas
-- ============================================================================

theorem pcFree_regIs (r : Reg) (v : Word) : (regIs r v).pcFree := by
  intro h hp; rw [regIs] at hp; subst hp; rfl

theorem pcFree_memIs (a : Addr) (v : Word) : (memIs a v).pcFree := by
  intro h hp; rw [memIs] at hp; subst hp; rfl

theorem pcFree_regOwn (r : Reg) : (regOwn r).pcFree := by
  intro h ⟨v, hv⟩; exact pcFree_regIs r v h hv

theorem pcFree_memOwn (a : Addr) : (memOwn a).pcFree := by
  intro h ⟨v, hv⟩; exact pcFree_memIs a v h hv

theorem pcFree_emp : empAssertion.pcFree := by
  intro h hp; rw [empAssertion] at hp; subst hp; rfl

theorem pcFree_sepConj {P Q : Assertion} (hP : P.pcFree) (hQ : Q.pcFree) :
    (P ** Q).pcFree := by
  intro h ⟨h1, h2, hd, hunion, hp1, hp2⟩
  have hp1 := hP h1 hp1
  have hp2 := hQ h2 hp2
  rw [← hunion]; simp [PartialState.union, hp1, hp2]

/-- Type class for PC-free assertions. Synthesized automatically by instance search.
    Kernel verifies each instance once; uses are opaque references (no inline nesting). -/
class Assertion.PCFree (P : Assertion) : Prop where
  proof : P.pcFree

instance : Assertion.PCFree empAssertion             := ⟨pcFree_emp⟩
instance : Assertion.PCFree (r ↦ᵣ v)                := ⟨pcFree_regIs r v⟩
instance : Assertion.PCFree (a ↦ₘ v)                := ⟨pcFree_memIs a v⟩
instance : Assertion.PCFree (regOwn r)               := ⟨pcFree_regOwn r⟩
instance : Assertion.PCFree (memOwn a)               := ⟨pcFree_memOwn a⟩
@[reducible, instance] def instPCFreeSepConj [hP : Assertion.PCFree P] [hQ : Assertion.PCFree Q] :
    Assertion.PCFree (P ** Q)                        := ⟨pcFree_sepConj hP.proof hQ.proof⟩

-- ============================================================================
-- Algebraic properties
-- ============================================================================

theorem sepConj_comm (P Q : Assertion) :
    ∀ h, (P ** Q) h ↔ (Q ** P) h := by
  intro h
  constructor
  · intro ⟨h1, h2, hd, hunion, hp1, hp2⟩
    exact ⟨h2, h1, hd.symm, by rw [PartialState.union_comm_of_disjoint hd.symm, hunion], hp2, hp1⟩
  · intro ⟨h1, h2, hd, hunion, hp1, hp2⟩
    exact ⟨h2, h1, hd.symm, by rw [PartialState.union_comm_of_disjoint hd.symm, hunion], hp2, hp1⟩

theorem sepConj_emp_left (P : Assertion) :
    ∀ h, (empAssertion ** P) h ↔ P h := by
  intro h
  constructor
  · intro ⟨h1, h2, _, hunion, hemp, hp⟩
    rw [empAssertion] at hemp; subst hemp
    rw [PartialState.union_empty_left] at hunion
    rw [← hunion]; exact hp
  · intro hp
    exact ⟨PartialState.empty, h, PartialState.Disjoint_empty_left h,
           PartialState.union_empty_left h, rfl, hp⟩

theorem sepConj_emp_right (P : Assertion) :
    ∀ h, (P ** empAssertion) h ↔ P h := by
  intro h
  rw [sepConj_comm]
  exact sepConj_emp_left P h

/-- Helper: union is associative. -/
private theorem union_assoc (h1 h2 h3 : PartialState) :
    (h1.union h2).union h3 = h1.union (h2.union h3) := by
  simp only [PartialState.union, PartialState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext r; cases h1.regs r <;> simp
  · funext a; cases h1.mem a <;> simp
  · funext a; cases h1.code a <;> simp
  · cases h1.pc <;> simp
  · cases h1.publicValues <;> simp
  · cases h1.privateInput <;> simp

/-- Helper: extract disjointness facts from nested unions. -/
theorem disjoint_of_union_disjoint_right
    {h1 h2 h3 : PartialState} (hd12 : h1.Disjoint h2)
    (hd_union_3 : (h1.union h2).Disjoint h3) :
    h2.Disjoint h3 := by
  obtain ⟨hdr, hdm, hdc, hdpc, hdpv, hdpi⟩ := hd_union_3
  obtain ⟨hdr12, hdm12, hdc12, hdpc12, hdpv12, hdpi12⟩ := hd12
  refine ⟨fun r => ?_, fun a => ?_, fun a => ?_, ?_, ?_, ?_⟩
  · rcases hdr12 r with h1none | h2none
    · have h := hdr r
      simp only [PartialState.union] at h
      rw [h1none] at h; simp at h; exact h
    · exact Or.inl h2none
  · rcases hdm12 a with h1none | h2none
    · have h := hdm a
      simp only [PartialState.union] at h
      rw [h1none] at h; simp at h; exact h
    · exact Or.inl h2none
  · rcases hdc12 a with h1none | h2none
    · have h := hdc a
      simp only [PartialState.union] at h
      rw [h1none] at h; simp at h; exact h
    · exact Or.inl h2none
  · rcases hdpc12 with h1none | h2none
    · have h := hdpc
      simp only [PartialState.union] at h
      rw [h1none] at h; simp at h; exact h
    · exact Or.inl h2none
  · rcases hdpv12 with h1none | h2none
    · have h := hdpv
      simp only [PartialState.union] at h
      rw [h1none] at h; simp at h; exact h
    · exact Or.inl h2none
  · rcases hdpi12 with h1none | h2none
    · have h := hdpi
      simp only [PartialState.union] at h
      rw [h1none] at h; simp at h; exact h
    · exact Or.inl h2none

private theorem disjoint_of_union_disjoint_left
    {h1 h2 h3 : PartialState} (hd12 : h1.Disjoint h2)
    (hd_union_3 : (h1.union h2).Disjoint h3) :
    h1.Disjoint (h2.union h3) := by
  obtain ⟨hdr, hdm, hdc, hdpc, hdpv, hdpi⟩ := hd_union_3
  obtain ⟨hdr12, hdm12, hdc12, hdpc12, hdpv12, hdpi12⟩ := hd12
  refine ⟨fun r => ?_, fun a => ?_, fun a => ?_, ?_, ?_, ?_⟩
  · rcases hdr12 r with h1none | h2none
    · exact Or.inl h1none
    · have h := hdr r
      simp only [PartialState.union] at h
      cases h1r : h1.regs r
      · exact Or.inl rfl
      · rw [h1r] at h; simp at h
        right; show (PartialState.union h2 h3).regs r = none
        simp only [PartialState.union]; rw [h2none]; exact h
  · rcases hdm12 a with h1none | h2none
    · exact Or.inl h1none
    · have h := hdm a
      simp only [PartialState.union] at h
      cases h1m : h1.mem a
      · exact Or.inl rfl
      · rw [h1m] at h; simp at h
        right; show (PartialState.union h2 h3).mem a = none
        simp only [PartialState.union]; rw [h2none]; exact h
  · rcases hdc12 a with h1none | h2none
    · exact Or.inl h1none
    · have h := hdc a
      simp only [PartialState.union] at h
      cases h1c : h1.code a
      · exact Or.inl rfl
      · rw [h1c] at h; simp at h
        right; show (PartialState.union h2 h3).code a = none
        simp only [PartialState.union]; rw [h2none]; exact h
  · rcases hdpc12 with h1none | h2none
    · exact Or.inl h1none
    · have h := hdpc
      simp only [PartialState.union] at h
      cases h1pc : h1.pc
      · exact Or.inl rfl
      · rw [h1pc] at h; simp at h
        right; show (PartialState.union h2 h3).pc = none
        simp only [PartialState.union]; rw [h2none]; exact h
  · rcases hdpv12 with h1none | h2none
    · exact Or.inl h1none
    · have h := hdpv
      simp only [PartialState.union] at h
      cases h1pv : h1.publicValues
      · exact Or.inl rfl
      · rw [h1pv] at h; simp at h
        right; show (PartialState.union h2 h3).publicValues = none
        simp only [PartialState.union]; rw [h2none]; exact h
  · rcases hdpi12 with h1none | h2none
    · exact Or.inl h1none
    · have h := hdpi
      simp only [PartialState.union] at h
      cases h1pi : h1.privateInput
      · exact Or.inl rfl
      · rw [h1pi] at h; simp at h
        right; show (PartialState.union h2 h3).privateInput = none
        simp only [PartialState.union]; rw [h2none]; exact h

theorem disjoint_left_of_disjoint_union_right
    {h1 h2 h3 : PartialState} (hd1_23 : h1.Disjoint (h2.union h3)) :
    h1.Disjoint h2 := by
  obtain ⟨hdr, hdm, hdc, hdpc, hdpv, hdpi⟩ := hd1_23
  refine ⟨fun r => ?_, fun a => ?_, fun a => ?_, ?_, ?_, ?_⟩
  · rcases (hdr r) with h1none | h23none
    · exact Or.inl h1none
    · simp only [PartialState.union] at h23none
      cases h2r : h2.regs r <;> rw [h2r] at h23none <;> simp at h23none
      exact Or.inr rfl
  · rcases (hdm a) with h1none | h23none
    · exact Or.inl h1none
    · simp only [PartialState.union] at h23none
      cases h2m : h2.mem a <;> rw [h2m] at h23none <;> simp at h23none
      exact Or.inr rfl
  · rcases (hdc a) with h1none | h23none
    · exact Or.inl h1none
    · simp only [PartialState.union] at h23none
      cases h2c : h2.code a <;> rw [h2c] at h23none <;> simp at h23none
      exact Or.inr rfl
  · rcases hdpc with h1none | h23none
    · exact Or.inl h1none
    · simp only [PartialState.union] at h23none
      cases h2pc : h2.pc <;> rw [h2pc] at h23none <;> simp at h23none
      exact Or.inr rfl
  · rcases hdpv with h1none | h23none
    · exact Or.inl h1none
    · simp only [PartialState.union] at h23none
      cases h2pv : h2.publicValues <;> rw [h2pv] at h23none <;> simp at h23none
      exact Or.inr rfl
  · rcases hdpi with h1none | h23none
    · exact Or.inl h1none
    · simp only [PartialState.union] at h23none
      cases h2pi : h2.privateInput <;> rw [h2pi] at h23none <;> simp at h23none
      exact Or.inr rfl

private theorem disjoint_union_left_of_disjoint_union_right
    {h1 h2 h3 : PartialState} (hd23 : h2.Disjoint h3)
    (hd1_23 : h1.Disjoint (h2.union h3)) :
    (h1.union h2).Disjoint h3 := by
  obtain ⟨hdr, hdm, hdc, hdpc, hdpv, hdpi⟩ := hd1_23
  obtain ⟨hdr23, hdm23, hdc23, hdpc23, hdpv23, hdpi23⟩ := hd23
  refine ⟨fun r => ?_, fun a => ?_, fun a => ?_, ?_, ?_, ?_⟩
  · rcases hdr23 r with h2none | h3none
    · have h := hdr r
      simp only [PartialState.union] at h
      rw [h2none] at h; simp at h
      rcases h with h1none | h3none
      · left; show (PartialState.union h1 h2).regs r = none
        simp only [PartialState.union]; rw [h1none]; simp [h2none]
      · exact Or.inr h3none
    · exact Or.inr h3none
  · rcases hdm23 a with h2none | h3none
    · have h := hdm a
      simp only [PartialState.union] at h
      rw [h2none] at h; simp at h
      rcases h with h1none | h3none
      · left; show (PartialState.union h1 h2).mem a = none
        simp only [PartialState.union]; rw [h1none]; simp [h2none]
      · exact Or.inr h3none
    · exact Or.inr h3none
  · rcases hdc23 a with h2none | h3none
    · have h := hdc a
      simp only [PartialState.union] at h
      rw [h2none] at h; simp at h
      rcases h with h1none | h3none
      · left; show (PartialState.union h1 h2).code a = none
        simp only [PartialState.union]; rw [h1none]; simp [h2none]
      · exact Or.inr h3none
    · exact Or.inr h3none
  · rcases hdpc23 with h2none | h3none
    · have h := hdpc
      simp only [PartialState.union] at h
      rw [h2none] at h; simp at h
      rcases h with h1none | h3none
      · left; show (PartialState.union h1 h2).pc = none
        simp only [PartialState.union]; rw [h1none]; simp [h2none]
      · exact Or.inr h3none
    · exact Or.inr h3none
  · rcases hdpv23 with h2none | h3none
    · have h := hdpv
      simp only [PartialState.union] at h
      rw [h2none] at h; simp at h
      rcases h with h1none | h3none
      · left; show (PartialState.union h1 h2).publicValues = none
        simp only [PartialState.union]; rw [h1none]; simp [h2none]
      · exact Or.inr h3none
    · exact Or.inr h3none
  · rcases hdpi23 with h2none | h3none
    · have h := hdpi
      simp only [PartialState.union] at h
      rw [h2none] at h; simp at h
      rcases h with h1none | h3none
      · left; show (PartialState.union h1 h2).privateInput = none
        simp only [PartialState.union]; rw [h1none]; simp [h2none]
      · exact Or.inr h3none
    · exact Or.inr h3none

theorem sepConj_assoc (P Q R : Assertion) :
    ∀ h, ((P ** Q) ** R) h ↔ (P ** (Q ** R)) h := by
  intro h
  constructor
  · intro ⟨h12, h3, hd12_3, hunion12_3, ⟨h1, h2, hd12, hunion12, hp, hq⟩, hr⟩
    subst hunion12
    have hd2_3 := disjoint_of_union_disjoint_right hd12 hd12_3
    have hd1_23 := disjoint_of_union_disjoint_left hd12 hd12_3
    exact ⟨h1, h2.union h3, hd1_23,
           by rw [← union_assoc, hunion12_3],
           hp, h2, h3, hd2_3, rfl, hq, hr⟩
  · intro ⟨h1, h23, hd1_23, hunion1_23, hp, h2, h3, hd23, hunion23, hq, hr⟩
    subst hunion23
    have hd12 := disjoint_left_of_disjoint_union_right hd1_23
    have hd12_3 := disjoint_union_left_of_disjoint_union_right hd23 hd1_23
    exact ⟨h1.union h2, h3, hd12_3,
           by rw [union_assoc, hunion1_23],
           ⟨h1, h2, hd12, rfl, hp, hq⟩, hr⟩

/-- Commutativity of separating conjunction at the holdsFor level. -/
theorem holdsFor_sepConj_comm {P Q : Assertion} {s : MachineState} :
    (P ** Q).holdsFor s ↔ (Q ** P).holdsFor s := by
  constructor
  · intro ⟨h, hcompat, hP⟩
    exact ⟨h, hcompat, (sepConj_comm P Q h).mp hP⟩
  · intro ⟨h, hcompat, hP⟩
    exact ⟨h, hcompat, (sepConj_comm Q P h).mp hP⟩

/-- Associativity of separating conjunction at the holdsFor level. -/
theorem holdsFor_sepConj_assoc {P Q R : Assertion} {s : MachineState} :
    ((P ** Q) ** R).holdsFor s ↔ (P ** (Q ** R)).holdsFor s := by
  constructor
  · intro ⟨h, hcompat, hP⟩
    exact ⟨h, hcompat, (sepConj_assoc P Q R h).mp hP⟩
  · intro ⟨h, hcompat, hP⟩
    exact ⟨h, hcompat, (sepConj_assoc P Q R h).mpr hP⟩

/-- Swap the two inner assertions: ((P ** Q) ** R) ↔ ((Q ** P) ** R). -/
theorem holdsFor_sepConj_swap_inner {P Q R : Assertion} {s : MachineState} :
    ((P ** Q) ** R).holdsFor s ↔ ((Q ** P) ** R).holdsFor s := by
  constructor <;> intro ⟨h, hcompat, hP⟩
  · -- Forward: ((P ** Q) ** R) → ((Q ** P) ** R)
    obtain ⟨h12, h3, hd12_3, hunion12_3, hPQ, hR⟩ := hP
    have hQP := (sepConj_comm P Q h12).mp hPQ
    exact ⟨h, hcompat, h12, h3, hd12_3, hunion12_3, hQP, hR⟩
  · -- Backward: ((Q ** P) ** R) → ((P ** Q) ** R)
    obtain ⟨h12, h3, hd12_3, hunion12_3, hQP, hR⟩ := hP
    have hPQ := (sepConj_comm Q P h12).mp hQP
    exact ⟨h, hcompat, h12, h3, hd12_3, hunion12_3, hPQ, hR⟩

/-- Pull the second inner assertion out: ((P ** Q) ** R) ↔ (Q ** (P ** R)). -/
theorem holdsFor_sepConj_pull_second {P Q R : Assertion} {s : MachineState} :
    ((P ** Q) ** R).holdsFor s ↔ (Q ** (P ** R)).holdsFor s := by
  constructor <;> intro ⟨h, hcompat, hP⟩
  · -- Forward: ((P ** Q) ** R) → (Q ** (P ** R))
    -- Step 1: Apply assoc to get (P ** (Q ** R))
    have h1 := (sepConj_assoc P Q R h).mp hP
    -- Step 2: Apply comm to get ((Q ** R) ** P)
    have h2 := (sepConj_comm P (Q ** R) h).mp h1
    -- Step 3: Apply assoc to get (Q ** (R ** P))
    have h3 := (sepConj_assoc Q R P h).mp h2
    -- Step 4: Apply comm on inner to get (Q ** (P ** R))
    obtain ⟨h_Q, h_RP, hd, hunion, hQ, hRP⟩ := h3
    have hPR := (sepConj_comm R P h_RP).mp hRP
    exact ⟨h, hcompat, h_Q, h_RP, hd, hunion, hQ, hPR⟩
  · -- Backward: (Q ** (P ** R)) → ((P ** Q) ** R)
    -- Reverse the steps
    obtain ⟨h_Q, h_PR, hd, hunion, hQ, hPR⟩ := hP
    -- Step 1: Apply comm on inner to get (Q ** (R ** P))
    have hRP := (sepConj_comm P R h_PR).mp hPR
    have h3 : (Q ** (R ** P)) h := ⟨h_Q, h_PR, hd, hunion, hQ, hRP⟩
    -- Step 2: Apply assoc backwards to get ((Q ** R) ** P)
    have h2 := (sepConj_assoc Q R P h).mpr h3
    -- Step 3: Apply comm to get (P ** (Q ** R))
    have h1 := (sepConj_comm ((Q ** R)) P h).mp h2
    -- Step 4: Apply assoc backwards to get ((P ** Q) ** R)
    have hP' := (sepConj_assoc P Q R h).mpr h1
    exact ⟨h, hcompat, hP'⟩

/-- Pull the first inner assertion out: ((P ** Q) ** R) ↔ (P ** (Q ** R)).
    This is just holdsFor_sepConj_assoc, provided for symmetry. -/
theorem holdsFor_sepConj_pull_first {P Q R : Assertion} {s : MachineState} :
    ((P ** Q) ** R).holdsFor s ↔ (P ** (Q ** R)).holdsFor s :=
  holdsFor_sepConj_assoc

-- ============================================================================
-- Pure modality: lifting Prop into Assertion
-- ============================================================================

/-- The pure assertion: holds on the empty partial state when P is true.
    This is the standard separation logic ⌜P⌝ modality. -/
def pure (P : Prop) : Assertion :=
  fun h => h = PartialState.empty ∧ P

/-- Notation: ⌜P⌝ is the pure assertion lifting P into the assertion language. -/
notation "⌜" P "⌝" => EvmAsm.pure P

@[simp]
theorem holdsFor_pure (P : Prop) (s : MachineState) :
    (⌜P⌝).holdsFor s ↔ P := by
  simp only [Assertion.holdsFor, pure]
  constructor
  · rintro ⟨h, _, rfl, hp⟩; exact hp
  · intro hp; exact ⟨PartialState.empty, PartialState.CompatibleWith_empty s, rfl, hp⟩

theorem pcFree_pure (P : Prop) : (⌜P⌝).pcFree := by
  intro h ⟨hemp, _⟩; subst hemp; rfl

instance (P : Prop) : Assertion.PCFree (⌜P⌝) := ⟨pcFree_pure P⟩

theorem pure_true_eq_emp : ⌜True⌝ = empAssertion := by
  funext h; simp [pure, empAssertion]

theorem sepConj_pure_left (P : Prop) (Q : Assertion) :
    ∀ h, (⌜P⌝ ** Q) h ↔ P ∧ Q h := by
  intro h
  constructor
  · intro ⟨h1, h2, _, hunion, ⟨hemp, hp⟩, hq⟩
    subst hemp; rw [PartialState.union_empty_left] at hunion
    exact ⟨hp, hunion ▸ hq⟩
  · intro ⟨hp, hq⟩
    exact ⟨PartialState.empty, h, PartialState.Disjoint_empty_left h,
           PartialState.union_empty_left h, ⟨rfl, hp⟩, hq⟩

theorem sepConj_pure_right (P : Assertion) (Q : Prop) :
    ∀ h, (P ** ⌜Q⌝) h ↔ P h ∧ Q := by
  intro h
  rw [sepConj_comm]
  simp only [sepConj_pure_left]
  exact And.comm

-- ============================================================================
-- Logical combinators (preserved for backward compatibility)
-- ============================================================================

/-- Universal quantification over assertions. -/
def aForall {α : Type} (P : α → Assertion) : Assertion :=
  fun h => ∀ a, P a h

/-- Existential quantification over assertions. -/
def aExists {α : Type} (P : α → Assertion) : Assertion :=
  fun h => ∃ a, P a h

-- ============================================================================
-- publicValuesIs assertion
-- ============================================================================

/-- Public values stream equals a given list. -/
def publicValuesIs (vals : List (BitVec 8)) : Assertion :=
  fun h => h = PartialState.singletonPublicValues vals

-- ============================================================================
-- CompatibleWith / holdsFor for publicValuesIs
-- ============================================================================

namespace PartialState

theorem CompatibleWith_singletonPublicValues (vals : List (BitVec 8)) (s : MachineState) :
    (singletonPublicValues vals).CompatibleWith s ↔ s.publicValues = vals := by
  constructor
  · intro ⟨_, _, _, _, hpv, _⟩
    exact hpv vals rfl
  · intro heq
    exact ⟨fun _ _ h => by simp [singletonPublicValues] at h,
           fun _ _ h => by simp [singletonPublicValues] at h,
           fun _ _ h => by simp [singletonPublicValues] at h,
           fun _ h => by simp [singletonPublicValues] at h,
           fun v' h => by simp [singletonPublicValues] at h; rw [← h]; exact heq,
           fun _ h => by simp [singletonPublicValues] at h⟩

end PartialState

@[simp]
theorem holdsFor_publicValuesIs (vals : List (BitVec 8)) (s : MachineState) :
    (publicValuesIs vals).holdsFor s ↔ s.publicValues = vals := by
  simp only [Assertion.holdsFor, publicValuesIs]
  constructor
  · rintro ⟨h, hcompat, rfl⟩
    exact (PartialState.CompatibleWith_singletonPublicValues vals s).mp hcompat
  · intro heq
    exact ⟨_, (PartialState.CompatibleWith_singletonPublicValues vals s).mpr heq, rfl⟩

-- ============================================================================
-- pcFree for publicValuesIs
-- ============================================================================

theorem pcFree_publicValuesIs (vals : List (BitVec 8)) : (publicValuesIs vals).pcFree := by
  intro h hp; rw [publicValuesIs] at hp; subst hp; rfl

instance (vals : List (BitVec 8)) : Assertion.PCFree (publicValuesIs vals) :=
  ⟨pcFree_publicValuesIs vals⟩

-- ============================================================================
-- Disjointness lemmas for publicValuesIs composition
-- ============================================================================

private theorem singletonReg_disjoint_singletonPublicValues (r : Reg) (v : Word) (vals : List (BitVec 8)) :
    (PartialState.singletonReg r v).Disjoint (PartialState.singletonPublicValues vals) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem singletonMem_disjoint_singletonPublicValues (a : Addr) (v : Word) (vals : List (BitVec 8)) :
    (PartialState.singletonMem a v).Disjoint (PartialState.singletonPublicValues vals) := by
  exact ⟨fun _ => Or.inl rfl, fun _ => Or.inr rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

-- ============================================================================
-- holdsFor_sepConj convenience lemmas for publicValuesIs
-- ============================================================================

theorem holdsFor_sepConj_regIs_publicValuesIs {r : Reg} {v : Word}
    {vals : List (BitVec 8)} {s : MachineState} :
    ((regIs r v) ** (publicValuesIs vals)).holdsFor s ↔
      s.getReg r = v ∧ s.publicValues = vals := by
  constructor
  · rintro ⟨h, hcompat, h1, h2, hd, hunion, hp1, hp2⟩
    rw [regIs] at hp1; rw [publicValuesIs] at hp2; subst hp1; subst hp2
    rw [← hunion] at hcompat
    rw [PartialState.CompatibleWith_union hd] at hcompat
    exact ⟨(PartialState.CompatibleWith_singletonReg r v s).mp hcompat.1,
           (PartialState.CompatibleWith_singletonPublicValues vals s).mp hcompat.2⟩
  · intro ⟨h1, h2⟩
    have hd := singletonReg_disjoint_singletonPublicValues r v vals
    exact ⟨_, (PartialState.CompatibleWith_union hd).mpr
      ⟨(PartialState.CompatibleWith_singletonReg r v s).mpr h1,
       (PartialState.CompatibleWith_singletonPublicValues vals s).mpr h2⟩,
      _, _, hd, rfl, rfl, rfl⟩

-- ============================================================================
-- privateInputIs assertion
-- ============================================================================

/-- Private input stream equals a given list. -/
def privateInputIs (vals : List (BitVec 8)) : Assertion :=
  fun h => h = PartialState.singletonPrivateInput vals

-- ============================================================================
-- CompatibleWith / holdsFor for privateInputIs
-- ============================================================================

namespace PartialState

theorem CompatibleWith_singletonPrivateInput (vals : List (BitVec 8)) (s : MachineState) :
    (singletonPrivateInput vals).CompatibleWith s ↔ s.privateInput = vals := by
  constructor
  · intro ⟨_, _, _, _, _, hpi⟩
    exact hpi vals rfl
  · intro heq
    exact ⟨fun _ _ h => by simp [singletonPrivateInput] at h,
           fun _ _ h => by simp [singletonPrivateInput] at h,
           fun _ _ h => by simp [singletonPrivateInput] at h,
           fun _ h => by simp [singletonPrivateInput] at h,
           fun _ h => by simp [singletonPrivateInput] at h,
           fun v' h => by simp [singletonPrivateInput] at h; rw [← h]; exact heq⟩

end PartialState

@[simp]
theorem holdsFor_privateInputIs (vals : List (BitVec 8)) (s : MachineState) :
    (privateInputIs vals).holdsFor s ↔ s.privateInput = vals := by
  simp only [Assertion.holdsFor, privateInputIs]
  constructor
  · rintro ⟨h, hcompat, rfl⟩
    exact (PartialState.CompatibleWith_singletonPrivateInput vals s).mp hcompat
  · intro heq
    exact ⟨_, (PartialState.CompatibleWith_singletonPrivateInput vals s).mpr heq, rfl⟩

-- ============================================================================
-- pcFree for privateInputIs
-- ============================================================================

theorem pcFree_privateInputIs (vals : List (BitVec 8)) : (privateInputIs vals).pcFree := by
  intro h hp; rw [privateInputIs] at hp; subst hp; rfl

instance (vals : List (BitVec 8)) : Assertion.PCFree (privateInputIs vals) :=
  ⟨pcFree_privateInputIs vals⟩

-- ============================================================================
-- Disjointness lemmas for privateInputIs composition
-- ============================================================================

private theorem singletonReg_disjoint_singletonPrivateInput (r : Reg) (v : Word) (vals : List (BitVec 8)) :
    (PartialState.singletonReg r v).Disjoint (PartialState.singletonPrivateInput vals) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem singletonMem_disjoint_singletonPrivateInput (a : Addr) (v : Word) (vals : List (BitVec 8)) :
    (PartialState.singletonMem a v).Disjoint (PartialState.singletonPrivateInput vals) := by
  exact ⟨fun _ => Or.inl rfl, fun _ => Or.inr rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem singletonPublicValues_disjoint_singletonPrivateInput (pv : List (BitVec 8)) (pi : List (BitVec 8)) :
    (PartialState.singletonPublicValues pv).Disjoint (PartialState.singletonPrivateInput pi) := by
  exact ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inr rfl, Or.inl rfl⟩

-- ============================================================================
-- holdsFor_sepConj convenience lemmas for privateInputIs
-- ============================================================================

theorem holdsFor_sepConj_regIs_privateInputIs {r : Reg} {v : Word}
    {vals : List (BitVec 8)} {s : MachineState} :
    ((regIs r v) ** (privateInputIs vals)).holdsFor s ↔
      s.getReg r = v ∧ s.privateInput = vals := by
  constructor
  · rintro ⟨h, hcompat, h1, h2, hd, hunion, hp1, hp2⟩
    rw [regIs] at hp1; rw [privateInputIs] at hp2; subst hp1; subst hp2
    rw [← hunion] at hcompat
    rw [PartialState.CompatibleWith_union hd] at hcompat
    exact ⟨(PartialState.CompatibleWith_singletonReg r v s).mp hcompat.1,
           (PartialState.CompatibleWith_singletonPrivateInput vals s).mp hcompat.2⟩
  · intro ⟨h1, h2⟩
    have hd := singletonReg_disjoint_singletonPrivateInput r v vals
    exact ⟨_, (PartialState.CompatibleWith_union hd).mpr
      ⟨(PartialState.CompatibleWith_singletonReg r v s).mpr h1,
       (PartialState.CompatibleWith_singletonPrivateInput vals s).mpr h2⟩,
      _, _, hd, rfl, rfl, rfl⟩

-- ============================================================================
-- fullState: a partial state owning all tracked resources
-- ============================================================================

namespace PartialState

/-- A partial state that owns regs, mem, code, pc, publicValues, privateInput
    with values from a full machine state. -/
def fullState (s : MachineState) : PartialState where
  regs := fun r => some (s.getReg r)
  mem  := fun a => some (s.getMem a)
  code := fun _ => none
  pc   := some s.pc
  publicValues := some s.publicValues
  privateInput := some s.privateInput

theorem CompatibleWith_fullState (s : MachineState) :
    (fullState s).CompatibleWith s := by
  refine ⟨fun r v h => ?_, fun a v h => ?_, fun a i h => ?_, fun v h => ?_, fun v h => ?_, fun v h => ?_⟩ <;>
  simp [fullState] at h <;> exact h ▸ rfl

end PartialState

-- ============================================================================
-- stateIs: exact state match (up to committed field)
-- ============================================================================

/-- Assert that the machine state matches the target on all resources tracked by PartialState
    (registers, memory, PC, publicValues, privateInput). -/
def stateIs (target : MachineState) : Assertion :=
  fun h => h = PartialState.fullState target

@[simp]
theorem holdsFor_stateIs (target : MachineState) (s : MachineState) :
    (stateIs target).holdsFor s ↔
      (∀ r, s.getReg r = target.getReg r) ∧
      (∀ a, s.getMem a = target.getMem a) ∧
      s.pc = target.pc ∧
      s.publicValues = target.publicValues ∧
      s.privateInput = target.privateInput := by
  simp only [Assertion.holdsFor, stateIs]
  constructor
  · rintro ⟨h, hcompat, rfl⟩
    obtain ⟨hr, hm, hc, hpc, hpv, hpi⟩ := hcompat
    exact ⟨fun r => hr r (target.getReg r) (by simp [PartialState.fullState]),
           fun a => hm a (target.getMem a) (by simp [PartialState.fullState]),
           hpc target.pc (by simp [PartialState.fullState]),
           hpv target.publicValues (by simp [PartialState.fullState]),
           hpi target.privateInput (by simp [PartialState.fullState])⟩
  · intro ⟨hregs, hmem, hpc, hpv, hpi⟩
    refine ⟨PartialState.fullState target, ?_, rfl⟩
    refine ⟨fun r v hv => ?_, fun a v hv => ?_, fun a i hv => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
    · simp [PartialState.fullState] at hv; rw [hregs, hv]
    · simp [PartialState.fullState] at hv; rw [hmem, hv]
    · simp [PartialState.fullState] at hv
    · simp [PartialState.fullState] at hv; rw [hpc, hv]
    · simp [PartialState.fullState] at hv; rw [hpv, hv]
    · simp [PartialState.fullState] at hv; rw [hpi, hv]


-- ============================================================================
-- Frame preservation: CompatibleWith through state modifications
-- ============================================================================

namespace PartialState

/-- If a partial state doesn't own register r, then modifying r preserves compatibility. -/
theorem CompatibleWith_setReg {h : PartialState} {s : MachineState} {r : Reg} {v : Word}
    (hcompat : h.CompatibleWith s) (hnone : h.regs r = none) :
    h.CompatibleWith (s.setReg r v) := by
  obtain ⟨hr, hm, hc, hpc, hpv, hpi⟩ := hcompat
  refine ⟨fun r' v' hv => ?_, fun a' v' hv => by rw [MachineState.getMem_setReg]; exact hm a' v' hv,
         fun a' i' hv => by rw [MachineState.code_setReg]; exact hc a' i' hv,
         fun v' hv => by rw [MachineState.pc_setReg]; exact hpc v' hv,
         fun v' hv => by rw [MachineState.publicValues_setReg]; exact hpv v' hv,
         fun v' hv => by rw [MachineState.privateInput_setReg]; exact hpi v' hv⟩
  by_cases heq : r' = r
  · subst heq; rw [hnone] at hv; simp at hv
  · have := MachineState.getReg_setReg_ne s r r' v (Ne.symm heq)
    rw [this]; exact hr r' v' hv

/-- If a partial state doesn't own address a, then modifying mem[a] preserves compatibility. -/
theorem CompatibleWith_setMem {h : PartialState} {s : MachineState} {a : Addr} {v : Word}
    (hcompat : h.CompatibleWith s) (hnone : h.mem a = none) :
    h.CompatibleWith (s.setMem a v) := by
  obtain ⟨hr, hm, hc, hpc, hpv, hpi⟩ := hcompat
  refine ⟨fun r' v' hv => ?_, fun a' v' hv => ?_,
         fun a' i' hv => by rw [MachineState.code_setMem]; exact hc a' i' hv,
         fun v' hv => by rw [MachineState.pc_setMem]; exact hpc v' hv,
         fun v' hv => by rw [MachineState.publicValues_setMem]; exact hpv v' hv,
         fun v' hv => by rw [MachineState.privateInput_setMem]; exact hpi v' hv⟩
  · -- setMem doesn't change registers
    have : (s.setMem a v).getReg r' = s.getReg r' := by
      cases r' <;> simp [MachineState.getReg, MachineState.setMem]
    rw [this]; exact hr r' v' hv
  · by_cases heq : a' = a
    · subst heq; rw [hnone] at hv; exact absurd hv (by simp)
    · rw [MachineState.getMem_setMem_ne s a a' v heq]; exact hm a' v' hv

/-- If a partial state doesn't own the PC, then modifying PC preserves compatibility. -/
theorem CompatibleWith_setPC {h : PartialState} {s : MachineState}
    (hcompat : h.CompatibleWith s) (hnone : h.pc = none) :
    h.CompatibleWith (s.setPC v) := by
  obtain ⟨hr, hm, hc, hpc, hpv, hpi⟩ := hcompat
  refine ⟨fun r' v' hv => ?_, fun a' v' hv => ?_, fun a' i' hv => ?_, fun v' hv => ?_, fun v' hv => ?_, fun v' hv => ?_⟩
  · rw [MachineState.getReg_setPC]; exact hr r' v' hv
  · simp [MachineState.getMem, MachineState.setPC]; exact hm a' v' hv
  · rw [MachineState.code_setPC]; exact hc a' i' hv
  · rw [hnone] at hv; simp at hv
  · simp [MachineState.setPC] at *; exact hpv v' hv
  · simp [MachineState.setPC] at *; exact hpi v' hv

end PartialState

-- ============================================================================
-- Assertion-level monotonicity for sepConj
-- ============================================================================

theorem sepConj_mono_left {P P' Q : Assertion} (himpl : ∀ h, P h → P' h) :
    ∀ h, (P ** Q) h → (P' ** Q) h := by
  intro h ⟨h1, h2, hd, hunion, hp, hq⟩
  exact ⟨h1, h2, hd, hunion, himpl h1 hp, hq⟩

theorem sepConj_mono_right {P Q Q' : Assertion} (himpl : ∀ h, Q h → Q' h) :
    ∀ h, (P ** Q) h → (P ** Q') h := by
  intro h ⟨h1, h2, hd, hunion, hp, hq⟩
  exact ⟨h1, h2, hd, hunion, hp, himpl h2 hq⟩

theorem sepConj_mono {P P' Q Q' : Assertion} (hp : ∀ h, P h → P' h) (hq : ∀ h, Q h → Q' h) :
    ∀ h, (P ** Q) h → (P' ** Q') h := by
  intro h hpq
  exact sepConj_mono_right hq h (sepConj_mono_left hp h hpq)

-- ============================================================================
-- CompatibleWith decomposition through unions
-- ============================================================================

namespace PartialState

/-- If a union is compatible with a state, the left part is also compatible. -/
theorem CompatibleWith_union_elim_left {h1 h2 : PartialState} {s : MachineState}
    (hd : h1.Disjoint h2) (hcompat : (h1.union h2).CompatibleWith s) :
    h1.CompatibleWith s := by
  have ⟨hcompat1, hcompat2⟩ := (CompatibleWith_union hd).mp hcompat
  exact hcompat1

/-- If a union is compatible with a state, the right part is also compatible. -/
theorem CompatibleWith_union_elim_right {h1 h2 : PartialState} {s : MachineState}
    (hd : h1.Disjoint h2) (hcompat : (h1.union h2).CompatibleWith s) :
    h2.CompatibleWith s := by
  have ⟨hcompat1, hcompat2⟩ := (CompatibleWith_union hd).mp hcompat
  exact hcompat2

end PartialState

-- ============================================================================
-- Extracting register values from nested sepConj
-- ============================================================================

/-- Extract register values from a 3-way separating conjunction.
    Note: ** is right-associative, so this is (r1 ** (r2 ** r3)) -/
theorem holdsFor_sepConj_regIs_regIs_regIs {r1 r2 r3 : Reg} {v1 v2 v3 : Word}
    {s : MachineState}
    (h : ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3)).holdsFor s) :
    s.getReg r1 = v1 ∧ s.getReg r2 = v2 ∧ s.getReg r3 = v3 := by
  -- Structure is (r1 ** (r2 ** r3)) because ** is right-associative
  obtain ⟨hp, hcompat, hp_outer⟩ := h
  obtain ⟨h_r1, h_r23, hd_outer, hunion_outer, hp_r1, hp_r23⟩ := hp_outer
  obtain ⟨h_r2, h_r3, hd_inner, hunion_inner, hp_r2, hp_r3⟩ := hp_r23
  -- Now extract values using CompatibleWith
  simp only [regIs] at hp_r1 hp_r2 hp_r3
  subst hp_r1 hp_r2 hp_r3
  -- First split outer union, then split inner union
  rw [← hunion_outer] at hcompat
  have ⟨hc_r1, hc_r23⟩ := (PartialState.CompatibleWith_union hd_outer).mp hcompat
  rw [← hunion_inner] at hc_r23
  have ⟨hc_r2, hc_r3⟩ := (PartialState.CompatibleWith_union hd_inner).mp hc_r23
  exact ⟨(PartialState.CompatibleWith_singletonReg r1 v1 s).mp hc_r1,
         (PartialState.CompatibleWith_singletonReg r2 v2 s).mp hc_r2,
         (PartialState.CompatibleWith_singletonReg r3 v3 s).mp hc_r3⟩

-- ============================================================================
-- Preservation of holdsFor through setReg for disjoint registers
-- ============================================================================

/-- If a register assertion doesn't mention register r', it's preserved by setReg r'. -/
theorem holdsFor_regIs_setReg_other {r r' : Reg} {v v' : Word} {s : MachineState}
    (hne : r ≠ r')
    (h : (r ↦ᵣ v).holdsFor s) :
    (r ↦ᵣ v).holdsFor (s.setReg r' v') := by
  obtain ⟨h_partial, hcompat, hreg⟩ := h
  simp only [regIs] at hreg; subst hreg
  have hcompat' : (PartialState.singletonReg r v).CompatibleWith (s.setReg r' v') := by
    apply (PartialState.CompatibleWith_singletonReg r v (s.setReg r' v')).mpr
    rw [MachineState.getReg_setReg_ne s r' r v' hne.symm]
    exact (PartialState.CompatibleWith_singletonReg r v s).mp hcompat
  exact ⟨PartialState.singletonReg r v, hcompat', rfl⟩

/-- If a 2-register conjunction doesn't mention register r, it's preserved by setReg r. -/
theorem holdsFor_sepConj_regIs_regIs_setReg_other {r1 r2 r : Reg} {v1 v2 v' : Word}
    {s : MachineState} (hne1 : r1 ≠ r) (hne2 : r2 ≠ r)
    (h : ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2)).holdsFor s) :
    ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2)).holdsFor (s.setReg r v') := by
  obtain ⟨h_partial, hcompat, h1, h2, hd, hunion, hreg1, hreg2⟩ := h
  simp only [regIs] at hreg1 hreg2; subst hreg1; subst hreg2
  -- After substitution, hunion tells us h_partial = union of singletons
  rw [← hunion] at hcompat
  have hcompat' : (PartialState.singletonReg r1 v1).union (PartialState.singletonReg r2 v2) |>.CompatibleWith (s.setReg r v') := by
    apply (PartialState.CompatibleWith_union hd).mpr
    constructor
    · apply (PartialState.CompatibleWith_singletonReg r1 v1 (s.setReg r v')).mpr
      rw [MachineState.getReg_setReg_ne s r r1 v' hne1.symm]
      have ⟨hc1, _⟩ := (PartialState.CompatibleWith_union hd).mp hcompat
      exact (PartialState.CompatibleWith_singletonReg r1 v1 s).mp hc1
    · apply (PartialState.CompatibleWith_singletonReg r2 v2 (s.setReg r v')).mpr
      rw [MachineState.getReg_setReg_ne s r r2 v' hne2.symm]
      have ⟨_, hc2⟩ := (PartialState.CompatibleWith_union hd).mp hcompat
      exact (PartialState.CompatibleWith_singletonReg r2 v2 s).mp hc2
  exact ⟨(PartialState.singletonReg r1 v1).union (PartialState.singletonReg r2 v2), hcompat',
          PartialState.singletonReg r1 v1, PartialState.singletonReg r2 v2, hd, rfl, rfl, rfl⟩

-- ============================================================================
-- Frame-preserving register update
-- ============================================================================

/-- If `(r ↦ᵣ v) ** R` holds for `s`, then `(r ↦ᵣ v') ** R` holds for `s.setReg r v'`.
    The frame R is preserved because it's disjoint from the register being modified. -/
theorem holdsFor_sepConj_regIs_setReg {r : Reg} {v v' : Word} {R : Assertion}
    {s : MachineState} (hr_ne : r ≠ .x0)
    (hPR : ((r ↦ᵣ v) ** R).holdsFor s) :
    ((r ↦ᵣ v') ** R).holdsFor (s.setReg r v') := by
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hh1, hh2⟩ := hPR
  rw [regIs] at hh1; subst hh1; rw [← hunion] at hcompat
  -- h2 doesn't own r (from disjointness)
  have hr2 : h2.regs r = none := by
    rcases hdisj.1 r with h | h
    · simp [PartialState.singletonReg] at h
    · exact h
  -- Disjointness preserved (same register ownership shape)
  have hdisj' : (PartialState.singletonReg r v').Disjoint h2 := by
    refine ⟨fun r' => ?_, hdisj.2.1, hdisj.2.2.1, hdisj.2.2.2.1, hdisj.2.2.2.2⟩
    by_cases h : r' = r
    · subst h; exact Or.inr hr2
    · left; show (if r' == r then some v' else none) = none
      simp [h]
  -- Split old compatibility
  have ⟨hc1, hc2⟩ := (PartialState.CompatibleWith_union hdisj).mp hcompat
  -- singletonReg r v' compatible with s.setReg r v'
  have hc1' : (PartialState.singletonReg r v').CompatibleWith (s.setReg r v') := by
    refine ⟨fun r' w hr' => ?_,
            fun a w ha => by simp [PartialState.singletonReg] at ha,
            fun a i hi => by simp [PartialState.singletonReg] at hi,
            fun w hw => by simp [PartialState.singletonReg] at hw,
            fun w hw => by simp [PartialState.singletonReg] at hw,
            fun w hw => by simp [PartialState.singletonReg] at hw⟩
    simp only [PartialState.singletonReg] at hr'
    split at hr' <;> simp_all
    exact MachineState.getReg_setReg_eq _ _ _ hr_ne
  -- h2 compatible with s.setReg r v' (doesn't own r)
  have hc2' : h2.CompatibleWith (s.setReg r v') := PartialState.CompatibleWith_setReg hc2 hr2
  refine ⟨(PartialState.singletonReg r v').union h2, ?_, PartialState.singletonReg r v', h2, hdisj', rfl, rfl, hh2⟩
  exact (PartialState.CompatibleWith_union hdisj').mpr ⟨hc1', hc2'⟩

/-- Update the third register in a 3-way register conjunction.
    Note: ** is right-associative, so this is (r1 ** (r2 ** r3)) -/
theorem holdsFor_sepConj_regIs_regIs_regIs_update_third
    {r1 r2 r3 : Reg} {v1 v2 v3 v' : Word} {s : MachineState}
    (hr3_ne : r3 ≠ .x0)
    (h : ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3)).holdsFor s) :
    ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v')).holdsFor (s.setReg r3 v') := by
  -- Algebraic manipulation to get r3 first:
  -- (r1 ** (r2 ** r3)) -[assoc.mpr]→ ((r1 ** r2) ** r3) -[comm]→ (r3 ** (r1 ** r2))
  have h1 := holdsFor_sepConj_assoc.mpr h  -- ((r1 ** r2) ** r3).holdsFor s
  have h2 := holdsFor_sepConj_comm.mp h1  -- (r3 ** (r1 ** r2)).holdsFor s
  -- Apply setReg lemma
  have h3 := holdsFor_sepConj_regIs_setReg (v' := v') (R := ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2))) hr3_ne h2
  -- (r3' ** (r1 ** r2)).holdsFor (s.setReg r3 v')
  -- Reverse the rearrangement:
  -- (r3' ** (r1 ** r2)) -[comm]→ ((r1 ** r2) ** r3') -[assoc.mp]→ (r1 ** (r2 ** r3'))
  have h4 := holdsFor_sepConj_comm.mpr h3  -- ((r1 ** r2) ** r3').holdsFor (s.setReg r3 v')
  exact holdsFor_sepConj_assoc.mp h4  -- (r1 ** (r2 ** r3')).holdsFor (s.setReg r3 v')

-- ============================================================================
-- holdsFor preservation through setReg and setPC
-- ============================================================================

/-- setReg preserves holdsFor for any assertion whose partial state doesn't own the register. -/
theorem holdsFor_setReg {P : Assertion} {r : Reg} {v : Word} {s : MachineState}
    (hP_no_r : ∀ h, P h → h.regs r = none)
    (hP : P.holdsFor s) :
    P.holdsFor (s.setReg r v) := by
  obtain ⟨h, hcompat, hp⟩ := hP
  exact ⟨h, PartialState.CompatibleWith_setReg hcompat (hP_no_r h hp), hp⟩

theorem holdsFor_pcFree_setPC {P : Assertion} (hP : P.pcFree) (s : MachineState) (v : Word) :
    P.holdsFor s → P.holdsFor (s.setPC v) := by
  intro ⟨h, hcompat, hp⟩
  have hpc_none := hP h hp
  obtain ⟨hr, hm, hc, hpc, hpv, hpi⟩ := hcompat
  exact ⟨h, ⟨fun r' v' hv => by rw [MachineState.getReg_setPC]; exact hr r' v' hv,
              fun a' v' hv => by simp [MachineState.getMem, MachineState.setPC]; exact hm a' v' hv,
              fun a' i' hv => hc a' i' hv,
              fun v' hv => by rw [hpc_none] at hv; simp at hv,
              fun v' hv => by simp [MachineState.setPC] at *; exact hpv v' hv,
              fun v' hv => by simp [MachineState.setPC] at *; exact hpi v' hv⟩, hp⟩

/-- Update the third register in a 3-way conjunction with frame.
    This is the version with the CPS frame included. -/
theorem holdsFor_sepConj_regIs_regIs_regIs_setReg
    {r1 r2 r3 : Reg} {v1 v2 v3 v' : Word} {R : Assertion} {s : MachineState}
    (hr3_ne : r3 ≠ .x0)
    (h : (((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3)) ** R).holdsFor s) :
    (((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v')) ** R).holdsFor (s.setReg r3 v') := by
  -- Rearrange: ((r1 ** (r2 ** r3)) ** R) → ((r2 ** r3) ** (r1 ** R)) → (r3 ** (r2 ** (r1 ** R)))
  have h1 := holdsFor_sepConj_pull_second.mp h
  have h2 := holdsFor_sepConj_pull_second.mp h1
  -- Apply single-register frame update: (r3 ** frame) → (r3' ** frame) after setReg
  have h3 := holdsFor_sepConj_regIs_setReg (v' := v') hr3_ne h2
  -- Reverse: (r3' ** (r2 ** (r1 ** R))) → ((r2 ** r3') ** (r1 ** R)) → ((r1 ** (r2 ** r3')) ** R)
  have h4 := holdsFor_sepConj_pull_second.mpr h3
  exact holdsFor_sepConj_pull_second.mpr h4

-- ============================================================================
-- holdsFor preservation through setMem
-- ============================================================================

/-- If `(a ↦ₘ v) ** R` holds for `s`, then `(a ↦ₘ v') ** R` holds for `s.setMem a v'`.
    The frame R is preserved because it's disjoint from the memory being modified. -/
theorem holdsFor_sepConj_memIs_setMem {a : Addr} {v v' : Word} {R : Assertion}
    {s : MachineState}
    (hPR : ((a ↦ₘ v) ** R).holdsFor s) :
    ((a ↦ₘ v') ** R).holdsFor (s.setMem a v') := by
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hh1, hh2⟩ := hPR
  rw [memIs] at hh1; subst hh1; rw [← hunion] at hcompat
  -- h2 doesn't own address a (from disjointness)
  have ha2 : h2.mem a = none := by
    rcases hdisj.2.1 a with h | h
    · simp [PartialState.singletonMem] at h
    · exact h
  -- Disjointness preserved (same memory ownership shape)
  have hdisj' : (PartialState.singletonMem a v').Disjoint h2 := by
    refine ⟨hdisj.1, fun a' => ?_, hdisj.2.2.1, hdisj.2.2.2.1, hdisj.2.2.2.2⟩
    by_cases h : a' = a
    · subst h; exact Or.inr ha2
    · left; show (if a' == a then some v' else none) = none
      simp [h]
  -- Split old compatibility
  have ⟨hc1, hc2⟩ := (PartialState.CompatibleWith_union hdisj).mp hcompat
  -- singletonMem a v' compatible with s.setMem a v'
  have hc1' : (PartialState.singletonMem a v').CompatibleWith (s.setMem a v') := by
    refine ⟨fun r w hr => by simp [PartialState.singletonMem] at hr,
            fun a' w ha' => ?_,
            fun _ _ h => by simp [PartialState.singletonMem] at h,
            fun w hw => by simp [PartialState.singletonMem] at hw,
            fun w hw => by simp [PartialState.singletonMem] at hw,
            fun w hw => by simp [PartialState.singletonMem] at hw⟩
    simp only [PartialState.singletonMem] at ha'
    split at ha' <;> simp_all
  -- h2 compatible with s.setMem a v' (doesn't own a)
  have hc2' : h2.CompatibleWith (s.setMem a v') := PartialState.CompatibleWith_setMem hc2 ha2
  refine ⟨(PartialState.singletonMem a v').union h2, ?_, PartialState.singletonMem a v', h2, hdisj', rfl, rfl, hh2⟩
  exact (PartialState.CompatibleWith_union hdisj').mpr ⟨hc1', hc2'⟩

/-- setMem preserves holdsFor for any assertion whose partial state doesn't own the address. -/
theorem holdsFor_setMem {P : Assertion} {a : Addr} {v : Word} {s : MachineState}
    (hP_no_a : ∀ h, P h → h.mem a = none)
    (hP : P.holdsFor s) :
    P.holdsFor (s.setMem a v) := by
  obtain ⟨h, hcompat, hp⟩ := hP
  exact ⟨h, PartialState.CompatibleWith_setMem hcompat (hP_no_a h hp), hp⟩

-- ============================================================================
-- SubStateOf: partial state inclusion
-- ============================================================================

namespace PartialState

/-- h1 is a sub-state of h: every resource owned by h1 is also owned by h
    with the same value. h may own additional resources beyond h1. -/
def SubStateOf (h1 h : PartialState) : Prop :=
  (∀ r v, h1.regs r = some v → h.regs r = some v) ∧
  (∀ a v, h1.mem a = some v → h.mem a = some v) ∧
  (∀ a i, h1.code a = some i → h.code a = some i) ∧
  (∀ v, h1.pc = some v → h.pc = some v) ∧
  (∀ v, h1.publicValues = some v → h.publicValues = some v) ∧
  (∀ v, h1.privateInput = some v → h.privateInput = some v)

theorem SubStateOf_refl (h : PartialState) : h.SubStateOf h :=
  ⟨fun _ _ hv => hv, fun _ _ hv => hv, fun _ _ hv => hv, fun _ hv => hv,
   fun _ hv => hv, fun _ hv => hv⟩

theorem SubStateOf_empty (h : PartialState) : empty.SubStateOf h :=
  ⟨fun _ _ hv => by simp [empty] at hv, fun _ _ hv => by simp [empty] at hv,
   fun _ _ hv => by simp [empty] at hv,
   fun _ hv => by simp [empty] at hv, fun _ hv => by simp [empty] at hv,
   fun _ hv => by simp [empty] at hv⟩

theorem SubStateOf_CompatibleWith {h1 h : PartialState} {s : MachineState}
    (hsub : h1.SubStateOf h) (hcompat : h.CompatibleWith s) :
    h1.CompatibleWith s := by
  obtain ⟨sr, sm, sc, spc, spv, spi⟩ := hsub
  obtain ⟨hr, hm, hc, hpc, hpv, hpi⟩ := hcompat
  exact ⟨fun r v hv => hr r v (sr r v hv),
         fun a v hv => hm a v (sm a v hv),
         fun a i hv => hc a i (sc a i hv),
         fun v hv => hpc v (spc v hv),
         fun v hv => hpv v (spv v hv),
         fun v hv => hpi v (spi v hv)⟩

theorem SubStateOf_Disjoint {h1 h2 h3 : PartialState}
    (hd : h1.Disjoint h2) (hsub : h3.SubStateOf h1) :
    h3.Disjoint h2 := by
  obtain ⟨dr, dm, dc, dpc, dpv, dpi⟩ := hd
  obtain ⟨sr, sm, sc, spc, spv, spi⟩ := hsub
  refine ⟨fun r => ?_, fun a => ?_, fun a => ?_, ?_, ?_, ?_⟩
  -- registers
  · rcases dr r with h1none | h2none
    · left
      match h3eq : h3.regs r with
      | none => rfl
      | some v => exact absurd (sr r v h3eq) (by simp [h1none])
    · right; exact h2none
  -- memory
  · rcases dm a with h1none | h2none
    · left
      match h3eq : h3.mem a with
      | none => rfl
      | some v => exact absurd (sm a v h3eq) (by simp [h1none])
    · right; exact h2none
  -- code
  · rcases dc a with h1none | h2none
    · left
      match h3eq : h3.code a with
      | none => rfl
      | some i => exact absurd (sc a i h3eq) (by simp [h1none])
    · right; exact h2none
  -- pc
  · rcases dpc with h1none | h2none
    · left
      match h3eq : h3.pc with
      | none => rfl
      | some v => exact absurd (spc v h3eq) (by simp [h1none])
    · right; exact h2none
  -- publicValues
  · rcases dpv with h1none | h2none
    · left
      match h3eq : h3.publicValues with
      | none => rfl
      | some v => exact absurd (spv v h3eq) (by simp [h1none])
    · right; exact h2none
  -- privateInput
  · rcases dpi with h1none | h2none
    · left
      match h3eq : h3.privateInput with
      | none => rfl
      | some v => exact absurd (spi v h3eq) (by simp [h1none])
    · right; exact h2none

end PartialState

-- ============================================================================
-- AgreesWith: partial states that agree on overlapping resources
-- ============================================================================

namespace PartialState

/-- Two partial states agree on overlapping resources:
    where both own a value, those values are equal. -/
def AgreesWith (h1 h2 : PartialState) : Prop :=
  (∀ r v1 v2, h1.regs r = some v1 → h2.regs r = some v2 → v1 = v2) ∧
  (∀ a v1 v2, h1.mem a = some v1 → h2.mem a = some v2 → v1 = v2) ∧
  (∀ a i1 i2, h1.code a = some i1 → h2.code a = some i2 → i1 = i2) ∧
  (∀ v1 v2, h1.pc = some v1 → h2.pc = some v2 → v1 = v2) ∧
  (∀ v1 v2, h1.publicValues = some v1 → h2.publicValues = some v2 → v1 = v2) ∧
  (∀ v1 v2, h1.privateInput = some v1 → h2.privateInput = some v2 → v1 = v2)

theorem AgreesWith_refl (h : PartialState) : h.AgreesWith h :=
  ⟨fun _ _ _ h1 h2 => by rw [h1] at h2; exact Option.some.inj h2,
   fun _ _ _ h1 h2 => by rw [h1] at h2; exact Option.some.inj h2,
   fun _ _ _ h1 h2 => by rw [h1] at h2; exact Option.some.inj h2,
   fun _ _ h1 h2 => by rw [h1] at h2; exact Option.some.inj h2,
   fun _ _ h1 h2 => by rw [h1] at h2; exact Option.some.inj h2,
   fun _ _ h1 h2 => by rw [h1] at h2; exact Option.some.inj h2⟩

theorem AgreesWith_symm {h1 h2 : PartialState} (ha : h1.AgreesWith h2) : h2.AgreesWith h1 :=
  ⟨fun r v1 v2 h2r h1r => (ha.1 r v2 v1 h1r h2r).symm,
   fun a v1 v2 h2a h1a => (ha.2.1 a v2 v1 h1a h2a).symm,
   fun a i1 i2 h2c h1c => (ha.2.2.1 a i2 i1 h1c h2c).symm,
   fun v1 v2 h2pc h1pc => (ha.2.2.2.1 v2 v1 h1pc h2pc).symm,
   fun v1 v2 h2pv h1pv => (ha.2.2.2.2.1 v2 v1 h1pv h2pv).symm,
   fun v1 v2 h2pi h1pi => (ha.2.2.2.2.2 v2 v1 h1pi h2pi).symm⟩

/-- Disjoint states trivially agree (no overlapping fields). -/
theorem Disjoint_AgreesWith {h1 h2 : PartialState} (hd : h1.Disjoint h2) : h1.AgreesWith h2 := by
  obtain ⟨dr, dm, dc, dpc, dpv, dpi⟩ := hd
  exact ⟨fun r _ _ h1r h2r => by rcases dr r with h | h <;> simp [h] at h1r h2r,
         fun a _ _ h1a h2a => by rcases dm a with h | h <;> simp [h] at h1a h2a,
         fun a _ _ h1c h2c => by rcases dc a with h | h <;> simp [h] at h1c h2c,
         fun _ _ h1pc h2pc => by rcases dpc with h | h <;> simp [h] at h1pc h2pc,
         fun _ _ h1pv h2pv => by rcases dpv with h | h <;> simp [h] at h1pv h2pv,
         fun _ _ h1pi h2pi => by rcases dpi with h | h <;> simp [h] at h1pi h2pi⟩

/-- If h1 and h2 agree, h2 is compatible with any state that h1 ∪ h2 is compatible with. -/
theorem CompatibleWith_union_right {h1 h2 : PartialState} {s : MachineState}
    (ha : h1.AgreesWith h2) (hcompat : (h1.union h2).CompatibleWith s) :
    h2.CompatibleWith s := by
  obtain ⟨hr, hm, hc, hpc, hpv, hpi⟩ := hcompat
  obtain ⟨ar, am, ac, apc, apv, api⟩ := ha
  refine ⟨fun r v hv => ?_, fun a v hv => ?_, fun a i hv => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · -- h2.regs r = some v → s.getReg r = v
    have hu := hr r
    match h1eq : h1.regs r with
    | some w =>
      have := ar r w v h1eq hv; subst this
      exact hu w (by simp [union, h1eq])
    | none => exact hu v (by simp [union, h1eq, hv])
  · have hu := hm a
    match h1eq : h1.mem a with
    | some w =>
      have := am a w v h1eq hv; subst this
      exact hu w (by simp [union, h1eq])
    | none => exact hu v (by simp [union, h1eq, hv])
  · have hu := hc a
    match h1eq : h1.code a with
    | some j =>
      have := ac a j i h1eq hv; subst this
      exact hu j (by simp [union, h1eq])
    | none => exact hu i (by simp [union, h1eq, hv])
  · match h1eq : h1.pc with
    | some w =>
      have := apc w v h1eq hv; subst this
      exact hpc w (by simp [union, h1eq])
    | none => exact hpc v (by simp [union, h1eq, hv])
  · match h1eq : h1.publicValues with
    | some w =>
      have := apv w v h1eq hv; subst this
      exact hpv w (by simp [union, h1eq])
    | none => exact hpv v (by simp [union, h1eq, hv])
  · match h1eq : h1.privateInput with
    | some w =>
      have := api w v h1eq hv; subst this
      exact hpi w (by simp [union, h1eq])
    | none => exact hpi v (by simp [union, h1eq, hv])

/-- h1 is always compatible with any state that h1 ∪ h2 is compatible with. -/
theorem CompatibleWith_union_left {h1 h2 : PartialState} {s : MachineState}
    (hcompat : (h1.union h2).CompatibleWith s) :
    h1.CompatibleWith s := by
  obtain ⟨hr, hm, hc, hpc, hpv, hpi⟩ := hcompat
  exact ⟨fun r v hv => hr r v (by simp [union, hv]),
         fun a v hv => hm a v (by simp [union, hv]),
         fun a i hv => hc a i (by simp [union, hv]),
         fun v hv => hpc v (by simp [union, hv]),
         fun v hv => hpv v (by simp [union, hv]),
         fun v hv => hpi v (by simp [union, hv])⟩

end PartialState

-- ============================================================================
-- Additive conjunction (aAnd / //\\)
-- ============================================================================

/-- Additive conjunction: P ⋒ Q holds on h when h = h1 ∪ h2 for
    two partial states h1, h2 that agree on overlaps (AgreesWith),
    with P h1 and Q h2. Unlike **, h1 and h2 may share resources.
    This preserves pcFree: if both P and Q are pcFree, so is P ⋒ Q. -/
def aAnd (P Q : Assertion) : Assertion :=
  fun h => ∃ h1 h2, h1.AgreesWith h2 ∧ h1.union h2 = h ∧ P h1 ∧ Q h2

infixr:37 " ⋒ " => aAnd

theorem aAnd_holdsFor_elim {P Q : Assertion} {s : MachineState}
    (h : (P ⋒ Q).holdsFor s) : P.holdsFor s ∧ Q.holdsFor s := by
  obtain ⟨h, hcompat, h1, h2, ha, hunion, hp, hq⟩ := h
  rw [← hunion] at hcompat
  exact ⟨⟨h1, PartialState.CompatibleWith_union_left hcompat, hp⟩,
         ⟨h2, PartialState.CompatibleWith_union_right ha hcompat, hq⟩⟩

theorem aAnd_holdsFor_intro {P Q : Assertion} {s : MachineState} {h : PartialState}
    (hcompat : h.CompatibleWith s) (hp : P h) (hq : Q h) :
    (P ⋒ Q).holdsFor s :=
  ⟨h, hcompat, h, h, PartialState.AgreesWith_refl h,
    PartialState.union_self h, hp, hq⟩

theorem aAnd_left {P Q : Assertion} :
    ∀ h, (P ⋒ Q) h → ∃ h1, P h1 :=
  fun _ ⟨h1, _, _, _, hp, _⟩ => ⟨h1, hp⟩

theorem aAnd_right {P Q : Assertion} :
    ∀ h, (P ⋒ Q) h → ∃ h2, Q h2 :=
  fun _ ⟨_, h2, _, _, _, hq⟩ => ⟨h2, hq⟩

theorem aAnd_mono_left {P P' Q : Assertion} (himpl : ∀ h, P h → P' h) :
    ∀ h, (P ⋒ Q) h → (P' ⋒ Q) h := by
  intro h ⟨h1, h2, ha, hunion, hp, hq⟩
  exact ⟨h1, h2, ha, hunion, himpl h1 hp, hq⟩

theorem aAnd_mono_right {P Q Q' : Assertion} (himpl : ∀ h, Q h → Q' h) :
    ∀ h, (P ⋒ Q) h → (P ⋒ Q') h := by
  intro h ⟨h1, h2, ha, hunion, hp, hq⟩
  exact ⟨h1, h2, ha, hunion, hp, himpl h2 hq⟩

theorem pcFree_aAnd {P Q : Assertion} (hP : P.pcFree) (hQ : Q.pcFree) :
    (P ⋒ Q).pcFree := by
  intro h ⟨h1, h2, _, hunion, hp, hq⟩
  have h1pc := hP h1 hp
  have h2pc := hQ h2 hq
  rw [← hunion]; simp [PartialState.union, h1pc, h2pc]

@[reducible, instance] def instPCFreeAAnd [hP : Assertion.PCFree P] [hQ : Assertion.PCFree Q] :
    Assertion.PCFree (P ⋒ Q)                         := ⟨pcFree_aAnd hP.proof hQ.proof⟩

-- ============================================================================
-- liftPred: lift a MachineState predicate to Assertion
-- ============================================================================

/-- Lift a predicate on MachineState to an Assertion.
    `(liftPred P).holdsFor s ↔ P s` for predicates P that only depend on
    registers, memory, PC, publicValues, and privateInput (not committed). -/
def liftPred (P : MachineState → Prop) : Assertion :=
  fun h => ∀ s, h.CompatibleWith s → P s

/-- The forward direction of holdsFor for liftPred always works. -/
theorem holdsFor_liftPred_mp {P : MachineState → Prop} {s : MachineState}
    (h : (liftPred P).holdsFor s) : P s := by
  obtain ⟨h, hcompat, hP⟩ := h
  exact hP s hcompat

/-- Backward: construct holdsFor for liftPred using fullState.
    Requires proving P transfers through compatible states. -/
theorem holdsFor_liftPred_intro {P : MachineState → Prop} {s : MachineState}
    (htransfer : ∀ t : MachineState,
      (∀ r, t.getReg r = s.getReg r) → (∀ a, t.getMem a = s.getMem a) →
      t.pc = s.pc → t.publicValues = s.publicValues → t.privateInput = s.privateInput →
      P t) :
    (liftPred P).holdsFor s := by
  refine ⟨PartialState.fullState s, PartialState.CompatibleWith_fullState s, fun t hcompat => ?_⟩
  obtain ⟨hr, hm, hc, hpc, hpv, hpi⟩ := hcompat
  apply htransfer
  · intro r; exact hr r (s.getReg r) (by simp [PartialState.fullState])
  · intro a; exact hm a (s.getMem a) (by simp [PartialState.fullState])
  · exact hpc s.pc (by simp [PartialState.fullState])
  · exact hpv s.publicValues (by simp [PartialState.fullState])
  · exact hpi s.privateInput (by simp [PartialState.fullState])

/-- Simpler backward direction: if P only depends on tracked fields
    (getReg, getMem, pc, publicValues, privateInput), then P s → (liftPred P).holdsFor s. -/
theorem holdsFor_liftPred_of {P : MachineState → Prop} {s : MachineState}
    (hPs : P s)
    (hstable : ∀ t : MachineState,
      (∀ r, t.getReg r = s.getReg r) → (∀ a, t.getMem a = s.getMem a) →
      t.pc = s.pc → t.publicValues = s.publicValues → t.privateInput = s.privateInput →
      P s → P t) :
    (liftPred P).holdsFor s :=
  holdsFor_liftPred_intro (fun t hr hm hpc hpv hpi => hstable t hr hm hpc hpv hpi hPs)

-- ============================================================================
-- Code assertion: instrAt and programAt
-- ============================================================================

/-- Code ownership at address a with instruction i. -/
def instrAt (a : Addr) (i : Instr) : Assertion := fun h => h = PartialState.singletonCode a i

/-- Notation: a ↦ᵢ i means code at address a holds instruction i. -/
notation:50 a " ↦ᵢ " i => instrAt a i

/-- Program ownership: a recursive assertion for a program. -/
def programAt : List (Addr × Instr) → Assertion
  | [] => empAssertion
  | (a, i) :: rest => (instrAt a i) ** (programAt rest)

/-- Convert a program (List Instr) at a base address to address-instruction pairs.
    Each instruction occupies 4 bytes. -/
def progIndexed (base : Addr) : List Instr → List (Addr × Instr)
  | [] => []
  | i :: rest => (base, i) :: progIndexed (base + 4) rest

/-- Program assertion at a base address: owns instrAt for every instruction. -/
def progAt (base : Addr) (prog : List Instr) : Assertion :=
  programAt (progIndexed base prog)

/-- Indexed list for append splits into indexed lists for each part. -/
theorem progIndexed_append (base : Addr) (p1 p2 : List Instr) :
    progIndexed base (p1 ++ p2) = progIndexed base p1 ++ progIndexed (base + BitVec.ofNat 32 (4 * p1.length)) p2 := by
  induction p1 generalizing base with
  | nil => simp [progIndexed, List.nil_append, BitVec.ofNat]
  | cons i rest ih =>
    simp only [List.cons_append, progIndexed, List.cons_append]
    congr 1
    rw [ih (base + 4)]
    congr 1
    simp only [List.length_cons]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- programAt splits on append. -/
theorem programAt_append (l1 l2 : List (Addr × Instr)) :
    programAt (l1 ++ l2) = (programAt l1 ** programAt l2) := by
  induction l1 with
  | nil =>
    simp [programAt]
    funext h; exact propext (sepConj_emp_left (programAt l2) h).symm
  | cons p rest ih =>
    simp only [List.cons_append, programAt]
    rw [ih]
    funext h; exact propext ⟨(sepConj_assoc _ _ _ h).mpr, (sepConj_assoc _ _ _ h).mp⟩

/-- progAt splits on program append. -/
theorem progAt_append (base : Addr) (p1 p2 : List Instr) :
    progAt base (p1 ++ p2) = (progAt base p1 ** progAt (base + BitVec.ofNat 32 (4 * p1.length)) p2) := by
  simp only [progAt, progIndexed_append, programAt_append]

-- ============================================================================
-- CompatibleWith for singletonCode
-- ============================================================================

namespace PartialState

theorem CompatibleWith_singletonCode (a : Addr) (i : Instr) (s : MachineState) :
    (singletonCode a i).CompatibleWith s ↔ s.code a = some i := by
  constructor
  · intro ⟨_, _, hc, _, _, _⟩
    have : (if a == a then some i else none) = some i := by simp
    exact hc a i this
  · intro heq
    refine ⟨fun _ _ h => by simp [singletonCode] at h,
           fun _ _ h => by simp [singletonCode] at h,
           fun a' i' h => ?_,
           fun _ h => by simp [singletonCode] at h,
           fun _ h => by simp [singletonCode] at h,
           fun _ h => by simp [singletonCode] at h⟩
    simp only [singletonCode] at h
    split at h
    · rename_i heq'; rw [beq_iff_eq] at heq'; subst heq'
      simp at h; rw [← h]; exact heq
    · simp at h

end PartialState

-- ============================================================================
-- holdsFor simplification for instrAt
-- ============================================================================

@[simp]
theorem holdsFor_instrAt (a : Addr) (i : Instr) (s : MachineState) :
    (instrAt a i).holdsFor s ↔ s.code a = some i := by
  simp only [Assertion.holdsFor, instrAt]
  constructor
  · rintro ⟨h, hcompat, rfl⟩
    exact (PartialState.CompatibleWith_singletonCode a i s).mp hcompat
  · intro heq
    exact ⟨_, (PartialState.CompatibleWith_singletonCode a i s).mpr heq, rfl⟩

-- ============================================================================
-- Disjointness lemmas for singletonCode
-- ============================================================================

private theorem singletonCode_disjoint_singletonCode (a1 a2 : Addr) (i1 i2 : Instr)
    (hne : a1 ≠ a2) :
    (PartialState.singletonCode a1 i1).Disjoint (PartialState.singletonCode a2 i2) := by
  refine ⟨fun r => Or.inl rfl, fun _ => Or.inl rfl, fun a => ?_, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  simp only [PartialState.singletonCode]
  by_cases h1 : a == a1
  · simp [h1]
    by_cases h2 : a == a2
    · exfalso
      have := beq_iff_eq.mp h1
      have := beq_iff_eq.mp h2
      exact hne (by rw [← ‹a = a1›, ← ‹a = a2›])
    · exact fun hi2 => h2 (beq_iff_eq.mpr hi2)
  · simp [h1]

private theorem singletonReg_disjoint_singletonCode (r : Reg) (v : Word) (a : Addr) (i : Instr) :
    (PartialState.singletonReg r v).Disjoint (PartialState.singletonCode a i) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem singletonMem_disjoint_singletonCode (a : Addr) (v : Word) (a' : Addr) (i : Instr) :
    (PartialState.singletonMem a v).Disjoint (PartialState.singletonCode a' i) := by
  exact ⟨fun _ => Or.inl rfl, fun _ => Or.inr rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem singletonPC_disjoint_singletonCode (v : Word) (a : Addr) (i : Instr) :
    (PartialState.singletonPC v).Disjoint (PartialState.singletonCode a i) := by
  exact ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl, Or.inr rfl, Or.inl rfl, Or.inl rfl⟩

private theorem singletonPublicValues_disjoint_singletonCode (vals : List (BitVec 8)) (a : Addr) (i : Instr) :
    (PartialState.singletonPublicValues vals).Disjoint (PartialState.singletonCode a i) := by
  exact ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inr rfl, Or.inl rfl⟩

private theorem singletonPrivateInput_disjoint_singletonCode (vals : List (BitVec 8)) (a : Addr) (i : Instr) :
    (PartialState.singletonPrivateInput vals).Disjoint (PartialState.singletonCode a i) := by
  exact ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inr rfl⟩

-- ============================================================================
-- pcFree for code assertions
-- ============================================================================

theorem pcFree_instrAt (a : Addr) (i : Instr) : (instrAt a i).pcFree := by
  intro h hp; rw [instrAt] at hp; subst hp; rfl

theorem pcFree_programAt : ∀ prog, (programAt prog).pcFree
  | [] => pcFree_emp
  | (a, i) :: rest =>
    pcFree_sepConj (pcFree_instrAt a i) (pcFree_programAt rest)

instance : Assertion.PCFree (instrAt a i) := ⟨pcFree_instrAt a i⟩

instance : Assertion.PCFree (programAt prog) := ⟨pcFree_programAt prog⟩

theorem pcFree_progAt (base : Addr) (prog : List Instr) : (progAt base prog).pcFree :=
  pcFree_programAt (progIndexed base prog)

instance : Assertion.PCFree (progAt base prog) := ⟨pcFree_progAt base prog⟩

-- ============================================================================
-- Assertion-level equalities for AC normalization of sepConj
-- ============================================================================

theorem sepConj_comm' (P Q : Assertion) : (P ** Q) = (Q ** P) :=
  funext fun h => propext (sepConj_comm P Q h)

theorem sepConj_assoc' (P Q R : Assertion) : ((P ** Q) ** R) = (P ** (Q ** R)) :=
  funext fun h => propext (sepConj_assoc P Q R h)

theorem sepConj_left_comm' (P Q R : Assertion) : (P ** (Q ** R)) = (Q ** (P ** R)) := by
  rw [← sepConj_assoc', ← sepConj_assoc', sepConj_comm' P Q]

theorem sepConj_emp_right' (P : Assertion) : (P ** empAssertion) = P :=
  funext fun h => propext (sepConj_emp_right P h)

theorem sepConj_emp_left' (P : Assertion) : (empAssertion ** P) = P :=
  funext fun h => propext (sepConj_emp_left P h)

instance : Std.Associative (α := Assertion) sepConj := ⟨sepConj_assoc'⟩
instance : Std.Commutative (α := Assertion) sepConj := ⟨sepConj_comm'⟩

/-- `sep_perm h` closes a goal of the form `(A₁ ** ... ** Aₙ) s` given a hypothesis `h`
    that is a permutation of the same assertions applied to the same state.
    Works by proving assertion equality via `ac_rfl` and transporting with `congrFun`.
    Note: uses `show _ = _ by ac_rfl` (hyp → goal direction) rather than
    `by ac_rfl : _ = _` (goal → hyp direction) to avoid inconsistent atom orderings
    when the two sides were elaborated in different contexts. -/
syntax "sep_perm" ident : tactic
macro_rules
  | `(tactic| sep_perm $hyp) =>
    `(tactic| exact (congrFun (show _ = _ by delta Word Addr; dsimp (config := { failIfUnchanged := false }) only []; all_goals ac_rfl) _).mp $hyp)

/-- `sep_eq` closes a goal of the form `⊢ f x = g x` where `f` and `g` are AC-equivalent
    `sepConj` chains. Decomposes the function application with `congrFun` and proves
    the function equality via `ac_rfl`. -/
syntax "sep_eq" : tactic
macro_rules
  | `(tactic| sep_eq) => `(tactic| exact congrFun (by ac_rfl) _)

/-- Proves `P.pcFree` by synthesizing an `Assertion.PCFree P` instance.
    Falls back to a manual recursive proof for very deep assertion chains
    where instance synthesis exceeds heartbeat limits. -/
syntax "pcFree" : tactic
macro_rules
  | `(tactic| pcFree) => `(tactic|
    first
    | exact (inferInstance : Assertion.PCFree _).proof
    | repeat (first
      | apply pcFree_sepConj
      | exact pcFree_instrAt _ _
      | exact pcFree_regIs _ _
      | exact pcFree_memIs _ _
      | exact pcFree_regOwn _
      | exact pcFree_memOwn _
      | exact pcFree_emp
      | exact pcFree_pure _
      | exact pcFree_programAt _))

-- ============================================================================
-- himpl: Assertion implication (for xsimp framework)
-- ============================================================================

/-- Assertion implication: P entails Q if for all partial states h, P h → Q h. -/
def himpl (P Q : Assertion) : Prop := ∀ h, P h → Q h

/-- himpl follows from equality. -/
theorem himpl_of_eq {P Q : Assertion} (h : P = Q) : himpl P Q :=
  h ▸ fun _ hp => hp

/-- himpl is reflexive. -/
theorem himpl_refl (P : Assertion) : himpl P P := fun _ hp => hp

/-- himpl is transitive. -/
theorem himpl_trans {P Q R : Assertion} (h1 : himpl P Q) (h2 : himpl Q R) : himpl P R :=
  fun h hp => h2 h (h1 h hp)

/-- himpl lifts to holdsFor. -/
theorem holdsFor_of_himpl {P Q : Assertion} {s : MachineState} (himpl_pq : himpl P Q)
    (hp : P.holdsFor s) : Q.holdsFor s := by
  obtain ⟨h, hcompat, hP⟩ := hp
  exact ⟨h, hcompat, himpl_pq h hP⟩

end EvmAsm
