/-
  EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpecRefWitness

  Per-arm non-vacuity witnesses for the attributed post `hvbfSpecRefRetPost`
  of `header_validate_base_fee_specref_within` (issue #12346; an increment on
  #12762).  The premise-set inhabitant
  (`header_validate_base_fee_specref_within_inhabitable`) only shows the
  theorem's static premises are jointly satisfiable — it says nothing about
  the POST.  This file shows each of the three outcome disjuncts is
  separately inhabitable, at concrete parameters where the disjunct's own
  guard genuinely holds:

  * **arm 0 (match, status 0)** — `headerBytes` IS the recurrence encoding
    (at the witness family's gas values the recurrence's equal arm fires and
    the expected encoding is the all-zero list, `hvbfExpectedBytes_zeros`),
    so the reference-acceptance implication is non-vacuous.
  * **arm 1 (mismatch, status 1)** — `headerBytes` is a genuinely differing
    32-byte encoding (`hvbfHdr1Bytes`), so the
    `.invalidBlock "base fee mismatch"` implication is non-vacuous.
  * **arm 2 (K73 failure, status 2)** — the guest-internal failure disjunct,
    inhabited directly.

  The arm index is the STATUS value (0 match, 1 mismatch, 2 K73 failure),
  not the position in the disjunction (which lists status 2 first).

  The witness family mirrors #12762's
  `header_validate_base_fee_final_arms_inhabited`, but with the recurrence
  coupling the attribution layer imposes: #12762's witness hardcodes
  `v18 = 25000`, while here the `target` slot is `gasLimit >>> 1 = 50000`
  and the scratch content is `hvbfExpectedBytes` (the all-zero list at these
  gas values).  Each arm theorem is followed by a `…_yields_post` corollary
  re-embedding the arm witness into the full `hvbfSpecRefRetPost` — this
  kernel-checks that the inlined arm statement has not drifted from the
  post's definition.
-/

import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpecRefCompose
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeWitnessSupport

namespace EvmAsm.Codegen.HeaderValidateBaseFeeSpecRef

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec hiding K73
open EvmAsm.Codegen.HeaderValidateBaseFeeSpec
open EvmAsm.Codegen.HeaderValidateBaseFeeCompositionIncreaseRoute
open EvmAsm.Stateless.SpecRef

/-! ## §1  The witness family's expected encoding -/

/-- At the witness family's gas values (`gasLimit = 100000`,
    `gasUsed = 50000`, all-zero parent base fee) the recurrence's equal arm
    fires (`gasUsed = gasLimit / 2`), so the expected base fee is the parent
    fee `0` and its 32-byte encoding is the all-zero list — the scratch
    content of #12762's `hvbfRegions`. -/
theorem hvbfExpectedBytes_zeros :
    hvbfExpectedBytes (100000 : Word) (50000 : Word) hvbfBytes32 =
      hvbfBytes32 := by
  decide

/-! ## §2  The mismatch arm's header encoding and its region heap -/

/-- The mismatch-arm header encoding: thirty-one zero bytes then a one —
    genuinely differs from the all-zero expected encoding of the witness
    family. -/
def hvbfHdr1Bytes : List (BitVec 8) := List.replicate 31 (0 : BitVec 8) ++ [1]

/-- The packed final dword of `hvbfHdr1Bytes` (bytes 24–31). -/
def hvbfHdr1Dword : Word := packBytes (List.replicate 7 (0 : BitVec 8) ++ [1])

/-- The memory cells of the mismatch-arm region heap: the same twelve
    addresses as #12762's `hvbfRegionCells`, with the header region's last
    dword holding `hvbfHdr1Dword` instead of the all-zero chunk.  The zero
    values are written as `packBytes` of the zero chunk (rather than the
    literal `0`) so the region-decomposition proofs below match
    syntactically after `simp` normalizes the byte lists. -/
def hvbfRegionsHdr1Cells : List (Word × Word) :=
  [((0x200000 : Word), packBytes (List.replicate 8 (0 : BitVec 8))),
   (0x200008, packBytes (List.replicate 8 (0 : BitVec 8))),
   (0x200010, packBytes (List.replicate 8 (0 : BitVec 8))),
   (0x200018, hvbfHdr1Dword),
   ((0x200100 : Word), packBytes (List.replicate 8 (0 : BitVec 8))),
   (0x200108, packBytes (List.replicate 8 (0 : BitVec 8))),
   (0x200110, packBytes (List.replicate 8 (0 : BitVec 8))),
   (0x200118, packBytes (List.replicate 8 (0 : BitVec 8))),
   (Expected, packBytes (List.replicate 8 (0 : BitVec 8))),
   (Expected + 8, packBytes (List.replicate 8 (0 : BitVec 8))),
   (Expected + 16, packBytes (List.replicate 8 (0 : BitVec 8))),
   (Expected + 24, packBytes (List.replicate 8 (0 : BitVec 8)))]

/-- The mismatch-arm region assertion: header region holding
    `hvbfHdr1Bytes`, parent and expected-scratch regions all-zero. -/
def hvbfRegionsHdr1 : Assertion :=
  bytesRegion (0x200000 : Word) hvbfHdr1Bytes **
    bytesRegion (0x200100 : Word) hvbfBytes32 **
    bytesRegion Expected hvbfBytes32

/-- The mismatch-arm region heap. -/
def hvbfRegionsHdr1State : PartialState :=
  hvbfRegionsHdr1Cells.foldr
    (fun p acc => (PartialState.singletonMem p.1 p.2).union acc)
    PartialState.empty

private theorem singletonMem_pair_disjoint {p q : Word × Word} (hne : p.1 ≠ q.1) :
    (PartialState.singletonMem p.1 p.2).Disjoint
      (PartialState.singletonMem q.1 q.2) := by
  refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro a
  by_cases h : a = p.1
  · subst a
    right
    simp [PartialState.singletonMem, hne]
  · left
    simp [PartialState.singletonMem, h]

theorem hvbfRegionsHdr1_inhabited : hvbfRegionsHdr1 hvbfRegionsHdr1State := by
  have h0 : bytesRegion (0x200000 : Word) hvbfHdr1Bytes =
      (((0x200000 : Word) ↦ₘ packBytes (List.replicate 8 (0 : BitVec 8))) **
      ((0x200008 : Word) ↦ₘ packBytes (List.replicate 8 (0 : BitVec 8))) **
      ((0x200010 : Word) ↦ₘ packBytes (List.replicate 8 (0 : BitVec 8))) **
      ((0x200018 : Word) ↦ₘ hvbfHdr1Dword) ** empAssertion) := by
    simp [bytesRegion, bytesRegionAux, hvbfHdr1Bytes, hvbfHdr1Dword,
      List.replicate]
  have h1 : bytesRegion (0x200100 : Word) hvbfBytes32 =
      (((0x200100 : Word) ↦ₘ packBytes (List.replicate 8 (0 : BitVec 8))) **
      ((0x200108 : Word) ↦ₘ packBytes (List.replicate 8 (0 : BitVec 8))) **
      ((0x200110 : Word) ↦ₘ packBytes (List.replicate 8 (0 : BitVec 8))) **
      ((0x200118 : Word) ↦ₘ packBytes (List.replicate 8 (0 : BitVec 8))) **
      empAssertion) := by
    simp [bytesRegion, bytesRegionAux, hvbfBytes32, List.replicate]
  have h2 : bytesRegion Expected hvbfBytes32 =
      ((Expected ↦ₘ packBytes (List.replicate 8 (0 : BitVec 8))) **
      ((Expected + 8) ↦ₘ packBytes (List.replicate 8 (0 : BitVec 8))) **
      ((Expected + 16) ↦ₘ packBytes (List.replicate 8 (0 : BitVec 8))) **
      ((Expected + 24) ↦ₘ packBytes (List.replicate 8 (0 : BitVec 8))) **
      empAssertion) := by
    simp [bytesRegion, bytesRegionAux, hvbfBytes32, List.replicate,
      Expected, GuestAddrs.hvbf_expected]
  have hc := sepConj_foldr_satisfiable
    (atom := fun p : Word × Word => p.1 ↦ₘ p.2)
    (heap := fun p : Word × Word => PartialState.singletonMem p.1 p.2)
    (xs := hvbfRegionsHdr1Cells)
    (by
      intro p hp
      simp [hvbfRegionsHdr1Cells] at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact ⟨rfl, by decide⟩)
    (by
      exact List.Pairwise.imp
        (fun {p q} hpq => singletonMem_pair_disjoint hpq) (by decide))
  unfold hvbfRegionsHdr1 hvbfRegionsHdr1State
  rw [h0, h1, h2]
  simp only [hvbfRegionsHdr1Cells, List.foldr, sepConj_emp_right',
    sepConj_assoc', PartialState.union_empty_right] at hc ⊢
  xperm_chunked hc

/-- The mismatch-arm region heap is disjoint from any state whose memory
    footprint is the wrapper/K73 frame — the analogue of #12762's
    `hvbfRegions_disjoint_of_frame` (the address set is identical; only the
    value at `0x200018` differs). -/
theorem hvbfRegionsHdr1_disjoint_of_frame (h : PartialState)
    (hmem : ∀ a, h.mem a ≠ none →
      a = (0x0ffff0 : Word) ∨ a = 0x0ffff8 ∨ a = 0x0fffb8 ∨
      a = 0x0fffc0 ∨ a = 0x0fffc8 ∨ a = 0x0fffd0 ∨
      a = 0x0fffd8 ∨ a = 0x0fffe0) :
    h.Disjoint hvbfRegionsHdr1State := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    right
    simp [hvbfRegionsHdr1State, hvbfRegionsHdr1Cells, PartialState.union,
      PartialState.empty, PartialState.singletonMem]
  · intro a
    by_cases hnone : h.mem a = none
    · exact Or.inl hnone
    · right
      have ha := hmem a hnone
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [hvbfRegionsHdr1State, hvbfRegionsHdr1Cells, Expected,
          GuestAddrs.hvbf_expected, PartialState.union, PartialState.empty,
          PartialState.singletonMem]
  · intro a
    right
    simp [hvbfRegionsHdr1State, hvbfRegionsHdr1Cells, PartialState.union,
      PartialState.empty, PartialState.singletonMem]
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl

/-! ## §3  The shared final-state witness (recurrence-coupled) -/

/-- The attribution-coupled analogue of #12762's
    `header_validate_base_fee_final_inhabited`: the final wrapper state at
    the caller-shaped addresses, with `target = gasLimit >>> 1 = 50000`
    (where #12762's witness hardcoded `25000`) and the expected scratch
    all-zero (the recurrence encoding at the witness family's gas values,
    via `hvbfExpectedBytes_zeros`).  The header byte list and its region
    heap are parameters, so the match/failure arms reuse #12762's all-zero
    `hvbfRegions` while the mismatch arm supplies `hvbfRegionsHdr1`. -/
theorem header_validate_base_fee_specref_final_inhabited
    (status out11 : Word) (headerBytes : List (BitVec 8))
    (regionsState : PartialState)
    (hregions : (bytesRegion (0x200000 : Word) headerBytes **
      bytesRegion (0x200100 : Word) hvbfBytes32 **
      bytesRegion Expected hvbfBytes32) regionsState)
    (hdisj : ∀ hh : PartialState, (∀ a, hh.mem a ≠ none →
        a = (0x0ffff0 : Word) ∨ a = 0x0ffff8 ∨ a = 0x0fffb8 ∨
        a = 0x0fffc0 ∨ a = 0x0fffc8 ∨ a = 0x0fffd0 ∨
        a = 0x0fffd8 ∨ a = 0x0fffe0) → hh.Disjoint regionsState) :
    ∃ h : PartialState,
      hvbfFinal (0x100000 : Word) (0x0ffff0 : Word) (0x0fffb8 : Word)
        (0x12340000 : Word) (0x56780000 : Word) (0x200000 : Word)
        1 (2 : Word) ((100000 : Word) >>> 1) 3 4 50000 (0x200100 : Word) status out11
        hvbfBytes32 hvbfBytes32 headerBytes (k74FlatFrame empAssertion) h := by
  have htarget : ((100000 : Word) >>> 1) = (50000 : Word) := by decide
  rw [htarget]
  let fixedRegs : List Reg :=
    [.x1, .x2, .x8, .x18, .x10, .x11, .x9, .x19, .x20, .x0]
  let fixedVal : Reg → Word := fun r => match r with
    | .x1 => 0x12340000
    | .x2 => 0x100000
    | .x8 => 0x56780000
    | .x18 => 2
    | .x10 => status
    | .x11 => out11
    | .x9 => 1
    | .x19 => 3
    | .x20 => 4
    | .x12 => 0x200100
    | .x0 => 0
    | _ => 0
  let ownedRegs : List Reg :=
    [.x5, .x6, .x7, .x12, .x13, .x14, .x15, .x16, .x17, .x28, .x29, .x30, .x31]
  let fixedMems : List (Word × Word) :=
    [(0x0ffff0, 0x12340000), (0x0ffff8, 0x56780000),
     (0x0fffb8, H + 40), (0x0fffc0, 0x200000), (0x0fffc8, 1),
     (0x0fffd0, 2), (0x0fffd8, 3), (0x0fffe0, 4)]
  let fixedHeap : Reg → PartialState :=
    fun r => PartialState.singletonReg r (fixedVal r)
  let ownedHeap : Reg → PartialState :=
    fun r => PartialState.singletonReg r 0
  let memHeap : (Word × Word) → PartialState :=
    fun p => PartialState.singletonMem p.1 p.2
  have singletonReg_disjoint {r1 r2 : Reg} {v1 v2 : Word}
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
  have singletonMem_disjoint {a1 a2 v1 v2 : Word} (hne : a1 ≠ a2) :
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
  have hFixed :
      (fixedRegs.foldr (fun r acc => (r ↦ᵣ fixedVal r) ** acc) empAssertion)
        (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
          PartialState.empty) := by
    apply sepConj_foldr_satisfiable
    · intro r hr
      simp [fixedHeap, fixedVal, regIs]
    · exact List.Pairwise.imp (fun {r1 r2} hne => singletonReg_disjoint hne)
        (by decide)
  have hOwned :
      (ownedRegs.foldr (fun r acc => regOwn r ** acc) empAssertion)
        (ownedRegs.foldr (fun r acc => (ownedHeap r).union acc)
          PartialState.empty) := by
    apply sepConj_foldr_satisfiable
    · intro r hr
      exact ⟨0, by simp [ownedHeap, regIs]⟩
    · exact List.Pairwise.imp (fun {r1 r2} hne => singletonReg_disjoint hne)
        (by decide)
  have hRegs := sepConj_foldr_cross_satisfiable
    (atomL := fun r : Reg => r ↦ᵣ fixedVal r) (heapL := fixedHeap)
    (xs := fixedRegs) (atomR := fun r : Reg => regOwn r)
    (heapR := ownedHeap) (ys := ownedRegs) hFixed hOwned (by
      intro r1 hr1 r2 hr2
      apply singletonReg_disjoint
      simp [fixedRegs] at hr1
      simp [ownedRegs] at hr2
      aesop)
  have hMems :
      (fixedMems.foldr (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion)
        (fixedMems.foldr (fun p acc => (memHeap p).union acc)
          PartialState.empty) := by
    apply sepConj_foldr_satisfiable
    · intro p hp
      simp [fixedMems] at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals
        refine ⟨rfl, ?_⟩
        apply isValidDwordAccess_of_toNat
        · decide
        · left
          exact ⟨by decide, by decide⟩
    · exact List.Pairwise.imp
        (fun {p q} hpq => singletonMem_disjoint hpq) (by decide)
  let regState : PartialState :=
    (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
      PartialState.empty).union
      (ownedRegs.foldr (fun r acc => (ownedHeap r).union acc)
        PartialState.empty)
  let memState : PartialState :=
    fixedMems.foldr (fun p acc => (memHeap p).union acc) PartialState.empty
  have hRegMem : regState.Disjoint memState := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r
      right
      simp [memState, fixedMems, memHeap, PartialState.singletonMem,
        PartialState.union, PartialState.empty]
    · intro a
      left
      simp [regState, fixedRegs, ownedRegs, fixedHeap, ownedHeap,
        PartialState.singletonReg, PartialState.union, PartialState.empty]
    · intro a
      exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
  have hAll :
      (((fixedRegs.foldr (fun r acc => (r ↦ᵣ fixedVal r) ** acc) empAssertion) **
        (ownedRegs.foldr (fun r acc => regOwn r ** acc) empAssertion)) **
        (fixedMems.foldr (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion))
        (regState.union memState) := by
    exact ⟨regState, memState, hRegMem, rfl, hRegs, hMems⟩
  have hBaseRegion : (regState.union memState).Disjoint regionsState := by
    apply hdisj
    intro a ha
    simp [regState, memState, fixedRegs, ownedRegs, fixedHeap, ownedHeap,
      fixedMems, memHeap, PartialState.union, PartialState.empty,
      PartialState.singletonReg, PartialState.singletonMem] at ha
    split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
  have hAllRegion :
      (((((fixedRegs.foldr (fun r acc => (r ↦ᵣ fixedVal r) ** acc) empAssertion) **
        (ownedRegs.foldr (fun r acc => regOwn r ** acc) empAssertion)) **
        (fixedMems.foldr (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion)) **
        (bytesRegion (0x200000 : Word) headerBytes **
          bytesRegion (0x200100 : Word) hvbfBytes32 **
          bytesRegion Expected hvbfBytes32))
        ((regState.union memState).union regionsState)) := by
    exact ⟨regState.union memState, regionsState, hBaseRegion, rfl,
      hAll, hregions⟩
  refine ⟨(regState.union memState).union regionsState, ?_⟩
  unfold hvbfFinal
  dsimp [regState, memState, fixedRegs, fixedVal, ownedRegs, fixedMems,
    fixedHeap, ownedHeap, memHeap, hvbfBytes32, tailRest,
    tailRestCore, frameSlotsSaved, hvbfSaved, k73Saved, hvbfFrame, k73Frame,
    k74FlatFrame]
    at hAllRegion ⊢
  simp [sepConj_assoc', sepConj_emp_right', signExtend12]
    at hAllRegion ⊢
  xperm_chunked hAllRegion

/-! ## §4  The three post arms are separately inhabitable -/

/-- Arm 0 (match, status 0): the header fee bytes ARE the recurrence
    encoding — non-vacuously, since at the witness family's gas values the
    expected encoding is the all-zero list (`hvbfExpectedBytes_zeros`) and
    `headerBytes := hvbfBytes32`.  The reference's isolated base-fee check
    accepts (`hvbfSpecRefBaseFeeCheck_ok`). -/
theorem header_validate_base_fee_specref_within_arm0_inhabitable :
    ∃ h : PartialState,
      ((hvbfFinal (0x100000 : Word) (0x0ffff0 : Word) (0x0fffb8 : Word)
          (0x12340000 : Word) (0x56780000 : Word) (0x200000 : Word)
          1 (2 : Word) ((100000 : Word) >>> 1) 3 4 50000 (0x200100 : Word)
          (0 : Word) Expected hvbfBytes32
          (hvbfExpectedBytes (100000 : Word) (50000 : Word) hvbfBytes32)
          hvbfBytes32 (k74FlatFrame empAssertion)) **
        ⌜hvbfBytes32 =
            hvbfExpectedBytes (100000 : Word) (50000 : Word) hvbfBytes32 →
          ∀ blockGasLimit : Nat,
            check_gas_limit blockGasLimit (100000 : Word).toNat = true →
            hvbfSpecRefBaseFeeCheck blockGasLimit (100000 : Word) (50000 : Word)
              hvbfBytes32 hvbfBytes32 = .ok ()⌝) h := by
  obtain ⟨h, hh⟩ := header_validate_base_fee_specref_final_inhabited
    (0 : Word) Expected hvbfBytes32 hvbfRegionsState hvbfRegions_inhabited
    hvbfRegions_disjoint_of_frame
  refine ⟨h, (sepConj_pure_right h).2 ⟨?_, fun hmatch bl hb =>
    hvbfSpecRefBaseFeeCheck_ok bl (100000 : Word) (50000 : Word)
      hvbfBytes32 hvbfBytes32 hb hmatch⟩⟩
  rw [hvbfExpectedBytes_zeros]
  exact hh

/-- Arm 1 (mismatch, status 1): the header fee bytes genuinely differ from
    the recurrence encoding (`hvbfHdr1Bytes` vs the all-zero expected
    encoding) — the reference raises `.invalidBlock "base fee mismatch"`
    (`hvbfSpecRefBaseFeeCheck_mismatch`), explicitly never the gas-limit
    raise. -/
theorem header_validate_base_fee_specref_within_arm1_inhabitable :
    ∃ h : PartialState,
      ((hvbfFinal (0x100000 : Word) (0x0ffff0 : Word) (0x0fffb8 : Word)
          (0x12340000 : Word) (0x56780000 : Word) (0x200000 : Word)
          1 (2 : Word) ((100000 : Word) >>> 1) 3 4 50000 (0x200100 : Word)
          (1 : Word) Expected hvbfBytes32
          (hvbfExpectedBytes (100000 : Word) (50000 : Word) hvbfBytes32)
          hvbfHdr1Bytes (k74FlatFrame empAssertion)) **
        ⌜hvbfHdr1Bytes ≠
            hvbfExpectedBytes (100000 : Word) (50000 : Word) hvbfBytes32 →
          ∀ blockGasLimit : Nat,
            check_gas_limit blockGasLimit (100000 : Word).toNat = true →
            hvbfSpecRefBaseFeeCheck blockGasLimit (100000 : Word) (50000 : Word)
              hvbfBytes32 hvbfHdr1Bytes =
                .error (.invalidBlock "base fee mismatch")⌝) h := by
  obtain ⟨h, hh⟩ := header_validate_base_fee_specref_final_inhabited
    (1 : Word) Expected hvbfHdr1Bytes hvbfRegionsHdr1State
    hvbfRegionsHdr1_inhabited hvbfRegionsHdr1_disjoint_of_frame
  refine ⟨h, (sepConj_pure_right h).2 ⟨?_, fun hne bl hb =>
    hvbfSpecRefBaseFeeCheck_mismatch bl (100000 : Word) (50000 : Word)
      hvbfBytes32 hvbfHdr1Bytes hb hne⟩⟩
  rw [hvbfExpectedBytes_zeros]
  exact hh

/-- Arm 2 (K73 failure, status 2): the guest-internal failure outcome (no
    reference counterpart), inhabited directly at the witness family's
    parameters. -/
theorem header_validate_base_fee_specref_within_arm2_inhabitable :
    ∃ h : PartialState,
      (hvbfFinalScratch (0x100000 : Word) (0x0ffff0 : Word) (0x0fffb8 : Word)
        (0x12340000 : Word) (0x56780000 : Word) (0x200000 : Word)
        1 (2 : Word) ((100000 : Word) >>> 1) 3 4 50000 (0x200100 : Word)
        (2 : Word) (50000 : Word) hvbfBytes32
        (hvbfExpectedBytes (100000 : Word) (50000 : Word) hvbfBytes32)
        hvbfBytes32 (k74FlatFrame empAssertion)) h := by
  obtain ⟨h, hh⟩ := header_validate_base_fee_specref_final_inhabited
    (2 : Word) (50000 : Word) hvbfBytes32 hvbfRegionsState
    hvbfRegions_inhabited hvbfRegions_disjoint_of_frame
  rw [hvbfExpectedBytes_zeros]
  refine ⟨h, ?_⟩
  let outRest : Assertion :=
    (.x1 ↦ᵣ (0x12340000 : Word)) ** (.x2 ↦ᵣ (0x100000 : Word)) **
      (.x8 ↦ᵣ (0x56780000 : Word)) ** (.x10 ↦ᵣ (2 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved hvbfFrame (0x0ffff0 : Word)
        (hvbfSaved (0x12340000 : Word) (0x56780000 : Word)) **
      tailRestCore (0x0ffff0 : Word) (0x0fffb8 : Word)
        (0x12340000 : Word) (0x56780000 : Word) (0x200000 : Word)
        1 (2 : Word) ((100000 : Word) >>> 1) 3 4 50000 (0x200100 : Word)
        hvbfBytes32 hvbfBytes32 hvbfBytes32 (k74FlatFrame empAssertion)
  have hq1 : ((.x11 ↦ᵣ (50000 : Word)) ** outRest) h := by
    dsimp [outRest, hvbfFinal, tailRest] at hh ⊢
    xperm_hyp hh
  have hq2 : (regOwn .x11 ** outRest) h :=
    sepConj_mono_left
      (P := (.x11 ↦ᵣ (50000 : Word))) (P' := regOwn .x11) (Q := outRest)
      (regIs_implies_regOwn (r := .x11) (v := (50000 : Word))) _ hq1
  dsimp [outRest, hvbfFinalScratch, tailRestScratch] at hq2 ⊢
  rw [show BitVec.ofNat 64 0 = (0 : Word) by rfl] at hq2
  rw [← (show (0 : Word) = BitVec.ofNat 64 0 by rfl)]
  xperm_chunked hq2

/-! ## §5  Re-embedding ties: each arm witness inhabits the full post

    These corollaries kernel-check that the inlined arm statements above
    have not drifted from `hvbfSpecRefRetPost`'s disjuncts (the post lists
    the status-2 disjunct first). -/

theorem header_validate_base_fee_specref_within_arm0_yields_post :
    ∃ h : PartialState,
      hvbfSpecRefRetPost (0x100000 : Word) (0x0ffff0 : Word) (0x0fffb8 : Word)
        (0x12340000 : Word) (0x56780000 : Word) (0x200000 : Word)
        (100000 : Word) (50000 : Word) (0x200100 : Word)
        1 (2 : Word) 3 4 hvbfBytes32 hvbfBytes32 (k74FlatFrame empAssertion) h := by
  obtain ⟨h, hh⟩ := header_validate_base_fee_specref_within_arm0_inhabitable
  exact ⟨h, Or.inr (Or.inl hh)⟩

theorem header_validate_base_fee_specref_within_arm1_yields_post :
    ∃ h : PartialState,
      hvbfSpecRefRetPost (0x100000 : Word) (0x0ffff0 : Word) (0x0fffb8 : Word)
        (0x12340000 : Word) (0x56780000 : Word) (0x200000 : Word)
        (100000 : Word) (50000 : Word) (0x200100 : Word)
        1 (2 : Word) 3 4 hvbfBytes32 hvbfHdr1Bytes (k74FlatFrame empAssertion) h := by
  obtain ⟨h, hh⟩ := header_validate_base_fee_specref_within_arm1_inhabitable
  exact ⟨h, Or.inr (Or.inr hh)⟩

theorem header_validate_base_fee_specref_within_arm2_yields_post :
    ∃ h : PartialState,
      hvbfSpecRefRetPost (0x100000 : Word) (0x0ffff0 : Word) (0x0fffb8 : Word)
        (0x12340000 : Word) (0x56780000 : Word) (0x200000 : Word)
        (100000 : Word) (50000 : Word) (0x200100 : Word)
        1 (2 : Word) 3 4 hvbfBytes32 hvbfBytes32 (k74FlatFrame empAssertion) h := by
  obtain ⟨h, hh⟩ := header_validate_base_fee_specref_within_arm2_inhabitable
  exact ⟨h, Or.inl ⟨hvbfBytes32, hh⟩⟩

#print axioms hvbfExpectedBytes_zeros
#print axioms hvbfRegionsHdr1_inhabited
#print axioms hvbfRegionsHdr1_disjoint_of_frame
#print axioms header_validate_base_fee_specref_final_inhabited
#print axioms header_validate_base_fee_specref_within_arm0_inhabitable
#print axioms header_validate_base_fee_specref_within_arm1_inhabitable
#print axioms header_validate_base_fee_specref_within_arm2_inhabitable
#print axioms header_validate_base_fee_specref_within_arm0_yields_post
#print axioms header_validate_base_fee_specref_within_arm1_yields_post
#print axioms header_validate_base_fee_specref_within_arm2_yields_post

/-! ## §6  The Route-B machine post is inhabited (#12346 residual 2b)

The repaired wrapper premise returns K73 through
`k73RouteBCallPost`, whose success arm claims — among the usual restored
registers — that the Expected window holds the image K73 actually wrote
(`hvbfWrittenImage`), which the OLD premise could not claim truthfully
(it reused the caller-owned entry list).  This section CONSTRUCTS an
inhabitant of the success-arm shape at the witness family's gas values,
proving the repaired contract non-vacuous: there is a real state
satisfying every atom of the formerly-false clause.  The failure arm
(existential scratch) is satisfiable a fortiori and needs no separate
construction. -/

/-- Split witness for the Route-B success arm: some partial state carries
the callsite link register together with the entire `k73PostOwn` body at
the written-image spelling. -/
theorem k73_routeB_post_success_split :
    ∃ h : PartialState,
      ((.x1 ↦ᵣ (H + 40)) **
        k73PostOwn (0x0ffff0 : Word) (0x0fffb8 : Word) (0x200000 : Word)
          1 (2 : Word) ((100000 : Word) >>> 1) 3 4 50000 (0x200100 : Word)
          hvbfBytes32 (hvbfWrittenImage (100000 : Word) (50000 : Word) hvbfBytes32)
          hvbfBytes32 (0x12340000 : Word) (0x56780000 : Word)
          (k74FlatFrame empAssertion)) h := by
  let fixedRegs : List Reg :=
    [.x1, .x2, .x8, .x9, .x18, .x19, .x20, .x0]
  let fixedVal : Reg → Word := fun r => match r with
    | .x1 => H + 40
    | .x2 => 0x0ffff0
    | .x8 => 0x200000
    | .x9 => 1
    | .x18 => 2
    | .x19 => 3
    | .x20 => 4
    | .x12 => 0x200100
    | .x0 => 0
    | _ => 0
  let ownedRegs : List Reg :=
    [.x5, .x6, .x7, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
      .x28, .x29, .x30, .x31]
  let fixedMems : List (Word × Word) :=
    [(0x0ffff0, 0x12340000), (0x0ffff8, 0x56780000),
     (0x0fffb8, H + 40), (0x0fffc0, 0x200000), (0x0fffc8, 1),
     (0x0fffd0, 2), (0x0fffd8, 3), (0x0fffe0, 4)]
  have hwz : hvbfWrittenImage (100000 : Word) (50000 : Word) hvbfBytes32
      = hvbfBytes32 := by
    simp only [hvbfWrittenImage]
    exact hvbfExpectedBytes_zeros
  -- h2: pins, owned regs, frame dwords, and the three byte regions.
  let fixedHeap : Reg → PartialState :=
    fun r => PartialState.singletonReg r (fixedVal r)
  let ownedHeap : Reg → PartialState :=
    fun r => PartialState.singletonReg r 0
  let memHeap : (Word × Word) → PartialState :=
    fun p => PartialState.singletonMem p.1 p.2
  have singletonReg_disjoint {r1 r2 : Reg} {v1 v2 : Word}
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
  have singletonMem_disjoint {a1 a2 v1 v2 : Word} (hne : a1 ≠ a2) :
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
  have hFixed :
      (fixedRegs.foldr (fun r acc => (r ↦ᵣ fixedVal r) ** acc) empAssertion)
        (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
          PartialState.empty) := by
    apply sepConj_foldr_satisfiable
    · intro r hr
      simp [fixedHeap, fixedVal, regIs]
    · exact List.Pairwise.imp (fun {r1 r2} hne => singletonReg_disjoint hne)
        (by decide)
  have hOwned :
      (ownedRegs.foldr (fun r acc => regOwn r ** acc) empAssertion)
        (ownedRegs.foldr (fun r acc => (ownedHeap r).union acc)
          PartialState.empty) := by
    apply sepConj_foldr_satisfiable
    · intro r hr
      exact ⟨0, by simp [ownedHeap, regIs]⟩
    · exact List.Pairwise.imp (fun {r1 r2} hne => singletonReg_disjoint hne)
        (by decide)
  have hRegs := sepConj_foldr_cross_satisfiable
    (atomL := fun r : Reg => r ↦ᵣ fixedVal r) (heapL := fixedHeap)
    (xs := fixedRegs) (atomR := fun r : Reg => regOwn r)
    (heapR := ownedHeap) (ys := ownedRegs) hFixed hOwned (by
      intro r1 hr1 r2 hr2
      apply singletonReg_disjoint
      simp [fixedRegs] at hr1
      simp [ownedRegs] at hr2
      aesop)
  have hMems :
      (fixedMems.foldr (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion)
        (fixedMems.foldr (fun p acc => (memHeap p).union acc)
          PartialState.empty) := by
    apply sepConj_foldr_satisfiable
    · intro p hp
      simp [fixedMems] at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals
        refine ⟨rfl, ?_⟩
        apply isValidDwordAccess_of_toNat
        · decide
        · left
          exact ⟨by decide, by decide⟩
    · exact List.Pairwise.imp
        (fun {p q} hpq => singletonMem_disjoint hpq) (by decide)
  let regState : PartialState :=
    (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
      PartialState.empty).union
      (ownedRegs.foldr (fun r acc => (ownedHeap r).union acc)
        PartialState.empty)
  let memState : PartialState :=
    fixedMems.foldr (fun p acc => (memHeap p).union acc) PartialState.empty
  have hRegMem : regState.Disjoint memState := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r
      right
      simp [memState, fixedMems, memHeap, PartialState.singletonMem,
        PartialState.union, PartialState.empty]
    · intro a
      left
      simp [regState, fixedRegs, ownedRegs, fixedHeap, ownedHeap,
        PartialState.singletonReg, PartialState.union, PartialState.empty]
    · intro a
      exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
  have hAll :
      (((fixedRegs.foldr (fun r acc => (r ↦ᵣ fixedVal r) ** acc) empAssertion) **
        (ownedRegs.foldr (fun r acc => regOwn r ** acc) empAssertion)) **
        (fixedMems.foldr (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion))
        (regState.union memState) := by
    exact ⟨regState, memState, hRegMem, rfl, hRegs, hMems⟩
  have hRegions :
      (bytesRegion (0x200000 : Word) hvbfBytes32 **
        bytesRegion (0x200100 : Word) hvbfBytes32 **
        bytesRegion Expected
          (hvbfWrittenImage (100000 : Word) (50000 : Word) hvbfBytes32))
        hvbfRegionsState := by
    rw [hwz]
    exact hvbfRegions_inhabited
  have hBaseRegion : (regState.union memState).Disjoint hvbfRegionsState := by
    apply hvbfRegions_disjoint_of_frame
    intro a ha
    simp [regState, memState, fixedRegs, ownedRegs, fixedHeap, ownedHeap,
      fixedMems, memHeap, PartialState.union, PartialState.empty,
      PartialState.singletonReg, PartialState.singletonMem] at ha
    split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
  have hAllRegion :
      (((((fixedRegs.foldr (fun r acc => (r ↦ᵣ fixedVal r) ** acc) empAssertion) **
        (ownedRegs.foldr (fun r acc => regOwn r ** acc) empAssertion)) **
        (fixedMems.foldr (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion)) **
        (bytesRegion (0x200000 : Word) hvbfBytes32 **
          bytesRegion (0x200100 : Word) hvbfBytes32 **
          bytesRegion Expected
            (hvbfWrittenImage (100000 : Word) (50000 : Word) hvbfBytes32)))
        ((regState.union memState).union hvbfRegionsState)) := by
    exact ⟨regState.union memState, hvbfRegionsState, hBaseRegion, rfl,
      hAll, hRegions⟩
  refine ⟨(regState.union memState).union hvbfRegionsState, ?_⟩
  dsimp [regState, memState, fixedRegs, fixedVal, ownedRegs, fixedMems,
    fixedHeap, ownedHeap, memHeap, hvbfBytes32, k73PostOwn, tailRest,
    tailRestCore, frameSlotsSaved, hvbfSaved, k73Saved, hvbfFrame, k73Frame,
    k74FlatFrame]
    at hAllRegion ⊢
  simp [sepConj_assoc', sepConj_emp_right', signExtend12]
    at hAllRegion ⊢
  xperm_chunked hAllRegion

/-! ## §7  Closed K74 wrapper witness (#12979)

The wrapper theorem is instantiated at a concrete increase arm.  Its K73
premise is the already-closed Route-B adapter, while the two code-monotonicity
premises are discharged from the linked address ranges (the public pair
lemmas in `HeaderValidateBaseFeeSpec`).  This is deliberately a closed
inhabitant: the registry row below points at this theorem rather than at the
open static-premise inhabitant. -/

private abbrev k74WitnessBytes32 : List (BitVec 8) := List.replicate 32 0

private abbrev k74WitnessOutT : List (BitVec 8) :=
  EvmAsm.Codegen.U256MulU64Be.copyState
    (EvmAsm.Codegen.U256MulU64Be.mulState k74WitnessBytes32 (2500 : Word) 32)
    k74WitnessBytes32 32

private abbrev k74WitnessQ1 (T : List (BitVec 8)) (target : Word) : List (BitVec 8) :=
  EvmAsm.Codegen.U256DivU64BeSAsm.u256DivU64BeQuotBytes T T target

private abbrev k74WitnessQ2 (T : List (BitVec 8)) (target : Word) : List (BitVec 8) :=
  EvmAsm.Codegen.U256DivU64BeSAsm.u256DivU64BeQuotBytes
    (k74WitnessQ1 T target) (k74WitnessQ1 T target) 8

private abbrev k74WitnessAcc : List (BitVec 8) :=
  EvmAsm.Codegen.U256MulU64Be.mulState k74WitnessBytes32 (2500 : Word) 32

private abbrev k74WitnessN73 : Nat :=
  14 + 3857 + (10 +
    (EvmAsm.Codegen.U256DivU64BeSAsm.u256DivU64BeInPlaceFn Expected
      ((10000 : Word) >>> 1) k74WitnessOutT).body.steps +
    (EvmAsm.Codegen.U256DivU64BeSAsm.u256DivU64BeInPlaceFn Expected 8
      (k74WitnessQ1 k74WitnessOutT ((10000 : Word) >>> 1))).body.steps +
    (12 + (1 + (((1 + 1) + (1 +
      (EvmAsm.Codegen.U256FromU64BeSAsm.u256FromU64BeFn 1 Expected
        (k74WitnessQ2 k74WitnessOutT ((10000 : Word) >>> 1))).body.steps + 1)) + 1)))) +
    1000000

private def k74WitnessWhole : CodeReq := wholeCode

private def k74WitnessCode : CodeReq :=
  hvbfCode.union (k74WitnessWhole.union u256EqCode)

private theorem k74Witness_hvbf_u256eq_disjoint :
    hvbfCode.Disjoint u256EqCode := by
  unfold hvbfCode hvbfProg u256EqCode
  apply CodeReq.Disjoint.ofProg_ranges <;> decide

theorem header_validate_base_fee_spec_within_inhabited :
    cpsTripleWithin
      (27 + k74WitnessN73 +
        (U256EqSAsm.u256EqBody (0x200000 : Word)
          Expected k74WitnessBytes32 k74WitnessOutT).steps)
      H (H + 40) k74WitnessCode
      (hvbfPre (0xa0050048 : Word) (0xa0050038 : Word) (0xa0050000 : Word)
        (H + 40) 0 (0x200000 : Word) 10000 7500 (0x200100 : Word)
        0 0 0 0 k74WitnessBytes32 k74WitnessOutT k74WitnessBytes32
        (k73_incr_env (0xa0050000 : Word) 0 0 0 0 0 0 k74WitnessAcc empAssertion))
      (hvbfFinalRouteB (0xa0050048 : Word) (0xa0050038 : Word) (0xa0050000 : Word)
        (H + 40) 0 (0x200000 : Word) 0 0 ((10000 : Word) >>> 1) 0 0
        10000 7500 (0x200100 : Word) k74WitnessBytes32 k74WitnessBytes32
        (k73_incr_outj (0xa0050000 : Word) (0x200100 : Word) 7500
          ((10000 : Word) >>> 1) k74WitnessBytes32 k74WitnessAcc empAssertion)) := by
  have hk73 : cpsTripleWithin k74WitnessN73 K73 (H + 40) k74WitnessWhole
      ((.x1 ↦ᵣ (H + 40)) **
        k73PreRest (0xa0050038 : Word) (0xa0050000 : Word) (0x200000 : Word)
          0 0 0 0 10000 7500 (0x200100 : Word) k74WitnessBytes32
          k74WitnessOutT k74WitnessBytes32 (H + 40) 0
          (k73_incr_env (0xa0050000 : Word) 0 0 0 0 0 0 k74WitnessAcc empAssertion))
      ((.x1 ↦ᵣ (H + 40)) **
        k73RouteBCallPost (0xa0050038 : Word) (0xa0050000 : Word) (H + 40) 0
          (0x200000 : Word) 0 0 ((10000 : Word) >>> 1) 0 0 7500 10000
          (0x200100 : Word) k74WitnessBytes32 k74WitnessBytes32
          (k73_incr_outj (0xa0050000 : Word) (0x200100 : Word) 7500
            ((10000 : Word) >>> 1) k74WitnessBytes32 k74WitnessAcc empAssertion)) := by
    convert EvmAsm.Codegen.HeaderValidateBaseFeeCompositionIncreaseRoute.k73_incr_route_adapter_inhabited using 1 <;> rfl
  apply header_validate_base_fee_spec_within
    (cr := k74WitnessCode) (k73Code := k74WitnessWhole) (n73 := k74WitnessN73)
    (0xa0050048 : Word) (0xa0050038 : Word) (0xa0050000 : Word) (H + 40) 0
    (0x200000 : Word) 10000 7500 (0x200100 : Word)
    0 0 0 0 0 0 0 0 0 0
    k74WitnessBytes32 k74WitnessOutT k74WitnessBytes32 k74WitnessAcc empAssertion
  · decide
  · decide
  · unfold H; rfl
  · pcf
  · decide
  · have hlen : k74WitnessOutT.length = 32 := by
      exact EvmAsm.Codegen.U256MulU64Be.copyState_len _ _ 32 (by simp [k74WitnessBytes32])
    exact hvbfWrittenImage_wf (gasLimit := (10000 : Word)) (gasUsed := (7500 : Word))
      (parentBytes := k74WitnessBytes32) (expectedBytes := k74WitnessOutT) (by decide) hlen
  · rfl
  · exact EvmAsm.Codegen.U256MulU64Be.copyState_len _ _ 32 (by simp [k74WitnessBytes32])
  · decide
  · exact CodeReq.union_mono_left
  · intro a i h
    have hwhole : k74WitnessWhole a = some i := h
    have hvnone : hvbfCode a = none := by
      cases hv : hvbfCode a with
      | none => exact rfl
      | some j =>
        have hwhole' : wholeCode a = some i := by
          change wholeCode a = some i at hwhole
          exact hwhole
        exact False.elim (k74_hvbf_whole_disjoint hv hwhole')
    exact CodeReq.union_skip hvnone (CodeReq.union_hit hwhole)
  · exact hk73
  · intro a i h
    have hwhole : k74WitnessWhole a = none := by
      cases hw : k74WitnessWhole a with
      | none => exact rfl
      | some j =>
        have hw' : wholeCode a = some j := by
          change wholeCode a = some j at hw
          exact hw
        exact False.elim (k74_whole_u256eq_disjoint hw' h)
    have hvnone : hvbfCode a = none := by
      cases hv : hvbfCode a with
      | none => exact rfl
      | some j =>
        rcases k74Witness_hvbf_u256eq_disjoint a with hleft | hright
        · rw [hv] at hleft
          simp at hleft
        · rw [h] at hright
          simp at hright
    exact CodeReq.union_skip hvnone (CodeReq.union_skip hwhole h)

#print axioms k73_routeB_post_success_split
#print axioms header_validate_base_fee_spec_within_inhabited

end EvmAsm.Codegen.HeaderValidateBaseFeeSpecRef
