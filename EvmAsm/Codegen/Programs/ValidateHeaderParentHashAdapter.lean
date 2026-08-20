/-
  Adapter for the unified `header_validate_parent_hash` contract.

  The machine-facing caller contract owns the claimed output cell and the
  keccak continuation resources explicitly.  This file only changes the
  framing name (`hvphPre` to `hvphEntryRest`) and the fuel presentation; it
  does not erase the outcome-specific resources in the unified post.
-/

import EvmAsm.Codegen.Programs.ValidateHeaderCompose
import EvmAsm.Codegen.Programs.HeaderValidateParentHashUnified

namespace EvmAsm.Codegen.ValidateHeaderCompose

open EvmAsm EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderValidateParentHashSpec
open EvmAsm.Codegen.Proofs

noncomputable section

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_frameSlotsSaved _ _ _)

/-! The strong post used by the caller-facing hcallee adapter.  Keeping the
    claimed/digest/keccak resources in this post is load-bearing: the unified
    witness produces them, and an adapter must not silently discard ownership.
-/
def hvphUnifiedPost
    (sp0 spC ret thisPtr parentPtr parentLen : Word) (vals : Reg → Word)
    (v20 : Word) (thisBytes parentBytes C0 : List (BitVec 8))
    (N rem : Nat) (os : List (BitVec 8)) (F : Assertion) : Assertion :=
  fun s =>
    (⌜headersParentHash_status thisBytes = (0 : Word) ∧
        ∀ q, q < 4 →
          dwordAt (headersParentHash_out thisBytes C0) q =
            dwordAt (keccakBodyDigest parentBytes N rem) q⌝ **
      (HeaderValidateParentHashSpec.hvphPost sp0 thisPtr parentPtr ret
          (0 : Word) vals thisBytes parentBytes **
        hvphMatchExitExtra spC parentPtr parentLen v20 vals parentBytes
          (headersParentHash_out thisBytes C0)
          (keccakBodyDigest parentBytes N rem) N rem F)) s ∨
    (⌜headersParentHash_status thisBytes ≠ (0 : Word)⌝ **
      ((HeaderValidateParentHashSpec.hvphPost sp0 thisPtr parentPtr ret
          (1 : Word) vals thisBytes parentBytes **
        claimedOwn (headersParentHash_out thisBytes C0)) **
          hvphSuccKeccakAmb spC v20 os (List.replicate 32 0) F)) s ∨
    ∃ k, k < 4 ∧
      (⌜headersParentHash_status thisBytes = (0 : Word) ∧
          (∀ j, j < k →
            dwordAt (headersParentHash_out thisBytes C0) j =
              dwordAt (keccakBodyDigest parentBytes N rem) j) ∧
          dwordAt (headersParentHash_out thisBytes C0) k ≠
            dwordAt (keccakBodyDigest parentBytes N rem) k⌝ **
        (HeaderValidateParentHashSpec.hvphPost sp0 thisPtr parentPtr ret
            (2 : Word) vals thisBytes parentBytes **
          hvphMatchExitExtra spC parentPtr parentLen v20 vals parentBytes
            (headersParentHash_out thisBytes C0)
            (keccakBodyDigest parentBytes N rem) N rem F)) s

set_option maxRecDepth 8000 in
/-- Adapt the unified parent-hash specification to the machine-facing hcallee.

    `hHeaderAlign` is the K67 header-base alignment gate and `hOutLen` is the
    explicit 32-byte output-length gate.  Both remain named premises here;
    neither is absorbed into the framing conversion. -/
theorem header_validate_parent_hash_hcallee_from_spec
    (sp0 spC ret thisPtr thisLen parentPtr parentLen : Word)
    (vals : Reg → Word) (v20 : Word)
    (thisBytes parentBytes C0 : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8)) (F : Assertion) (hF : F.pcFree)
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hlenW : thisBytes.length = thisLen.toNat)
    (hlen3 : 3 ≤ thisBytes.length)
    (hclaim0 : C0.length = 32)
    (hHeaderAlign : thisPtr.toNat % 8 = 0)
    (hsover : thisPtr.toNat + thisBytes.length ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < thisBytes.length →
      isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true)
    (hOutLen : (headersParentHash_out thisBytes C0).length = 32)
    (hplen : parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin (40 + 312 + nKeccak N rem) H ret fullCode
      ((.x1 ↦ᵣ ret) **
        ValidateHeaderParentHashCorrespondence.hvphEntryRest
          sp0 thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes **
        claimedOwn C0 ** hvphSuccKeccakAmb spC v20 os (List.replicate 32 0) F)
      (hvphUnifiedPost sp0 spC ret thisPtr parentPtr parentLen vals v20
        thisBytes parentBytes C0 N rem os F) := by
  have h := header_validate_parent_hash_spec_within
    sp0 spC ret thisPtr thisLen parentPtr parentLen vals v20
    thisBytes parentBytes C0 N rem os F hF hret hspC hlenW hlen3 hclaim0
    hHeaderAlign hsover hsvalid hOutLen hplen hlen hrem_le hos halign_zk hover
    hNbound hrem64 hb8i hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simpa [HeaderValidateParentHashSpec.hvphPre,
        ValidateHeaderParentHashCorrespondence.hvphEntryRest] using hp)
    (fun _ hq => hq) h

/-! Fuel reconciliation is independent of the adapter's large assertion.  The
    caller supplies its own `n` and only needs to prove that it dominates the
    witness's `40 + 312 + nKeccak N rem` bound. -/
theorem header_validate_parent_hash_hcallee_mono_fuel
    {bound n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} (hbound : bound ≤ n)
    (hbase : cpsTripleWithin bound entry exit_ cr P Q) :
    cpsTripleWithin n entry exit_ cr P Q :=
  cpsTripleWithin_mono_nSteps hbound hbase

/-! A real consumer of the strong hcallee.  This is the same direct-JAL seam
    as the older common-post call theorem, but it preserves the unified
    outcome post (including the Claimed/digest/keccak resources) instead of
    pretending those resources were unchanged. -/
set_option maxRecDepth 8000 in
theorem validate_header_parent_hash_unified_call_spec_within
    {cr calleeCode : CodeReq} {n : Nat}
    (sp0 spC thisPtr thisLen parentPtr parentLen oldRa : Word)
    (vals : Reg → Word)
    (thisBytes parentBytes C0 : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8)) (v20 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hdisj : (CodeReq.singleton
      ValidateHeaderParentHashCorrespondence.A
      (.JAL .x1 (jalOff GuestAddrs.header_validate_parent_hash
        (GuestAddrs.validate_header + 244)))).Disjoint calleeCode)
    (hcallerDisj : ValidateHeaderParentHashCorrespondence.callerCode.Disjoint calleeCode)
    (hcode : ∀ a i, (ValidateHeaderParentHashCorrespondence.callerCode.union calleeCode) a = some i →
      cr a = some i)
    (hcallee : cpsTripleWithin n
      ValidateHeaderParentHashCorrespondence.Callee
      ValidateHeaderParentHashCorrespondence.Ret calleeCode
      ((.x1 ↦ᵣ ValidateHeaderParentHashCorrespondence.Ret) **
        ValidateHeaderParentHashCorrespondence.hvphEntryRest
          sp0 thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes **
        claimedOwn C0 ** hvphSuccKeccakAmb spC v20 os (List.replicate 32 0) G)
      (hvphUnifiedPost sp0 spC ValidateHeaderParentHashCorrespondence.Ret
        thisPtr parentPtr parentLen vals v20 thisBytes parentBytes C0 N rem os G)) :
    cpsTripleWithin (1 + n)
      ValidateHeaderParentHashCorrespondence.A
      ValidateHeaderParentHashCorrespondence.Ret cr
      ((.x1 ↦ᵣ oldRa) **
        ValidateHeaderParentHashCorrespondence.hvphEntryRest
          sp0 thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes **
        claimedOwn C0 ** hvphSuccKeccakAmb spC v20 os (List.replicate 32 0) G)
      (hvphUnifiedPost sp0 spC ValidateHeaderParentHashCorrespondence.Ret
        thisPtr parentPtr parentLen vals v20 thisBytes parentBytes C0 N rem os G) := by
  let Prest : Assertion :=
    ValidateHeaderParentHashCorrespondence.hvphEntryRest
        sp0 thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes **
      claimedOwn C0 ** hvphSuccKeccakAmb spC v20 os (List.replicate 32 0) G
  let Q : Assertion :=
    hvphUnifiedPost sp0 spC ValidateHeaderParentHashCorrespondence.Ret
      thisPtr parentPtr parentLen vals v20 thisBytes parentBytes C0 N rem os G
  have hPrest : Prest.pcFree := by
    unfold Prest claimedOwn
    pcf
    exact hG
  have htarget : ValidateHeaderParentHashCorrespondence.A +
      signExtend21 (jalOff GuestAddrs.header_validate_parent_hash
        (GuestAddrs.validate_header + 244)) =
      ValidateHeaderParentHashCorrespondence.Callee := by
    change BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 244 + _ =
      BitVec.ofNat 64 GuestAddrs.header_validate_parent_hash
    exact jalOff_correct_add GuestAddrs.header_validate_parent_hash
      GuestAddrs.validate_header 244 (by decide) (by decide) (by decide) (by decide)
  have hret : (ValidateHeaderParentHashCorrespondence.A + 4) &&&
      ~~~(1 : Word) = ValidateHeaderParentHashCorrespondence.A + 4 := by decide
  have hRet : ValidateHeaderParentHashCorrespondence.A + 4 =
      ValidateHeaderParentHashCorrespondence.Ret := by decide
  have hcallee' : cpsTripleWithin n
      ValidateHeaderParentHashCorrespondence.Callee
      ((ValidateHeaderParentHashCorrespondence.A + 4) &&& ~~~(1 : Word))
      calleeCode ((.x1 ↦ᵣ ValidateHeaderParentHashCorrespondence.Ret) ** Prest) Q := by
    rw [hret, hRet]
    exact hcallee
  have hcall := WP.cpsCallWithin
    (nSteps := n)
    (callerPC := ValidateHeaderParentHashCorrespondence.A)
    (calleeEntry := ValidateHeaderParentHashCorrespondence.Callee)
    (vOld := oldRa) (calleeCode := calleeCode)
    (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.header_validate_parent_hash
      (GuestAddrs.validate_header + 244))
    htarget hret hPrest hdisj hcallee'
  have hcallCode : ∀ a i,
      ((CodeReq.singleton ValidateHeaderParentHashCorrespondence.A
        (.JAL .x1 (jalOff GuestAddrs.header_validate_parent_hash
          (GuestAddrs.validate_header + 244)))).union calleeCode) a = some i →
      (ValidateHeaderParentHashCorrespondence.callerCode.union calleeCode) a = some i := by
    exact CodeReq.union_split_mono
      (fun a i h => CodeReq.union_mono_left a i
        (ValidateHeaderParentHashCorrespondence.validateHeader_parentHash_jal_mem a i h))
      (fun a i h => CodeReq.mono_union_right hcallerDisj
        (fun _ _ h' => h') a i h)
  have hcallC := cpsTripleWithin_extend_code hcallCode hcall
  have hcallCr := cpsTripleWithin_extend_code hcode hcallC
  simpa [Prest, Q] using hcallCr

/-! ## Anti-vacuity witness

    This is a concrete witness for the complete `hvphEntryRest` premise, not a
    symbolic-value coverage claim.  The frame is at `0xfc8`, while the two
    byte regions use independently owned bases `0x2000` and `0x3000`; hence it
    establishes isolation satisfiability only.  It does **not** establish that
    a validate-header caller can supply those pointers: in the real
    composition both RLPs are sibling subranges of one input buffer. -/
/-! A deliberately degenerate variant (`sp0 = 0x100`, both pointers and
    lengths zero, and both byte lists empty) also satisfies the same assertion;
    the frame is valid at that non-wrapping stack address.  Thus the premise is
    weak, not strong: non-empty distinct sibling coverage is an obligation on
    the caller, discharged via `bytesRegion_append` under the K67 8-alignment
    premise, not by this theorem.  The attempted `sp0 = 0` witness fails only
    on wrapped frame-address dword validity. -/

def hvphInhabitantRegs : List (Reg × Word) :=
  [(.x2, 0xFE8), (.x8, 0), (.x9, 0), (.x18, 0),
   (.x10, 0x2000), (.x11, 1), (.x12, 0x3000), (.x13, 1),
   (.x5, 0), (.x6, 0), (.x7, 0), (.x28, 0), (.x29, 0), (.x30, 0),
   (.x31, 0), (.x0, 0)]

def hvphInhabitantMems : List (Word × Word) :=
  [(0xFC8, 0), (0xFD0, 0), (0xFD8, 0), (0xFE0, 0),
   (0x2000, 0), (0x3000, 0)]

def hvphInhabitantFrameMems : List (Word × Word) :=
  [(0xFC8, 0), (0xFD0, 0), (0xFD8, 0), (0xFE0, 0)]

def hvphInhabitantRegHeap : (Reg × Word) → PartialState :=
  fun p => PartialState.singletonReg p.1 p.2

def hvphInhabitantMemHeap : (Word × Word) → PartialState :=
  fun p => PartialState.singletonMem p.1 p.2

def hvphInhabitantRegAtom : (Reg × Word) → Assertion := fun p => p.1 ↦ᵣ p.2
def hvphInhabitantMemAtom : (Word × Word) → Assertion := fun p => p.1 ↦ₘ p.2

def hvphInhabitantRegFold : Assertion :=
  hvphInhabitantRegs.foldr (fun p acc => hvphInhabitantRegAtom p ** acc) empAssertion

def hvphInhabitantMemFold : Assertion :=
  hvphInhabitantMems.foldr (fun p acc => hvphInhabitantMemAtom p ** acc) empAssertion

def hvphInhabitantRegHeapFold : PartialState :=
  hvphInhabitantRegs.foldr
    (fun p acc => (hvphInhabitantRegHeap p).union acc) PartialState.empty

def hvphInhabitantMemHeapFold : PartialState :=
  hvphInhabitantMems.foldr
    (fun p acc => (hvphInhabitantMemHeap p).union acc) PartialState.empty

theorem hvphInhabitantRegFold_sat :
    hvphInhabitantRegFold hvphInhabitantRegHeapFold := by
  apply sepConj_foldr_satisfiable hvphInhabitantRegAtom
    hvphInhabitantRegHeap hvphInhabitantRegs
  · intro p hp
    rfl
  · have hd : hvphInhabitantRegs.Pairwise (fun p q => p.1 ≠ q.1) := by decide
    exact List.Pairwise.imp
      (fun {_ _} h => routeInhabitantRegSingletonDisjoint h) hd

theorem hvphInhabitantMemFold_sat :
    hvphInhabitantMemFold hvphInhabitantMemHeapFold := by
  apply sepConj_foldr_satisfiable hvphInhabitantMemAtom
    hvphInhabitantMemHeap hvphInhabitantMems
  · intro p hp
    rcases p with ⟨a, v⟩
    rcases (by simpa [hvphInhabitantMems] using hp) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals exact ⟨rfl, by decide⟩
  · have hd : hvphInhabitantMems.Pairwise (fun p q => p.1 ≠ q.1) := by decide
    exact List.Pairwise.imp
      (fun {_ _} h => routeInhabitantMemSingletonDisjoint h) hd

theorem hvphInhabitantCross :
    ∀ p ∈ hvphInhabitantRegs, ∀ q ∈ hvphInhabitantMems,
      (hvphInhabitantRegHeap p).Disjoint (hvphInhabitantMemHeap q) := by
  intro p hp q hq
  unfold hvphInhabitantRegHeap hvphInhabitantMemHeap
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

def hvphInhabitantAssertion : Assertion :=
  hvphInhabitantRegFold ** hvphInhabitantMemFold

def hvphInhabitantHeap : PartialState :=
  hvphInhabitantRegHeapFold.union hvphInhabitantMemHeapFold

theorem hvphInhabitantSat :
    hvphInhabitantAssertion hvphInhabitantHeap := by
  exact sepConj_foldr_cross_satisfiable hvphInhabitantRegAtom
    hvphInhabitantRegHeap hvphInhabitantRegs hvphInhabitantMemAtom
    hvphInhabitantMemHeap hvphInhabitantMems hvphInhabitantRegFold_sat
    hvphInhabitantMemFold_sat hvphInhabitantCross

def hvphInhabitantOwnReg (r : Reg) : Prop :=
  r = .x5 ∨ r = .x6 ∨ r = .x7 ∨ r = .x28 ∨
    r = .x29 ∨ r = .x30 ∨ r = .x31

local instance : DecidablePred hvphInhabitantOwnReg := Classical.decPred _

noncomputable def hvphInhabitantMixedFold : Assertion :=
  hvphInhabitantRegs.foldr
    (fun p acc =>
      if hvphInhabitantOwnReg p.1 then regOwn p.1 ** acc else (p.1 ↦ᵣ p.2) ** acc)
    empAssertion

theorem hvphInhabitantRegFold_to_mixed (xs : List (Reg × Word)) : ∀ h,
    xs.foldr (fun p acc => (p.1 ↦ᵣ p.2) ** acc) empAssertion h →
    xs.foldr
      (fun p acc =>
        if hvphInhabitantOwnReg p.1 then regOwn p.1 ** acc
        else (p.1 ↦ᵣ p.2) ** acc) empAssertion h := by
  induction xs with
  | nil => simp
  | cons p ps ih =>
    intro h
    simp only [List.foldr]
    by_cases hown : hvphInhabitantOwnReg p.1
    · rw [if_pos hown]
      apply sepConj_mono
        (P := (p.1 ↦ᵣ p.2))
        (Q := ps.foldr (fun p acc => (p.1 ↦ᵣ p.2) ** acc) empAssertion)
        (P' := regOwn p.1)
        (Q' := ps.foldr
          (fun p acc =>
            if hvphInhabitantOwnReg p.1 then regOwn p.1 ** acc
            else (p.1 ↦ᵣ p.2) ** acc) empAssertion)
      · intro _ hp
        exact regIs_to_regOwn p.1 p.2 _ hp
      · intro h' hp
        exact ih h' hp
    · rw [if_neg hown]
      apply sepConj_mono
        (P := (p.1 ↦ᵣ p.2))
        (Q := ps.foldr (fun p acc => (p.1 ↦ᵣ p.2) ** acc) empAssertion)
        (P' := (p.1 ↦ᵣ p.2))
        (Q' := ps.foldr
          (fun p acc =>
            if hvphInhabitantOwnReg p.1 then regOwn p.1 ** acc
            else (p.1 ↦ᵣ p.2) ** acc) empAssertion)
      · intro _ hp
        exact hp
      · intro h' hp
        exact ih h' hp

def hvphInhabitantFrameExact : Assertion :=
  hvphInhabitantFrameMems.foldr
    (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion

def hvphInhabitantFrameOwn : Assertion :=
  hvphInhabitantFrameMems.foldr
    (fun p acc => memOwn p.1 ** acc) empAssertion

theorem hvphInhabitantFrame_to_own (xs : List (Word × Word)) : ∀ h,
    xs.foldr (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion h →
    xs.foldr (fun p acc => memOwn p.1 ** acc) empAssertion h := by
  induction xs with
  | nil => simp
  | cons p ps ih =>
    intro h
    apply sepConj_mono
      (P := (p.1 ↦ₘ p.2))
      (Q := ps.foldr (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion)
      (P' := memOwn p.1)
      (Q' := ps.foldr (fun p acc => memOwn p.1 ** acc) empAssertion)
    · intro _ hp
      exact ⟨p.2, hp⟩
    · intro h' hp
      exact ih h' hp

theorem hvphEntryRest_inhabited :
    ∃ h,
      ValidateHeaderParentHashCorrespondence.hvphEntryRest
        (0xFE8 : Word) (0x2000 : Word) (1 : Word)
        (0x3000 : Word) (1 : Word) (fun _ => 0) [0] [0] h := by
  refine ⟨hvphInhabitantHeap, ?_⟩
  unfold ValidateHeaderParentHashCorrespondence.hvphEntryRest
    ValidateHeaderParentHashCorrespondence.hvphFrame
    ValidateHeaderParentHashCorrespondence.hvphSavedFrame
    EvmAsm.Rv64.SAsm.regsAt
  simp only [bytesRegion, bytesRegionAux]
  norm_num
  simp only [sepConj_emp_right']
  have hExact :
      (hvphInhabitantRegFold ** hvphInhabitantFrameExact **
        ((0x2000 : Word) ↦ₘ 0) ** ((0x3000 : Word) ↦ₘ 0))
        hvphInhabitantHeap := by
    have h := hvphInhabitantSat
    simp only [hvphInhabitantAssertion, hvphInhabitantRegFold,
      hvphInhabitantMemFold, hvphInhabitantMems, hvphInhabitantMemHeapFold,
      hvphInhabitantMemHeap, hvphInhabitantFrameExact,
      hvphInhabitantFrameMems, hvphInhabitantRegs, hvphInhabitantHeap,
      hvphInhabitantRegHeapFold, hvphInhabitantRegHeap,
      hvphInhabitantRegAtom, hvphInhabitantMemAtom, List.foldr] at h ⊢
    sep_perm h
  have hWeak :
      (hvphInhabitantMixedFold ** hvphInhabitantFrameOwn **
        ((0x2000 : Word) ↦ₘ 0) ** ((0x3000 : Word) ↦ₘ 0))
        hvphInhabitantHeap := by
    have hFrameBytes := sepConj_mono_right
      (sepConj_mono_left (hvphInhabitantFrame_to_own hvphInhabitantFrameMems))
      _ hExact
    exact sepConj_mono_left
      (hvphInhabitantRegFold_to_mixed hvphInhabitantRegs) _ hFrameBytes
  simp only [hvphInhabitantMixedFold, hvphInhabitantOwnReg,
    hvphInhabitantFrameOwn, hvphInhabitantFrameMems, hvphInhabitantRegs,
    List.foldr] at hWeak
  have hneg : signExtend12 (-32 : BitVec 12) =
      (0xFFFFFFFFFFFFFFE0 : Word) := by decide
  rw [hneg] at ⊢
  have hf0 : (0xFE8 : Word) + 0xFFFFFFFFFFFFFFE0 = 0xFC8 := by decide
  rw [hf0] at ⊢
  norm_num at hWeak ⊢
  simp at hWeak ⊢
  simp only [sepConj_emp_right'] at hWeak ⊢
  sep_perm hWeak

end

end EvmAsm.Codegen.ValidateHeaderCompose
