/-
  EvmAsm.Codegen.Programs.RlpRecursiveDecodeLinkedSpec

  The #12749 linked-image tie: `itemsSound_all` is proven over the synthetic
  `decCr`, whose three `CodeReq.ofProg` legs are (since the pin move) the
  linked direct-JAL programs at the linked `GuestAddrs` entries — anchored by
  `recursiveDecodeDirectCode_eq_decCr`.  This module wraps that knot into the
  production adapter's ABI vocabulary: a caller-agnostic, entry-rooted
  `cpsTripleWithin` at `rlp_recursive_decode_items` from
  `productionItemsPre` to an existentially-quantified `productionItemsPost`
  (status and final frame bytes are outputs, not inputs), and instantiates
  the adapter's post-parametric call rule with it.

  Deliberately caller-agnostic: nothing here mentions `rlp_walk_next_shared`
  or any descent-site shape — under #12843's architecture A the tie must hold
  for an entry-rooted validation call, and it does, because `itemsSound_all`
  quantifies over every entry condition.  The depth cap stays a parameter:
  the theorem is stated over `rlpRecursiveDecodeDepthCap` (referenced, never
  duplicated as a literal).
-/

import EvmAsm.Codegen.Programs.RlpRecursiveDecodeDirect
import EvmAsm.Codegen.Programs.RlpValidatePayloadProductionAdapter
import EvmAsm.Codegen.Programs.RlpRecursiveDecodeProductionBridge
import EvmAsm.Rv64.RLP.RecDecode.Knot

namespace EvmAsm.Codegen.RlpValidatePayloadProductionAdapter

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.RecDecode

set_option maxRecDepth 8000

/-! ## Local PartialState helpers

    `SepLogic` keeps `union_assoc` and the disjointness climbs private; the
    fold below needs exactly these three facts, so they are reproduced here
    in fieldwise form. -/

private theorem pUnion_assoc (h1 h2 h3 : PartialState) :
    (h1.union h2).union h3 = h1.union (h2.union h3) := by
  simp only [PartialState.union, PartialState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext r; cases h1.regs r <;> simp
  · funext a; cases h1.mem a <;> simp
  · funext a; cases h1.code a <;> simp
  · cases h1.pc <;> simp
  · cases h1.publicValues <;> simp
  · cases h1.privateInput <;> simp
  · cases h1.inputBufBase <;> simp

private theorem disjoint_union_right_local {h1 h2 h3 : PartialState}
    (d1 : h1.Disjoint h3) (d2 : h2.Disjoint h3) :
    (h1.union h2).Disjoint h3 := by
  obtain ⟨d1r, d1m, d1c, d1p, d1v, d1i, d1b⟩ := d1
  obtain ⟨d2r, d2m, d2c, d2p, d2v, d2i, d2b⟩ := d2
  refine ⟨fun r => ?_, fun a => ?_, fun a => ?_, ?_, ?_, ?_, ?_⟩
  · rcases d1r r with h | h
    · rcases d2r r with h' | h'
      · exact Or.inl (by simp only [PartialState.union, h, h'])
      · exact Or.inr h'
    · exact Or.inr h
  · rcases d1m a with h | h
    · rcases d2m a with h' | h'
      · exact Or.inl (by simp only [PartialState.union, h, h'])
      · exact Or.inr h'
    · exact Or.inr h
  · rcases d1c a with h | h
    · rcases d2c a with h' | h'
      · exact Or.inl (by simp only [PartialState.union, h, h'])
      · exact Or.inr h'
    · exact Or.inr h
  · rcases d1p with h | h
    · rcases d2p with h' | h'
      · exact Or.inl (by simp only [PartialState.union, h, h'])
      · exact Or.inr h'
    · exact Or.inr h
  · rcases d1v with h | h
    · rcases d2v with h' | h'
      · exact Or.inl (by simp only [PartialState.union, h, h'])
      · exact Or.inr h'
    · exact Or.inr h
  · rcases d1i with h | h
    · rcases d2i with h' | h'
      · exact Or.inl (by simp only [PartialState.union, h, h'])
      · exact Or.inr h'
    · exact Or.inr h
  · rcases d1b with h | h
    · rcases d2b with h' | h'
      · exact Or.inl (by simp only [PartialState.union, h, h'])
      · exact Or.inr h'
    · exact Or.inr h

/-- Grow the right summand: disjointness of one heap with two others
    gives disjointness with their union. -/
private theorem disjoint_union_left_local {h1 h2 h3 : PartialState}
    (d1 : h1.Disjoint h2) (d2 : h1.Disjoint h3) :
    h1.Disjoint (h2.union h3) := by
  obtain ⟨d1r, d1m, d1c, d1p, d1v, d1i, d1b⟩ := d1
  obtain ⟨d2r, d2m, d2c, d2p, d2v, d2i, d2b⟩ := d2
  refine ⟨fun r => ?_, fun a => ?_, fun a => ?_, ?_, ?_, ?_, ?_⟩
  · rcases d1r r with h | h
    · exact Or.inl h
    · rcases d2r r with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by simp only [PartialState.union, h, h'])
  · rcases d1m a with h | h
    · exact Or.inl h
    · rcases d2m a with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by simp only [PartialState.union, h, h'])
  · rcases d1c a with h | h
    · exact Or.inl h
    · rcases d2c a with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by simp only [PartialState.union, h, h'])
  · rcases d1p with h | h
    · exact Or.inl h
    · rcases d2p with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by simp only [PartialState.union, h, h'])
  · rcases d1v with h | h
    · exact Or.inl h
    · rcases d2v with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by simp only [PartialState.union, h, h'])
  · rcases d1i with h | h
    · exact Or.inl h
    · rcases d2i with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by simp only [PartialState.union, h, h'])
  · rcases d1b with h | h
    · exact Or.inl h
    · rcases d2b with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by simp only [PartialState.union, h, h'])

/-- Right-elimination: keep only the right summand's disjointness. -/
private theorem disjoint_right_of_disjoint_union {h1 h2 h3 : PartialState}
    (hd : h1.Disjoint (h2.union h3)) : h1.Disjoint h3 := by
  obtain ⟨dr, dm, dc, dp, dv, di, db⟩ := hd
  refine ⟨fun r => ?_, fun a => ?_, fun a => ?_, ?_, ?_, ?_, ?_⟩
  · rcases dr r with h | h
    · exact Or.inl h
    · simp only [PartialState.union] at h
      rcases hv : h2.regs r with _ | v
      · rw [hv] at h; exact Or.inr h
      · rw [hv] at h; simp at h
  · rcases dm a with h | h
    · exact Or.inl h
    · simp only [PartialState.union] at h
      rcases hv : h2.mem a with _ | v
      · rw [hv] at h; exact Or.inr h
      · rw [hv] at h; simp at h
  · rcases dc a with h | h
    · exact Or.inl h
    · simp only [PartialState.union] at h
      rcases hv : h2.code a with _ | v
      · rw [hv] at h; exact Or.inr h
      · rw [hv] at h; simp at h
  · rcases dp with h | h
    · exact Or.inl h
    · simp only [PartialState.union] at h
      rcases hv : h2.pc with _ | v
      · rw [hv] at h; exact Or.inr h
      · rw [hv] at h; simp at h
  · rcases dv with h | h
    · exact Or.inl h
    · simp only [PartialState.union] at h
      rcases hv : h2.publicValues with _ | v
      · rw [hv] at h; exact Or.inr h
      · rw [hv] at h; simp at h
  · rcases di with h | h
    · exact Or.inl h
    · simp only [PartialState.union] at h
      rcases hv : h2.privateInput with _ | v
      · rw [hv] at h; exact Or.inr h
      · rw [hv] at h; simp at h
  · rcases db with h | h
    · exact Or.inl h
    · simp only [PartialState.union] at h
      rcases hv : h2.inputBufBase with _ | v
      · rw [hv] at h; exact Or.inr h
      · rw [hv] at h; simp at h

/-- Left-elimination: keep only the left summand's disjointness. -/
private theorem disjoint_left_of_disjoint_union {h1 h2 h3 : PartialState}
    (hd : h1.Disjoint (h2.union h3)) : h1.Disjoint h2 := by
  obtain ⟨dr, dm, dc, dp, dv, di, db⟩ := hd
  refine ⟨fun r => ?_, fun a => ?_, fun a => ?_, ?_, ?_, ?_, ?_⟩
  · rcases dr r with h | h
    · exact Or.inl h
    · rcases hv : h2.regs r with _ | v
      · exact Or.inr rfl
      · simp only [PartialState.union, hv] at h; simp at h
  · rcases dm a with h | h
    · exact Or.inl h
    · rcases hv : h2.mem a with _ | v
      · exact Or.inr rfl
      · simp only [PartialState.union, hv] at h; simp at h
  · rcases dc a with h | h
    · exact Or.inl h
    · rcases hv : h2.code a with _ | v
      · exact Or.inr rfl
      · simp only [PartialState.union, hv] at h; simp at h
  · rcases dp with h | h
    · exact Or.inl h
    · rcases hv : h2.pc with _ | v
      · exact Or.inr rfl
      · simp only [PartialState.union, hv] at h; simp at h
  · rcases dv with h | h
    · exact Or.inl h
    · rcases hv : h2.publicValues with _ | v
      · exact Or.inr rfl
      · simp only [PartialState.union, hv] at h; simp at h
  · rcases di with h | h
    · exact Or.inl h
    · rcases hv : h2.privateInput with _ | v
      · exact Or.inr rfl
      · simp only [PartialState.union, hv] at h; simp at h
  · rcases db with h | h
    · exact Or.inl h
    · rcases hv : h2.inputBufBase with _ | v
      · exact Or.inr rfl
      · simp only [PartialState.union, hv] at h; simp at h

/-! ## Right-nested own-chains and the snapshot split -/

/-- The eleven callee-scratch registers `productionItemsPre` owns via
    `regOwn`, in `exposedRegs` order. -/
private def prodOwnRegs : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x10, .x11, .x14, .x17]

/-- Right-nested `regOwn` chain with an arbitrary tail assertion. -/
private def regOwnR : List Reg → Assertion → Assertion
  | [], tail => tail
  | r :: rest, tail => regOwn r ** regOwnR rest tail

/-- Right-nested `regIs` chain with an arbitrary tail assertion. -/
private def regIsR (rf : RegFile) : List Reg → Assertion → Assertion
  | [], tail => tail
  | r :: rest, tail => regIs r (rf.get r) ** regIsR rf rest tail

/-- The register-file snapshot of a machine state. -/
private def snapRf (s : MachineState) : RegFile := fun r => s.getReg r

private theorem snapRf_get (s : MachineState) {r : Reg} (hr : r ≠ .x0) :
    (snapRf s).get r = s.getReg r := by
  simp [snapRf, RegFile.get, hr]

private theorem prodOwnRegs_ne_x0 : ∀ r ∈ prodOwnRegs, r ≠ .x0 := by decide

/-- **Snapshot split**: an owned register chain held at a subheap compatible
    with `s` splits into the same chain of snapshot-valued `regIs` atoms at
    the register part and the untouched tail at the frame part.  This is the
    one new separation-logic fact the linked tie needs: it converts the
    production ABI's `regOwn` transfer into the model's `regFileIs` snapshot
    without strengthening or discarding any ownership. -/
private theorem regOwnR_snap_split (s : MachineState) :
    ∀ (rs : List Reg) (tail : Assertion) (hsub : PartialState),
      (∀ r ∈ rs, r ≠ Reg.x0) → hsub.CompatibleWith s → regOwnR rs tail hsub →
      ∃ h1 h2, h1.Disjoint h2 ∧ h1.union h2 = hsub ∧
        regIsR (snapRf s) rs empAssertion h1 ∧ tail h2 := by
  intro rs
  induction rs with
  | nil =>
    intro tail hsub _ hcompat htail
    refine ⟨PartialState.empty, hsub, ?_, PartialState.union_empty_left, ?_, htail⟩
    · exact PartialState.Disjoint_empty_left
    · show empAssertion PartialState.empty
      rfl
  | cons r rest ih =>
    intro tail hsub hne hcompat hh
    obtain ⟨h1, h2, hd, hu, hown, hrest⟩ := hh
    have hr0 : r ≠ Reg.x0 := hne r (by simp)
    rw [← hu] at hcompat
    obtain ⟨hc1, hc2⟩ := (PartialState.CompatibleWith_union hd).mp hcompat
    obtain ⟨v, hv⟩ := hown
    have hc1' : (PartialState.singletonReg r v).CompatibleWith s := by
      rw [← hv]; exact hc1
    have hrv : s.getReg r = v := PartialState.CompatibleWith_singletonReg.mp hc1'
    have hleaf : regIs r ((snapRf s).get r) h1 := by
      show h1 = PartialState.singletonReg r ((snapRf s).get r)
      rw [hv, snapRf_get s hr0, hrv]
    obtain ⟨h1', ht, hd', hu', hIs', htail'⟩ :=
      ih tail h2 (fun r' hr' => hne r' (by simp [hr'])) hc2 hrest
    -- disjointness: h1 ⊥ (h1' ∪ ht) from hd (hu' : h1'.union ht = h2),
    -- so h1 ⊥ h1' and h1 ⊥ ht
    have hd12 : h1.Disjoint (h1'.union ht) := by rw [hu']; exact hd
    have hd1t : h1.Disjoint ht := disjoint_right_of_disjoint_union hd12
    have hdclimb : (h1.union h1').Disjoint ht :=
      disjoint_union_right_local hd1t hd'
    have huclimb : (h1.union h1').union ht = hsub := by
      rw [pUnion_assoc, hu', hu]
    exact ⟨h1.union h1', ht, hdclimb, huclimb,
      ⟨h1, h1', disjoint_left_of_disjoint_union hd12, rfl, hleaf, hIs'⟩, htail'⟩

/-! ## The pre fold

    The one new separation-logic fact the linked tie needs on the way IN:
    a caller state satisfying `(x1 ↦ᵣ RetPC ** productionItemsPre) ** R`
    already contains the model callee's `asrtM` precondition, witnessed by the
    register-file snapshot of `s`.  No ownership is strengthened or dropped:
    the `regOwn` chain is converted in place to snapshot-valued `regIs` atoms,
    the frame bytes stay owned, and `R` is carried through untouched. -/

/-- **The fold** (pre-decomposition).  `productionItemsPre` is an ownership
    transfer of exactly the resources `itemsSound_all`'s precondition needs,
    so any state satisfying it (with the call machinery's `x1` and the caller's
    frame `R`) satisfies the model's `asrtM … (Reach.exact (snapRf s) …) ** R`
    at the same heap. -/
private theorem productionItemsPre_fold
    (listBase listEnd framePtr : Word)
    (inputBytes frameBytes : List (BitVec 8))
    (hfb : frameBytes.length = FrameBytes)
    (hlistEnd : listEnd = listBase + BitVec.ofNat 64 inputBytes.length)
    (s : MachineState) (R : Assertion)
    (hPR : (((.x1 ↦ᵣ RetPC) ** productionItemsPre listBase listEnd framePtr
      inputBytes frameBytes) ** R).holdsFor s) :
    ∃ A₀, A₀.pcFree ∧
      itemsPreS inputBytes listBase rlpRecursiveDecodeDepthCap framePtr
        (snapRf s) frameBytes A₀ ∧
      (((.x1 ↦ᵣ RetPC) ** asrtM ⟨listBase, inputBytes⟩
        (itemsRw rlpRecursiveDecodeDepthCap framePtr)
        (Reach.exact (snapRf s) frameBytes A₀)) ** R).holdsFor s := by
  obtain ⟨h, hcompat, hPRh⟩ := hPR
  obtain ⟨hXPRE, hR, hd1, hu1, hXPREh, hRh⟩ := hPRh
  obtain ⟨hX, hPRE, hd2, hu2, hXh, hPREh⟩ := hXPREh
  unfold productionItemsPre at hPREh
  obtain ⟨hPINS, hIB, hd3, hu3, hPINSh, hIBh⟩ := hPREh
  -- `**` is right-associative: the pins nest as
  -- `x15 ** (x16 ** (x12 ** (x13 ** CHAIN)))`
  obtain ⟨h15, hR1, hd4, hu4, h15h, hR1h⟩ := hPINSh
  obtain ⟨h16, hR2, hd5, hu5, h16h, hR2h⟩ := hR1h
  obtain ⟨h12, hR3, hd6, hu6, h12h, hR3h⟩ := hR2h
  obtain ⟨h13, hCH, hd7, hu7, h13h, hCHh⟩ := hR3h
  -- the eleven-`regOwn` chain, restated right-nested for the snapshot split
  have hCHh' : regOwnR prodOwnRegs (bytesRegion framePtr frameBytes) hCH := by
    change (regOwn .x5 ** (regOwn .x6 ** (regOwn .x7 ** (regOwn .x28 ** (regOwn .x29 **
      (regOwn .x30 ** (regOwn .x31 ** (regOwn .x10 ** (regOwn .x11 ** (regOwn .x14 **
      (regOwn .x17 ** bytesRegion framePtr frameBytes))))))))))) hCH
    xperm_hyp hCHh
  -- compatibility walk to the chain heap
  rw [← hu1] at hcompat
  obtain ⟨hcXPRE, hcR⟩ := (PartialState.CompatibleWith_union hd1).mp hcompat
  rw [← hu2] at hcXPRE
  obtain ⟨hcX, hcPRE⟩ := (PartialState.CompatibleWith_union hd2).mp hcXPRE
  rw [← hu3] at hcPRE
  obtain ⟨hcPINS, hcIB⟩ := (PartialState.CompatibleWith_union hd3).mp hcPRE
  rw [← hu4] at hcPINS
  obtain ⟨hc15, hcR1⟩ := (PartialState.CompatibleWith_union hd4).mp hcPINS
  rw [← hu5] at hcR1
  obtain ⟨hc16, hcR2⟩ := (PartialState.CompatibleWith_union hd5).mp hcR1
  rw [← hu6] at hcR2
  obtain ⟨hc12, hcR3⟩ := (PartialState.CompatibleWith_union hd6).mp hcR2
  rw [← hu7] at hcR3
  obtain ⟨hc13, hcCH⟩ := (PartialState.CompatibleWith_union hd7).mp hcR3
  obtain ⟨hIsHeap, hFB, hdIs, huIs, hIs', hFBh⟩ :=
    regOwnR_snap_split s prodOwnRegs (bytesRegion framePtr frameBytes) hCH
      prodOwnRegs_ne_x0 hcCH hCHh'
  -- spelled out so `xperm` sees eleven `regIs` atoms, not one opaque
  -- `regIsR` application (xperm does not delta-unfold plain defs)
  have hIsSpelled :
      (regIs Reg.x5 ((snapRf s).get Reg.x5) **
        (regIs Reg.x6 ((snapRf s).get Reg.x6) **
        (regIs Reg.x7 ((snapRf s).get Reg.x7) **
        (regIs Reg.x28 ((snapRf s).get Reg.x28) **
        (regIs Reg.x29 ((snapRf s).get Reg.x29) **
        (regIs Reg.x30 ((snapRf s).get Reg.x30) **
        (regIs Reg.x31 ((snapRf s).get Reg.x31) **
        (regIs Reg.x10 ((snapRf s).get Reg.x10) **
        (regIs Reg.x11 ((snapRf s).get Reg.x11) **
        (regIs Reg.x14 ((snapRf s).get Reg.x14) **
        (regIs Reg.x17 ((snapRf s).get Reg.x17) ** empAssertion))))))))))) hIsHeap :=
    hIs'
  -- pin values read off the state
  have hv15 : s.getReg .x15 = listBase :=
    PartialState.CompatibleWith_singletonReg.mp (by rw [← h15h]; exact hc15)
  have hv16 : s.getReg .x16 = listEnd :=
    PartialState.CompatibleWith_singletonReg.mp (by rw [← h16h]; exact hc16)
  have hv12 : s.getReg .x12 = Cap :=
    PartialState.CompatibleWith_singletonReg.mp (by rw [← h12h]; exact hc12)
  have hv13 : s.getReg .x13 = framePtr :=
    PartialState.CompatibleWith_singletonReg.mp (by rw [← h13h]; exact hc13)
  -- snapshot-valued pin atoms
  have h15h' : (.x15 ↦ᵣ (snapRf s).get .x15) h15 := by
    show h15 = PartialState.singletonReg .x15 ((snapRf s).get .x15)
    rw [snapRf_get s (by decide), hv15]
    exact h15h
  have h16h' : (.x16 ↦ᵣ (snapRf s).get .x16) h16 := by
    show h16 = PartialState.singletonReg .x16 ((snapRf s).get .x16)
    rw [snapRf_get s (by decide), hv16]
    exact h16h
  have h12h' : (.x12 ↦ᵣ (snapRf s).get .x12) h12 := by
    show h12 = PartialState.singletonReg .x12 ((snapRf s).get .x12)
    rw [snapRf_get s (by decide), hv12]
    exact h12h
  have h13h' : (.x13 ↦ᵣ (snapRf s).get .x13) h13 := by
    show h13 = PartialState.singletonReg .x13 ((snapRf s).get .x13)
    rw [snapRf_get s (by decide), hv13]
    exact h13h
  -- spell the pin heaps through the chain snapshot for elimination
  have hR3' : hR3 = h13.union (hIsHeap.union hFB) := by rw [← hu7, huIs]
  rw [hR3'] at hd6
  have hR2' : hR2 = h12.union (h13.union (hIsHeap.union hFB)) := by rw [← hu6, hR3']
  rw [hR2'] at hd5
  have hR1' : hR1 = h16.union (h12.union (h13.union (hIsHeap.union hFB))) := by
    rw [← hu5, hR2']
  rw [hR1'] at hd4
  have hd7' : h13.Disjoint (hIsHeap.union hFB) := by rw [← huIs] at hd7; exact hd7
  -- pin-to-subheap disjointness for the snapshot witness
  have d13Is : h13.Disjoint hIsHeap := disjoint_left_of_disjoint_union hd7'
  have d12L : h12.Disjoint h13 := disjoint_left_of_disjoint_union hd6
  have d12Is : h12.Disjoint hIsHeap :=
    disjoint_left_of_disjoint_union (disjoint_right_of_disjoint_union hd6)
  have d12Sub : h12.Disjoint (h13.union hIsHeap) :=
    disjoint_union_left_local d12L d12Is
  have d16L : h16.Disjoint h12 := disjoint_left_of_disjoint_union hd5
  have d1613 : h16.Disjoint h13 :=
    disjoint_left_of_disjoint_union (disjoint_right_of_disjoint_union hd5)
  have d16Is : h16.Disjoint hIsHeap :=
    disjoint_left_of_disjoint_union (disjoint_right_of_disjoint_union
      (disjoint_right_of_disjoint_union hd5))
  have d16Sub : h16.Disjoint (h13.union hIsHeap) :=
    disjoint_union_left_local d1613 d16Is
  have d16Sub2 : h16.Disjoint (h12.union (h13.union hIsHeap)) :=
    disjoint_union_left_local d16L d16Sub
  have d15L : h15.Disjoint h16 := disjoint_left_of_disjoint_union hd4
  have d1512 : h15.Disjoint h12 :=
    disjoint_left_of_disjoint_union (disjoint_right_of_disjoint_union hd4)
  have d1513 : h15.Disjoint h13 :=
    disjoint_left_of_disjoint_union (disjoint_right_of_disjoint_union
      (disjoint_right_of_disjoint_union hd4))
  have d15Is : h15.Disjoint hIsHeap :=
    disjoint_left_of_disjoint_union (disjoint_right_of_disjoint_union
      (disjoint_right_of_disjoint_union (disjoint_right_of_disjoint_union hd4)))
  have d15Sub : h15.Disjoint (h16.union (h12.union (h13.union hIsHeap))) :=
    disjoint_union_left_local d15L
      (disjoint_union_left_local d1512 (disjoint_union_left_local d1513 d15Is))
  -- frame disjointness climbs
  have hd13FB : h13.Disjoint hFB := disjoint_right_of_disjoint_union hd7'
  have hd12FB : h12.Disjoint hFB :=
    disjoint_right_of_disjoint_union (disjoint_right_of_disjoint_union hd6)
  have hd16FB : h16.Disjoint hFB :=
    disjoint_right_of_disjoint_union (disjoint_right_of_disjoint_union
      (disjoint_right_of_disjoint_union hd5))
  have hd15FB : h15.Disjoint hFB :=
    disjoint_right_of_disjoint_union (disjoint_right_of_disjoint_union
      (disjoint_right_of_disjoint_union (disjoint_right_of_disjoint_union hd4)))
  have hdF : (h15.union (h16.union (h12.union (h13.union hIsHeap)))).Disjoint hFB :=
    disjoint_union_right_local hd15FB (disjoint_union_right_local hd16FB
      (disjoint_union_right_local hd12FB (disjoint_union_right_local hd13FB hdIs)))
  have huF : (h15.union (h16.union (h12.union (h13.union hIsHeap)))).union hFB = hPINS := by
    rw [pUnion_assoc, pUnion_assoc, pUnion_assoc, pUnion_assoc, huIs, hu7, hu6, hu5, hu4]
  -- the register-file snapshot holds at the pins-and-chain heap
  have hwit : (((.x15 ↦ᵣ (snapRf s).get .x15) **
      ((.x16 ↦ᵣ (snapRf s).get .x16) **
      ((.x12 ↦ᵣ (snapRf s).get .x12) **
      ((.x13 ↦ᵣ (snapRf s).get .x13) **
      (regIs Reg.x5 ((snapRf s).get Reg.x5) **
      (regIs Reg.x6 ((snapRf s).get Reg.x6) **
      (regIs Reg.x7 ((snapRf s).get Reg.x7) **
      (regIs Reg.x28 ((snapRf s).get Reg.x28) **
      (regIs Reg.x29 ((snapRf s).get Reg.x29) **
      (regIs Reg.x30 ((snapRf s).get Reg.x30) **
      (regIs Reg.x31 ((snapRf s).get Reg.x31) **
      (regIs Reg.x10 ((snapRf s).get Reg.x10) **
      (regIs Reg.x11 ((snapRf s).get Reg.x11) **
      (regIs Reg.x14 ((snapRf s).get Reg.x14) **
      (regIs Reg.x17 ((snapRf s).get Reg.x17) ** empAssertion))))))))))))))))
      (h15.union (h16.union (h12.union (h13.union hIsHeap)))) :=
    ⟨h15, _, d15Sub, rfl, h15h',
      ⟨h16, _, d16Sub2, rfl, h16h',
        ⟨h12, _, d12Sub, rfl, h12h',
          ⟨h13, hIsHeap, d13Is, rfl, h13h', hIsSpelled⟩⟩⟩⟩
  have hREG : regFileIs (snapRf s)
      (h15.union (h16.union (h12.union (h13.union hIsHeap)))) := by
    -- strip hwit's trailing `empAssertion` so both sides of the
    -- permutation are bare fifteen-atom chains
    rw [sepConj_emp_right'] at hwit
    rw [regFileIs_eq_atoms]
    xperm_hyp hwit
  -- the asrtOf length side condition
  have hFrameEq : FrameBytes = 40 * rlpRecursiveDecodeDepthCap + 40 := by
    rw [production_frame_shape.2.1]
    decide
  have LEN : frameBytes.length = (itemsRw rlpRecursiveDecodeDepthCap framePtr).len := by
    rw [hfb, hFrameEq]
    rfl
  -- the goal, rebuilt at the same heap
  have inner5 : (regFileIs (snapRf s) ** bytesRegion framePtr frameBytes) hPINS :=
    ⟨h15.union (h16.union (h12.union (h13.union hIsHeap))), hFB, hdF, huF, hREG, hFBh⟩
  have inner4 : ((regFileIs (snapRf s) ** bytesRegion framePtr frameBytes) **
    empAssertion) hPINS :=
    ⟨hPINS, PartialState.empty, PartialState.Disjoint_empty_right,
      PartialState.union_empty_right, inner5, rfl⟩
  have inner3 : asrtOf (itemsRw rlpRecursiveDecodeDepthCap framePtr)
      (Reach.exact (snapRf s) frameBytes empAssertion) hPINS :=
    ⟨snapRf s, frameBytes, empAssertion, LEN, pcFree_emp, ⟨rfl, rfl, rfl⟩, inner4⟩
  have inner2 : asrtM ⟨listBase, inputBytes⟩ (itemsRw rlpRecursiveDecodeDepthCap framePtr)
      (Reach.exact (snapRf s) frameBytes empAssertion) hPRE := by
    change (asrtOf (itemsRw rlpRecursiveDecodeDepthCap framePtr)
      (Reach.exact (snapRf s) frameBytes empAssertion) **
      bytesRegion listBase inputBytes) hPRE
    exact ⟨hPINS, hIB, hd3, hu3, inner3, hIBh⟩
  refine ⟨empAssertion, pcFree_emp, ⟨0, inputBytes.length, ?_, ?_, ?_, ?_, by omega,
    by omega⟩, ?_⟩
  · rw [snapRf_get s (by decide), hv15]
    simp
  · rw [snapRf_get s (by decide), hv16, hlistEnd]
  · rw [snapRf_get s (by decide), hv12]
    decide
  · rw [snapRf_get s (by decide), hv13]
  have hcom : h.CompatibleWith s := by rw [← hu1]; exact hcompat
  exact ⟨h, hcom, ⟨hXPRE, hR, hd1, hu1,
    ⟨hX, hPRE, hd2, hu2, hXh, inner2⟩, hRh⟩⟩

/-! ## The linked tie -/

/-- **The #12749 linked-image tie** (callee side).  The emitted direct-`JAL`
    image of `rlp_recursive_decode_items` — the exact code linked into the
    guest at `GuestAddrs.rlp_recursive_decode_items`, tied to the synthetic
    `decCr` of `itemsSound_all` by `recursiveDecodeDirectCode_eq_decCr` and
    the byte-identical program equalities in `RlpRecursiveDecodeDirect` —
    satisfies the production adapter's callee contract at an entry-rooted
    call.  Caller-agnostic: no premise mentions `rlp_walk_next_shared` or any
    descent-site shape.  Status and the final frame bytes are outputs
    (existentially quantified in the postcondition); the depth cap is carried
    as the `rlpRecursiveDecodeDepthCap` parameter, never duplicated. -/
theorem rlp_recursive_decode_items_linked_spec_within
    (listBase listEnd framePtr : Word) (inputBytes frameBytes : List (BitVec 8))
    (hL : RdLayout listBase inputBytes framePtr FrameBytes)
    (hfb : frameBytes.length = FrameBytes)
    (hlistEnd : listEnd = listBase + BitVec.ofNat 64 inputBytes.length) :
    cpsTripleWithin (itemsSteps inputBytes.length rlpRecursiveDecodeDepthCap)
      Items RetPC recursiveDecodeDirectCode
      ((.x1 ↦ᵣ RetPC) ** productionItemsPre listBase listEnd framePtr
        inputBytes frameBytes)
      ((.x1 ↦ᵣ RetPC) ** fun h => ∃ status frameBytes' F,
        (productionItemsPost listBase framePtr status inputBytes frameBytes' ** F) h) := by
  intro R hR s hcr hPR hpc
  obtain ⟨A₀, hApc, hpreS, hPR'⟩ :=
    productionItemsPre_fold listBase listEnd framePtr inputBytes frameBytes hfb hlistEnd
      s R hPR
  rw [recursiveDecodeDirectCode_eq_decCr] at hcr
  have hFrameEq : FrameBytes = 40 * rlpRecursiveDecodeDepthCap + 40 := by
    rw [production_frame_shape.2.1]
    decide
  rw [hFrameEq] at hL hfb
  obtain ⟨k, hk, s', hstep, hpc', hpost⟩ :=
    itemsSound_all inputBytes listBase rlpRecursiveDecodeDepthCap framePtr hL
      (snapRf s) frameBytes A₀ hfb hApc hpreS RetPC (by decide) R hR s hcr hPR' hpc
  refine ⟨k, hk, s', hstep, hpc', ?_⟩
  obtain ⟨hTop, hcompat', hToph⟩ := hpost
  obtain ⟨hXa, hR', hd, hu, hXah, hRh'⟩ := hToph
  obtain ⟨hx1, hM, hd', hu', hx1h, hMh⟩ := hXah
  obtain ⟨status, fb', F', hlen', hFpc, hprod⟩ :=
    items_asrtM_post_to_production_post inputBytes listBase framePtr
      (snapRf s) frameBytes A₀ hM hMh
  exact ⟨hTop, hcompat', ⟨hXa, hR', hd, hu,
    ⟨hx1, hM, hd', hu', hx1h, ⟨status, fb', F', hprod⟩⟩, hRh'⟩⟩

/-- **The #12749 linked-image tie** (call site).  The adapter's post-parametric
    call rule instantiated with the linked callee: one `JAL` from
    `rlp_validate_payload`'s call site to the linked direct-JAL image, with
    the existentially-quantified post.  The framing hypotheses (`hdisj`,
    `hcallerDisj`, `hcode`) are the caller's to discharge against its own
    `cr`.  This is the consumption point `:890` was designed for; the
    fixed-status `:784` variant is **not** honestly dischargeable with this
    callee (its post pins the status and reuses the input frame bytes; the
    model leaves both free) — see the #12749 discussion. -/
theorem rlp_validate_payload_items_call_post_linked
    {cr : CodeReq}
    (listBase listEnd framePtr oldRa : Word)
    (inputBytes frameBytes : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hL : RdLayout listBase inputBytes framePtr FrameBytes)
    (hfb : frameBytes.length = FrameBytes)
    (hlistEnd : listEnd = listBase + BitVec.ofNat 64 inputBytes.length)
    (hdisj : (CodeReq.singleton CallPC (.JAL .x1 itemsJalOff)).Disjoint
      recursiveDecodeDirectCode)
    (hcallerDisj : wrapperCode.Disjoint recursiveDecodeDirectCode)
    (hcode : ∀ a i, (wrapperCode.union recursiveDecodeDirectCode) a = some i →
      cr a = some i) :
    cpsTripleWithin (1 + itemsSteps inputBytes.length rlpRecursiveDecodeDepthCap)
      CallPC RetPC cr
      (((.x1 ↦ᵣ oldRa) ** productionItemsPre listBase listEnd framePtr
        inputBytes frameBytes) ** F)
      (((.x1 ↦ᵣ RetPC) ** (fun h => ∃ status frameBytes' F',
        (productionItemsPost listBase framePtr status inputBytes frameBytes' ** F') h)) ** F) :=
  rlp_validate_payload_items_call_post_spec_within listBase listEnd framePtr oldRa
    inputBytes frameBytes _ F hF hdisj hcallerDisj hcode
    (rlp_recursive_decode_items_linked_spec_within listBase listEnd framePtr inputBytes
      frameBytes hL hfb hlistEnd)

/-! ## Anti-vacuity witnesses

    The geometry antecedents are satisfiable on a real (nonempty) call path,
    and they hold for a family of distinct input windows, so the tie is not
    about one frozen input.  The production precondition's own inhabitance
    is carried by the adapter's `production_items_pre_inhabited_for_frame` /
    `production_items_pre_degenerate_inhabited`; `x1` is call machinery,
    not an exposed register, so it cannot double-own against the fifteen
    owned registers. -/

/-- Byte-granular memory validity for the frame arena, proved at a variable
    base so the zone constants reduce (with a concrete base, `simp` partially
    evaluates the `decide` zone tests and swallows the zone lemmas). -/
private theorem isValidMemAddr_frameOffset {frame : Word} (hbase : frame.toNat = GuestAddrs.rlp_recursive_decode_frame)
    (k : Nat) (hk : k < 41000) : isValidMemAddr (frame + BitVec.ofNat 64 k) = true := by
  have hpin : GuestAddrs.rlp_recursive_decode_frame = 0xbf5e2000 := by rfl
  have hlt : frame.toNat + k < 2 ^ 64 := by rw [hbase, hpin]; omega
  have hto : (frame + BitVec.ofNat 64 k).toNat = GuestAddrs.rlp_recursive_decode_frame + k := by
    rw [toNat_add_ofNat_of_le hlt, hbase]
  simp only [isValidMemAddr, hto, hpin, EvmAsm.Rv64.MEM_START, EvmAsm.Rv64.MEM_END,
    EvmAsm.Rv64.INPUT_MEM_START, EvmAsm.Rv64.INPUT_MEM_END,
    EvmAsm.Rv64.RAM_MEM_START, EvmAsm.Rv64.RAM_MEM_END,
    decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true]
  omega

/-- The frame arena's `RwRegion.wf` factored out for reuse by both witness
    theorems below. -/
private theorem frameArena_wf : (RwRegion.mk Frame FrameBytes).wf := by
  refine ⟨by decide, ?_, ?_⟩
  · have hb : Frame.toNat = GuestAddrs.rlp_recursive_decode_frame := by decide
    have hpin : GuestAddrs.rlp_recursive_decode_frame = 0xbf5e2000 := by rfl
    rw [production_frame_shape.2.1]
    show Frame.toNat + 41000 < 2 ^ 64
    rw [hb, hpin]
    omega
  · intro k hk
    have hk' : k < 41000 := by
      simpa [FrameBytes, rlpRecursiveDecodeFrameBytes, rlpRecursiveDecodeDepthCap] using hk
    exact isValidMemAddr_frameOffset (by decide) k hk'

theorem items_linked_preconditions_reachable :
    ∃ frameBytes : List (BitVec 8),
      RdLayout 0x8000 [0xC2, 0xC1, 0x80] Frame FrameBytes ∧
      frameBytes.length = FrameBytes ∧
      ((0x8000 + 3 : Word) = 0x8000 + BitVec.ofNat 64 3) :=
  ⟨List.replicate FrameBytes 0, ⟨by decide, frameArena_wf, Or.inl (by decide)⟩,
    by simp, by decide⟩

/-- The tie applies to a *family* of inputs, not one frozen window: two
    input geometries — a depth-2 nested list (`0xC2 0xC1 0x80`) and a
    depth-1 nested list (`0xC1 0x80`), different lengths and different
    decode first-bytes — both satisfy the tie's geometry antecedents.
    A value-level status control (status 0 on the well-formed window,
    nonzero on a truncated one, as measured by `#eval`) is NOT
    kernel-provable here: the reference decoder is a well-founded mutual
    recursion whose `WellFounded.fix` application does not whnf under
    `rfl`/`decide`/`simp` on concrete inputs, and `RefDecode`'s own
    concrete facts are `#guard`-compiled evaluations. -/
theorem items_linked_geometry_discriminating :
    RdLayout 0x8000 [0xC2, 0xC1, 0x80] Frame FrameBytes ∧
    RdLayout 0x8000 [0xC1, 0x80] Frame FrameBytes ∧
    [0xC2, 0xC1, 0x80].length ≠ [0xC1, 0x80].length :=
  ⟨⟨by decide, frameArena_wf, Or.inl (by decide)⟩,
    ⟨by decide, frameArena_wf, Or.inl (by decide)⟩, by decide⟩

#print axioms rlp_recursive_decode_items_linked_spec_within
#print axioms rlp_validate_payload_items_call_post_linked
#print axioms items_linked_preconditions_reachable
#print axioms items_linked_geometry_discriminating

end EvmAsm.Codegen.RlpValidatePayloadProductionAdapter
