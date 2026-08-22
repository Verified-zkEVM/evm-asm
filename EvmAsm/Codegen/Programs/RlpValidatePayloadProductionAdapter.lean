/-
  EvmAsm.Codegen.Programs.RlpValidatePayloadProductionAdapter

  The production call boundary for `rlp_validate_payload`.

  `RlpWalk` emits the 21-instruction wrapper at the linked entry.  Its
  recursive callee is emitted from the RecDecode model after replacing the
  model's two-instruction `li`/`jalr` call pairs with direct `jal`/`nop`
  pairs.  The existing `ItemsSound` theorem is therefore deliberately not
  reused as if it were a production image theorem: it is proved over the
  synthetic `decCr` and the model's indirect-call programs.

  This file does the sound part that is available now.  It composes the real
  wrapper `jal` at `V + 40` with an explicit production-callee CPS premise,
  carries the 1024-level / 41000-byte frame and status postcondition, and
  proves the wrapper call instruction is the linked Program instruction.  A
  future direct-JAL RecDecode correspondence theorem can consume this
  adapter without changing its caller-facing shape.
-/

import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.RegionMap
import EvmAsm.Rv64.MemSat
import EvmAsm.Rv64.RLP.RecDecode.Correct
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.DualReadByteScan

namespace EvmAsm.Codegen.RlpValidatePayloadProductionAdapter

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.RecDecode

abbrev V : Word := (GuestAddrs.rlp_validate_payload : Word)
abbrev CallPC : Word := V + 40
abbrev RetPC : Word := V + 44
abbrev Items : Word := (GuestAddrs.rlp_recursive_decode_items : Word)
abbrev itemsJalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_recursive_decode_items
    (GuestAddrs.rlp_validate_payload + 40)
abbrev Frame : Word := (GuestAddrs.rlp_recursive_decode_frame : Word)
abbrev Cap : Word := (rlpRecursiveDecodeDepthCap : Word)
abbrev FrameBytes : Nat := rlpRecursiveDecodeFrameBytes rlpRecursiveDecodeDepthCap

abbrev wrapperCode : CodeReq := CodeReq.ofProg V rlpValidatePayload_prog

theorem production_frame_shape :
    Cap = (1024 : Word) ∧ FrameBytes = 41000 ∧
      Frame = (RegionMap.rlpRecursiveFrameRegion).base ∧
      FrameBytes = (RegionMap.rlpRecursiveFrameRegion).size := by
  decide

/- The pre owns the complete register footprint exposed by the callee post.
   The wrapper-pinned inputs remain `regIs`; the registers that the recursive
   decoder may overwrite are transferred as `regOwn`, including `x10`.  A
   caller must replace its existing ownership with this pre, not frame this
   pre beside that ownership, or the separating conjunction would double-own
   the register. -/
def productionItemsPre
    (listBase listEnd framePtr : Word)
    (inputBytes frameBytes : List (BitVec 8)) : Assertion :=
  ((.x15 ↦ᵣ listBase) ** (.x16 ↦ᵣ listEnd) ** (.x12 ↦ᵣ Cap) **
    (.x13 ↦ᵣ framePtr) **
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 **
      regOwn .x11 ** regOwn .x14 ** regOwn .x17 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion framePtr frameBytes)) **
    bytesRegion listBase inputBytes

def productionItemsPost
    (listBase framePtr status : Word)
    (inputBytes frameBytes : List (BitVec 8)) : Assertion :=
  ((.x10 ↦ᵣ status) ** (.x13 ↦ᵣ framePtr) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
    regOwn .x12 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x17 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** bytesRegion framePtr frameBytes) **
    bytesRegion listBase inputBytes

theorem productionItemsPre_pcFree
    (listBase listEnd framePtr : Word)
    (inputBytes frameBytes : List (BitVec 8)) :
    (productionItemsPre listBase listEnd framePtr inputBytes frameBytes).pcFree := by
  unfold productionItemsPre
  repeat' apply pcFree_sepConj
  all_goals first
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact bytesRegion_pcFree _ _

theorem productionItemsPost_pcFree
    (listBase framePtr status : Word)
    (inputBytes frameBytes : List (BitVec 8)) :
    (productionItemsPost listBase framePtr status inputBytes frameBytes).pcFree := by
  unfold productionItemsPost
  repeat' apply pcFree_sepConj
  all_goals first
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact bytesRegion_pcFree _ _

/-! ## Concrete model-side inhabitance check

This witness is intentionally about the existing RecDecode calling family,
not a claim that its synthetic `decCr` is the linked direct-JAL image.  It
keeps the distinction visible while checking that the 1024-frame shape is not
being made vacuous by the register/window contract itself.
-/

def exampleItemsRf : RegFile :=
  RegFile.set
    (RegFile.set
      (RegFile.set
        (RegFile.set (fun _ : Reg => (0 : Word)) .x15 0x8000)
          .x16 0x8000)
        .x12 2)
      .x13 0x10000

theorem exampleItemsPre_inhabited :
    itemsPreS [0xC2, 0xC1, 0x80] 0x8000 2 0x10000 exampleItemsRf
      (List.replicate (40 * 2 + 40) 0) empAssertion := by
  unfold itemsPreS
  refine ⟨0, 0, ?_, ?_, ?_, ?_, by omega⟩
  · simp [exampleItemsRf, RegFile.get, RegFile.set]
  · simp [exampleItemsRf, RegFile.get, RegFile.set]
  · simp [exampleItemsRf, RegFile.get, RegFile.set]
  · simp [exampleItemsRf, RegFile.get, RegFile.set]

theorem exampleItemsLayout :
    RdLayout 0x8000 [0xC2, 0xC1, 0x80] 0x10000 (40 * 2 + 40) := by
  refine ⟨by decide, by decide, ?_⟩
  exact Or.inl (by decide)

/-! ## Region-level inhabitance of the production callee precondition

The wrapper's own 21 instructions touch only its 32-byte stack frame.  The
recursive callee, however, writes the depth-indexed frame arena, so the
caller-facing callee premise owns all `40 * Cap + 40` bytes.  This witness
uses `satWithin_bytesRegion`; it does not enumerate the 5125 dwords. -/

private def exampleProductionRegAtoms : List (Reg × Word) :=
  [(.x15, 0x8000), (.x16, 0x8000), (.x12, Cap), (.x13, Frame),
   (.x5, 0), (.x6, 0), (.x7, 0), (.x10, 0), (.x11, 0), (.x14, 0),
   (.x17, 0), (.x28, 0), (.x29, 0), (.x30, 0), (.x31, 0)]

private def exampleProductionRegAtom (p : Reg × Word) : Assertion :=
  if p.1 == .x15 || p.1 == .x16 || p.1 == .x12 || p.1 == .x13 then
    p.1 ↦ᵣ p.2
  else
    regOwn p.1

private def exampleProductionRegHeapAtom (p : Reg × Word) : PartialState :=
  PartialState.singletonReg p.1 p.2

private def exampleProductionRegAssertion : Assertion :=
  exampleProductionRegAtoms.foldr
    (fun p acc => exampleProductionRegAtom p ** acc) empAssertion

private def exampleProductionRegHeap : PartialState :=
  exampleProductionRegAtoms.foldr
    (fun p acc => (exampleProductionRegHeapAtom p).union acc) PartialState.empty

private theorem singletonReg_disjoint_singletonReg_prod
    {r1 r2 : Reg} {v1 v2 : Word} (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint
      (PartialState.singletonReg r2 v2) := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r
  by_cases hr : r = r1
  · subst r
    exact Or.inr (by simp [PartialState.singletonReg, hne])
  · exact Or.inl (by simp [PartialState.singletonReg, hr])

private theorem exampleProductionReg_sat :
    exampleProductionRegAssertion exampleProductionRegHeap := by
  apply sepConj_foldr_satisfiable exampleProductionRegAtom
    exampleProductionRegHeapAtom exampleProductionRegAtoms
  · intro p hp
    by_cases h_fixed :
        p.1 == .x15 || p.1 == .x16 || p.1 == .x12 || p.1 == .x13
    · rw [show exampleProductionRegAtom p = (p.1 ↦ᵣ p.2) by
          simp [exampleProductionRegAtom, h_fixed]]
      rfl
    · rw [show exampleProductionRegAtom p = regOwn p.1 by
          simp [exampleProductionRegAtom, h_fixed]]
      exact ⟨p.2, rfl⟩
  · exact List.Pairwise.imp
      (fun {p q} hpq => by
        exact singletonReg_disjoint_singletonReg_prod hpq)
      (by decide)

private theorem exampleProductionRegHeap_disjoint_memOnly
    {h : PartialState} {lo hi : Nat}
    (hw : h.MemOnlyWithin lo hi) :
    exampleProductionRegHeap.Disjoint h := by
  refine ⟨fun r => Or.inr (hw.regs r), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    exact Or.inl (by simp [exampleProductionRegAtoms, exampleProductionRegHeap,
      exampleProductionRegHeapAtom, PartialState.singletonReg,
      PartialState.union, PartialState.empty])
  · intro a
    exact Or.inl (by simp [exampleProductionRegAtoms, exampleProductionRegHeap,
      exampleProductionRegHeapAtom, PartialState.singletonReg,
      PartialState.union, PartialState.empty])
  · exact Or.inl (by simp [exampleProductionRegAtoms, exampleProductionRegHeap,
      exampleProductionRegHeapAtom, PartialState.singletonReg,
      PartialState.union, PartialState.empty])
  · exact Or.inl (by simp [exampleProductionRegAtoms, exampleProductionRegHeap,
      exampleProductionRegHeapAtom, PartialState.singletonReg,
      PartialState.union, PartialState.empty])
  · exact Or.inl (by simp [exampleProductionRegAtoms, exampleProductionRegHeap,
      exampleProductionRegHeapAtom, PartialState.singletonReg,
      PartialState.union, PartialState.empty])
  · exact Or.inl (by simp [exampleProductionRegAtoms, exampleProductionRegHeap,
      exampleProductionRegHeapAtom, PartialState.singletonReg,
      PartialState.union, PartialState.empty])

private theorem production_frame_valid_of_length
    {frameBytes : List (BitVec 8)} (hframeLen : frameBytes.length = FrameBytes) :
    ∀ k, k < (frameBytes.length + 7) / 8 →
      isValidDwordAccess (Frame + BitVec.ofNat 64 (8 * k)) = true := by
  intro k hk
  rw [hframeLen] at hk
  have hk' : k < 5125 := by
    -- v4.33 needs the depth cap unfolded too: without it `simp` stops at
    -- `(40 * rlpRecursiveDecodeDepthCap + 40 + 7) / 8` and `simpa`, closing at
    -- reducible transparency, will not finish the numeral.
    simpa [FrameBytes, rlpRecursiveDecodeFrameBytes, rlpRecursiveDecodeDepthCap] using hk
  have hbase : Frame.toNat = 0xbf5e2000 := by decide
  have hlt : Frame.toNat + 8 * k < 2 ^ 64 := by
    rw [hbase]
    omega
  apply isValidDwordAccess_of_toNat
  · rw [toNat_add_ofNat_of_le hlt, hbase]
    omega
  · rw [toNat_add_ofNat_of_le hlt, hbase]
    right
    right
    omega

set_option maxRecDepth 8000 in
theorem production_items_pre_inhabited_for_frame
    (frameBytes : List (BitVec 8)) (hframeLen : frameBytes.length = FrameBytes) :
    ∃ h, productionItemsPre 0x8000 0x8000 Frame [] frameBytes h := by
  have hframe := satWithin_bytesRegion Frame frameBytes
    (production_frame_valid_of_length hframeLen)
  obtain ⟨hmem, hmem_sat, hmem_bounds⟩ := hframe
  have hdisj := exampleProductionRegHeap_disjoint_memOnly hmem_bounds
  have hcomb :
      (exampleProductionRegAssertion **
        bytesRegion Frame frameBytes)
        (exampleProductionRegHeap.union hmem) :=
    ⟨exampleProductionRegHeap, hmem, hdisj, rfl,
      exampleProductionReg_sat, hmem_sat⟩
  refine ⟨exampleProductionRegHeap.union hmem, ?_⟩
  -- `exampleProductionRegAtom` (singular) must be unfolded explicitly: v4.33's
  -- `simpa` closes at reducible transparency and cannot see through the `def`.
  simpa [productionItemsPre, exampleProductionRegAssertion,
    exampleProductionRegAtoms, exampleProductionRegAtom,
    bytesRegion_nil, sepConj_assoc', sepConj_emp_left', sepConj_emp_right']
    using hcomb

private theorem production_frame_bytes_length :
    ∃ frameBytes : List (BitVec 8), frameBytes.length = FrameBytes := by
  refine ⟨List.replicate FrameBytes 0, ?_⟩
  simp only [List.length_replicate]

noncomputable def exampleProductionFrameBytes : List (BitVec 8) :=
  Classical.choose production_frame_bytes_length

theorem exampleProductionFrameBytes_length :
    exampleProductionFrameBytes.length = FrameBytes :=
  Classical.choose_spec production_frame_bytes_length

theorem production_items_pre_inhabited :
    ∃ h, productionItemsPre 0x8000 0x8000 Frame []
      exampleProductionFrameBytes h := by
  exact production_items_pre_inhabited_for_frame _
    exampleProductionFrameBytes_length

/-! The raw production precondition is also inhabited by a deliberately
degenerate zero-length witness: empty `bytesRegion`s reduce to `empAssertion`.
This is only isolation satisfiability, not evidence that the recursive callee's
41000-byte frame contract is discharged.  The latter is the preceding
`production_items_pre_inhabited_for_frame` result, whose length hypothesis is
what forces the real arena shape. -/

theorem production_items_pre_degenerate_inhabited :
    ∃ h, productionItemsPre 0x8000 0x8000 Frame [] [] h := by
  refine ⟨exampleProductionRegHeap, ?_⟩
  simpa [productionItemsPre, exampleProductionRegAssertion,
    exampleProductionRegAtoms, exampleProductionRegAtom, bytesRegion_nil,
    sepConj_assoc', sepConj_emp_left', sepConj_emp_right'] using
      exampleProductionReg_sat

theorem production_items_pre_all_zero_inhabited :
    ∃ h, productionItemsPre 0x8000 0x8000 Frame []
      (List.replicate FrameBytes 0) h := by
  exact production_items_pre_inhabited_for_frame _ (by simp)

/-! The first three linked wrapper instructions establish the production
    stack frame.  This is intentionally separate from the later `AUIPC`/`ADDI`
    and branch setup: the saved `x13` value is an observable success output,
    while the recursive callee receives the fixed `Frame` pointer. -/

theorem rlp_validate_payload_production_frame_setup_spec_within
    (sp old13 raVal : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 3 V (V + 12) wrapperCode
      (((.x2 ↦ᵣ (sp + 32)) ** (.x1 ↦ᵣ raVal) ** (.x13 ↦ᵣ old13) **
        (memOwn sp) ** (memOwn (sp + 8))) ** F)
      (((.x2 ↦ᵣ sp) ** (.x1 ↦ᵣ raVal) ** (.x13 ↦ᵣ old13) **
        (memIs sp raVal) ** (memIs (sp + 8) old13)) ** F) := by
  apply cpsTripleWithin_frameR F hF
  have h0 := addi_spec_gen_same_within .x2 (sp + 32)
    (-32 : BitVec 12) V (by decide)
  rw [show (sp + 32) + signExtend12 (-32 : BitVec 12) = sp from by
        rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide]
        bv_omega] at h0
  have h1 := sd_spec_gen_own_within .x2 .x1 sp raVal
    (0 : BitVec 12) (V + 4)
  have h2 := sd_spec_gen_own_within .x2 .x13 sp old13
    (8 : BitVec 12) (V + 8)
  runBlock h0 h1 h2

/-! ## The production wrapper call -/

theorem production_items_call_jal_mem :
    ∀ a i, CodeReq.singleton CallPC
      (.JAL .x1 itemsJalOff) a = some i → wrapperCode a = some i := by
  exact CodeReq.ofProg_mem_at V CallPC rlpValidatePayload_prog 10 _
    (by bv_omega) (by decide) rfl (by decide)

set_option maxRecDepth 8000 in
theorem rlp_validate_payload_items_call_spec_within
    {cr calleeCode : CodeReq} {n : Nat}
    (listBase listEnd framePtr status oldRa : Word)
    (inputBytes frameBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hdisj : (CodeReq.singleton CallPC
      (.JAL .x1 itemsJalOff)).Disjoint calleeCode)
    (hcallerDisj : wrapperCode.Disjoint calleeCode)
    (hcode : ∀ a i, (wrapperCode.union calleeCode) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n Items RetPC calleeCode
      (((.x1 ↦ᵣ RetPC) **
        productionItemsPre listBase listEnd framePtr inputBytes frameBytes))
      (((.x1 ↦ᵣ RetPC) **
        productionItemsPost listBase framePtr status inputBytes frameBytes))) :
    cpsTripleWithin (1 + n) CallPC RetPC cr
      (((.x1 ↦ᵣ oldRa) **
        productionItemsPre listBase listEnd framePtr inputBytes frameBytes) ** F)
      (((.x1 ↦ᵣ RetPC) **
        productionItemsPost listBase framePtr status inputBytes frameBytes) ** F) := by
  have htarget : CallPC + signExtend21 itemsJalOff = Items := by
    change (BitVec.ofNat 64 GuestAddrs.rlp_validate_payload + 40) +
      signExtend21 (jalOff GuestAddrs.rlp_recursive_decode_items
        (GuestAddrs.rlp_validate_payload + 40)) =
      BitVec.ofNat 64 GuestAddrs.rlp_recursive_decode_items
    exact jalOff_correct_add GuestAddrs.rlp_recursive_decode_items
      GuestAddrs.rlp_validate_payload 40 (by decide) (by decide) (by decide)
      (by decide)
  have hret : (CallPC + 4) &&& ~~~(1 : Word) = RetPC := by decide
  have hpre := productionItemsPre_pcFree listBase listEnd framePtr inputBytes frameBytes
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := CallPC) (calleeEntry := Items) (vOld := oldRa)
    (calleeCode := calleeCode)
    (Prest := productionItemsPre listBase listEnd framePtr inputBytes frameBytes)
    (Q := (.x1 ↦ᵣ RetPC) **
      productionItemsPost listBase framePtr status inputBytes frameBytes)
    itemsJalOff htarget hret hpre hdisj hcallee
  have hcallCode : ∀ a i,
      ((CodeReq.singleton CallPC (.JAL .x1 itemsJalOff)).union calleeCode) a =
        some i → (wrapperCode.union calleeCode) a = some i := by
    exact CodeReq.union_split_mono
      (fun a i h => CodeReq.union_mono_left a i
        (production_items_call_jal_mem a i h))
      (fun a i h => by
        rcases hcallerDisj a with hnone | hnone
        · simp [CodeReq.union, hnone, h]
        · rw [h] at hnone
          cases hnone)
  have hcall' := cpsTripleWithin_extend_code hcallCode hcall
  have hcall'' := cpsTripleWithin_extend_code hcode hcall'
  exact cpsTripleWithin_frameR F hF hcall''

/-! ## Linked status tails

The call theorem above deliberately stops at the linked `JAL` return point:
the recursive callee's production post is explicit, rather than being
silently identified with the retired strict-fuel post.  These two lemmas
verify the remaining status tails of the same 21-instruction wrapper.  They
are therefore the production-side continuation boundary that a future
direct-JAL RecDecode theorem can consume.

In particular, the success arm restores `x13` from the wrapper frame, while
the failure arm jumps over that restore and returns with `x13 = framePtr`.
That distinction is observable in the linked code and is intentionally not
collapsed into the old `ValidateResultPost`.
-/

theorem rlp_validate_payload_production_success_tail_spec_within
    (sp old13 raVal : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (V + 68) (raVal &&& ~~~(1 : Word)) wrapperCode
      (((.x2 ↦ᵣ sp) ** (.x1 ↦ᵣ (V + 44)) **
        (.x13 ↦ᵣ Frame) ** (.x0 ↦ᵣ (0 : Word)) **
        (memIs sp raVal) ** (memIs (sp + 8) old13)) ** F)
      (((.x2 ↦ᵣ (sp + 32)) ** (.x1 ↦ᵣ raVal) **
        (.x13 ↦ᵣ old13) ** (.x0 ↦ᵣ (0 : Word)) **
        (memIs sp raVal) ** (memIs (sp + 8) old13)) ** F) := by
  apply cpsTripleWithin_frameR F hF
  have h16 := ld_spec_gen_within .x13 .x2 sp Frame old13
    (8 : BitVec 12) (V + 68) (by decide)
  have h17 := ld_spec_gen_within .x1 .x2 sp (V + 44) raVal
    (0 : BitVec 12) (V + 72) (by decide)
  have h18 := addi_spec_gen_same_within .x2 sp (32 : BitVec 12)
    (V + 76) (by decide)
  have h19 := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (V + 80)
  runBlock h16 h17 h18 h19

theorem rlp_validate_payload_production_failure_tail_spec_within
    (sp old13 raVal x10Old : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (V + 48) (V + 72) wrapperCode
      (((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ x10Old) ** (.x1 ↦ᵣ (V + 44)) **
        (.x13 ↦ᵣ Frame) ** (.x0 ↦ᵣ (0 : Word)) **
        (memIs sp raVal) ** (memIs (sp + 8) old13)) ** F)
      (((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ (7 : Word)) ** (.x1 ↦ᵣ (V + 44)) **
        (.x13 ↦ᵣ Frame) ** (.x0 ↦ᵣ (0 : Word)) **
        (memIs sp raVal) ** (memIs (sp + 8) old13)) ** F) := by
  apply cpsTripleWithin_frameR F hF
  have h0 := li_spec_gen_within .x10 x10Old (7 : Word) (V + 48) (by decide)
  rw [show V + 48 + 4 = V + 52 from by bv_omega] at h0
  have h1 := jal_x0_spec_gen_within (20 : BitVec 21) (V + 52)
  rw [show V + 52 + signExtend21 (20 : BitVec 21) = V + 72 from by
        rw [show signExtend21 (20 : BitVec 21) = (20 : Word) from by decide]
        bv_omega] at h1
  runBlock h0 h1

theorem rlp_validate_payload_production_status_branch_spec_within
    (status : Word) :
    cpsBranchWithin 1 (V + 44) wrapperCode
      ((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)))
      (V + 68)
        ((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** pure (status = 0))
      (V + 48)
        ((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** pure (status ≠ 0)) := by
  have h := beq_spec_gen_within .x10 .x0 (24 : BitVec 13)
    status (0 : Word) (V + 44)
  rw [show V + 44 + signExtend13 (24 : BitVec 13) = V + 68 from by
        rw [show signExtend13 (24 : BitVec 13) = (24 : Word) from by decide]
        bv_omega,
      show V + 44 + 4 = V + 48 from by bv_omega] at h
  have hmono : ∀ a i,
      CodeReq.singleton (V + 44) (.BEQ .x10 .x0 (24 : BitVec 13)) a = some i →
        wrapperCode a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr V
        (rlpValidatePayload_prog_with_cap (rlpRecursiveDecodeDepthCap : Word)) 11
        (V + 44) (by decide) (by decide) (by bv_omega)
      simpa [wrapperCode, rlpValidatePayload_prog,
        rlpValidatePayload_prog_with_cap] using hm)
  exact cpsBranchWithin_extend_code hmono h

/-! The linked status branch and its two tails form a complete local
continuation relation.  The successful exit keeps the status register as an
unchanged output; the failure exit overwrites it with status seven and skips
the frame-pointer restore.  This is deliberately a production-side boundary
theorem, not an identification with the retired `ValidateFuel` post. -/

theorem rlp_validate_payload_production_status_tails_spec_within
    (sp old13 raVal status : Word) :
    cpsNBranchWithin 7 (V + 44) wrapperCode
      (((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x2 ↦ᵣ sp) ** (.x1 ↦ᵣ (V + 44)) **
          (.x13 ↦ᵣ Frame) **
          (memIs sp raVal) ** (memIs (sp + 8) old13)))
      [ (raVal &&& ~~~(1 : Word),
          (((.x10 ↦ᵣ status) ** (.x2 ↦ᵣ (sp + 32)) **
            (.x1 ↦ᵣ raVal) ** (.x13 ↦ᵣ old13) **
            (.x0 ↦ᵣ (0 : Word)) ** (memIs sp raVal) **
            (memIs (sp + 8) old13)) ** pure (status = 0))),
        (V + 72,
          (((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ (7 : Word)) **
            (.x1 ↦ᵣ (V + 44)) ** (.x13 ↦ᵣ Frame) **
            (.x0 ↦ᵣ (0 : Word)) ** (memIs sp raVal) **
            (memIs (sp + 8) old13)) ** pure (status ≠ 0))) ] := by
  let B :=
    ((.x2 ↦ᵣ sp) ** (.x1 ↦ᵣ (V + 44)) **
      (.x13 ↦ᵣ Frame) ** (memIs sp raVal) **
      (memIs (sp + 8) old13))
  have hB : B.pcFree := by
    dsimp [B]
    repeat' apply pcFree_sepConj
    all_goals first
      | exact pcFree_regIs
      | exact pcFree_memIs
  have hbr := cpsBranchWithin_frameR B hB
    (rlp_validate_payload_production_status_branch_spec_within status)
  have hsucc0Raw :=
    rlp_validate_payload_production_success_tail_spec_within
      sp old13 raVal empAssertion pcFree_emp
  have hsucc0 : cpsTripleWithin 4 (V + 68) (raVal &&& ~~~(1 : Word))
      wrapperCode
      ((.x2 ↦ᵣ sp) ** (.x1 ↦ᵣ (V + 44)) **
        (.x13 ↦ᵣ Frame) ** (.x0 ↦ᵣ (0 : Word)) **
        (memIs sp raVal) ** (memIs (sp + 8) old13))
      ((.x2 ↦ᵣ (sp + 32)) ** (.x1 ↦ᵣ raVal) **
        (.x13 ↦ᵣ old13) ** (.x0 ↦ᵣ (0 : Word)) **
        (memIs sp raVal) ** (memIs (sp + 8) old13)) := by
    simpa only [sepConj_emp_right'] using hsucc0Raw
  have hsucc1 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ status) ** pure (status = 0))
    (by repeat' apply pcFree_sepConj <;>
      first | exact pcFree_regIs | exact pcFree_pure) hsucc0
  have hsucc : cpsTripleWithin 4 (V + 68) (raVal &&& ~~~(1 : Word))
      wrapperCode
      (((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** pure (status = 0)) ** B)
      (((.x10 ↦ᵣ status) ** (.x2 ↦ᵣ (sp + 32)) ** (.x1 ↦ᵣ raVal) **
        (.x13 ↦ᵣ old13) ** (.x0 ↦ᵣ (0 : Word)) **
        (memIs sp raVal) ** (memIs (sp + 8) old13)) **
        pure (status = 0)) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [sepConj_assoc'] at hp ⊢
        xperm_hyp hp)
      (fun _ hp => by
        simp only [sepConj_assoc'] at hp ⊢
        xperm_hyp hp) hsucc1
  have hfail0Raw :=
    rlp_validate_payload_production_failure_tail_spec_within
      sp old13 raVal status empAssertion pcFree_emp
  have hfail0 : cpsTripleWithin 2 (V + 48) (V + 72) wrapperCode
      ((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ status) ** (.x1 ↦ᵣ (V + 44)) **
        (.x13 ↦ᵣ Frame) ** (.x0 ↦ᵣ (0 : Word)) **
        (memIs sp raVal) ** (memIs (sp + 8) old13))
      ((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ (7 : Word)) **
        (.x1 ↦ᵣ (V + 44)) ** (.x13 ↦ᵣ Frame) **
        (.x0 ↦ᵣ (0 : Word)) ** (memIs sp raVal) **
        (memIs (sp + 8) old13)) := by
    simpa only [sepConj_emp_right'] using hfail0Raw
  have hfail1 := cpsTripleWithin_frameR
    (pure (status ≠ 0)) pcFree_pure hfail0
  have hfail : cpsTripleWithin 2 (V + 48) (V + 72) wrapperCode
      (((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** pure (status ≠ 0)) ** B)
      (((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ (7 : Word)) **
        (.x1 ↦ᵣ (V + 44)) ** (.x13 ↦ᵣ Frame) **
        (.x0 ↦ᵣ (0 : Word)) ** (memIs sp raVal) **
        (memIs (sp + 8) old13)) ** pure (status ≠ 0)) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [sepConj_assoc'] at hp ⊢
        xperm_hyp hp)
      (fun _ hp => by
        simp only [sepConj_assoc'] at hp ⊢
        xperm_hyp hp) hfail1
  have hmid := cpsBranchWithin_cons_cpsNBranchWithin_same_cr hbr
    (cpsTripleWithin_as_cpsNBranchWithin hfail)
  have hfinal := cpsNBranchWithin_extend_head_nbranch hmid
    (cpsTripleWithin_as_cpsNBranchWithin hsucc)
  simpa [B, sepConj_assoc'] using hfinal

#print axioms rlp_validate_payload_items_call_spec_within
#print axioms rlp_validate_payload_production_status_tails_spec_within

end EvmAsm.Codegen.RlpValidatePayloadProductionAdapter
