/-
  EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledEmpty

  #12183 — parent `witness_lookup_by_hash` under **production** ambient:
  `widx_enabled = 1`, section matches the built index, `widx_count = 0`.

  ## Domain (SAY SO)

  * `widx_enabled = 1` (index armed — production walk ambient after build)
  * `widx_section_ptr = a0` and `widx_section_len = a1 = 0` (match)
  * `widx_count = 0` (empty index; REACHABLE with enable=1)
  * Post: `a0 = 1` miss via **indexed** empty-miss, not linear path
  * Telemetry: lookup_calls +1, indexed_calls +1, indexed_misses +1
    (linear cells untouched)

  ## Callee

  `witness_lookup_by_hash_indexed_spec_within_empty` (fuel 28) via callWithin.

  ## What this is NOT

  * Does not replace enable=0 empty_section (linear miss).
  * Hit arm under enable=1 is separate (one-hit callee).
  * Linear scan / keccak still outside claim.
-/

import EvmAsm.Codegen.Programs.WitnessLookupByHashSpec
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedSpec
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedEmpty
import EvmAsm.Codegen.Programs.MptWitnessLookup
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Codegen.WitnessLookupByHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.WitnessLookupByHashIndexedSpec
  (IndexedB fullCode wrapperCode recordPtrCode cmp32Code indexed_prog_length
    record_ptr_prog_length cmp32_prog_length WidxCountLoc indexedFrame)
open EvmAsm.Codegen.WitnessLookupByHashIndexedEmpty
  (indexedSavedVals IndexedSaved
    witness_lookup_by_hash_indexed_spec_within_empty)

set_option maxRecDepth 8000

private theorem sext12_zero : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

/-! ## Cells -/

def SecPtrLoc : Word := (GuestAddrs.widx_section_ptr : Word)
def SecLenLoc : Word := (GuestAddrs.widx_section_len : Word)
def IdxCallsLoc : Word := (GuestAddrs.wlh_indexed_calls : Word)
def IdxMissLoc : Word := (GuestAddrs.wlh_indexed_misses : Word)
def IdxHitLoc : Word := (GuestAddrs.wlh_indexed_hits : Word)

theorem enable_cells_distinct :
    WidxEnLoc ≠ SecPtrLoc ∧ WidxEnLoc ≠ SecLenLoc ∧ WidxEnLoc ≠ WidxCountLoc ∧
    WidxEnLoc ≠ IdxCallsLoc ∧ WidxEnLoc ≠ IdxMissLoc ∧ WidxEnLoc ≠ CallsLoc ∧
    SecPtrLoc ≠ SecLenLoc ∧ SecPtrLoc ≠ WidxCountLoc ∧ SecPtrLoc ≠ IdxCallsLoc ∧
    SecLenLoc ≠ WidxCountLoc ∧ IdxCallsLoc ≠ IdxMissLoc ∧ CallsLoc ≠ IdxCallsLoc := by
  unfold WidxEnLoc SecPtrLoc SecLenLoc WidxCountLoc IdxCallsLoc IdxMissLoc CallsLoc
  decide

/-! ## CodeReq: parent ∪ indexed fullCode -/

private theorem wlh_prog_length : witnessLookupByHash_prog.length = 155 := by
  decide

def enableFullCode : CodeReq := wlhCr.union fullCode

set_option maxRecDepth 8000 in
theorem wlh_wrapper_disjoint : wlhCr.Disjoint wrapperCode := by
  unfold wlhCr wrapperCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [wlh_prog_length]; decide
  · rw [indexed_prog_length]; decide
  · rw [wlh_prog_length, indexed_prog_length]; decide

set_option maxRecDepth 8000 in
theorem wlh_record_ptr_disjoint : wlhCr.Disjoint recordPtrCode := by
  unfold wlhCr recordPtrCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [wlh_prog_length]; decide
  · rw [record_ptr_prog_length]; decide
  · rw [wlh_prog_length, record_ptr_prog_length]; decide

set_option maxRecDepth 8000 in
theorem wlh_cmp32_disjoint : wlhCr.Disjoint cmp32Code := by
  unfold wlhCr cmp32Code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [wlh_prog_length]; decide
  · rw [cmp32_prog_length]; decide
  · rw [wlh_prog_length, cmp32_prog_length]; decide

theorem wlh_fullCode_disjoint : wlhCr.Disjoint fullCode := by
  have hwr : wlhCr.Disjoint (wrapperCode.union recordPtrCode) :=
    CodeReq.Disjoint.union_right wlh_wrapper_disjoint wlh_record_ptr_disjoint
  exact CodeReq.Disjoint.union_right hwr wlh_cmp32_disjoint

theorem wlh_in_enableFull :
    ∀ a i, wlhCr a = some i → enableFullCode a = some i := by
  intro a i hi
  simp only [enableFullCode, CodeReq.union, hi]

theorem idx_in_enableFull :
    ∀ a i, fullCode a = some i → enableFullCode a = some i := by
  intro a i h
  simp only [enableFullCode, CodeReq.union]
  cases hw : wlhCr a with
  | none => simpa [hw] using h
  | some j =>
    rcases wlh_fullCode_disjoint a with hnone | hnone
    · simp [hw] at hnone
    · simp [h] at hnone

/-- Close `∀ a i, singleton/ofProg … → enableFullCode a = some i` when the
    code lives in the parent program. -/
macro "enable_parent_mem" : tactic =>
  `(tactic| (intro a i hi; apply wlh_in_enableFull; revert a i hi; unfold wlhCr; code_mem))

/-! ## Enabled-empty args / outs -/

def wlhEnArgs (v5 v6 secPtr hashPtr outOffP outLenP
    nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
  ((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
  ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
  ((.x14 : Reg) ↦ᵣ outLenP) **
  (CallsLoc ↦ₘ nCalls) ** (WidxEnLoc ↦ₘ (1 : Word)) **
  (SecPtrLoc ↦ₘ secPtr) ** (SecLenLoc ↦ₘ (0 : Word)) **
  (WidxCountLoc ↦ₘ (0 : Word)) **
  (IdxCallsLoc ↦ₘ nIdx) ** (IdxMissLoc ↦ₘ nMiss) **
  (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
  (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss)

def wlhEnMissOut (secPtr hashPtr outOffP outLenP
    nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  ((.x10 : Reg) ↦ᵣ (1 : Word)) **
  ((.x11 : Reg) ↦ᵣ (0 : Word)) **
  ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
  ((.x14 : Reg) ↦ᵣ outLenP) **
  (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (1 : Word)) **
  (SecPtrLoc ↦ₘ secPtr) ** (SecLenLoc ↦ₘ (0 : Word)) **
  (WidxCountLoc ↦ₘ (0 : Word)) **
  (IdxCallsLoc ↦ₘ (nIdx + 1)) ** (IdxMissLoc ↦ₘ (nMiss + 1)) **
  (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
  (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss)

theorem wlhEnArgs_pcFree (v5 v6 secPtr hashPtr outOffP outLenP
    nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word) :
    (wlhEnArgs v5 v6 secPtr hashPtr outOffP outLenP
      nCalls nIdx nMiss nLin nLast nMax nLinMiss).pcFree := by
  unfold wlhEnArgs
  repeat' first
    | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs

theorem wlhEnMissOut_pcFree (secPtr hashPtr outOffP outLenP
    nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word) :
    (wlhEnMissOut secPtr hashPtr outOffP outLenP
      nCalls nIdx nMiss nLin nLast nMax nLinMiss).pcFree := by
  unfold wlhEnMissOut
  repeat' first
    | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs

/-! ## S3' — enable=1 falls through (BEQ ntaken) -/

private theorem beq_zero_ne_absurd {r1 r2 : Reg} {v : Word} (hne : v ≠ 0) :
    ∀ hp, (((r1 : Reg) ↦ᵣ v) ** ((r2 : Reg) ↦ᵣ (0 : Word)) ** ⌜v = (0 : Word)⌝) hp →
      False := by
  intro hp hq
  obtain ⟨_, _, _, _, _, hB⟩ := hq
  obtain ⟨_, _, _, _, _, hP⟩ := hB
  exact hne hP.2

/-- Load `widx_enabled = 1` and fall through the `beq` (do not take linear). -/
theorem wlhEnableFallthrough_spec (v5 : Word) :
    cpsTripleWithin 4 (wlhB + 76) (wlhB + 92) enableFullCode
      (((.x5 : Reg) ↦ᵣ v5) ** (WidxEnLoc ↦ₘ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (((.x5 : Reg) ↦ᵣ (1 : Word)) ** (WidxEnLoc ↦ₘ (1 : Word)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word))) := by
  have hla := la_materialize_within .x5 v5 (wlhB + 76) WidxEnLoc
    (cr := enableFullCode)
    (by decide) (by decide)
    (by enable_parent_mem) (by enable_parent_mem)
  rw [show (wlhB + 76 : Word) + 8 = wlhB + 84 from by bv_omega] at hla
  have hld := liftCode (cr' := enableFullCode)
    (ld_spec_gen_same_within .x5 WidxEnLoc (1 : Word) (0 : BitVec 12) (wlhB + 84)
      (by decide))
    (by enable_parent_mem)
  rw [sext12_zero, show WidxEnLoc + (0 : Word) = WidxEnLoc from by bv_omega,
    show (wlhB + 84 : Word) + 4 = wlhB + 88 from by bv_omega] at hld
  have hbr := cpsBranchWithin_extend_code (cr' := enableFullCode)
    (by enable_parent_mem)
    (beq_spec_gen_within .x5 .x0
      (brOff (GuestAddrs.witness_lookup_by_hash + 220)
        (GuestAddrs.witness_lookup_by_hash + 88)) (1 : Word) (0 : Word) (wlhB + 88))
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr
    (beq_zero_ne_absurd (by decide : (1 : Word) ≠ 0))
  rw [show (wlhB + 88 : Word) + 4 = wlhB + 92 from by bv_omega] at hnt
  have f1 := cpsTripleWithin_frameR
    ((WidxEnLoc ↦ₘ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) (by pcf) hla
  have f2 := cpsTripleWithin_frameR (((.x0 : Reg) ↦ᵣ (0 : Word))) (by pcf) hld
  have f3 := cpsTripleWithin_frameR ((WidxEnLoc ↦ₘ (1 : Word))) (by pcf) hnt
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f1 f2
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 f3
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c2)


/-! ## S4 — section_ptr match (BNE ntaken when equal) -/

private theorem bne_same_absurd {r1 r2 : Reg} {v : Word} :
    ∀ hp, (((r1 : Reg) ↦ᵣ v) ** ((r2 : Reg) ↦ᵣ v) ** ⌜v ≠ v⌝) hp → False := by
  intro hp hq
  obtain ⟨_, _, _, _, _, hB⟩ := hq
  obtain ⟨_, _, _, _, _, hP⟩ := hB
  exact hP.2 rfl

/-- Load section_ptr and fall through BNE (s0 equals loaded value). -/
theorem wlhSecPtrMatch_spec (v5 secPtr : Word) :
    cpsTripleWithin 4 (wlhB + 92) (wlhB + 108) enableFullCode
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x8 : Reg) ↦ᵣ secPtr) **
        (SecPtrLoc ↦ₘ secPtr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (((.x5 : Reg) ↦ᵣ secPtr) ** ((.x8 : Reg) ↦ᵣ secPtr) **
        (SecPtrLoc ↦ₘ secPtr) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) := by
  have hla := la_materialize_within .x5 v5 (wlhB + 92) SecPtrLoc
    (cr := enableFullCode) (by decide) (by decide)
    (by enable_parent_mem) (by enable_parent_mem)
  rw [show (wlhB + 92 : Word) + 8 = wlhB + 100 from by bv_omega] at hla
  have hld := liftCode (cr' := enableFullCode)
    (ld_spec_gen_same_within .x5 SecPtrLoc secPtr (0 : BitVec 12) (wlhB + 100)
      (by decide))
    (by enable_parent_mem)
  rw [sext12_zero, show SecPtrLoc + (0 : Word) = SecPtrLoc from by bv_omega,
    show (wlhB + 100 : Word) + 4 = wlhB + 104 from by bv_omega] at hld
  have hbr := cpsBranchWithin_extend_code (cr' := enableFullCode)
    (by enable_parent_mem)
    (bne_spec_gen_within .x8 .x5
      (brOff (GuestAddrs.witness_lookup_by_hash + 220)
        (GuestAddrs.witness_lookup_by_hash + 104)) secPtr secPtr (wlhB + 104))
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr bne_same_absurd
  rw [show (wlhB + 104 : Word) + 4 = wlhB + 108 from by bv_omega] at hnt
  have f1 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ secPtr) ** (SecPtrLoc ↦ₘ secPtr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hla
  have f2 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ secPtr) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) (by pcf) hld
  have f3 := cpsTripleWithin_frameR
    ((SecPtrLoc ↦ₘ secPtr) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) (by pcf) hnt
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f1 f2
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 f3
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c2)

/-- Load section_len=0 and fall through BNE (s1 equals 0). -/
theorem wlhSecLenMatch_spec (v5 : Word) :
    cpsTripleWithin 4 (wlhB + 108) (wlhB + 124) enableFullCode
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
        (SecLenLoc ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (((.x5 : Reg) ↦ᵣ (0 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
        (SecLenLoc ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) := by
  have hla := la_materialize_within .x5 v5 (wlhB + 108) SecLenLoc
    (cr := enableFullCode) (by decide) (by decide)
    (by enable_parent_mem) (by enable_parent_mem)
  rw [show (wlhB + 108 : Word) + 8 = wlhB + 116 from by bv_omega] at hla
  have hld := liftCode (cr' := enableFullCode)
    (ld_spec_gen_same_within .x5 SecLenLoc (0 : Word) (0 : BitVec 12) (wlhB + 116)
      (by decide))
    (by enable_parent_mem)
  rw [sext12_zero, show SecLenLoc + (0 : Word) = SecLenLoc from by bv_omega,
    show (wlhB + 116 : Word) + 4 = wlhB + 120 from by bv_omega] at hld
  have hbr := cpsBranchWithin_extend_code (cr' := enableFullCode)
    (by enable_parent_mem)
    (bne_spec_gen_within .x9 .x5
      (brOff (GuestAddrs.witness_lookup_by_hash + 220)
        (GuestAddrs.witness_lookup_by_hash + 120)) (0 : Word) (0 : Word) (wlhB + 120))
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr bne_same_absurd
  rw [show (wlhB + 120 : Word) + 4 = wlhB + 124 from by bv_omega] at hnt
  have f1 := cpsTripleWithin_frameR
    (((.x9 : Reg) ↦ᵣ (0 : Word)) ** (SecLenLoc ↦ₘ (0 : Word)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word))) (by pcf) hla
  have f2 := cpsTripleWithin_frameR
    (((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) (by pcf) hld
  have f3 := cpsTripleWithin_frameR
    ((SecLenLoc ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) (by pcf) hnt
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f1 f2
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 f3
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c2)

/-! ## S5 — restore ABI args from s-regs before indexed call -/

theorem wlhIdxAbiMoves_spec (secPtr hashPtr outOffP outLenP
    a10 a11 a12 a13 a14 : Word) :
    cpsTripleWithin 5 (wlhB + 124) (wlhB + 144) enableFullCode
      (((.x8 : Reg) ↦ᵣ secPtr) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
        ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
        ((.x20 : Reg) ↦ᵣ outLenP) **
        ((.x10 : Reg) ↦ᵣ a10) ** ((.x11 : Reg) ↦ᵣ a11) **
        ((.x12 : Reg) ↦ᵣ a12) ** ((.x13 : Reg) ↦ᵣ a13) ** ((.x14 : Reg) ↦ᵣ a14))
      (((.x8 : Reg) ↦ᵣ secPtr) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
        ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
        ((.x20 : Reg) ↦ᵣ outLenP) **
        ((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
        ((.x14 : Reg) ↦ᵣ outLenP)) := by
  have h0 := liftCode (cr' := enableFullCode)
    (mv_spec_gen_within .x10 .x8 secPtr a10 (wlhB + 124) (by decide))
    (by enable_parent_mem)
  rw [show (wlhB + 124 : Word) + 4 = wlhB + 128 from by bv_omega] at h0
  have h1 := liftCode (cr' := enableFullCode)
    (mv_spec_gen_within .x11 .x9 (0 : Word) a11 (wlhB + 128) (by decide))
    (by enable_parent_mem)
  rw [show (wlhB + 128 : Word) + 4 = wlhB + 132 from by bv_omega] at h1
  have h2 := liftCode (cr' := enableFullCode)
    (mv_spec_gen_within .x12 .x18 hashPtr a12 (wlhB + 132) (by decide))
    (by enable_parent_mem)
  rw [show (wlhB + 132 : Word) + 4 = wlhB + 136 from by bv_omega] at h2
  have h3 := liftCode (cr' := enableFullCode)
    (mv_spec_gen_within .x13 .x19 outOffP a13 (wlhB + 136) (by decide))
    (by enable_parent_mem)
  rw [show (wlhB + 136 : Word) + 4 = wlhB + 140 from by bv_omega] at h3
  have h4 := liftCode (cr' := enableFullCode)
    (mv_spec_gen_within .x14 .x20 outLenP a14 (wlhB + 140) (by decide))
    (by enable_parent_mem)
  rw [show (wlhB + 140 : Word) + 4 = wlhB + 144 from by bv_omega] at h4
  -- MV focuses rd+rs; frame omits both.
  have f0 := cpsTripleWithin_frameR
    (((.x9 : Reg) ↦ᵣ (0 : Word)) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
      ((.x20 : Reg) ↦ᵣ outLenP) ** ((.x11 : Reg) ↦ᵣ a11) **
      ((.x12 : Reg) ↦ᵣ a12) ** ((.x13 : Reg) ↦ᵣ a13) ** ((.x14 : Reg) ↦ᵣ a14))
    (by pcf) h0
  have f1 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ secPtr) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
      ((.x20 : Reg) ↦ᵣ outLenP) ** ((.x10 : Reg) ↦ᵣ secPtr) **
      ((.x12 : Reg) ↦ᵣ a12) ** ((.x13 : Reg) ↦ᵣ a13) ** ((.x14 : Reg) ↦ᵣ a14))
    (by pcf) h1
  have f2 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ secPtr) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
      ((.x19 : Reg) ↦ᵣ outOffP) **
      ((.x20 : Reg) ↦ᵣ outLenP) ** ((.x10 : Reg) ↦ᵣ secPtr) **
      ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x13 : Reg) ↦ᵣ a13) **
      ((.x14 : Reg) ↦ᵣ a14)) (by pcf) h2
  have f3 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ secPtr) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
      ((.x18 : Reg) ↦ᵣ hashPtr) **
      ((.x20 : Reg) ↦ᵣ outLenP) ** ((.x10 : Reg) ↦ᵣ secPtr) **
      ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
      ((.x14 : Reg) ↦ᵣ a14)) (by pcf) h3
  have f4 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ secPtr) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
      ((.x10 : Reg) ↦ᵣ secPtr) **
      ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
      ((.x13 : Reg) ↦ᵣ outOffP)) (by pcf) h4
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f0 f1
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 f2
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 f3
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c3 f4
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c4)


/-! ## S6 — bump indexed_calls -/

/-- Bump `wlh_indexed_calls` at body +144 (5 insn). -/
theorem wlhIdxCallsBump_spec (v5 v6 nIdx : Word) :
    cpsTripleWithin 5 (wlhB + 144) (wlhB + 164) enableFullCode
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** (IdxCallsLoc ↦ₘ nIdx))
      (((.x5 : Reg) ↦ᵣ IdxCallsLoc) ** ((.x6 : Reg) ↦ᵣ (nIdx + 1)) **
        (IdxCallsLoc ↦ₘ (nIdx + 1))) := by
  have hbase := wlhCounterBump_spec (wlhB + 144) IdxCallsLoc v5 v6 nIdx
    (by decide)
    (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem)
    (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem)
    (by unfold wlhCr; code_mem)
  exact cpsTripleWithin_extend_code wlh_in_enableFull hbase

/-- Bump `wlh_indexed_misses` at body +196 (5 insn). -/
theorem wlhIdxMissBump_spec (v5 v6 nMiss : Word) :
    cpsTripleWithin 5 (wlhB + 196) (wlhB + 216) enableFullCode
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** (IdxMissLoc ↦ₘ nMiss))
      (((.x5 : Reg) ↦ᵣ IdxMissLoc) ** ((.x6 : Reg) ↦ᵣ (nMiss + 1)) **
        (IdxMissLoc ↦ₘ (nMiss + 1))) := by
  have hbase := wlhCounterBump_spec (wlhB + 196) IdxMissLoc v5 v6 nMiss
    (by decide)
    (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem)
    (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem)
    (by unfold wlhCr; code_mem)
  exact cpsTripleWithin_extend_code wlh_in_enableFull hbase

private theorem indexed_jal_target :
    (wlhB + 164) + signExtend21
      (jalOff GuestAddrs.witness_lookup_by_hash_indexed
        (GuestAddrs.witness_lookup_by_hash + 164)) =
      (IndexedB : Word) := by
  unfold wlhB IndexedB; decide

private theorem indexed_ret_pc :
    (wlhB + 164 : Word) + 4 = wlhB + 168 := by
  unfold wlhB; decide

private theorem miss_jal_epi_target :
    (wlhB + 216) + signExtend21
      (jalOff (GuestAddrs.witness_lookup_by_hash + 580)
        (GuestAddrs.witness_lookup_by_hash + 216)) =
      wlhB + 580 := by
  unfold wlhB; decide

/-- After indexed returns a0=1, BNE taken jumps to miss telemetry (+196). -/
theorem wlhIndexedMissBranch_spec (v0 : Word) (hne : v0 ≠ 0) :
    cpsTripleWithin 1 (wlhB + 168) (wlhB + 196) enableFullCode
      (((.x10 : Reg) ↦ᵣ v0) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (((.x10 : Reg) ↦ᵣ v0) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) := by
  have hbr := cpsBranchWithin_extend_code (cr' := enableFullCode)
    (by enable_parent_mem)
    (bne_spec_gen_within .x10 .x0 (28 : BitVec 13) v0 (0 : Word) (wlhB + 168))
  -- taken arm: v0 ≠ 0 is the pure on taken
  have htk := cpsBranchWithin_takenStripPure2 hbr
    (fun hp hq => by
      -- fallthrough pure is ⌜v0 = 0⌝
      obtain ⟨_, _, _, _, _, hB⟩ := hq
      obtain ⟨_, _, _, _, _, hP⟩ := hB
      exact hne hP.2)
  rw [show (wlhB + 168 : Word) + signExtend13 (28 : BitVec 13) = wlhB + 196
      from by unfold wlhB; decide] at htk
  exact cpsTripleWithin_mono_nSteps (by omega) htk

/-- JAL x0 to epilogue at +580 from +216. -/
theorem wlhJalEpi_spec :
    cpsTripleWithin 1 (wlhB + 216) (wlhB + 580) enableFullCode
      empAssertion empAssertion := by
  have h := liftCode (cr' := enableFullCode)
    (jal_x0_spec_gen_within
      (jalOff (GuestAddrs.witness_lookup_by_hash + 580)
        (GuestAddrs.witness_lookup_by_hash + 216)) (wlhB + 216))
    (by enable_parent_mem)
  rw [miss_jal_epi_target] at h
  exact h






/-! ## Nested call: parent JAL → indexed empty-miss

    Nested stack: callee needs 8 free dwords below parent SP. Walk ambient
    must supply `stackFree sp0 16` at wl entry (`stackFree_split`).
    **SAY SO**: enable=1 path is more than glue — nested stack budget grows.
-/

private abbrev WlhProgL : List Instr := witnessLookupByHash_prog

private theorem wlhProgL_length : WlhProgL.length = 155 := by
  simp only [WlhProgL]; exact wlh_prog_length

private theorem indexedFrame_eq_wlhFrame : indexedFrame = wlhFrame := by decide

theorem stackFree8_eq_indexedSlotsOwn (sp : Word) :
    stackFree sp 8 =
      frameSlotsOwn indexedFrame (sp + signExtend12 (-64 : BitVec 12)) := by
  rw [indexedFrame_eq_wlhFrame, stackFree8_eq_frameSlotsOwn]

private abbrev idxJalOff : BitVec 21 :=
  jalOff GuestAddrs.witness_lookup_by_hash_indexed
    (GuestAddrs.witness_lookup_by_hash + 164)

private theorem idx_jal_target :
    (wlhB + 164 : Word) + signExtend21 idxJalOff = (IndexedB : Word) := by
  unfold wlhB IndexedB idxJalOff
  decide

private theorem idx_call_ret_even :
    (((wlhB + 164 : Word) + 4) &&& ~~~(1 : Word)) = (wlhB + 164 : Word) + 4 := by
  decide

private theorem prog_jal_indexed :
    WlhProgL[41]'(by rw [wlhProgL_length]; decide) =
      Instr.JAL .x1 idxJalOff := by
  unfold WlhProgL witnessLookupByHash_prog idxJalOff
  rfl

/-- CallWithin P: empty-miss needs except `x1`. -/
def wlhIdxCallP (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen v5 v10 : Word) : Assertion :=
  ((.x2 ↦ᵣ spC) **
    (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
    (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
    (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
    (.x12 ↦ᵣ hashPtr) ** (.x13 ↦ᵣ outOff) ** (.x14 ↦ᵣ outLen) **
    (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
    frameSlotsOwn indexedFrame (spC + signExtend12 (-64 : BitVec 12)) **
    (WidxCountLoc ↦ₘ (0 : Word)))

/-- CallWithin Q: empty-miss post without outer `x1`. -/
def wlhIdxCallQ (spC ret : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word) : Assertion :=
  ((.x10 ↦ᵣ (1 : Word)) ** (.x2 ↦ᵣ spC) **
    (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
    (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
    (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
    frameSlotsSaved indexedFrame (spC + signExtend12 (-64 : BitVec 12))
      (indexedSavedVals { s with ra := ret }) **
    ((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)) **
    ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
    ((.x14 : Reg) ↦ᵣ outLen))

private theorem wlhIdxCallP_pcFree (spC : Word) (s : IndexedSaved)
    (hashPtr outOff outLen v5 v10 : Word) :
    (wlhIdxCallP spC s hashPtr outOff outLen v5 v10).pcFree := by
  dsimp [wlhIdxCallP]
  -- frameSlotsOwn unfolds to memOwn chain under simp; reg/mem atoms only
  repeat' first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_emp

/-- Nested callWithin at +164 → indexed empty-miss → +168. Fuel 29. -/
theorem wlhIndexedEmptyCall_spec
    (spC vOld : Word) (s : IndexedSaved)
    (hashPtr outOff outLen v5 v10 : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 29 (wlhB + 164) (wlhB + 168) enableFullCode
      ((.x1 ↦ᵣ vOld) ** wlhIdxCallP spC s hashPtr outOff outLen v5 v10 ** F)
      ((.x1 ↦ᵣ ((wlhB + 164 : Word) + 4)) **
        wlhIdxCallQ spC ((wlhB + 164 : Word) + 4) s hashPtr outOff outLen ** F) := by
  set ret : Word := (wlhB + 164 : Word) + 4
  have hbase0 :=
    witness_lookup_by_hash_indexed_spec_within_empty spC ret s
      hashPtr outOff outLen v5 v10 idx_call_ret_even
  have hbase := cpsTripleWithin_extend_code idx_in_enableFull hbase0
  have hcallee0 : cpsTripleWithin 28 (IndexedB : Word) ret enableFullCode
      ((.x1 ↦ᵣ ret) ** wlhIdxCallP spC s hashPtr outOff outLen v5 v10)
      ((.x1 ↦ᵣ ret) ** wlhIdxCallQ spC ret s hashPtr outOff outLen) := by
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hbase
    · rw [WitnessLookupByHashIndexedEmpty.regsAt_indexedFrame]
      dsimp [wlhIdxCallP, indexedSavedVals] at hp ⊢
      xperm_chunked hp
    · dsimp [wlhIdxCallQ, indexedSavedVals] at hq ⊢
      xperm_chunked hq
  have hP :
      (wlhIdxCallP spC s hashPtr outOff outLen v5 v10 ** F).pcFree :=
    pcFree_sepConj (wlhIdxCallP_pcFree _ _ _ _ _ _ _) hF
  have hcallee : cpsTripleWithin 28 (IndexedB : Word) ret enableFullCode
      ((.x1 ↦ᵣ ret) ** (wlhIdxCallP spC s hashPtr outOff outLen v5 v10 ** F))
      ((.x1 ↦ᵣ ret) ** (wlhIdxCallQ spC ret s hashPtr outOff outLen ** F)) := by
    have hfr := cpsTripleWithin_frameR F hF hcallee0
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hfr
  have hmem : ∀ a i,
      CodeReq.singleton (wlhB + 164) (Instr.JAL .x1 idxJalOff) a = some i →
        enableFullCode a = some i := by
    intro a i hh
    apply wlh_in_enableFull
    exact CodeReq.ofProg_mem_at wlhB (wlhB + 164) WlhProgL 41
      (Instr.JAL .x1 idxJalOff)
      (by unfold wlhB; decide)
      (by rw [wlhProgL_length]; decide)
      prog_jal_indexed
      (by rw [wlhProgL_length]; decide)
      a i hh
  have hcall := callWithin_spec (wlhB + 164) (IndexedB : Word) vOld idxJalOff 28
    idx_jal_target hmem hP hcallee
  -- hcall exit A+4 = ret; goal exit wlhB+168
  have hpc : ret = wlhB + 168 := by simp only [ret]; unfold wlhB; decide
  have hn : 1 + 28 = 29 := rfl
  -- Rewrite exit PC only
  have hcall' : cpsTripleWithin 29 (wlhB + 164) (wlhB + 168) enableFullCode
      ((.x1 ↦ᵣ vOld) ** (wlhIdxCallP spC s hashPtr outOff outLen v5 v10 ** F))
      ((.x1 ↦ᵣ ret) ** (wlhIdxCallQ spC ret s hashPtr outOff outLen ** F)) := by
    rw [← hn, ← hpc]
    exact hcall
  exact hcall'

end EvmAsm.Codegen.WitnessLookupByHashSpec
