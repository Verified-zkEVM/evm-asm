/-
  EvmAsm.Codegen.Programs.HeaderFieldsGenericBlocks

  Extractor-parametric ("generic") versions of the shared header-field-extractor
  glue blocks, abstracted over the guest base address (`base`), the ambient code
  (`code`), the exact PCs of the tail instructions (supplied via per-instruction
  `CodeReq.singleton … → code` membership hypotheses, exactly as `hesrMarshalNext`
  does), and the two global scratch cells (`offAddr`/`lenAddr`).

  The state-root proof hand-wrote each of these blocks pinned to `hesrBase` /
  `headerExtractStateRoot_prog` / the state-root scratch addresses.  These generic
  copies let a single stage lemma be applied N times (6 for receipts, 17 for
  withdrawals) without re-deriving the shared spine per field index.

  Classical-3 axioms only; no `sorry`/`native_decide`/`bv_decide`.
-/
import EvmAsm.Codegen.Programs.HeaderFieldsSpecCommon

namespace EvmAsm.Codegen.HeaderFieldsSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

/-- Discharge a `.pcFree` side goal over frames of `bytesRegion`/`regIs`/`memIs`
    cells. -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj
    | pcFree)

/-! ## Generic scratch/ambient descriptors (parametric over `offAddr`/`lenAddr`) -/

/-- The two written global scratch cells, folded to one atom (both stay `memOwn`
    in the return post).  Parametric over the extractor's two scratch addresses. -/
def hfScratchConst (offAddr lenAddr : Word) : Assertion := memOwn offAddr ** memOwn lenAddr

theorem pcFree_hfScratchConst (offAddr lenAddr : Word) :
    (hfScratchConst offAddr lenAddr).pcFree := by
  unfold hfScratchConst
  exact pcFree_sepConj pcFree_memOwn pcFree_memOwn

/-- The pass-through carry the walk and dispatch never write: the two global
    scratch cells (`hfScratchConst`) and the output buffer. -/
def hfAmbConst (offAddr lenAddr outPtr : Word) (outBytes : List (BitVec 8)) : Assertion :=
  hfScratchConst offAddr lenAddr ** bytesRegion outPtr outBytes

theorem pcFree_hfAmbConst (offAddr lenAddr outPtr : Word) (outBytes : List (BitVec 8)) :
    (hfAmbConst offAddr lenAddr outPtr outBytes).pcFree := by
  unfold hfAmbConst
  exact pcFree_sepConj (pcFree_hfScratchConst _ _) (bytesRegion_pcFree _ _)

/-- The caller ambient the `rlp_walk_next` calls do not touch = `hesrAmbRegs`
    (consumed by the epilogue) followed by `hfAmbConst` (pass-through). -/
def hfWalkAmbient (offAddr lenAddr newSp outPtr listBase v9 : Word) (saved : Saved)
    (outBytes : List (BitVec 8)) : Assertion :=
  hesrAmbRegs newSp listBase v9 outPtr saved ** hfAmbConst offAddr lenAddr outPtr outBytes

theorem pcFree_hfWalkAmbient (offAddr lenAddr newSp outPtr listBase v9 : Word) (saved : Saved)
    (outBytes : List (BitVec 8)) :
    (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes).pcFree := by
  unfold hfWalkAmbient
  exact pcFree_sepConj (pcFree_hesrAmbRegs _ _ _ _ _) (pcFree_hfAmbConst _ _ _ _)

/-- The single shared function-return postcondition of the whole dispatch, a
    3-way disjunction pinning `Success`/`Failure`.  Parametric over the extractor's
    two scratch addresses. -/
def hfRetPost (offAddr lenAddr newSp listBase outPtr : Word) (saved : Saved)
    (headerBytes outBytes : List (BitVec 8)) (listLen index : Nat)
    (Fr : Assertion) : Assertion :=
  fun h => ∃ (a0v : Word) (finalOut : List (BitVec 8)) (fo len : Word),
    ((((.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ saved.ra) ** hesrAmbRegsRestored newSp saved) **
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29 **
       hfScratchConst offAddr lenAddr ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase headerBytes ** bytesRegion outPtr finalOut ** Fr)) **
     ⌜(a0v = (0 : Word) ∧ RlpListNthItemSAsm.Success headerBytes listBase listLen index fo len ∧
          len = (32 : Word) ∧ finalOut = copyIntoRegion outBytes headerBytes 0 fo.toNat 32) ∨
       (a0v = (2 : Word) ∧ RlpListNthItemSAsm.Success headerBytes listBase listLen index fo len ∧
          len ≠ (32 : Word) ∧ finalOut = outBytes) ∨
       (a0v = (1 : Word) ∧ RlpListNthItemSAsm.Failure headerBytes listBase listLen index)⌝) h

/-- Weaken the residual frame of `hfRetPost` monotonically. -/
theorem hfRetPost_frame_mono {offAddr lenAddr newSp listBase outPtr : Word} {saved : Saved}
    {headerBytes outBytes : List (BitVec 8)} {listLen index : Nat}
    {Fr Fr' : Assertion} (himp : ∀ h, Fr h → Fr' h) :
    ∀ h, hfRetPost offAddr lenAddr newSp listBase outPtr saved headerBytes outBytes listLen index Fr h →
      hfRetPost offAddr lenAddr newSp listBase outPtr saved headerBytes outBytes listLen index Fr' h := by
  intro h hq
  unfold hfRetPost at hq ⊢
  obtain ⟨a0v, finalOut, fo, len, hq'⟩ := hq
  exact ⟨a0v, finalOut, fo, len,
    sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right himp))))))))))) h hq'⟩

/-! ## Generic epilogue

    Six instructions at `epiloguePC`: restore `ra/s0/s1/s2`, deallocate the frame,
    `ret`.  The status word `a0` (and any framed rest `Fr`) is carried untouched. -/
set_option maxRecDepth 8000 in
theorem hfEpilogue {code : CodeReq} (epiloguePC newSp a0v v1 v8 v9 v18 : Word) (saved : Saved)
    (Fr : Assertion) (hFr : Fr.pcFree)
    (hc0 : ∀ a i, CodeReq.singleton epiloguePC (.LD .x1 .x2 (0 : BitVec 12)) a = some i → code a = some i)
    (hc1 : ∀ a i, CodeReq.singleton (epiloguePC + 4) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → code a = some i)
    (hc2 : ∀ a i, CodeReq.singleton (epiloguePC + 8) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → code a = some i)
    (hc3 : ∀ a i, CodeReq.singleton (epiloguePC + 12) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → code a = some i)
    (hc4 : ∀ a i, CodeReq.singleton (epiloguePC + 16) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → code a = some i)
    (hc5 : ∀ a i, CodeReq.singleton (epiloguePC + 20) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → code a = some i) :
    cpsTripleWithin 6 epiloguePC (saved.ra &&& ~~~(1 : Word)) code
      (((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** savedFrame newSp saved) ** Fr)
      (((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
        (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) **
        savedFrame newSp saved) ** Fr) := by
  unfold savedFrame
  -- [ld ra, 0(sp)]
  have hl0 := ld_spec_gen_within .x1 .x2 newSp v1 saved.ra (0 : BitVec 12) epiloguePC (by decide)
  rw [signExtend12_0, show (newSp + 0 : Word) = newSp from by bv_omega] at hl0
  have el0 := cpsTripleWithin_extend_code hc0 hl0
  have el0F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0v) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
     ((newSp + 8) ↦ₘ saved.s0) ** ((newSp + 16) ↦ₘ saved.s1) **
     ((newSp + 24) ↦ₘ saved.s2) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) el0
  -- [ld s0, 8(sp)]
  have hl1 := ld_spec_gen_within .x8 .x2 newSp v8 saved.s0 (8 : BitVec 12) (epiloguePC + 4) (by decide)
  rw [show newSp + signExtend12 (8 : BitVec 12) = newSp + 8 from by
        rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide],
      show (epiloguePC + 4 : Word) + 4 = epiloguePC + 8 from by bv_omega] at hl1
  have el1 := cpsTripleWithin_extend_code hc1 hl1
  have el1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ saved.ra) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
     (newSp ↦ₘ saved.ra) ** ((newSp + 16) ↦ₘ saved.s1) ** ((newSp + 24) ↦ₘ saved.s2) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) el1
  -- [ld s1, 16(sp)]
  have hl2 := ld_spec_gen_within .x9 .x2 newSp v9 saved.s1 (16 : BitVec 12) (epiloguePC + 8) (by decide)
  rw [show newSp + signExtend12 (16 : BitVec 12) = newSp + 16 from by
        rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide],
      show (epiloguePC + 8 : Word) + 4 = epiloguePC + 12 from by bv_omega] at hl2
  have el2 := cpsTripleWithin_extend_code hc2 hl2
  have el2F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ saved.ra) ** (.x8 ↦ᵣ saved.s0) ** (.x18 ↦ᵣ v18) **
     (newSp ↦ₘ saved.ra) ** ((newSp + 8) ↦ₘ saved.s0) ** ((newSp + 24) ↦ₘ saved.s2) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) el2
  -- [ld s2, 24(sp)]
  have hl3 := ld_spec_gen_within .x18 .x2 newSp v18 saved.s2 (24 : BitVec 12) (epiloguePC + 12) (by decide)
  rw [show newSp + signExtend12 (24 : BitVec 12) = newSp + 24 from by
        rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide],
      show (epiloguePC + 12 : Word) + 4 = epiloguePC + 16 from by bv_omega] at hl3
  have el3 := cpsTripleWithin_extend_code hc3 hl3
  have el3F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ saved.ra) ** (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
     (newSp ↦ₘ saved.ra) ** ((newSp + 8) ↦ₘ saved.s0) ** ((newSp + 16) ↦ₘ saved.s1) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) el3
  have hr01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) el0F el1F
  have hr012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hr01 el2F
  have hldF := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hr012 el3F
  -- [addi sp, sp, 48]
  have haddi := addi_spec_gen_same_within .x2 newSp (48 : BitVec 12) (epiloguePC + 16) (by decide)
  rw [show newSp + signExtend12 (48 : BitVec 12) = newSp + 48 from by
      rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide],
    show (epiloguePC + 16 : Word) + 4 = epiloguePC + 20 from by bv_omega] at haddi
  have haddiE := cpsTripleWithin_extend_code hc4 haddi
  have haddiF := cpsTripleWithin_frameR
    (((.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ saved.ra) ** (.x8 ↦ᵣ saved.s0) **
      (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** (newSp ↦ₘ saved.ra) ** ((newSp + 8) ↦ₘ saved.s0) ** ((newSp + 16) ↦ₘ saved.s1) ** ((newSp + 24) ↦ₘ saved.s2)) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) haddiE
  -- [jalr x0, 0(x1)]
  have hjalr := jalr_x0_spec_gen_within .x1 saved.ra (0 : BitVec 12) (epiloguePC + 20)
  simp only [signExtend12_0] at hjalr
  rw [show (saved.ra + 0 : Word) = saved.ra from by bv_omega] at hjalr
  have hjalrE := cpsTripleWithin_extend_code hc5 hjalr
  have hjalrF := cpsTripleWithin_frameR
    (((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x8 ↦ᵣ saved.s0) **
      (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** (newSp ↦ₘ saved.ra) ** ((newSp + 8) ↦ₘ saved.s0) ** ((newSp + 16) ↦ₘ saved.s1) ** ((newSp + 24) ↦ₘ saved.s2)) ** Fr)
    (by repeat' first | exact hFr | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hjalrE
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hldF haddiF
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hjalrF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) s2

/-! ## Generic status-1 (parse/walk failure) return tail

    `li a0, 1` at `status1PC`, `jal x0, +8` → the epilogue at `status1PC + 12`
    (the `+8` offset from the JAL PC `status1PC + 4` skips the status-2 code). -/
set_option maxRecDepth 8000 in
theorem hfStatus1Return {code : CodeReq} (status1PC newSp a0old v1 v8 v9 v18 : Word) (saved : Saved)
    (Fr : Assertion) (hFr : Fr.pcFree)
    (hcli : ∀ a i, CodeReq.singleton status1PC (.LI .x10 (1 : Word)) a = some i → code a = some i)
    (hcj : ∀ a i, CodeReq.singleton (status1PC + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → code a = some i)
    (hc0 : ∀ a i, CodeReq.singleton (status1PC + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → code a = some i)
    (hc1 : ∀ a i, CodeReq.singleton (status1PC + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → code a = some i)
    (hc2 : ∀ a i, CodeReq.singleton (status1PC + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → code a = some i)
    (hc3 : ∀ a i, CodeReq.singleton (status1PC + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → code a = some i)
    (hc4 : ∀ a i, CodeReq.singleton (status1PC + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → code a = some i)
    (hc5 : ∀ a i, CodeReq.singleton (status1PC + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → code a = some i) :
    cpsTripleWithin (2 + 6) status1PC (saved.ra &&& ~~~(1 : Word)) code
      (((.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** savedFrame newSp saved) ** Fr)
      (((.x10 ↦ᵣ (1 : Word)) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
        (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) **
        savedFrame newSp saved) ** Fr) := by
  have hli := li_spec_gen_within .x10 a0old (1 : Word) status1PC (by decide)
  have hliE := cpsTripleWithin_extend_code hcli hli
  have hliF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ v18) ** savedFrame newSp saved) ** Fr) (by
      repeat' first
        | exact hFr | unfold savedFrame | exact pcFree_regIs | exact pcFree_memIs
        | apply pcFree_sepConj) hliE
  have hj := jal_x0_spec_gen_within (8 : BitVec 21) (status1PC + 4)
  rw [show status1PC + 4 + signExtend21 (8 : BitVec 21) = status1PC + 12 from by
      rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]; bv_omega] at hj
  have hjE := cpsTripleWithin_extend_code hcj hj
  have hjF := cpsTripleWithin_frameR
    (((.x10 ↦ᵣ (1 : Word)) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** savedFrame newSp saved) ** Fr) (by
      repeat' first
        | exact hFr | unfold savedFrame | exact pcFree_regIs | exact pcFree_memIs
        | apply pcFree_sepConj) hjE
  rw [sepConj_emp_left'] at hjF
  have hep := hfEpilogue (status1PC + 12) newSp (1 : Word) v1 v8 v9 v18 saved Fr hFr
    hc0
    (fun a i h => hc1 a i (by rw [show (status1PC + 12 + 4 : Word) = status1PC + 16 from by bv_omega] at h; exact h))
    (fun a i h => hc2 a i (by rw [show (status1PC + 12 + 8 : Word) = status1PC + 20 from by bv_omega] at h; exact h))
    (fun a i h => hc3 a i (by rw [show (status1PC + 12 + 12 : Word) = status1PC + 24 from by bv_omega] at h; exact h))
    (fun a i h => hc4 a i (by rw [show (status1PC + 12 + 16 : Word) = status1PC + 28 from by bv_omega] at h; exact h))
    (fun a i h => hc5 a i (by rw [show (status1PC + 12 + 20 : Word) = status1PC + 32 from by bv_omega] at h; exact h))
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hliF hjF
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hep
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s2)

/-- Bundled-entry wrapper for the status-1 return: the ambient registers stay
    folded as `hesrAmbRegs`/`hesrAmbRegsRestored`. -/
theorem hfStatus1Bundled {code : CodeReq} (status1PC newSp listBase v9 outPtr a0old v1 : Word)
    (saved : Saved) (Fr : Assertion) (hFr : Fr.pcFree)
    (hcli : ∀ a i, CodeReq.singleton status1PC (.LI .x10 (1 : Word)) a = some i → code a = some i)
    (hcj : ∀ a i, CodeReq.singleton (status1PC + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → code a = some i)
    (hc0 : ∀ a i, CodeReq.singleton (status1PC + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → code a = some i)
    (hc1 : ∀ a i, CodeReq.singleton (status1PC + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → code a = some i)
    (hc2 : ∀ a i, CodeReq.singleton (status1PC + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → code a = some i)
    (hc3 : ∀ a i, CodeReq.singleton (status1PC + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → code a = some i)
    (hc4 : ∀ a i, CodeReq.singleton (status1PC + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → code a = some i)
    (hc5 : ∀ a i, CodeReq.singleton (status1PC + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → code a = some i) :
    cpsTripleWithin (2 + 6) status1PC (saved.ra &&& ~~~(1 : Word)) code
      (((.x10 ↦ᵣ a0old) ** (.x1 ↦ᵣ v1)) ** hesrAmbRegs newSp listBase v9 outPtr saved ** Fr)
      (((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ saved.ra)) **
        hesrAmbRegsRestored newSp saved ** Fr) := by
  have h := hfStatus1Return status1PC newSp a0old v1 listBase v9 outPtr saved Fr hFr
    hcli hcj hc0 hc1 hc2 hc3 hc4 hc5
  refine cpsTripleWithin_weaken
    (fun _ hp => by unfold hesrAmbRegs at hp; xperm_hyp hp)
    (fun _ hq => by unfold hesrAmbRegsRestored; xperm_hyp hq) h

/-! ## Generic status-2 (wrong-length) return tail

    `li a0, 2` at `status2PC` then fall straight into the epilogue at `status2PC + 4`. -/
set_option maxRecDepth 8000 in
theorem hfStatus2Return {code : CodeReq} (status2PC newSp a0old v1 v8 v9 v18 : Word) (saved : Saved)
    (Fr : Assertion) (hFr : Fr.pcFree)
    (hcli : ∀ a i, CodeReq.singleton status2PC (.LI .x10 (2 : Word)) a = some i → code a = some i)
    (hc0 : ∀ a i, CodeReq.singleton (status2PC + 4) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → code a = some i)
    (hc1 : ∀ a i, CodeReq.singleton (status2PC + 8) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → code a = some i)
    (hc2 : ∀ a i, CodeReq.singleton (status2PC + 12) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → code a = some i)
    (hc3 : ∀ a i, CodeReq.singleton (status2PC + 16) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → code a = some i)
    (hc4 : ∀ a i, CodeReq.singleton (status2PC + 20) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → code a = some i)
    (hc5 : ∀ a i, CodeReq.singleton (status2PC + 24) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → code a = some i) :
    cpsTripleWithin (1 + 6) status2PC (saved.ra &&& ~~~(1 : Word)) code
      (((.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** savedFrame newSp saved) ** Fr)
      (((.x10 ↦ᵣ (2 : Word)) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
        (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) **
        savedFrame newSp saved) ** Fr) := by
  have hli := li_spec_gen_within .x10 a0old (2 : Word) status2PC (by decide)
  have hliE := cpsTripleWithin_extend_code hcli hli
  have hliF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ v18) ** savedFrame newSp saved) ** Fr) (by
      repeat' first
        | exact hFr | unfold savedFrame | exact pcFree_regIs | exact pcFree_memIs
        | apply pcFree_sepConj) hliE
  have hep := hfEpilogue (status2PC + 4) newSp (2 : Word) v1 v8 v9 v18 saved Fr hFr
    hc0
    (fun a i h => hc1 a i (by rw [show (status2PC + 4 + 4 : Word) = status2PC + 8 from by bv_omega] at h; exact h))
    (fun a i h => hc2 a i (by rw [show (status2PC + 4 + 8 : Word) = status2PC + 12 from by bv_omega] at h; exact h))
    (fun a i h => hc3 a i (by rw [show (status2PC + 4 + 12 : Word) = status2PC + 16 from by bv_omega] at h; exact h))
    (fun a i h => hc4 a i (by rw [show (status2PC + 4 + 16 : Word) = status2PC + 20 from by bv_omega] at h; exact h))
    (fun a i h => hc5 a i (by rw [show (status2PC + 4 + 20 : Word) = status2PC + 24 from by bv_omega] at h; exact h))
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hliF hep
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s1

/-! ## Generic status-0 (success) finish tail

    `li a0, 0` at `finishPC`, `jal x0, +16` → the epilogue at `finishPC + 20`
    (the `+16` offset from the JAL PC `finishPC + 4` skips the status-1/2 code). -/
set_option maxRecDepth 8000 in
theorem hfSuccessFinish {code : CodeReq} (finishPC newSp a0old v1 v8 v9 v18 : Word) (saved : Saved)
    (Fr : Assertion) (hFr : Fr.pcFree)
    (hcli : ∀ a i, CodeReq.singleton finishPC (.LI .x10 (0 : Word)) a = some i → code a = some i)
    (hcj : ∀ a i, CodeReq.singleton (finishPC + 4) (.JAL .x0 (16 : BitVec 21)) a = some i → code a = some i)
    (hc0 : ∀ a i, CodeReq.singleton (finishPC + 20) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → code a = some i)
    (hc1 : ∀ a i, CodeReq.singleton (finishPC + 24) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → code a = some i)
    (hc2 : ∀ a i, CodeReq.singleton (finishPC + 28) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → code a = some i)
    (hc3 : ∀ a i, CodeReq.singleton (finishPC + 32) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → code a = some i)
    (hc4 : ∀ a i, CodeReq.singleton (finishPC + 36) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → code a = some i)
    (hc5 : ∀ a i, CodeReq.singleton (finishPC + 40) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → code a = some i) :
    cpsTripleWithin (2 + 6) finishPC (saved.ra &&& ~~~(1 : Word)) code
      (((.x10 ↦ᵣ a0old) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** savedFrame newSp saved) ** Fr)
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (newSp + 48)) ** (.x1 ↦ᵣ saved.ra) **
        (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) **
        savedFrame newSp saved) ** Fr) := by
  have hli := li_spec_gen_within .x10 a0old (0 : Word) finishPC (by decide)
  have hliE := cpsTripleWithin_extend_code hcli hli
  have hliF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ v18) ** savedFrame newSp saved) ** Fr) (by
      repeat' first
        | exact hFr | unfold savedFrame | exact pcFree_regIs | exact pcFree_memIs
        | apply pcFree_sepConj) hliE
  have hj := jal_x0_spec_gen_within (16 : BitVec 21) (finishPC + 4)
  rw [show finishPC + 4 + signExtend21 (16 : BitVec 21) = finishPC + 20 from by
      rw [show signExtend21 (16 : BitVec 21) = (16 : Word) from by decide]; bv_omega] at hj
  have hjE := cpsTripleWithin_extend_code hcj hj
  have hjF := cpsTripleWithin_frameR
    (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** savedFrame newSp saved) ** Fr) (by
      repeat' first
        | exact hFr | unfold savedFrame | exact pcFree_regIs | exact pcFree_memIs
        | apply pcFree_sepConj) hjE
  rw [sepConj_emp_left'] at hjF
  have hep := hfEpilogue (finishPC + 20) newSp (0 : Word) v1 v8 v9 v18 saved Fr hFr
    hc0
    (fun a i h => hc1 a i (by rw [show (finishPC + 20 + 4 : Word) = finishPC + 24 from by bv_omega] at h; exact h))
    (fun a i h => hc2 a i (by rw [show (finishPC + 20 + 8 : Word) = finishPC + 28 from by bv_omega] at h; exact h))
    (fun a i h => hc3 a i (by rw [show (finishPC + 20 + 12 : Word) = finishPC + 32 from by bv_omega] at h; exact h))
    (fun a i h => hc4 a i (by rw [show (finishPC + 20 + 16 : Word) = finishPC + 36 from by bv_omega] at h; exact h))
    (fun a i h => hc5 a i (by rw [show (finishPC + 20 + 20 : Word) = finishPC + 40 from by bv_omega] at h; exact h))
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hliF hjF
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hep
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s2)

/-! ## Generic inter-call marshalling `SD x10; LD x10; LD x11` -/

theorem hfMarshalNext {code : CodeReq} (entryPC newcursor endPtr newSp v11 g1 : Word)
    (hc0 : ∀ a i, CodeReq.singleton entryPC (.SD .x2 .x10 (32 : BitVec 12)) a = some i → code a = some i)
    (hc1 : ∀ a i, CodeReq.singleton (entryPC + 4) (.LD .x10 .x2 (32 : BitVec 12)) a = some i → code a = some i)
    (hc2 : ∀ a i, CodeReq.singleton (entryPC + 8) (.LD .x11 .x2 (40 : BitVec 12)) a = some i → code a = some i) :
    cpsTripleWithin 3 entryPC (entryPC + 12) code
      ((.x10 ↦ᵣ newcursor) ** (.x11 ↦ᵣ v11) ** (.x2 ↦ᵣ newSp) **
       ((newSp + 32) ↦ₘ g1) ** ((newSp + 40) ↦ₘ endPtr))
      ((.x10 ↦ᵣ newcursor) ** (.x11 ↦ᵣ endPtr) ** (.x2 ↦ᵣ newSp) **
       ((newSp + 32) ↦ₘ newcursor) ** ((newSp + 40) ↦ₘ endPtr)) := by
  have h0 := sd_spec_gen_within .x2 .x10 newSp newcursor g1 (32 : BitVec 12) entryPC
  rw [show newSp + signExtend12 (32 : BitVec 12) = newSp + 32 from by
        rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]] at h0
  have e0 := cpsTripleWithin_extend_code hc0 h0
  have f0 := cpsTripleWithin_frameR ((.x11 ↦ᵣ v11) ** ((newSp + 40) ↦ₘ endPtr)) (by pcFreeR) e0
  have h1 := ld_spec_gen_within .x10 .x2 newSp newcursor newcursor (32 : BitVec 12) (entryPC + 4) (by decide)
  rw [show newSp + signExtend12 (32 : BitVec 12) = newSp + 32 from by
        rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide],
      show (entryPC + 4 : Word) + 4 = entryPC + 8 from by bv_omega] at h1
  have e1 := cpsTripleWithin_extend_code hc1 h1
  have f1 := cpsTripleWithin_frameR ((.x11 ↦ᵣ v11) ** ((newSp + 40) ↦ₘ endPtr)) (by pcFreeR) e1
  have h2 := ld_spec_gen_within .x11 .x2 newSp v11 endPtr (40 : BitVec 12) (entryPC + 8) (by decide)
  rw [show newSp + signExtend12 (40 : BitVec 12) = newSp + 40 from by
        rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide],
      show (entryPC + 8 : Word) + 4 = entryPC + 12 from by bv_omega] at h2
  have e2 := cpsTripleWithin_extend_code hc2 h2
  have f2 := cpsTripleWithin_frameR ((.x10 ↦ᵣ newcursor) ** ((newSp + 32) ↦ₘ newcursor)) (by pcFreeR) e2
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f0 f1
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f2
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s2

/-- Bundled-entry wrapper for the inter-call marshalling. -/
theorem hfMarshalNextBundled {code : CodeReq}
    (offAddr lenAddr entryPC next endPtr newSp listBase v9 outPtr g1 : Word)
    (saved : Saved) (outBytes : List (BitVec 8)) (Fr : Assertion) (hFr : Fr.pcFree)
    (hc0 : ∀ a i, CodeReq.singleton entryPC (.SD .x2 .x10 (32 : BitVec 12)) a = some i → code a = some i)
    (hc1 : ∀ a i, CodeReq.singleton (entryPC + 4) (.LD .x10 .x2 (32 : BitVec 12)) a = some i → code a = some i)
    (hc2 : ∀ a i, CodeReq.singleton (entryPC + 8) (.LD .x11 .x2 (40 : BitVec 12)) a = some i → code a = some i) :
    cpsTripleWithin 3 entryPC (entryPC + 12) code
      (((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word))) **
        (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes **
         hesrSpill newSp g1 endPtr ** Fr))
      (((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr)) **
        (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes **
         hesrSpill newSp next endPtr ** Fr)) := by
  have hm := hfMarshalNext entryPC next endPtr newSp (0 : Word) g1 hc0 hc1 hc2
  have hmF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ outPtr) ** savedFrame newSp saved **
     hfAmbConst offAddr lenAddr outPtr outBytes ** Fr)
    (by
      repeat' first
        | exact hFr | exact pcFree_hfAmbConst _ _ _ _ | unfold savedFrame
        | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hm
  refine cpsTripleWithin_weaken
    (fun h hp => by unfold hfWalkAmbient hesrAmbRegs hesrSpill at hp; xperm_chunked hp)
    (fun h hq => by unfold hfWalkAmbient hesrAmbRegs hesrSpill; xperm_chunked hq) hmF

#print axioms hfEpilogue
#print axioms hfStatus1Bundled
#print axioms hfStatus2Return
#print axioms hfSuccessFinish
#print axioms hfMarshalNextBundled

end EvmAsm.Codegen.HeaderFieldsSpec
