/-
  Pre-zero outputs after extract prologue (instr 14-17 at E+56):
    sd zero, 0(s2); sd zero, 8(s2); sw zero, 16(s2); sd zero, 0(s3)
  Leaves PC at E+72 (type_dispatch setup).
-/

import EvmAsm.Codegen.Programs.TxExtractToAddressPrologue
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.TxIntrinsicStateGasSpec (extractToBufOwn)

private theorem add0 (w : Word) : w + (0 : Word) = w := by bv_omega

/-- After pre-zero: first two toBuf dwords zero; third dword owned; isCreation=0. -/
def preZeroPost (toBuf isCreationPtr : Word) : Assertion :=
  (toBuf ↦ₘ (0 : Word)) ** ((toBuf + 8) ↦ₘ (0 : Word)) **
  memOwn (toBuf + 16) **
  (isCreationPtr ↦ₘ (0 : Word))

set_option maxRecDepth 8000 in
/-- Core with concrete third-dword value (for of_forall peel). -/
theorem extractPreZero_core
    (toBuf isCreationPtr old16 : Word)
    (halign : toBuf.toNat % 8 = 0)
    (hover : toBuf.toNat + 16 < 2 ^ 64)
    (hvalid16 : isValidMemAccess (toBuf + (16 : Word)) = true) :
    cpsTripleWithin 4 (E + 56) (E + 72) extractCode
      ((.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn toBuf ** memOwn (toBuf + 8) ** ((toBuf + 16) ↦ₘ old16) **
        memOwn isCreationPtr)
      ((.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) ** (.x0 ↦ᵣ (0 : Word)) **
        preZeroPost toBuf isCreationPtr) := by
  have hSD0 := sd_spec_gen_own_within .x18 .x0 toBuf (0 : Word) (0 : BitVec 12) (E + 56)
  have hSD1 := sd_spec_gen_own_within .x18 .x0 toBuf (0 : Word) (8 : BitVec 12) (E + 60)
  have hSD3 := sd_spec_gen_own_within .x19 .x0 isCreationPtr (0 : Word) (0 : BitVec 12) (E + 68)
  simp only [signExtend12_0, signExtend12_8, add0] at hSD0 hSD1 hSD3
  have e0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E (E + 56) extractProg 14
      (.SD .x18 .x0 (0 : BitVec 12)) (by bv_omega) (by rw [extract_length]; decide) rfl
      (by rw [extract_length]; decide)) hSD0
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E (E + 60) extractProg 15
      (.SD .x18 .x0 (8 : BitVec 12)) (by bv_omega) (by rw [extract_length]; decide) rfl
      (by rw [extract_length]; decide)) hSD1
  have e3 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E (E + 68) extractProg 17
      (.SD .x19 .x0 (0 : BitVec 12)) (by bv_omega) (by rw [extract_length]; decide) rfl
      (by rw [extract_length]; decide)) hSD3
  have hdw : alignToDword (toBuf + signExtend12 (16 : BitVec 12)) = toBuf + 16 := by
    simp only [signExtend12_16]
    have h := alignToDword_add_ofNat_of_aligned (base := toBuf) (i := 16) halign hover
    simpa using h
  have hsw0 :=
    sw_spec_gen_within .x18 .x0 toBuf (0 : Word) (16 : BitVec 12) (E + 64)
      (toBuf + 16) old16 hdw (by simpa [signExtend12_16] using hvalid16)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E (E + 64) extractProg 16
      (.SW .x18 .x0 (16 : BitVec 12)) (by bv_omega) (by rw [extract_length]; decide) rfl
      (by rw [extract_length]; decide)) hsw0
  simp only [signExtend12_16] at e2
  -- Frame each leaf
  have e0F := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ isCreationPtr) ** memOwn (toBuf + 8) ** ((toBuf + 16) ↦ₘ old16) **
      memOwn isCreationPtr)
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact pcFree_memOwn) e0
  have e1F := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ isCreationPtr) ** (toBuf ↦ₘ (0 : Word)) ** ((toBuf + 16) ↦ₘ old16) **
      memOwn isCreationPtr)
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact pcFree_memOwn) e1
  have e2F := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ isCreationPtr) ** (toBuf ↦ₘ (0 : Word)) ** ((toBuf + 8) ↦ₘ (0 : Word)) **
      memOwn isCreationPtr)
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact pcFree_memOwn) e2
  -- e3 already owns x0; do not re-frame x0 (would duplicate the atom).
  have e3F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ toBuf) **
      (toBuf ↦ₘ (0 : Word)) ** ((toBuf + 8) ↦ₘ (0 : Word)) **
      ((toBuf + 16) ↦ₘ replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
        ((0 : Word).truncate 32)))
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e3
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e0F e1F
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 e2F
  have h0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h012 e3F
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun s hq => by
    -- Reassoc so third-dword memIs is rightmost of a binary **; convert to memOwn.
    have hq1 :
        (((.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) ** (.x0 ↦ᵣ (0 : Word)) **
            (toBuf ↦ₘ (0 : Word)) ** ((toBuf + 8) ↦ₘ (0 : Word)) **
            (isCreationPtr ↦ₘ (0 : Word))) **
          ((toBuf + 16) ↦ₘ replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
            ((0 : Word).truncate 32))) s := by
      xperm_hyp hq
    have hq2 :
        (((.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) ** (.x0 ↦ᵣ (0 : Word)) **
            (toBuf ↦ₘ (0 : Word)) ** ((toBuf + 8) ↦ₘ (0 : Word)) **
            (isCreationPtr ↦ₘ (0 : Word))) **
          memOwn (toBuf + 16)) s :=
      (sepConj_mono (fun _ x => x) memIs_implies_memOwn) s hq1
    have hq3 :
        ((.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) ** (.x0 ↦ᵣ (0 : Word)) **
          (toBuf ↦ₘ (0 : Word)) ** ((toBuf + 8) ↦ₘ (0 : Word)) **
          memOwn (toBuf + 16) ** (isCreationPtr ↦ₘ (0 : Word))) s := by
      xperm_hyp hq2
    simpa only [preZeroPost] using hq3) h0123

set_option maxRecDepth 8000 in
/-- Top-level: peel third dword via of_forall. -/
theorem extractPreZero
    (toBuf isCreationPtr : Word)
    (halign : toBuf.toNat % 8 = 0)
    (hover : toBuf.toNat + 16 < 2 ^ 64)
    (hvalid16 : isValidMemAccess (toBuf + (16 : Word)) = true) :
    cpsTripleWithin 4 (E + 56) (E + 72) extractCode
      ((.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x0 ↦ᵣ (0 : Word)) ** extractToBufOwn toBuf ** memOwn isCreationPtr)
      ((.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x0 ↦ᵣ (0 : Word)) ** preZeroPost toBuf isCreationPtr) := by
  -- Reassoc so (toBuf+16) is rightmost of a binary ** for of_forall
  have hgo :
      cpsTripleWithin 4 (E + 56) (E + 72) extractCode
        (((.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) ** (.x0 ↦ᵣ (0 : Word)) **
            memOwn toBuf ** memOwn (toBuf + 8) ** memOwn isCreationPtr) **
          memOwn (toBuf + 16))
        ((.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
          (.x0 ↦ᵣ (0 : Word)) ** preZeroPost toBuf isCreationPtr) := by
    apply cpsTripleWithin_of_forall_memIs_to_memOwn (a := toBuf + 16)
    intro old16
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (extractPreZero_core toBuf isCreationPtr old16 halign hover hvalid16)
  exact cpsTripleWithin_weaken (fun _ hp => by
    unfold extractToBufOwn at hp
    xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hgo

#print axioms extractPreZero_core
#print axioms extractPreZero

end EvmAsm.Codegen.TxExtractToAddressSpec
