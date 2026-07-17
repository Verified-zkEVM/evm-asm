/-
  Extract body: type234 SUB content-ptr + JAL to HaveField join.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.GenericSpecs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkNextRest
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Codegen

local macro "pcf" : tactic => `(tactic|
  repeat first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_emp
    | exact pcFree_pure
    | exact bytesRegion_pcFree _ _)

/-- Join point: content end in a0, content len in a2; t6 = a0 - a2. -/
abbrev HaveField : Word := E + 484
abbrev Type234JalHavePc : Word := E + 296

set_option maxRecDepth 8000 in
/-- type234: `sub t6,a0,a2` AfterWalkNext5Bne → Type234JalHavePc. -/
theorem extractType234Sub (a0 a2 t6Old : Word) :
    cpsTripleWithin 1 AfterWalkNext5Bne Type234JalHavePc extractLinkedCode
      ((.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x31 ↦ᵣ t6Old))
      ((.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x31 ↦ᵣ (a0 - a2))) := by
  have hs := sub_spec_gen_within .x31 .x10 .x12 a0 a2 t6Old AfterWalkNext5Bne (by decide)
  have he := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E AfterWalkNext5Bne extractProg 73
        (.SUB .x31 .x10 .x12) (by simp only [AfterWalkNext5Bne]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hs
  simpa only [Type234JalHavePc, AfterWalkNext5Bne] using he

set_option maxRecDepth 8000 in
/-- type234: `j .Ltea_have_field` (JAL x0 188) → HaveField. -/
theorem extractType234JalHave :
    cpsTripleWithin 1 Type234JalHavePc HaveField extractLinkedCode
      empAssertion empAssertion := by
  have hj := jal_x0_spec_gen_within (188 : BitVec 21) Type234JalHavePc
  have ht : Type234JalHavePc + signExtend21 (188 : BitVec 21) = HaveField := by
    simp only [Type234JalHavePc, HaveField, E]
    rw [show signExtend21 (188 : BitVec 21) = (188 : Word) from by decide]
    bv_omega
  rw [ht] at hj
  exact cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E Type234JalHavePc extractProg 74
        (.JAL .x0 (188 : BitVec 21)) (by simp only [Type234JalHavePc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hj

set_option maxRecDepth 8000 in
/-- type234: SUB ;; JAL have_field. -/
theorem extractType234ToHaveField (a0 a2 t6Old : Word) :
    cpsTripleWithin (1 + 1) AfterWalkNext5Bne HaveField extractLinkedCode
      ((.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x31 ↦ᵣ t6Old))
      ((.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x31 ↦ᵣ (a0 - a2))) := by
  have hs := extractType234Sub a0 a2 t6Old
  have hj := extractType234JalHave
  have hjF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x31 ↦ᵣ (a0 - a2))) (by pcf) hj
  have hjF' : cpsTripleWithin 1 Type234JalHavePc HaveField extractLinkedCode
      ((.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x31 ↦ᵣ (a0 - a2)))
      ((.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x31 ↦ᵣ (a0 - a2))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simpa only [sepConj_emp_left'] using hp) (fun _ hq => by
      simpa only [sepConj_emp_left'] using hq) hjF
  exact cpsTripleWithin_seq_same_cr hs hjF'

#print axioms extractType234Sub
#print axioms extractType234JalHave
#print axioms extractType234ToHaveField

end EvmAsm.Codegen.TxExtractToAddressSpec
