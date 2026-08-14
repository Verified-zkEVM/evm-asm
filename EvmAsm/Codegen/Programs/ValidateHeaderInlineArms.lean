/-
  EvmAsm.Codegen.Programs.ValidateHeaderInlineArms

  Inline scalar-comparison arms of SpecRef-shaped `validate_header` (#12346):
  conjuncts 1, 3, 5, 6.  No callee triple — each reject arm is proved against
  the linked exit (relative to `H`), carrying DISTINCT statuses 1 / 3 / 5 / 6.

  Reuses `H` / `callerCode` / `validateHeader_length` from
  `ValidateHeaderCorrespondence` — do not invent a second entry contract.

  Absolute PCs move with the link; proofs use `H + offset` only.
-/

import EvmAsm.Codegen.Programs.ValidateHeaderCorrespondence
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen.ValidateHeaderInlineArms

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.ValidateHeaderCorrespondence

abbrev prog : Program := EvmAsm.Codegen.validateHeader_prog

theorem prog_length : prog.length = 97 := validateHeader_length

/-! ## Shared epilogue at `H + 352` (idx 88–96)

    Same 56-byte ABI-frame restore as `cvitEpilogue`. -/

set_option maxRecDepth 8000 in
theorem vhEpi
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 9 (H + 352) raIn callerCode
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
        ((spC + 48) ↦ₘ cs5))
      ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) **
        (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
        ((spC + 48) ↦ₘ cs5)) := by
  subst hspC
  have l0 := ld_spec_gen_within .x1 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o1 raIn
    (0 : BitVec 12) (H + 352) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (sp0 + signExtend12 (-56 : BitVec 12)) + (0 : Word)
      = sp0 + signExtend12 (-56 : BitVec 12) from by bv_omega] at l0
  have l1 := ld_spec_gen_within .x8 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o8 cs0
    (8 : BitVec 12) (H + 356) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at l1
  have l2 := ld_spec_gen_within .x9 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o9 cs1
    (16 : BitVec 12) (H + 360) (by decide)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at l2
  have l3 := ld_spec_gen_within .x18 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o18 cs2
    (24 : BitVec 12) (H + 364) (by decide)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at l3
  have l4 := ld_spec_gen_within .x19 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o19 cs3
    (32 : BitVec 12) (H + 368) (by decide)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at l4
  have l5 := ld_spec_gen_within .x20 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o20 cs4
    (40 : BitVec 12) (H + 372) (by decide)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide] at l5
  have l6 := ld_spec_gen_within .x21 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o21 cs5
    (48 : BitVec 12) (H + 376) (by decide)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide] at l6
  have l7 := addi_spec_gen_same_within .x2 (sp0 + signExtend12 (-56 : BitVec 12))
    (56 : BitVec 12) (H + 380) (by decide)
  rw [show (sp0 + signExtend12 (-56 : BitVec 12)) + signExtend12 (56 : BitVec 12) = sp0
      from by rw [show signExtend12 (-56 : BitVec 12) = (-56 : Word) from by decide,
        show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide]; bv_omega] at l7
  have hblock : cpsTripleWithin 8 (H + 352) (H + 384) callerCode
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-56 : BitVec 12))) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) **
        (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        (.x21 ↦ᵣ o21) **
        ((sp0 + signExtend12 (-56 : BitVec 12)) ↦ₘ raIn) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 8) ↦ₘ cs0) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 16) ↦ₘ cs1) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 24) ↦ₘ cs2) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 32) ↦ₘ cs3) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 40) ↦ₘ cs4) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 48) ↦ₘ cs5))
      ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) ** (.x2 ↦ᵣ sp0) **
        ((sp0 + signExtend12 (-56 : BitVec 12)) ↦ₘ raIn) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 8) ↦ₘ cs0) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 16) ↦ₘ cs1) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 24) ↦ₘ cs2) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 32) ↦ₘ cs3) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 40) ↦ₘ cs4) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 48) ↦ₘ cs5)) := by
    runBlock l0 l1 l2 l3 l4 l5 l6 l7
  have hjalr := EvmAsm.Evm64.ret_spec_within' (H + 384) raIn
  rw [hret] at hjalr
  have hjalrC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 384) prog 96 (.JALR .x0 .x1 (0 : BitVec 12))
      (by bv_omega) (by rw [prog_length]; decide) rfl (by rw [prog_length]; decide))
    hjalr
  have hjalrF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) **
      (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) ** (.x2 ↦ᵣ sp0) **
      ((sp0 + signExtend12 (-56 : BitVec 12)) ↦ₘ raIn) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 8) ↦ₘ cs0) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 16) ↦ₘ cs1) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 24) ↦ₘ cs2) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 32) ↦ₘ cs3) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 40) ↦ₘ cs4) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 48) ↦ₘ cs5)) (by pcf) hjalrC
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblock hjalrF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

end EvmAsm.Codegen.ValidateHeaderInlineArms
