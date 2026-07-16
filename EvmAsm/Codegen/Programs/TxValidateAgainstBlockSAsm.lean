/-
  EvmAsm.Codegen.Programs.TxValidateAgainstBlockSAsm

  Byte-identical SAsm/CPS proof for `tx_validate_against_block`.

  The emitted helper is a cascade of three guards with four shared return
  tails:

    chain mismatch -> 1
    gas over limit -> 2
    nonce mismatch -> 3
    otherwise      -> 0

  The branch targets are forward return tails, so this is proved at the
  `RetForwardJoin` level rather than by duplicating tails in `Stmt.retIf`.
-/

import EvmAsm.Rv64.SAsm.RetForwardJoin
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace TxValidateAgainstBlockSAsm

abbrev txvabCode (base : Word) : CodeReq :=
  CodeReq.ofProg base txValidateAgainstBlock_prog

def txValidateAgainstBlockResult
    (txChain blockChain txGas blockGas txNonce accountNonce : Word) : Word :=
  if txChain ≠ blockChain then 1
  else if BitVec.ult blockGas txGas then 2
  else if txNonce ≠ accountNonce then 3
  else 0

theorem txValidateAgainstBlock_byte_tie :
    txValidateAgainstBlockFunction
      = "tx_validate_against_block:\n" ++ emitProgram txValidateAgainstBlock_prog := rfl

#guard txValidateAgainstBlock_prog.length = 11

theorem txvabJoin_spec
    (base ret txChain blockChain txGas blockGas txNonce accountNonce : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 5 base ret (txvabCode base)
      ((.x10 ↦ᵣ txChain) ** (.x11 ↦ᵣ blockChain) ** (.x12 ↦ᵣ txGas) **
        (.x13 ↦ᵣ blockGas) ** (.x14 ↦ᵣ txNonce) ** (.x15 ↦ᵣ accountNonce) **
        (.x0 ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret))
      ((.x10 ↦ᵣ txValidateAgainstBlockResult txChain blockChain txGas blockGas
          txNonce accountNonce) **
        (.x11 ↦ᵣ blockChain) ** (.x12 ↦ᵣ txGas) ** (.x13 ↦ᵣ blockGas) **
        (.x14 ↦ᵣ txNonce) ** (.x15 ↦ᵣ accountNonce) **
        (.x0 ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret)) := by
  set Ptail : Assertion :=
    ((.x11 ↦ᵣ blockChain) ** (.x12 ↦ᵣ txGas) ** (.x13 ↦ᵣ blockGas) **
      (.x14 ↦ᵣ txNonce) ** (.x15 ↦ᵣ accountNonce) ** (.x0 ↦ᵣ (0 : Word)))
    with hPtail
  have hPtailF : Ptail.pcFree := by rw [hPtail]; pcf
  have htail0 := sharedRetTail_spec (txvabCode base) (base + 12) ret .x10
    (0 : Word) txChain Ptail hPtailF (by decide) halign
    (CodeReq.ofProg_mono_sub base (base + 12) txValidateAgainstBlock_prog
      [.LI .x10 (0 : Word)] 3 (by bv_omega) (by decide) (by decide) (by decide))
    (CodeReq.ofProg_mono_sub base (base + 12 + 4) txValidateAgainstBlock_prog
      [.JALR .x0 .x1 0] 4 (by bv_omega) (by decide) (by decide) (by decide))
  have htail1 := sharedRetTail_spec (txvabCode base) (base + 20) ret .x10
    (1 : Word) txChain Ptail hPtailF (by decide) halign
    (CodeReq.ofProg_mono_sub base (base + 20) txValidateAgainstBlock_prog
      [.LI .x10 (1 : Word)] 5 (by bv_omega) (by decide) (by decide) (by decide))
    (CodeReq.ofProg_mono_sub base (base + 20 + 4) txValidateAgainstBlock_prog
      [.JALR .x0 .x1 0] 6 (by bv_omega) (by decide) (by decide) (by decide))
  have htail2 := sharedRetTail_spec (txvabCode base) (base + 28) ret .x10
    (2 : Word) txChain Ptail hPtailF (by decide) halign
    (CodeReq.ofProg_mono_sub base (base + 28) txValidateAgainstBlock_prog
      [.LI .x10 (2 : Word)] 7 (by bv_omega) (by decide) (by decide) (by decide))
    (CodeReq.ofProg_mono_sub base (base + 28 + 4) txValidateAgainstBlock_prog
      [.JALR .x0 .x1 0] 8 (by bv_omega) (by decide) (by decide) (by decide))
  have htail3 := sharedRetTail_spec (txvabCode base) (base + 36) ret .x10
    (3 : Word) txChain Ptail hPtailF (by decide) halign
    (CodeReq.ofProg_mono_sub base (base + 36) txValidateAgainstBlock_prog
      [.LI .x10 (3 : Word)] 9 (by bv_omega) (by decide) (by decide) (by decide))
    (CodeReq.ofProg_mono_sub base (base + 36 + 4) txValidateAgainstBlock_prog
      [.JALR .x0 .x1 0] 10 (by bv_omega) (by decide) (by decide) (by decide))

  have hbr3 := cpsBranchWithin_frameR
    ((.x10 ↦ᵣ txChain) ** (.x11 ↦ᵣ blockChain) ** (.x12 ↦ᵣ txGas) **
      (.x13 ↦ᵣ blockGas) ** (.x0 ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret))
    (by pcf)
    (cpsBranchWithin_extend_code
      (h := bne_spec_gen_within .x14 .x15 (28 : BitVec 13) txNonce accountNonce (base + 8))
      (hmono := CodeReq.ofProg_mono_sub base (base + 8) txValidateAgainstBlock_prog
        [.BNE .x14 .x15 (28 : BitVec 13)] 2 (by bv_omega) (by decide) (by decide) (by decide)))
  rw [show (base + 8 : Word) + signExtend13 (28 : BitVec 13) = base + 36 from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega,
      show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at hbr3
  have hstation3 : cpsTripleWithin 3 (base + 8) ret (txvabCode base)
      ((.x14 ↦ᵣ txNonce) ** (.x15 ↦ᵣ accountNonce) ** (.x10 ↦ᵣ txChain) **
        (.x11 ↦ᵣ blockChain) ** (.x12 ↦ᵣ txGas) ** (.x13 ↦ᵣ blockGas) **
        (.x0 ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret))
      ((.x10 ↦ᵣ (if txNonce ≠ accountNonce then (3 : Word) else (0 : Word))) **
        ((.x1 : Reg) ↦ᵣ ret) ** Ptail) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
      (retJoinStation_spec
        (PT := (.x10 ↦ᵣ txChain) ** ((.x1 : Reg) ↦ᵣ ret) ** Ptail)
        (PF := (.x10 ↦ᵣ txChain) ** ((.x1 : Reg) ↦ᵣ ret) ** Ptail)
        hbr3
        (fun h hq => by rw [hPtail]; xperm_hyp hq)
        (fun h hq => by
          rw [show (¬txNonce ≠ accountNonce) = (txNonce = accountNonce) from propext not_ne_iff, hPtail]
          xperm_hyp hq)
        (fun hc => cpsTripleWithin_weaken
          (fun h hp => by rw [hPtail]; xperm_hyp hp)
          (fun h hq => by rw [if_pos hc, hPtail]; xperm_hyp hq)
          htail3)
        (fun hc => cpsTripleWithin_weaken
          (fun h hp => by rw [hPtail]; xperm_hyp hp)
          (fun h hq => by rw [if_neg hc, hPtail]; xperm_hyp hq)
          htail0))

  have hbr2 := cpsBranchWithin_frameR
    ((.x10 ↦ᵣ txChain) ** (.x11 ↦ᵣ blockChain) ** (.x14 ↦ᵣ txNonce) **
      (.x15 ↦ᵣ accountNonce) ** (.x0 ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret))
    (by pcf)
    (cpsBranchWithin_extend_code
      (h := bltu_spec_gen_within .x13 .x12 (24 : BitVec 13) blockGas txGas (base + 4))
      (hmono := CodeReq.ofProg_mono_sub base (base + 4) txValidateAgainstBlock_prog
        [.BLTU .x13 .x12 (24 : BitVec 13)] 1 (by bv_omega) (by decide) (by decide) (by decide)))
  rw [show (base + 4 : Word) + signExtend13 (24 : BitVec 13) = base + 28 from by
        rw [show signExtend13 (24 : BitVec 13) = (24 : Word) from by decide]; bv_omega,
      show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hbr2
  have hstation2 : cpsTripleWithin 4 (base + 4) ret (txvabCode base)
      ((.x13 ↦ᵣ blockGas) ** (.x12 ↦ᵣ txGas) ** (.x10 ↦ᵣ txChain) **
        (.x11 ↦ᵣ blockChain) ** (.x14 ↦ᵣ txNonce) ** (.x15 ↦ᵣ accountNonce) **
        (.x0 ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret))
      ((.x10 ↦ᵣ (if BitVec.ult blockGas txGas then (2 : Word)
                 else if txNonce ≠ accountNonce then (3 : Word) else (0 : Word))) **
        ((.x1 : Reg) ↦ᵣ ret) ** Ptail) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
      (retJoinStation_spec
        (PT := (.x10 ↦ᵣ txChain) ** ((.x1 : Reg) ↦ᵣ ret) ** Ptail)
        (PF := (.x13 ↦ᵣ blockGas) ** (.x12 ↦ᵣ txGas) ** (.x10 ↦ᵣ txChain) **
          (.x11 ↦ᵣ blockChain) ** (.x14 ↦ᵣ txNonce) ** (.x15 ↦ᵣ accountNonce) **
          (.x0 ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret))
        hbr2
        (fun h hq => by rw [hPtail]; xperm_hyp hq)
        (fun h hq => by xperm_hyp hq)
        (fun hc => cpsTripleWithin_mono_nSteps (by omega)
          (cpsTripleWithin_weaken
            (fun h hp => by rw [hPtail]; xperm_hyp hp)
            (fun h hq => by rw [if_pos hc, hPtail]; xperm_hyp hq)
            htail2))
        (fun hc => cpsTripleWithin_weaken
          (fun h hp => by xperm_hyp hp)
          (fun h hq => by rw [if_neg hc]; exact hq)
          hstation3))

  have hbr1 := cpsBranchWithin_frameR
    ((.x12 ↦ᵣ txGas) ** (.x13 ↦ᵣ blockGas) ** (.x14 ↦ᵣ txNonce) **
      (.x15 ↦ᵣ accountNonce) ** (.x0 ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret))
    (by pcf)
    (cpsBranchWithin_extend_code
      (h := bne_spec_gen_within .x10 .x11 (20 : BitVec 13) txChain blockChain base)
      (hmono := CodeReq.ofProg_mono_sub base base txValidateAgainstBlock_prog
        [.BNE .x10 .x11 (20 : BitVec 13)] 0 (by bv_omega) (by decide) (by decide) (by decide)))
  rw [show signExtend13 (20 : BitVec 13) = (20 : Word) from by decide] at hbr1
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => ?_)
    (retJoinStation_spec
      (PT := (.x10 ↦ᵣ txChain) ** ((.x1 : Reg) ↦ᵣ ret) ** Ptail)
      (PF := (.x10 ↦ᵣ txChain) ** (.x11 ↦ᵣ blockChain) ** (.x12 ↦ᵣ txGas) **
        (.x13 ↦ᵣ blockGas) ** (.x14 ↦ᵣ txNonce) ** (.x15 ↦ᵣ accountNonce) **
        (.x0 ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret))
      (Q := ((.x10 ↦ᵣ txValidateAgainstBlockResult txChain blockChain txGas blockGas
          txNonce accountNonce) **
        (.x11 ↦ᵣ blockChain) ** (.x12 ↦ᵣ txGas) ** (.x13 ↦ᵣ blockGas) **
        (.x14 ↦ᵣ txNonce) ** (.x15 ↦ᵣ accountNonce) **
        (.x0 ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret)))
      hbr1
      (fun h hq => by rw [hPtail]; xperm_hyp hq)
      (fun h hq => by
        rw [show (¬txChain ≠ blockChain) = (txChain = blockChain) from propext not_ne_iff]
        xperm_hyp hq)
      (fun hc => cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken
          (fun h hp => by rw [hPtail]; xperm_hyp hp)
          (fun h hq => by
            have hres : txValidateAgainstBlockResult txChain blockChain txGas blockGas
                txNonce accountNonce = (1 : Word) := by
              simp [txValidateAgainstBlockResult, hc]
            rw [hres]
            rw [hPtail] at hq
            xperm_hyp hq)
          htail1))
      (fun hc => cpsTripleWithin_weaken
        (fun h hp => by xperm_hyp hp)
        (fun h hq => by
          have hres : txValidateAgainstBlockResult txChain blockChain txGas blockGas
                txNonce accountNonce =
              (if BitVec.ult blockGas txGas then (2 : Word)
               else if txNonce ≠ accountNonce then (3 : Word) else (0 : Word)) := by
            simp [txValidateAgainstBlockResult, hc]
          rw [hres]
          rw [hPtail] at hq
          xperm_hyp hq)
        hstation2))
  exact hq


end TxValidateAgainstBlockSAsm

end EvmAsm.Codegen
