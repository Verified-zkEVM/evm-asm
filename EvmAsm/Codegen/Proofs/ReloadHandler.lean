/-
  EvmAsm.Codegen.Proofs.ReloadHandler

  Handler-level lift infrastructure for EVM opcode bodies that CLOBBER the
  dispatcher's EVM code pointer `x10` (Multiply, SignExtend, Byte, AddMod,
  SDiv, SMod, Push). Unlike the `cleanRetHandler` (which advances the
  surviving `x10`), these bodies need `x10` saved before the body and reloaded
  from the saved register after, before the advance-and-return tail.

  This file provides the foundational, kernel-checked pieces; the full
  `reloadRetHandlerSpec` lift (composing the five pieces below, mirroring
  `cleanRetHandlerSpec` in HandlerSpecs.lean) is the remaining step — see the
  module note at the bottom.
-/

import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64 (cc_ret)

/-- `4 * nSteps` as a 64-bit code-offset Word (local mirror of the private
    `fourTimes` in HandlerSpecs; the two never collide — both are file-private). -/
private def fourTimes (nSteps : Nat) : Word := BitVec.ofNat 64 (4 * nSteps)

/-- The save/reload handler ABI: save the EVM code pointer `x10` into `save`,
    run the (x10-clobbering) `body`, reload `x10` from `save`, advance by `n`
    bytes, and return via `cc_ret`. The dual of `cleanRetHandlerProgram` for
    x10-clobbering bodies. -/
def saveReloadHandlerProgram (body : Program) (n : BitVec 12) (save : Reg) : Program :=
  MV save .x10 ;; body ;; MV .x10 save ;; (Rv64.ADDI .x10 .x10 n) ;; cc_ret

theorem saveReloadHandlerProgram_length (body : Program) (n : BitVec 12) (save : Reg) :
    (saveReloadHandlerProgram body n save).length = body.length + 4 := by
  simp only [saveReloadHandlerProgram, seq, MV, Rv64.ADDI, cc_ret, JALR, single,
    Program.length_append, List.length_cons, List.length_nil]
  omega

/-- `MV rd rs` consuming a *don't-care* (owned) destination value — the novel
    step in the reload tail: the reloaded `x10` discards the body's garbage
    value. Built directly from `mv_spec_within` via the regOwn-elimination
    rule `cpsTripleWithin_of_forall_regIs_to_regOwn`. This is the piece that
    resolves the `regOwn .x10` in an x10-clobbering body's postcondition
    (e.g. `evmMulStackPost`). -/
theorem mv_dst_regOwn_spec_within (rd rs : Reg) (v : Word) (addr : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.MV rd rs))
      ((rs ↦ᵣ v) ** regOwn rd)
      ((rs ↦ᵣ v) ** (rd ↦ᵣ v)) :=
  cpsTripleWithin_of_forall_regIs_to_regOwn
    (fun vOld => mv_spec_within rd rs v vOld addr hrd_ne_x0)

/-- Handler-level lift for an x10-clobbering EVM opcode body. Given a body
    spec whose precondition owns the EVM code pointer `x10` (at value
    `x10_init`, separated as `(.x10 ↦ᵣ x10_init) ** R`) and whose
    postcondition merely *owns* `x10` (`regOwn .x10 ** S`, i.e. the body left
    garbage in it), the `saveReloadHandlerProgram` wrapper produces a full
    handler spec: it saves `x10` into `save`, runs the body, reloads `x10`,
    advances the EVM code pointer by `n`, and returns. The dual of
    `cleanRetHandlerSpec` for the 7 x10-clobbering opcodes
    (Multiply/SignExtend/Byte/AddMod/SDiv/SMod/Push). Five sub-blocks composed
    via `cpsTripleWithin_seq`; the `regOwn .x10` in the body's post is consumed
    by `mv_dst_regOwn_spec_within`. -/
theorem reloadRetHandlerSpec
    {nSteps : Nat} {base : Word} {body : List Instr} {R S : Assertion} {n : BitVec 12}
    {save : Reg} {x10_init : Word}
    (hRpcFree : R.pcFree) (hSpcFree : S.pcFree)
    (hsave_ne_x0 : save ≠ .x0)
    (hBodyLen : body.length = nSteps)
    (hBodyLenBound : nSteps < 2 ^ 60)
    (h_body : cpsTripleWithin nSteps (base + 4) ((base + 4) + fourTimes nSteps)
                (CodeReq.ofProg (base + 4) body)
                ((.x10 ↦ᵣ x10_init) ** R) (regOwn .x10 ** S))
    (s_init x1_init : Word) :
    cpsTripleWithin (nSteps + 4) base (x1_init &&& ~~~1)
      (CodeReq.ofProg base (saveReloadHandlerProgram body n save))
      ((save ↦ᵣ s_init) ** (.x10 ↦ᵣ x10_init) ** R ** (.x1 ↦ᵣ x1_init))
      ((save ↦ᵣ x10_init) ** (.x10 ↦ᵣ (x10_init + signExtend12 n)) ** S
        ** (.x1 ↦ᵣ x1_init)) := by
  have hNBound : (4 * nSteps : Nat) < 2 ^ 64 := by
    have : (2:Nat)^60 * 4 ≤ 2^64 := by decide
    omega
  -- pieces
  have p1 :
      cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.MV save .x10))
        ((save ↦ᵣ s_init) ** (.x10 ↦ᵣ x10_init) ** R ** (.x1 ↦ᵣ x1_init))
        ((save ↦ᵣ x10_init) ** (.x10 ↦ᵣ x10_init) ** R ** (.x1 ↦ᵣ x1_init)) := by
    have core := mv_spec_within save .x10 x10_init s_init base hsave_ne_x0
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR (R ** (.x1 ↦ᵣ x1_init)) (pcFree_sepConj hRpcFree pcFree_regIs) core)
  have p2 :
      cpsTripleWithin nSteps (base + 4) ((base + 4) + fourTimes nSteps)
        (CodeReq.ofProg (base + 4) body)
        ((save ↦ᵣ x10_init) ** (.x10 ↦ᵣ x10_init) ** R ** (.x1 ↦ᵣ x1_init))
        ((save ↦ᵣ x10_init) ** regOwn .x10 ** S ** (.x1 ↦ᵣ x1_init)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameL ((save ↦ᵣ x10_init)) pcFree_regIs
        (cpsTripleWithin_frameR ((.x1 ↦ᵣ x1_init)) pcFree_regIs h_body))
  have p3 :
      cpsTripleWithin 1 ((base + 4) + fourTimes nSteps) (((base + 4) + fourTimes nSteps) + 4)
        (CodeReq.singleton ((base + 4) + fourTimes nSteps) (.MV .x10 save))
        ((save ↦ᵣ x10_init) ** regOwn .x10 ** S ** (.x1 ↦ᵣ x1_init))
        ((save ↦ᵣ x10_init) ** (.x10 ↦ᵣ x10_init) ** S ** (.x1 ↦ᵣ x1_init)) := by
    have core := mv_dst_regOwn_spec_within .x10 save x10_init
      ((base + 4) + fourTimes nSteps) (by decide)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR (S ** (.x1 ↦ᵣ x1_init)) (pcFree_sepConj hSpcFree pcFree_regIs) core)
  have p4 :
      cpsTripleWithin 1 (((base + 4) + fourTimes nSteps) + 4) ((((base + 4) + fourTimes nSteps) + 4) + 4)
        (CodeReq.singleton (((base + 4) + fourTimes nSteps) + 4) (.ADDI .x10 .x10 n))
        ((save ↦ᵣ x10_init) ** (.x10 ↦ᵣ x10_init) ** S ** (.x1 ↦ᵣ x1_init))
        ((save ↦ᵣ x10_init) ** (.x10 ↦ᵣ (x10_init + signExtend12 n)) ** S ** (.x1 ↦ᵣ x1_init)) := by
    have core := addi_spec_same_within .x10 x10_init n (((base + 4) + fourTimes nSteps) + 4) (by decide)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameL ((save ↦ᵣ x10_init)) pcFree_regIs
        (cpsTripleWithin_frameR (S ** (.x1 ↦ᵣ x1_init)) (pcFree_sepConj hSpcFree pcFree_regIs) core))
  have p5 :
      cpsTripleWithin 1 ((((base + 4) + fourTimes nSteps) + 4) + 4) (x1_init &&& ~~~1)
        (CodeReq.singleton ((((base + 4) + fourTimes nSteps) + 4) + 4) (.JALR .x0 .x1 0))
        ((save ↦ᵣ x10_init) ** (.x10 ↦ᵣ (x10_init + signExtend12 n)) ** S ** (.x1 ↦ᵣ x1_init))
        ((save ↦ᵣ x10_init) ** (.x10 ↦ᵣ (x10_init + signExtend12 n)) ** S ** (.x1 ↦ᵣ x1_init)) := by
    have core := EvmAsm.Evm64.ret_spec_within' ((((base + 4) + fourTimes nSteps) + 4) + 4) x1_init
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameL ((save ↦ᵣ x10_init) ** (.x10 ↦ᵣ (x10_init + signExtend12 n)) ** S)
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hSpcFree)) core)
  -- disjointness helpers
  have hbody_none : ∀ (a : Word),
      (∀ k : Nat, k < nSteps → a ≠ (base + 4) + BitVec.ofNat 64 (4 * k)) →
      CodeReq.ofProg (base + 4) body a = none := by
    intro a ha
    apply CodeReq.ofProg_none_range
    intro k hk
    rw [hBodyLen] at hk
    exact ha k hk
  have d12 : (CodeReq.singleton base (.MV save .x10)).Disjoint
      (CodeReq.ofProg (base + 4) body) := by
    apply CodeReq.Disjoint.singleton_ofProg
    apply hbody_none; intro k hk heq
    have : (4 * k : Nat) < 2 ^ 64 := by omega
    bv_omega
  have d123 : ((CodeReq.singleton base (.MV save .x10)).union
      (CodeReq.ofProg (base + 4) body)).Disjoint
      (CodeReq.singleton ((base + 4) + fourTimes nSteps) (.MV .x10 save)) := by
    apply CodeReq.Disjoint.union_left
    · apply CodeReq.Disjoint.singleton; simp only [fourTimes]; bv_omega
    · apply CodeReq.Disjoint.ofProg_singleton
      apply hbody_none; intro k hk heq
      simp only [fourTimes] at heq
      have : (4 * k : Nat) < 2 ^ 64 := by omega
      bv_omega
  have d1234 : (((CodeReq.singleton base (.MV save .x10)).union
      (CodeReq.ofProg (base + 4) body)).union
      (CodeReq.singleton ((base + 4) + fourTimes nSteps) (.MV .x10 save))).Disjoint
      (CodeReq.singleton (((base + 4) + fourTimes nSteps) + 4) (.ADDI .x10 .x10 n)) := by
    apply CodeReq.Disjoint.union_left
    · apply CodeReq.Disjoint.union_left
      · apply CodeReq.Disjoint.singleton; simp only [fourTimes]; bv_omega
      · apply CodeReq.Disjoint.ofProg_singleton
        apply hbody_none; intro k hk heq
        simp only [fourTimes] at heq
        have : (4 * k : Nat) < 2 ^ 64 := by omega
        bv_omega
    · apply CodeReq.Disjoint.singleton; bv_omega
  have d12345 : ((((CodeReq.singleton base (.MV save .x10)).union
      (CodeReq.ofProg (base + 4) body)).union
      (CodeReq.singleton ((base + 4) + fourTimes nSteps) (.MV .x10 save))).union
      (CodeReq.singleton (((base + 4) + fourTimes nSteps) + 4) (.ADDI .x10 .x10 n))).Disjoint
      (CodeReq.singleton ((((base + 4) + fourTimes nSteps) + 4) + 4) (.JALR .x0 .x1 0)) := by
    apply CodeReq.Disjoint.union_left
    · apply CodeReq.Disjoint.union_left
      · apply CodeReq.Disjoint.union_left
        · apply CodeReq.Disjoint.singleton; simp only [fourTimes]; bv_omega
        · apply CodeReq.Disjoint.ofProg_singleton
          apply hbody_none; intro k hk heq
          simp only [fourTimes] at heq
          have : (4 * k : Nat) < 2 ^ 64 := by omega
          bv_omega
      · apply CodeReq.Disjoint.singleton; simp only [fourTimes]; bv_omega
    · apply CodeReq.Disjoint.singleton; bv_omega
  -- seq compose
  have s12 := cpsTripleWithin_seq d12 p1 p2
  have s123 := cpsTripleWithin_seq d123 s12 p3
  have s1234 := cpsTripleWithin_seq d1234 s123 p4
  have s12345 := cpsTripleWithin_seq d12345 s1234 p5
  -- align CodeReq
  have hCodeEq :
      ((((CodeReq.singleton base (.MV save .x10)).union
        (CodeReq.ofProg (base + 4) body)).union
        (CodeReq.singleton ((base + 4) + fourTimes nSteps) (.MV .x10 save))).union
        (CodeReq.singleton (((base + 4) + fourTimes nSteps) + 4) (.ADDI .x10 .x10 n))).union
        (CodeReq.singleton ((((base + 4) + fourTimes nSteps) + 4) + 4) (.JALR .x0 .x1 0))
      = CodeReq.ofProg base (saveReloadHandlerProgram body n save) := by
    change _ = CodeReq.ofProg base
      ([Instr.MV save .x10] ++ (body ++ ([Instr.MV .x10 save] ++
        ([Instr.ADDI .x10 .x10 n] ++ [Instr.JALR .x0 .x1 0]))))
    rw [CodeReq.ofProg_append, CodeReq.ofProg_append, CodeReq.ofProg_append,
      CodeReq.ofProg_append]
    simp only [CodeReq.ofProg_singleton, List.length_cons, List.length_nil,
      hBodyLen, fourTimes, ← CodeReq.union_assoc]
    repeat' congr 1
  rw [← hCodeEq, show nSteps + 4 = 1 + nSteps + 1 + 1 + 1 from by omega]
  exact s12345

end EvmAsm.Codegen.Proofs
