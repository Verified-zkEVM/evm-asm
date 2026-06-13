/-
  EvmAsm.Codegen.Proofs.HandlerSpecs

  Phase 4 of the codegen-proofs roadmap: lift verified body specs from
  `Evm64/<Op>/Spec.lean` to **dispatcher-handler-level** specs that
  also account for the M5b dispatcher's wrapping (preBody + tail).

  This file delivers the **first** Phase 4 instance: a reusable template
  `cleanRetHandlerSpec` covering all handlers that use the standard
  `.advanceAndRet n` tail with an empty `preBody`, plus concrete
  instances for ADD (0x01) and POP (0x50).

  The template applies to ~70 of the 91 wired handlers today (every
  "clean-shape" entry: empty `preBody`, `tail := .advanceAndRet n`).
  Future PRs can add:
    * a `withX10SavePreBody` variant for MUL/SIGNEXTEND/BYTE/SHR;
    * a `signedDivModTail` variant for SDIV/SMOD;
    * a self-calling variant for ADDMOD;
    * parameterized templates for the PUSH/DUP/SWAP families.

  See `CODEGEN.md` for the full roadmap.
-/

import EvmAsm.Codegen.Programs
import EvmAsm.Evm64.Add.Spec
import EvmAsm.Evm64.Pop.Spec
import EvmAsm.Evm64.Sub.Spec
import EvmAsm.Evm64.Lt.Spec
import EvmAsm.Evm64.Gt.Spec
import EvmAsm.Evm64.Slt.Spec
import EvmAsm.Evm64.Sgt.Spec
import EvmAsm.Evm64.Eq.Spec
import EvmAsm.Evm64.IsZero.Spec
import EvmAsm.Evm64.And.Spec
import EvmAsm.Evm64.Or.Spec
import EvmAsm.Evm64.Xor.Spec
import EvmAsm.Evm64.Not.Spec
import EvmAsm.Evm64.MSize.Spec
import EvmAsm.Evm64.Env.Wrappers
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Rv64.InstructionSpecs

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Evm64 (cc_ret)
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- 1. The clean-ret handler Program + CodeReq
-- ============================================================================

/-- Wrap a verified body in the M5b dispatcher's "clean-ret" handler
    ABI: run the body, then advance the EVM code pointer `x10` by `n`
    bytes (the opcode's byte width), then return via `JALR x0, x1, 0`
    to the dispatcher's `j .dispatch_loop` continuation. -/
def cleanRetHandlerProgram (body : Program) (n : BitVec 12) : Program :=
  body ;; (Rv64.ADDI .x10 .x10 n) ;; cc_ret

/-- CodeReq for a clean-ret handler at base address `base`. -/
abbrev cleanRetHandlerCode (base : Word) (body : Program) (n : BitVec 12) : CodeReq :=
  CodeReq.ofProg base (cleanRetHandlerProgram body n)

theorem cleanRetHandlerProgram_length (body : Program) (n : BitVec 12) :
    (cleanRetHandlerProgram body n).length = body.length + 2 := by
  simp [cleanRetHandlerProgram, seq, Rv64.ADDI, cc_ret, Rv64.JALR, single]

-- ============================================================================
-- 2. The handler-level spec template
-- ============================================================================

/-- Helper: 4 * (nSteps : Nat) as a 64-bit Word. -/
private def fourTimes (nSteps : Nat) : Word := BitVec.ofNat 64 (4 * nSteps)

/-- Lift a verified body spec to a handler subroutine spec.

    Given:
    * `h_body` — the body's verified `cpsTripleWithin` spec from
      `Evm64/<Op>/Spec.lean`. Its exit PC must be `base + 4*body.length`
      and its CodeReq must be `CodeReq.ofProg base body` (the standard
      shape produced by the `*_code` abbreviations);
    * `hQpcFree` — the body's postcondition `Q` is pcFree. Satisfied
      automatically by any sepConj of `regIs` / `memCellIs` cells
      (true for every body spec in `Evm64/`);
    * `n` — the opcode's byte width (typically `1`; up to `33` for PUSH32);

    we get a Hoare triple for the full handler subroutine
    `body ;; ADDI x10 x10 n ;; JALR x0 x1 0` that says:
    * x10 is incremented by `signExtend12 n` (= `n` as a Word, for `n < 2048`);
    * x1 is preserved;
    * the body's frame `P → Q` carries through.

    The exit PC is `x1_init &&& ~~~1` — the standard JALR mask. In the
    M5b dispatcher, x1 was set by the loop's `jalr x1, x7, 0` to the
    address of the `j .dispatch_loop` instruction (always 4-byte
    aligned), so the mask is a no-op there. -/
theorem cleanRetHandlerSpec
    {nSteps : Nat} {base : Word} {body : Program} {P Q : Assertion}
    (hQpcFree : Q.pcFree)
    (hBodyLen : body.length = nSteps)
    (hBodyLenBound : nSteps < 2 ^ 60)
    (h_body : cpsTripleWithin nSteps base (base + fourTimes nSteps)
                (CodeReq.ofProg base body) P Q)
    (n : BitVec 12)
    (x10_init x1_init : Word) :
    cpsTripleWithin (nSteps + 2) base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base body n)
      (P ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (Q ** (.x10 ↦ᵣ (x10_init + signExtend12 n)) ** (.x1 ↦ᵣ x1_init)) := by
  -- Set up code-region addresses.
  set addiAddr : Word := base + fourTimes nSteps with haddiAddr
  set jalrAddr : Word := addiAddr + 4 with hjalrAddr
  -- Frame blocks (open formulas so `pcFree` can see the structure):
  -- pre-tail `F = (x10 ↦ x10_init) ** (x1 ↦ x1_init)`
  -- post-tail `F' = (x10 ↦ x10_init + n) ** (x1 ↦ x1_init)`
  -- Framing order is chosen so that all three pieces compose with no
  -- associativity dance: body's post and ADDI's pre are syntactically
  -- `Q ** F`; ADDI's post and JALR's pre/post are syntactically `Q ** F'`.
  -- Step 1: body, framed with F on the right.
  have h_body_framed :=
    cpsTripleWithin_frameR
      ((.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (by pcFree) h_body
  -- Step 2: ADDI x10 x10 n at addiAddr. Frame x1 on the right (giving
  -- F / F' as combined frame), then Q on the left.
  have h_addi := addi_spec_same_within .x10 x10_init n addiAddr (by decide)
  have h_addi_x1 :=
    cpsTripleWithin_frameR (.x1 ↦ᵣ x1_init) pcFree_regIs h_addi
  have h_addi_framed :=
    cpsTripleWithin_frameL Q hQpcFree h_addi_x1
  -- Step 3: JALR x0 x1 0 (= cc_ret) at jalrAddr. Frame `(x10 ↦ +n)` on
  -- the left (giving F'), then Q on the left.
  have h_jalr := EvmAsm.Evm64.ret_spec_within' jalrAddr x1_init
  have h_jalr_x10 :=
    cpsTripleWithin_frameL (.x10 ↦ᵣ (x10_init + signExtend12 n))
      pcFree_regIs h_jalr
  have h_jalr_framed :=
    cpsTripleWithin_frameL Q hQpcFree h_jalr_x10
  -- Disjointness #1: body code vs ADDI singleton.
  have hNStepsBound64 : (4 * nSteps : Nat) < 2 ^ 64 := by
    have : (2 : Nat) ^ 60 * 4 ≤ 2 ^ 64 := by decide
    omega
  have h_disj_body_addi :
      (CodeReq.ofProg base body).Disjoint
        (CodeReq.singleton addiAddr (.ADDI .x10 .x10 n)) := by
    intro a
    by_cases ha : a = addiAddr
    · left
      apply CodeReq.ofProg_none_range
      intro k hk heq
      subst ha
      simp only [addiAddr, fourTimes, ← hBodyLen] at heq
      have hk_bound : (4 * k : Nat) < 4 * body.length := by omega
      have hbody_bound : (4 * body.length : Nat) < 2 ^ 64 := by
        rw [hBodyLen]; exact hNStepsBound64
      have hk_bound' : (4 * k : Nat) < 2 ^ 64 := by omega
      bv_omega
    · right
      simp [CodeReq.singleton, ha]
  -- Compose body ;; ADDI.
  have h_body_addi :=
    cpsTripleWithin_seq h_disj_body_addi h_body_framed h_addi_framed
  -- Disjointness #2: (body ∪ ADDI) vs JALR singleton.
  have h_disj_bodyaddi_jalr :
      ((CodeReq.ofProg base body).union
          (CodeReq.singleton addiAddr (.ADDI .x10 .x10 n))).Disjoint
        (CodeReq.singleton jalrAddr (.JALR .x0 .x1 0)) := by
    apply CodeReq.Disjoint.union_left
    · -- body vs JALR
      intro a
      by_cases ha : a = jalrAddr
      · left
        apply CodeReq.ofProg_none_range
        intro k hk heq
        subst ha
        simp only [jalrAddr, addiAddr, fourTimes, ← hBodyLen] at heq
        have hk_bound : (4 * k : Nat) < 4 * body.length := by omega
        have hbody_bound : (4 * body.length : Nat) < 2 ^ 64 := by
          rw [hBodyLen]; exact hNStepsBound64
        have hk_bound' : (4 * k : Nat) < 2 ^ 64 := by omega
        bv_omega
      · right; simp [CodeReq.singleton, ha]
    · -- ADDI vs JALR: singletons at addiAddr vs addiAddr + 4.
      apply CodeReq.Disjoint.singleton
      intro heq
      -- addiAddr ≠ addiAddr + 4 (since 4 ≠ 0 in Word).
      have : (4 : Word) = 0 := by
        have h := heq
        bv_omega
      exact absurd this (by decide)
  -- Compose (body ;; ADDI) ;; JALR. Bound: (nSteps + 1) + 1 = nSteps + 2.
  have h_full :=
    cpsTripleWithin_seq h_disj_bodyaddi_jalr h_body_addi h_jalr_framed
  -- Align the CodeReq with cleanRetHandlerCode. Mirrors the pattern from
  -- `mul_callable_code_eq_ofProg`: unfold seq, then apply ofProg_append
  -- twice to peel off the two tail instructions. Note `;;` is
  -- right-associative, so `body ;; ADDI ;; cc_ret = body ++ (ADDI ++ cc_ret)`.
  have hCodeEq :
      ((CodeReq.ofProg base body).union
          (CodeReq.singleton addiAddr (.ADDI .x10 .x10 n))).union
            (CodeReq.singleton jalrAddr (.JALR .x0 .x1 0)) =
        cleanRetHandlerCode base body n := by
    unfold cleanRetHandlerCode cleanRetHandlerProgram
    unfold seq
    -- Goal: `... = ofProg base (body ++ (Rv64.ADDI x10 x10 n ++ cc_ret))`
    -- Outer split: peel `body` off the front.
    have hOuter :
        CodeReq.ofProg base (body ++ (Rv64.ADDI .x10 .x10 n ++ cc_ret)) =
          (CodeReq.ofProg base body).union
            (CodeReq.ofProg (base + BitVec.ofNat 64 (4 * body.length))
              (Rv64.ADDI .x10 .x10 n ++ cc_ret)) :=
      CodeReq.ofProg_append
    rw [hOuter]
    -- Inner split: peel ADDI off the front of (ADDI ++ cc_ret).
    have hInner :
        CodeReq.ofProg (base + BitVec.ofNat 64 (4 * body.length))
            (Rv64.ADDI .x10 .x10 n ++ cc_ret) =
          (CodeReq.ofProg (base + BitVec.ofNat 64 (4 * body.length))
              (Rv64.ADDI .x10 .x10 n)).union
            (CodeReq.ofProg
              (base + BitVec.ofNat 64 (4 * body.length)
                + BitVec.ofNat 64 (4 * (Rv64.ADDI .x10 .x10 n).length))
              cc_ret) :=
      CodeReq.ofProg_append
    rw [hInner]
    -- Reduce single-instr ofProgs.
    rw [show CodeReq.ofProg (base + BitVec.ofNat 64 (4 * body.length))
              (Rv64.ADDI .x10 .x10 n)
            = CodeReq.singleton (base + BitVec.ofNat 64 (4 * body.length))
                (Instr.ADDI .x10 .x10 n) from
        CodeReq.ofProg_singleton]
    rw [show CodeReq.ofProg
              (base + BitVec.ofNat 64 (4 * body.length)
                + BitVec.ofNat 64 (4 * (Rv64.ADDI .x10 .x10 n).length))
              cc_ret
            = CodeReq.singleton
                (base + BitVec.ofNat 64 (4 * body.length)
                  + BitVec.ofNat 64 (4 * (Rv64.ADDI .x10 .x10 n).length))
                (Instr.JALR .x0 .x1 0) from
        CodeReq.ofProg_singleton]
    -- Reassociate union: ofProg_append produces right-nested
    -- `A ∪ (B ∪ C)` but h_full's CodeReq is `(A ∪ B) ∪ C`.
    rw [← CodeReq.union_assoc]
    -- Resolve address offsets to `addiAddr` / `jalrAddr`.
    have h_addi_len : (Rv64.ADDI .x10 .x10 n).length = 1 := by
      simp [Rv64.ADDI, single]
    have h_addi_off :
        base + BitVec.ofNat 64 (4 * body.length) = addiAddr := by
      simp only [addiAddr, fourTimes, hBodyLen]
    rw [h_addi_off]
    -- After the addi rewrite, the jalr address is
    -- `addiAddr + BitVec.ofNat 64 (4 * (Rv64.ADDI ...).length)`.
    have h_jalr_off :
        addiAddr + BitVec.ofNat 64 (4 * (Rv64.ADDI .x10 .x10 n).length) = jalrAddr := by
      rw [h_addi_len]
      simp only [jalrAddr]
      bv_omega
    rw [h_jalr_off]
  -- Align step bound and finish.
  rw [← hCodeEq, show nSteps + 2 = (nSteps + 1) + 1 from by omega]
  exact h_full

-- ============================================================================
-- 3. Concrete instance — ADD (0x01)
-- ============================================================================

/-- Handler-level spec for `h_ADD` (opcode 0x01). The verified
    `evm_add_spec_within` body spec gets lifted through the dispatcher's
    `.advanceAndRet 1` tail. After the handler runs, the EVM stack is
    one word smaller (per evm_add), `x10` (EVM code pointer) advances
    by 1, and `x1` (dispatcher's return address) is preserved. -/
theorem evmAddHandlerSpec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (v7 v6 v5 v11 : Word)
    (x10_init x1_init : Word) :
    let sum0 := a0 + b0
    let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
    let psum1 := a1 + b1
    let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
    let carry1 := carry1a ||| carry1b
    let psum2 := a2 + b2
    let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
    let carry2 := carry2a ||| carry2b
    let psum3 := a3 + b3
    let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
    let result3 := psum3 + carry2
    let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
    let carry3 := carry3a ||| carry3b
    cpsTripleWithin 32 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base EvmAsm.Evm64.evm_add 1)
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) ** (.x5 ↦ᵣ carry3) **
        (.x11 ↦ᵣ carry3a) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ sum0) ** ((sp + 40) ↦ₘ result1) ** ((sp + 48) ↦ₘ result2) **
        ((sp + 56) ↦ₘ result3))
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  intro sum0 carry0 psum1 carry1a result1 carry1b carry1 psum2 carry2a result2 carry2b carry2 psum3 carry3a result3 carry3b carry3
  have h_body := EvmAsm.Evm64.evm_add_spec_within sp base a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 v5 v11
  -- evm_add_code base = CodeReq.ofProg base evm_add (by abbrev). Body length = 30.
  -- evm_add_spec_within has exit PC `base + 120` = `base + fourTimes 30`.
  have hBodyLen : EvmAsm.Evm64.evm_add.length = 30 := by decide
  have hExitEq : (base + (120 : Word)) = base + fourTimes 30 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) ** (.x5 ↦ᵣ carry3) **
        (.x11 ↦ᵣ carry3a) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ sum0) ** ((sp + 40) ↦ₘ result1) ** ((sp + 48) ↦ₘ result2) **
        ((sp + 56) ↦ₘ result3)) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 4. Concrete instance — POP (0x50)
-- ============================================================================

/-- Handler-level spec for `h_POP` (opcode 0x50). The simplest possible
    handler: a 1-instruction body (`ADDI x12 x12 32`) that pops one
    256-bit EVM stack word, wrapped with the dispatcher's standard
    advance-by-1 tail. Total: 3 RISC-V instructions. -/
theorem evmPopHandlerSpec (sp base : Word) (x10_init x1_init : Word) :
    cpsTripleWithin 3 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base EvmAsm.Evm64.evm_pop 1)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  have h_body := EvmAsm.Evm64.evm_pop_spec_within sp base
  have hBodyLen : EvmAsm.Evm64.evm_pop.length = 1 := by decide
  have hExitEq : (base + (4 : Word)) = base + fourTimes 1 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree : ((.x12 ↦ᵣ (sp + 32)) : Assertion).pcFree := pcFree_regIs
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 5. Concrete instance — SUB (0x03)
-- ============================================================================

/-- Handler-level spec for `h_SUB` (opcode 0x03). Mirrors `evmAddHandlerSpec`
    but with `evm_sub_spec_within` as the underlying body. 30-instruction
    body + 2-instruction tail = 32 RISC-V steps. -/
theorem evmSubHandlerSpec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (v7 v6 v5 v11 : Word)
    (x10_init x1_init : Word) :
    let borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0
    let diff0 := a0 - b0
    let borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0
    let temp1 := a1 - b1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let result1 := temp1 - borrow0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0
    let temp2 := a2 - b2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let result2 := temp2 - borrow1
    let borrow2 := borrow2a ||| borrow2b
    let borrow3a := if BitVec.ult a3 b3 then (1 : Word) else 0
    let temp3 := a3 - b3
    let borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0
    let result3 := temp3 - borrow2
    let borrow3 := borrow3a ||| borrow3b
    cpsTripleWithin 32 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base EvmAsm.Evm64.evm_sub 1)
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ borrow3b) ** (.x5 ↦ᵣ borrow3) **
        (.x11 ↦ᵣ borrow3a) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ diff0) ** ((sp + 40) ↦ₘ result1) ** ((sp + 48) ↦ₘ result2) **
        ((sp + 56) ↦ₘ result3))
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  intro borrow0 diff0 borrow1a temp1 borrow1b result1 borrow1 borrow2a temp2 borrow2b result2 borrow2 borrow3a temp3 borrow3b result3 borrow3
  have h_body := EvmAsm.Evm64.evm_sub_spec_within sp base a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 v5 v11
  have hBodyLen : EvmAsm.Evm64.evm_sub.length = 30 := by decide
  have hExitEq : (base + (120 : Word)) = base + fourTimes 30 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ borrow3b) ** (.x5 ↦ᵣ borrow3) **
        (.x11 ↦ᵣ borrow3a) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ diff0) ** ((sp + 40) ↦ₘ result1) ** ((sp + 48) ↦ₘ result2) **
        ((sp + 56) ↦ₘ result3)) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 6. Concrete instance — LT (0x10)
-- ============================================================================

/-- Handler-level spec for `h_LT` (opcode 0x10). 26-instruction body
    (unsigned borrow chain → boolean result) + 2-instruction tail = 28 steps. -/
theorem evmLtHandlerSpec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (v7 v6 v5 v11 : Word)
    (x10_init x1_init : Word) :
    let borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0
    let borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0
    let temp1 := a1 - b1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0
    let temp2 := a2 - b2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    let borrow3a := if BitVec.ult a3 b3 then (1 : Word) else 0
    let temp3 := a3 - b3
    let borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0
    let borrow3 := borrow3a ||| borrow3b
    cpsTripleWithin 28 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base EvmAsm.Evm64.evm_lt 1)
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ temp3) ** (.x6 ↦ᵣ borrow3b) **
        (.x5 ↦ᵣ borrow3) ** (.x11 ↦ᵣ borrow3a) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ borrow3) ** ((sp + 40) ↦ₘ 0) ** ((sp + 48) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0))
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  intro borrow0 borrow1a temp1 borrow1b borrow1 borrow2a temp2 borrow2b borrow2 borrow3a temp3 borrow3b borrow3
  have h_body := EvmAsm.Evm64.evm_lt_spec_within sp base a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 v5 v11
  have hBodyLen : EvmAsm.Evm64.evm_lt.length = 26 := by decide
  have hExitEq : (base + (104 : Word)) = base + fourTimes 26 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ temp3) ** (.x6 ↦ᵣ borrow3b) **
        (.x5 ↦ᵣ borrow3) ** (.x11 ↦ᵣ borrow3a) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ borrow3) ** ((sp + 40) ↦ₘ 0) ** ((sp + 48) ↦ₘ 0) **
        ((sp + 56) ↦ₘ 0)) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 7. Concrete instance — GT (0x11)
-- ============================================================================

/-- Handler-level spec for `h_GT` (opcode 0x11). Same shape as LT with
    swapped operands (GT(a, b) = LT(b, a)); 26-instruction body. -/
theorem evmGtHandlerSpec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (v7 v6 v5 v11 : Word)
    (x10_init x1_init : Word) :
    let borrow0 := if BitVec.ult b0 a0 then (1 : Word) else 0
    let borrow1a := if BitVec.ult b1 a1 then (1 : Word) else 0
    let temp1 := b1 - a1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult b2 a2 then (1 : Word) else 0
    let temp2 := b2 - a2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    let borrow3a := if BitVec.ult b3 a3 then (1 : Word) else 0
    let temp3 := b3 - a3
    let borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0
    let borrow3 := borrow3a ||| borrow3b
    cpsTripleWithin 28 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base EvmAsm.Evm64.evm_gt 1)
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ temp3) ** (.x6 ↦ᵣ borrow3b) **
        (.x5 ↦ᵣ borrow3) ** (.x11 ↦ᵣ borrow3a) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ borrow3) ** ((sp + 40) ↦ₘ 0) ** ((sp + 48) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0))
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  intro borrow0 borrow1a temp1 borrow1b borrow1 borrow2a temp2 borrow2b borrow2 borrow3a temp3 borrow3b borrow3
  have h_body := EvmAsm.Evm64.evm_gt_spec_within sp base a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 v5 v11
  have hBodyLen : EvmAsm.Evm64.evm_gt.length = 26 := by decide
  have hExitEq : (base + (104 : Word)) = base + fourTimes 26 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ temp3) ** (.x6 ↦ᵣ borrow3b) **
        (.x5 ↦ᵣ borrow3) ** (.x11 ↦ᵣ borrow3a) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ borrow3) ** ((sp + 40) ↦ₘ 0) ** ((sp + 48) ↦ₘ 0) **
        ((sp + 56) ↦ₘ 0)) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 8. Concrete instance — SLT (0x12)
-- ============================================================================

/-- Handler-level spec for `h_SLT` (opcode 0x12). 25-instruction body
    (signed less-than via MSB-equal/MSB-differ branches) + 2-instruction
    tail = 27 steps. -/
theorem evmSltHandlerSpec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (v7 v6 v5 v11 : Word)
    (x10_init x1_init : Word) :
    let borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0
    let borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0
    let temp1 := a1 - b1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0
    let temp2 := a2 - b2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    let sltMsb := if BitVec.slt a3 b3 then (1 : Word) else 0
    let result := if a3 = b3 then borrow2 else sltMsb
    cpsTripleWithin 27 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base EvmAsm.Evm64.evm_slt 1)
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((.x12 ↦ᵣ (sp + 32)) **
        (.x7 ↦ᵣ (if a3 = b3 then temp2 else a3)) **
        (.x6 ↦ᵣ (if a3 = b3 then borrow2b else b3)) **
        (.x5 ↦ᵣ result) **
        (.x11 ↦ᵣ (if a3 = b3 then borrow2a else v11)) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ result) ** ((sp + 40) ↦ₘ 0) ** ((sp + 48) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0))
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  intro borrow0 borrow1a temp1 borrow1b borrow1 borrow2a temp2 borrow2b borrow2 sltMsb result
  have h_body := EvmAsm.Evm64.evm_slt_spec_within sp base a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 v5 v11
  have hBodyLen : EvmAsm.Evm64.evm_slt.length = 25 := by decide
  have hExitEq : (base + (100 : Word)) = base + fourTimes 25 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((.x12 ↦ᵣ (sp + 32)) **
        (.x7 ↦ᵣ (if a3 = b3 then temp2 else a3)) **
        (.x6 ↦ᵣ (if a3 = b3 then borrow2b else b3)) **
        (.x5 ↦ᵣ result) **
        (.x11 ↦ᵣ (if a3 = b3 then borrow2a else v11)) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ result) ** ((sp + 40) ↦ₘ 0) ** ((sp + 48) ↦ₘ 0) **
        ((sp + 56) ↦ₘ 0)) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 9. Concrete instance — SGT (0x13)
-- ============================================================================

/-- Handler-level spec for `h_SGT` (opcode 0x13). Same shape as SLT with
    swapped operands (SGT(a, b) = SLT(b, a)); 25-instruction body. -/
theorem evmSgtHandlerSpec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (v7 v6 v5 v11 : Word)
    (x10_init x1_init : Word) :
    let borrow0 := if BitVec.ult b0 a0 then (1 : Word) else 0
    let borrow1a := if BitVec.ult b1 a1 then (1 : Word) else 0
    let temp1 := b1 - a1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult b2 a2 then (1 : Word) else 0
    let temp2 := b2 - a2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    let sgtMsb := if BitVec.slt b3 a3 then (1 : Word) else 0
    let result := if b3 = a3 then borrow2 else sgtMsb
    cpsTripleWithin 27 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base EvmAsm.Evm64.evm_sgt 1)
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((.x12 ↦ᵣ (sp + 32)) **
        (.x7 ↦ᵣ (if b3 = a3 then temp2 else b3)) **
        (.x6 ↦ᵣ (if b3 = a3 then borrow2b else a3)) **
        (.x5 ↦ᵣ result) **
        (.x11 ↦ᵣ (if b3 = a3 then borrow2a else v11)) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ result) ** ((sp + 40) ↦ₘ 0) ** ((sp + 48) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0))
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  intro borrow0 borrow1a temp1 borrow1b borrow1 borrow2a temp2 borrow2b borrow2 sgtMsb result
  have h_body := EvmAsm.Evm64.evm_sgt_spec_within sp base a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 v5 v11
  have hBodyLen : EvmAsm.Evm64.evm_sgt.length = 25 := by decide
  have hExitEq : (base + (100 : Word)) = base + fourTimes 25 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((.x12 ↦ᵣ (sp + 32)) **
        (.x7 ↦ᵣ (if b3 = a3 then temp2 else b3)) **
        (.x6 ↦ᵣ (if b3 = a3 then borrow2b else a3)) **
        (.x5 ↦ᵣ result) **
        (.x11 ↦ᵣ (if b3 = a3 then borrow2a else v11)) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ result) ** ((sp + 40) ↦ₘ 0) ** ((sp + 48) ↦ₘ 0) **
        ((sp + 56) ↦ₘ 0)) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 10. Concrete instance — EQ (0x14)
-- ============================================================================

/-- Handler-level spec for `h_EQ` (opcode 0x14). 21-instruction body
    (XOR-OR-accumulate → SLTIU) + 2-instruction tail = 23 steps. -/
theorem evmEqHandlerSpec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (v7 v6 v5 v11 : Word)
    (x10_init x1_init : Word) :
    let acc0 := a0 ^^^ b0
    let acc1 := acc0 ||| (a1 ^^^ b1)
    let acc2 := acc1 ||| (a2 ^^^ b2)
    let acc3 := acc2 ||| (a3 ^^^ b3)
    let eqResult := if BitVec.ult acc3 (1 : Word) then (1 : Word) else 0
    cpsTripleWithin 23 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base EvmAsm.Evm64.evm_eq 1)
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((.x12 ↦ᵣ (sp + 32)) **
        (.x7 ↦ᵣ eqResult) ** (.x6 ↦ᵣ (a3 ^^^ b3)) ** (.x5 ↦ᵣ b3) ** (.x11 ↦ᵣ v11) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ eqResult) ** ((sp + 40) ↦ₘ 0) ** ((sp + 48) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0))
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  intro acc0 acc1 acc2 acc3 eqResult
  have h_body := EvmAsm.Evm64.evm_eq_spec_within sp base a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 v5 v11
  have hBodyLen : EvmAsm.Evm64.evm_eq.length = 21 := by decide
  have hExitEq : (base + (84 : Word)) = base + fourTimes 21 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((.x12 ↦ᵣ (sp + 32)) **
        (.x7 ↦ᵣ eqResult) ** (.x6 ↦ᵣ (a3 ^^^ b3)) ** (.x5 ↦ᵣ b3) ** (.x11 ↦ᵣ v11) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ eqResult) ** ((sp + 40) ↦ₘ 0) ** ((sp + 48) ↦ₘ 0) **
        ((sp + 56) ↦ₘ 0)) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 11. Concrete instance — ISZERO (0x15)
-- ============================================================================

/-- Handler-level spec for `h_ISZERO` (opcode 0x15). 12-instruction unary
    body (OR-accumulate → SLTIU) + 2-instruction tail = 14 steps. -/
theorem evmIsZeroHandlerSpec (sp base : Word)
    (a0 a1 a2 a3 : Word) (v7 v6 : Word)
    (x10_init x1_init : Word) :
    let orAll := a0 ||| a1 ||| a2 ||| a3
    let result := if BitVec.ult orAll (1 : Word) then (1 : Word) else 0
    cpsTripleWithin 14 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base EvmAsm.Evm64.evm_iszero 1)
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ a3) **
        (sp ↦ₘ result) ** ((sp + 8) ↦ₘ 0) ** ((sp + 16) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0))
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  intro orAll result
  have h_body := EvmAsm.Evm64.evm_iszero_spec_within sp base a0 a1 a2 a3 v7 v6
  have hBodyLen : EvmAsm.Evm64.evm_iszero.length = 12 := by decide
  have hExitEq : (base + (48 : Word)) = base + fourTimes 12 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ a3) **
        (sp ↦ₘ result) ** ((sp + 8) ↦ₘ 0) ** ((sp + 16) ↦ₘ 0) **
        ((sp + 24) ↦ₘ 0)) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 12. Concrete instance — AND (0x16)
-- ============================================================================

/-- Handler-level spec for `h_AND` (opcode 0x16). 17-instruction body
    (bitwise AND per limb) + 2-instruction tail = 19 steps. -/
theorem evmAndHandlerSpec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (v7 v6 : Word)
    (x10_init x1_init : Word) :
    cpsTripleWithin 19 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base EvmAsm.Evm64.evm_and 1)
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a3 &&& b3)) ** (.x6 ↦ᵣ b3) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ (a0 &&& b0)) ** ((sp + 40) ↦ₘ (a1 &&& b1)) **
        ((sp + 48) ↦ₘ (a2 &&& b2)) ** ((sp + 56) ↦ₘ (a3 &&& b3)))
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  have h_body := EvmAsm.Evm64.evm_and_spec_within sp base a0 a1 a2 a3 b0 b1 b2 b3 v7 v6
  have hBodyLen : EvmAsm.Evm64.evm_and.length = 17 := by decide
  have hExitEq : (base + (68 : Word)) = base + fourTimes 17 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a3 &&& b3)) ** (.x6 ↦ᵣ b3) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ (a0 &&& b0)) ** ((sp + 40) ↦ₘ (a1 &&& b1)) **
        ((sp + 48) ↦ₘ (a2 &&& b2)) **
        ((sp + 56) ↦ₘ (a3 &&& b3))) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 13. Concrete instance — OR (0x17)
-- ============================================================================

/-- Handler-level spec for `h_OR` (opcode 0x17). 17-instruction body
    (bitwise OR per limb) + 2-instruction tail = 19 steps. -/
theorem evmOrHandlerSpec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (v7 v6 : Word)
    (x10_init x1_init : Word) :
    cpsTripleWithin 19 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base EvmAsm.Evm64.evm_or 1)
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a3 ||| b3)) ** (.x6 ↦ᵣ b3) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ (a0 ||| b0)) ** ((sp + 40) ↦ₘ (a1 ||| b1)) **
        ((sp + 48) ↦ₘ (a2 ||| b2)) ** ((sp + 56) ↦ₘ (a3 ||| b3)))
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  have h_body := EvmAsm.Evm64.evm_or_spec_within sp base a0 a1 a2 a3 b0 b1 b2 b3 v7 v6
  have hBodyLen : EvmAsm.Evm64.evm_or.length = 17 := by decide
  have hExitEq : (base + (68 : Word)) = base + fourTimes 17 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a3 ||| b3)) ** (.x6 ↦ᵣ b3) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ (a0 ||| b0)) ** ((sp + 40) ↦ₘ (a1 ||| b1)) **
        ((sp + 48) ↦ₘ (a2 ||| b2)) **
        ((sp + 56) ↦ₘ (a3 ||| b3))) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 14. Concrete instance — XOR (0x18)
-- ============================================================================

/-- Handler-level spec for `h_XOR` (opcode 0x18). 17-instruction body
    (bitwise XOR per limb) + 2-instruction tail = 19 steps. -/
theorem evmXorHandlerSpec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (v7 v6 : Word)
    (x10_init x1_init : Word) :
    cpsTripleWithin 19 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base EvmAsm.Evm64.evm_xor 1)
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a3 ^^^ b3)) ** (.x6 ↦ᵣ b3) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ (a0 ^^^ b0)) ** ((sp + 40) ↦ₘ (a1 ^^^ b1)) **
        ((sp + 48) ↦ₘ (a2 ^^^ b2)) ** ((sp + 56) ↦ₘ (a3 ^^^ b3)))
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  have h_body := EvmAsm.Evm64.evm_xor_spec_within sp base a0 a1 a2 a3 b0 b1 b2 b3 v7 v6
  have hBodyLen : EvmAsm.Evm64.evm_xor.length = 17 := by decide
  have hExitEq : (base + (68 : Word)) = base + fourTimes 17 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a3 ^^^ b3)) ** (.x6 ↦ᵣ b3) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ (a0 ^^^ b0)) ** ((sp + 40) ↦ₘ (a1 ^^^ b1)) **
        ((sp + 48) ↦ₘ (a2 ^^^ b2)) **
        ((sp + 56) ↦ₘ (a3 ^^^ b3))) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 15. Concrete instance — NOT (0x19)
-- ============================================================================

/-- Handler-level spec for `h_NOT` (opcode 0x19). 12-instruction unary
    body (bitwise complement per limb) + 2-instruction tail = 14 steps. -/
theorem evmNotHandlerSpec (sp base : Word)
    (a0 a1 a2 a3 : Word) (v7 : Word)
    (x10_init x1_init : Word) :
    let c := signExtend12 (-1 : BitVec 12)
    cpsTripleWithin 14 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base EvmAsm.Evm64.evm_not 1)
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a3 ^^^ c)) **
        (sp ↦ₘ (a0 ^^^ c)) ** ((sp + 8) ↦ₘ (a1 ^^^ c)) **
        ((sp + 16) ↦ₘ (a2 ^^^ c)) ** ((sp + 24) ↦ₘ (a3 ^^^ c)))
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  intro c
  have h_body := EvmAsm.Evm64.evm_not_spec_within sp base a0 a1 a2 a3 v7
  have hBodyLen : EvmAsm.Evm64.evm_not.length = 12 := by decide
  have hExitEq : (base + (48 : Word)) = base + fourTimes 12 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a3 ^^^ c)) **
        (sp ↦ₘ (a0 ^^^ c)) ** ((sp + 8) ↦ₘ (a1 ^^^ c)) **
        ((sp + 16) ↦ₘ (a2 ^^^ c)) **
        ((sp + 24) ↦ₘ (a3 ^^^ c))) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 16. Concrete instance — MSIZE (0x59)
-- ============================================================================

/-- Handler-level spec for `h_MSIZE` (opcode 0x59). Lifts the verified
    `evm_msize_spec_within` body (6-instruction memory-size push: load the
    size cell into `tempReg`, decrement SP, write the low limb + three zero
    upper limbs) through the dispatcher's standard `.advanceAndRet 1` tail.
    6-instruction body + 2-instruction tail = 8 RISC-V steps.

    Unlike the binary/unary arithmetic handlers, the body is parameterized by
    the size-cell pointer register `sizeReg` and a scratch `tempReg`
    (`tempReg ≠ x0`); the spec is correspondingly general. After the handler
    runs, the EVM stack grows by one word holding `sizeBytes` in its low limb,
    `x10` advances by 1, and `x1` is preserved. -/
theorem evmMsizeHandlerSpec
    (sizeReg tempReg : Reg) (htemp_ne_x0 : tempReg ≠ .x0)
    (nsp base sizeLoc tempOld : Word) (sizeBytes : Nat)
    (d0 d1 d2 d3 : Word) (x10_init x1_init : Word) :
    cpsTripleWithin (6 + 2) base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base (EvmAsm.Evm64.evm_msize sizeReg tempReg) 1)
      (((sizeReg ↦ᵣ sizeLoc) ** (tempReg ↦ᵣ tempOld) ** (.x12 ↦ᵣ (nsp + 32)) **
        (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) ** ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
        EvmAsm.Evm64.evmMemSizeIs sizeLoc sizeBytes)
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((sizeReg ↦ᵣ sizeLoc) ** (tempReg ↦ᵣ BitVec.ofNat 64 sizeBytes) ** (.x12 ↦ᵣ nsp) **
        (nsp ↦ₘ BitVec.ofNat 64 sizeBytes) ** ((nsp + 8) ↦ₘ 0) **
        ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0) **
        EvmAsm.Evm64.evmMemSizeIs sizeLoc sizeBytes)
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  have h_body := EvmAsm.Evm64.evm_msize_spec_within sizeReg tempReg htemp_ne_x0
    nsp base sizeLoc tempOld sizeBytes d0 d1 d2 d3
  have hBodyLen : (EvmAsm.Evm64.evm_msize sizeReg tempReg).length = 6 :=
    EvmAsm.Evm64.evm_msize_length sizeReg tempReg
  have hExitEq : (base + (24 : Word)) = base + fourTimes 6 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((sizeReg ↦ᵣ sizeLoc) ** (tempReg ↦ᵣ BitVec.ofNat 64 sizeBytes) ** (.x12 ↦ᵣ nsp) **
        (nsp ↦ₘ BitVec.ofNat 64 sizeBytes) ** ((nsp + 8) ↦ₘ 0) **
        ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0) **
        EvmAsm.Evm64.evmMemSizeIs sizeLoc sizeBytes) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 17. Parameterized instance — the 13 simple environment opcodes
-- ============================================================================

open EvmAsm.Evm64 (EvmEnv evmStackIs) in
open EvmAsm.Evm64.Env (SimpleEnvField evm_env_load evm_env_load_length
  evm_env_load_stack_spec_within) in
/-- Handler-level spec for the 13 simple environment opcodes
    (ADDRESS/CALLER/CALLVALUE/ORIGIN/GASPRICE/COINBASE/TIMESTAMP/NUMBER/
    PREVRANDAO/GASLIMIT/CHAINID/BASEFEE/SELFBALANCE), parameterized by the
    `SimpleEnvField`. Lifts the field-generic `evm_env_load_stack_spec_within`
    9-instruction body (load the env field, decrement SP, push the value) through
    the dispatcher's `.advanceAndRet 1` clean-ret tail. 9-instruction body +
    2-instruction tail = 11 RISC-V steps. Instantiating `field` at `.address`,
    `.caller`, … yields each opcode's handler spec. -/
theorem evmEnvWrapperHandlerSpec
    (field : SimpleEnvField)
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld : Word) (env : EvmEnv)
    (d0 d1 d2 d3 : Word) (rest : List EvmAsm.Evm64.EvmWord) (x10_init x1_init : Word) :
    cpsTripleWithin (9 + 2) base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base (evm_env_load envBaseReg tmpReg field) 1)
      (((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) ** (.x12 ↦ᵣ (nsp + 32)) **
        (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) ** ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
        EvmEnv.envIs envAddr env ** evmStackIs (nsp + 32) rest)
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ (field.value env).getLimbN 3) **
        (.x12 ↦ᵣ nsp) **
        evmStackIs nsp (field.value env :: rest) ** EvmEnv.envIs envAddr env)
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  have h_body := evm_env_load_stack_spec_within envBaseReg tmpReg htmp_ne_x0
    nsp base envAddr tempOld field env d0 d1 d2 d3 rest
  have hBodyLen : (evm_env_load envBaseReg tmpReg field).length = 9 :=
    evm_env_load_length envBaseReg tmpReg field
  have hExitEq : (base + (36 : Word)) = base + fourTimes 9 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ (field.value env).getLimbN 3) **
        (.x12 ↦ᵣ nsp) **
        evmStackIs nsp (field.value env :: rest) **
        EvmEnv.envIs envAddr env) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

end EvmAsm.Codegen.Proofs
