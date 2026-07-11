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
import EvmAsm.Codegen.Proofs.ReloadHandler
import EvmAsm.Evm64.Add.Spec
import EvmAsm.Evm64.Pop.Spec
import EvmAsm.Evm64.Push0.Spec
import EvmAsm.Evm64.MStore8.Spec
import EvmAsm.Evm64.Dup.Spec
import EvmAsm.Evm64.Swap.Spec
import EvmAsm.Evm64.Multiply.Spec
import EvmAsm.Evm64.SignExtend.Spec
import EvmAsm.Evm64.Byte.Spec
import EvmAsm.Evm64.MSize.Spec
import EvmAsm.Evm64.Calldata.SizeSpec
import EvmAsm.Evm64.Env.Spec
import EvmAsm.Evm64.MStore.UnalignedFramedStackSpec
import EvmAsm.Evm64.MLoad.MemoryRegionStackSpec
import EvmAsm.Evm64.Push.Spec
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

/-- **Looping-body variant of `cleanRetHandlerSpec`.**

    `cleanRetHandlerSpec` assumes the body's step count equals `body.length`
    (`hBodyLen`), which only holds for straight-line bodies. A body with an
    internal loop (e.g. the CALLDATALOAD staging copy, 401 steps over 121
    instructions) executes more steps than it has instructions, so its
    `cpsTripleWithin` bound `nSteps` is decoupled from `body.length`.

    This variant takes `nSteps` free and pins the body's exit PC to the
    *instruction*-derived `base + 4 * body.length` (the address just past the
    body, where the `ADDI x10` tail begins). Everything else is identical to
    `cleanRetHandlerSpec`. Reusable for every looping handler body (EXP, …). -/
theorem cleanRetHandlerSpec'
    {nSteps : Nat} {base : Word} {body : Program} {P Q : Assertion}
    (hQpcFree : Q.pcFree)
    (hBodyLenBound : body.length < 2 ^ 60)
    (h_body : cpsTripleWithin nSteps base (base + BitVec.ofNat 64 (4 * body.length))
                (CodeReq.ofProg base body) P Q)
    (n : BitVec 12)
    (x10_init x1_init : Word) :
    cpsTripleWithin (nSteps + 2) base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base body n)
      (P ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (Q ** (.x10 ↦ᵣ (x10_init + signExtend12 n)) ** (.x1 ↦ᵣ x1_init)) := by
  -- Set up code-region addresses (instruction-derived, not step-derived).
  set addiAddr : Word := base + BitVec.ofNat 64 (4 * body.length) with haddiAddr
  set jalrAddr : Word := addiAddr + 4 with hjalrAddr
  -- Step 1: body, framed with F on the right.
  have h_body_framed :=
    cpsTripleWithin_frameR
      ((.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (by pcFree) h_body
  -- Step 2: ADDI x10 x10 n at addiAddr.
  have h_addi := addi_spec_same_within .x10 x10_init n addiAddr (by decide)
  have h_addi_x1 :=
    cpsTripleWithin_frameR (.x1 ↦ᵣ x1_init) pcFree_regIs h_addi
  have h_addi_framed :=
    cpsTripleWithin_frameL Q hQpcFree h_addi_x1
  -- Step 3: JALR x0 x1 0 (= cc_ret) at jalrAddr.
  have h_jalr := EvmAsm.Evm64.ret_spec_within' jalrAddr x1_init
  have h_jalr_x10 :=
    cpsTripleWithin_frameL (.x10 ↦ᵣ (x10_init + signExtend12 n))
      pcFree_regIs h_jalr
  have h_jalr_framed :=
    cpsTripleWithin_frameL Q hQpcFree h_jalr_x10
  -- 4 * body.length < 2^64 from the < 2^60 length bound.
  have hBodyLenBound64 : (4 * body.length : Nat) < 2 ^ 64 := by
    have : (2 : Nat) ^ 60 * 4 ≤ 2 ^ 64 := by decide
    omega
  -- Disjointness #1: body code vs ADDI singleton.
  have h_disj_body_addi :
      (CodeReq.ofProg base body).Disjoint
        (CodeReq.singleton addiAddr (.ADDI .x10 .x10 n)) := by
    intro a
    by_cases ha : a = addiAddr
    · left
      apply CodeReq.ofProg_none_range
      intro k hk heq
      subst ha
      simp only [addiAddr] at heq
      have hk_bound : (4 * k : Nat) < 4 * body.length := by omega
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
    · intro a
      by_cases ha : a = jalrAddr
      · left
        apply CodeReq.ofProg_none_range
        intro k hk heq
        subst ha
        simp only [jalrAddr, addiAddr] at heq
        have hk_bound : (4 * k : Nat) < 4 * body.length := by omega
        have hk_bound' : (4 * k : Nat) < 2 ^ 64 := by omega
        bv_omega
      · right; simp [CodeReq.singleton, ha]
    · apply CodeReq.Disjoint.singleton
      intro heq
      have : (4 : Word) = 0 := by
        have h := heq
        bv_omega
      exact absurd this (by decide)
  -- Compose (body ;; ADDI) ;; JALR.
  have h_full :=
    cpsTripleWithin_seq h_disj_bodyaddi_jalr h_body_addi h_jalr_framed
  -- Align the CodeReq with cleanRetHandlerCode.
  have hCodeEq :
      ((CodeReq.ofProg base body).union
          (CodeReq.singleton addiAddr (.ADDI .x10 .x10 n))).union
            (CodeReq.singleton jalrAddr (.JALR .x0 .x1 0)) =
        cleanRetHandlerCode base body n := by
    unfold cleanRetHandlerCode cleanRetHandlerProgram
    unfold seq
    have hOuter :
        CodeReq.ofProg base (body ++ (Rv64.ADDI .x10 .x10 n ++ cc_ret)) =
          (CodeReq.ofProg base body).union
            (CodeReq.ofProg (base + BitVec.ofNat 64 (4 * body.length))
              (Rv64.ADDI .x10 .x10 n ++ cc_ret)) :=
      CodeReq.ofProg_append
    rw [hOuter]
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
    rw [← CodeReq.union_assoc]
    have h_addi_len : (Rv64.ADDI .x10 .x10 n).length = 1 := by
      simp [Rv64.ADDI, single]
    have h_addi_off :
        base + BitVec.ofNat 64 (4 * body.length) = addiAddr := by
      simp only [addiAddr]
    rw [h_addi_off]
    have h_jalr_off :
        addiAddr + BitVec.ofNat 64 (4 * (Rv64.ADDI .x10 .x10 n).length) = jalrAddr := by
      rw [h_addi_len]
      simp only [jalrAddr]
      bv_omega
    rw [h_jalr_off]
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
-- 17. Concrete instance — PUSH0 (0x5f)
-- ============================================================================

/-- Handler-level spec for `h_PUSH0` (opcode 0x5f). 5-instruction body
    (`ADDI x12 x12 -32` + 4×`SD x0`, growing the EVM stack by one zero word)
    + 2-instruction tail = 7 RISC-V steps. PUSH0 advances the EVM code
    pointer (`x10`) by 1 and is `x10`-clean (the body never touches `x10`),
    so it lifts directly through the dispatcher's `cleanRetHandler` tail —
    the same template as the arithmetic/stack handlers above. `nsp` is the
    NEW (post-decrement) stack pointer; the four cells at `nsp` are
    overwritten with zero. -/
theorem evmPush0HandlerSpec (nsp base : Word)
    (d0 d1 d2 d3 : Word)
    (x10_init x1_init : Word) :
    cpsTripleWithin 7 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base EvmAsm.Evm64.evm_push0 1)
      (((.x12 ↦ᵣ (nsp + 32)) **
        (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) ** ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((.x12 ↦ᵣ nsp) **
        (nsp ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0))
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  have h_body := EvmAsm.Evm64.evm_push0_spec_within nsp base d0 d1 d2 d3
  simp only [EvmAsm.Evm64.evm_push0_code] at h_body
  have hBodyLen : EvmAsm.Evm64.evm_push0.length = 5 := by decide
  have hExitEq : (base + (20 : Word)) = base + fourTimes 5 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((.x12 ↦ᵣ nsp) **
        (nsp ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 16) ↦ₘ 0) **
        ((nsp + 24) ↦ₘ 0)) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 18. Concrete instance — MSTORE8 (0x53)
-- ============================================================================

/-- Handler-level spec for `h_MSTORE8` (opcode 0x53). 5-instruction body
    (load offset + value limbs from the EVM stack, compute `memBase + offset`,
    store the low byte, pop the two consumed words) + 2-instruction tail =
    7 RISC-V steps. The body is `x10`-clean for any register choice disjoint
    from `x10`/`x1`, so it lifts directly through the `cleanRetHandler` tail
    like the unparameterized handlers above; the working registers
    (`offReg`/`valReg`/`addrReg`/`memBaseReg`) stay as parameters. MSTORE8
    advances the EVM code pointer by 1. -/
theorem evmMStore8HandlerSpec
    (offReg valReg addrReg memBaseReg : Reg)
    (sp memBase offOld valOld addrOld offset valueLow wordOld : Word)
    (base dwordAddr : Word)
    (x10_init x1_init : Word)
    (hoff_ne_x0 : offReg ≠ .x0)
    (hval_ne_x0 : valReg ≠ .x0)
    (haddr_ne_x0 : addrReg ≠ .x0)
    (halign : alignToDword (memBase + offset) = dwordAddr)
    (hvalid : isValidByteAccess (memBase + offset) = true) :
    let targetAddr := memBase + offset
    cpsTripleWithin 7 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base
        (EvmAsm.Evm64.evm_mstore8 offReg valReg addrReg memBaseReg) 1)
      (((.x12 ↦ᵣ sp) ** (memBaseReg ↦ᵣ memBase) **
        (offReg ↦ᵣ offOld) ** (valReg ↦ᵣ valOld) ** (addrReg ↦ᵣ addrOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ offset) **
        ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ valueLow) **
        (dwordAddr ↦ₘ wordOld))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
        (memBaseReg ↦ᵣ memBase) **
        (offReg ↦ᵣ offset) ** (valReg ↦ᵣ valueLow) **
        (addrReg ↦ᵣ targetAddr) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ offset) **
        ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ valueLow) **
        (dwordAddr ↦ₘ
         replaceByte wordOld (byteOffset targetAddr) (valueLow.truncate 8)))
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  intro targetAddr
  have h_body := EvmAsm.Evm64.evm_mstore8_spec_within
    offReg valReg addrReg memBaseReg
    sp memBase offOld valOld addrOld offset valueLow wordOld base dwordAddr
    hoff_ne_x0 hval_ne_x0 haddr_ne_x0 halign hvalid
  simp only [EvmAsm.Evm64.evm_mstore8_code] at h_body
  have hBodyLen :
      (EvmAsm.Evm64.evm_mstore8 offReg valReg addrReg memBaseReg).length = 5 :=
    EvmAsm.Evm64.evm_mstore8_length offReg valReg addrReg memBaseReg
  have hExitEq : (base + (20 : Word)) = base + fourTimes 5 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
        (memBaseReg ↦ᵣ memBase) **
        (offReg ↦ᵣ offset) ** (valReg ↦ᵣ valueLow) **
        (addrReg ↦ᵣ targetAddr) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ offset) **
        ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ valueLow) **
        (dwordAddr ↦ₘ
         replaceByte wordOld (byteOffset targetAddr)
           (valueLow.truncate 8))) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 19. Concrete instance — DUPn (0x80..0x8f)
-- ============================================================================

/-- Handler-level spec for the `h_DUPn` family (opcodes 0x80..0x8f, `1 ≤ n ≤ 16`).
    9-instruction body (`ADDI x12 x12 -32` to grow the stack, then 4 limb
    copies of the nth stack element) + 2-instruction tail = 11 RISC-V steps.
    The body is `x10`-clean (only `x12`/`x7` + memory), but `evm_dup_code` is
    a hand-built union-of-singletons (symbolic `n` blocks `ofProg` reduction),
    so we first bridge it to `ofProg` form via `evm_dup_code_eq_ofProg`, then
    lift through the clean-ret tail. `nsp` is the NEW (post-decrement) stack
    pointer; DUPn advances the EVM code pointer by 1. -/
theorem evmDupHandlerSpec (nsp base : Word) (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (s0 s1 s2 s3 d0 d1 d2 d3 v7 : Word) (x10_init x1_init : Word) :
    cpsTripleWithin 11 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base (EvmAsm.Evm64.evm_dup n) 1)
      (((.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
        (nsp ↦ₘ d0) ** ((nsp+8) ↦ₘ d1) ** ((nsp+16) ↦ₘ d2) ** ((nsp+24) ↦ₘ d3) **
        ((nsp + BitVec.ofNat 64 (n*32))    ↦ₘ s0) **
        ((nsp + BitVec.ofNat 64 (n*32+8))  ↦ₘ s1) **
        ((nsp + BitVec.ofNat 64 (n*32+16)) ↦ₘ s2) **
        ((nsp + BitVec.ofNat 64 (n*32+24)) ↦ₘ s3))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ s3) **
        (nsp ↦ₘ s0) ** ((nsp+8) ↦ₘ s1) ** ((nsp+16) ↦ₘ s2) ** ((nsp+24) ↦ₘ s3) **
        ((nsp + BitVec.ofNat 64 (n*32))    ↦ₘ s0) **
        ((nsp + BitVec.ofNat 64 (n*32+8))  ↦ₘ s1) **
        ((nsp + BitVec.ofNat 64 (n*32+16)) ↦ₘ s2) **
        ((nsp + BitVec.ofNat 64 (n*32+24)) ↦ₘ s3))
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  have h_body := EvmAsm.Evm64.evm_dup_spec_within nsp base n hn1 hn16
    s0 s1 s2 s3 d0 d1 d2 d3 v7
  rw [EvmAsm.Evm64.evm_dup_code_eq_ofProg] at h_body
  have hBodyLen : (EvmAsm.Evm64.evm_dup n).length = 9 := EvmAsm.Evm64.evm_dup_length n
  have hExitEq : (base + (36 : Word)) = base + fourTimes 9 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ s3) **
        (nsp ↦ₘ s0) ** ((nsp+8) ↦ₘ s1) ** ((nsp+16) ↦ₘ s2) ** ((nsp+24) ↦ₘ s3) **
        ((nsp + BitVec.ofNat 64 (n*32))    ↦ₘ s0) **
        ((nsp + BitVec.ofNat 64 (n*32+8))  ↦ₘ s1) **
        ((nsp + BitVec.ofNat 64 (n*32+16)) ↦ₘ s2) **
        ((nsp + BitVec.ofNat 64 (n*32+24)) ↦ₘ s3)) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 20. Concrete instance — SWAPn (0x90..0x9f)
-- ============================================================================

/-- Handler-level spec for the `h_SWAPn` family (opcodes 0x90..0x9f, `1 ≤ n ≤ 16`).
    16-instruction body (4 limb quads swapping the top stack word with the
    nth) + 2-instruction tail = 18 RISC-V steps. `x10`-clean (only `x12`/`x7`/
    `x6` + memory); `evm_swap_code` is a union-of-singletons, so we bridge it
    to `ofProg` via `evm_swap_code_eq_ofProg`, then lift through the clean-ret
    tail. The stack pointer is unchanged (swap preserves depth); SWAPn advances
    the EVM code pointer by 1. -/
theorem evmSwapHandlerSpec (sp base : Word) (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 : Word) (x10_init x1_init : Word) :
    cpsTripleWithin 18 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base (EvmAsm.Evm64.evm_swap n) 1)
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
        (sp ↦ₘ a0) ** ((sp+8) ↦ₘ a1) ** ((sp+16) ↦ₘ a2) ** ((sp+24) ↦ₘ a3) **
        ((sp + BitVec.ofNat 64 (n*32))    ↦ₘ b0) **
        ((sp + BitVec.ofNat 64 (n*32+8))  ↦ₘ b1) **
        ((sp + BitVec.ofNat 64 (n*32+16)) ↦ₘ b2) **
        ((sp + BitVec.ofNat 64 (n*32+24)) ↦ₘ b3))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a3) ** (.x6 ↦ᵣ b3) **
        (sp ↦ₘ b0) ** ((sp+8) ↦ₘ b1) ** ((sp+16) ↦ₘ b2) ** ((sp+24) ↦ₘ b3) **
        ((sp + BitVec.ofNat 64 (n*32))    ↦ₘ a0) **
        ((sp + BitVec.ofNat 64 (n*32+8))  ↦ₘ a1) **
        ((sp + BitVec.ofNat 64 (n*32+16)) ↦ₘ a2) **
        ((sp + BitVec.ofNat 64 (n*32+24)) ↦ₘ a3))
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  have h_body := EvmAsm.Evm64.evm_swap_spec_within sp base n hn1 hn16
    a0 a1 a2 a3 b0 b1 b2 b3 v7 v6
  rw [EvmAsm.Evm64.evm_swap_code_eq_ofProg] at h_body
  have hBodyLen : (EvmAsm.Evm64.evm_swap n).length = 16 := EvmAsm.Evm64.evm_swap_length n
  have hExitEq : (base + (64 : Word)) = base + fourTimes 16 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a3) ** (.x6 ↦ᵣ b3) **
        (sp ↦ₘ b0) ** ((sp+8) ↦ₘ b1) ** ((sp+16) ↦ₘ b2) ** ((sp+24) ↦ₘ b3) **
        ((sp + BitVec.ofNat 64 (n*32))    ↦ₘ a0) **
        ((sp + BitVec.ofNat 64 (n*32+8))  ↦ₘ a1) **
        ((sp + BitVec.ofNat 64 (n*32+16)) ↦ₘ a2) **
        ((sp + BitVec.ofNat 64 (n*32+24)) ↦ₘ a3)) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 17. Concrete instance — MUL (0x02), via the reload-handler lift
-- ============================================================================

/-- Handler-level spec for `h_MUL` (opcode 0x02). The MUL body CLOBBERS the
    EVM code pointer `x10` (it is used as a multiplication scratch register, so
    `evmMulStackPost` only `regOwn`s it) and so cannot use the clean-ret tail.
    Instead it lifts through `reloadRetHandlerSpec`: the handler saves `x10`
    into `save`, runs the 63-instruction `evm_mul` body, reloads `x10`, advances
    the EVM code pointer by 1, and returns. First application of the reload
    lift; the same recipe (`rw [evm_X_code_eq_ofProg]`, factor P/Q via `xperm`,
    apply `reloadRetHandlerSpec`) handles all 7 x10-clobbering opcodes. -/
theorem evmMulHandlerSpec (sp base : Word) (a b : EvmAsm.Evm64.EvmWord)
    (v5 v6 v7 v11 : Word) (save : Reg) (hsave_ne_x0 : save ≠ .x0)
    (x10_init s_init x1_init : Word) :
    cpsTripleWithin (63 + 4) base (x1_init &&& ~~~1)
      (CodeReq.ofProg base (saveReloadHandlerProgram EvmAsm.Evm64.evm_mul 1 save))
      ((save ↦ᵣ s_init) ** (.x10 ↦ᵣ x10_init) **
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
         EvmAsm.Evm64.evmWordIs sp a ** EvmAsm.Evm64.evmWordIs (sp + 32) b)
        ** (.x1 ↦ᵣ x1_init))
      ((save ↦ᵣ x10_init) ** (.x10 ↦ᵣ (x10_init + signExtend12 1)) **
        ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
         memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) ** memOwn (sp + 24) **
         EvmAsm.Evm64.evmWordIs (sp + 32) (a * b))
        ** (.x1 ↦ᵣ x1_init)) := by
  have h_body0 := EvmAsm.Evm64.evm_mul_stack_spec_within sp (base + 4) a b v5 v6 v7 x10_init v11
  rw [EvmAsm.Evm64.evm_mul_code_eq_ofProg] at h_body0
  unfold EvmAsm.Evm64.evmMulStackPost at h_body0
  have h_body : cpsTripleWithin 63 (base + 4) ((base + 4) + (252 : Word))
      (CodeReq.ofProg (base + 4) EvmAsm.Evm64.evm_mul)
      ((.x10 ↦ᵣ x10_init) **
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
         EvmAsm.Evm64.evmWordIs sp a ** EvmAsm.Evm64.evmWordIs (sp + 32) b))
      (regOwn .x10 **
        ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
         memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) ** memOwn (sp + 24) **
         EvmAsm.Evm64.evmWordIs (sp + 32) (a * b))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) h_body0
  have hlen : EvmAsm.Evm64.evm_mul.length = 63 := by decide
  exact reloadRetHandlerSpec (by pcFree) (by pcFree) hsave_ne_x0 hlen (by decide) h_body
    s_init x1_init

-- ============================================================================
-- 18. Concrete instance — SIGNEXTEND (0x0b), via the reload-handler lift
-- ============================================================================

/-- Handler-level spec for `h_SIGNEXTEND` (opcode 0x0b). The body clobbers `x10`
    (post `regOwn`s it), so it lifts through `reloadRetHandlerSpec`. The body is
    branchy — its step bound (28) is below its instruction count (48) — so we
    first bump the bound to the length via `cpsTripleWithin_mono_nSteps`, then
    apply the reload lift. -/
theorem evmSignExtendHandlerSpec (sp base : Word) (b x : EvmAsm.Evm64.EvmWord)
    (v5 v6 : Word) (save : Reg) (hsave_ne_x0 : save ≠ .x0)
    (x10_init s_init x1_init : Word) :
    cpsTripleWithin (48 + 4) base (x1_init &&& ~~~1)
      (CodeReq.ofProg base (saveReloadHandlerProgram EvmAsm.Evm64.evm_signextend 1 save))
      ((save ↦ᵣ s_init) ** (.x10 ↦ᵣ x10_init) **
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
         EvmAsm.Evm64.evmWordIs sp b ** EvmAsm.Evm64.evmWordIs (sp + 32) x)
        ** (.x1 ↦ᵣ x1_init))
      ((save ↦ᵣ x10_init) ** (.x10 ↦ᵣ (x10_init + signExtend12 1)) **
        ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0 : Word)) **
         EvmAsm.Evm64.evmWordIs sp b **
         EvmAsm.Evm64.evmWordIs (sp + 32) (EvmAsm.Evm64.EvmWord.signextend b x))
        ** (.x1 ↦ᵣ x1_init)) := by
  have h0 := EvmAsm.Evm64.evm_signextend_stack_spec_within sp (base + 4) b x v5 v6 x10_init
  simp only [EvmAsm.Evm64.signextCode] at h0
  have h1 := cpsTripleWithin_mono_nSteps (show (28 : Nat) ≤ 48 by omega) h0
  have h_body : cpsTripleWithin 48 (base + 4) ((base + 4) + (192 : Word))
      (CodeReq.ofProg (base + 4) EvmAsm.Evm64.evm_signextend)
      ((.x10 ↦ᵣ x10_init) **
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
         EvmAsm.Evm64.evmWordIs sp b ** EvmAsm.Evm64.evmWordIs (sp + 32) x))
      (regOwn .x10 **
        ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0 : Word)) **
         EvmAsm.Evm64.evmWordIs sp b **
         EvmAsm.Evm64.evmWordIs (sp + 32) (EvmAsm.Evm64.EvmWord.signextend b x))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) h1
  have hlen : EvmAsm.Evm64.evm_signextend.length = 48 := by decide
  exact reloadRetHandlerSpec (by pcFree) (by pcFree) hsave_ne_x0 hlen (by decide) h_body
    s_init x1_init

-- ============================================================================
-- 19. Concrete instance — BYTE (0x1a), via the reload-handler lift
-- ============================================================================

/-- Handler-level spec for `h_BYTE` (opcode 0x1a). Like SIGNEXTEND: the body
    clobbers `x10` and is branchy (step bound 29 < instruction count 45), so we
    bump the bound to the length and lift through `reloadRetHandlerSpec`. -/
theorem evmByteHandlerSpec (sp base : Word) (idx val : EvmAsm.Evm64.EvmWord)
    (v5 v6 : Word) (save : Reg) (hsave_ne_x0 : save ≠ .x0)
    (x10_init s_init x1_init : Word) :
    cpsTripleWithin (45 + 4) base (x1_init &&& ~~~1)
      (CodeReq.ofProg base (saveReloadHandlerProgram EvmAsm.Evm64.evm_byte 1 save))
      ((save ↦ᵣ s_init) ** (.x10 ↦ᵣ x10_init) **
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
         EvmAsm.Evm64.evmWordIs sp idx ** EvmAsm.Evm64.evmWordIs (sp + 32) val)
        ** (.x1 ↦ᵣ x1_init))
      ((save ↦ᵣ x10_init) ** (.x10 ↦ᵣ (x10_init + signExtend12 1)) **
        ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0 : Word)) **
         EvmAsm.Evm64.evmWordIs sp idx **
         EvmAsm.Evm64.evmWordIs (sp + 32) (EvmAsm.Evm64.EvmWord.byte idx val))
        ** (.x1 ↦ᵣ x1_init)) := by
  have h0 := EvmAsm.Evm64.evm_byte_stack_spec_within sp (base + 4) idx val v5 v6 x10_init
  simp only [EvmAsm.Evm64.evm_byte_code] at h0
  have h1 := cpsTripleWithin_mono_nSteps (show (29 : Nat) ≤ 45 by omega) h0
  have h_body : cpsTripleWithin 45 (base + 4) ((base + 4) + (180 : Word))
      (CodeReq.ofProg (base + 4) EvmAsm.Evm64.evm_byte)
      ((.x10 ↦ᵣ x10_init) **
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
         EvmAsm.Evm64.evmWordIs sp idx ** EvmAsm.Evm64.evmWordIs (sp + 32) val))
      (regOwn .x10 **
        ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0 : Word)) **
         EvmAsm.Evm64.evmWordIs sp idx **
         EvmAsm.Evm64.evmWordIs (sp + 32) (EvmAsm.Evm64.EvmWord.byte idx val))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) h1
  have hlen : EvmAsm.Evm64.evm_byte.length = 45 := by decide
  exact reloadRetHandlerSpec (by pcFree) (by pcFree) hsave_ne_x0 hlen (by decide) h_body
    s_init x1_init
-- 21. Concrete instance — MSIZE (0x59)
-- ============================================================================

/-- Handler-level spec for `h_MSIZE` (opcode 0x59). 6-instruction body
    (load the memory-size cell, grow the stack by one word holding the size
    as its low limb + three zero limbs) + 2-instruction tail = 8 RISC-V
    steps. `x10`-clean; `evm_msize_code` is already `ofProg`-based, so it
    lifts directly via `cleanRetHandlerSpec` with the working registers
    (`sizeReg`/`tempReg`) kept as parameters. `nsp` is the NEW
    (post-decrement) stack pointer; MSIZE advances the EVM code pointer by 1. -/
theorem evmMSizeHandlerSpec
    (sizeReg tempReg : Reg) (htemp_ne_x0 : tempReg ≠ .x0)
    (nsp base sizeLoc tempOld : Word) (sizeBytes : Nat)
    (d0 d1 d2 d3 : Word) (x10_init x1_init : Word) :
    cpsTripleWithin 8 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base (EvmAsm.Evm64.evm_msize sizeReg tempReg) 1)
      (((sizeReg ↦ᵣ sizeLoc) ** (tempReg ↦ᵣ tempOld) **
        (.x12 ↦ᵣ (nsp + 32)) **
        (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
        ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
        EvmAsm.Evm64.evmMemSizeIs sizeLoc sizeBytes)
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((sizeReg ↦ᵣ sizeLoc) ** (tempReg ↦ᵣ BitVec.ofNat 64 sizeBytes) **
        (.x12 ↦ᵣ nsp) **
        (nsp ↦ₘ BitVec.ofNat 64 sizeBytes) ** ((nsp + 8) ↦ₘ 0) **
        ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0) **
        EvmAsm.Evm64.evmMemSizeIs sizeLoc sizeBytes)
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  have h_body := EvmAsm.Evm64.evm_msize_spec_within sizeReg tempReg htemp_ne_x0
    nsp base sizeLoc tempOld sizeBytes d0 d1 d2 d3
  simp only [EvmAsm.Evm64.evm_msize_code] at h_body
  have hBodyLen : (EvmAsm.Evm64.evm_msize sizeReg tempReg).length = 6 :=
    EvmAsm.Evm64.evm_msize_length sizeReg tempReg
  have hExitEq : (base + (24 : Word)) = base + fourTimes 6 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((sizeReg ↦ᵣ sizeLoc) ** (tempReg ↦ᵣ BitVec.ofNat 64 sizeBytes) **
        (.x12 ↦ᵣ nsp) **
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
-- 22. Concrete instance — environment loads (h_ADDRESS/h_CALLER/… family)
-- ============================================================================

/-- Handler-level spec for the single-field environment-load handlers
    (ADDRESS 0x30, CALLER 0x33, CALLVALUE 0x34, …, parameterized by
    `field : SimpleEnvField`). 9-instruction body (`ADDI x12 x12 -32` to grow
    the stack, then 4 limb copies of the env field) + 2-instruction tail =
    11 RISC-V steps. `x10`-clean; `evm_env_load_code` is `ofProg`-based, so it
    lifts directly via `cleanRetHandlerSpec` with `envBaseReg`/`tmpReg`/`field`
    kept as parameters. `nsp` is the NEW (post-decrement) stack pointer; the
    handler advances the EVM code pointer by 1. -/
theorem evmEnvLoadHandlerSpec
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (envAddr nsp tempOld base : Word) (env : EvmAsm.Evm64.EvmEnv)
    (field : EvmAsm.Evm64.Env.SimpleEnvField)
    (d0 d1 d2 d3 : Word) (x10_init x1_init : Word) :
    cpsTripleWithin 11 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base
        (EvmAsm.Evm64.Env.evm_env_load envBaseReg tmpReg field) 1)
      (((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
        (.x12 ↦ᵣ (nsp + 32)) **
        ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 0)) ↦ₘ
           (field.value env).getLimbN 0) **
        ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 1)) ↦ₘ
           (field.value env).getLimbN 1) **
        ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 2)) ↦ₘ
           (field.value env).getLimbN 2) **
        ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 3)) ↦ₘ
           (field.value env).getLimbN 3) **
        ((nsp + BitVec.ofNat 64 (8 * 0)) ↦ₘ d0) **
        ((nsp + BitVec.ofNat 64 (8 * 1)) ↦ₘ d1) **
        ((nsp + BitVec.ofNat 64 (8 * 2)) ↦ₘ d2) **
        ((nsp + BitVec.ofNat 64 (8 * 3)) ↦ₘ d3))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ (field.value env).getLimbN 3) **
        (.x12 ↦ᵣ nsp) **
        ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 0)) ↦ₘ
           (field.value env).getLimbN 0) **
        ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 1)) ↦ₘ
           (field.value env).getLimbN 1) **
        ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 2)) ↦ₘ
           (field.value env).getLimbN 2) **
        ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 3)) ↦ₘ
           (field.value env).getLimbN 3) **
        ((nsp + BitVec.ofNat 64 (8 * 0)) ↦ₘ (field.value env).getLimbN 0) **
        ((nsp + BitVec.ofNat 64 (8 * 1)) ↦ₘ (field.value env).getLimbN 1) **
        ((nsp + BitVec.ofNat 64 (8 * 2)) ↦ₘ (field.value env).getLimbN 2) **
        ((nsp + BitVec.ofNat 64 (8 * 3)) ↦ₘ (field.value env).getLimbN 3))
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  have h_body := EvmAsm.Evm64.Env.evm_env_load_spec_within
    envBaseReg tmpReg htmp_ne_x0 envAddr nsp tempOld env field d0 d1 d2 d3 base
  simp only [EvmAsm.Evm64.Env.evm_env_load_code] at h_body
  have hBodyLen :
      (EvmAsm.Evm64.Env.evm_env_load envBaseReg tmpReg field).length = 9 :=
    EvmAsm.Evm64.Env.evm_env_load_length envBaseReg tmpReg field
  have hExitEq : (base + (36 : Word)) = base + fourTimes 9 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ (field.value env).getLimbN 3) **
        (.x12 ↦ᵣ nsp) **
        ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 0)) ↦ₘ
           (field.value env).getLimbN 0) **
        ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 1)) ↦ₘ
           (field.value env).getLimbN 1) **
        ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 2)) ↦ₘ
           (field.value env).getLimbN 2) **
        ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 3)) ↦ₘ
           (field.value env).getLimbN 3) **
        ((nsp + BitVec.ofNat 64 (8 * 0)) ↦ₘ (field.value env).getLimbN 0) **
        ((nsp + BitVec.ofNat 64 (8 * 1)) ↦ₘ (field.value env).getLimbN 1) **
        ((nsp + BitVec.ofNat 64 (8 * 2)) ↦ₘ (field.value env).getLimbN 2) **
        ((nsp + BitVec.ofNat 64 (8 * 3)) ↦ₘ
           (field.value env).getLimbN 3)) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 20. Concrete instance — MSTORE (0x52)
-- ============================================================================

/-- Handler-level spec for `h_MSTORE` (opcode 0x52). `x10`-clean, so it lifts
    through the clean-ret tail like the other memory ops; the underlying body
    spec is the full `evm_mstore_stack_spec_within` (71-instruction unaligned
    framed store). Working registers + the limb window data stay as parameters. -/
theorem evmMStoreHandlerSpec
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase byteOld accOld : Word)
    (offsetWord valueWord : EvmAsm.Evm64.EvmWord) (rest : List EvmAsm.Evm64.EvmWord)
    (offsetHigh1 offsetHigh2 offsetHigh3 : Word)
    (limb0 limb1 limb2 limb3 : Word)
    (loAddr0 hiAddr0 loVal0 hiVal0 : Word)
    (loAddr1 hiAddr1 loVal1 hiVal1 : Word)
    (loAddr2 hiAddr2 loVal2 hiVal2 : Word)
    (loAddr3 hiAddr3 loVal3 hiVal3 : Word)
    (start : Nat) (base : Word) (x10_init x1_init : Word)
    (h_offset0 : offsetWord.getLimbN 0 = offset)
    (h_offset1 : offsetWord.getLimbN 1 = offsetHigh1)
    (h_offset2 : offsetWord.getLimbN 2 = offsetHigh2)
    (h_offset3 : offsetWord.getLimbN 3 = offsetHigh3)
    (h_value0 : valueWord.getLimbN 0 = limb0)
    (h_value1 : valueWord.getLimbN 1 = limb1)
    (h_value2 : valueWord.getLimbN 2 = limb2)
    (h_value3 : valueWord.getLimbN 3 = limb3)
    (h_off_ne_x0 : offReg ≠ .x0) (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window0 : EvmAsm.Evm64.mstoreLimbWindowOk (memBase + offset) loAddr0 hiAddr0 start 24 25 26 27 28 29 30 31)
    (h_window1 : EvmAsm.Evm64.mstoreLimbWindowOk (memBase + offset) loAddr1 hiAddr1 start 16 17 18 19 20 21 22 23)
    (h_window2 : EvmAsm.Evm64.mstoreLimbWindowOk (memBase + offset) loAddr2 hiAddr2 start 8 9 10 11 12 13 14 15)
    (h_window3 : EvmAsm.Evm64.mstoreLimbWindowOk (memBase + offset) loAddr3 hiAddr3 start 0 1 2 3 4 5 6 7) :
    let stored0 := EvmAsm.Evm64.MStore.mstoreDwordPairStoreLimb loVal0 hiVal0 limb0 start
    let stored1 := EvmAsm.Evm64.MStore.mstoreDwordPairStoreLimb loVal1 hiVal1 limb1 start
    let stored2 := EvmAsm.Evm64.MStore.mstoreDwordPairStoreLimb loVal2 hiVal2 limb2 start
    let stored3 := EvmAsm.Evm64.MStore.mstoreDwordPairStoreLimb loVal3 hiVal3 limb3 start
    cpsTripleWithin ((2 + (17 + 17 + 17 + 17) + 1) + 2) base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base
        (EvmAsm.Evm64.evm_mstore offReg valReg byteReg accReg addrReg memBaseReg) 1)
      (((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        EvmAsm.Evm64.evmStackIs sp (offsetWord :: valueWord :: rest)) **
       ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
        (loAddr0 ↦ₘ loVal0) ** (hiAddr0 ↦ₘ hiVal0) **
        (loAddr1 ↦ₘ loVal1) ** (hiAddr1 ↦ₘ hiVal1) **
        (loAddr2 ↦ₘ loVal2) ** (hiAddr2 ↦ₘ hiVal2) **
        (loAddr3 ↦ₘ loVal3) ** (hiAddr3 ↦ₘ hiVal3)))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      ((((.x12 : Reg) ↦ᵣ (sp + 64)) **
        EvmAsm.Evm64.evmStackIs (sp + 64) rest **
        EvmAsm.Evm64.evmWordIs sp offsetWord ** EvmAsm.Evm64.evmWordIs (sp + 32) valueWord **
        ((offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) **
         (addrReg ↦ᵣ (memBase + offset)) **
         (byteReg ↦ᵣ limb3) ** (accReg ↦ᵣ limb3) **
         (loAddr3 ↦ₘ stored3.1) ** (hiAddr3 ↦ₘ stored3.2) **
         (loAddr0 ↦ₘ stored0.1) ** (hiAddr0 ↦ₘ stored0.2) **
         (loAddr1 ↦ₘ stored1.1) ** (hiAddr1 ↦ₘ stored1.2) **
         (loAddr2 ↦ₘ stored2.1) ** (hiAddr2 ↦ₘ stored2.2)))
       ** (.x10 ↦ᵣ (x10_init + signExtend12 1)) ** (.x1 ↦ᵣ x1_init)) := by
  intro stored0 stored1 stored2 stored3
  have h_body := EvmAsm.Evm64.evm_mstore_stack_spec_within
    offReg valReg byteReg accReg addrReg memBaseReg
    sp offset offOld addrOld memBase byteOld accOld offsetWord valueWord rest
    offsetHigh1 offsetHigh2 offsetHigh3 limb0 limb1 limb2 limb3
    loAddr0 hiAddr0 loVal0 hiVal0 loAddr1 hiAddr1 loVal1 hiVal1
    loAddr2 hiAddr2 loVal2 hiVal2 loAddr3 hiAddr3 loVal3 hiVal3 start base
    h_offset0 h_offset1 h_offset2 h_offset3 h_value0 h_value1 h_value2 h_value3
    h_off_ne_x0 h_addr_ne_x0 h_byte_ne_x0 h_acc_ne_x0
    h_window0 h_window1 h_window2 h_window3
  simp only [EvmAsm.Evm64.evm_mstore_code] at h_body
  have hBodyLen : (EvmAsm.Evm64.evm_mstore offReg valReg byteReg accReg addrReg memBaseReg).length
      = 2 + (17 + 17 + 17 + 17) + 1 := by
    rw [EvmAsm.Evm64.evm_mstore_length]
  have hExitEq : (base + (284 : Word)) = base + fourTimes (2 + (17 + 17 + 17 + 17) + 1) := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((((.x12 : Reg) ↦ᵣ (sp + 64)) **
        EvmAsm.Evm64.evmStackIs (sp + 64) rest **
        EvmAsm.Evm64.evmWordIs sp offsetWord ** EvmAsm.Evm64.evmWordIs (sp + 32) valueWord **
        ((offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) **
         (addrReg ↦ᵣ (memBase + offset)) **
         (byteReg ↦ᵣ limb3) ** (accReg ↦ᵣ limb3) **
         (loAddr3 ↦ₘ stored3.1) ** (hiAddr3 ↦ₘ stored3.2) **
         (loAddr0 ↦ₘ stored0.1) ** (hiAddr0 ↦ₘ stored0.2) **
         (loAddr1 ↦ₘ stored1.1) ** (hiAddr1 ↦ₘ stored1.2) **
         (loAddr2 ↦ₘ stored2.1) ** (hiAddr2 ↦ₘ stored2.2)))) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  exact h

-- ============================================================================
-- 21. Concrete instance — MLOAD (0x51)
-- ============================================================================

/-- Handler-level MLOAD spec against the folded EVM-memory assertion. -/
theorem evmMLoadHandlerSpec
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase byteOld accOld : Word)
    (offsetWord : EvmAsm.Evm64.EvmWord) (rest : List EvmAsm.Evm64.EvmWord)
    (dstOld1 dstOld2 dstOld3 : Word)
    (capacity : Nat) (contents : List (BitVec 8))
    (base x10_init x1_init : Word)
    (h_offset0 : offsetWord.getLimbN 0 = offset)
    (h_offset1 : offsetWord.getLimbN 1 = dstOld1)
    (h_offset2 : offsetWord.getLimbN 2 = dstOld2)
    (h_offset3 : offsetWord.getLimbN 3 = dstOld3)
    (h_off_ne_x0 : offReg ≠ .x0) (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (hlen : contents.length = capacity)
    (halignB : memBase.toNat % 8 = 0)
    (hin : 8 * (offset.toNat / 8) + 40 ≤ contents.length)
    (hbound : memBase.toNat + contents.length ≤ 2 ^ 64)
    (hvalid : ∀ i : Nat, i < contents.length →
      isValidMemAddr (memBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin ((2 + (23 + 23 + 23 + 23)) + 2) base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base
        (EvmAsm.Evm64.evm_mload offReg byteReg accReg addrReg memBaseReg) 1)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       EvmAsm.Evm64.evmStackIs sp (offsetWord :: rest) **
       (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       EvmAsm.Evm64.evmMemoryIs memBase capacity contents **
       (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (EvmAsm.Evm64.evmStackIs sp
         (EvmAsm.Evm64.evmMemoryReadWord contents offset.toNat :: rest) **
       ((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (byteReg ↦ᵣ
         (getByteAt contents (offset.toNat + 7)).zeroExtend 64) **
       (accReg ↦ᵣ
         (EvmAsm.Evm64.evmMemoryReadWord contents offset.toNat).getLimbN 3) **
       EvmAsm.Evm64.evmMemoryIs memBase capacity contents **
       (.x10 ↦ᵣ (x10_init + signExtend12 1)) ** (.x1 ↦ᵣ x1_init)) := by
  have h_body := EvmAsm.Evm64.evm_mload_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset offOld addrOld memBase byteOld accOld offsetWord rest
    dstOld1 dstOld2 dstOld3 capacity contents base
    h_offset0 h_offset1 h_offset2 h_offset3
    h_off_ne_x0 h_addr_ne_x0 h_byte_ne_x0 h_acc_ne_x0
    hlen halignB hin hbound hvalid
  simp only [EvmAsm.Evm64.evm_mload_code] at h_body
  have hBodyLen :
      (EvmAsm.Evm64.evm_mload offReg byteReg accReg addrReg memBaseReg).length =
        2 + (23 + 23 + 23 + 23) := by
    rw [EvmAsm.Evm64.evm_mload_length]
  have hExitEq : (base + (376 : Word)) =
      base + fourTimes (2 + (23 + 23 + 23 + 23)) := by
    simp only [fourTimes]
    bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (EvmAsm.Evm64.evmStackIs sp
         (EvmAsm.Evm64.evmMemoryReadWord contents offset.toNat :: rest) **
       ((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (byteReg ↦ᵣ
         (getByteAt contents (offset.toNat + 7)).zeroExtend 64) **
       (accReg ↦ᵣ
         (EvmAsm.Evm64.evmMemoryReadWord contents offset.toNat).getLimbN 3) **
       EvmAsm.Evm64.evmMemoryIs memBase capacity contents : Assertion).pcFree := by
    pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide)
    h_body 1 x10_init x1_init
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    h

-- ============================================================================
-- 22. Passthrough handler lift (x10-preserving bodies, e.g. PUSHn)
-- ============================================================================

/-- Handler lift for an x10-PRESERVING body: the body reads `x10` (e.g. PUSHn
    fetching its immediate from the EVM code pointer) and leaves it unchanged,
    so `x10` appears in the body spec's P and Q at the same value. Threads `x10`
    through the body, then advances it by `n` and returns. The third handler
    pattern, between `cleanRetHandlerSpec` (x10 framed out) and
    `reloadRetHandlerSpec` (x10 clobbered). -/
theorem passthroughRetHandlerSpec
    {nSteps : Nat} {base : Word} {body : List Instr} {S : Assertion} {n : BitVec 12}
    {R : Assertion} {x10_init : Word}
    (hSpcFree : S.pcFree)
    (hBodyLen : body.length = nSteps)
    (hBodyLenBound : nSteps < 2 ^ 60)
    (h_body : cpsTripleWithin nSteps base (base + fourTimes nSteps)
                (CodeReq.ofProg base body)
                ((.x10 ↦ᵣ x10_init) ** R) ((.x10 ↦ᵣ x10_init) ** S))
    (x1_init : Word) :
    cpsTripleWithin (nSteps + 2) base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base body n)
      ((.x10 ↦ᵣ x10_init) ** R ** (.x1 ↦ᵣ x1_init))
      ((.x10 ↦ᵣ (x10_init + signExtend12 n)) ** S ** (.x1 ↦ᵣ x1_init)) := by
  have hNBound : (4 * nSteps : Nat) < 2 ^ 64 := by
    have : (2:Nat)^60 * 4 ≤ 2^64 := by decide
    omega
  have p1 :
      cpsTripleWithin nSteps base (base + fourTimes nSteps) (CodeReq.ofProg base body)
        ((.x10 ↦ᵣ x10_init) ** R ** (.x1 ↦ᵣ x1_init))
        ((.x10 ↦ᵣ x10_init) ** S ** (.x1 ↦ᵣ x1_init)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR ((.x1 ↦ᵣ x1_init)) pcFree_regIs h_body)
  have p2 :
      cpsTripleWithin 1 (base + fourTimes nSteps) ((base + fourTimes nSteps) + 4)
        (CodeReq.singleton (base + fourTimes nSteps) (.ADDI .x10 .x10 n))
        ((.x10 ↦ᵣ x10_init) ** S ** (.x1 ↦ᵣ x1_init))
        ((.x10 ↦ᵣ (x10_init + signExtend12 n)) ** S ** (.x1 ↦ᵣ x1_init)) := by
    have core := addi_spec_same_within .x10 x10_init n (base + fourTimes nSteps) (by decide)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR (S ** (.x1 ↦ᵣ x1_init)) (pcFree_sepConj hSpcFree pcFree_regIs) core)
  have p3 :
      cpsTripleWithin 1 ((base + fourTimes nSteps) + 4) (x1_init &&& ~~~1)
        (CodeReq.singleton ((base + fourTimes nSteps) + 4) (.JALR .x0 .x1 0))
        ((.x10 ↦ᵣ (x10_init + signExtend12 n)) ** S ** (.x1 ↦ᵣ x1_init))
        ((.x10 ↦ᵣ (x10_init + signExtend12 n)) ** S ** (.x1 ↦ᵣ x1_init)) := by
    have core := EvmAsm.Evm64.ret_spec_within' ((base + fourTimes nSteps) + 4) x1_init
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameL ((.x10 ↦ᵣ (x10_init + signExtend12 n)) ** S)
        (pcFree_sepConj pcFree_regIs hSpcFree) core)
  have hbody_none : ∀ (a : Word),
      (∀ k : Nat, k < nSteps → a ≠ base + BitVec.ofNat 64 (4 * k)) →
      CodeReq.ofProg base body a = none := by
    intro a ha; apply CodeReq.ofProg_none_range; intro k hk; rw [hBodyLen] at hk; exact ha k hk
  have d12 : (CodeReq.ofProg base body).Disjoint
      (CodeReq.singleton (base + fourTimes nSteps) (.ADDI .x10 .x10 n)) := by
    apply CodeReq.Disjoint.ofProg_singleton
    apply hbody_none; intro k hk heq
    simp only [fourTimes] at heq
    have : (4 * k : Nat) < 2 ^ 64 := by omega
    bv_omega
  have d123 : ((CodeReq.ofProg base body).union
      (CodeReq.singleton (base + fourTimes nSteps) (.ADDI .x10 .x10 n))).Disjoint
      (CodeReq.singleton ((base + fourTimes nSteps) + 4) (.JALR .x0 .x1 0)) := by
    apply CodeReq.Disjoint.union_left
    · apply CodeReq.Disjoint.ofProg_singleton
      apply hbody_none; intro k hk heq
      simp only [fourTimes] at heq
      have : (4 * k : Nat) < 2 ^ 64 := by omega
      bv_omega
    · apply CodeReq.Disjoint.singleton; bv_omega
  have s12 := cpsTripleWithin_seq d12 p1 p2
  have s123 := cpsTripleWithin_seq d123 s12 p3
  have hCodeEq :
      ((CodeReq.ofProg base body).union
        (CodeReq.singleton (base + fourTimes nSteps) (.ADDI .x10 .x10 n))).union
        (CodeReq.singleton ((base + fourTimes nSteps) + 4) (.JALR .x0 .x1 0))
      = cleanRetHandlerCode base body n := by
    unfold cleanRetHandlerCode cleanRetHandlerProgram cc_ret
    change ((CodeReq.ofProg base body).union _).union _ = CodeReq.ofProg base
      (body ++ ([Instr.ADDI .x10 .x10 n] ++ [Instr.JALR .x0 .x1 0]))
    rw [CodeReq.ofProg_append, CodeReq.ofProg_append]
    simp only [CodeReq.ofProg_singleton, List.length_cons, List.length_nil,
      hBodyLen, fourTimes, ← CodeReq.union_assoc]
    repeat' congr 1
  rw [← hCodeEq, show nSteps + 2 = nSteps + 1 + 1 from by omega]
  exact s123

-- ============================================================================
-- 23. Concrete instance — PUSH1 (0x60), via the passthrough lift
-- ============================================================================

/-- Handler-level spec for `h_PUSH1` (opcode 0x60). PUSH1 reads its 1 immediate
    byte from the EVM code pointer `x10` (= `codePtr`) and leaves `x10`
    unchanged, then the dispatcher advances `x10` by 2 (opcode + 1 immediate).
    First application of `passthroughRetHandlerSpec`; the same recipe covers the
    PUSH1..32 family (`evm_push n`, advance `n+1`). -/
theorem evmPush1HandlerSpec
    (sp codePtr v7Old d0 d1 d2 d3 codeWord codeDwordAddr : Word)
    (base x1_init : Word) (rest : List EvmAsm.Evm64.EvmWord) (byteVal : BitVec 8)
    (h_byte : extractByte codeWord
        (byteOffset (codePtr + signExtend12 (BitVec.ofNat 12 (EvmAsm.Evm64.pushByteSrcOffset 0)))) = byteVal)
    (h_code_align : alignToDword (codePtr + signExtend12 (BitVec.ofNat 12 (EvmAsm.Evm64.pushByteSrcOffset 0))) = codeDwordAddr)
    (h_code_valid : isValidByteAccess (codePtr + signExtend12 (BitVec.ofNat 12 (EvmAsm.Evm64.pushByteSrcOffset 0))) = true)
    (h_dst_align : alignToDword (sp + signExtend12 ((-32 : BitVec 12)) + signExtend12 (BitVec.ofNat 12 (EvmAsm.Evm64.pushByteDstOffset 1 0))) = sp + signExtend12 ((-32 : BitVec 12)))
    (h_dst_valid : isValidByteAccess (sp + signExtend12 ((-32 : BitVec 12)) + signExtend12 (BitVec.ofNat 12 (EvmAsm.Evm64.pushByteDstOffset 1 0))) = true) :
    let nsp := sp + signExtend12 ((-32 : BitVec 12))
    cpsTripleWithin (7 + 2) base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base (EvmAsm.Evm64.evm_push 1) 2)
      ((.x10 ↦ᵣ codePtr) **
        ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word)) **
         ((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
         ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
         ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
         ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
         (codeDwordAddr ↦ₘ codeWord) ** EvmAsm.Evm64.evmStackIs sp rest)
       ** (.x1 ↦ᵣ x1_init))
      ((.x10 ↦ᵣ (codePtr + signExtend12 2)) **
        ((.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ byteVal.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
         (codeDwordAddr ↦ₘ codeWord) **
         EvmAsm.Evm64.evmStackIs nsp (EvmAsm.Evm64.pushImmediateWord 1 (fun _ => byteVal) :: rest))
       ** (.x1 ↦ᵣ x1_init)) := by
  intro nsp
  have h0 := EvmAsm.Evm64.evm_push1_stack_spec_within sp codePtr v7Old d0 d1 d2 d3 codeWord codeDwordAddr
    base rest byteVal h_byte h_code_align h_code_valid h_dst_align h_dst_valid
  simp only [EvmAsm.Evm64.evm_push_code] at h0
  rw [show (base + 28 : Word) = base + fourTimes 7 from by simp only [fourTimes]; bv_omega] at h0
  have h_body : cpsTripleWithin 7 base (base + fourTimes 7) (CodeReq.ofProg base (EvmAsm.Evm64.evm_push 1))
      ((.x10 ↦ᵣ codePtr) **
        ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word)) **
         ((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
         ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
         ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
         ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
         (codeDwordAddr ↦ₘ codeWord) ** EvmAsm.Evm64.evmStackIs sp rest))
      ((.x10 ↦ᵣ codePtr) **
        ((.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ byteVal.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
         (codeDwordAddr ↦ₘ codeWord) **
         EvmAsm.Evm64.evmStackIs nsp (EvmAsm.Evm64.pushImmediateWord 1 (fun _ => byteVal) :: rest))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) h0
  have hlen : (EvmAsm.Evm64.evm_push 1).length = 7 := by decide
  exact passthroughRetHandlerSpec (by pcFree) hlen (by decide) h_body x1_init

-- ============================================================================
-- 24. Concrete instance — CALLDATASIZE (0x36), via the clean-ret lift
-- ============================================================================

/-- Handler-level spec for `h_CALLDATASIZE` (opcode 0x36). The 6-instruction
    `evm_calldatasize` body loads `env.callDataLen` (offset `callDataLenOff`)
    and grows the stack by one word holding the length as its low limb with
    three zero limbs; the 2-instruction clean-ret tail advances the EVM code
    pointer by 1 and returns (8 RISC-V instructions total). Structurally
    identical to `evmMSizeHandlerSpec` (no `x10` clobber → it lifts directly
    through `cleanRetHandlerSpec`); the only difference from MSIZE is the source
    cell (`env.callDataLen` instead of the memory-size cell). -/
theorem evmCallDataSizeHandlerSpec
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld callDataLen : Word)
    (d0 d1 d2 d3 : Word) (x10_init x1_init : Word) :
    cpsTripleWithin 8 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base (EvmAsm.Evm64.Calldata.evm_calldatasize envBaseReg tmpReg) 1)
      (((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
        (.x12 ↦ᵣ (nsp + 32)) **
        (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
        ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
        ((envAddr + BitVec.ofNat 64 EvmAsm.Evm64.EvmEnv.callDataLenOff) ↦ₘ callDataLen))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ callDataLen) **
        (.x12 ↦ᵣ nsp) **
        (nsp ↦ₘ callDataLen) ** ((nsp + 8) ↦ₘ 0) **
        ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0) **
        ((envAddr + BitVec.ofNat 64 EvmAsm.Evm64.EvmEnv.callDataLenOff) ↦ₘ callDataLen))
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  have h_body := EvmAsm.Evm64.Calldata.evm_calldatasize_spec_within envBaseReg tmpReg htmp_ne_x0
    nsp base envAddr tempOld callDataLen d0 d1 d2 d3
  simp only [EvmAsm.Evm64.Calldata.evm_calldatasize_code] at h_body
  have hBodyLen : (EvmAsm.Evm64.Calldata.evm_calldatasize envBaseReg tmpReg).length = 6 :=
    EvmAsm.Evm64.Calldata.evm_calldatasize_length envBaseReg tmpReg
  have hExitEq : (base + (24 : Word)) = base + fourTimes 6 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ callDataLen) **
        (.x12 ↦ᵣ nsp) **
        (nsp ↦ₘ callDataLen) ** ((nsp + 8) ↦ₘ 0) **
        ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0) **
        ((envAddr + BitVec.ofNat 64 EvmAsm.Evm64.EvmEnv.callDataLenOff) ↦ₘ callDataLen)) : Assertion).pcFree := by
    pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

end EvmAsm.Codegen.Proofs
