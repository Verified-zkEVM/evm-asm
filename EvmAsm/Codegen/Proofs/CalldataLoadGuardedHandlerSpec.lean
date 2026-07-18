/-
  EvmAsm.Codegen.Proofs.CalldataLoadGuardedHandlerSpec

  Handler-glue proof for `h_CALLDATALOAD` (opcode 0x35), closing the
  DRIFT.md "codegen is unverified by design" surface for this opcode.

  Background. The registry marks CALLDATALOAD `.proven` on the strength of the
  *body* spec `evm_calldataload_staged_stack_spec_within`
  (`Evm64/Calldata/StageSpec.lean`), a `cpsTripleWithin` over
  `evm_calldataload_staged` alone. But the subroutine the codegen actually
  emits wraps that verified body in glue:

  ```
  h_CALLDATALOAD:
    <10-instr stack-underflow guard>   (stackUnderflowGuardAsm 1, negOff = -32)
    la x14, bv_cdl_stage               (2 instrs: auipc + addi — buffer base)
    <evm_calldataload_staged>          (121 instrs / 401 steps, VERIFIED)
    addi x10, x10, 1 ; ret             (2 instrs: .advanceAndRet 1)
  ```

  The guard + `la x14` + tail is exactly the unverified glue. The `h_ADD`
  precedent (`GuardedHandlerSpecs.evmAddGuardedHandlerSpec`) proves the same
  shape but (a) has no intervening `la x14`, (b) frames `x14` around the body
  (here the body *consumes* `x14`), and (c) has a straight-line body
  (here the staging copy loop makes steps ≠ instruction count).

  This file closes all three gaps:
  * `laX14_staged_body_spec_within` — composes the `la x14` pair with the body
    spec, threading `x14` into the body (Step 1);
  * `guardedHandlerX14Spec` — the guard-prologue template with `x14` flowing
    into the handler rather than framed around it (Step 3, reusable);
  * `evm_calldataload_staged_guarded_handler_spec` — the concrete `h_CALLDATALOAD`
    handler-level triple with the standard conditional (underflow / no-underflow)
    post (Step 4).

  `HandlerSpecs.cleanRetHandlerSpec'` (the looping-body lift, steps ≠ length)
  bridges Step 1 and Step 3.

  The `la x14, bv_cdl_stage` target is left as an `hla3` reconstruction
  hypothesis, exactly as `GuardedHandlerSpecs` leaves `hla1`/`hla2` for the two
  guard `la`s; tying it to the emitted bytes (promoting `bv_cdl_stage` to a
  guest address + extending `check_guarded_handler_bytes.py`) is deferred.
-/

import EvmAsm.Codegen.Proofs.HandlerSpecs
import EvmAsm.Codegen.Proofs.GuardedHandlerSpecs
import EvmAsm.Evm64.Calldata.StageSpec

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64
open EvmAsm.Evm64.EvmEnv
open EvmAsm.Evm64.Calldata

/-- Local `PCFree` instance for `bytesRegion` (there is no global one — only
    section-scoped ones in the RLP files). With it, `bytesRegion`, `evmStackIs`,
    `envIs`, `calldataRegionIs`, `regIs`, `regOwn`, and `sepConj` all resolve by
    instance search, so plain `by pcFree` closes every pcFree goal in this file
    via its `inferInstance` path — no expensive metavariable unification. -/
local instance instPCFreeBytesRegion (base : Word) (bs : List (BitVec 8)) :
    Assertion.PCFree (bytesRegion base bs) := ⟨bytesRegion_pcFree base bs⟩

/-- The two-instruction `la x14, bv_cdl_stage` expansion (auipc + addi): the
    inter-guard/body glue that materialises the staging-buffer base into `x14`
    (an input the verified body consumes). `hi3`/`lo3` are the linker `la` pair,
    kept symbolic and tied to the buffer address via an `hla3` hypothesis. -/
def laX14Prog (hi3 : BitVec 20) (lo3 : BitVec 12) : Program :=
  [.AUIPC .x14 hi3, .ADDI .x14 .x14 lo3]

@[simp] theorem laX14Prog_length (hi3 : BitVec 20) (lo3 : BitVec 12) :
    (laX14Prog hi3 lo3).length = 2 := rfl

/-- The full guarded-body Program: the `la x14` glue followed by the verified
    staging body. Length 123 = 2 + 121. -/
def calldataloadStagedGuardedBody (hi3 : BitVec 20) (lo3 : BitVec 12) : Program :=
  laX14Prog hi3 lo3 ;; evm_calldataload_staged

theorem calldataloadStagedGuardedBody_length (hi3 : BitVec 20) (lo3 : BitVec 12) :
    (calldataloadStagedGuardedBody hi3 lo3).length = 123 := by
  simp [calldataloadStagedGuardedBody, laX14Prog, seq, evm_calldataload_staged_length]

/-- Length of the inline `la x14 ;; body` combined program (= 123). -/
theorem laX14_staged_length (hi3 : BitVec 20) (lo3 : BitVec 12) :
    (laX14Prog hi3 lo3 ;; evm_calldataload_staged).length = 123 := by
  show (laX14Prog hi3 lo3 ++ evm_calldataload_staged).length = 123
  rw [Program.length_append, laX14Prog_length, evm_calldataload_staged_length]

-- ============================================================================
-- Step 1: `la x14, bv_cdl_stage ;; evm_calldataload_staged`
-- ============================================================================


/-- **The `la x14` + verified-body composition.** Sits at `hbase + 40` (the
    post-guard address). The two `la` instructions overwrite the incoming
    (guard-residual) `x14 = x14g` with the buffer base `buf` (via `hla3`), then
    the verified staging body runs with `x14 = buf`. The pre/post are the body
    spec's, but with `x14` generalised on entry (it is clobbered by the `la`). -/
theorem laX14_staged_body_spec_within
    (hbase envAddr sp buf memBase : Word) (cdByteOff len : Nat)
    (offsetWord : EvmWord) (env : EvmEnv) (rest : List EvmWord)
    (data memBytes origBuf : List (BitVec 8))
    (x5o x6o x7o x28o x29o x30o x31o offOld byteOld accOld addrOld x14g : Word)
    (hi3 : BitVec 20) (lo3 : BitVec 12)
    (hla3 : (hbase + 40) + ((hi3.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo3 = buf)
    (h_cdp : env.callDataPtr = memBase + BitVec.ofNat 64 cdByteOff)
    (h_len : data.length = env.callDataLen.toNat)
    (h_len_def : len = env.callDataLen.toNat)
    (h_data : data = (memBytes.drop cdByteOff).take len)
    (h_mem_align : memBase.toNat % 8 = 0)
    (h_buf_align : buf.toNat % 8 = 0)
    (h_fits : cdByteOff + len ≤ memBytes.length)
    (h_mem_over : memBase.toNat + memBytes.length + 32 ≤ 2 ^ 64)
    (h_mem_valid : ∀ k, k < memBytes.length →
      isValidByteAccess (memBase + BitVec.ofNat 64 k) = true)
    (h_buf_over : buf.toNat + 64 < 2 ^ 64)
    (h_buf_valid : ∀ k, k < 64 → isValidByteAccess (buf + BitVec.ofNat 64 k) = true)
    (h_origBuf_len : origBuf.length = 64)
    (h_origBuf_tail : origBuf.drop 32 = List.replicate 32 0) :
    cpsTripleWithin (2 + 401) (hbase + 40)
      ((hbase + 40) + BitVec.ofNat 64
        (4 * (laX14Prog hi3 lo3 ;; evm_calldataload_staged).length))
      (CodeReq.ofProg (hbase + 40) (laX14Prog hi3 lo3 ;; evm_calldataload_staged))
      (((.x12 : Reg) ↦ᵣ sp) ** ((.x20 : Reg) ↦ᵣ envAddr) **
       ((.x14 : Reg) ↦ᵣ x14g) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ x5o) ** ((.x6 : Reg) ↦ᵣ x6o) ** ((.x7 : Reg) ↦ᵣ x7o) **
       ((.x28 : Reg) ↦ᵣ x28o) ** ((.x29 : Reg) ↦ᵣ x29o) **
       ((.x30 : Reg) ↦ᵣ x30o) ** ((.x31 : Reg) ↦ᵣ x31o) **
       ((.x15 : Reg) ↦ᵣ offOld) ** ((.x16 : Reg) ↦ᵣ byteOld) **
       ((.x17 : Reg) ↦ᵣ accOld) ** ((.x18 : Reg) ↦ᵣ addrOld) **
       evmStackIs sp (offsetWord :: rest) ** envIs envAddr env **
       bytesRegion buf origBuf ** bytesRegion memBase memBytes)
      (((.x12 : Reg) ↦ᵣ sp) ** ((.x20 : Reg) ↦ᵣ envAddr) **
       ((.x14 : Reg) ↦ᵣ buf) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x28 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x15 **
       regOwn .x16 ** regOwn .x17 ** regOwn .x18 **
       evmStackIs sp (callDataLoadWord data offsetWord.toNat :: rest) **
       envIs envAddr env **
       calldataRegionIs buf (stagedWindowBytes data offsetWord.toNat) **
       bytesRegion memBase memBytes) := by
  -- The la pair: AUIPC x14 at hbase+40, ADDI x14 at hbase+44; x14g → buf.
  have s1 := auipc_spec_within .x14 x14g hi3 (hbase + 40) (by nofun)
  rw [show (hbase + 40 : Word) + 4 = hbase + 44 from by bv_omega] at s1
  have s2 := addi_spec_same_within .x14
    ((hbase + 40) + ((hi3.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64) lo3
    (hbase + 44) (by nofun)
  rw [hla3, show (hbase + 44 : Word) + 4 = hbase + 48 from by bv_omega] at s2
  have hd_la : (CodeReq.singleton (hbase + 40) (Instr.AUIPC .x14 hi3)).Disjoint
      (CodeReq.singleton (hbase + 44) (Instr.ADDI .x14 .x14 lo3)) :=
    CodeReq.Disjoint.singleton (by bv_omega)
  have h_la := cpsTripleWithin_seq hd_la s1 s2
  -- Rewrite the la CodeReq into `ofProg` form.
  have hcode_la : CodeReq.ofProg (hbase + 40) (laX14Prog hi3 lo3) =
      (CodeReq.singleton (hbase + 40) (Instr.AUIPC .x14 hi3)).union
        (CodeReq.singleton (hbase + 44) (Instr.ADDI .x14 .x14 lo3)) := by
    simp only [laX14Prog, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
      CodeReq.union_empty_right]
    rw [show (hbase + 40 : Word) + 4 = hbase + 44 from by bv_omega]
  rw [← hcode_la] at h_la
  -- Frame the body's `x12`/`x20` prefix on the left and the remaining cells on
  -- the right, in body-pre order — so only re-association (no permutation) is
  -- needed to match the body spec's pre.
  have h_la1 := cpsTripleWithin_frameL
    (((.x12 : Reg) ↦ᵣ sp) ** ((.x20 : Reg) ↦ᵣ envAddr)) (by pcFree) h_la
  have h_la2 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x5 : Reg) ↦ᵣ x5o) ** ((.x6 : Reg) ↦ᵣ x6o) ** ((.x7 : Reg) ↦ᵣ x7o) **
      ((.x28 : Reg) ↦ᵣ x28o) ** ((.x29 : Reg) ↦ᵣ x29o) **
      ((.x30 : Reg) ↦ᵣ x30o) ** ((.x31 : Reg) ↦ᵣ x31o) **
      ((.x15 : Reg) ↦ᵣ offOld) ** ((.x16 : Reg) ↦ᵣ byteOld) **
      ((.x17 : Reg) ↦ᵣ accOld) ** ((.x18 : Reg) ↦ᵣ addrOld) **
      evmStackIs sp (offsetWord :: rest) ** envIs envAddr env **
      bytesRegion buf origBuf ** bytesRegion memBase memBytes)
    (by pcFree) h_la1
  -- The verified body spec at hbase+48.
  have h_body := evm_calldataload_staged_stack_spec_within (hbase + 48) envAddr sp buf
    memBase cdByteOff len offsetWord env rest data memBytes origBuf
    x5o x6o x7o x28o x29o x30o x31o offOld byteOld accOld addrOld
    h_cdp h_len h_len_def h_data h_mem_align h_buf_align h_fits h_mem_over h_mem_valid
    h_buf_over h_buf_valid h_origBuf_len h_origBuf_tail
  -- Reshape the la's pre to STEP1PRE and its post to the body's pre — both are
  -- the same atoms in the same order, differing only in association.
  have h_la_f' := cpsTripleWithin_weaken
    (fun _ hp => by simp only [sepConj_assoc'] at hp ⊢; exact hp)
    (fun _ hq => by simp only [sepConj_assoc'] at hq ⊢; exact hq) h_la2
  -- Disjointness of the la region and the body region.
  have hd_full : (CodeReq.ofProg (hbase + 40) (laX14Prog hi3 lo3)).Disjoint
      (CodeReq.ofProg (hbase + 48) evm_calldataload_staged) := by
    intro a
    by_cases hmem : ∃ k : Nat, k < 2 ∧ a = (hbase + 40) + BitVec.ofNat 64 (4 * k)
    · right
      obtain ⟨k, hk, ha⟩ := hmem
      apply CodeReq.ofProg_none_range
      intro j hj heq
      rw [evm_calldataload_staged_length] at hj
      subst ha
      bv_omega
    · left
      apply CodeReq.ofProg_none_range
      intro k hk heq
      have hk2 : k < 2 := by simpa [laX14Prog] using hk
      exact hmem ⟨k, hk2, heq⟩
  -- Sequence la ;; body.
  have h_seq := cpsTripleWithin_seq hd_full h_la_f' h_body
  -- Combined-body length (avoids reducing the 121-instr program by `rfl`).
  have hlen : (laX14Prog hi3 lo3 ;; evm_calldataload_staged).length = 123 := by
    show (laX14Prog hi3 lo3 ++ evm_calldataload_staged).length = 123
    rw [Program.length_append, laX14Prog_length, evm_calldataload_staged_length]
  -- Reconcile the CodeReq to `ofProg (hbase+40) (laX14Prog ;; staged)`.
  have haddr : (hbase + 40 : Word) + BitVec.ofNat 64 (4 * (laX14Prog hi3 lo3).length)
      = hbase + 48 := by rw [laX14Prog_length]; bv_omega
  have hcode_full :
      CodeReq.ofProg (hbase + 40) (laX14Prog hi3 lo3 ++ evm_calldataload_staged) =
        (CodeReq.ofProg (hbase + 40) (laX14Prog hi3 lo3)).union
          (CodeReq.ofProg ((hbase + 40) + BitVec.ofNat 64 (4 * (laX14Prog hi3 lo3).length))
            evm_calldataload_staged) :=
    CodeReq.ofProg_append
  rw [haddr] at hcode_full
  rw [← hcode_full] at h_seq
  -- Reconcile the exit PC.
  have hexit : (hbase + 40 : Word) + BitVec.ofNat 64
      (4 * (laX14Prog hi3 lo3 ;; evm_calldataload_staged).length)
      = (hbase + 48) + 484 := by rw [hlen]; bv_omega
  rw [hexit]
  exact h_seq

-- ============================================================================
-- Step 3: the guard-prologue template with `x14` threaded into the handler
-- ============================================================================

/-- **Guard template with `x14` consumed by the handler.** The sibling of
    `GuardedHandlerSpecs.guardedCleanRetHandlerSpec`, but the guard's residual
    `x14` (`= curTop + signExtend12 negOff`) flows *into* the handler's pre
    rather than being framed around the body. This is what a handler needs when
    its `preBody` re-materialises `x14` (here `la x14, bv_cdl_stage`) and the
    body consumes it. Same conditional post: on underflow the halt flag is set
    to 7 and the EVM state is untouched; otherwise the handler post `Q`. -/
theorem guardedHandlerX14Spec
    {nBody : Nat} {base cell flag sp : Word} {body : Program} {n : BitVec 12}
    {P' Q : Assertion}
    (hi1 : BitVec 20) (lo1 : BitVec 12) (hi2 : BitVec 20) (lo2 : BitVec 12)
    (negOff : BitVec 12)
    (hn : 5 ≤ nBody)
    (hP'free : P'.pcFree)
    (hBodyLenBound : body.length < 2 ^ 60)
    (hla1 : base + ((hi1.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo1 = cell)
    (hla2 : base + 20 + 4 + ((hi2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo2 = flag)
    (v5 v6 x10_init x1_init x14_init curTop f0 : Word)
    (h_handler : cpsTripleWithin nBody (base + 40) (x1_init &&& ~~~1)
      (cleanRetHandlerCode (base + 40) body n)
      ((((.x12 : Reg) ↦ᵣ sp) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        ((.x14 : Reg) ↦ᵣ (curTop + signExtend12 negOff)) ** P') **
        ((.x10 : Reg) ↦ᵣ x10_init) ** ((.x1 : Reg) ↦ᵣ x1_init))
      Q) :
    cpsTripleWithin (5 + nBody) base (x1_init &&& ~~~1)
      (guardedCleanRetHandlerCode base hi1 lo1 hi2 lo2 negOff body n)
      (((((.x12 : Reg) ↦ᵣ sp) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** P') **
         ((.x10 : Reg) ↦ᵣ x10_init) ** ((.x1 : Reg) ↦ᵣ x1_init)) **
        ((.x14 : Reg) ↦ᵣ x14_init) ** (cell ↦ₘ curTop) ** (flag ↦ₘ f0))
      (if BitVec.ult (curTop + signExtend12 negOff) sp then
        ((((.x12 : Reg) ↦ᵣ sp) ** ((.x5 : Reg) ↦ᵣ (7 : Word)) ** ((.x6 : Reg) ↦ᵣ flag) ** P') **
          ((.x10 : Reg) ↦ᵣ x10_init) ** ((.x1 : Reg) ↦ᵣ x1_init)) **
          ((.x14 : Reg) ↦ᵣ (curTop + signExtend12 negOff)) ** (cell ↦ₘ curTop) **
          (flag ↦ₘ (7 : Word))
      else
        Q ** (cell ↦ₘ curTop) ** (flag ↦ₘ f0)) := by
  -- Split the full CodeReq into check / halt / clean-ret regions.
  have hsplit : guardedCleanRetHandlerCode base hi1 lo1 hi2 lo2 negOff body n =
      ((CodeReq.ofProg base (stackGuardCheckProgram hi1 lo1 negOff)).union
        (CodeReq.ofProg (base + 20) (stackGuardHaltProgram hi2 lo2))).union
        (CodeReq.ofProg (base + 40) (cleanRetHandlerProgram body n)) := by
    unfold guardedCleanRetHandlerCode guardedCleanRetHandlerProgram
    rw [stackUnderflowGuardProgram_split]
    unfold seq
    have hOuter : CodeReq.ofProg base
          ((stackGuardCheckProgram hi1 lo1 negOff ++ stackGuardHaltProgram hi2 lo2)
            ++ cleanRetHandlerProgram body n) =
        (CodeReq.ofProg base
            (stackGuardCheckProgram hi1 lo1 negOff ++ stackGuardHaltProgram hi2 lo2)).union
          (CodeReq.ofProg (base + BitVec.ofNat 64
              (4 * (stackGuardCheckProgram hi1 lo1 negOff
                ++ stackGuardHaltProgram hi2 lo2).length))
            (cleanRetHandlerProgram body n)) :=
      CodeReq.ofProg_append
    rw [hOuter]
    have hInner : CodeReq.ofProg base
          (stackGuardCheckProgram hi1 lo1 negOff ++ stackGuardHaltProgram hi2 lo2) =
        (CodeReq.ofProg base (stackGuardCheckProgram hi1 lo1 negOff)).union
          (CodeReq.ofProg (base + BitVec.ofNat 64
              (4 * (stackGuardCheckProgram hi1 lo1 negOff).length))
            (stackGuardHaltProgram hi2 lo2)) :=
      CodeReq.ofProg_append
    rw [hInner,
      show (stackGuardCheckProgram hi1 lo1 negOff
          ++ stackGuardHaltProgram hi2 lo2).length = 10 from rfl,
      show (stackGuardCheckProgram hi1 lo1 negOff).length = 5 from rfl,
      show base + BitVec.ofNat 64 (4 * 10) = base + 40 from by bv_omega,
      show base + BitVec.ofNat 64 (4 * 5) = base + 20 from by bv_omega]
  -- Region disjointness.
  have hd1 : (CodeReq.ofProg base (stackGuardCheckProgram hi1 lo1 negOff)).Disjoint
      (CodeReq.ofProg (base + 20) (stackGuardHaltProgram hi2 lo2)) := by
    intro a
    by_cases hmem : ∃ k : Nat, k < 5 ∧ a = base + BitVec.ofNat 64 (4 * k)
    · right
      obtain ⟨k, hk, ha⟩ := hmem
      apply CodeReq.ofProg_none_range
      intro j hj
      have hj5 : j < 5 := hj
      subst ha
      bv_omega
    · left
      apply CodeReq.ofProg_none_range
      intro k hk heq
      exact hmem ⟨k, hk, heq⟩
  have hd2 : ((CodeReq.ofProg base (stackGuardCheckProgram hi1 lo1 negOff)).union
      (CodeReq.ofProg (base + 20) (stackGuardHaltProgram hi2 lo2))).Disjoint
      (CodeReq.ofProg (base + 40) (cleanRetHandlerProgram body n)) := by
    intro a
    by_cases hmem : ∃ k : Nat, k < 10 ∧ a = base + BitVec.ofNat 64 (4 * k)
    · right
      obtain ⟨k, hk, ha⟩ := hmem
      apply CodeReq.ofProg_none_range
      intro j hj
      rw [cleanRetHandlerProgram_length] at hj
      subst ha
      bv_omega
    · left
      have h1 : CodeReq.ofProg base (stackGuardCheckProgram hi1 lo1 negOff) a = none := by
        apply CodeReq.ofProg_none_range
        intro k hk heq
        have hk5 : k < 5 := hk
        exact hmem ⟨k, by omega, heq⟩
      have h2 : CodeReq.ofProg (base + 20) (stackGuardHaltProgram hi2 lo2) a = none := by
        apply CodeReq.ofProg_none_range
        intro j hj heq
        have hj5 : j < 5 := hj
        exact hmem ⟨5 + j, by omega, by rw [heq]; bv_omega⟩
      rw [CodeReq.union_none_left h1]
      exact h2
  -- Subsumption of each region into the full CodeReq.
  have hsub1 : ∀ a i,
      CodeReq.ofProg base (stackGuardCheckProgram hi1 lo1 negOff) a = some i →
      guardedCleanRetHandlerCode base hi1 lo1 hi2 lo2 negOff body n a = some i := by
    intro a i h
    rw [hsplit]
    exact CodeReq.union_mono_left a i (CodeReq.union_mono_left a i h)
  have hsub2 : ∀ a i,
      CodeReq.ofProg (base + 20) (stackGuardHaltProgram hi2 lo2) a = some i →
      guardedCleanRetHandlerCode base hi1 lo1 hi2 lo2 negOff body n a = some i := by
    intro a i h
    rw [hsplit]
    apply CodeReq.union_mono_left
    rcases hd1 a with h1 | h1
    · rw [CodeReq.union_none_left h1]; exact h
    · rw [h1] at h; cases h
  have hsub3 : ∀ a i,
      CodeReq.ofProg (base + 40) (cleanRetHandlerProgram body n) a = some i →
      guardedCleanRetHandlerCode base hi1 lo1 hi2 lo2 negOff body n a = some i := by
    intro a i h
    rw [hsplit]
    rcases hd2 a with h1 | h1
    · rw [CodeReq.union_none_left h1]; exact h
    · rw [h1] at h; cases h
  -- The guard branch, framed with everything the check does not touch.
  have hbr := stackGuardBranch hi1 lo1 negOff base cell sp curTop x14_init hla1
  have hFbr : (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** P' ** ((.x10 : Reg) ↦ᵣ x10_init) **
      ((.x1 : Reg) ↦ᵣ x1_init) ** (flag ↦ₘ f0) : Assertion).pcFree := by
    repeat first
      | apply pcFree_sepConj
      | exact hP'free
      | exact pcFree_regIs
      | exact pcFree_memIs
  have hbr2 := cpsBranchWithin_extend_code hsub1
    (cpsBranchWithin_frameR
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** P' ** ((.x10 : Reg) ↦ᵣ x10_init) **
        ((.x1 : Reg) ↦ᵣ x1_init) ** (flag ↦ₘ f0))
      hFbr hbr)
  have hFt : ((cell ↦ₘ curTop) ** (flag ↦ₘ f0) : Assertion).pcFree := by pcFree
  have h_t2 := cpsTripleWithin_frameR
    (⌜¬BitVec.ult (curTop + signExtend12 negOff) sp⌝) pcFree_pure
    (cpsTripleWithin_extend_code hsub3
      (cpsTripleWithin_frameR
        ((cell ↦ₘ curTop) ** (flag ↦ₘ f0))
        hFt h_handler))
  -- `hla2` is already in `stackGuardHalt`'s `hbase + 4 + …` shape (hbase = base+20).
  have h_halt := stackGuardHalt hi2 lo2 (base + 20) flag v5 v6 x1_init f0 hla2
  have hFf : (((.x12 : Reg) ↦ᵣ sp) ** P' ** ((.x10 : Reg) ↦ᵣ x10_init) **
      ((.x14 : Reg) ↦ᵣ (curTop + signExtend12 negOff)) ** (cell ↦ₘ curTop) : Assertion).pcFree := by
    repeat first
      | apply pcFree_sepConj
      | exact hP'free
      | exact pcFree_regIs
      | exact pcFree_memIs
  have h_f3 := cpsTripleWithin_mono_nSteps hn
    (cpsTripleWithin_frameR
      (⌜BitVec.ult (curTop + signExtend12 negOff) sp⌝) pcFree_pure
      (cpsTripleWithin_extend_code hsub2
        (cpsTripleWithin_frameR
          (((.x12 : Reg) ↦ᵣ sp) ** P' ** ((.x10 : Reg) ↦ᵣ x10_init) **
            ((.x14 : Reg) ↦ᵣ (curTop + signExtend12 negOff)) ** (cell ↦ₘ curTop))
          hFf h_halt)))
  -- Merge the two paths (both exit at x1_init &&& ~~~1) and align shapes.
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsBranchWithin_merge_same_cr hbr2
      (cpsTripleWithin_weaken (fun _ hp => by xperm_pure hp)
        (fun h hq => by
          obtain ⟨hq', hfact⟩ := (sepConj_pure_right h).mp hq
          rw [if_neg hfact]
          exact hq')
        h_t2)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_pure hp)
        (fun h hq => by
          obtain ⟨hq', hfact⟩ := (sepConj_pure_right h).mp hq
          rw [if_pos hfact]
          xperm_hyp hq')
        h_f3))

-- ============================================================================
-- Step 4: the concrete `h_CALLDATALOAD` handler-level spec
-- ============================================================================

/-- **The verified `h_CALLDATALOAD` handler subroutine** (opcode 0x35). The full
    emitted glue — the 10-instruction stack-underflow guard (`negOff = -32`,
    word count 1), the `la x14, bv_cdl_stage` buffer-base load, the verified
    `evm_calldataload_staged` body, and the `.advanceAndRet 1` tail — as one
    `cpsTripleWithin` from `hbase` to the dispatcher return `x1_init &&& ~~~1`.

    On stack underflow (`curTop - 32 <u sp`) the halt flag is set to routing
    code 7 and the EVM state is untouched (`x10` not advanced). Otherwise the
    body's stack post holds — the 256-bit offset is popped and
    `callDataLoadWord data offsetWord.toNat` is pushed in place — and `x10`
    (the EVM code pointer) advances by 1.

    `hla1`/`hla2` reconstruct the guard's `la evm_cur_stack_top` / `la
    evm_halt_flag`; `hla3` reconstructs `la x14, bv_cdl_stage`. These tie the
    symbolic `la` immediates to their target cells (the deferred byte-check
    would discharge them against the emitted ELF). This is the CALLDATALOAD
    analogue of `GuardedHandlerSpecs.evmAddGuardedHandlerSpec`. -/
theorem evm_calldataload_staged_guarded_handler_spec
    (hbase envAddr sp buf memBase cell flag : Word) (cdByteOff len : Nat)
    (offsetWord : EvmWord) (env : EvmEnv) (rest : List EvmWord)
    (data memBytes origBuf : List (BitVec 8))
    (x5o x6o x7o x28o x29o x30o x31o offOld byteOld accOld addrOld : Word)
    (x10_init x1_init x14_init curTop f0 : Word)
    (hi1 : BitVec 20) (lo1 : BitVec 12) (hi2 : BitVec 20) (lo2 : BitVec 12)
    (hi3 : BitVec 20) (lo3 : BitVec 12)
    (hla1 : hbase + ((hi1.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo1 = cell)
    (hla2 : hbase + 20 + 4 + ((hi2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo2 = flag)
    (hla3 : (hbase + 40) + ((hi3.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo3 = buf)
    (h_cdp : env.callDataPtr = memBase + BitVec.ofNat 64 cdByteOff)
    (h_len : data.length = env.callDataLen.toNat)
    (h_len_def : len = env.callDataLen.toNat)
    (h_data : data = (memBytes.drop cdByteOff).take len)
    (h_mem_align : memBase.toNat % 8 = 0)
    (h_buf_align : buf.toNat % 8 = 0)
    (h_fits : cdByteOff + len ≤ memBytes.length)
    (h_mem_over : memBase.toNat + memBytes.length + 32 ≤ 2 ^ 64)
    (h_mem_valid : ∀ k, k < memBytes.length →
      isValidByteAccess (memBase + BitVec.ofNat 64 k) = true)
    (h_buf_over : buf.toNat + 64 < 2 ^ 64)
    (h_buf_valid : ∀ k, k < 64 → isValidByteAccess (buf + BitVec.ofNat 64 k) = true)
    (h_origBuf_len : origBuf.length = 64)
    (h_origBuf_tail : origBuf.drop 32 = List.replicate 32 0) :
    cpsTripleWithin 410 hbase (x1_init &&& ~~~1)
      (guardedCleanRetHandlerCode hbase hi1 lo1 hi2 lo2 (-32)
        (laX14Prog hi3 lo3 ;; evm_calldataload_staged) 1)
      (((((.x12 : Reg) ↦ᵣ sp) ** ((.x5 : Reg) ↦ᵣ x5o) ** ((.x6 : Reg) ↦ᵣ x6o) **
          (((.x20 : Reg) ↦ᵣ envAddr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           ((.x7 : Reg) ↦ᵣ x7o) ** ((.x28 : Reg) ↦ᵣ x28o) ** ((.x29 : Reg) ↦ᵣ x29o) **
           ((.x30 : Reg) ↦ᵣ x30o) ** ((.x31 : Reg) ↦ᵣ x31o) **
           ((.x15 : Reg) ↦ᵣ offOld) ** ((.x16 : Reg) ↦ᵣ byteOld) **
           ((.x17 : Reg) ↦ᵣ accOld) ** ((.x18 : Reg) ↦ᵣ addrOld) **
           evmStackIs sp (offsetWord :: rest) ** envIs envAddr env **
           bytesRegion buf origBuf ** bytesRegion memBase memBytes)) **
         ((.x10 : Reg) ↦ᵣ x10_init) ** ((.x1 : Reg) ↦ᵣ x1_init)) **
        ((.x14 : Reg) ↦ᵣ x14_init) ** (cell ↦ₘ curTop) ** (flag ↦ₘ f0))
      (if BitVec.ult (curTop + signExtend12 (-32 : BitVec 12)) sp then
        ((((.x12 : Reg) ↦ᵣ sp) ** ((.x5 : Reg) ↦ᵣ (7 : Word)) ** ((.x6 : Reg) ↦ᵣ flag) **
          (((.x20 : Reg) ↦ᵣ envAddr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           ((.x7 : Reg) ↦ᵣ x7o) ** ((.x28 : Reg) ↦ᵣ x28o) ** ((.x29 : Reg) ↦ᵣ x29o) **
           ((.x30 : Reg) ↦ᵣ x30o) ** ((.x31 : Reg) ↦ᵣ x31o) **
           ((.x15 : Reg) ↦ᵣ offOld) ** ((.x16 : Reg) ↦ᵣ byteOld) **
           ((.x17 : Reg) ↦ᵣ accOld) ** ((.x18 : Reg) ↦ᵣ addrOld) **
           evmStackIs sp (offsetWord :: rest) ** envIs envAddr env **
           bytesRegion buf origBuf ** bytesRegion memBase memBytes)) **
          ((.x10 : Reg) ↦ᵣ x10_init) ** ((.x1 : Reg) ↦ᵣ x1_init)) **
          ((.x14 : Reg) ↦ᵣ (curTop + signExtend12 (-32 : BitVec 12))) **
          (cell ↦ₘ curTop) ** (flag ↦ₘ (7 : Word))
      else
        ((((.x12 : Reg) ↦ᵣ sp) ** ((.x20 : Reg) ↦ᵣ envAddr) **
          ((.x14 : Reg) ↦ᵣ buf) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x28 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x15 **
          regOwn .x16 ** regOwn .x17 ** regOwn .x18 **
          evmStackIs sp (callDataLoadWord data offsetWord.toNat :: rest) **
          envIs envAddr env **
          calldataRegionIs buf (stagedWindowBytes data offsetWord.toNat) **
          bytesRegion memBase memBytes) **
         ((.x10 : Reg) ↦ᵣ (x10_init + signExtend12 (1 : BitVec 12))) **
         ((.x1 : Reg) ↦ᵣ x1_init)) **
        (cell ↦ₘ curTop) ** (flag ↦ₘ f0)) := by
  have h_step1 := laX14_staged_body_spec_within hbase envAddr sp buf memBase cdByteOff len
    offsetWord env rest data memBytes origBuf x5o x6o x7o x28o x29o x30o x31o
    offOld byteOld accOld addrOld (curTop + signExtend12 (-32 : BitVec 12)) hi3 lo3 hla3
    h_cdp h_len h_len_def h_data h_mem_align h_buf_align h_fits h_mem_over h_mem_valid
    h_buf_over h_buf_valid h_origBuf_len h_origBuf_tail
  have h_handler0 := cleanRetHandlerSpec' (by pcFree)
    (by rw [laX14_staged_length]; decide) h_step1 (1 : BitVec 12) x10_init x1_init
  exact guardedHandlerX14Spec (P' :=
      ((.x20 : Reg) ↦ᵣ envAddr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x7 : Reg) ↦ᵣ x7o) ** ((.x28 : Reg) ↦ᵣ x28o) ** ((.x29 : Reg) ↦ᵣ x29o) **
      ((.x30 : Reg) ↦ᵣ x30o) ** ((.x31 : Reg) ↦ᵣ x31o) **
      ((.x15 : Reg) ↦ᵣ offOld) ** ((.x16 : Reg) ↦ᵣ byteOld) **
      ((.x17 : Reg) ↦ᵣ accOld) ** ((.x18 : Reg) ↦ᵣ addrOld) **
      evmStackIs sp (offsetWord :: rest) ** envIs envAddr env **
      bytesRegion buf origBuf ** bytesRegion memBase memBytes)
    hi1 lo1 hi2 lo2 (-32 : BitVec 12) (by omega) (by pcFree)
    (by rw [laX14_staged_length]; decide) hla1 hla2
    x5o x6o x10_init x1_init x14_init curTop f0
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq)
      h_handler0)

/-- Structural pin: the full emitted `h_CALLDATALOAD` program is 135 instructions
    (10 guard + 2 `la x14` + 121 body + 2 tail). A layout edit fails here. -/
theorem calldataload_guarded_handler_length
    (hi1 : BitVec 20) (lo1 : BitVec 12) (hi2 : BitVec 20) (lo2 : BitVec 12)
    (hi3 : BitVec 20) (lo3 : BitVec 12) :
    (guardedCleanRetHandlerProgram hi1 lo1 hi2 lo2 (-32)
      (laX14Prog hi3 lo3 ;; evm_calldataload_staged) 1).length = 135 := by
  unfold guardedCleanRetHandlerProgram
  show (stackUnderflowGuardProgram hi1 lo1 hi2 lo2 (-32)
    ++ cleanRetHandlerProgram (laX14Prog hi3 lo3 ;; evm_calldataload_staged) 1).length = 135
  rw [Program.length_append, cleanRetHandlerProgram_length, laX14_staged_length,
    show (stackUnderflowGuardProgram hi1 lo1 hi2 lo2 (-32)).length = 10 from rfl]

-- Axiom audit: `laX14_staged_body_spec_within`, `guardedHandlerX14Spec`, and
-- `evm_calldataload_staged_guarded_handler_spec` each kernel-depend only on
-- `[propext, Classical.choice, Quot.sound]` (the classical-3), verified by
-- `scripts/check-axioms.sh`; `#print axioms` omitted here to keep re-elaboration
-- output-free per the zero-warning policy.

end EvmAsm.Codegen.Proofs
