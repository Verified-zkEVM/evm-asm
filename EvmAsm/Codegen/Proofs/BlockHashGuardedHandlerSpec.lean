/-
  EvmAsm.Codegen.Proofs.BlockHashGuardedHandlerSpec

  Handler-glue proof for `h_BLOCKHASH` (opcode 0x40), closing the
  DRIFT.md "codegen is unverified by design" surface for this opcode. This is
  the direct BLOCKHASH analogue of the BLOBHASH glue proof
  (`BlobHashGuardedHandlerSpec.lean`).

  Background. The registry marks BLOCKHASH `.proven` on the strength of the
  *body* spec `EvmAsm.Evm64.BlockHash.evm_blockhash_stack_spec_within`
  (`Evm64/BlockHash/Spec.lean`), a `cpsTripleWithin` over the verified
  `evm_blockhash` program alone. But the subroutine the codegen actually emits
  (`EvmBlockHashHandlers.h_BLOCKHASH`) wraps that verified body in glue:

  ```
  h_BLOCKHASH:
    <10-instr stack-underflow guard>   (stackUnderflowGuardAsm 1, negOff = -32)
    la x18, evm_block_hashes           (2 instrs: auipc + addi — table base)
    <evm_blockhash x20 x18 x14 x16 x19> (28 instrs / 24 steps, VERIFIED)
    addi x10, x10, 1 ; ret             (2 instrs: .advanceAndRet 1)
  ```

  The guard + `la x18` + tail is exactly the unverified glue.

  Reuse of the `x14` template. The stack-underflow guard *always* clobbers
  `x14` (it materialises the stack-top cell there, subtracts the window, and
  branches). In BLOCKHASH `x14` is the body's `tgtReg` — an *arbitrary* body
  input (`tgtOld`) that the body immediately overwrites with a fresh `LD`. So
  the guard's residual `x14 = curTop + signExtend12 (-32)` is simply consumed
  as `tgtOld`, and `CalldataLoadGuardedHandlerSpec.guardedHandlerX14Spec` (which
  threads the guard residual `x14` into the handler pre) applies *unchanged* —
  no reg generalization is needed. The `la` re-materialises `x18` (the *table
  base*, the body's `tableBaseReg`), which lives inside the opaque handler frame
  `P'` of `guardedHandlerX14Spec` and is overwritten there, as CALLDATALOAD's
  `la x14` overwrites the (dead-on-that-path) guard residual. This is why the
  x14-specialised template covers this opcode too despite the differing `la`
  target register.

  This file closes the gap in three steps, mirroring BLOBHASH:
  * `laX18_body_spec_within` — composes the `la x18` pair with the verified
    body, threading the table base into `x18` (Step 1);
  * `HandlerSpecs.cleanRetHandlerSpec'` — lifts through the `.advanceAndRet 1`
    tail (the body's step count 24 ≠ its instruction count 28, so the
    steps-decoupled variant is required);
  * `evm_blockhash_guarded_handler_spec` — the concrete `h_BLOCKHASH`
    handler-level triple with the standard conditional (underflow /
    no-underflow) post (Step 4).

  The `la x18, evm_block_hashes` target is left as an `hla3` reconstruction
  hypothesis, exactly as `GuardedHandlerSpecs` leaves `hla1`/`hla2` for the two
  guard `la`s and CALLDATALOAD leaves `hla3` for `la x14, bv_cdl_stage`; tying
  it to the emitted bytes (promoting `evm_block_hashes` to a guest address) is a
  documented follow-up, not blocked on here.
-/

import EvmAsm.Codegen.Proofs.HandlerSpecs
import EvmAsm.Codegen.Proofs.GuardedHandlerSpecs
import EvmAsm.Codegen.Proofs.CalldataLoadGuardedHandlerSpec
import EvmAsm.Evm64.BlockHash.Spec

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64
open EvmAsm.Evm64.BlockHash

/-- The two-instruction `la x18, evm_block_hashes` expansion (auipc + addi): the
    inter-guard/body glue that materialises the `evm_block_hashes` table base
    into `x18` (the input `tableBaseReg` the verified body consumes). `hi3`/`lo3`
    are the linker `la` pair, kept symbolic and tied to the table address via an
    `hla3` hypothesis. -/
def laX18Prog (hi3 : BitVec 20) (lo3 : BitVec 12) : Program :=
  [.AUIPC .x18 hi3, .ADDI .x18 .x18 lo3]

@[simp] theorem laX18Prog_length (hi3 : BitVec 20) (lo3 : BitVec 12) :
    (laX18Prog hi3 lo3).length = 2 := rfl

/-- Length of the inline `la x18 ;; body` combined program (2 + 28 = 30). -/
theorem laX18_body_length (hi3 : BitVec 20) (lo3 : BitVec 12) :
    (laX18Prog hi3 lo3 ;; evm_blockhash .x20 .x18 .x14 .x16 .x19).length = 30 := by
  show (laX18Prog hi3 lo3 ++ evm_blockhash .x20 .x18 .x14 .x16 .x19).length = 30
  rw [Program.length_append, laX18Prog_length, evm_blockhash_length]

-- ============================================================================
-- Step 1: `la x18, evm_block_hashes ;; evm_blockhash`
-- ============================================================================

/-- **The `la x18` + verified-body composition.** Sits at `hbase + 40` (the
    post-guard address). The two `la` instructions overwrite the incoming
    (guard-frame) `x18 = x18g` with the table base `tblAddr` (via `hla3`), then
    the verified `evm_blockhash` body runs with `x18 = tblAddr`. The pre/post are
    the body spec's, but with `x18` generalised on entry (it is clobbered by the
    `la`) and `x5`/`x6` framed through (they are threaded by the guard on the
    no-underflow path, so the guard template needs them split out). The body's
    `tgtReg = x14` starts at the arbitrary `tgtOld` — in the full handler this
    receives the guard residual `curTop + signExtend12 (-32)`. -/
theorem laX18_body_spec_within
    (hbase envAddr nsp tblAddr tgtOld tmpOld valOld x18g v5 v6 : Word)
    (w : EvmWord) (cur count : Word) (hashes rest : List EvmWord)
    (hi3 : BitVec 20) (lo3 : BitVec 12)
    (hla3 : (hbase + 40) + ((hi3.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo3 = tblAddr)
    (hcount : count.toNat ≤ hashes.length) :
    cpsTripleWithin 26 (hbase + 40)
      ((hbase + 40) + BitVec.ofNat 64
        (4 * (laX18Prog hi3 lo3 ;; evm_blockhash .x20 .x18 .x14 .x16 .x19).length))
      (CodeReq.ofProg (hbase + 40) (laX18Prog hi3 lo3 ;; evm_blockhash .x20 .x18 .x14 .x16 .x19))
      (((.x18 : Reg) ↦ᵣ x18g) ** ((.x14 : Reg) ↦ᵣ tgtOld) ** ((.x16 : Reg) ↦ᵣ tmpOld) **
       ((.x19 : Reg) ↦ᵣ valOld) ** ((.x20 : Reg) ↦ᵣ envAddr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x12 : Reg) ↦ᵣ nsp) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
       evmStackIs nsp (w :: rest) **
       ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
       ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count) **
       evmStackIs tblAddr hashes)
      ((regOwn .x18 ** regOwn .x14 ** regOwn .x16 ** regOwn .x19 **
        ((.x20 : Reg) ↦ᵣ envAddr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ nsp) **
        evmStackIs nsp
          ((if w.getLimbN 1 = 0 ∧ w.getLimbN 2 = 0 ∧ w.getLimbN 3 = 0 ∧
               BitVec.ult (w.getLimbN 0) cur ∧ ¬ BitVec.ult count (cur - w.getLimbN 0)
            then hashes.getD (count - (cur - w.getLimbN 0)).toNat 0 else 0) :: rest) **
        ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
        ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count) **
        evmStackIs tblAddr hashes) ** (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6))) := by
  -- The la pair: AUIPC x18 at hbase+40, ADDI x18 at hbase+44; x18g → tblAddr.
  have s1 := auipc_spec_within .x18 x18g hi3 (hbase + 40) (by nofun)
  rw [show (hbase + 40 : Word) + 4 = hbase + 44 from by bv_omega] at s1
  have s2 := addi_spec_same_within .x18
    ((hbase + 40) + ((hi3.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64) lo3
    (hbase + 44) (by nofun)
  rw [hla3, show (hbase + 44 : Word) + 4 = hbase + 48 from by bv_omega] at s2
  have hd_la : (CodeReq.singleton (hbase + 40) (Instr.AUIPC .x18 hi3)).Disjoint
      (CodeReq.singleton (hbase + 44) (Instr.ADDI .x18 .x18 lo3)) :=
    CodeReq.Disjoint.singleton (by bv_omega)
  have h_la := cpsTripleWithin_seq hd_la s1 s2
  -- Rewrite the la CodeReq into `ofProg` form.
  have hcode_la : CodeReq.ofProg (hbase + 40) (laX18Prog hi3 lo3) =
      (CodeReq.singleton (hbase + 40) (Instr.AUIPC .x18 hi3)).union
        (CodeReq.singleton (hbase + 44) (Instr.ADDI .x18 .x18 lo3)) := by
    simp only [laX18Prog, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
      CodeReq.union_empty_right]
    rw [show (hbase + 40 : Word) + 4 = hbase + 44 from by bv_omega]
  rw [← hcode_la] at h_la
  -- Frame everything the la does not touch onto the la triple.
  have h_la_f := cpsTripleWithin_frameR
    (((.x14 : Reg) ↦ᵣ tgtOld) ** ((.x16 : Reg) ↦ᵣ tmpOld) ** ((.x19 : Reg) ↦ᵣ valOld) **
     ((.x20 : Reg) ↦ᵣ envAddr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ nsp) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
     evmStackIs nsp (w :: rest) **
     ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
     ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count) **
     evmStackIs tblAddr hashes)
    (by pcFree) h_la
  -- The verified body spec at hbase+48, with x5/x6 framed through.
  have h_body0 := evm_blockhash_stack_spec_within .x20 .x18 .x14 .x16 .x19
    (by decide) (by decide) (by decide) (by decide)
    nsp (hbase + 48) envAddr tblAddr tgtOld tmpOld valOld w cur count hashes rest hcount
  have h_body := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6)) (by pcFree) h_body0
  -- Disjointness of the la region and the body region.
  have hd_full : (CodeReq.ofProg (hbase + 40) (laX18Prog hi3 lo3)).Disjoint
      (CodeReq.ofProg (hbase + 48) (evm_blockhash .x20 .x18 .x14 .x16 .x19)) := by
    intro a
    by_cases hmem : ∃ k : Nat, k < 2 ∧ a = (hbase + 40) + BitVec.ofNat 64 (4 * k)
    · right
      obtain ⟨k, hk, ha⟩ := hmem
      apply CodeReq.ofProg_none_range
      intro j hj heq
      rw [evm_blockhash_length] at hj
      subst ha
      bv_omega
    · left
      apply CodeReq.ofProg_none_range
      intro k hk heq
      have hk2 : k < 2 := by simpa [laX18Prog] using hk
      exact hmem ⟨k, hk2, heq⟩
  -- Sequence la ;; body (the la post permutes to the body pre).
  have h_seq := cpsTripleWithin_seq_with_perm hd_full
    (fun _ hp => by xperm_hyp hp) h_la_f h_body
  -- Reconcile the CodeReq to `ofProg (hbase+40) (laX18Prog ;; evm_blockhash)`.
  have haddr : (hbase + 40 : Word) + BitVec.ofNat 64 (4 * (laX18Prog hi3 lo3).length)
      = hbase + 48 := by rw [laX18Prog_length]; bv_omega
  have hcode_full :
      CodeReq.ofProg (hbase + 40) (laX18Prog hi3 lo3 ++ evm_blockhash .x20 .x18 .x14 .x16 .x19) =
        (CodeReq.ofProg (hbase + 40) (laX18Prog hi3 lo3)).union
          (CodeReq.ofProg ((hbase + 40) + BitVec.ofNat 64 (4 * (laX18Prog hi3 lo3).length))
            (evm_blockhash .x20 .x18 .x14 .x16 .x19)) :=
    CodeReq.ofProg_append
  rw [haddr] at hcode_full
  rw [← hcode_full] at h_seq
  -- Reconcile the exit PC.
  have hexit : (hbase + 40 : Word) + BitVec.ofNat 64
      (4 * (laX18Prog hi3 lo3 ;; evm_blockhash .x20 .x18 .x14 .x16 .x19).length)
      = (hbase + 48) + 112 := by rw [laX18_body_length]; bv_omega
  rw [hexit]
  exact h_seq

-- ============================================================================
-- Step 4: the concrete `h_BLOCKHASH` handler-level spec
-- ============================================================================

/-- **The verified `h_BLOCKHASH` handler subroutine** (opcode 0x40). The full
    emitted glue — the 10-instruction stack-underflow guard (`negOff = -32`,
    word count 1), the `la x18, evm_block_hashes` table-base load, the verified
    `evm_blockhash` body, and the `.advanceAndRet 1` tail — as one
    `cpsTripleWithin` from `hbase` to the dispatcher return `x1_init &&& ~~~1`.

    On stack underflow (`curTop - 32 <u nsp`) the halt flag is set to routing
    code 7 and the EVM state is untouched (`x10` not advanced). Otherwise the
    body's stack post holds — the target block number `w` is popped and, in
    place at the stack top, replaced by `hashes[count - (cur - w)]` when `w` is
    a valid recent block (high limbs zero, `w <u cur`, and the age within the
    loaded window) or by `0` otherwise — and `x10` (the EVM code pointer)
    advances by 1.

    `hla1`/`hla2` reconstruct the guard's `la evm_cur_stack_top` / `la
    evm_halt_flag`; `hla3` reconstructs `la x18, evm_block_hashes`. These tie the
    symbolic `la` immediates to their target cells (the deferred byte-check
    would discharge them against the emitted ELF). This is the BLOCKHASH analogue
    of `BlobHashGuardedHandlerSpec.evm_blobhash_guarded_handler_spec`.

    Reuses `GuardedHandlerSpecs.guardedHandlerX14Spec` verbatim: the guard's
    residual `x14` is BLOCKHASH's arbitrary `tgtReg` input, so no reg-generic
    template is needed (see file header). -/
theorem evm_blockhash_guarded_handler_spec
    (hbase envAddr nsp tblAddr cell flag : Word)
    (w : EvmWord) (cur count : Word) (hashes rest : List EvmWord)
    (tmpOld valOld x18g v5 v6 : Word)
    (x10_init x1_init x14_init curTop f0 : Word)
    (hi1 : BitVec 20) (lo1 : BitVec 12) (hi2 : BitVec 20) (lo2 : BitVec 12)
    (hi3 : BitVec 20) (lo3 : BitVec 12)
    (hla1 : hbase + ((hi1.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo1 = cell)
    (hla2 : hbase + 20 + 4 + ((hi2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo2 = flag)
    (hla3 : (hbase + 40) + ((hi3.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo3 = tblAddr)
    (hcount : count.toNat ≤ hashes.length) :
    cpsTripleWithin 33 hbase (x1_init &&& ~~~1)
      (guardedCleanRetHandlerCode hbase hi1 lo1 hi2 lo2 (-32)
        (laX18Prog hi3 lo3 ;; evm_blockhash .x20 .x18 .x14 .x16 .x19) 1)
      (((((.x12 : Reg) ↦ᵣ nsp) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
          (((.x18 : Reg) ↦ᵣ x18g) ** ((.x16 : Reg) ↦ᵣ tmpOld) ** ((.x19 : Reg) ↦ᵣ valOld) **
           ((.x20 : Reg) ↦ᵣ envAddr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           evmStackIs nsp (w :: rest) **
           ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
           ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count) **
           evmStackIs tblAddr hashes)) **
         ((.x10 : Reg) ↦ᵣ x10_init) ** ((.x1 : Reg) ↦ᵣ x1_init)) **
        ((.x14 : Reg) ↦ᵣ x14_init) ** (cell ↦ₘ curTop) ** (flag ↦ₘ f0))
      (if BitVec.ult (curTop + signExtend12 (-32 : BitVec 12)) nsp then
        ((((.x12 : Reg) ↦ᵣ nsp) ** ((.x5 : Reg) ↦ᵣ (7 : Word)) ** ((.x6 : Reg) ↦ᵣ flag) **
          (((.x18 : Reg) ↦ᵣ x18g) ** ((.x16 : Reg) ↦ᵣ tmpOld) ** ((.x19 : Reg) ↦ᵣ valOld) **
           ((.x20 : Reg) ↦ᵣ envAddr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           evmStackIs nsp (w :: rest) **
           ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
           ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count) **
           evmStackIs tblAddr hashes)) **
          ((.x10 : Reg) ↦ᵣ x10_init) ** ((.x1 : Reg) ↦ᵣ x1_init)) **
          ((.x14 : Reg) ↦ᵣ (curTop + signExtend12 (-32 : BitVec 12))) **
          (cell ↦ₘ curTop) ** (flag ↦ₘ (7 : Word))
      else
        ((((.x12 : Reg) ↦ᵣ nsp) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
          (regOwn .x18 ** regOwn .x14 ** regOwn .x16 ** regOwn .x19 **
           ((.x20 : Reg) ↦ᵣ envAddr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           evmStackIs nsp
             ((if w.getLimbN 1 = 0 ∧ w.getLimbN 2 = 0 ∧ w.getLimbN 3 = 0 ∧
                  BitVec.ult (w.getLimbN 0) cur ∧ ¬ BitVec.ult count (cur - w.getLimbN 0)
               then hashes.getD (count - (cur - w.getLimbN 0)).toNat 0 else 0) :: rest) **
           ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
           ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count) **
           evmStackIs tblAddr hashes)) **
         ((.x10 : Reg) ↦ᵣ (x10_init + signExtend12 (1 : BitVec 12))) **
         ((.x1 : Reg) ↦ᵣ x1_init)) **
        (cell ↦ₘ curTop) ** (flag ↦ₘ f0)) := by
  have h_step1 := laX18_body_spec_within hbase envAddr nsp tblAddr
    (curTop + signExtend12 (-32 : BitVec 12)) tmpOld valOld x18g v5 v6
    w cur count hashes rest hi3 lo3 hla3 hcount
  have h_handler0 := cleanRetHandlerSpec' (by pcFree)
    (by rw [laX18_body_length]; decide) h_step1 (1 : BitVec 12) x10_init x1_init
  exact guardedHandlerX14Spec (P' :=
      ((.x18 : Reg) ↦ᵣ x18g) ** ((.x16 : Reg) ↦ᵣ tmpOld) ** ((.x19 : Reg) ↦ᵣ valOld) **
      ((.x20 : Reg) ↦ᵣ envAddr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      evmStackIs nsp (w :: rest) **
      ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
      ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count) **
      evmStackIs tblAddr hashes)
    hi1 lo1 hi2 lo2 (-32 : BitVec 12) (by omega) (by pcFree)
    (by rw [laX18_body_length]; decide) hla1 hla2
    v5 v6 x10_init x1_init x14_init curTop f0
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq)
      h_handler0)

/-- Structural pin: the full emitted `h_BLOCKHASH` program is 42 instructions
    (10 guard + 2 `la x18` + 28 body + 2 tail). A layout edit fails here. -/
theorem blockhash_guarded_handler_length
    (hi1 : BitVec 20) (lo1 : BitVec 12) (hi2 : BitVec 20) (lo2 : BitVec 12)
    (hi3 : BitVec 20) (lo3 : BitVec 12) :
    (guardedCleanRetHandlerProgram hi1 lo1 hi2 lo2 (-32)
      (laX18Prog hi3 lo3 ;; evm_blockhash .x20 .x18 .x14 .x16 .x19) 1).length = 42 := by
  unfold guardedCleanRetHandlerProgram
  show (stackUnderflowGuardProgram hi1 lo1 hi2 lo2 (-32)
    ++ cleanRetHandlerProgram (laX18Prog hi3 lo3 ;; evm_blockhash .x20 .x18 .x14 .x16 .x19) 1).length
      = 42
  rw [Program.length_append, cleanRetHandlerProgram_length, laX18_body_length,
    show (stackUnderflowGuardProgram hi1 lo1 hi2 lo2 (-32)).length = 10 from rfl]

-- Axiom audit: `laX18_body_spec_within`, `evm_blockhash_guarded_handler_spec`,
-- and `blockhash_guarded_handler_length` each kernel-depend only on
-- `[propext, Classical.choice, Quot.sound]` (the classical-3), verified by
-- `scripts/check-axioms.sh`; `#print axioms` omitted here to keep re-elaboration
-- output-free per the zero-warning policy.

end EvmAsm.Codegen.Proofs
