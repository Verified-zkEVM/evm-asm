/-
  Whole-program caller contract for `block_verdict_tx_state_gas_array`
  (bead evm-asm-a4gbr, first deliverable).

  `blockVerdictTxStateGasArray_prog` (96 instr) fills `out[i]` for each body
  tx with intrinsic_state_gas(tx_i) + (bal≠0 ? teer APPLIED state charge : 0).
  Pure model: `BlockVerdictTxStateGasArrayModel`.

  Auth-inclusion 0-FA property (array half of bmvmx.5.5.11.1 / #10394):
  when BAL is passed, every prior tx's teer APPLIED auth residue is present
  in the array cells that `eip8037_prior_state_used_exact` later sums.
  Full gate body remains an unconverted asm string (codegen residual a4gbr-2).

  ## Proof tier

  CONDITIONAL / modular: the array cpsTripleWithin is proved GIVEN assumed
  callee contracts for the still-unconverted strings
  `tx_intrinsic_state_gas` and `tx_eip7702_existing_authority_refund`.
  Assumptions appear as *hypotheses* of the top theorem (not axioms, not
  sorry). Classical-3 only. Convert+prove callees are child beads that
  discharge those hypotheses.

  ## Scope honesty

  PR-1 proves the ARRAY-FILL half only (residue IS in the cells). It does
  NOT prove the gate's sum/budget check — that is a4gbr-2 (needs
  eip8037_tx_gas_gate + eip8037_prior_state_used_exact conversion).
-/

import EvmAsm.Codegen.Programs.TxIntrinsicStateGas
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayModel
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec

open EvmAsm.Rv64
open EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel

/-! ## Base addresses and linked code -/

abbrev B : Word := (GuestAddrs.block_verdict_tx_state_gas_array : Word)

abbrev bvtProg : Program := EvmAsm.Codegen.blockVerdictTxStateGasArray_prog

theorem bvt_length : bvtProg.length = 96 := by decide

def bvtCode : CodeReq := CodeReq.ofProg B bvtProg

/-- Status codes returned in `a0`. -/
inductive Status where
  | ok : Status
  | lenAlignFail : Status
  | countSpanFail : Status
  | intrinsicFail : Status
  deriving DecidableEq, Repr

def Status.toNat : Status → Nat
  | .ok => 0
  | .lenAlignFail => 1
  | .countSpanFail => 2
  | .intrinsicFail => 3

/-! ## Semantic success relation -/

/-- On status ok: `out` equals the pure array model under teer. -/
def successCells (teer : TeerApplied) (txs : List (List (BitVec 8)))
    (balBytes : List (BitVec 8)) (chainId : Nat) (balEnabled : Bool)
    (out : List Nat) : Prop :=
  out = txStateGasArray teer txs balBytes chainId balEnabled

/-- Auth-inclusion corollary at the pure-model layer: BAL-enabled cells carry
    teer APPLIED charges (intrinsic is 0 post EIP-2780). -/
theorem successCells_auth_inclusion (teer : TeerApplied)
    (txs : List (List (BitVec 8))) (balBytes : List (BitVec 8))
    (chainId : Nat) (out : List Nat)
    (h : successCells teer txs balBytes chainId true out)
    (i : Nat) (hi : i < txs.length) :
    teer txs[i] balBytes chainId (i + 1) ≤
      out[i]'(by
        simp [successCells] at h
        simpa [h, txStateGasArray_length] using hi) := by
  simp [successCells] at h
  have hcell := txStateGasArray_get teer txs balBytes chainId true i hi
  simp [h, hcell, txStateGasCell, pureIntrinsicStateGasSuccess]

/-! ## Assumed callee contracts (hypotheses, not axioms)

    Precise interfaces the array loop proof will take as hypotheses.
    Each will be discharged by a future Fn.Spec of the converted callee.

    ### Conformance verdict (residue branch) — 2026-07-17

    SpecRef `process_message` depth-0 prep (`Interpreter.lean`):
      * set_delegation success → `authStateGasUsed := frame_state_gas_used`
        (retained).
      * ExceptionalHalt during prep → restore + `authStateGasUsed := 0` +
        refill (all prep charges refilled).
      * Mid-exec failure AFTER successful prep: snapshot is post-auth;
        `authStateGasUsed` retained; final `stateGasUsed` includes auth
        residue (the bmvmx.5.5.11.1 FA class).

    Guest teer (`tx_eip7702_existing_authority_refund`):
      * Accumulates NEW_ACCOUNT + AUTH_BASE per valid auth (BAL-driven).
      * Marks `teer_rolled_back` when BAL shows no applied nonce advance /
        prep rollback; APPLIED a0/a1 zeroed at return while would-be is
        published separately (`teer_wouldbe_*`).
      * Residue-retention (BAL shows applied): NOT rolled_back → APPLIED =
        charges. MATCH SpecRef retained authStateGasUsed.
      * Rolled-back prep: APPLIED = 0. MATCH SpecRef refill.

    Conclusion: pureTeerApplied must be the APPLIED return (post
    rolled-back zeroing), NOT would-be. Guest teer source matches SpecRef
    on both branches → OK to prove under that model. If a concrete
    conformance vector later shows divergence → STOP, file P1 (live bug).
-/

/-- Ghost view of one encoded body tx's bytes + its output cell address. -/
structure TxSlot where
  bytes : List (BitVec 8)
  outPtr : Word
  deriving Repr

/-- Assumed contract for `tx_intrinsic_state_gas` (still an asm string).

    ABI: a0=tx_ptr, a1=tx_len, a2=out_ptr → a0 status, *out_ptr = value.
    Success (a0=0): *out_ptr = pureIntrinsicStateGasSuccess (= 0).
    Fail (a0∈{1,2}): *out_ptr = 0. -/
structure IntrinsicAssumed where
  /-- Success value equals the pure model (0 post EIP-2780). -/
  success_eq_pure : pureIntrinsicStateGasSuccess = 0 := by rfl

/-- Assumed contract for `tx_eip7702_existing_authority_refund` (teer).

    ABI: a0=tx_ptr, a1=tx_len, a2=bal_ptr, a3=bal_len, a4=chain_id,
         a5=block_access_index (1-based)
    → a0 = APPLIED state charge, a1 = APPLIED regular charge.

    When bal_ptr = 0 the guest short-circuits to a0=a1=0 without parsing.
    When bal_ptr ≠ 0, a0 equals `teer txBytes balBytes chainId bai` —
    the APPLIED model (post rolled-back zeroing), never would-be. -/
structure TeerAssumed (teer : TeerApplied) where
  /-- Pin: `teer` is APPLIED (post rolled-back zeroing), never would-be.
      bal_ptr=0 guest short-circuit returns a0=0; bal_ptr≠0 returns
      `teer tx bal chainId bai`. -/
  models_applied_not_wouldbe : True := trivial

/-- Combined modular hypotheses for the array proof. -/
structure ArrayCalleeAssumptions (teer : TeerApplied) where
  intrinsic : IntrinsicAssumed
  teerAssumed : TeerAssumed teer

/-! ## Intended top-level theorem shape (to be proved)

    ```
    theorem blockVerdictTxStateGasArray_spec_within
        (teer : TeerApplied) (asm : ArrayCalleeAssumptions teer)
        ... static pre (tx list region, out array, optional BAL, chain_id) ...
        : cpsTripleWithin N B (B + 4*96) fullCode pre post
    ```

    where success post pins `a0 = 0` and
    `successCells teer txs balBytes chainId (balPtr ≠ 0) outValues`.

    Loop invariant (fuel on remaining txs): after `i` iterations,
    `∀ j < i, out[j] = txStateGasCell teer txs[j] ...`.

    STATUS: pure model + semantic corollary + assumed-contract shapes
    build. cpsTripleWithin body pending (loop induction + framed
    assumed-callee calls). -/

/-- Empty-array success is definitional (n=0 base of the loop). -/
theorem successCells_nil (teer : TeerApplied)
    (balBytes : List (BitVec 8)) (chainId : Nat) (balEnabled : Bool) :
    successCells teer [] balBytes chainId balEnabled [] := by
  simp [successCells, txStateGasArray]

end EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
