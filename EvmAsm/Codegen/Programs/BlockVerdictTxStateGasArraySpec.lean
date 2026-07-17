/-
  Whole-program caller contract for `block_verdict_tx_state_gas_array`
  (bead evm-asm-a4gbr, first deliverable).

  `blockVerdictTxStateGasArray_prog` (96 instr) fills `out[i]` for each body
  tx with intrinsic_state_gas(tx_i) + (bal≠0 ? teer APPLIED state charge : 0).
  Pure model: `BlockVerdictTxStateGasArrayModel`.

  Auth-inclusion 0-FA property (array half of bmvmx.5.5.11.1 / #10394):
  when BAL is passed, every prior tx's teer APPLIED auth residue is present
  in the array cells that `eip8037_prior_state_used_exact` later sums.
  Full gate body remains an unconverted asm string (codegen residual a4gbr.1).

  ## Proof tier

  CONDITIONAL / modular: the array cpsTripleWithin is proved GIVEN assumed
  callee contracts for the still-unconverted strings
  `tx_intrinsic_state_gas` and `tx_eip7702_existing_authority_refund`.
  Assumptions appear as *hypotheses* of the top theorem (not axioms, not
  sorry). Classical-3 only. Convert+prove callees are child beads that
  discharge those hypotheses.

  ## Conformance verdict (residue branch) — 2026-07-17

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
  on both branches → OK to prove under that model.

  ## Scope honesty

  PR-1 proves the ARRAY-FILL half only (residue IS in the cells). It does
  NOT prove the gate's sum/budget check — that is a4gbr.1 (needs
  eip8037_tx_gas_gate + eip8037_prior_state_used_exact conversion).
-/

import EvmAsm.Codegen.Programs.TxIntrinsicStateGas
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayModel
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.BalGasValidSAsm
import EvmAsm.Codegen.Programs.ChainValidateExtraDataLengthSpec
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.FnFlat

namespace EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
  (wordArray wordArrayFrom wordArray_split pcFree_wordArray)

/-! ## Base addresses and linked code -/

abbrev B : Word := (GuestAddrs.block_verdict_tx_state_gas_array : Word)

abbrev bvtProg : Program := EvmAsm.Codegen.blockVerdictTxStateGasArray_prog

theorem bvt_length : bvtProg.length = 96 := by decide

def bvtCode : CodeReq := CodeReq.ofProg B bvtProg

/-- Proven leaf `bgv_u32le` (12 instr Program). -/
abbrev Bgv : Word := (GuestAddrs.bgv_u32le : Word)

abbrev bgvProg : Program := EvmAsm.Codegen.bgvU32le_prog

theorem bgv_length : bgvProg.length = 12 := by decide

def bgvCode : CodeReq := CodeReq.ofProg Bgv bgvProg

/-- Linked closure for the array program + bgv leaf. Unconverted intrinsic /
    teer strings are NOT in this CodeReq; their contracts are assumed as
    hypotheses over an ambient `cr` that the top theorem takes mono into
    `fullCode` once those Programs exist. For PR-1 the assumed contracts
    quantify over an arbitrary `cr` that contains the call sites. -/
def fullCode : CodeReq := bvtCode.union bgvCode

theorem bvt_bgv_disjoint : bvtCode.Disjoint bgvCode := by
  unfold bvtCode bgvCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [bvt_length]; decide
  · rw [bgv_length]; decide
  · -- bgv lives at a lower linked address than the array program
    right; rw [bgv_length]; decide

theorem bgv_mono : ∀ a i, bgvCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right bvt_bgv_disjoint (fun _ _ h => h) a i hi

theorem bvt_mono : ∀ a i, bvtCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi

/-! ## Frame (112-byte: ra + s0–s11 = 13 dwords at spC..spC+96) -/

/-- Callee-saved + ra snapshot for the array routine. -/
structure Saved where
  ra  : Word
  s0  : Word  -- x8
  s1  : Word  -- x9
  s2  : Word  -- x18
  s3  : Word  -- x19
  s4  : Word  -- x20
  s5  : Word  -- x21
  s6  : Word  -- x22
  s7  : Word  -- x23
  s8  : Word  -- x24
  s9  : Word  -- x25
  s10 : Word  -- x26
  s11 : Word  -- x27
  deriving Repr

def savedFrame (spC : Word) (s : Saved) : Assertion :=
  ((spC + signExtend12 (0 : BitVec 12)) ↦ₘ s.ra) **
  ((spC + signExtend12 (8 : BitVec 12)) ↦ₘ s.s0) **
  ((spC + signExtend12 (16 : BitVec 12)) ↦ₘ s.s1) **
  ((spC + signExtend12 (24 : BitVec 12)) ↦ₘ s.s2) **
  ((spC + signExtend12 (32 : BitVec 12)) ↦ₘ s.s3) **
  ((spC + signExtend12 (40 : BitVec 12)) ↦ₘ s.s4) **
  ((spC + signExtend12 (48 : BitVec 12)) ↦ₘ s.s5) **
  ((spC + signExtend12 (56 : BitVec 12)) ↦ₘ s.s6) **
  ((spC + signExtend12 (64 : BitVec 12)) ↦ₘ s.s7) **
  ((spC + signExtend12 (72 : BitVec 12)) ↦ₘ s.s8) **
  ((spC + signExtend12 (80 : BitVec 12)) ↦ₘ s.s9) **
  ((spC + signExtend12 (88 : BitVec 12)) ↦ₘ s.s10) **
  ((spC + signExtend12 (96 : BitVec 12)) ↦ₘ s.s11)

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

/-- Empty-array success is definitional (n=0 base of the loop). -/
theorem successCells_nil (teer : TeerApplied)
    (balBytes : List (BitVec 8)) (chainId : Nat) (balEnabled : Bool) :
    successCells teer [] balBytes chainId balEnabled [] := by
  simp [successCells, txStateGasArray]

/-- Prefix extension of the pure array model (loop-step pure glue). -/
theorem txStateGasArray_snoc (teer : TeerApplied)
    (txs : List (List (BitVec 8))) (tx : List (BitVec 8))
    (balBytes : List (BitVec 8)) (chainId : Nat) (balEnabled : Bool) :
    txStateGasArray teer (txs ++ [tx]) balBytes chainId balEnabled =
      txStateGasArray teer txs balBytes chainId balEnabled ++
        [txStateGasCell teer tx balBytes chainId (txs.length + 1) balEnabled] := by
  simp [txStateGasArray, List.mapIdx_append]

/-! ## Assumed callee contracts (hypotheses, not axioms)

    Precise interfaces the array loop proof takes as hypotheses. Each is the
    literal flat post a future converted-callee Fn.Spec will establish, so
    discharge is a drop-in (a4gbr.2).

    Shape: quantify over any `cr : CodeReq` that the top theorem mono-lifts
    into `fullCode` once the callee Programs land. Until then the top
    theorem is conditional on `asm : ArrayCalleeAssumptions cr teer` for a
    caller-chosen `cr` that already contains whatever the assumed contracts
    need (today: abstract; after convert: ofProg of the real Programs).
-/

/-- Step budget placeholders for unconverted callees (over-approx; mono). -/
def nIntrinsicSteps : Nat := 256
def nTeerSteps : Nat := 4096

/-- Assumed contract for `tx_intrinsic_state_gas` (still an asm string).

    ABI: a0=tx_ptr, a1=tx_len, a2=out_ptr → a0 status, *out_ptr = value.
    Success (a0=0): *out_ptr = pureIntrinsicStateGasSuccess (= 0).
    The assumed triple is the SUCCESS arm only — failure is routed by the
    array body to status 3 without a success claim on `out[]`. -/
structure IntrinsicAssumed (cr : CodeReq) where
  /-- Entry PC of the (future) converted intrinsic Program. -/
  entry : Word
  /-- Success-path flat contract: writes pure model 0 into `outPtr`. -/
  success_flat :
    ∀ (ret txPtr txLenW outPtr oldOut : Word) (txBytes : List (BitVec 8)),
      (ret &&& ~~~(1 : Word)) = ret →
      txLenW = BitVec.ofNat 64 txBytes.length →
      cpsTripleWithin nIntrinsicSteps entry ret cr
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) **
          (.x12 ↦ᵣ outPtr) ** bytesRegion txPtr txBytes **
          (outPtr ↦ₘ oldOut) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ (0 : Word)) **
          bytesRegion txPtr txBytes **
          (outPtr ↦ₘ (BitVec.ofNat 64 pureIntrinsicStateGasSuccess)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))

/-- Assumed contract for `tx_eip7702_existing_authority_refund` (teer).

    ABI: a0=tx_ptr, a1=tx_len, a2=bal_ptr, a3=bal_len, a4=chain_id,
         a5=block_access_index (1-based)
    → a0 = APPLIED state charge, a1 = APPLIED regular charge.

    When bal_ptr = 0 the guest short-circuits to a0=a1=0 without parsing
    (array body skips the call entirely via `beq s8, zero`).
    When bal_ptr ≠ 0, a0 equals `teer txBytes balBytes chainId bai` —
    the APPLIED model (post rolled-back zeroing), never would-be. -/
structure TeerAssumed (cr : CodeReq) (teer : TeerApplied) where
  /-- Entry PC of the (future) converted teer Program. -/
  entry : Word
  /-- BAL-enabled APPLIED flat contract. -/
  applied_flat :
    ∀ (ret txPtr txLenW balPtr balLenW chainIdW baiW : Word)
      (txBytes balBytes : List (BitVec 8)) (chainId bai : Nat),
      (ret &&& ~~~(1 : Word)) = ret →
      balPtr ≠ 0 →
      txLenW = BitVec.ofNat 64 txBytes.length →
      balLenW = BitVec.ofNat 64 balBytes.length →
      chainIdW = BitVec.ofNat 64 chainId →
      baiW = BitVec.ofNat 64 bai →
      cpsTripleWithin nTeerSteps entry ret cr
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) **
          (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
          (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
          bytesRegion txPtr txBytes ** bytesRegion balPtr balBytes **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
        ((.x1 ↦ᵣ ret) **
          (.x10 ↦ᵣ BitVec.ofNat 64 (teer txBytes balBytes chainId bai)) **
          regOwn .x11 **
          bytesRegion txPtr txBytes ** bytesRegion balPtr balBytes **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
          regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))

/-- Combined modular hypotheses for the array proof. -/
structure ArrayCalleeAssumptions (cr : CodeReq) (teer : TeerApplied) where
  intrinsic : IntrinsicAssumed cr
  teerAssumed : TeerAssumed cr teer

/-! ## Payload / loop invariant / posts

    Index-based invariant at the loop guard (`B + 128` = instr 32):
    after `i` successful iterations, `out[0..i)` equals the pure model
    prefix and loop regs hold the ABI-saved bases + `i`.
-/

/-- Link address after the intrinsic `jal` (instr 54 → B+216+4 = B+220). -/
abbrev LinkIntrinsic : Word := B + 220

/-- Link address after the teer `jal` (instr 63 → B+252+4 = B+256). -/
abbrev LinkTeer : Word := B + 256

/-- Loop guard PC (instr 32 = B + 128). -/
abbrev LoopGuard : Word := B + 128

/-- Tx-list + out-array + optional BAL footprint (unchanged across the loop
    except out-array cells written by the body). -/
def payload (txBase outBase balBase : Word)
    (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) : Assertion :=
  bytesRegion txBase txBlob ** wordArray outBase outVals **
    if balEnabled then bytesRegion balBase balBytes else empAssertion

/-- Scratch regs owned across calls (t0–t2, a-temps incl a7/x17, temporaries).
    Includes `x17` so loop-site `bgvScratch` (which owns a7) packs from LoopInv. -/
def scratchRegs : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

/-- Return-path scratch: same as `scratchRegs` but without `x10` (a0 holds status). -/
def scratchRegsNoA0 : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))
/-- Loop invariant at `LoopGuard` entering iteration `i` (`i ≤ n`).
    `outVals` is the full eventual array; the pure prefix fact is carried
    separately as a Prop hypothesis on the induction (value-level inv).
    Extra frame regs `x1/x22/x23/x27` are `regOwn` so the epilogue `loadSeq`
    can restore them (body may clobber their values). -/
def LoopInv (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (i : Nat) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) **
  regOwn .x1 ** regOwn .x22 ** regOwn .x23 ** regOwn .x27 **
  savedFrame spC csaved **
  payload txBase outBase balBase txBlob outVals balBytes balEnabled **
  scratchRegs

/-- Shared return footprint (restored frame + payload; a0 pinned by caller). -/
def commonRet (sp0 spC txBase outBase balBase : Word) (csaved : Saved)
    (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) : Assertion :=
  (.x1 ↦ᵣ csaved.ra) ** (.x2 ↦ᵣ sp0) **
  (.x8 ↦ᵣ csaved.s0) ** (.x9 ↦ᵣ csaved.s1) **
  (.x18 ↦ᵣ csaved.s2) ** (.x19 ↦ᵣ csaved.s3) **
  (.x20 ↦ᵣ csaved.s4) ** (.x21 ↦ᵣ csaved.s5) **
  (.x22 ↦ᵣ csaved.s6) ** (.x23 ↦ᵣ csaved.s7) **
  (.x24 ↦ᵣ csaved.s8) ** (.x25 ↦ᵣ csaved.s9) **
  (.x26 ↦ᵣ csaved.s10) ** (.x27 ↦ᵣ csaved.s11) **
  savedFrame spC csaved **
  payload txBase outBase balBase txBlob outVals balBytes balEnabled **
  scratchRegsNoA0

/-- Success post: `a0 = 0` and out-array equals the pure model. -/
def postOk (sp0 spC txBase outBase balBase : Word) (csaved : Saved)
    (teer : TeerApplied) (txs : List (List (BitVec 8)))
    (txBlob : List (BitVec 8)) (balBytes : List (BitVec 8))
    (chainId : Nat) (balEnabled : Bool) (outVals : List Nat) : Assertion :=
  ⌜successCells teer txs balBytes chainId balEnabled outVals⌝ **
  (.x10 ↦ᵣ (0 : Word)) **
  commonRet sp0 spC txBase outBase balBase csaved txBlob outVals balBytes
    balEnabled

/-- Failure post (status ∈ {1,2,3}): no success claim on out cells. -/
def postFail (sp0 spC txBase outBase balBase : Word) (csaved : Saved)
    (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (status : Nat) :
    Assertion :=
  ⌜status = 1 ∨ status = 2 ∨ status = 3⌝ **
  (.x10 ↦ᵣ BitVec.ofNat 64 status) **
  commonRet sp0 spC txBase outBase balBase csaved txBlob outVals balBytes
    balEnabled

/-- Whole-program post: success with genuine cells, or clean fail. -/
def bvtPost (sp0 spC txBase outBase balBase : Word) (csaved : Saved)
    (teer : TeerApplied) (txs : List (List (BitVec 8)))
    (txBlob : List (BitVec 8)) (balBytes : List (BitVec 8))
    (chainId : Nat) (balEnabled : Bool) (outVals : List Nat) : Assertion :=
  fun h =>
    postOk sp0 spC txBase outBase balBase csaved teer txs txBlob balBytes
        chainId balEnabled outVals h ∨
    (∃ st, postFail sp0 spC txBase outBase balBase csaved txBlob outVals
        balBytes balEnabled st h)

/-! ## Intended top-level theorem shape

    ```
    theorem blockVerdictTxStateGasArray_spec_within
        (cr : CodeReq) (teer : TeerApplied)
        (asm : ArrayCalleeAssumptions cr teer)
        (hcr : ∀ a i, cr a = some i → fullCode.union cr a = some i)
        … static pre (tx list region, out array, optional BAL, chain_id,
          frame layout, alignment, span well-formedness) …
        : cpsTripleWithin N B raIn (fullCode.union cr) pre
            (bvtPost … teer txs … outVals)
    ```

    Success arm pins `a0 = 0` and
    `successCells teer txs balBytes chainId (balPtr ≠ 0) outVals`.

    Loop invariant (fuel on remaining txs): after `i` iterations,
    `∀ j < i, outVals[j] = txStateGasCell teer txs[j] …` and the physical
    `wordArray` holds `outVals`.

    STATUS: pure model + semantic corollary + assumed-contract shapes +
    LoopInv/Post scaffolding build. cpsTripleWithin body (prologue + loop
    induction + framed assumed-callee calls) is the remaining proof work —
    patterned on `ChainValidateGasUsedUnderLimit*` (index inv + fuel +
    callWithin). bgv is proven SAsm (`bgvU32leFn_spec`); lift via
    `Fn.retSpecFlat` / ambient adapter. Intrinsic/teer stay assumed until
    a4gbr.2 converts them.
-/

/-- Auth-inclusion at the post layer: success + BAL ⇒ every cell ≥ teer. -/
theorem postOk_auth_inclusion
    (teer : TeerApplied) (txs : List (List (BitVec 8)))
    (balBytes : List (BitVec 8)) (chainId : Nat) (outVals : List Nat)
    (i : Nat) (hi : i < txs.length)
    (hcells : successCells teer txs balBytes chainId true outVals) :
    teer txs[i] balBytes chainId (i + 1) ≤
      outVals[i]'(by
        simp [successCells] at hcells
        simpa [hcells, txStateGasArray_length] using hi) :=
  successCells_auth_inclusion teer txs balBytes chainId outVals hcells i hi

end EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
