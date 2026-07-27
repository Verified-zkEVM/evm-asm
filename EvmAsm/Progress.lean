/-
  EvmAsm.Progress

  Drift-proof registry of per-opcode verification state across the
  143 EVM opcode bytes modeled by `EvmAsm.Evm64.EvmOpcode`. The
  registry is the single source of truth for the coverage tables in
  `PROGRESS.md`; renaming or deleting a theorem named below fails
  this file's elaboration via the witness `abbrev`s at the bottom.

  See `scripts/progress-report.sh` for how the registry is consumed.
  See `PROGRESS.md` for the rendered report.

  Conventions:
  * `ProofTier` classifies an `EvmOpcode` constructor by how deep
    its verification reaches.
  * `OpcodeEntry` is one row of the registry.
  * Parameterized opcode families (`DUP n`, `SWAP n`, `LOG kind`)
    are one row each.
  * Counts are kernel-checked via `by decide` theorems.
-/

import EvmAsm.Evm64.Add.Spec
import EvmAsm.Evm64.Sub.Spec
import EvmAsm.Evm64.Multiply.Spec
import EvmAsm.Evm64.SignExtend.Spec
import EvmAsm.Evm64.And.Spec
import EvmAsm.Evm64.Or.Spec
import EvmAsm.Evm64.Xor.Spec
import EvmAsm.Evm64.Not.Spec
import EvmAsm.Evm64.Byte.Spec
import EvmAsm.Evm64.Shift.Semantic
import EvmAsm.Evm64.Shift.ShlSemantic
import EvmAsm.Evm64.Shift.SarSemantic
import EvmAsm.Evm64.Lt.Spec
import EvmAsm.Evm64.Gt.Spec
import EvmAsm.Evm64.Eq.Spec
import EvmAsm.Evm64.IsZero.Spec
import EvmAsm.Evm64.Slt.Spec
import EvmAsm.Evm64.Sgt.Spec
import EvmAsm.Evm64.Pop.Spec
import EvmAsm.Evm64.Push0.Spec
import EvmAsm.Evm64.Push.Spec
import EvmAsm.Evm64.Push.ImmediateCompose
import EvmAsm.Evm64.Dup.Spec
import EvmAsm.Evm64.Swap.Spec
import EvmAsm.Evm64.MSize.Spec
import EvmAsm.Stateless.State.AccountAssertions
import EvmAsm.Evm64.MLoad.MemoryRegionStackSpec
import EvmAsm.Evm64.MptAssertions
import EvmAsm.Evm64.MptCorrespondence
import EvmAsm.Evm64.WitnessAssertions
import EvmAsm.Evm64.MStore8.Spec
import EvmAsm.Evm64.MLoad.UnalignedFramedStackSpec
import EvmAsm.Evm64.MStore.UnalignedFramedStackSpec
import EvmAsm.Evm64.DivMod.Spec.Unified
import EvmAsm.Evm64.DivMod.V5StackSurfaceShared
import EvmAsm.Evm64.DivMod.Compose.V6DivStackSpec
import EvmAsm.Evm64.SDiv.SpecShared
import EvmAsm.Evm64.SDiv.Compose.StackSpecV5
import EvmAsm.Evm64.SDiv.Compose.ResultStackV5
import EvmAsm.Evm64.SMod.Compose.StackSpecV5
import EvmAsm.Evm64.SMod.Compose.ResultStackV5
import EvmAsm.Evm64.SMod.SpecAllCase
import EvmAsm.Evm64.AddMod.ResultTotalShared
import EvmAsm.Evm64.MulMod.Compose.StackSpecAll
import EvmAsm.Evm64.Exp.Spec
import EvmAsm.Evm64.Exp.HeadroomProgramSpec
import EvmAsm.Evm64.Exp.StackExecutionBridge
import EvmAsm.Evm64.Env.Wrappers
import EvmAsm.Evm64.Calldata.SizeSpec
import EvmAsm.Evm64.Code.SizeSpec
import EvmAsm.Evm64.ControlFlow.PcSpec
import EvmAsm.Evm64.ControlFlow.JumpSpec
import EvmAsm.Evm64.ControlFlow.JumpiSpec
import EvmAsm.Evm64.GasOpcode.Spec
import EvmAsm.Evm64.ReturnData.SizeSpec
import EvmAsm.Evm64.BlobBaseFee.Spec
import EvmAsm.Evm64.BlobHash.Spec
import EvmAsm.Evm64.BlockHash.Spec
import EvmAsm.Evm64.Code.CopyLoopSpec
import EvmAsm.Evm64.ControlFlow.Jumpdest
import EvmAsm.Evm64.Calldata.StageSpec
import EvmAsm.Evm64.Calldata.CopySpec
import EvmAsm.Evm64.Calldata.CopyLoopSpec
import EvmAsm.Evm64.Terminating.StopSpec
import EvmAsm.Evm64.Terminating.InvalidSpec
import EvmAsm.Evm64.Terminating.ReturnHaltSpec
import EvmAsm.Evm64.Terminating.ReturnSpec
import EvmAsm.Evm64.Terminating.ReturnCaptureSpec
import EvmAsm.Evm64.Terminating.ReturnHaltResolved
import EvmAsm.Evm64.Terminating.RevertSpec
import EvmAsm.Evm64.Terminating.SelfdestructSpec
import EvmAsm.Evm64.Terminating.SelfdestructHaltResolved
import EvmAsm.Evm64.Transient.StoreSpec
import EvmAsm.Evm64.Transient.LoadSpec
import EvmAsm.Evm64.Storage.LoadSpec
import EvmAsm.Evm64.Mcopy.Spec
import EvmAsm.Evm64.ReturnData.CopySpec

namespace EvmAsm.Progress

/-- Verification depth for one EVM opcode (or parameterized family). -/
inductive ProofTier
  /-- Top-level stack-level Hoare triple is proven for the full opcode. -/
  | proven
  /-- Program defined + `EvmWord.<op>_correct` theorem proven, but no
      top-level `evm_<op>_stack_spec_within` wrap yet. -/
  | partly
  /-- Top-level Hoare triple proven, but gated by a nonvacuous input-domain
      precondition (e.g. DIV/MOD `b.getLimbN 3 = 0`, SDIV `hStack`) — distinct
      from `partly` (no complete triple). The dashboard shows domain coverage,
      not blurred existence. -/
  | conditional
  /-- Pure executable-spec / handler / bridge semantics only; no RV64
      subroutine produces the EVM result for this opcode. -/
  | execSpec
  /-- Not represented in `EvmOpcode` yet (e.g. unimplemented EIPs). -/
  | notStarted
  deriving DecidableEq, BEq, Repr

/-- One row of the progress registry. -/
structure OpcodeEntry where
  /-- Display name; usually the EVM mnemonic. Parameterized families
      use a width range, e.g. "PUSH1" or "DUP1..16". -/
  name : String
  /-- Verification depth. -/
  tier : ProofTier
  /-- Best-available witness theorem name, for diff readability. -/
  proofRef : Option String
  /-- Optional short note for the rendered report. -/
  notes : String := ""
  /-- Worst-case `cpsTripleWithin N` step bound for the witness theorem, when
      one exists. Typed source of truth for the C.1 cycle-bound surrogate: a
      silent `cpsTripleWithin 30 → 100` inflation now shows up as a registry
      diff rather than buried in a free-text note (R-C4). `none` where the
      opcode has no single literal bound (DivMod uses `unifiedDivBound`) or no
      top-level triple yet. The kernel-checked *binding* of this `N` to the
      theorem's literal is deferred — see PLAN.md follow-up. -/
  cycleBound : Option Nat := none
  /-- Optional graded sub-lemma milestones (decode / stack-effect /
      memory-effect / gas / composed-triple) so a long opcode push emits
      incremental signal (R-A4). Empty = no milestone scaffold recorded. -/
  milestones : List String := []
  /-- For a `conditional` entry: name of a `…_precondition_reachable` lemma
      (`decide`-checked on representative real inputs) proving the gating
      antecedent is *satisfiable* — the anti-near-vacuity cover property
      (R-A3). `none` until such a lemma is written. -/
  coverRef : Option String := none
  deriving Repr

/-- Smart constructor for a registry row. Keeps the optional fields
    (`cycleBound`, `milestones`, `coverRef`) defaulted so common rows stay
    terse and only the entries that carry the extra data spell them out
    (typically via the named `(cycleBound := N)` / `(coverRef := …)` args).
    The anonymous `⟨…⟩` constructor cannot omit trailing defaulted fields, so
    this wrapper is what makes the defaults usable in the registry literal. -/
def entry (name : String) (tier : ProofTier) (proofRef : Option String)
    (notes : String := "") (cycleBound : Option Nat := none)
    (milestones : List String := []) (coverRef : Option String := none) :
    OpcodeEntry :=
  { name, tier, proofRef, notes, cycleBound, milestones, coverRef }

/-! ## Registry

    Ordering follows EVM opcode bytes 0x00..0xff for easy cross-reference
    with `EvmAsm.Evm64.EvmOpcode.byte?`. -/
def registry : List OpcodeEntry := [
  -- Stop and arithmetic (0x00..0x0b)
  entry "STOP" .proven (some "evm_stop_stack_spec_within")
      ("halt-triple over the verified `evm_stop` program (byte image of the "
       ++ "emitted `dispatchHaltRet 1` tail): sets `evm_halt_flag := 1`, points "
       ++ "x1 at `.Ldispatch_resume`, and rets to `resume &&& ~~~1`; the two "
       ++ "`la`s stay `hla1`/`hla2` reconstruction hyps as in the guard/glue "
       ++ "precedents. First terminating/halt opcode — shape for INVALID/RETURN/"
       ++ "REVERT/SELFDESTRUCT")
      (cycleBound := some 7),
  entry "ADD" .proven (some "evm_add_stack_spec_within") (cycleBound := some 30),
  entry "MUL" .proven (some "evm_mul_stack_spec_within") (cycleBound := some 63),
  entry "SUB" .proven (some "evm_sub_stack_spec_within") (cycleBound := some 30),
  entry "DIV" .proven (some "evm_div_v6_stack_spec")
      ("full-domain unconditional v6 DIV stack spec over divCodeV6 (n=1 " ++
       "single-limb fast-path dispatch); the n≥2 / b=0 arm reuses the v5 " ++
       "proof (evm_div_v5_unconditional_over_divCodeV6), the n=1 fast arm is " ++
       "divK_fastBody_dispatchPostV5_within_v6, merged via the BNE/BEQ dispatch"),
  entry "SDIV" .proven (some "evm_sdiv_exact_callable_return_result_stack_spec_within_v5")
      ("unconditional SDIV stack spec over sdivCodeV5 (the shipped v5 codegen — " ++
       "signed DIV via the proven unsigned evm_div_callable_v5); the former " ++
       "hStack is discharged by M2's callable correctness, incoming x2/x9 " ++
       "generalized (both dead), x9 shed at the return"),
  entry "MOD" .proven (some "evm_mod_v6_stack_spec")
      ("full-domain unconditional v6 MOD stack spec over modCodeV6 (n=1 " ++
       "single-limb fast-path dispatch); the n≥2 / b=0 arm reuses the v5 " ++
       "proof (evm_mod_v5_unconditional_over_modCodeV6), the n=1 fast arm is " ++
       "modK_fastBody_dispatchPostV5_within_v6, merged via the BNE/BEQ dispatch"),
  entry "SMOD" .proven
      (some "evm_smod_exact_callable_return_result_stack_spec_within_v5")
      ("unconditional SMOD stack spec over smodCodeV5 (the shipped v5 codegen — " ++
       "signed MOD via the proven unsigned evm_mod_callable_v5); the former " ++
       "hStack is discharged by M2's callable correctness, incoming x2/x9 " ++
       "generalized (both dead), x9 shed at the return.  (was: " ++
       "nonzero path still parameterized by unsigned-MOD callable h_stack"),
  entry "ADDMOD" .proven (some "evm_addmod_total_result_stack_spec_within")
      ("unconditional total ADDMOD stack spec over evm_addmod_total ∪ " ++
       "evm_mod_callable_v5 (the shipped codegen — issue #9704): all three " ++
       "runtime branches covered (N = 0 zero path; no-carry low-sum " ++
       "reduction; the 257-bit carry-out path computing (2^256 + r) mod N " ++
       "via three MOD near-calls — rMod, pow256ModN N as ((2^256−1) mod N " ++
       "+ 1) mod N, and a pre-reduced modular add with branch-free " ++
       "conditional subtract). Public form evmStackIs sp [a, b, N] → " ++
       "evmStackIs (sp+64) [EvmWord.addmod a b N]; only dispatcher-pinned " ++
       "code-layout side conditions.  (was: partial OR-guard domain " ++
       "surface over the legacy v1 callable)"),
  entry "MULMOD" .proven (some "evm_mulmod_stack_spec_within")
      ("full-domain unconditional MULMOD stack spec for every modulus (no " ++
       "n ≤ 2^255 hypothesis); bit-serial 512-bit reducer. Scratchpad " ++
       "relocated below the stack pointer (sp + signExtend12 3936..4088 = " ++
       "sp-160..sp-8) so the live EVM stack is preserved")
      (cycleBound := some 34295),
  entry "EXP" .proven (some "evm_exp_stack_spec_within")
      ("unconditional EXP stack spec over the concrete appended headroom " ++
       "program (evm_exp_msb_saved_bit_two_mul_fixed_headroom ;; mul_callable, " ++
       "CodeReq.ofProg): full 256-iteration square-and-multiply loop via the " ++
       "proven MUL callable; pre = evmStackIs evmSp (base :: exponent :: rest) " ++
       "plus an explicit x2 local frame and 8 headroom dwords + 2 scratch EVM " ++
       "words below the live stack (evmSp-128..evmSp-32 — MULMOD below-sp " ++
       "precedent); post = evmStackIs (evmSp+32) (EvmWord.exp base exponent " ++
       ":: rest) with clobbered state shed to evmExpHeadroomPublicLeftoverFrame; " ++
       "only side condition is the even entry base.  (was: partial headroom " ++
       "surface pending the public wrapper)")
      (cycleBound := some 49447),
  entry "SIGNEXTEND" .proven (some "evm_signextend_stack_spec_within") (cycleBound := some 28),

  -- Comparison and bitwise (0x10..0x1d)
  entry "LT" .proven (some "evm_lt_stack_spec_within") (cycleBound := some 26),
  entry "GT" .proven (some "evm_gt_stack_spec_within") (cycleBound := some 26),
  entry "SLT" .proven (some "evm_slt_stack_spec_within") (cycleBound := some 25),
  entry "SGT" .proven (some "evm_sgt_stack_spec_within") (cycleBound := some 25),
  entry "EQ" .proven (some "evm_eq_stack_spec_within") (cycleBound := some 21),
  entry "ISZERO" .proven (some "evm_iszero_stack_spec_within") (cycleBound := some 12),
  entry "AND" .proven (some "evm_and_stack_spec_within") (cycleBound := some 17),
  entry "OR" .proven (some "evm_or_stack_spec_within") (cycleBound := some 17),
  entry "XOR" .proven (some "evm_xor_stack_spec_within") (cycleBound := some 17),
  entry "NOT" .proven (some "evm_not_stack_spec_within") (cycleBound := some 12),
  entry "BYTE" .proven (some "evm_byte_stack_spec_within") (cycleBound := some 29),
  entry "SHL" .proven (some "evm_shl_stack_spec_within") (cycleBound := some 90),
  entry "SHR" .proven (some "evm_shr_stack_spec_within") (cycleBound := some 90),
  entry "SAR" .proven (some "evm_sar_stack_spec_within") (cycleBound := some 95),

  -- KECCAK (0x20)
  entry "KECCAK256" .execSpec none
      "delegated to zkvm_keccak256 accelerator; EL/Keccak*Bridge",

  -- Environment (0x30..0x3e)
  entry "ADDRESS" .proven (some "Env.evm_address_stack_spec_within"),
  entry "BALANCE" .execSpec none "witness-backed account read",
  entry "ORIGIN" .proven (some "Env.evm_origin_stack_spec_within"),
  entry "CALLER" .proven (some "Env.evm_caller_stack_spec_within"),
  entry "CALLVALUE" .proven (some "Env.evm_callvalue_stack_spec_within"),
  entry "CALLDATALOAD" .proven
      (some "Calldata.evm_calldataload_staged_stack_spec_within"),
  entry "CALLDATASIZE" .proven
      (some "Calldata.evm_calldatasize_stack_spec_within"),
  entry "CALLDATACOPY" .proven
      (some "Calldata.evm_calldatacopy_stack_spec_within"),
  entry "CODESIZE" .proven (some "Code.evm_codesize_stack_spec_within"),
  entry "CODECOPY" .proven (some "Code.evm_codecopy_stack_spec_within")
      "copy-loop body proven (mirror of CALLDATACOPY); preBody gas/MSIZE glue unverified per DRIFT",
  entry "GASPRICE" .proven (some "Env.evm_gasprice_stack_spec_within"),
  entry "EXTCODESIZE" .execSpec none "witness-backed account read",
  entry "EXTCODECOPY" .execSpec none "witness-backed code copy",
  entry "RETURNDATASIZE" .proven
      (some "ReturnData.evm_returndatasize_stack_spec_within"),
  entry "RETURNDATACOPY" .proven
      (some "ReturnData.evm_returndatacopy_body_stack_spec_within")
      ("whole-body stack triple over guards ++ setup ++ copy loop "
       ++ "(ReturnData/{RevertProgram,RevertSpec,CopyProgram,CopyLoopSpec,"
       ++ "CopySpec}.lean), base→base+80, composed with "
       ++ "cpsTripleWithin_seq_perm_same_cr: the guard prefix loads the three low "
       ++ "stack limbs, materializes `evm_precompile_frame`, loads the return-data "
       ++ "length and falls through the two execution-specs bounds checks "
       ++ "(start+size wrap, start+size>retlen — the old 256-byte frame cap was "
       ++ "removed from the guest in #10160); setup pops the operands, takes the "
       ++ "size≠0 skip and builds the pointers; the byte-identical bottom-tested "
       ++ "`do..while` loop copies stagedBytes[start..start+size) into EVM memory "
       ++ "[destOff,destOff+size) via the Mcopy forward-loop content model, with "
       ++ "the source region anchored at the aligned frame+16 base and the read "
       ++ "offset carried in the pointer register (decoupled from destOff). The "
       ++ "two invalid exits are companion witnesses "
       ++ "(guard_{wrap,len}_invalid_stack). Same scope as CALLDATACOPY's "
       ++ "registered witness: interleaved gas/OOG/MSIZE glue is framed out per "
       ++ "DRIFT. RESIDUAL: the handler's high-limb operand check (ld/or/or/bnez "
       ++ "on limbs 1-3 of the source offset) lives in that framed-out region, so "
       ++ "the witness ASSUMES its postcondition via h_destOff/h_srcOff/h_sizeV "
       ++ "(operand.getLimbN 0 = ofNat n) — i.e. proven for low-limb operands, NOT "
       ++ "for the >=2^64 offset/size inputs the handler reverts on. Satisfiable, "
       ++ "so a coverage precondition rather than a vacuous guard; see DRIFT."),
  entry "EXTCODEHASH" .execSpec none "witness-backed account read",

  -- Block (0x40..0x4a)
  entry "BLOCKHASH" .proven (some "BlockHash.evm_blockhash_stack_spec_within")
      (cycleBound := some 24),
  entry "COINBASE" .proven (some "Env.evm_coinbase_stack_spec_within"),
  entry "TIMESTAMP" .proven (some "Env.evm_timestamp_stack_spec_within"),
  entry "NUMBER" .proven (some "Env.evm_number_stack_spec_within"),
  entry "PREVRANDAO" .proven (some "Env.evm_prevrandao_stack_spec_within"),
  entry "GASLIMIT" .proven (some "Env.evm_gaslimit_stack_spec_within"),
  entry "CHAINID" .proven (some "Env.evm_chainid_stack_spec_within"),
  entry "SELFBALANCE" .proven (some "Env.evm_selfbalance_stack_spec_within"),
  entry "BASEFEE" .proven (some "Env.evm_basefee_stack_spec_within"),
  entry "BLOBHASH" .proven (some "BlobHash.evm_blobhash_stack_spec_within")
      (cycleBound := some 20),
  entry "BLOBBASEFEE" .proven (some "BlobBaseFee.evm_blobbasefee_stack_spec_within"),

  -- Stack/Memory/Storage/Flow (0x50..0x5f)
  entry "POP" .proven (some "evm_pop_stack_spec_within") (cycleBound := some 1),
  entry "MLOAD" .proven (some "evm_mload_stack_spec_within")
      ("all byte alignments; memory framed by evmMemoryIs; the explicit " ++
       "trailing guard band supplies the pair-read tail"),
  entry "MSTORE" .proven (some "evm_mstore_stack_spec_within")
      "aligned spec proven; unaligned _public variants in progress",
  entry "MSTORE8" .proven (some "evm_mstore8_stack_spec_within") (cycleBound := some 5),
  entry "SLOAD" .conditional (some "Storage.evm_sload_stack_spec_within")
      ("stage-1 of the two-stage SLOAD plan: the persistent-log reverse scan " ++
       "(byte-identical body-as-Program of the h_SLOAD handler, base 0xa0630000, " ++
       "length cell env+448) is proven to replace the stack top in place with " ++
       "persistentLookup — the `current` of the most-recent committedStorageIs " ++
       "entry keyed by (env.ADDRESS, slotKey), or 0 on miss. `.conditional` " ++
       "because the miss→0 branch is EVM-sound only RELATIVE to the " ++
       "committedStorageIs snapshot supplied in the precondition; full MPT-" ++
       "witness verification that the snapshot faithfully reflects state root " ++
       "is deferred to stage-2 (post-Phase-10). Structural clone of the proven " ++
       "TLOAD reverse scan on the transient log.")
      (coverRef := some "sload_precondition_reachable"),
  entry "SSTORE" .execSpec none "Storage*.lean; ECALL → host",
  entry "JUMP" .proven (some "ControlFlow.evm_jump_stack_spec_within")
      (cycleBound := some 13),
  entry "JUMPI" .proven (some "ControlFlow.evm_jumpi_stack_spec_within")
      (cycleBound := some 21),
  entry "PC" .proven (some "ControlFlow.evm_pc_stack_spec_within"),
  entry "MSIZE" .proven (some "evm_msize_stack_spec_within") (cycleBound := some 6),
  entry "GAS" .proven (some "GasOpcode.evm_gas_stack_spec_within"),
  entry "JUMPDEST" .proven (some "ControlFlow.evm_jumpdest_stack_spec_within")
      (cycleBound := some 0),
  entry "TLOAD" .proven (some "Transient.evm_tload_stack_spec_within"),
  entry "TSTORE" .proven (some "Transient.evm_tstore_stack_spec_within"),
  entry "MCOPY" .proven (some "Mcopy.evm_mcopy_stack_spec_within")
      ("EIP-5656 (Cancun) overlap-aware memmove copy core proven "
       ++ "(Mcopy/{Program,Result,ForwardLoopSpec,BackwardLoopSpec,Spec}.lean): "
       ++ "byte-identical body-as-Program of the h_MCOPY handler tail (verified "
       ++ "against riscv64-elf-as), TOTAL over all (destOff,srcOff,len) — the two "
       ++ "BGEU offset comparisons dispatch to a forward (low→high) or backward "
       ++ "(high→low) byte loop, both proven to land on the same direction-"
       ++ "independent mcopyResult (memmove: dst window ← original src slice) via "
       ++ "a single evolving evmMemoryIs slab with a read-sees-original invariant "
       ++ "per direction. Stack decode + gas/MSIZE/range-guard glue unverified per "
       ++ "DRIFT (same as CALLDATACOPY/CODECOPY). First memory→memory / overlap-"
       ++ "aware opcode; first two-directional loop proof."),
  entry "PUSH0" .proven (some "evm_push0_stack_spec_within") (cycleBound := some 5),

  -- Push family (0x60..0x7f). PUSH1 has its own top-level spec; PUSH2..32
  -- share one parameterized full-immediate spec generic over the width n.
  entry "PUSH1" .proven (some "evm_push1_stack_spec_within"),
  entry "PUSH2..32" .proven (some "evm_push_stack_spec_within")
      "single proof generic over n=2..32; pushes the big-endian immediate; 31 byte-codes",

  -- Dup/Swap families (0x80..0x9f) — single generic proof each
  entry "DUP1..16" .proven (some "evm_dup_stack_spec_within")
      "single proof generic over n=1..16",
  entry "SWAP1..16" .proven (some "evm_swap_stack_spec_within")
      "single proof generic over n=1..16",

  -- Log family (0xa0..0xa4)
  entry "LOG0..4" .execSpec none
      "LogArgs + LogDataBridge + LogExecutionBridge; 5 byte-codes",

  -- System (0xf0..0xff)
  entry "CREATE" .execSpec none
      "Create.lean + CreateAddress + CreateArgsBridge + CreateEffects",
  entry "CALL" .execSpec none "CallArgs + Call*Bridge family",
  entry "CALLCODE" .execSpec none "ChildFrameHandlers; shared CALL family",
  entry "RETURN" .conditional (some "Terminating.evm_return_stack_spec_within_with_capture")
      ("full standalone (depthAware=false) return-data window + halt core, from " ++
       "the post-gas handler entry through the RETURN-only system_call_mode " ++
       "capture block and the 0xa0010000 descriptor (header/22-dword-body " ++
       "zeroing, size@+64, clamped=min(size,176)@+248, " ++
       "evm_memory[offset..offset+clamped] copied to +72, first min(size,32) " ++
       "bytes to +0, kind=1@+32) to the shared dispatchHaltRet 2 core " ++
       "(evm_halt_flag:=2, x1:=resume, ret to resume&&&~~~1). The front now " ++
       "covers all system_call_mode cases: zero skips capture; nonzero with " ++
       "size>4096 skips conservatively; nonzero with size<=4096 stores " ++
       "system_call_returndata_len:=size and copies the full returndata window " ++
       "to system_call_returndata. `.conditional` remains because the memory-gas " ++
       "`preBody` (its .exit_outofgas branch) is framed OUT as a decision-1 TCB " ++
       "boundary, so the theorem still carries the post-gas memory-domain hyps " ++
       "(hOff/hOff32 and branch-conditional hOffCapture/hRdCapture). The seven " ++
       "`la` immediates stay as reconstruction hyps (shared deferred byte-check, " ++
       "as in the halt core).")
      (coverRef := some "return_capture_nondegenerate"),
  entry "DELEGATECALL" .execSpec none "CallArgs kind = .delegatecall",
  entry "CREATE2" .execSpec none "shared Create family",
  entry "STATICCALL" .execSpec none "CallArgs kind = .staticcall",
  entry "REVERT" .conditional (some "Terminating.evm_revert_stack_spec_within")
      ("full standalone (depthAware=false) return-data window + rollback + halt " ++
       "core, from the post-gas handler entry through the 0xa0010000 descriptor " ++
       "(header/22-dword-body zeroing, size@+64, clamped=min(size,176)@+248, " ++
       "evm_memory[offset..offset+clamped] copied to +72, first min(size,32) " ++
       "bytes to +0, kind=2@+32), the five straight-line rollback env-cell stores " ++
       "on x20 (env+448:=env+456, env+464:=0, env+472:=env+480), to the shared " ++
       "dispatchHaltRet 2 core (evm_halt_flag:=2, x1:=resume, ret to " ++
       "resume&&&~~~1). Near-clone of RETURN reusing its window loop closures + " ++
       "halt core verbatim (only the code layout shifts down 80 bytes with no " ++
       "capture block, the kind-store value is 2, and the rollback is appended). " ++
       "`.conditional` NOT because of a system_call_mode gate (REVERT has no " ++
       "capture block — that is kind==1/RETURN-only — so it is strictly more " ++
       "general than RETURN) but because (1) the memory-gas `preBody` (its " ++
       ".exit_outofgas branch) is framed OUT as a decision-1 TCB boundary and " ++
       "(2) the evm_memory well-formedness domain hyps (hOff/hOff32 etc.) restrict " ++
       "the input domain, exactly as in RETURN. The four `la` immediates stay as " ++
       "reconstruction hyps (shared deferred byte-check, as in the halt core).")
      (coverRef := some "revert_window_nondegenerate"),
  entry "INVALID" .proven (some "evm_invalid_stack_spec_within")
      ("halt-triple over the verified `evm_invalid` program (byte image of the "
       ++ "emitted `dispatchHaltRet 3` tail): sets `evm_halt_flag := 3`, points "
       ++ "x1 at `.Ldispatch_resume`, and rets to `resume &&& ~~~1`; the two "
       ++ "`la`s stay `hla1`/`hla2` reconstruction hyps as in the guard/glue "
       ++ "precedents. Direct STOP clone with routing code 3 (`.exit_invalid_op`)")
      (cycleBound := some 7),
  entry "SELFDESTRUCT" .conditional (some "Terminating.evm_selfdestruct_stack_spec_resolved")
      ("halt/routing tail only — the shared dispatchHaltRet 4 core (evm_halt_flag:=4, " ++
       "x1:=.Ldispatch_resume, ret to resume&&&~~~1) over the verified `evm_selfdestruct` " ++
       "program; direct STOP/INVALID clone with routing code 4 (`.exit_selfdestruct`). " ++
       "The two `la`s (`evm_halt_flag`, `.Ldispatch_resume`) are RESOLVED via `la_resolve` " ++
       "(#10059), leaving only decidable `laInRange` per `la`. `.conditional` — NOT `.proven` " ++
       "unlike STOP/INVALID (whose dispatched handler IS just the halt tail, body:=[]) — " ++
       "because SELFDESTRUCT's dispatched handler (`selfdestructTailAsm`) runs a substantial " ++
       "effects body BEFORE this tail that is framed OUT as the residual: cold-access gas " ++
       "(with its own .exit_outofgas branch), new-account surcharge, EIP-6780 created-in-tx " ++
       "detection, balance transfer to the beneficiary, EIP-7708 log, beneficiary nonstorage " ++
       "record, and the CREATE-child frame_return path. A larger residual than RETURN/REVERT's " ++
       "gas-only preBody; a future phase proves it against `EL/SelfdestructEffects` to earn " ++
       "`.proven`.")
      (cycleBound := some 7),
]

/-! ## Counts (kernel-checked) -/

/-- Count of registry entries at a given tier. -/
def countTier (t : ProofTier) : Nat :=
  registry.countP (fun e => e.tier == t)

def provenCount      : Nat := countTier .proven
def partialCount     : Nat := countTier .partly
def conditionalCount : Nat := countTier .conditional
def execSpecCount    : Nat := countTier .execSpec
def notStartedCount  : Nat := countTier .notStarted
def totalEntries     : Nat := registry.length

theorem provenCount_eq      : provenCount      = 68 := by decide
theorem partialCount_eq     : partialCount     = 0  := by decide
theorem conditionalCount_eq : conditionalCount = 4  := by decide
theorem execSpecCount_eq    : execSpecCount    = 13 := by decide
theorem notStartedCount_eq  : notStartedCount  = 0  := by decide
theorem totalEntries_eq     : totalEntries     = 85 := by decide

/-! ## Byte-code counts

    Counts opcode *bytes* (not registry entries), expanding the
    parameterized families. Each `OpcodeEntry` whose `name` matches one
    of the families below contributes its width; everything else
    contributes 1. -/

def entryByteCount (e : OpcodeEntry) : Nat :=
  match e.name with
  | "PUSH2..32" => 31
  | "DUP1..16"  => 16
  | "SWAP1..16" => 16
  | "LOG0..4"   => 5
  | _           => 1

def byteCountTier (t : ProofTier) : Nat :=
  (registry.filter (fun e => e.tier == t)).foldl
    (fun acc e => acc + entryByteCount e) 0

def provenBytes      : Nat := byteCountTier .proven
def partialBytes     : Nat := byteCountTier .partly
def conditionalBytes : Nat := byteCountTier .conditional
def execSpecBytes    : Nat := byteCountTier .execSpec
def notStartedBytes  : Nat := byteCountTier .notStarted
def totalBytes       : Nat :=
  provenBytes + partialBytes + conditionalBytes + execSpecBytes + notStartedBytes

theorem provenBytes_eq      : provenBytes      = 128 := by decide
theorem partialBytes_eq     : partialBytes     = 0   := by decide
theorem conditionalBytes_eq : conditionalBytes = 4   := by decide
theorem execSpecBytes_eq    : execSpecBytes    = 17  := by decide
theorem notStartedBytes_eq  : notStartedBytes  = 0   := by decide
theorem totalBytes_eq       : totalBytes       = 149 := by decide

/-! ## Witness `abbrev`s

    Each `.proven`, `.conditional`, and `.partly` entry above names a
    theorem; the abbrev below forces its definition to exist. If a theorem is
    renamed or deleted, this file fails to elaborate. Update both
    the registry entry and this section when refactoring.

    Convention: name the abbrev `_<lower>_witness`; mark it
    `private noncomputable` to avoid polluting the namespace. -/

private noncomputable abbrev _add_witness        := @EvmAsm.Evm64.evm_add_stack_spec_within
private noncomputable abbrev _mul_witness        := @EvmAsm.Evm64.evm_mul_stack_spec_within
private noncomputable abbrev _sub_witness        := @EvmAsm.Evm64.evm_sub_stack_spec_within
private noncomputable abbrev _div_witness        := @EvmAsm.Evm64.evm_div_v6_stack_spec
private noncomputable abbrev _sdiv_witness       :=
  @EvmAsm.Evm64.SDiv.Compose.evm_sdiv_exact_callable_return_result_stack_spec_within_v5
private noncomputable abbrev _mod_witness        := @EvmAsm.Evm64.evm_mod_v6_stack_spec
private noncomputable abbrev _smod_witness       :=
  @EvmAsm.Evm64.SMod.Compose.evm_smod_exact_callable_return_result_stack_spec_within_v5
private noncomputable abbrev _addmod_witness     :=
  @EvmAsm.Evm64.AddMod.Compose.evm_addmod_total_result_stack_spec_within
private noncomputable abbrev _mulmod_witness      := @EvmAsm.Evm64.MulMod.Compose.evm_mulmod_stack_spec_within
private noncomputable abbrev _exp_witness         := @EvmAsm.Evm64.evm_exp_stack_spec_within
private noncomputable abbrev _signextend_witness := @EvmAsm.Evm64.evm_signextend_stack_spec_within
private noncomputable abbrev _lt_witness         := @EvmAsm.Evm64.evm_lt_stack_spec_within
private noncomputable abbrev _gt_witness         := @EvmAsm.Evm64.evm_gt_stack_spec_within
private noncomputable abbrev _slt_witness        := @EvmAsm.Evm64.evm_slt_stack_spec_within
private noncomputable abbrev _sgt_witness        := @EvmAsm.Evm64.evm_sgt_stack_spec_within
private noncomputable abbrev _eq_witness         := @EvmAsm.Evm64.evm_eq_stack_spec_within
private noncomputable abbrev _iszero_witness     := @EvmAsm.Evm64.evm_iszero_stack_spec_within
private noncomputable abbrev _and_witness        := @EvmAsm.Evm64.evm_and_stack_spec_within
private noncomputable abbrev _or_witness         := @EvmAsm.Evm64.evm_or_stack_spec_within
private noncomputable abbrev _xor_witness        := @EvmAsm.Evm64.evm_xor_stack_spec_within
private noncomputable abbrev _not_witness        := @EvmAsm.Evm64.evm_not_stack_spec_within
private noncomputable abbrev _byte_witness       := @EvmAsm.Evm64.evm_byte_stack_spec_within
private noncomputable abbrev _shl_witness        := @EvmAsm.Evm64.evm_shl_stack_spec_within
private noncomputable abbrev _shr_witness        := @EvmAsm.Evm64.evm_shr_stack_spec_within
private noncomputable abbrev _sar_witness        := @EvmAsm.Evm64.evm_sar_stack_spec_within
private noncomputable abbrev _address_witness    := @EvmAsm.Evm64.Env.evm_address_stack_spec_within
private noncomputable abbrev _origin_witness     := @EvmAsm.Evm64.Env.evm_origin_stack_spec_within
private noncomputable abbrev _caller_witness     := @EvmAsm.Evm64.Env.evm_caller_stack_spec_within
private noncomputable abbrev _callvalue_witness  := @EvmAsm.Evm64.Env.evm_callvalue_stack_spec_within
private noncomputable abbrev _gasprice_witness   := @EvmAsm.Evm64.Env.evm_gasprice_stack_spec_within
private noncomputable abbrev _coinbase_witness   := @EvmAsm.Evm64.Env.evm_coinbase_stack_spec_within
private noncomputable abbrev _timestamp_witness  := @EvmAsm.Evm64.Env.evm_timestamp_stack_spec_within
private noncomputable abbrev _number_witness     := @EvmAsm.Evm64.Env.evm_number_stack_spec_within
private noncomputable abbrev _prevrandao_witness := @EvmAsm.Evm64.Env.evm_prevrandao_stack_spec_within
private noncomputable abbrev _gaslimit_witness   := @EvmAsm.Evm64.Env.evm_gaslimit_stack_spec_within
private noncomputable abbrev _chainid_witness    := @EvmAsm.Evm64.Env.evm_chainid_stack_spec_within
private noncomputable abbrev _selfbalance_witness := @EvmAsm.Evm64.Env.evm_selfbalance_stack_spec_within
private noncomputable abbrev _basefee_witness    := @EvmAsm.Evm64.Env.evm_basefee_stack_spec_within
private noncomputable abbrev _calldataload_witness :=
  @EvmAsm.Evm64.Calldata.evm_calldataload_staged_stack_spec_within
private noncomputable abbrev _calldatasize_witness :=
  @EvmAsm.Evm64.Calldata.evm_calldatasize_stack_spec_within
private noncomputable abbrev _calldatacopy_witness :=
  @EvmAsm.Evm64.Calldata.evm_calldatacopy_stack_spec_within
private noncomputable abbrev _codesize_witness :=
  @EvmAsm.Evm64.Code.evm_codesize_stack_spec_within
private noncomputable abbrev _pc_witness :=
  @EvmAsm.Evm64.ControlFlow.evm_pc_stack_spec_within
private noncomputable abbrev _gas_witness :=
  @EvmAsm.Evm64.GasOpcode.evm_gas_stack_spec_within
private noncomputable abbrev _blobbasefee_witness :=
  @EvmAsm.Evm64.BlobBaseFee.evm_blobbasefee_stack_spec_within
private noncomputable abbrev _jumpdest_witness :=
  @EvmAsm.Evm64.ControlFlow.evm_jumpdest_stack_spec_within
private noncomputable abbrev _jump_witness :=
  @EvmAsm.Evm64.ControlFlow.evm_jump_stack_spec_within
private noncomputable abbrev _jumpi_witness :=
  @EvmAsm.Evm64.ControlFlow.evm_jumpi_stack_spec_within
private noncomputable abbrev _blobhash_witness :=
  @EvmAsm.Evm64.BlobHash.evm_blobhash_stack_spec_within
private noncomputable abbrev _blockhash_witness :=
  @EvmAsm.Evm64.BlockHash.evm_blockhash_stack_spec_within
private noncomputable abbrev _codecopy_witness :=
  @EvmAsm.Evm64.Code.evm_codecopy_stack_spec_within
private noncomputable abbrev _returndatasize_witness :=
  @EvmAsm.Evm64.ReturnData.evm_returndatasize_stack_spec_within
private noncomputable abbrev _returndatacopy_witness :=
  @EvmAsm.Evm64.ReturnData.evm_returndatacopy_body_stack_spec_within
private noncomputable abbrev _returndatacopy_copy_core_witness :=
  @EvmAsm.Evm64.ReturnData.evm_returndatacopy_stack_spec_within
private noncomputable abbrev _returndatacopy_setup_witness :=
  @EvmAsm.Evm64.ReturnData.evm_returndatacopy_setup_spec_within
private noncomputable abbrev _returndatacopy_guard_success_witness :=
  @EvmAsm.Evm64.ReturnData.evm_returndatacopy_guard_success_stack_spec_within
private noncomputable abbrev _returndatacopy_guard_wrap_witness :=
  @EvmAsm.Evm64.ReturnData.evm_returndatacopy_guard_wrap_invalid_stack_spec_within
private noncomputable abbrev _returndatacopy_guard_len_witness :=
  @EvmAsm.Evm64.ReturnData.evm_returndatacopy_guard_len_invalid_stack_spec_within
private noncomputable abbrev _tload_witness :=
  @EvmAsm.Evm64.Transient.evm_tload_stack_spec_within
private noncomputable abbrev _sload_witness :=
  @EvmAsm.Evm64.Storage.evm_sload_stack_spec_within
private noncomputable abbrev _sload_cover :=
  @EvmAsm.Evm64.Storage.sload_precondition_reachable
private noncomputable abbrev _tstore_witness :=
  @EvmAsm.Evm64.Transient.evm_tstore_stack_spec_within
private noncomputable abbrev _stop_witness :=
  @EvmAsm.Evm64.Terminating.evm_stop_stack_spec_within
private noncomputable abbrev _invalid_witness :=
  @EvmAsm.Evm64.Terminating.evm_invalid_stack_spec_within
-- Shared RETURN/REVERT halt core (`dispatchHaltRet 2` → `.exit_no_epilogue`).
private noncomputable abbrev _return_halt_witness :=
  @EvmAsm.Evm64.Terminating.evm_return_halt_spec_within
-- Full RETURN (0xf3) return-data window + halt core (see the registry note).
private noncomputable abbrev _return_witness :=
  @EvmAsm.Evm64.Terminating.evm_return_stack_spec_within_with_capture
private noncomputable abbrev _return_cover :=
  @EvmAsm.Evm64.Terminating.return_capture_nondegenerate
-- Full REVERT (0xfd) return-data window + rollback + halt core (see the note).
private noncomputable abbrev _revert_witness :=
  @EvmAsm.Evm64.Terminating.evm_revert_stack_spec_within
private noncomputable abbrev _revert_cover :=
  @EvmAsm.Evm64.Terminating.revert_window_nondegenerate
-- SELFDESTRUCT (0xff) halt tail with the two `la`s resolved (see the registry note).
private noncomputable abbrev _selfdestruct_witness :=
  @EvmAsm.Evm64.Terminating.evm_selfdestruct_stack_spec_resolved
private noncomputable abbrev _pop_witness        := @EvmAsm.Evm64.evm_pop_stack_spec_within
private noncomputable abbrev _mload_witness      := @EvmAsm.Evm64.evm_mload_stack_spec_within
private noncomputable abbrev _mstore_witness     := @EvmAsm.Evm64.evm_mstore_stack_spec_within
private noncomputable abbrev _mstore8_witness    := @EvmAsm.Evm64.evm_mstore8_stack_spec_within
private noncomputable abbrev _msize_witness      := @EvmAsm.Evm64.evm_msize_stack_spec_within
private noncomputable abbrev _push0_witness      := @EvmAsm.Evm64.evm_push0_stack_spec_within
private noncomputable abbrev _push1_witness      := @EvmAsm.Evm64.evm_push1_stack_spec_within
private noncomputable abbrev _push_witness       := @EvmAsm.Evm64.evm_push_stack_spec_within
private noncomputable abbrev _dup_witness        := @EvmAsm.Evm64.evm_dup_stack_spec_within
private noncomputable abbrev _swap_witness       := @EvmAsm.Evm64.evm_swap_stack_spec_within

/-! ### State-assertion vocabulary witnesses

    Headline lemmas of the separation-logic Assertions over the guest's
    structured arenas (`evmMemoryIs` PR #9844; MPT node / node-DB;
    witness-section / code-DB
    assertions). Fenced here so `scripts/check-axioms.sh` audits them. -/

private noncomputable abbrev _evm_memory_is_mload_witness :=
  @EvmAsm.Evm64.evm_mload_stack_spec_within
private noncomputable abbrev _evm_memory_is_peel_witness :=
  @EvmAsm.Evm64.evmMemoryIs_peel_window64
private noncomputable abbrev _mpt_node_kind_spec_witness :=
  @EvmAsm.Evm64.mptNodeKindSpec_rlp
private noncomputable abbrev _hp_roundtrip_witness :=
  @EvmAsm.Evm64.hpDecode_hpEncode
private noncomputable abbrev _rlp_to_mutable_node_witness :=
  @EvmAsm.Evm64.rlpToMutableNode_rlp
private noncomputable abbrev _node_db_snoc_witness :=
  @EvmAsm.Evm64.nodeDbIs_snoc
private noncomputable abbrev _node_db_lookup_spec_witness :=
  @EvmAsm.Evm64.nodeDbLookupSpec_eq_build_node_db
private noncomputable abbrev _node_db_stride_witness :=
  @EvmAsm.Evm64.roundUp8_eq_alignToDword
private noncomputable abbrev _witness_lookup_spec_witness :=
  @EvmAsm.Evm64.witnessLookupSpec_correct
private noncomputable abbrev _witness_index_split_witness :=
  @EvmAsm.Evm64.witnessIndexIs_split_at
private noncomputable abbrev _index_of_section_hashes_witness :=
  @EvmAsm.Evm64.indexOfSection_hashes_eq_build_code_db
private noncomputable abbrev _index_of_section_matches_witness :=
  @EvmAsm.Evm64.indexOfSection_matchesSection
private noncomputable abbrev _account_rlp_decode_witness :=
  @EvmAsm.Stateless.decode_account_from_leaf_accountRlp
private noncomputable abbrev _account_balance_slot_witness :=
  @EvmAsm.Stateless.bytesBEtoNat_beBytes32
private noncomputable abbrev _account_rlp_length_witness :=
  @EvmAsm.Stateless.accountRlp_length_le

end EvmAsm.Progress
