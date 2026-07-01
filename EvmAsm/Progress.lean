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
import EvmAsm.Evm64.MStore8.Spec
import EvmAsm.Evm64.MLoad.UnalignedFramedStackSpec
import EvmAsm.Evm64.MStore.UnalignedFramedStackSpec
import EvmAsm.Evm64.DivMod.Spec.Unified
import EvmAsm.Evm64.DivMod.Compose.FullPathV5DivUnconditionalFull
import EvmAsm.Evm64.DivMod.Compose.V6DivStackSpec
import EvmAsm.Evm64.DivMod.Compose.V6ModStackSpec
import EvmAsm.Evm64.SDiv.Spec
import EvmAsm.Evm64.SMod.SpecAllCase
import EvmAsm.Evm64.AddMod.Spec
import EvmAsm.Evm64.AddMod.LiveStackPost
import EvmAsm.Evm64.MulMod.Compose.StackSpecAll
import EvmAsm.Evm64.Exp.Spec
import EvmAsm.Evm64.Exp.HeadroomProgramSpec
import EvmAsm.Evm64.Exp.StackExecutionBridge
import EvmAsm.Evm64.Env.Wrappers
import EvmAsm.Evm64.Calldata.SizeSpec
import EvmAsm.Evm64.Calldata.CopySpec

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
  entry "STOP" .execSpec none
      "executable-spec only; `Termination.lean` + `TerminatingArgs.lean`",
  entry "ADD" .proven (some "evm_add_stack_spec_within") (cycleBound := some 30),
  entry "MUL" .proven (some "evm_mul_stack_spec_within") (cycleBound := some 63),
  entry "SUB" .proven (some "evm_sub_stack_spec_within") (cycleBound := some 30),
  entry "DIV" .proven (some "evm_div_v6_stack_spec")
      ("full-domain unconditional v6 DIV stack spec over divCodeV6 (n=1 " ++
       "single-limb fast-path dispatch); the n≥2 / b=0 arm reuses the v5 " ++
       "proof (evm_div_v5_unconditional_over_divCodeV6), the n=1 fast arm is " ++
       "divK_fastBody_dispatchPostV5_within_v6, merged via the BNE/BEQ dispatch"),
  entry "SDIV" .conditional (some "evm_sdiv_exact_callable_return_stack_spec_within")
      ("callable+dispatch shim; evm_sdiv_stack_spec_within conditional on " ++
       "hStack (discharged for divisor=0 and n=1/2/3/n4-call-skip); blocked " ++
       "on DIV/MOD spec-layer migration (bead evm-asm-9iqmw)"),
  entry "MOD" .proven (some "evm_mod_v6_stack_spec")
      ("full-domain unconditional v6 MOD stack spec over modCodeV6 (n=1 " ++
       "single-limb fast-path dispatch); the n≥2 / b=0 arm reuses the v5 " ++
       "proof (evm_mod_v5_unconditional_over_modCodeV6), the n=1 fast arm is " ++
       "modK_fastBody_dispatchPostV5_within_v6, merged via the BNE/BEQ dispatch"),
  entry "SMOD" .conditional
      (some "evm_smod_stack_spec_within")
      ("all-case v4 wrapper result-stack spec; zero divisor discharged, " ++
       "nonzero path still parameterized by unsigned-MOD callable h_stack"),
  entry "ADDMOD" .partly (some "evm_addmod_partial_or_guard_domain_canonical_existential_regs_owned_stack_tail_spec_within")
      ("addmod_correct proven; zero-modulus stack spec done for arbitrary b; " ++
       "no-overflow skeleton composed through legacy MOD no-NOP body proof; " ++
       "current partial theorem has a final live-stack post at sp+64 preserving an arbitrary caller stack tail, consumed operand cells and all leftover registers in the current frame weakened to ownership, and old register/scratch witnesses packaged in an existential precondition that can carry the runtime OR-fold zero-test guard, with the MOD callable base specialized to the canonical JAL target; zero-modulus and no-overflow branches also have canonical existential stack-tail surfaces evm_addmod_n0_canonical_existential_regs_owned_stack_tail_spec_within and evm_addmod_no_overflow_canonical_existential_regs_owned_stack_tail_spec_within, with explicit zero-result N=0 and OR-zero tail surfaces evm_addmod_n0_canonical_existential_regs_owned_zero_stack_tail_spec_within and evm_addmod_or_zero_domain_canonical_existential_regs_owned_zero_stack_tail_spec_within, plus no-overflow and OR-guard domain-pre surfaces evm_addmod_no_overflow_domain_canonical_existential_regs_owned_stack_tail_spec_within and evm_addmod_partial_or_guard_domain_canonical_existential_regs_owned_stack_tail_spec_within"),
  entry "MULMOD" .proven (some "evm_mulmod_stack_spec_within")
      ("full-domain unconditional MULMOD stack spec for every modulus (no " ++
       "n ≤ 2^255 hypothesis); bit-serial 512-bit reducer. Scratchpad " ++
       "relocated below the stack pointer (sp + signExtend12 3936..4088 = " ++
       "sp-160..sp-8) so the live EVM stack is preserved")
      (cycleBound := some 34295),
  entry "EXP" .partly (some "evm_exp_headroom_visible_result_stack_program_spec_within")
      "exp_correct proven; pure executable stack transition names EvmWord.exp; headroom RV64 full-loop composition now reaches a canonical concrete-program theorem over CodeReq.ofProg with ordinary entry-base alignment, old register/scratch values and the internal scratch base existentially packaged, and the semantic result stack exposed directly at evmSp+32 as EvmWord.exp base exponent :: rest; consumed operand/scratch cells and leftover headroom stack cells are weakened to ownership, with leftover implementation resources existentially framed; public evm_exp_stack_spec_within wrapper still pending",
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
  entry "BALANCE" .execSpec none "not in EvmOpcode enum yet",
  entry "ORIGIN" .proven (some "Env.evm_origin_stack_spec_within"),
  entry "CALLER" .proven (some "Env.evm_caller_stack_spec_within"),
  entry "CALLVALUE" .proven (some "Env.evm_callvalue_stack_spec_within"),
  entry "CALLDATALOAD" .execSpec none
      "program in Calldata/LoadProgram.lean; no stack spec yet",
  entry "CALLDATASIZE" .proven
      (some "Calldata.evm_calldatasize_stack_spec_within"),
  entry "CALLDATACOPY" .partly
      (some "Calldata.evm_calldatacopy_preamble_stack_spec_within")
      "preamble + partial memory effect; full loop pending",
  entry "CODESIZE" .execSpec none "env read in Code/Basic.lean",
  entry "CODECOPY" .execSpec none "Code/CopyExec.lean + CopyMemory.lean",
  entry "GASPRICE" .proven (some "Env.evm_gasprice_stack_spec_within"),
  entry "EXTCODESIZE" .execSpec none "not in EvmOpcode enum yet",
  entry "EXTCODECOPY" .execSpec none "not in EvmOpcode enum yet",
  entry "RETURNDATASIZE" .execSpec none
      "ReturnDataHandlers.lean; table dispatch only",
  entry "RETURNDATACOPY" .execSpec none "ReturnData/CopyExec + CopyMemory",
  entry "EXTCODEHASH" .execSpec none "not in EvmOpcode enum yet",

  -- Block (0x40..0x4a)
  entry "BLOCKHASH" .execSpec none "env-bridge level",
  entry "COINBASE" .proven (some "Env.evm_coinbase_stack_spec_within"),
  entry "TIMESTAMP" .proven (some "Env.evm_timestamp_stack_spec_within"),
  entry "NUMBER" .proven (some "Env.evm_number_stack_spec_within"),
  entry "PREVRANDAO" .proven (some "Env.evm_prevrandao_stack_spec_within"),
  entry "GASLIMIT" .proven (some "Env.evm_gaslimit_stack_spec_within"),
  entry "CHAINID" .proven (some "Env.evm_chainid_stack_spec_within"),
  entry "SELFBALANCE" .proven (some "Env.evm_selfbalance_stack_spec_within"),
  entry "BASEFEE" .proven (some "Env.evm_basefee_stack_spec_within"),
  entry "BLOBHASH" .execSpec none "env-bridge level",
  entry "BLOBBASEFEE" .execSpec none "env-bridge level",

  -- Stack/Memory/Storage/Flow (0x50..0x5f)
  entry "POP" .proven (some "evm_pop_stack_spec_within") (cycleBound := some 1),
  entry "MLOAD" .proven (some "evm_mload_stack_spec_within")
      "aligned spec proven; unaligned _public variants in progress",
  entry "MSTORE" .proven (some "evm_mstore_stack_spec_within")
      "aligned spec proven; unaligned _public variants in progress",
  entry "MSTORE8" .proven (some "evm_mstore8_stack_spec_within") (cycleBound := some 5),
  entry "SLOAD" .execSpec none "Storage*.lean; ECALL → host",
  entry "SSTORE" .execSpec none "Storage*.lean; ECALL → host",
  entry "JUMP" .execSpec none "handled by interpreter PC update",
  entry "JUMPI" .execSpec none "handled by interpreter PC update",
  entry "PC" .execSpec none "reads EVM PC from EvmState",
  entry "MSIZE" .proven (some "evm_msize_stack_spec_within") (cycleBound := some 6),
  entry "GAS" .execSpec none "reads remaining gas from EvmState",
  entry "JUMPDEST" .execSpec none "no-op opcode; gas-only",
  entry "TLOAD" .notStarted none "EIP-1153 (Cancun); not in EvmOpcode enum",
  entry "TSTORE" .notStarted none "EIP-1153 (Cancun); not in EvmOpcode enum",
  entry "MCOPY" .notStarted none "EIP-5656 (Cancun); not in EvmOpcode enum",
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
  entry "CALLCODE" .execSpec none "not in EvmOpcode enum yet",
  entry "RETURN" .execSpec none "TerminatingArgs + TerminatingExecutionBridge",
  entry "DELEGATECALL" .execSpec none "CallArgs kind = .delegatecall",
  entry "CREATE2" .execSpec none "shared Create family",
  entry "STATICCALL" .execSpec none "CallArgs kind = .staticcall",
  entry "REVERT" .execSpec none "TerminatingArgs",
  entry "INVALID" .execSpec none "TerminatingArgs",
  entry "SELFDESTRUCT" .execSpec none "SelfdestructEffects + terminating bridge",
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

theorem provenCount_eq      : provenCount      = 45 := by decide
theorem partialCount_eq     : partialCount     = 3  := by decide
theorem conditionalCount_eq : conditionalCount = 2  := by decide
theorem execSpecCount_eq    : execSpecCount    = 32 := by decide
theorem notStartedCount_eq  : notStartedCount  = 3  := by decide
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

theorem provenBytes_eq      : provenBytes      = 105 := by decide
theorem partialBytes_eq     : partialBytes     = 3   := by decide
theorem conditionalBytes_eq : conditionalBytes = 2   := by decide
theorem execSpecBytes_eq    : execSpecBytes    = 36  := by decide
theorem notStartedBytes_eq  : notStartedBytes  = 3   := by decide
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
  @EvmAsm.Evm64.evm_sdiv_exact_callable_return_stack_spec_within
private noncomputable abbrev _mod_witness        := @EvmAsm.Evm64.evm_mod_v6_stack_spec
private noncomputable abbrev _smod_witness       :=
  @EvmAsm.Evm64.evm_smod_stack_spec_within
private noncomputable abbrev _addmod_witness     := @EvmAsm.Evm64.evm_addmod_partial_or_guard_domain_canonical_existential_regs_owned_stack_tail_spec_within
private noncomputable abbrev _mulmod_witness      := @EvmAsm.Evm64.MulMod.Compose.evm_mulmod_stack_spec_within
private noncomputable abbrev _exp_witness         := @EvmAsm.Evm64.evm_exp_headroom_visible_result_stack_program_spec_within
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
private noncomputable abbrev _calldatasize_witness :=
  @EvmAsm.Evm64.Calldata.evm_calldatasize_stack_spec_within
private noncomputable abbrev _calldatacopy_witness :=
  @EvmAsm.Evm64.Calldata.evm_calldatacopy_preamble_stack_spec_within
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

end EvmAsm.Progress
