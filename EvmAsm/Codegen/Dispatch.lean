/-
  EvmAsm.Codegen.Dispatch

  Declarative registry shape for the M5b runtime fetch/decode/dispatch
  loop. Each opcode is one `OpcodeHandlerSpec` entry; the helpers
  below render the dispatcher prologue, the 256-entry jump table, and
  the handler subroutines from a `List OpcodeHandlerSpec`.

  Adding a new opcode to the dispatcher = adding one entry to the
  registry. The dispatcher scaffolding (loop body, exit path, invalid
  fallback) stays here so `Programs.lean` only declares opcode-
  specific data.

  Per CODEGEN.md §Tricky bits #9 the loop scaffold is raw asm; only
  verified opcode bodies (rendered via `emitProgram`) sit inside the
  handler subroutines.
-/

import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.SstoreGasRefund
import EvmAsm.Codegen.Programs.CreateCodeEffectLog
import EvmAsm.Codegen.Programs.CreateDeployedCodeValid
import EvmAsm.Codegen.Programs.CreateCreatorNonce
import EvmAsm.Codegen.Programs.CreateFrameDescend
import EvmAsm.Codegen.Programs.NonstorageEffectLog
import EvmAsm.Codegen.Programs.StorageReadLog
import EvmAsm.Codegen.CallFrameLayout
import EvmAsm.Codegen.Programs.Address
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.EvmOpcodes
import EvmAsm.Codegen.Programs.EvmNonce
import EvmAsm.Codegen.Programs.EvmCodes
import EvmAsm.Codegen.Programs.EvmOpcodesExtcodecopy
import EvmAsm.Codegen.Programs.EvmStorageAccessGas
import EvmAsm.Codegen.Programs.PrecompileBackendProbes
import EvmAsm.Codegen.Programs.AmsterdamSystemTx
import EvmAsm.Codegen.Programs.ModexpBackend
import EvmAsm.Codegen.Programs.Bn254Curve
import EvmAsm.Codegen.Programs.Bn254Pairing
import EvmAsm.Codegen.Programs.Bls12G1
import EvmAsm.Codegen.Programs.Bls12G2
import EvmAsm.Codegen.Programs.Bls12Pairing
import EvmAsm.Codegen.Programs.Bls12Kzg
import EvmAsm.Codegen.Programs.Blake2f
import EvmAsm.Codegen.Programs.P256Verify
import EvmAsm.Codegen.Programs.Bls12Map
import EvmAsm.Codegen.Programs.Ripemd160
import EvmAsm.Codegen.Programs.StateCompose
import EvmAsm.Codegen.Programs.StatePredicates
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.SeedTxAccessList
import EvmAsm.Codegen.Programs.AccountBalance
import EvmAsm.Codegen.Programs.EIP7708Logs
import EvmAsm.Codegen.Programs.RuntimeSameBlockCode
import EvmAsm.Codegen.Programs.CallFrameBase
import EvmAsm.Codegen.Programs.CallFrameSwitch
import EvmAsm.Codegen.Programs.CallFrameDescend
import EvmAsm.Codegen.Programs.CallFrameReturn
import EvmAsm.Codegen.Programs.StaticContext
import EvmAsm.Stateless.SpecRef.InstructionsEnv

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Rounded capture capacity for the Amsterdam builder-deposit predeploy:
    64 requests × 184 bytes = 11,776 bytes, rounded to 12 KiB so the RV64
    immediate remains a single instruction.  The builder-exit body is smaller. -/
def systemCallReturndataMaxBytes : Nat := 12288

#guard systemCallReturndataMaxBytes = 12288

/-- EIP-170's Amsterdam deployed-code limit.  Top-level creation retains a
    successful initcode RETURN in a fixed buffer of exactly this size before
    applying the code-deposit rules. -/
def topLevelCreationReturndataMaxBytes : Nat := 65536

#guard topLevelCreationReturndataMaxBytes = 65536

def selfdestructDestroyedAddressCap : Nat := 32768
def selfdestructSeenOriginCap : Nat := 65536

/-- Protocol EVM stack depth in 256-bit words. The dispatcher stack arena
    is static, so this is the capacity that valid bytecode may rely on. -/
def evmStackWordCapacity : Nat := 1024

/-- Runtime EVM stack slot size: one 256-bit word. -/
def evmStackWordBytes : Nat := 32

/-- Static byte size reserved for the runtime EVM stack arena. -/
def evmStackScratchBytes : Nat := evmStackWordCapacity * evmStackWordBytes

/-- Guard bytes around the EVM stack arena for opcode bodies that still use
    nearby stack-relative offsets as internal scratch. -/
def evmStackGuardBytes : Nat := 512

/-- Concrete byte capacity of the root runtime EVM memory arena (depth-0
    `evm_memory`). This is a guest implementation bound, not a protocol limit.
    Depth-0 memory is larger than nested-frame memory so runtime gas replay can
    execute large-but-valid memory expansions without inflating every call-frame
    slot in the preallocated frame array. Nested frames keep `frameMemBytes`. -/
def runtimeMemoryBytes : Nat := 0x400000

/-- Preserve the historical `.data` layout after moving root EVM memory into
    its dedicated fixed RegionMap arena. -/
def runtimeMemoryLayoutPadBytes : Nat := 0x50000

/-- Shared CALL/STATICCALL precompile-frame status word offset. -/
def precompileFrameStatusOff : Nat := 0

/-- Shared CALL/STATICCALL precompile-frame returndata-length offset. -/
def precompileFrameReturndataLenOff : Nat := 8

/-- Shared CALL/STATICCALL precompile-frame returndata byte window offset. -/
def precompileFrameReturndataOff : Nat := 16

/-- G1-class compact input lane, also reused as G2 ADD's first operand lane. -/
def precompileFrameBls12G1Input0Off : Nat := 144

/-- G1 ADD compact second operand lane. -/
def precompileFrameBls12G1Input1Off : Nat := 240

/-- G1-class compact result lane, also reused by map-Fp-to-G1 and pairing bool. -/
def precompileFrameBls12G1OutputOff : Nat := 336

/-- G2 ADD compact first operand lane. -/
def precompileFrameBls12G2AddInput0Off : Nat := precompileFrameBls12G1Input0Off

/-- G2 ADD compact second operand lane. -/
def precompileFrameBls12G2AddInput1Off : Nat := 336

/-- G2 ADD compact result lane. -/
def precompileFrameBls12G2AddOutputOff : Nat := 528

/-- G2-class compact input lane for MSM and map-Fp2-to-G2. -/
def precompileFrameBls12G2InputOff : Nat := 720

/-- G2-class compact result lane for MSM and map-Fp2-to-G2. -/
def precompileFrameBls12G2OutputOff : Nat := 944

/-- ECRECOVER staged input words: hash, v, r, s after buffer_read padding. -/
def precompileFrameEcrecoverInputOff : Nat := 1152

/-- Routing flag cell name (see the flag+`ret` discipline note below;
    defined here because the stack guards reference it). -/
def haltFlagLabel : String := "evm_halt_flag"

/-- Inline flag+`ret` halt block for the stack guards (bead `evm-asm-vgyg9`
    = `.49.a`; §3 amendment in docs/4ch8f-interp-strategy.md): set
    `evm_halt_flag := code` and return.  `emitDispatchResume` routes the code
    to the matching exceptional exit join (`7`→`.exit_stack_underflow`,
    `8`→`.exit_stack_overflow`).

    Deliberately does NOT load `.Ldispatch_resume` into `x1` (contrast
    `dispatchHaltRet`): guards run at handler entry, where `x1` still holds
    the `jalr`-passed return address, so a plain `ret` reaches the same
    resume point — and preserving the caller's `x1` keeps the packaged
    handle's `FnHandleS.sound` contract (∀ aligned `ret`) provable. -/
def stackGuardHaltAsm (code : Nat) : String :=
  s!"  li x5, {code}\n" ++
  s!"  la x6, {haltFlagLabel}\n" ++
  "  sd x5, 0(x6)\n" ++
  "  ret\n"

/-- Raw dispatcher guard for handlers that read `wordCount` EVM stack
    words before their body runs. The EVM stack grows downward from the
    CURRENT frame's stack top; a handler needing `n` words requires
    `x12 <= cur_stack_top - 32*n`. If not, halt via the flag+`ret`
    discipline with routing code 7 (`.exit_stack_underflow`) before any
    body performs unchecked loads — the skip-branch keeps the handler
    single-`ret`-exit (vgyg9; the local label `137` is repo-unique).

    Frame-relative: reads `evm_cur_stack_top` (a cell holding the current
    frame's stack-top address) rather than the global `evm_stack_top` label,
    so a child call frame — whose stack lives in `call_frame_arena`, ABOVE the
    global arena — is bounded against its OWN top. At depth 0 the cell is
    statically `&evm_stack_top`, so the depth-0 output is byte-identical. -/
def stackUnderflowGuardAsm (wordCount : Nat) : String :=
  "  la x14, evm_cur_stack_top\n" ++
  "  ld x14, 0(x14)\n" ++
  s!"  addi x14, x14, -{wordCount * evmStackWordBytes}\n" ++
  "  bgeu x14, x12, 137f\n" ++
  stackGuardHaltAsm 7 ++
  "137:"

/-- Raw dispatcher guard for handlers that push one EVM stack word. The EVM
    stack is full exactly when the live pointer has reached the current frame's
    stack low; pushing then would decrement below the protocol 1024-word arena.
    On overflow, halt via the flag+`ret` discipline with routing code 8
    (`.exit_stack_overflow`); see `stackUnderflowGuardAsm` for the shape.

    Frame-relative: reads `evm_cur_stack_low` (the current frame's stack-low
    address) instead of the global `evm_stack_low` label, so a child call
    frame's pushes are bounded against its own arena. At depth 0 the cell is
    statically `&evm_stack_low`, so the depth-0 output is byte-identical. -/
def stackOverflowGuardAsm : String :=
  "  la x14, evm_cur_stack_low\n" ++
  "  ld x14, 0(x14)\n" ++
  "  bltu x14, x12, 137f\n" ++
  stackGuardHaltAsm 8 ++
  "137:"

/-! ### flag+`ret` handler-tail discipline (bead 4ch8f.10.3)

    Every opcode handler is invoked via `jalr x1, x7, 0` at the dispatch
    site and MUST return via `ret` so it satisfies the `Stmt.callRegS` /
    `FnHandleS` contract (docs/4ch8f-interp-strategy.md §3).  Historically
    some handlers ended by *jumping* elsewhere instead of returning:
      * STOP → `j .exit_label`
      * RETURN/REVERT (depth-0 halt) → `j .exit_no_epilogue`
      * INVALID → `j .exit_invalid_op`
      * SELFDESTRUCT (depth-0) → `j .exit_selfdestruct`
      * CALL-family / depth-aware halts (frame descend/return) → `j .dispatch_loop`

    Convention (§3 amendment):
      * A **memory flag cell** `evm_halt_flag` (u64) carries the routing
        decision across the handler's `ret`.  `0` = continue the loop;
        a nonzero routing code selects an exit join (see `dispatchHaltRet`).
        A memory cell is used (not a register) so it survives the handler's
        own register restores / `sp` resets / helper calls, and it does not
        collide with any EVM-ABI register the handlers pin (x5/x6/x7 are
        handler-clobbered scratch; x10/x11/x12 the a0/a1/a2 aliases).
      * The dispatch site's continuation label is `.Ldispatch_resume`,
        emitted immediately after the `jalr`.  A handler "returns to the
        loop" by loading that label into `x1` and `ret`-ing
        (`dispatchContinueRet`); a handler "halts" by additionally setting
        `evm_halt_flag` (`dispatchHaltRet kind`).
      * `emitDispatchResume` (at `.Ldispatch_resume`) reads the flag,
        resets it, and branches to the encoded exit join — otherwise falls
        straight through to `.dispatch_loop`.

    Byte-behavior preservation: for a *continue* handler,
    `la x1, .Ldispatch_resume; ret` reaches `.Ldispatch_resume` with the
    flag `0`, which falls through to `.dispatch_loop` exactly as the old
    `j .dispatch_loop` did (the only observable difference is x1/x5/x6
    clobbers, all dead/reassigned at the loop head).  For a *halt* handler,
    the flag is set, `ret` reaches `.Ldispatch_resume`, the flag is reset,
    and control lands at the same exit join the old `j .exit_*` targeted
    (x5/x6/x7/x1 are dead at every join, which reload x16/x17/x20). -/

/-- Dispatch-site continuation label, emitted right after the `jalr`. -/
def dispatchResumeLabel : String := ".Ldispatch_resume"

/-- Handler exit that continues the loop: restore the dispatch
    continuation into `x1` and `ret`.  Byte-behavior-identical to the old
    `j .dispatch_loop`. -/
def dispatchContinueRet : String :=
  s!"  la x1, {dispatchResumeLabel}\n  ret"

/-- Handler exit that halts the interpreter: set `evm_halt_flag` to the
    routing code `kind`, then `ret` to `.Ldispatch_resume`, which routes on
    the flag.  Routing codes: `1` STOP→`.exit_label`, `2`
    RETURN/REVERT→`.exit_no_epilogue`, `3` INVALID→`.exit_invalid_op`,
    `4` SELFDESTRUCT→`.exit_selfdestruct`; the stack guards set `7`
    →`.exit_stack_underflow` / `8`→`.exit_stack_overflow` inline via
    `stackGuardHaltAsm` (which preserves `x1`, unlike this helper). -/
def dispatchHaltRet (kind : Nat) : String :=
  s!"  li x5, {kind}\n" ++
  s!"  la x6, {haltFlagLabel}\n" ++
  "  sd x5, 0(x6)\n" ++
  s!"  la x1, {dispatchResumeLabel}\n  ret"

/-- Dispatch resume point + flag routing, emitted immediately after the
    loop's `jalr x1, x7, 0` (replacing the bare `j .dispatch_loop`).  When
    the halt flag is `0` (the overwhelmingly common case) this is a single
    load + `beqz` fall-through into `.dispatch_loop`. -/
def emitDispatchResume : String :=
  -- Child frames enter at the same resume sequence their former
  -- `dispatchContinueRet` used.  It is deliberately below the root-only
  -- setup: a descended frame already owns its registers, stack, memory, and
  -- rollback snapshot.
  ".runtime_tx_child_message_entry:\n" ++
  s!"{dispatchResumeLabel}:\n" ++
  s!"  la x5, {haltFlagLabel}\n" ++
  "  ld x6, 0(x5)\n" ++
  "  beqz x6, .dispatch_loop\n" ++
  "  sd x0, 0(x5)\n" ++
  "  li x7, 1\n  beq x6, x7, .exit_label\n" ++
  "  li x7, 2\n  beq x6, x7, .exit_no_epilogue\n" ++
  "  li x7, 3\n  beq x6, x7, .exit_invalid_op\n" ++
  "  li x7, 4\n  beq x6, x7, .exit_selfdestruct\n" ++
  "  li x7, 7\n  beq x6, x7, .exit_stack_underflow\n" ++
  "  li x7, 8\n  beq x6, x7, .exit_stack_overflow\n" ++
  "  j .dispatch_loop"

/-- Tail emitted after each handler's verified body.

    `advanceAndRet width` is the standard subroutine return: advance
    the EVM PC (`x10`) by the opcode's byte width, then `ret` back to
    the dispatcher loop. `custom asm` is for handlers that don't
    return to the dispatcher (e.g. STOP → `j .exit_label`). -/
inductive HandlerTail where
  | advanceAndRet (width : Nat)
  | custom (asm : String)

/-- Spec for one opcode handler in the M5b dispatch registry. -/
structure OpcodeHandlerSpec where
  /-- Subroutine label (e.g. `"h_ADD"`). Must be unique across the
      registry; rendered as a label in the emitted asm and as a
      target in the 256-entry jump table. -/
  label   : String
  /-- Opcode bytes this handler covers. Bytes not claimed by any
      spec route to `h_invalid` via the jump table fill. -/
  opcodes : List Nat
  /-- Raw asm emitted *between* the label and the verified body.
      Used to save dispatcher-state registers that the verified body
      may clobber. For example, `evm_mul` / `evm_signextend` /
      `evm_byte` / `evm_shr` use `x10` as a scratch accumulator —
      our dispatcher expects `x10` to be the preserved EVM code
      pointer, so those handlers carry `preBody := "  mv x9, x10"`
      and a tail that restores via `mv x10, x9` before advancing.
      Empty string means "no save needed". -/
  preBody : String := ""
  /-- Verified RV64 body, rendered verbatim via `emitProgram`.
      May be empty (e.g. STOP has no work to do before exiting). -/
  body    : Program
  /-- Optional label emitted *between* the verified body and the tail.
      Used by M9's trampoline pattern for handlers whose verified
      bodies end with a saved-ra-ret (`JALR x0, x18, 0`): the body's
      ret-jump targets this label (set in `preBody` via
      `la x18, <postBodyLabel>`), and the tail then restores `x10`
      and falls through. Handlers that return cleanly via the
      standard `addi; ret` tail leave this `none` — emission is then
      byte-identical to pre-M9. -/
  postBodyLabel : Option String := none
  /-- Tail emitted after the body (or after `postBodyLabel:` if set). -/
  tail    : HandlerTail

namespace OpcodeHandlerSpec

/-- Render a handler tail as raw asm. -/
def emitTail : HandlerTail → String
  | .advanceAndRet width => s!"  addi x10, x10, {width}\n  ret"
  | .custom asm          => asm

/-- Render the handler as a labeled subroutine. Empty bodies (STOP,
    INVALID-style entries) skip the body line entirely to avoid a
    blank line after the label. `preBody` is inserted between the
    label and the body (used for clobber-saving). `postBodyLabel`,
    when set, emits an additional label between the body and the
    tail (M9 trampoline pattern). -/
def emitSubroutine (h : OpcodeHandlerSpec) : String :=
  let preLine  := if h.preBody.isEmpty then "" else h.preBody ++ "\n"
  let bodyText := emitProgram h.body
  let bodyLine := if bodyText.isEmpty then "" else bodyText ++ "\n"
  let postLine := match h.postBodyLabel with
                  | some lbl => s!"{lbl}:\n"
                  | none     => ""
  s!"{h.label}:\n" ++ preLine ++ bodyLine ++ postLine ++ emitTail h.tail

end OpcodeHandlerSpec

/-- The label that opcode byte `b` should dispatch to. Bytes not
    claimed by any spec route to `h_invalid`. -/
def jumpTargetLabel (registry : List OpcodeHandlerSpec) (b : Nat) : String :=
  match registry.find? (fun h => h.opcodes.contains b) with
  | some h => h.label
  | none   => "h_invalid"

/-- Render the 256-entry jump table inside the `.data` section.
    Does *not* emit its own `.section .data` directive — the caller
    (`emitDispatcherDataSection`) opens the section once at the top. -/
def emitJumpTable (registry : List OpcodeHandlerSpec) : String :=
  let entries :=
    (List.range 256).map (fun b => s!"  .dword {jumpTargetLabel registry b}")
  ".balign 8\n" ++
  "opcode_handlers:\n" ++
  String.intercalate "\n" entries

open EvmAsm.Stateless.SpecRef.GasCosts in
/-- M30 (gas metering, first slice): the **static base** gas cost of each
    EVM opcode byte, used by the dispatch loop to charge gas per instruction.

    Sourced from the standard EVM gas tiers
    (`execution-specs/src/ethereum/forks/prague/vm/gas.py`): ZERO=0,
    JUMPDEST=1, BASE=2, VERYLOW=3, LOW=5, MID=8, HIGH=10, BLOCKHASH=20,
    KECCAK256 base=30, LOG base=375, warm access=100. Amsterdam/EIP-8037
    charges CREATE/CREATE2's account-access regular component as
    CREATE_ACCESS = ACCOUNT_WRITE(8000) + COLD_STORAGE_ACCESS(3000).

    **Static base costs only** — all *dynamic* components are dropped:
    memory-expansion, copy (per-word), KECCAK/LOG per-word/per-topic, EXP
    per-byte, and cold-access surcharges (SLOAD/BALANCE/EXTCODE*/CALL use

    the warm floor of 100; SSTORE uses 100; cold deltas are charged in
    opcode-specific helpers).


    Halt opcodes (STOP/RETURN/REVERT/INVALID/SELFDESTRUCT) and every byte
    not assigned a real opcode are 0, so trusted programs never spuriously
    run out of gas on a terminator or an unwired byte.

    ## Sourced from SpecRef rather than transcribed (GH #10569)

    Every entry with a SpecRef symbol now names it, so a fork repricing an
    opcode fails the build here instead of silently charging the old value.
    Before substituting, each symbol's value was compared against the literal it
    replaces and **all agreed** — so this records that the table was *correct*,
    not merely that it is now pinned.

    Entries that keep a bare literal, and why:
    * `CREATE`/`CREATE2` (11000) and `SELFDESTRUCT` (5000) — no SpecRef symbol
      exists for these base charges;
    * halt and unwired bytes — deliberately 0 per the note above, so there is
      no static constant to name. -/
def staticGasCost (op : Nat) : Nat :=
  if op = 0x5f then OPCODE_PUSH0
  else if 0x60 ≤ op ∧ op ≤ 0x7f then OPCODE_PUSH        -- PUSH1..PUSH32
  else if 0x80 ≤ op ∧ op ≤ 0x8f then OPCODE_DUP         -- DUP1..DUP16
  else if 0x90 ≤ op ∧ op ≤ 0x9f then OPCODE_SWAP        -- SWAP1..SWAP16
  else if op = 0xe6 then OPCODE_DUPN                    -- EIP-8024
  else if op = 0xe7 then OPCODE_SWAPN
  else if op = 0xe8 then OPCODE_EXCHANGE
  else if 0xa0 ≤ op ∧ op ≤ 0xa4 then OPCODE_LOG_BASE    -- LOG0..LOG4
  else match op with
    -- arithmetic
    | 0x01 => OPCODE_ADD        | 0x03 => OPCODE_SUB
    | 0x02 => OPCODE_MUL        | 0x04 => OPCODE_DIV
    | 0x05 => OPCODE_SDIV       | 0x06 => OPCODE_MOD
    | 0x07 => OPCODE_SMOD       | 0x0b => OPCODE_SIGNEXTEND
    | 0x08 => OPCODE_ADDMOD     | 0x09 => OPCODE_MULMOD
    | 0x0a => OPCODE_EXP_BASE
    -- comparison & bitwise
    | 0x10 => OPCODE_LT         | 0x11 => OPCODE_GT
    | 0x12 => OPCODE_SLT        | 0x13 => OPCODE_SGT
    | 0x14 => OPCODE_EQ         | 0x15 => OPCODE_ISZERO
    | 0x16 => OPCODE_AND        | 0x17 => OPCODE_OR
    | 0x18 => OPCODE_XOR        | 0x19 => OPCODE_NOT
    | 0x1a => OPCODE_BYTE
    | 0x1b => OPCODE_SHL        | 0x1c => OPCODE_SHR
    | 0x1d => OPCODE_SAR
    | 0x1e => OPCODE_CLZ                                 -- EIP-7939
    | 0x20 => OPCODE_KECCAK256_BASE
    -- environment / context
    | 0x30 => OPCODE_ADDRESS    | 0x32 => OPCODE_ORIGIN
    | 0x33 => OPCODE_CALLER     | 0x34 => OPCODE_CALLVALUE
    | 0x3a => OPCODE_GASPRICE
    | 0x35 => OPCODE_CALLDATALOAD
    | 0x36 => OPCODE_CALLDATASIZE
    | 0x38 => OPCODE_CODESIZE   | 0x3d => OPCODE_RETURNDATASIZE
    | 0x37 => OPCODE_CALLDATACOPY_BASE
    | 0x39 => OPCODE_CODECOPY_BASE
    | 0x3e => OPCODE_RETURNDATACOPY_BASE
    -- account-access opcodes: the STATIC entry is the warm floor; the cold
    -- delta is added by the access-charge path, not here.
    | 0x31 => WARM_ACCESS       -- BALANCE
    | 0x3b => WARM_ACCESS       -- EXTCODESIZE
    | 0x3c => WARM_ACCESS       -- EXTCODECOPY
    | 0x3f => WARM_ACCESS       -- EXTCODEHASH
    | 0x40 => OPCODE_BLOCKHASH
    | 0x41 => OPCODE_COINBASE   | 0x42 => OPCODE_TIMESTAMP
    | 0x43 => OPCODE_NUMBER     | 0x44 => OPCODE_PREVRANDAO
    | 0x45 => OPCODE_GASLIMIT   | 0x46 => OPCODE_CHAINID
    | 0x48 => OPCODE_BASEFEE    | 0x4a => OPCODE_BLOBBASEFEE
    | 0x4b => OPCODE_SLOTNUM
    | 0x47 => FAST_STEP                                  -- SELFBALANCE (environment.py:524)
    | 0x49 => OPCODE_BLOBHASH
    -- stack / memory / flow
    | 0x50 => OPCODE_POP
    | 0x51 => OPCODE_MLOAD_BASE | 0x52 => OPCODE_MSTORE_BASE
    | 0x53 => OPCODE_MSTORE8_BASE
    | 0x54 => WARM_ACCESS       -- SLOAD  (warm floor)
    | 0x55 => WARM_ACCESS       -- SSTORE (warm floor)
    | 0x56 => OPCODE_JUMP       | 0x57 => OPCODE_JUMPI
    | 0x58 => OPCODE_PC         | 0x59 => OPCODE_MSIZE
    | 0x5a => OPCODE_GAS        | 0x5b => OPCODE_JUMPDEST
    | 0x5c => OPCODE_TLOAD      | 0x5d => OPCODE_TSTORE
    | 0x5e => OPCODE_MCOPY_BASE
    -- child frames (base; dynamic call/create costs charged elsewhere)
    | 0xf0 => CREATE_ACCESS | 0xf5 => CREATE_ACCESS      -- CREATE, CREATE2 (system.py:193,247)
    | 0xf1 => WARM_ACCESS       -- CALL         (warm floor)
    | 0xf2 => WARM_ACCESS       -- CALLCODE
    | 0xf4 => WARM_ACCESS       -- DELEGATECALL
    | 0xfa => WARM_ACCESS       -- STATICCALL
    | 0xff => 5000                                       -- SELFDESTRUCT: no SpecRef symbol
    -- STOP (0x00), RETURN (0xf3), REVERT (0xfd), INVALID (0xfe),
    -- and all unwired bytes → 0.
    | _ => 0

/-- Render the 256-entry static gas-cost table (`opcode_gas_costs:`,
    256 × `.dword`, 2 KiB) into the `.data` section. Indexed by
    `opcode * 8` — the same index the dispatch loop computes for the
    jump table. -/
def emitGasCostTable : String :=
  let entries :=
    (List.range 256).map (fun b => s!"  .dword {staticGasCost b}")
  ".balign 8\n" ++
  "opcode_gas_costs:\n" ++
  String.intercalate "\n" entries

private def emitBls12G1MsmDiscountTable : String :=
  ".balign 8\n" ++
  "bls12_g1_msm_discount_table:\n" ++
  "  .quad 1000, 949, 848, 797, 764, 750, 738, 728\n" ++
  "  .quad 719, 712, 705, 698, 692, 687, 682, 677\n" ++
  "  .quad 673, 669, 665, 661, 658, 654, 651, 648\n" ++
  "  .quad 645, 642, 640, 637, 635, 632, 630, 627\n" ++
  "  .quad 625, 623, 621, 619, 617, 615, 613, 611\n" ++
  "  .quad 609, 608, 606, 604, 603, 601, 599, 598\n" ++
  "  .quad 596, 595, 593, 592, 591, 589, 588, 586\n" ++
  "  .quad 585, 584, 582, 581, 580, 579, 577, 576\n" ++
  "  .quad 575, 574, 573, 572, 570, 569, 568, 567\n" ++
  "  .quad 566, 565, 564, 563, 562, 561, 560, 559\n" ++
  "  .quad 558, 557, 556, 555, 554, 553, 552, 551\n" ++
  "  .quad 550, 549, 548, 547, 547, 546, 545, 544\n" ++
  "  .quad 543, 542, 541, 540, 540, 539, 538, 537\n" ++
  "  .quad 536, 536, 535, 534, 533, 532, 532, 531\n" ++
  "  .quad 530, 529, 528, 528, 527, 526, 525, 525\n" ++
  "  .quad 524, 523, 522, 522, 521, 520, 520, 519\n"

private def emitBls12G2MsmDiscountTable : String :=
  ".balign 8\n" ++
  "bls12_g2_msm_discount_table:\n" ++
  "  .quad 1000, 1000, 923, 884, 855, 832, 812, 796\n" ++
  "  .quad 782, 770, 759, 749, 740, 732, 724, 717\n" ++
  "  .quad 711, 704, 699, 693, 688, 683, 679, 674\n" ++
  "  .quad 670, 666, 663, 659, 655, 652, 649, 646\n" ++
  "  .quad 643, 640, 637, 634, 632, 629, 627, 624\n" ++
  "  .quad 622, 620, 618, 615, 613, 611, 609, 607\n" ++
  "  .quad 606, 604, 602, 600, 598, 597, 595, 593\n" ++
  "  .quad 592, 590, 589, 587, 586, 584, 583, 582\n" ++
  "  .quad 580, 579, 578, 576, 575, 574, 573, 571\n" ++
  "  .quad 570, 569, 568, 567, 566, 565, 563, 562\n" ++
  "  .quad 561, 560, 559, 558, 557, 556, 555, 554\n" ++
  "  .quad 553, 552, 552, 551, 550, 549, 548, 547\n" ++
  "  .quad 546, 545, 545, 544, 543, 542, 541, 541\n" ++
  "  .quad 540, 539, 538, 537, 537, 536, 535, 535\n" ++
  "  .quad 534, 533, 532, 532, 531, 530, 530, 529\n" ++
  "  .quad 528, 528, 527, 526, 526, 525, 524, 524\n"

/-- Shared scratch for the CALL/STATICCALL precompile frame surface.
    Follow-up precompile bodies can write returndata bytes here before
    copying them into caller memory. Layout:
      +precompileFrameStatusOff             status / success word
      +precompileFrameReturndataLenOff      returndata length
      +precompileFrameReturndataOff         returndata data window
                                            (precompileFrameReturndataCapBytes
                                            bytes — ≥ any stageable retlen, so
                                            the FULL returndata is staged)
      +precompileFrameBls12G1Input0Off      G1-class compact input scratch
      +precompileFrameBls12G1Input1Off      G1 ADD compact p2 scratch
      +precompileFrameBls12G1OutputOff      G1-class compact result / pairing bool
      +precompileFrameBls12G2AddInput0Off   G2 ADD compact p1 scratch
      +precompileFrameBls12G2AddInput1Off   G2 ADD compact p2 scratch
      +precompileFrameBls12G2AddOutputOff   G2 ADD compact result scratch
      +precompileFrameBls12G2InputOff       G2-class compact input scratch
      +precompileFrameBls12G2OutputOff      G2-class compact result scratch
      +precompileFrameEcrecoverInputOff     ECRECOVER hash/v/r/s words.

    MODEXP uses separate `modexp_*_scratch` labels because it needs up to
    4 KiB of zero-padded base/exponent/modulus/output buffers.

    The lanes are handler-local scratch, so G1/G2 ADD may still reuse the
    older offsets internally. Map-Fp2-to-G2 uses the G2-class lane to avoid
    colliding with map-Fp-to-G1 stacked PR edits around +144/+336.

    The BLS/ECRECOVER lanes live INSIDE the returndata data window
    (+144..+1280 < +16 + precompileFrameReturndataCapBytes). That overlap is
    the existing discipline: lanes are written and consumed while a handler
    runs, strictly before that handler stages its returndata bytes (MODEXP
    already wrote up to +1040 across them). -/
def emitPrecompileFrameData : String :=
  ".balign 8\n" ++
  "evm_precompile_frame:\n" ++
  "  .zero " ++ toString (precompileFrameReturndataOff + precompileFrameReturndataCapBytes) ++ "\n"

/-- SELFDESTRUCT runtime staging scratch.

    `evm_selfdestruct_beneficiary` stores the popped beneficiary address as
    20 canonical big-endian bytes (the low 160 bits of the EVM stack word,
    with higher bits ignored). `evm_selfdestruct_created_in_tx` is the
    transaction-local EIP-6780 marker that CREATE/CREATE2 integration will set
    before SELFDESTRUCT reaches balance/deletion handling. It defaults to zero.
    `evm_selfdestruct_staged` is a u64 flag used by the test/diagnostic surface
    until later account-access/state children consume this staged beneficiary
    directly. `evm_selfdestruct_log_status` records the EIP-7708 synthetic-log
    bridge: 0 success/no-log, 1 skipped before account inputs, 2 balance parse
    failure, 3 append failure. -/
def emitSelfdestructData : String :=
  ".balign 32\n" ++
  "evm_selfdestruct_beneficiary:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "evm_selfdestruct_balance_scratch:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "rt_deleg_warm_be:\n" ++       -- 5tmlt: BE-20 scratch for the post-reset delegation-target warm
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "sd_eip7708_from_sw:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "sd_eip7708_to_sw:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "evm_selfdestruct_created_in_tx:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "evm_selfdestruct_log_status:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "evm_selfdestruct_staged:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "evm_selfdestruct_seen_count:\n  .zero 8\n" ++
  "evm_selfdestruct_seen_overflow:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "evm_selfdestruct_seen_table:\n  .zero " ++ toString (selfdestructSeenOriginCap * 32) ++ "\n" ++
  ".balign 8\n" ++
  "evm_selfdestruct_seen_count_by_depth:\n  .zero " ++ toString (1025 * 8) ++ "\n" ++
  "evm_selfdestruct_seen_overflow_by_depth:\n  .zero " ++ toString (1025 * 8) ++ "\n" ++
  "evm_selfdestruct_destroyed_count:\n" ++
  "  .zero 8\n" ++
  "evm_selfdestruct_destroyed_overflow:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "evm_selfdestruct_destroyed_table:\n" ++
  "  .zero " ++ toString (selfdestructDestroyedAddressCap * 32) ++ "\n"

/-- Zero-padded component and output buffers for the runtime MODEXP backend
    path. EIP-7823 caps each component at 1024 bytes before the backend call. -/
def emitModexpScratchData : String :=
  ".balign 8\n" ++
  "modexp_base_scratch:\n" ++
  "  .zero 1024\n" ++
  "modexp_exp_scratch:\n" ++
  "  .zero 1024\n" ++
  "modexp_modulus_scratch:\n" ++
  "  .zero 1024\n" ++
  "modexp_output_scratch:\n" ++
  "  .zero 1024\n"

/-- Scratch buffers used by `zkvm_sha256`. The wrapper expects these
    labels to exist in the dispatcher's data section. -/
def emitSha256Data : String :=
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n"

/-- Runtime CREATE/CREATE2 child-frame staging arena.

The first implementation slice only records the frame that later slices will
execute: creator/target/value, initcode length+bytes, and empty result/code
arenas. The status word is set to 1 when staging succeeds. -/
def emitCreateChildFrameData : String :=
  ".balign 8\n" ++
  "create_child_status:\n" ++
  "  .zero 8\n" ++
  "create_child_kind:\n" ++
  "  .zero 8\n" ++
  "create_child_init_len:\n" ++
  "  .zero 8\n" ++
  "create_child_return_len:\n" ++
  "  .zero 8\n" ++
  "create_child_code_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "create_child_creator_be:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "create_child_target_be:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "create_child_value_be:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "create_child_stack:\n" ++
  "  .zero 128\n" ++
  ".balign 32\n" ++
  "create_child_initcode:\n" ++
  "  .zero 0x20000\n" ++
  ".balign 32\n" ++
  "create_child_returndata:\n" ++
  "  .zero 0x20000\n" ++
  ".balign 32\n" ++
  "create_child_code:\n" ++
  "  .zero 0x20000\n" ++
  -- bmvmx.1.6.3 / .61.8b (.8b-2): the per-created-account CODE-effect log, co-located with
  -- create_child_code so it is defined in every closure whose CREATE tail deposits into it.
  createCodeEffectLogData ++ "\n" ++
  -- The code-effect log above remains BAL comparator evidence.  Execution reads
  -- use this bounded, real-address keyed CodeState overlay instead, so CREATE /
  -- SELFDESTRUCT / recreate follow current Ethereum state rather than an
  -- append-only event history.
  codeStateData ++ "\n" ++
  -- .61.8c-1: per-creator running-nonce table (multi-CREATE address correctness), co-located
  -- so the CREATE tail's create_creator_nonce_use resolves in every closure.
  createNonceTableData ++ "\n" ++
  -- .61.8.3.5 (.5a/.5b): CREATE-frame descent scratch (create_cd_desc / create_address_word /
  -- create_frame_flag), co-located here so create_frame_descend AND the depth-aware
  -- returnRevertTail CREATE branch resolve create_frame_flag in EVERY closure (guest + probes).
  createFrameDescendData ++ "\n" ++
  -- i3djw.1: per-account NON-STORAGE exec-effect log + the CALL value-transfer producer's
  -- scratch (callee addr / account struct / post-balance), co-located so callDescendFallThrough's
  -- producer resolves record_nonstorage_effect + its buffers in EVERY closure (guest + probes).
  nonstorageEffectLogData ++ "\n" ++
  nonstorageEffectAggregateScratch ++ "\n" ++   -- bmvmx.5.5.7.3: radix-sort scratch for nonstorage_effect_aggregate
  ".balign 8\n" ++
  "nse_callee_be:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "nse_acct:\n  .zero 104\n" ++
  "nse_post_bal:\n  .zero 32\n" ++
  -- i3djw.2: CREATE-site producer scratch — the created account's BE-reversed endowment
  -- (post_balance) and a zero buffer for the absent pre_balance.
  ".balign 32\n" ++
  "nse_create_post_bal:\n  .zero 32\n" ++
  "nse_zero_bal:\n  .zero 32\n" ++
  -- drj99.1 (initcode_calls_with_value bv_fail=44): the created account's staged block-pre balance
  -- (BE), captured at create_frame_descend before the endowment credit, used as the pre_balance of
  -- the created-account endowment-credit nonstorage record (ChildFrameHandlerTails .Lcr_nse_done).
  "nse_create_pre_bal:\n  .zero 32\n" ++
  "cr_alive_bal:\n  .zero 32\n" ++
  -- Amsterdam generic_create computes target_alive from the current tx_state before
  -- incorporating the child. A same-tx-created target can be alive even when its
  -- block-pre balance is zero; NoopHalt stashes that code-effect-log hit here.
  "create_target_alive_current_tx:\n  .zero 8\n" ++
  "create_state_gas_charged_current:\n  .zero 8\n" ++
  -- v0.6 (evm-asm-0w05f.17.2): failed-create NEW_ACCOUNT refund gate. The
  -- REVERT/invalid-deposit/exceptional-halt paths stash the by-depth
  -- create_target_alive_flag here before frame_return pops the depth; a
  -- nonzero value (alive target -> charge skipped) suppresses the
  -- credit_state_gas_refund mirror.
  "create_failed_refund_skip:\n  .zero 8\n"

/-- Scratch labels shared by runtime account-witness helpers.

These labels match the standalone header-state-root probes in
`Programs/EvmOpcodes.lean` for `extcodehash_at_header_state_root` and
its account-trie dependencies. They live in the dispatcher `.data`
section so BALANCE/EXTCODE* runtime handlers can share one witness-backed
account lookup surface. -/
def emitRuntimeAccountWitnessData : String :=
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_lookup_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_lookup_offset:\n" ++
  "  .zero 8\n" ++
  "mw_lookup_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_child_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_path_offset:\n" ++
  "  .zero 8\n" ++
  "mw_path_length:\n" ++
  "  .zero 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 32\n" ++
  "mlk_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "mlk_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "ad_offset:\n" ++
  "  .zero 8\n" ++
  "ad_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aa_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aa_value_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "bal_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "bal_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "bal_addr_padded:\n  .zero 32\n" ++   -- yisv8 .spine.2: padded query addr for the live-balance scan
  ".balign 32\n" ++
  "bal_output_scratch:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "aex_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "aex_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "aex_predicate:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aie_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "aie_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "aie_predicate:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aie_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70\n" ++
  ".balign 8\n" ++
  "sdai_status:\n" ++
  "  .zero 8\n" ++
  "sdai_origin_len:\n" ++
  "  .zero 8\n" ++
  "sdai_beneficiary_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "sdai_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "sdai_origin_address:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "sdai_origin_rlp:\n" ++
  "  .zero 256\n" ++
  ".balign 32\n" ++
  "sdai_beneficiary_rlp:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "sdai_transfer_status:\n" ++
  "  .zero 8\n" ++
  "sdai_transfer_origin_len:\n" ++
  "  .zero 8\n" ++
  "sdai_transfer_beneficiary_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "sdai_transfer_output:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "t48_offset:\n" ++
  "  .zero 8\n" ++
  "t48_length:\n" ++
  "  .zero 8\n" ++
  "mset_span_start:\n" ++
  "  .zero 8\n" ++
  "mset_span_size:\n" ++
  "  .zero 8\n" ++
  "mset_payload_start:\n" ++
  "  .zero 8\n" ++
  "mset_head_len:\n" ++
  "  .zero 8\n" ++
  "mset_tail_start:\n" ++
  "  .zero 8\n" ++
  "mset_tail_len:\n" ++
  "  .zero 8\n" ++
  "mset_new_payload_len:\n" ++
  "  .zero 8\n" ++
  "mset_prefix_len:\n" ++
  "  .zero 8\n" ++
  "mset_cursor:\n" ++
  "  .zero 8\n" ++
  "aab_bal_off:\n" ++
  "  .zero 8\n" ++
  "aab_bal_len:\n" ++
  "  .zero 8\n" ++
  "aab_enc_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aab_bal32:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "aab_enc:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "sdbt_delta32:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "eahsr_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "eahsr_address_scratch:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "eahsr_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "eahsr_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70\n" ++
  ".balign 32\n" ++
  "ecsahsr_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ecsahsr_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "ecsahsr_dummy_offset:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "ecsahsr_code_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "ecsahsr_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70\n" ++
  ".balign 32\n" ++
  "ecc_address_scratch:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ecc_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ecc_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "eccp_codes_ptr:\n" ++
  "  .zero 8\n" ++
  "eccp_codes_len:\n" ++
  "  .zero 8\n" ++
  "ecc_match_offset:\n" ++
  "  .zero 8\n" ++
  "ecc_match_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "nonce_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "nonce_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "create_nonce:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "create_init_offset:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "create_init_size:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "create_sender_be:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "create_salt_be:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "create_address_be:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "create_value_be:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "create_balance_be:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "create_creator_newbal:\n" ++
  "  .zero 32\n" ++
  emitCreateChildFrameData ++
  ".balign 8\n" ++
  "ac_buffer:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ac_nonce_be:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "ac_digest:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ac2_inner_digest:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ac2_outer_digest:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ac2_preimage:\n" ++
  "  .zero 88\n" ++
  ".balign 32\n" ++
  "hcon_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "hcon_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "hcon_predicate:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "hcon_empty_trie_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21\n" ++
  ".balign 32\n" ++
  "hcon_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70\n" ++
  ".balign 32\n" ++
  "ecc_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70\n"

/-- Dispatcher prologue: init EVM pointers (`x10` = code, `x12` =
    stack top, `x13` = EVM memory base) and enter the main
    fetch/decode/dispatch loop. Each iteration loads the opcode byte
    at `[x10]`, indexes the jump table, `jalr`s to the handler, then
    jumps back to `.dispatch_loop`.

    `x13` is added in M7 for the memory opcodes (MLOAD, MSTORE,
    MSTORE8). Handlers that don't touch memory ignore it; the verified
    bodies that do use it take `memBaseReg` as a Lean argument and our
    M7 handler entries pass `.x13`.

    `x20` is added in M12 for the simple environment opcodes
    (ADDRESS, CALLER, …). The verified `evm_env_load` body takes
    `envBaseReg` as a Lean argument and our M12 env handler entries
    pass `.x20`. `x20` was chosen because no verified body in
    `EvmAsm/Evm64/*/Program.lean` references it AND no existing
    handler `preBody` writes to it — the M8/M9/M10 DIV/MOD/SDIV/
    SMOD/ADDMOD handlers all save `x10` to `x14`, so `x14` is
    NOT safe as a permanent dispatcher register.

    `x21` is added in M15 for the control-flow opcodes
    (PC, JUMP, JUMPI). It holds the **initial value of `x10`** at
    `_start` — the EVM code base. PC computes `pc = x10 - x21`;
    JUMP/JUMPI compute `target = x21 + dest`. `x21` is audited the
    same way `x20` was: zero references across `EvmAsm/Evm64/*/Program.lean`
    and zero uses by any existing handler `preBody`/`tail`. -/
def emitDispatchLoopCodeSizeStopGuard (depthAwareStop : Bool := false) : String :=
  "  sub x5, x10, x21\n" ++
  "  ld x6, 496(x20)\n" ++
  if depthAwareStop then
    "  bltu x5, x6, 1f\n" ++
    "  la t0, evm_call_depth\n" ++
    "  ld t0, 0(t0)\n" ++
    "  beqz t0, .exit_label\n" ++
    "  la t1, create_frame_flag\n" ++
    "  slli t2, t0, 3\n" ++
    "  add t1, t1, t2\n" ++
    "  ld t3, 0(t1)\n" ++
    "  beqz t3, 2f\n" ++
    "  sd x0, 0(t1)\n" ++
    -- An empty CREATE initcode reaches this EOF halt route rather than the
    -- STOP opcode handler.  Restore the same depth-indexed CREATE metadata
    -- before entering the shared deposit path, otherwise it observes stale
    -- globals instead of this child frame's derived address/value/creator.
    "  la t1, create_address_by_depth; slli t2, t0, 5; add t1, t1, t2\n" ++
    "  la t2, create_address_be; ld t3, 0(t1); sd t3, 0(t2); ld t3, 8(t1); sd t3, 8(t2); ld t3, 16(t1); sd t3, 16(t2); ld t3, 24(t1); sd t3, 24(t2)\n" ++
    "  la t1, create_sender_by_depth; slli t2, t0, 5; add t1, t1, t2\n" ++
    "  la t2, create_sender_be; ld t3, 0(t1); sd t3, 0(t2); ld t3, 8(t1); sd t3, 8(t2); ld t3, 16(t1); sd t3, 16(t2); ld t3, 24(t1); sd t3, 24(t2)\n" ++
    "  la t1, create_value_by_depth; slli t2, t0, 5; add t1, t1, t2\n" ++
    "  la t2, create_value_be; ld t3, 0(t1); sd t3, 0(t2); ld t3, 8(t1); sd t3, 8(t2); ld t3, 16(t1); sd t3, 16(t2); ld t3, 24(t1); sd t3, 24(t2)\n" ++
    "  la t1, create_nonce_by_depth; slli t2, t0, 3; add t1, t1, t2\n" ++
    "  la t2, create_nonce; ld t3, 0(t1); sd t3, 0(t2)\n" ++
    "  li x14, 0\n" ++
    "  li x15, 0\n" ++
    "  j .Lcreate_deposit_from_halt_1\n" ++
    "2:\n" ++
    "  li a0, 1\n" ++
    "  li a1, 0\n" ++
    "  li a2, 0\n" ++
    "  jal ra, frame_return\n" ++
    "  j .dispatch_loop\n" ++
    "1:\n"
  else
    "  bgeu x5, x6, .exit_label\n"

def emitDispatcherPrologue : String :=
  "  la sp, lp64_sp_top\n" ++     -- M16: LP64 stack ptr for ECALL-bridge helpers
                                  -- (e.g. zkvm_keccak256's `addi sp, sp, -32`)
  "  la x10, evm_code\n" ++
  "  la x21, evm_code\n" ++       -- M15: preserved code base (for PC, JUMP, JUMPI)
  "  la x12, evm_stack_top\n" ++
  "  la x5, evm_cur_stack_top; sd x12, 0(x5)\n" ++
  "  la x5, evm_stack_low; la x6, evm_cur_stack_low; sd x5, 0(x6)\n" ++
  "  la x13, evm_memory\n" ++
  "  la x20, evm_env\n" ++
  -- M33: stash the exact running-bytecode length at env+496 for CODESIZE /
  -- CODECOPY. `evm_code_end` is emitted right after the baked bytecode in
  -- the data section, so `evm_code_end - evm_code` is the exact byte count
  -- (x10 still holds `evm_code` from the `la` above; `.balign 32` padding
  -- before `evm_memory` would over-count, hence the dedicated end label).
  "  la x5, evm_code_end\n" ++
  "  sub x5, x5, x10\n" ++         -- x5 = len(code) = evm_code_end - evm_code
  "  sd x5, 496(x20)\n" ++         -- env.codeSize = running bytecode length
  "  sd x0, " ++ toString staticContextFlagOff ++ "(x20)\n" ++ -- env.isStatic = 0
  -- M21: .data-baked variant has no calldata input. Initialize env's
  -- callDataPtrOff (416) to point at a safe zero region (`evm_memory`)
  -- and callDataLenOff (424) to 0. Any CALLDATALOAD reads zeros from
  -- evm_memory (M17 no-op-equivalent); CALLDATASIZE returns 0.
  -- Calldata-requiring tests must use the runtime-bytecode dispatcher
  -- (codegen-opcodes-runtime-check.sh).
  "  la x5, evm_memory\n" ++
  "  sd x5, 416(x20)\n" ++         -- env.callDataPtrOff = &evm_memory (zeros)
  "  sd x0, 424(x20)\n" ++         -- env.callDataLenOff = 0
  -- M24: .data-baked variant has no storage input. Initialize all
  -- three log-state env cells to 0. Persistent + transient logs live
  -- at STATE_TRACKER_AREA (0xa0630000 / 0xa0830000) outside `.data`;
  -- the regions are byte-accessed directly by the storage handlers.
  "  sd x0, 448(x20)\n" ++         -- env.persistentLogLengthOff = 0
  "  sd x0, 456(x20)\n" ++         -- env.persistentLogCheckpointOff = 0
  "  la x5, evm_refund_acc; sd x0, 0(x5)\n" ++   -- bmvmx.1.6.3: reset per-tx refund counter
  "  la x5, evm_selfdestruct_staged; sd x0, 0(x5)\n" ++   -- reset per-tx SELFDESTRUCT execution flag
  "  la x5, evm_selfdestruct_seen_count; sd x0, 0(x5)\n" ++
  "  la x5, evm_selfdestruct_seen_overflow; sd x0, 0(x5)\n" ++
  "  la x5, evm_selfdestruct_destroyed_count; sd x0, 0(x5)\n" ++
  "  la x5, evm_selfdestruct_destroyed_overflow; sd x0, 0(x5)\n" ++
  "  la x5, cd_destroyed_empty_hits; sd x0, 0(x5)\n" ++
  "  la x5, create_nonce_table_count; sd x0, 0(x5)\n" ++   -- .61.8c-1: reset per-creator nonce table per tx
  "  la x5, create_nonce_table_overflow; sd x0, 0(x5)\n" ++
  "  la x5, create_nonce_undo_count; sd x0, 0(x5)\n" ++
  -- The comparator evidence heap is per dispatch in standalone mode, but is
  -- block-lived while the MTx CodeState is active: retained code bytes are the
  -- backing store for cross-transaction execution reads.
  "  la x5, code_state_mtx_active; ld x6, 0(x5); bnez x6, .Lrtd_code_log_kept\n" ++
  "  la x5, exec_code_effect_count; sd x0, 0(x5)\n" ++
  "  la x5, exec_code_effect_next; sd x0, 0(x5)\n" ++
  "  la x5, exec_code_effect_overflow; sd x0, 0(x5)\n" ++
  ".Lrtd_code_log_kept:\n" ++
  "  la x5, account_state_pending_count; sd x0, 0(x5)\n" ++ -- AccountState pending journal is tx scoped
  "  la x5, account_state_created_count; sd x0, 0(x5)\n" ++ -- EIP-6780 created_accounts is tx scoped
  "  la x5, account_state_delete_count; sd x0, 0(x5)\n" ++
  "  la x5, account_state_overflow; sd x0, 0(x5)\n" ++
  "  sd x0, 464(x20)\n" ++         -- env.transientLogLengthOff = 0
  "  sd x0, 472(x20)\n" ++         -- env.eventLogLengthOff = 0
  "  la x5, evm_log_data_used; sd x0, 0(x5)\n" ++       -- 8uld3.1a: reset per-tx full-log-data buffer cursor
  "  la x5, evm_log_data_overflow; sd x0, 0(x5)\n" ++   -- 8uld3.1a: reset per-tx full-log-data overflow flag
  "  sd x0, 480(x20)\n" ++         -- env.eventLogCheckpointOff = 0
  "  sd x0, 488(x20)\n" ++         -- runtime activeMemorySize = 0
  "  sd x0, 512(x20)\n" ++         -- M28: blobBaseFee trailer slot = 0
  "  sd x0, 520(x20)\n" ++
  "  sd x0, 528(x20)\n" ++
  "  sd x0, 536(x20)\n" ++
  "  sd x0, 544(x20)\n" ++         -- M28: blobHashCount = 0
  "  sd x0, 552(x20)\n" ++         -- M29: currentBlockNumber = 0
  "  sd x0, 560(x20)\n" ++         -- M29: blockHashCount = 0
  -- M30: .data-baked variant has no input gas limit; seed a large
  -- constant so the per-opcode gas charge never spuriously runs out.
  "  li x5, 30000000\n" ++
  "  sd x5, 568(x20)\n" ++         -- env.gasRemaining = 30,000,000
  "  sd x0, 624(x20)\n" ++         -- EIP-7843 SLOTNUM word = 0
  "  sd x0, 632(x20)\n" ++
  "  sd x0, 640(x20)\n" ++
  "  sd x0, 648(x20)\n" ++
  "  mv x10, x21\n" ++
  "  la x12, evm_stack_top\n" ++
  "  la x5, evm_cur_stack_top; sd x12, 0(x5)\n" ++
  "  la x5, evm_stack_low; la x6, evm_cur_stack_low; sd x5, 0(x6)\n" ++
  "  la x13, evm_memory\n" ++
  ".dispatch_loop:\n" ++
  emitDispatchLoopCodeSizeStopGuard ++
  "  lbu x5, 0(x10)\n" ++
  "  slli x5, x5, 3\n" ++           -- x5 = opcode * 8 (index for both tables)
  -- M30 gas charge: look up the opcode's static cost, charge it against
  -- env.gasRemaining (env+568), and route to .exit_outofgas if it would
  -- underflow. Charge-then-execute matches the spec's `charge_gas` order
  -- (so e.g. GAS reflects its own cost already deducted). x6/x7 are
  -- per-iteration scratch; x5 (opcode*8) survives for the dispatch below.
  "  la x6, opcode_gas_costs\n" ++
  "  add x6, x6, x5\n" ++
  "  ld x6, 0(x6)\n" ++             -- x6 = static gas cost
  "  ld x7, 568(x20)\n" ++          -- x7 = gas remaining
  "  bltu x7, x6, .exit_outofgas\n" ++
  "  sub x7, x7, x6\n" ++
  "  sd x7, 568(x20)\n" ++          -- gasRemaining -= cost
  "  la x6, opcode_handlers\n" ++
  "  add x6, x6, x5\n" ++
  "  ld x7, 0(x6)\n" ++
  "  jalr x1, x7, 0\n" ++
  emitDispatchResume ++ "\n"

/-- Emit an exceptional-halt exit block: zero the result bytes at
    `OUTPUT[0..32]` (no return data), tag `halt_kind = kind` at
    `OUTPUT + 32`, then `j .exit_no_epilogue` (the universal exit join,
    bypassing `evmAddEpilogue` which would force `halt_kind = 0` and a
    stack-top result). Reached only via `j <label>`.

    `halt_kind` scheme (`OUTPUT + 32`, u64 LE):
    `0` STOP/unspecified · `1` RETURN · `2` REVERT · `3` INVALID (0xfe) ·
    `4` invalid JUMP/JUMPI dest (M15.5) · `5` SELFDESTRUCT (0xff) ·
    `6` out-of-gas · `7` stack underflow · `8` stack overflow. -/
def emitExceptionalExit (label : String) (kind : Nat) : String :=
  s!"{label}:\n" ++
  "  la x18, evm_call_depth\n" ++
  "  ld x18, 0(x18)\n" ++
  s!"  beqz x18, {label}_top\n" ++
  -- Exceptional exits can be reached after an opcode prelude has clobbered caller-saved
  -- registers. Rebuild the child env base from the depth counter before touching env+568;
  -- otherwise a stale x20 can turn the gas-zeroing store into an out-of-RAM write.
  s!"  li x5, {maxCallDepth}\n" ++
  s!"  bgtu x18, x5, {label}_top\n" ++
  -- ⚠️ NO `depth - 1` skew: `frame_base` indexes `call_frame_arena + depth * frameStride`
  -- (depth 0 owns slot 0), so this hand-rolled rebuild must match it.  This block is the
  -- reason a hex grep for the stride misses five sites: it renders `frameStride` and
  -- `frameEnvOff` through `s!` interpolation, i.e. in DECIMAL.  **The spelling-independent
  -- instrument is `la <reg>, call_frame_arena` — every site computing a frame address must
  -- materialise the arena base by symbol.**
  s!"  li x6, {frameStride}\n" ++
  "  mul x5, x18, x6\n" ++
  "  la x20, call_frame_arena\n" ++
  "  add x20, x20, x5\n" ++
  s!"  li x6, {frameEnvOff}\n" ++
  "  add x20, x20, x6\n" ++
  -- Exceptional child halt mirrors execution-specs: refill the child frame's
  -- state gas in LIFO order, but burn the gas-left portion by keeping env+568
  -- zero before frame_return observes it.
  "  ld x5, 632(x20)                 # used0\n" ++
  "  la x6, evm_state_gas_used; ld x7, 0(x6)\n" ++
  "  la x6, evm_state_gas_left; ld x28, 0(x6)\n" ++
  "  la x6, evm_state_gas_spilled; ld x29, 0(x6)\n" ++
  "  ld x30, 760(x20)                # spilled0\n" ++
  "  bleu x29, x30, 1f\n" ++
  "  sub x29, x29, x30\n" ++
  "  j 2f\n" ++
  "1:\n" ++
  "  li x29, 0\n" ++
  "2:\n" ++
  "  bleu x7, x5, 3f\n" ++
  "  sub x7, x7, x5\n" ++
  "  bleu x7, x29, 3f\n" ++
  "  sub x7, x7, x29\n" ++
  "  add x28, x28, x7\n" ++
  "3:\n" ++
  "  la x6, evm_state_gas_left; sd x28, 0(x6)\n" ++
  "  ld x5, 632(x20); la x6, evm_state_gas_used; sd x5, 0(x6)\n" ++
  "  ld x5, 760(x20); la x6, evm_state_gas_spilled; sd x5, 0(x6)\n" ++
  -- generic_create credits NEW_ACCOUNT state gas back on child error ONLY when
  -- it charged it (system.py:157-159 `if new_account_charged:`); an alive
  -- target skipped the conditional charge (v0.6, evm-asm-0w05f.17.2). Save
  -- "CREATE frame AND target not alive" before frame_return pops the depth.
  "  la x5, create_frame_flag; slli x6, x18, 3; add x5, x5, x6; ld x6, 0(x5); sd x0, 0(x5)\n" ++
  "  la x5, create_target_alive_flag; slli x7, x18, 3; add x5, x5, x7; ld x7, 0(x5)\n" ++
  "  beqz x7, 8f\n" ++
  "  li x6, 0\n" ++
  "8:\n" ++
  "  la x5, create_target_alive_current_tx; sd x6, 0(x5)\n" ++
  "  sd x0, 568(x20)\n" ++
  "  li a0, 0\n" ++
  "  li a1, 0\n" ++
  "  li a2, 0\n" ++
  "  jal ra, frame_return\n" ++
  "  la x5, create_target_alive_current_tx; ld x5, 0(x5); beqz x5, 4f\n" ++
  -- execution-specs `credit_state_gas_refund(NEW_ACCOUNT)` refills gas_left
  -- first when the CREATE charge spilled out of the state-gas reservoir.
  "  li x7, 183600\n" ++
  "  la x5, evm_state_gas_spilled; ld x6, 0(x5); li x28, 0\n" ++
  "  beqz x6, 5f\n" ++
  "  mv x28, x6\n" ++
  "  bleu x6, x7, 6f\n" ++
  "  mv x28, x7\n" ++
  "6:\n" ++
  "  sub x6, x6, x28; sd x6, 0(x5)\n" ++
  "  ld x6, 568(x20); add x6, x6, x28; sd x6, 568(x20)\n" ++
  "  sub x7, x7, x28\n" ++
  "5:\n" ++
  "  beqz x7, 7f\n" ++
  "  la x5, evm_state_gas_left; ld x6, 0(x5); add x6, x6, x7; sd x6, 0(x5)\n" ++
  "7:\n" ++
  "  la x5, evm_state_gas_used; ld x6, 0(x5); li x7, 183600; bltu x6, x7, 4f; sub x6, x6, x7; sd x6, 0(x5)\n" ++
  "4:\n" ++
  "  j .dispatch_loop\n" ++
  s!"{label}_top:\n" ++
  "  li x16, 0xa0010000\n" ++       -- OUTPUT_ADDR
  "  sd x0, 0(x16)\n" ++            -- zero-fill result OUTPUT[0..32]
  "  sd x0, 8(x16)\n" ++            -- (exceptional/return-data-free halt,
  "  sd x0, 16(x16)\n" ++           --  surfaced deterministically)
  "  sd x0, 24(x16)\n" ++
  s!"  li x17, {kind}\n" ++         -- halt_kind
  "  sd x17, 32(x16)\n" ++
  "  j .exit_no_epilogue\n"
/-- STATICCALL write violation. At child depth, fail only the child frame and
    resume the parent. At depth 0, surface the same halt kind as INVALID. -/
def emitStaticViolationExit : String :=
  ".exit_static_violation:\n" ++
  "  la t0, evm_call_depth\n" ++
  "  ld t0, 0(t0)\n" ++
  "  beqz t0, .exit_invalid_op\n" ++
  "  sd x0, 568(x20)\n" ++
  "  li a0, 0\n" ++
  "  li a1, 0\n" ++
  "  li a2, 0\n" ++
  "  jal ra, frame_return\n" ++
  "  j .dispatch_loop\n"

/-- SELFDESTRUCT (0xff). Unlike the other exceptional exits, SELFDESTRUCT is a
    SUCCESSFUL frame halt: the EVM stops the current frame, returns empty data to
    the caller, and KEEPS the frame's state effects (its balance transfer / EIP-6780
    deletion already recorded into the non-storage / code effect logs). So at child
    depth (coc3g.6.5) it must `frame_return` with success word a0 = 1 (NOT 0 — a 0
    success word is frame_return's REVERT signal, which truncates the child's recorded
    effects back to the pre-child snapshot, erasing the SELFDESTRUCT deletion +
    beneficiary credit and the child's prior CALL/CREATE effects). The leftover child
    gas (568(x20)) is forwarded by frame_return's EIP-150 refund (SELFDESTRUCT does not
    consume the remaining gas). At depth 0, surface the top-level halt kind 5. -/
def emitSelfdestructExit : String :=
  ".exit_selfdestruct:\n" ++
  "  la x18, evm_call_depth\n" ++
  "  ld x18, 0(x18)\n" ++
  "  beqz x18, .exit_selfdestruct_top\n" ++
  "  li a0, 1\n" ++          -- SUCCESS: keep the child frame's recorded effects
  "  li a1, 0\n" ++
  "  li a2, 0\n" ++
  "  jal ra, frame_return\n" ++
  "  j .dispatch_loop\n" ++
  ".exit_selfdestruct_top:\n" ++
  "  li x16, 0xa0010000\n" ++
  "  sd x0, 0(x16)\n" ++
  "  sd x0, 8(x16)\n" ++
  "  sd x0, 16(x16)\n" ++
  "  sd x0, 24(x16)\n" ++
  "  li x17, 5\n" ++         -- halt_kind = SELFDESTRUCT
  "  sd x17, 32(x16)\n" ++
  "  j .exit_no_epilogue\n"


/-- CREATE/CREATE2 child-frame staging helper emitted into the runtime dispatcher.

This duplicates the standalone probe helper label intentionally: each BuildUnit
links one asm image, and the dispatcher image needs the same callable label for
CREATE/CREATE2 handlers. -/
def createStageInitcodeFrame_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.create_child_status (GuestAddrs.create_stage_initcode_frame + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.create_child_status (GuestAddrs.create_stage_initcode_frame + 0)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.create_child_kind (GuestAddrs.create_stage_initcode_frame + 12)),
    .ADDI .x5 .x5 (laLo GuestAddrs.create_child_kind (GuestAddrs.create_stage_initcode_frame + 12)),
    .SD .x5 .x12 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.create_child_return_len (GuestAddrs.create_stage_initcode_frame + 24)),
    .ADDI .x5 .x5 (laLo GuestAddrs.create_child_return_len (GuestAddrs.create_stage_initcode_frame + 24)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.create_child_code_len (GuestAddrs.create_stage_initcode_frame + 36)),
    .ADDI .x5 .x5 (laLo GuestAddrs.create_child_code_len (GuestAddrs.create_stage_initcode_frame + 36)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.create_init_size (GuestAddrs.create_stage_initcode_frame + 48)),
    .ADDI .x5 .x5 (laLo GuestAddrs.create_init_size (GuestAddrs.create_stage_initcode_frame + 48)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.create_child_init_len (GuestAddrs.create_stage_initcode_frame + 60)),
    .ADDI .x7 .x7 (laLo GuestAddrs.create_child_init_len (GuestAddrs.create_stage_initcode_frame + 60)),
    .SD .x7 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.create_sender_be (GuestAddrs.create_stage_initcode_frame + 72)),
    .ADDI .x5 .x5 (laLo GuestAddrs.create_sender_be (GuestAddrs.create_stage_initcode_frame + 72)),
    .AUIPC .x7 (laHi GuestAddrs.create_child_creator_be (GuestAddrs.create_stage_initcode_frame + 80)),
    .ADDI .x7 .x7 (laLo GuestAddrs.create_child_creator_be (GuestAddrs.create_stage_initcode_frame + 80)),
    .LI .x28 (32 : Word),
    .LBU .x29 .x5 (0 : BitVec 12),
    .SB .x7 .x29 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .BNE .x28 .x0 (-20 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.create_address_be (GuestAddrs.create_stage_initcode_frame + 116)),
    .ADDI .x5 .x5 (laLo GuestAddrs.create_address_be (GuestAddrs.create_stage_initcode_frame + 116)),
    .AUIPC .x7 (laHi GuestAddrs.create_child_target_be (GuestAddrs.create_stage_initcode_frame + 124)),
    .ADDI .x7 .x7 (laLo GuestAddrs.create_child_target_be (GuestAddrs.create_stage_initcode_frame + 124)),
    .LI .x28 (32 : Word),
    .LBU .x29 .x5 (0 : BitVec 12),
    .SB .x7 .x29 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .BNE .x28 .x0 (-20 : BitVec 13),
    .ADDI .x5 .x11 (31 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.create_child_value_be (GuestAddrs.create_stage_initcode_frame + 164)),
    .ADDI .x7 .x7 (laLo GuestAddrs.create_child_value_be (GuestAddrs.create_stage_initcode_frame + 164)),
    .LI .x28 (32 : Word),
    .LBU .x29 .x5 (0 : BitVec 12),
    .SB .x7 .x29 (0 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .BNE .x28 .x0 (-20 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.create_init_offset (GuestAddrs.create_stage_initcode_frame + 200)),
    .ADDI .x5 .x5 (laLo GuestAddrs.create_init_offset (GuestAddrs.create_stage_initcode_frame + 200)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x5 .x10 .x7,
    .AUIPC .x7 (laHi GuestAddrs.create_child_initcode (GuestAddrs.create_stage_initcode_frame + 216)),
    .ADDI .x7 .x7 (laLo GuestAddrs.create_child_initcode (GuestAddrs.create_stage_initcode_frame + 216)),
    .MV .x28 .x6,
    .BEQ .x28 .x0 (28 : BitVec 13),
    .LBU .x29 .x5 (0 : BitVec 12),
    .SB .x7 .x29 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.create_child_status (GuestAddrs.create_stage_initcode_frame + 256)),
    .ADDI .x5 .x5 (laLo GuestAddrs.create_child_status (GuestAddrs.create_stage_initcode_frame + 256)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `createStageInitcodeFrame_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def createStageInitcodeFrame_relocs : RelocTable :=
  [ (0, .la .x5 "create_child_status"),
    (3, .la .x5 "create_child_kind"),
    (6, .la .x5 "create_child_return_len"),
    (9, .la .x5 "create_child_code_len"),
    (12, .la .x5 "create_init_size"),
    (15, .la .x7 "create_child_init_len"),
    (18, .la .x5 "create_sender_be"),
    (20, .la .x7 "create_child_creator_be"),
    (29, .la .x5 "create_address_be"),
    (31, .la .x7 "create_child_target_be"),
    (41, .la .x7 "create_child_value_be"),
    (50, .la .x5 "create_init_offset"),
    (54, .la .x7 "create_child_initcode"),
    (64, .la .x5 "create_child_status") ]

def createStageInitcodeFrameRuntimeFunction : String :=
  "create_stage_initcode_frame:\n" ++ emitProgramR createStageInitcodeFrame_prog createStageInitcodeFrame_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `createStageInitcodeFrame_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem createStageInitcodeFrameRuntimeFunction_eq_prog :
    createStageInitcodeFrameRuntimeFunction = "create_stage_initcode_frame:\n" ++ emitProgramR createStageInitcodeFrame_prog createStageInitcodeFrame_relocs := rfl

#guard createStageInitcodeFrameRuntimeFunction.startsWith "create_stage_initcode_frame:\n"
#guard createStageInitcodeFrame_prog.length = 70
/-- Bounded CREATE initcode executor over the staged child-frame arena.

Supported in this first executable slice: STOP, RETURN, REVERT, INVALID,
PUSH0/PUSH1..PUSH32 with u64 values, MSTORE, and MSTORE8. All other opcodes
fail deterministically. Result status uses the child-frame status word:
  2 deployed, 3 reverted, 4 failed/unsupported, 5 bounded-step exhaustion. -/
def createExecuteInitcodeFrame_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.create_child_status (GuestAddrs.create_execute_initcode_frame + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.create_child_status (GuestAddrs.create_execute_initcode_frame + 0)),
    .LI .x6 (4 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.create_child_return_len (GuestAddrs.create_execute_initcode_frame + 16)),
    .ADDI .x5 .x5 (laLo GuestAddrs.create_child_return_len (GuestAddrs.create_execute_initcode_frame + 16)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.create_child_code_len (GuestAddrs.create_execute_initcode_frame + 28)),
    .ADDI .x5 .x5 (laLo GuestAddrs.create_child_code_len (GuestAddrs.create_execute_initcode_frame + 28)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.create_child_returndata (GuestAddrs.create_execute_initcode_frame + 40)),
    .ADDI .x5 .x5 (laLo GuestAddrs.create_child_returndata (GuestAddrs.create_execute_initcode_frame + 40)),
    .AUIPC .x6 (laHi GuestAddrs.create_child_code (GuestAddrs.create_execute_initcode_frame + 48)),
    .ADDI .x6 .x6 (laLo GuestAddrs.create_child_code (GuestAddrs.create_execute_initcode_frame + 48)),
    .LI .x7 (256 : Word),
    .SB .x5 .x0 (0 : BitVec 12),
    .SB .x6 .x0 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-20 : BitVec 13),
    .LI .x5 (0 : Word),
    .AUIPC .x7 (laHi GuestAddrs.create_child_initcode (GuestAddrs.create_execute_initcode_frame + 88)),
    .ADDI .x7 .x7 (laLo GuestAddrs.create_child_initcode (GuestAddrs.create_execute_initcode_frame + 88)),
    .AUIPC .x28 (laHi GuestAddrs.create_child_stack (GuestAddrs.create_execute_initcode_frame + 96)),
    .ADDI .x28 .x28 (laLo GuestAddrs.create_child_stack (GuestAddrs.create_execute_initcode_frame + 96)),
    .LI .x29 (0 : Word),
    .LI .x30 (1024 : Word),
    .AUIPC .x6 (laHi GuestAddrs.create_child_init_len (GuestAddrs.create_execute_initcode_frame + 112)),
    .ADDI .x6 .x6 (laLo GuestAddrs.create_child_init_len (GuestAddrs.create_execute_initcode_frame + 112)),
    .LD .x6 .x6 (0 : BitVec 12),
    .BEQ .x30 .x0 (600 : BitVec 13),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .BGEU .x5 .x6 (532 : BitVec 13),
    .ADD .x10 .x7 .x5,
    .LBU .x31 .x10 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .BEQ .x31 .x0 (516 : BitVec 13),
    .LI .x10 (243 : Word),
    .BEQ .x31 .x10 (344 : BitVec 13),
    .LI .x10 (253 : Word),
    .BEQ .x31 .x10 (360 : BitVec 13),
    .LI .x10 (254 : Word),
    .BEQ .x31 .x10 (576 : BitVec 13),
    .LI .x10 (82 : Word),
    .BEQ .x31 .x10 (144 : BitVec 13),
    .LI .x10 (83 : Word),
    .BEQ .x31 .x10 (244 : BitVec 13),
    .LI .x10 (95 : Word),
    .BEQ .x31 .x10 (24 : BitVec 13),
    .LI .x10 (96 : Word),
    .BLTU .x31 .x10 (544 : BitVec 13),
    .LI .x10 (128 : Word),
    .BGEU .x31 .x10 (536 : BitVec 13),
    .JAL .x0 (12 : BitVec 21),
    .LI .x11 (0 : Word),
    .JAL .x0 (72 : BitVec 21),
    .ADDI .x12 .x31 (-95 : BitVec 12),
    .ADD .x13 .x5 .x12,
    .BLTU .x6 .x13 (512 : BitVec 13),
    .LI .x11 (0 : Word),
    .BEQ .x12 .x0 (52 : BitVec 13),
    .ADD .x13 .x7 .x5,
    .LBU .x14 .x13 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .LI .x13 (8 : Word),
    .BLTU .x13 .x12 (20 : BitVec 13),
    .SLLI .x11 .x11 (8 : BitVec 6),
    .OR .x11 .x11 .x14,
    .ADDI .x12 .x12 (-1 : BitVec 12),
    .JAL .x0 (-36 : BitVec 21),
    .BNE .x14 .x0 (464 : BitVec 13),
    .ADDI .x12 .x12 (-1 : BitVec 12),
    .JAL .x0 (-48 : BitVec 21),
    .LI .x10 (16 : Word),
    .BGEU .x29 .x10 (448 : BitVec 13),
    .SLLI .x10 .x29 (3 : BitVec 6),
    .ADD .x10 .x28 .x10,
    .SD .x10 .x11 (0 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .JAL .x0 (-196 : BitVec 21),
    .LI .x10 (2 : Word),
    .BLTU .x29 .x10 (420 : BitVec 13),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .SLLI .x10 .x29 (3 : BitVec 6),
    .ADD .x10 .x28 .x10,
    .LD .x11 .x10 (0 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .SLLI .x10 .x29 (3 : BitVec 6),
    .ADD .x10 .x28 .x10,
    .LD .x12 .x10 (0 : BitVec 12),
    .LI .x10 (224 : Word),
    .BLTU .x10 .x11 (380 : BitVec 13),
    .AUIPC .x13 (laHi GuestAddrs.create_child_returndata (GuestAddrs.create_execute_initcode_frame + 372)),
    .ADDI .x13 .x13 (laLo GuestAddrs.create_child_returndata (GuestAddrs.create_execute_initcode_frame + 372)),
    .ADD .x13 .x13 .x11,
    .LI .x14 (24 : Word),
    .SB .x13 .x0 (0 : BitVec 12),
    .ADDI .x13 .x13 (1 : BitVec 12),
    .ADDI .x14 .x14 (-1 : BitVec 12),
    .BNE .x14 .x0 (-12 : BitVec 13),
    .LI .x14 (56 : Word),
    .SRL .x15 .x12 .x14,
    .SB .x13 .x15 (0 : BitVec 12),
    .ADDI .x13 .x13 (1 : BitVec 12),
    .ADDI .x14 .x14 (-8 : BitVec 12),
    .BGE .x14 .x0 (-16 : BitVec 13),
    .JAL .x0 (-304 : BitVec 21),
    .LI .x10 (2 : Word),
    .BLTU .x29 .x10 (312 : BitVec 13),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .SLLI .x10 .x29 (3 : BitVec 6),
    .ADD .x10 .x28 .x10,
    .LD .x11 .x10 (0 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .SLLI .x10 .x29 (3 : BitVec 6),
    .ADD .x10 .x28 .x10,
    .LD .x12 .x10 (0 : BitVec 12),
    .LI .x10 (255 : Word),
    .BLTU .x10 .x11 (272 : BitVec 13),
    .AUIPC .x13 (laHi GuestAddrs.create_child_returndata (GuestAddrs.create_execute_initcode_frame + 480)),
    .ADDI .x13 .x13 (laLo GuestAddrs.create_child_returndata (GuestAddrs.create_execute_initcode_frame + 480)),
    .ADD .x13 .x13 .x11,
    .SB .x13 .x12 (0 : BitVec 12),
    .JAL .x0 (-372 : BitVec 21),
    .LI .x16 (2 : Word),
    .AUIPC .x17 (laHi GuestAddrs.create_child_code_len (GuestAddrs.create_execute_initcode_frame + 504)),
    .ADDI .x17 .x17 (laLo GuestAddrs.create_child_code_len (GuestAddrs.create_execute_initcode_frame + 504)),
    .AUIPC .x15 (laHi GuestAddrs.create_child_code (GuestAddrs.create_execute_initcode_frame + 512)),
    .ADDI .x15 .x15 (laLo GuestAddrs.create_child_code (GuestAddrs.create_execute_initcode_frame + 512)),
    .JAL .x0 (28 : BitVec 21),
    .LI .x16 (3 : Word),
    .AUIPC .x17 (laHi GuestAddrs.create_child_return_len (GuestAddrs.create_execute_initcode_frame + 528)),
    .ADDI .x17 .x17 (laLo GuestAddrs.create_child_return_len (GuestAddrs.create_execute_initcode_frame + 528)),
    .AUIPC .x15 (laHi GuestAddrs.create_child_returndata (GuestAddrs.create_execute_initcode_frame + 536)),
    .ADDI .x15 .x15 (laLo GuestAddrs.create_child_returndata (GuestAddrs.create_execute_initcode_frame + 536)),
    .JAL .x0 (4 : BitVec 21),
    .LI .x10 (2 : Word),
    .BLTU .x29 .x10 (196 : BitVec 13),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .SLLI .x10 .x29 (3 : BitVec 6),
    .ADD .x10 .x28 .x10,
    .LD .x11 .x10 (0 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .SLLI .x10 .x29 (3 : BitVec 6),
    .ADD .x10 .x28 .x10,
    .LD .x12 .x10 (0 : BitVec 12),
    .LI .x10 (256 : Word),
    .BLTU .x10 .x12 (156 : BitVec 13),
    .ADD .x10 .x11 .x12,
    .BLTU .x10 .x11 (148 : BitVec 13),
    .LI .x13 (256 : Word),
    .BLTU .x13 .x10 (140 : BitVec 13),
    .SD .x17 .x12 (0 : BitVec 12),
    .BEQ .x12 .x0 (52 : BitVec 13),
    .AUIPC .x13 (laHi GuestAddrs.create_child_returndata (GuestAddrs.create_execute_initcode_frame + 620)),
    .ADDI .x13 .x13 (laLo GuestAddrs.create_child_returndata (GuestAddrs.create_execute_initcode_frame + 620)),
    .ADD .x13 .x13 .x11,
    .MV .x14 .x12,
    .LBU .x10 .x13 (0 : BitVec 12),
    .SB .x15 .x10 (0 : BitVec 12),
    .ADDI .x13 .x13 (1 : BitVec 12),
    .ADDI .x15 .x15 (1 : BitVec 12),
    .ADDI .x14 .x14 (-1 : BitVec 12),
    .BNE .x14 .x0 (-20 : BitVec 13),
    .JAL .x0 (8 : BitVec 21),
    .LI .x16 (2 : Word),
    .LI .x10 (2 : Word),
    .BNE .x16 .x10 (32 : BitVec 13),
    .AUIPC .x11 (laHi GuestAddrs.create_child_returndata (GuestAddrs.create_execute_initcode_frame + 676)),
    .ADDI .x11 .x11 (laLo GuestAddrs.create_child_returndata (GuestAddrs.create_execute_initcode_frame + 676)),
    .LI .x12 (256 : Word),
    .SB .x11 .x0 (0 : BitVec 12),
    .ADDI .x11 .x11 (1 : BitVec 12),
    .ADDI .x12 .x12 (-1 : BitVec 12),
    .BNE .x12 .x0 (-12 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.create_child_status (GuestAddrs.create_execute_initcode_frame + 704)),
    .ADDI .x10 .x10 (laLo GuestAddrs.create_child_status (GuestAddrs.create_execute_initcode_frame + 704)),
    .SD .x10 .x16 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.create_child_status (GuestAddrs.create_execute_initcode_frame + 724)),
    .ADDI .x10 .x10 (laLo GuestAddrs.create_child_status (GuestAddrs.create_execute_initcode_frame + 724)),
    .LI .x11 (5 : Word),
    .SD .x10 .x11 (0 : BitVec 12),
    .LI .x10 (5 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.create_child_status (GuestAddrs.create_execute_initcode_frame + 748)),
    .ADDI .x10 .x10 (laLo GuestAddrs.create_child_status (GuestAddrs.create_execute_initcode_frame + 748)),
    .LI .x11 (4 : Word),
    .SD .x10 .x11 (0 : BitVec 12),
    .LI .x10 (4 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `createExecuteInitcodeFrame_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def createExecuteInitcodeFrame_relocs : RelocTable :=
  [ (0, .la .x5 "create_child_status"),
    (4, .la .x5 "create_child_return_len"),
    (7, .la .x5 "create_child_code_len"),
    (10, .la .x5 "create_child_returndata"),
    (12, .la .x6 "create_child_code"),
    (22, .la .x7 "create_child_initcode"),
    (24, .la .x28 "create_child_stack"),
    (28, .la .x6 "create_child_init_len"),
    (93, .la .x13 "create_child_returndata"),
    (120, .la .x13 "create_child_returndata"),
    (126, .la .x17 "create_child_code_len"),
    (128, .la .x15 "create_child_code"),
    (132, .la .x17 "create_child_return_len"),
    (134, .la .x15 "create_child_returndata"),
    (155, .la .x13 "create_child_returndata"),
    (169, .la .x11 "create_child_returndata"),
    (176, .la .x10 "create_child_status"),
    (181, .la .x10 "create_child_status"),
    (187, .la .x10 "create_child_status") ]

def createExecuteInitcodeFrameRuntimeFunction : String :=
  "create_execute_initcode_frame:\n" ++ emitProgramR createExecuteInitcodeFrame_prog createExecuteInitcodeFrame_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `createExecuteInitcodeFrame_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem createExecuteInitcodeFrameRuntimeFunction_eq_prog :
    createExecuteInitcodeFrameRuntimeFunction = "create_execute_initcode_frame:\n" ++ emitProgramR createExecuteInitcodeFrame_prog createExecuteInitcodeFrame_relocs := rfl

#guard createExecuteInitcodeFrameRuntimeFunction.startsWith "create_execute_initcode_frame:\n"
#guard createExecuteInitcodeFrame_prog.length = 193
/-- Post-dispatch per-transaction gas settlement fold (nxio8 / EIP-8037).

    The spec's transaction settlement is
    `tx_gas_used_before_refund = tx.gas - gas_left - state_gas_left`
    (fork.py process_transaction), with two tx-level error rules:
    on ANY error (REVERT or exceptional halt) `state_gas_left += state_gas_used`
    (no state was grown, so the full state-gas charge — including any portion
    spilled into gas_left — is restored), and the refund counter is discarded
    (interpreter.py only incorporates `evm.refund_counter` when `error is None`);
    an exceptional halt additionally burns all remaining regular gas
    (interpreter.py: `evm.gas_left = Uint(0)`), which the dispatcher's
    `.exit_*` paths do NOT apply to env+568.

    This helper folds all three rules into the values the gas-result consumers
    (`tx_gas_result_increments`, the bvgr arena) expect:
      a0 (output) = effective gas_left  = gas_left' + state_gas_left'
                    where gas_left' = 0 for exceptional halts, env+568 otherwise,
                    and state_gas_left' includes the on-error restore;
      a1 (output) = effective refund_counter = evm_refund_acc, or 0 on error;
      a2 (output) = tx success bit (1 when halt_kind is 0 STOP / 1 RETURN /
                    5 SELFDESTRUCT; 0 on REVERT or an exceptional halt) — the
                    receipt `succeeded` field (.63.1.6.2.1).
    halt_kind is read from OUTPUT+32 (set by every halt path): 0 STOP / 1 RETURN /
    5 SELFDESTRUCT are successes; 2 REVERT keeps gas_left but folds state gas and
    drops refunds; 3/4/6/7/8 are exceptional. Clobbers t0-t3. Read-only
    (callable repeatedly; mutates no dispatcher state). -/
/- Preserve executed state gas for successful halts (including the deposit STOP
   lane), but do not publish reverted/exceptional frame charges as
   `tx_output.state_gas_used`.  The tx-level intrinsic state gas already
   accounts for authorization charges; on an error the frame portion is
   refilled by the settlement fold and must be captured as 0. -/
def dispatcherTxGasSettle_prog : Program :=
  [ .LUI .x5 (10 : BitVec 20),
    .ADDIW .x5 .x5 (1 : BitVec 12),
    .SLLI .x5 .x5 (16 : BitVec 6),
    .LD .x6 .x5 (32 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.evm_env (GuestAddrs.dispatcher_tx_gas_settle + 16)),
    .ADDI .x5 .x5 (laLo GuestAddrs.evm_env (GuestAddrs.dispatcher_tx_gas_settle + 16)),
    .LD .x5 .x5 (568 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.evm_state_gas_left (GuestAddrs.dispatcher_tx_gas_settle + 28)),
    .ADDI .x7 .x7 (laLo GuestAddrs.evm_state_gas_left (GuestAddrs.dispatcher_tx_gas_settle + 28)),
    .LD .x7 .x7 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.evm_refund_acc (GuestAddrs.dispatcher_tx_gas_settle + 40)),
    .ADDI .x28 .x28 (laLo GuestAddrs.evm_refund_acc (GuestAddrs.dispatcher_tx_gas_settle + 40)),
    .LD .x11 .x28 (0 : BitVec 12),
    .LI .x12 (1 : Word),
    .BEQ .x6 .x0 (100 : BitVec 13),
    .LI .x28 (1 : Word),
    .BEQ .x6 .x28 (92 : BitVec 13),
    .LI .x28 (5 : Word),
    .BEQ .x6 .x28 (84 : BitVec 13),
    .LI .x11 (0 : Word),
    .LI .x12 (0 : Word),
    .AUIPC .x30 (laHi GuestAddrs.evm_state_gas_used (GuestAddrs.dispatcher_tx_gas_settle + 84)),
    .ADDI .x30 .x30 (laLo GuestAddrs.evm_state_gas_used (GuestAddrs.dispatcher_tx_gas_settle + 84)),
    .LD .x28 .x30 (0 : BitVec 12),
    .AUIPC .x31 (laHi GuestAddrs.evm_state_gas_spilled (GuestAddrs.dispatcher_tx_gas_settle + 96)),
    .ADDI .x31 .x31 (laLo GuestAddrs.evm_state_gas_spilled (GuestAddrs.dispatcher_tx_gas_settle + 96)),
    .LD .x29 .x31 (0 : BitVec 12),
    .BNE .x12 .x0 (8 : BitVec 13),
    .SD .x30 .x0 (0 : BitVec 12),
    .SD .x31 .x0 (0 : BitVec 12),
    .BGEU .x29 .x28 (16 : BitVec 13),
    .SUB .x28 .x28 .x29,
    .ADD .x7 .x7 .x28,
    .JAL .x0 (4 : BitVec 21),
    .LI .x28 (2 : Word),
    .BNE .x6 .x28 (12 : BitVec 13),
    .ADD .x5 .x5 .x29,
    .JAL .x0 (8 : BitVec 21),
    .LI .x5 (0 : Word),
    .ADD .x10 .x5 .x7,
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `dispatcherTxGasSettle_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def dispatcherTxGasSettle_relocs : RelocTable :=
  [ (4, .la .x5 "evm_env"),
    (7, .la .x7 "evm_state_gas_left"),
    (10, .la .x28 "evm_refund_acc"),
    (21, .la .x30 "evm_state_gas_used"),
    (24, .la .x31 "evm_state_gas_spilled") ]

def dispatcherTxGasSettleFunction : String :=
  "dispatcher_tx_gas_settle:\n" ++ emitProgramR dispatcherTxGasSettle_prog dispatcherTxGasSettle_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `dispatcherTxGasSettle_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem dispatcherTxGasSettleFunction_eq_prog :
    dispatcherTxGasSettleFunction = "dispatcher_tx_gas_settle:\n" ++ emitProgramR dispatcherTxGasSettle_prog dispatcherTxGasSettle_relocs := rfl

#guard dispatcherTxGasSettleFunction.startsWith "dispatcher_tx_gas_settle:\n"
#guard dispatcherTxGasSettle_prog.length = 41
/-- Dispatcher epilogue: handler subroutines (each ends with `ret` or
    `j .exit_label`), the `h_invalid` fallback, and `.exit_label`
    which runs `exitBody` (e.g. `evmAddEpilogue`) and falls through
    to the halt stub appended by `emitBuildUnit`.

    **M23 addition**: the `.exit_no_epilogue` label is emitted
    *after* `exitBody` and *before* the halt stub. Handlers that
    surface their own output bytes to `OUTPUT_ADDR` (e.g. real
    RETURN / REVERT) jump there to skip the default exit body
    (which would otherwise clobber their writes with the EVM
    stack-top copy). STOP and the other halts continue to flow
    through `.exit_label` → `exitBody` → halt stub. -/
def emitDispatcherEpilogueCore
    (registry : List OpcodeHandlerSpec) (exitBody : Program)
    (afterDiagnostics : String) (includeSharedHelpers : Bool := true)
    (skipExitFinalization : Bool := false) : String :=
  String.intercalate "\n" (registry.map OpcodeHandlerSpec.emitSubroutine) ++ "\n" ++
  (if includeSharedHelpers then
    -- M16/M27: hash subroutines sit BETWEEN the handler subroutines
    -- and the `h_invalid:` / `.exit_label:` blocks so it's reachable only
    -- via explicit `jal`s (not by fall-through from exitBody).
    -- Each handler subroutine ends with `ret` / `j .dispatch_loop`, so
    -- they don't fall through into these labels. The subroutines end
    -- with `ret`, returning to whoever JAL'd them.
    zkvmSha256Function ++ "\n" ++
    -- Real RIPEMD160 (0x03) software kernel (no ZisK accelerator exists
    -- for RIPEMD-160; see Programs/Ripemd160.lean).
    zkvmRipemd160Function ++ "\n" ++
    zkvmKeccak256Function ++ "\n" ++
    witnessLookupByHashFunction ++ "\n" ++
    rlpListNthItemFunction ++ "\n" ++
    mptNodeKindFunction ++ "\n" ++
    mptBranchChildFunction ++ "\n" ++
    hpDecodeNibblesFunction ++ "\n" ++
    bytesToNibblesFunction ++ "\n" ++
    mptWalkFunction ++ "\n" ++
    mptLookupByKeyFunction ++ "\n" ++
    rlpFieldToU256BeFunction ++ "\n" ++
    rlpEncodeBytesFunction ++ "\n" ++
    rlpEncodeUintBeFunction ++ "\n" ++
    rlpEncodeListPrefixFunction ++ "\n" ++
    rlpItemSizeFunction ++ "\n" ++
    rlpItemSpanFunction ++ "\n" ++
    -- Cursor-walk RLP primitives (single-pass decode; used by the tx/header
    -- decoders in the verdict pipeline). Peer to the index-based primitives
    -- above; linked here so every dispatcher-based ELF that transitively
    -- includes a cursor-walk decoder resolves these symbols.
    rlpWalkInitFunction ++ "\n" ++
    rlpWalkNextFunction ++ "\n" ++
    rlpContentToU64Function ++ "\n" ++
    rlpContentToU256BeFunction ++ "\n" ++
    msetMemcpyFunction ++ "\n" ++
    mptSpliceSlotFunction ++ "\n" ++
    accountDecodeFunction ++ "\n" ++
    accountAtAddressFunction ++ "\n" ++
    accountExtractBalanceFunction ++ "\n" ++
    accountAddBalanceFunction ++ "\n" ++
    accountSetUintFieldFunction ++ "\n" ++
    selfdestructBalanceTransferFunction ++ "\n" ++
    headerExtractStateRootFunction ++ "\n" ++
    balanceAtHeaderStateRootFunction ++ "\n" ++
    nonceAtHeaderStateRootFunction ++ "\n" ++
    accountExistsAtHeaderStateRootFunction ++ "\n" ++
    accountIsEmptyAtHeaderStateRootFunction ++ "\n" ++
    extcodehashAtHeaderStateRootFunction ++ "\n" ++
    extcodesizeAtHeaderStateRootFunction ++ "\n" ++
    extcodecopyAtHeaderStateRootFunction ++ "\n" ++
    runtimeSameBlockDelegationCodeFunction ++ "\n" ++
    hasCodeOrNonceAtHeaderStateRootFunction ++ "\n" ++
    addressComputeCreateFunction ++ "\n" ++
    addressComputeCreate2Function ++ "\n" ++
    createStageInitcodeFrameRuntimeFunction ++ "\n" ++
    createExecuteInitcodeFrameRuntimeFunction ++ "\n" ++
    createDeployedCodeValidFunction ++ "\n" ++
    createRecordCodeEffectFunction ++ "\n" ++
    findCodeEffectByAddressFunction ++ "\n" ++
    accountStateFindFunction ++ "\n" ++
    accountStateCopyFunction ++ "\n" ++
    accountStateAppendPendingFunction ++ "\n" ++
    accountStateUpsertDurableFunction ++ "\n" ++
    codeStateFinalBalanceNonzeroFunction ++ "\n" ++
    accountStateCommitPendingFunction ++ "\n" ++
    accountStatePromoteDeleteReadsFunction ++ "\n" ++
    accountStateRecordNonstorageFunction ++ "\n" ++
    accountStateRecordCodeFunction ++ "\n" ++
    accountStateRecordAuthFunction ++ "\n" ++
    accountStatePublishSenderInclusionFunction ++ "\n" ++
    accountStateAuthCurrentFunction ++ "\n" ++
    accountStateLatestBalanceFunction ++ "\n" ++
    accountStateLatestNonceFunction ++ "\n" ++
    accountStateLookupCurrentFunction ++ "\n" ++
    accountStateCreatedContainsFunction ++ "\n" ++
    codeStateLookupCurrentFunction ++ "\n" ++
    codeStateAddressSetInsertFunction ++ "\n" ++
    codeStateAddressSetFlagFunction ++ "\n" ++
    createCreatorNonceUseFunction ++ "\n" ++
    zkvmModexpBackendImpl ++ "\n" ++
    emitModexpBnScratchData ++ "\n" ++
    ".section .text\n" ++ "\n" ++
    storageAccessGasFunction ++ "\n" ++
    sstoreGasRefundOutcomeFunction ++ "\n" ++
    dispatcherTxGasSettleFunction ++ "\n" ++
    runtimeAccessAccountSeedFunction ++ "\n" ++
    runtimeAccessSeedInitialAccountsFunction ++ "\n" ++
    runtimeAccessAccountChargeFunction ++ "\n" ++
    eip7708SyntheticLogFunctions ++ "\n" ++
    -- Real BLS12-381 G1 ADD/MSM (0x0b/0x0c) kernels backed by the ziskemu
    -- Bls12_381CurveAdd/Dbl + Arith384Mod accelerators (EIP-2537 decode,
    -- on-curve + order-n subgroup checks; Programs/Bls12G1.lean).
    bls12G1PrecompileFunctions ++ "\n" ++
    -- Real BN254 precompile kernels: ecAdd/ecMul (0x06/0x07) field/curve
    -- helpers + `zkvm_bn254_g1_add` / `zkvm_bn254_g1_mul` backed by the
    -- ziskemu Bn254CurveAdd/Dbl + Arith256Mod accelerators, and the
    -- ecPairing (0x08) `zkvm_bn254_pairing` kernel (py_ecc-mirroring
    -- FQ12 Miller loop + final exponentiation, Bn254Complex* + Arith256Mod
    -- accelerated).
    bn254PrecompileFunctions ++ "\n" ++
    bn254PairingKernelFunctions ++ "\n" ++
    -- Real BLAKE2F (0x09) kernel backed by the ziskemu Blake2bRound
    -- accelerator (Programs/Blake2f.lean).
    blake2fKernelFunctions ++ "\n" ++
    -- Real KZG point-evaluation (0x0a) kernel: compressed-G1 decode +
    -- [tau]_2 pairing check on top of the BLS12-381 suites
    -- (Programs/Bls12Kzg.lean).
    bls12KzgKernelFunctions ++ "\n" ++
    -- Real P256VERIFY (0x100) kernel: software P-256 ECDSA over the
    -- Arith256Mod accelerator (Programs/P256Verify.lean).
    p256VerifyKernelFunctions ++ "\n" ++
    -- Real BLS12-381 G2 ADD/MSM (0x0d/0x0e) kernels: software Fp2
    -- chord/tangent over the complex accelerators + Arith384Mod Fermat
    -- inverse (Programs/Bls12G2.lean; blsf_copy_quads linked alongside).
    bls12G2PrecompileFunctions ++ "\n" ++
    -- Real BLS12-381 pairing (0x0f) kernel: py_ecc-mirroring FQ12
    -- Miller loop on Arith384Mod (Programs/Bls12Fq12 + Bls12Pairing).
    bls12PairingKernelFunctions ++ "\n" ++
    -- Real BLS12-381 map precompiles (0x10/0x11): SSWU + isogeny +
    -- accelerated cofactor clearing (Programs/Bls12Map.lean).
    bls12MapKernelFunctions ++ "\n"
   else
    "") ++
  "h_invalid:\n" ++
  "  j .exit_invalid_op\n" ++
  -- Exceptional-halt exits (reached only via `j <label>`; each ends with
  -- `j .exit_no_epilogue` so none fall through into exitBody). Unknown opcode
  -- bytes route through h_invalid into .exit_invalid_op, which is depth-aware:
  -- a child frame returns CALL failure, while depth 0 marks the tx exceptional. Each
  -- zero-fills the result and tags a distinct halt_kind so callers can
  -- tell STOP / RETURN / REVERT / INVALID / invalid-jump / SELFDESTRUCT
  -- apart at OUTPUT + 32.
  --   .exit_invalid     (4) — M15.5 invalid JUMP/JUMPI dest
  --                            (`jumpValidityTail`'s `bne … .exit_invalid`)
  --   .exit_invalid_op  (3) — M23.5 INVALID opcode (0xfe)
  --   .exit_selfdestruct(5) — M23.5 SELFDESTRUCT (0xff)
  --   .exit_outofgas    (6) — M30 dispatch-loop gas underflow
  --   .exit_stack_underflow(7) — stack consumer with too few words
  --   .exit_stack_overflow(8) — PUSH beyond the 1024-word EVM stack limit
  emitStaticViolationExit ++
  emitExceptionalExit ".exit_invalid" 4 ++
  emitExceptionalExit ".exit_invalid_op" 3 ++
  emitSelfdestructExit ++
  emitExceptionalExit ".exit_outofgas" 6 ++
  emitExceptionalExit ".exit_stack_underflow" 7 ++
  emitExceptionalExit ".exit_stack_overflow" 8 ++
  ".exit_label:\n" ++
  -- L2 (bmvmx.1.2.4.6.1): the block-verdict-callable epilogue runs without a
  -- state tracker (x20) or a live OUTPUT region for the EVM result -- env gas
  -- is captured from evm_env+568 in setup. Skip exitBody + the OUTPUT@0xa0010000
  -- log/slot/event/selfdestruct finalization (which derefs x20 and clobbers the
  -- verdict OUTPUT) and go straight to the caller-return. The .exit_label /
  -- .exit_no_epilogue labels stay defined so exceptional-exit `j`s still resolve.
  (if skipExitFinalization then "" else emitProgram exitBody) ++ "\n" ++
  ".exit_no_epilogue:\n" ++
  (if skipExitFinalization then "" else
  -- M24: surface final log lengths at OUTPUT_ADDR + 40 / + 48.
  -- This runs for EVERY halt path: STOP / RETURN / REVERT /
  -- INVALID / SELFDESTRUCT. REVERT's body has already restored
  -- the persistent log length to the checkpoint (and zeroed the
  -- transient length) by the time we get here, so the surfaced
  -- values reflect the post-rollback state for reverted txs and
  -- the live committed state for successful ones.
  "  li x16, 0xa0010000\n" ++       -- x16 = OUTPUT_ADDR
  "  ld x17, 448(x20)\n" ++         -- persistent log length
  "  sd x17, 40(x16)\n" ++          -- OUTPUT[40..48]
  "  ld x17, 464(x20)\n" ++         -- transient log length
  "  sd x17, 48(x16)\n" ++          -- OUTPUT[48..56]
  -- M25: dedup-and-emit modified persistent slots at OUTPUT+56..
  -- Walks the persistent log from end (last-write-wins); for each
  -- entry, checks if its slotKey has already been emitted at
  -- OUTPUT[64..64+count*64]; if not, emits (slotKey, current) and
  -- bumps the count cell at OUTPUT+56. Capped at 3 entries (192 B
  -- of slot data fits in the 200-byte slack after byte 56).
  -- All halt paths (STOP / RETURN / REVERT / INVALID / SELFDESTRUCT)
  -- run this; REVERT has already truncated the log to the checkpoint,
  -- so the surfaced slots reflect the post-rollback state.
  "  ld x15, 448(x20)\n" ++         -- x15 = persistent log_length
  "  li x17, 0\n" ++                -- x17 = emitted count
  "  sd x17, 56(x16)\n" ++          -- init OUTPUT+56 = 0
  "  beqz x15, 4f\n" ++             -- empty log → done
  "  li x14, 0xa0630000\n" ++       -- x14 = log base
  "  slli x18, x15, 7\n" ++         -- x18 = log_length * 128
  "  add x14, x14, x18\n" ++        -- x14 = past last entry
  "1:\n" ++                         -- scan iter (work backward)
  "  addi x14, x14, -128\n" ++      -- x14 = current entry
  -- Dedup: scan output[OUTPUT+64 .. OUTPUT+64+x17*64] for slotKey
  "  li x18, 0xa0010040\n" ++       -- x18 = OUTPUT + 64
  "  mv x19, x17\n" ++              -- x19 = emitted count to check
  "2:\n" ++                         -- dedup loop
  "  beqz x19, 3f\n" ++             -- exhausted → not duplicate, emit
  "  ld x21, 0(x18)\n" ++
  "  ld x22, 32(x14)\n" ++
  "  bne x21, x22, 5f\n" ++
  "  ld x21, 8(x18)\n" ++
  "  ld x22, 40(x14)\n" ++
  "  bne x21, x22, 5f\n" ++
  "  ld x21, 16(x18)\n" ++
  "  ld x22, 48(x14)\n" ++
  "  bne x21, x22, 5f\n" ++
  "  ld x21, 24(x18)\n" ++
  "  ld x22, 56(x14)\n" ++
  "  bne x21, x22, 5f\n" ++
  "  j 6f\n" ++                     -- match → already emitted, skip
  "5:\n" ++                         -- not match this output entry
  "  addi x18, x18, 64\n" ++
  "  addi x19, x19, -1\n" ++
  "  j 2b\n" ++
  "3:\n" ++                         -- emit (slotKey, current)
  "  li x19, 3\n" ++
  "  bgeu x17, x19, 4f\n" ++        -- cap reached
  "  slli x18, x17, 6\n" ++         -- x18 = emitted count * 64
  "  li x19, 0xa0010040\n" ++       -- x19 = OUTPUT + 64
  "  add x18, x19, x18\n" ++        -- x18 = write target
  -- Copy slotKey: log[+32..+64] → out[+0..+32]
  "  ld x21, 32(x14)\n" ++
  "  sd x21, 0(x18)\n" ++
  "  ld x21, 40(x14)\n" ++
  "  sd x21, 8(x18)\n" ++
  "  ld x21, 48(x14)\n" ++
  "  sd x21, 16(x18)\n" ++
  "  ld x21, 56(x14)\n" ++
  "  sd x21, 24(x18)\n" ++
  -- Copy current: log[+96..+128] → out[+32..+64]
  "  ld x21, 96(x14)\n" ++
  "  sd x21, 32(x18)\n" ++
  "  ld x21, 104(x14)\n" ++
  "  sd x21, 40(x18)\n" ++
  "  ld x21, 112(x14)\n" ++
  "  sd x21, 48(x18)\n" ++
  "  ld x21, 120(x14)\n" ++
  "  sd x21, 56(x18)\n" ++
  "  addi x17, x17, 1\n" ++
  "  sd x17, 56(x16)\n" ++          -- update count cell
  "6:\n" ++                         -- loop step
  "  addi x15, x15, -1\n" ++
  "  bnez x15, 1b\n" ++
  "4:\n" ++                         -- done — surface first LOG event, then halt
  -- M26: event LOG capture test surface. If receipt event logs
  -- exist, this intentionally reuses the storage diagnostic window:
  --   OUTPUT+56       : event log count (u64 LE)
  --   OUTPUT+64..256  : first event descriptor prefix
  -- Current opcode probes assert either storage post-state or LOG
  -- capture, not both. A future wider receipt-output ABI should
  -- carry both without sharing this test-only window.
  "  li x16, 0xa0010000\n" ++
  "  ld x17, 472(x20)\n" ++
  "  beqz x17, 8f\n" ++
  "  sd x17, 56(x16)\n" ++
  "  la x18, evm_event_logs\n" ++
  "  addi x19, x16, 64\n" ++
  "  li x21, 192\n" ++
  "7:\n" ++
  "  lbu x22, 0(x18)\n" ++
  "  sb x22, 0(x19)\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x21, x21, -1\n" ++
  "  bnez x21, 7b\n" ++
  "8:\n" ++                         -- done — fall through to halt stub
  -- SELFDESTRUCT staging diagnostic. The current concrete handler only
  -- stages the beneficiary for later gas/state children, so surface the
  -- staged canonical 20-byte address in the otherwise-empty storage/log
  -- diagnostic window. Future SELFDESTRUCT state/log integration can replace
  -- this probe once the staged address has a state consumer.
  "  la x18, evm_selfdestruct_staged\n" ++
  "  ld x17, 0(x18)\n" ++
  "  beqz x17, .L_selfdestruct_diag_done\n" ++
  "  la x18, evm_selfdestruct_beneficiary\n" ++
  "  addi x19, x16, 56\n" ++
  "  li x21, 20\n" ++
  "9:\n" ++
  "  lbu x22, 0(x18)\n" ++
  "  sb x22, 0(x19)\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x21, x21, -1\n" ++
  "  bnez x21, 9b\n" ++
  ".L_selfdestruct_diag_done:\n") ++
  afterDiagnostics

/-- Dispatcher epilogue for standalone BuildUnits. Falls through to the
    halt stub appended by `emitBuildUnit`. -/
def emitDispatcherEpilogue
    (registry : List OpcodeHandlerSpec) (exitBody : Program) : String :=
  emitDispatcherEpilogueCore registry exitBody ""

/-- Dispatcher epilogue for callable BuildUnits. It surfaces the same output
    diagnostics as the standalone path, then restores the caller's saved
    return address and returns. -/
def emitDispatcherCallableEpilogue
    (registry : List OpcodeHandlerSpec) (exitBody : Program) : String :=
  emitDispatcherEpilogueCore registry exitBody
    ("  la x5, runtime_dispatcher_caller_ra\n" ++
     "  ld ra, 0(x5)\n" ++
     "  ret\n")

/-- Callable dispatcher epilogue variant for embedding into a guest that already
    links the shared hash/RLP/MPT/account helper functions. -/
def emitDispatcherCallableEpilogueSharedHelpers
    (registry : List OpcodeHandlerSpec) (exitBody : Program) : String :=
  emitDispatcherEpilogueCore registry exitBody
    -- L3 (bmvmx.1.2.4.6.1): setup did `la sp, lp64_sp_top`, clobbering the
    -- caller's sp; restore it (saved in the callable prologue) BEFORE the ra
    -- restore so the post-dispatcher verdict runs on the caller's stack.
    ("  la x5, runtime_dispatcher_caller_sp\n" ++
     "  ld sp, 0(x5)\n" ++
     "  la x5, runtime_dispatcher_caller_ra\n" ++
     "  ld ra, 0(x5)\n" ++
     "  ret\n")
    false
    true

/-- `.data` section layout (starts at `0xa0000000` per
    `Driver.lean`'s `-Tdata=...`):

    ```
    evm_code:         <bytecode> (~50 B)
    .balign 32
    evm_memory:       fixed alias into the 16 MiB RegionMap EVM-memory arena
    .balign 8
    evm_env:          runtime environment and helper scratch follows
    lp64_stack:       helper-call stack
    evm_stack_guard:  .zero evmStackGuardBytes
    evm_stack_low:    .zero evmStackScratchBytes
                       (1024 × 32 B = 32 KiB EVM stack arena)
    evm_stack_top:
    evm_stack_top_guard:
                       .zero evmStackGuardBytes
    opcode_handlers:  256 × .dword (jump table, 2 KiB)
    ```

    The EVM memory region stays near the start of `.data` and grows upward
    from `evm_memory` indexed by `memBaseReg + offset`. The EVM stack lives
    in its own later static arena, grows downward from `evm_stack_top`, and
    supports the protocol 1024-word depth. The guard regions keep current
    stack-relative handler scratch inside reserved memory for existing runtime
    handler shapes while stack-overflow enforcement is tracked separately. -/
def emitDispatcherDataSection
    (bytecodeBytes : String) (registry : List OpcodeHandlerSpec) : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "evm_code:\n" ++
  s!"  .byte {bytecodeBytes}\n" ++
  "evm_code_end:\n" ++   -- M33: exact end of baked bytecode (CODESIZE/CODECOPY length)
  ".balign 32\n" ++
  "evm_memory_layout_pad:\n" ++
  "  .zero " ++ toString runtimeMemoryLayoutPadBytes ++ "\n" ++
  ".balign 8\n" ++
  "evm_sparse_memory_count:\n  .zero 8\n" ++
  "evm_sparse_memory_next_epoch:\n  .dword 1\n" ++
  "evm_sparse_memory_epoch_by_depth:\n  .zero " ++ toString (1025 * 8) ++ "\n" ++
  "evm_sparse_memory_entries:\n  .zero " ++ toString (4096 * 56) ++ "\n" ++
  ".balign 8\n" ++
  "evm_env:\n" ++
  "  .zero 656\n" ++      -- 13 SimpleEnvField slots × 32 B + calldata/return-data
                          -- + M22/M24/M26 log-state cells + M28/M29 blob/block
                          -- cells (up to env+560) + M30 gasRemaining at env+568
                          -- + M31 account-witness context at env+576..616
                          -- + EIP-7843 SLOTNUM word at env+624..655
                          -- + M28 BLOBBASEFEE word at env+512 (32 bytes)
                          -- + M28 blobHashCount at env+544
                          -- + M29 BLOCKHASH current/count at env+552/+560
  ".balign 8\n" ++
  "evm_blob_hashes:\n" ++
  "  .zero 512\n" ++      -- M28: bounded 16 × 32-byte tx blob versioned hashes
  ".balign 8\n" ++
  "evm_block_hashes:\n" ++
  "  .zero 8192\n" ++     -- M29: 256 × 32-byte recent BLOCKHASH ancestors
  ".balign 8\n" ++
  "evm_event_logs:\n" ++
  "  .zero 1048576\n" ++   -- M26: 4096 × 256-byte bounded LOG event descriptors (v0.6.0 deposit blocks exceed 1024)
  ".balign 8\n" ++
  "evm_log_data:\n" ++
  "  .zero 1048576\n" ++   -- 8uld3.1a: per-tx FULL LOG data buffer (parallel to evm_event_logs); overflow -> evm_log_data_overflow
  ".balign 8\n" ++
  "evm_log_data_meta:\n" ++
  "  .zero 65536\n" ++    -- 8uld3.1a: 4096 logs × [u64 byte-offset into evm_log_data][u64 data_len], parallel to the descriptors
  ".balign 8\n" ++
  "evm_log_data_used:\n" ++
  "  .zero 8\n" ++        -- 8uld3.1a: bytes used in evm_log_data this tx (reset with eventLogLength)
  "evm_log_data_overflow:\n" ++
  "  .zero 8\n" ++        -- 8uld3.1a: set to 1 if a log's full data overflowed the buffer -> consumer bails conservatively
  ".balign 8\n" ++
  "system_call_mode:\n" ++
  "  .zero 8\n" ++        -- 8uld3.2.1a: when !=0, a top-level (depth-0) RETURN captures its data into system_call_returndata (for EIP-7002/7251 predeploy system calls). 0 for normal txs -> halt path byte-identical.
  ".balign 8\n" ++
  "system_call_returndata_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "system_call_returndata:\n" ++
  "  .zero " ++ toString systemCallReturndataMaxBytes ++ "\n" ++     -- 8uld3.2.1a: includes builder deposits (64x184=11776; 12 KiB cap)
  ".balign 8\n" ++
  "top_level_creation_returndata_status:\n" ++
  "  .zero 8\n" ++        -- 0=no depth-0 RETURN, 1=captured, 2=oversized RETURN (fail closed)
  ".balign 8\n" ++
  "top_level_creation_returndata_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "top_level_creation_returndata:\n" ++
  "  .zero " ++ toString topLevelCreationReturndataMaxBytes ++ "\n" ++
  emitSelfdestructData ++
  eip7708SyntheticLogTopicData ++
  storageAccessGasData ++
  emitPrecompileFrameData ++
  emitModexpScratchData ++
  emitSha256Data ++
  ripemd160DataFragment ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++      -- M16: 25 × u64 keccak permutation state buffer
  emitRuntimeAccountWitnessData ++
  ".balign 16\n" ++
  "lp64_stack:\n" ++
  "  .zero 262144\n" ++   -- LP64 stack for nested KECCAK/RLP/MPT/account helpers
  "lp64_sp_top:\n" ++
  ".balign 32\n" ++
  "evm_stack_guard_low:\n" ++
  s!"  .zero {evmStackGuardBytes}\n" ++
  "evm_stack_low:\n" ++
  s!"  .zero {evmStackScratchBytes}\n" ++
  "evm_stack_top:\n" ++
  "evm_stack_top_guard:\n" ++
  s!"  .zero {evmStackGuardBytes}\n" ++
  ".balign 8\n" ++
  -- Frame-relative stack bounds. Each cell holds the CURRENT frame's stack-top /
  -- stack-low ADDRESS. Statically `&evm_stack_top` / `&evm_stack_low`, so at
  -- depth 0 the under/overflow guards resolve to the same bounds as before
  -- (byte-identical output). `call_frame_descend` repoints them to the child's
  -- arena stack (`frame_base(d)+frameStackTopOff` and its low), and
  -- `frame_return` restores the parent's on pop. This makes the guards bound
  -- a child frame against its own stack (which lives in `call_frame_arena`,
  -- outside this global region) instead of spuriously firing.
  "evm_cur_stack_top:\n" ++
  "  .dword evm_stack_top\n" ++
  "evm_cur_stack_low:\n" ++
  "  .dword evm_stack_low\n" ++
  ".balign 8\n" ++
  "exp_scratch:\n" ++
  "  .zero 32\n" ++       -- EXP (0x0a): 32-byte result-accumulator frame. The
                          -- verified EXP body uses `x2`(sp)+0..24 as its running
                          -- accumulator; the dispatcher's `sp` points at
                          -- `lp64_sp_top` (top of a down-growing stack), so
                          -- `sp+0..24` would scribble into the jump table.
                          -- h_EXP's preBody repoints `x2` here and its tail
                          -- restores `sp = lp64_sp_top`.
                          -- (ADDMOD (0x08) needs no scratch symbols here: the
                          -- verified `evm_addmod_total` body parks its carry
                          -- scratch below `x12`, inside the guarded EVM stack
                          -- region — see EvmSelfCallingHandlers.lean.)
  emitBls12G1MsmDiscountTable ++
  emitBls12G2MsmDiscountTable ++
  emitGasCostTable ++ "\n" ++
  emitJumpTable registry ++ "\n" ++
  ".balign 32\n" ++
  "evm_memory:\n" ++
  "  .zero " ++ toString runtimeMemoryBytes ++ "\n"

/-! ## Runtime-bytecode dispatcher (M8.5)

    Variant of the dispatcher that reads its bytecode at runtime
    from ziskemu's `-i <file>` input region instead of baking it
    into `.data`. Lets a single ELF run any bytecode — the test
    harness packs each per-case bytecode into an input file and
    re-uses the same ELF.

    Reads bytecode at `INPUT_ADDR + INPUT_DATA_OFFSET = 0x40000010`
    (see `EvmAsm/Codegen/Programs.lean` for the symbolic constants).
    All other dispatcher state (stack scratch, evm_memory, jump
    table) is identical to the `.data`-baked variant — only the
    prologue's `la x10, evm_code` swaps to `li x10, 0x40000010`
    and the `.data` section drops the `evm_code:` block. -/

/-- Seed the per-transaction access-list warm sets from the pending tx span.
    The span is prepared by `dispatch_tx_runtime_code`; standalone callers leave
    the globals zero, so this is inert. It must run after the per-tx warm-set
    reset and before any preparation charge consults accessed addresses. -/
def emitTxAccessListSeedLoop : String :=
  "  la x5, runtime_tx_access_list_ptr; ld a0, 0(x5)\n" ++
  "  la x6, runtime_tx_access_list_len; ld a1, 0(x6)\n" ++
  "  la x7, runtime_tx_access_list_seed_fn; ld x28, 0(x7)\n" ++
  "  sd x0, 0(x5); sd x0, 0(x6); sd x0, 0(x7)\n" ++
  "  beqz x28, .Ltx_access_seed_done\n" ++
  "  beqz a0, .Ltx_access_seed_done\n" ++
  "  beqz a1, .Ltx_access_seed_done\n" ++
  "  jalr ra, x28, 0\n" ++
  "  # seed failure is conservative: a missed warm seed over-charges gas.\n" ++
  ".Ltx_access_seed_done:\n" ++
  "  mv x10, x21\n"

/-- Runtime-bytecode dispatcher prologue. Same fetch/decode/dispatch
    loop as `emitDispatcherPrologue`; differs only in how `x10` is
    initialised — pointed at the input region instead of an
    in-`.data` label. The hex literal `0x40000010` matches
    `INPUT_ADDR + INPUT_DATA_OFFSET` in `Programs.lean`. -/
private def emitTopLevelMessageD0Preparation : String :=
  -- Cut A gathers the top-level preparation portion around `process_message`
  -- without changing its emitted order. Cut B will guard this exact fragment
  -- with `evm_call_depth == 0` before a later entry seam allows child frames
  -- here. Access seeding below is caller-scoped, rather than depth-guarded in
  -- the spec: nested messages inherit their parent's accessed-address set.
  -- Do not move individual instructions across this boundary: state-gas and
  -- early-exit ordering is part of the transaction semantics.
  -- 1. authorization traversal / set_delegation callback
  "  la x11, runtime_tx_auth_state_charge; sd x0, 0(x11)\n" ++
  "  la x11, runtime_tx_auth_exec_fn; ld x9, 0(x11); beqz x9, .runtime_tx_auth_exec_done\n" ++
  "  addi sp, sp, -56; sd ra, 0(sp); sd x5, 8(sp); sd x6, 16(sp); sd x7, 24(sp); sd x10, 32(sp); sd x20, 40(sp); sd x21, 48(sp)\n" ++
  "  la x11, runtime_tx_auth_inner_ptr; ld x10, 0(x11); la x11, runtime_tx_auth_inner_len; ld x11, 0(x11); la x12, runtime_tx_auth_sender_ptr; ld x12, 0(x12); la x13, runtime_tx_auth_type; ld x13, 0(x13)\n" ++
  "  jalr ra, x9, 0; mv x9, x10\n" ++
  "  ld ra, 0(sp); ld x5, 8(sp); ld x6, 16(sp); ld x7, 24(sp); ld x10, 32(sp); ld x20, 40(sp); ld x21, 48(sp); addi sp, sp, 56\n" ++
  "  bnez x9, .exit_outofgas\n" ++
  ".runtime_tx_auth_exec_done:\n" ++
  -- 2. authorization state-gas fold
  "  la x11, runtime_tx_auth_state_refund\n" ++
  "  ld x9, 0(x11)\n" ++
  "  beqz x9, .runtime_tx_auth_state_refund_done\n" ++
  "  la x11, runtime_tx_auth_state_charge; sd x9, 0(x11)\n" ++
  "  la x11, runtime_tx_state_gas_ptr; ld x8, 0(x11); ld x7, 0(x8); add x7, x7, x9; sd x7, 0(x8)\n" ++
  "  la x11, evm_state_gas_left\n" ++
  "  ld x8, 0(x11)\n" ++
  "  bltu x8, x9, .runtime_tx_auth_state_spill\n" ++
  "  sub x8, x8, x9\n" ++
  "  sd x8, 0(x11)\n" ++
  "  j .runtime_tx_auth_state_refund_done\n" ++
  ".runtime_tx_auth_state_spill:\n" ++
  "  sub x9, x9, x8\n" ++
  "  sd x0, 0(x11)\n" ++
  "  bltu x6, x9, .exit_outofgas\n" ++
  "  sub x6, x6, x9\n" ++
  ".runtime_tx_auth_state_refund_done:\n" ++
  "  la x11, runtime_tx_auth_state_charge; sd x0, 0(x11)\n" ++
  ".runtime_tx_auth_state_used_done:\n" ++
  -- 3. prepare_dispatch's staged creation state-gas charge
  "  la x11, runtime_tx_create_state_charge\n" ++
  "  ld x9, 0(x11)\n" ++
  "  beqz x9, .runtime_tx_create_state_done\n" ++
  "  mv x7, x9\n" ++
  "  la x11, evm_state_gas_left\n" ++
  "  ld x8, 0(x11)\n" ++
  "  bltu x8, x9, .runtime_tx_create_state_spill\n" ++
  "  sub x8, x8, x9\n" ++
  "  sd x8, 0(x11)\n" ++
  "  j .runtime_tx_create_state_used\n" ++
  ".runtime_tx_create_state_spill:\n" ++
  "  sub x9, x9, x8\n" ++
  "  bltu x6, x9, .exit_outofgas\n" ++
  "  sd x0, 0(x11)\n" ++
  "  sub x6, x6, x9\n" ++
  "  la x11, evm_state_gas_spilled\n" ++
  "  ld x8, 0(x11)\n" ++
  "  add x8, x8, x9\n" ++
  "  sd x8, 0(x11)\n" ++
  ".runtime_tx_create_state_used:\n" ++
  "  la x11, evm_state_gas_used\n" ++
  "  ld x8, 0(x11)\n" ++
  "  add x8, x8, x7\n" ++
  "  sd x8, 0(x11)\n" ++
  ".runtime_tx_create_state_done:\n" ++
  -- 4. top-level-only preparation halt, then top-frame gas and context
  "  la x11, runtime_tx_prepare_only; ld x9, 0(x11); beqz x9, .runtime_tx_prepare_prefix_continue\n" ++
  "  la x11, runtime_tx_prepare_prefix_status; li x9, 2; sd x9, 0(x11)\n" ++
  "  la x11, runtime_tx_prepare_only; sd x0, 0(x11); j runtime_dispatcher_prepare_only_return\n" ++
  ".runtime_tx_prepare_prefix_continue:\n" ++
  ".runtime_tx_gas_done:\n" ++
  "  sd x6, 568(x20)\n" ++
  "  la x11, runtime_tx_top_frame_regular_gas\n" ++
  "  ld x9, 0(x11)\n" ++
  "  beqz x9, .runtime_tx_top_frame_regular_done\n" ++
  "  bltu x6, x9, .exit_outofgas\n" ++
  "  sub x6, x6, x9\n" ++
  "  sd x6, 568(x20)\n" ++
  ".runtime_tx_top_frame_regular_done:\n" ++
  "  ld x6, 0(x5)\n" ++
  "  sd x6, 584(x20)\n" ++
  "  ld x7, 8(x5)\n" ++
  "  sd x7, 600(x20)\n" ++
  "  ld x8, 16(x5)\n" ++
  "  sd x8, 616(x20)\n" ++
  "  addi x5, x5, 24\n" ++
  "  sd x5, 576(x20)\n" ++
  "  add x5, x5, x6\n" ++
  "  sd x5, 592(x20)\n" ++
  "  add x5, x5, x7\n" ++
  "  sd x5, 608(x20)\n" ++
  -- 5. caller-scoped access seeding and the full deferred prepare_dispatch callback
  "  jal ra, runtime_access_seed_initial_accounts\n" ++
  emitTxAccessListSeedLoop ++ "\n" ++
  "  la x5, runtime_tx_post_top_frame_fn\n" ++
  "  ld x28, 0(x5)\n" ++
  "  beqz x28, .runtime_tx_post_top_frame_done\n" ++
  "  jalr ra, x28, 0\n" ++
  ".runtime_tx_post_top_frame_done:\n" ++
  -- 6. the depth-zero preparation marker.  The spec returns directly on a
  -- preparation halt, so reaching the shared body is its own marker; the
  -- guest records that distinction explicitly for the later reconciliation.
  "  la x11, runtime_tx_post_preparation_reached; li x9, 1; sd x9, 0(x11)\n"

def emitRuntimeDispatcherSetupWithInputAsm (inputAsm : String) : String :=
  "  la sp, lp64_sp_top\n" ++   -- M16: LP64 stack ptr for ECALL-bridge helpers
                                -- (e.g. zkvm_keccak256's `addi sp, sp, -32`)
  inputAsm ++
  "  la x12, evm_stack_top\n" ++
  "  la x5, evm_cur_stack_top; sd x12, 0(x5)\n" ++
  "  la x5, evm_stack_low; la x6, evm_cur_stack_low; sd x5, 0(x6)\n" ++
  "  la x13, evm_memory\n" ++
  "  la x20, evm_env\n" ++       -- M12: env-region base (ADDRESS, CALLER, …)
  -- M21: populate env's callDataPtr / callDataLen from the input region.
  -- The input file format (pack-bytecode.py) is:
  --   [8B bytecode-length][bytecode bytes][pad to 8][8B calldata-length][calldata bytes]
  -- bytecode-length sits at INPUT_ADDR + 8 = 0x40000008. We round it up
  -- to 8-byte boundary, add to bytecode start (x10), and that's the
  -- calldata-length address. Eight bytes past it is the calldata.
  "  addi x5, x10, -8\n" ++       -- &(bytecode length)
  "  ld x5, 0(x5)\n" ++            -- x5 = bytecode length (exact)
  "  sd x5, 496(x20)\n" ++         -- M33: env.codeSize = bytecode length (CODESIZE/CODECOPY)
  "  sd x0, " ++ toString staticContextFlagOff ++ "(x20)\n" ++ -- env.isStatic = 0
  "  addi x5, x5, 7\n" ++          -- round up to 8-byte boundary
  "  srli x5, x5, 3\n" ++
  "  slli x5, x5, 3\n" ++          -- x5 = padded bytecode length
  "  add x6, x10, x5\n" ++         -- x6 = &(calldata length)
  "  ld x7, 0(x6)\n" ++            -- x7 = calldata length
  "  addi x6, x6, 8\n" ++          -- x6 = calldata ptr
  "  sd x6, 416(x20)\n" ++         -- env.callDataPtrOff (416) = ptr
  "  sd x7, 424(x20)\n" ++         -- env.callDataLenOff (424) = len
  -- M24: locate the storage preload segment past the calldata pad and
  -- expand each 64-byte (key, value) input entry into a 128-byte
  -- Option A entry (addrHash=0, slotKey=key, original=value,
  -- current=value) at STATE_TRACKER_AREA = 0xa0630000. Save the
  -- preload count to both the live persistent log length AND the
  -- checkpoint (so REVERT rolls back to post-preload). Init
  -- transient log length to 0 (transient storage starts empty).
  --
  -- Input layout (unchanged from M22 `pack-bytecode.py --storage`):
  --   <u64 slot_count> followed by slot_count × (key:32, value:32)
  --   then a 32-byte BLOBBASEFEE word (M28; zero by default),
  --   u64 blob_hash_count, and blob_hash_count × 32-byte words.
  -- Output layout (Option A):
  --   STATE_TRACKER_AREA + i*128 = (addrHash=0:32, slotKey:32,
  --                                 original=value:32, current=value:32)
  "  add x5, x6, x7\n" ++          -- x5 = end of calldata bytes
  "  addi x5, x5, 7\n" ++          -- round up to 8-byte boundary
  "  srli x5, x5, 3\n" ++
  "  slli x5, x5, 3\n" ++          -- x5 = &(slot count)
  "  ld x6, 0(x5)\n" ++            -- x6 = slot_count (= preload count)
  "  li x28, 16384\n" ++
  "  bgtu x6, x28, .exit_invalid\n" ++
  "  sd x6, 448(x20)\n" ++         -- env.persistentLogLengthOff = preload count
  "  sd x6, 456(x20)\n" ++         -- env.persistentLogCheckpointOff = preload count
  "  sd x0, 464(x20)\n" ++         -- env.transientLogLengthOff = 0
  "  sd x0, 472(x20)\n" ++         -- env.eventLogLengthOff = 0
  -- 8uld3.2.1.3 FIX: reset the per-tx full-log-data globals via x28 (a dead scratch
  -- here), NOT x5. x5 is the live INPUT-WALK CURSOR (= &slot_count) in this input-driven
  -- setup; the original `la x5, …` (added by 8uld3.1a, 9e363d19d) clobbered it, so every
  -- subsequent walk step (preload src @+8, blob/M29/env trailers, and the M30 GAS trailer)
  -- read from &evm_log_data_overflow+8 (zeros) instead of the input -> gasRemaining read
  -- as 0 -> the dispatch OOGs before any opcode. Latent on main only because contract
  -- dispatch bails (sv_this_rlp restored by #8686); surfaces the moment the dispatcher
  -- actually runs (system calls 8uld3.2.1c, and the mtx re-land .57.11.6.5). The
  -- .data-baked setup's identical reset (~L974) is unaffected: it reloads x5 right after.
  "  la x28, evm_log_data_used; sd x0, 0(x28)\n" ++     -- reset per-tx full-log-data buffer cursor
  "  la x28, evm_log_data_overflow; sd x0, 0(x28)\n" ++ -- reset per-tx full-log-data overflow flag
  -- bmvmx.5.5.2.2.ln9ly: re-emit a block_verdict-staged top-level EIP-7708 transfer log HERE --
  -- after the event-log + full-log-data resets above wiped the pre-dispatch emit, before the
  -- checkpoint below -- so it lands as log 0 and survives into the receipt (fixes the single-tx
  -- contract-path bv_fail=53). dispatcher_reemit_pending_tl is gated on bv_pending_tl_flag (no-op
  -- otherwise) and preserves all caller regs (x5 cursor / x20 env live here); save ra around it.
  "  addi sp, sp, -16\n  sd ra, 0(sp)\n" ++
  "  jal ra, dispatcher_reemit_pending_tl\n" ++
  "  ld ra, 0(sp)\n  addi sp, sp, 16\n" ++
  -- nxio8: per-TRANSACTION dispatch state that previously leaked across calls in a
  -- multi-tx block (the callable dispatcher is invoked once per tx in one guest run):
  --   * evm_refund_acc — EIP-3529 refund counter is per tx (only the baked prologue
  --     reset it; a 2nd dispatch call inherited tx 1's refunds).
  --   * evm_storage_access_count — EIP-2929 accessed_storage_keys is per tx
  --     (prepare_message builds a fresh set); a 2nd call saw tx 1's keys as warm.
  --   * evm_state_gas_left / evm_state_gas_used / evm_state_gas_spilled — EIP-8037
  --     per-tx state-gas reservoir + usage + gas-left spill tracking.
  -- evm_storage_access_outcome_count is NOT reset: the outcome log is an append-only
  -- cross-tx diagnostic surface (bal_storage_access_outcome_descriptors).
  "  la x28, evm_refund_acc; sd x0, 0(x28)\n" ++
  "  la x28, evm_storage_access_count; sd x0, 0(x28)\n" ++
  "  la x28, evm_state_gas_left; sd x0, 0(x28)\n" ++
  "  la x28, evm_state_gas_used; sd x0, 0(x28)\n" ++
  "  la x28, evm_state_gas_spilled; sd x0, 0(x28)\n" ++
  -- This is a memoized control-flow fact, not independent guest state: it is
  -- set only after the common intrinsic, auth-state, and top-frame regular
  -- pre-dispatch charges have all passed their gas-coverage checks below.
  -- A pre-dispatch ExceptionalHalt leaves it zero; a later body REVERT keeps it.
  "  la x28, runtime_tx_post_preparation_reached; sd x0, 0(x28)\n" ++
  "  la x28, evm_sparse_memory_count; sd x0, 0(x28)\n" ++
  "  la x28, evm_sparse_memory_next_epoch; li x29, 1; sd x29, 0(x28)\n" ++
  "  la x28, evm_sparse_memory_epoch_by_depth; sd x0, 0(x28)\n" ++
  -- halt_kind (OUTPUT+32) = 0: the skip-finalization (verdict-callable) exit
  -- join never writes the success kind, so without this reset a prior
  -- dispatch's REVERT/exceptional kind would leak into dispatcher_tx_gas_settle.
  -- The exceptional exits and RETURN/REVERT tails overwrite it during this
  -- dispatch; a clean STOP leaves this 0.
  "  li x28, 0xa0010000; sd x0, 32(x28)\n" ++
  "  sd x0, 480(x20)\n" ++         -- env.eventLogCheckpointOff = 0
  "  sd x0, 488(x20)\n" ++         -- runtime activeMemorySize = 0
  "  sd x0, 512(x20)\n" ++         -- M28: blobBaseFee[0] = 0 (overwritten by trailer load below)
  "  sd x0, 520(x20)\n" ++         -- M28: blobBaseFee[1] = 0
  "  sd x0, 528(x20)\n" ++         -- M28: blobBaseFee[2] = 0
  "  sd x0, 536(x20)\n" ++         -- M28: blobBaseFee[3] = 0
  "  sd x0, 544(x20)\n" ++         -- M28: blobHashCount = 0 (overwritten by trailer load below)
  "  sd x0, 552(x20)\n" ++         -- M29: currentBlockNumber = 0 (overwritten by trailer load below)
  "  sd x0, 560(x20)\n" ++         -- M29: blockHashCount = 0
  "  addi x5, x5, 8\n" ++          -- x5 = src ptr (first preload entry)
  "  li x7, 0xa0630000\n" ++       -- x7 = dst ptr (STATE_TRACKER_AREA persistent log)
  "  la x9, exec_log_seed_flag\n" ++ -- this preload row is not an execution write
  ".preload_expand_loop:\n" ++
  "  beqz x6, .preload_expand_done\n" ++
  "  li x10, 1; sb x10, 0(x9)\n" ++
  -- addrHash = 0 (32 bytes)
  "  sd x0, 0(x7)\n" ++
  "  sd x0, 8(x7)\n" ++
  "  sd x0, 16(x7)\n" ++
  "  sd x0, 24(x7)\n" ++
  -- slotKey = src[0..32] → dst[32..64]
  "  ld x8, 0(x5)\n" ++
  "  sd x8, 32(x7)\n" ++
  "  ld x8, 8(x5)\n" ++
  "  sd x8, 40(x7)\n" ++
  "  ld x8, 16(x5)\n" ++
  "  sd x8, 48(x7)\n" ++
  "  ld x8, 24(x5)\n" ++
  "  sd x8, 56(x7)\n" ++
  -- value (src[32..64]) → original (dst[64..96]) AND current (dst[96..128])
  "  ld x8, 32(x5)\n" ++
  "  sd x8, 64(x7)\n" ++
  "  sd x8, 96(x7)\n" ++
  "  ld x8, 40(x5)\n" ++
  "  sd x8, 72(x7)\n" ++
  "  sd x8, 104(x7)\n" ++
  "  ld x8, 48(x5)\n" ++
  "  sd x8, 80(x7)\n" ++
  "  sd x8, 112(x7)\n" ++
  "  ld x8, 56(x5)\n" ++
  "  sd x8, 88(x7)\n" ++
  "  sd x8, 120(x7)\n" ++
  "  addi x5, x5, 64\n" ++         -- next input entry (64 B)
  "  addi x7, x7, 128\n" ++        -- next output entry (128 B)
  "  addi x9, x9, 1\n" ++
  "  addi x6, x6, -1\n" ++
  "  j .preload_expand_loop\n" ++
  ".preload_expand_done:\n" ++
  -- M28: x5 now points at the blob-base-fee trailer. Copy the 32-byte
  -- EVM-stack word into env+512..+540; opcode 0x4a loads it from there.
  "  ld x8, 0(x5)\n" ++
  "  sd x8, 512(x20)\n" ++
  "  ld x8, 8(x5)\n" ++
  "  sd x8, 520(x20)\n" ++
  "  ld x8, 16(x5)\n" ++
  "  sd x8, 528(x20)\n" ++
  "  ld x8, 24(x5)\n" ++
  "  sd x8, 536(x20)\n" ++
  "  addi x5, x5, 32\n" ++         -- x5 = &(blob_hash_count)
  "  ld x6, 0(x5)\n" ++            -- x6 = source blob_hash_count
  -- Static runtime table cap: enough for current protocol limits, and
  -- explicit truncation keeps the copy bounded if malformed test input
  -- claims more entries. Full EEST plumbing should reject impossible
  -- protocol configs before launch when this cap is insufficient.
  "  li x7, 16\n" ++
  "  bleu x6, x7, .blob_hash_count_ok\n" ++
  "  mv x6, x7\n" ++
  ".blob_hash_count_ok:\n" ++
  "  sd x6, 544(x20)\n" ++         -- env.blobHashCount = min(count, 16)
  "  addi x5, x5, 8\n" ++          -- x5 = first blob hash word
  "  la x7, evm_blob_hashes\n" ++
  ".blob_hash_copy_loop:\n" ++
  "  beqz x6, .blob_hash_copy_done\n" ++
  "  ld x8, 0(x5)\n" ++
  "  sd x8, 0(x7)\n" ++
  "  ld x8, 8(x5)\n" ++
  "  sd x8, 8(x7)\n" ++
  "  ld x8, 16(x5)\n" ++
  "  sd x8, 16(x7)\n" ++
  "  ld x8, 24(x5)\n" ++
  "  sd x8, 24(x7)\n" ++
  "  addi x5, x5, 32\n" ++
  "  addi x7, x7, 32\n" ++
  "  addi x6, x6, -1\n" ++
  "  j .blob_hash_copy_loop\n" ++
  ".blob_hash_copy_done:\n" ++
  -- M29: BLOCKHASH context trailer follows blob hash table:
  --   u64 current_block_number
  --   u64 block_hash_count
  --   count × 32-byte hashes, in increasing block-number order.
  -- The table is clamped to the EVM window size (256 ancestors).
  "  ld x6, 0(x5)\n" ++            -- x6 = current block number
  "  sd x6, 552(x20)\n" ++
  "  ld x6, 8(x5)\n" ++            -- x6 = source hash count
  "  li x7, 256\n" ++
  "  bgeu x7, x6, .blockhash_count_ok\n" ++
  "  mv x6, x7\n" ++
  ".blockhash_count_ok:\n" ++
  "  sd x6, 560(x20)\n" ++
  "  addi x5, x5, 16\n" ++         -- x5 = first source hash
  "  la x7, evm_block_hashes\n" ++
  ".blockhash_copy_loop:\n" ++
  "  beqz x6, .blockhash_copy_done\n" ++
  "  ld x8, 0(x5)\n" ++
  "  sd x8, 0(x7)\n" ++
  "  ld x8, 8(x5)\n" ++
  "  sd x8, 8(x7)\n" ++
  "  ld x8, 16(x5)\n" ++
  "  sd x8, 16(x7)\n" ++
  "  ld x8, 24(x5)\n" ++
  "  sd x8, 24(x7)\n" ++
  "  addi x5, x5, 32\n" ++
  "  addi x7, x7, 32\n" ++
  "  addi x6, x6, -1\n" ++
  "  j .blockhash_copy_loop\n" ++
  ".blockhash_copy_done:\n" ++
  -- Simple-env trailer: 13 contiguous 32-byte slots matching `EvmEnv`
  -- layout offsets 0..415: ADDRESS, SELFBALANCE, CALLER, CALLVALUE,
  -- ORIGIN, GASPRICE, COINBASE, TIMESTAMP, NUMBER, PREVRANDAO,
  -- GASLIMIT, BASEFEE, CHAINID. A 14th 32-byte trailer word carries
  -- EIP-7843 SLOTNUM and is copied to env+624 so existing helper offsets
  -- stay fixed. Zero defaults are preserved when the packer emits zeros.
  "  mv x6, x20\n" ++              -- x6 = evm_env destination
  "  li x7, 52\n" ++               -- 13 words × 4 dwords
  ".env_trailer_copy_loop:\n" ++
  "  ld x8, 0(x5)\n" ++
  "  sd x8, 0(x6)\n" ++
  "  addi x5, x5, 8\n" ++
  "  addi x6, x6, 8\n" ++
  "  addi x7, x7, -1\n" ++
  "  bnez x7, .env_trailer_copy_loop\n" ++
  "  ld x8, 0(x5)\n" ++
  "  sd x8, 624(x20)\n" ++
  "  ld x8, 8(x5)\n" ++
  "  sd x8, 632(x20)\n" ++
  "  ld x8, 16(x5)\n" ++
  "  sd x8, 640(x20)\n" ++
  "  ld x8, 24(x5)\n" ++
  "  sd x8, 648(x20)\n" ++
  "  addi x5, x5, 32\n" ++
  -- Re-tag the preloaded storage entries' addrHash to the executing frame's
  -- env.ADDRESS (now loaded above). The preload-expand wrote addrHash=0, but
  -- SLOAD/SSTORE key on env.ADDRESS (per-contract storage isolation), so without
  -- this the recipient's own SLOAD would miss its preloaded slots and read 0.
  -- All preloaded entries are the recipient's own storage, so a single
  -- env.ADDRESS tag is correct. (Nested-callee storage preload is a follow-up.)
  "  ld x6, 448(x20)\n" ++          -- x6 = preload count
  "  li x7, 0xa0630000\n" ++        -- x7 = persistent log base
  ".retag_preload_loop:\n" ++
  "  beqz x6, .retag_preload_done\n" ++
  "  ld x8, 0(x20);  sd x8, 0(x7)\n" ++
  "  ld x8, 8(x20);  sd x8, 8(x7)\n" ++
  "  ld x8, 16(x20); sd x8, 16(x7)\n" ++
  "  ld x8, 24(x20); sd x8, 24(x7)\n" ++
  "  addi x7, x7, 128\n" ++
  "  addi x6, x6, -1\n" ++
  "  j .retag_preload_loop\n" ++
  ".retag_preload_done:\n" ++
  -- M30/M35/M31: gas limit trailer, optional transaction intrinsic-gas
  -- validation controls, then optional account-witness context. When the
  -- tx-gas validation flag is zero, the gas trailer is treated as execution
  -- gas for backwards-compatible opcode-runtime tests. When it is nonzero,
  -- the trailer is transaction gas: compute Amsterdam call/create intrinsic
  -- gas plus the EIP-7623 calldata floor, reject if gas < max(intrinsic,
  -- floor), and start execution with gas - intrinsic.
  "  ld x6, 0(x5)\n" ++
  "  addi x5, x5, 8\n" ++          -- x5 = &(tx gas validation flag)
  "  ld x7, 0(x5)\n" ++            -- x7 = validate_tx_gas flag
  "  addi x5, x5, 8\n" ++          -- x5 = &(tx is_creation flag)
  "  ld x8, 0(x5)\n" ++            -- x8 = is_creation
  "  addi x5, x5, 8\n" ++          -- x5 = &(account-witness header_len)
  "  beqz x7, .runtime_tx_gas_done\n" ++
  "  li x7, 12000\n" ++            -- x7 = intrinsic.regular = Amsterdam TX_BASE
  "  li x10, 12000\n" ++           -- x10 = calldata floor = Amsterdam TX_BASE
  "  beqz x8, .runtime_tx_gas_no_create\n" ++
  "  li x8, 11000\n" ++            -- CREATE_ACCESS = ACCOUNT_WRITE + COLD_STORAGE_ACCESS
  "  add x7, x7, x8\n" ++
  "  add x10, x10, x8\n" ++        -- v0.6.0: floor anchors on base_regular_gas
  -- `calculate_intrinsic_cost` includes the EIP-7708 synthetic Transfer-log
  -- cost in a value-carrying CREATE's recipient_regular_gas.  This is part of
  -- base_regular_gas, so it must feed both the regular intrinsic and the
  -- calldata floor before the latter is persisted below.
  "  ld x8, 96(x20); ld x9, 104(x20); or x8, x8, x9\n" ++
  "  ld x9, 112(x20); or x8, x8, x9\n" ++
  "  ld x9, 120(x20); or x8, x8, x9\n" ++
  "  beqz x8, .runtime_tx_gas_recipient_done\n" ++
  "  li x8, 1756\n" ++             -- TRANSFER_LOG_COST
  "  add x7, x7, x8\n" ++
  "  add x10, x10, x8\n" ++
  "  j .runtime_tx_gas_recipient_done\n" ++
  ".runtime_tx_gas_no_create:\n" ++
  -- EIP-2780 decomposes the non-create recipient/value components out of the
  -- bundled legacy base. Non-self calls pay COLD_ACCOUNT_ACCESS, and non-self
  -- value calls additionally pay TRANSFER_LOG_COST + TX_VALUE_COST.
  "  ld x8, -8(x5)\n" ++           -- x8 = is_creation
  "  bnez x8, .runtime_tx_gas_recipient_done\n" ++
  "  li x8, 0\n" ++
  ".runtime_tx_gas_self_cmp:\n" ++
  "  li x9, 20; beq x8, x9, .runtime_tx_gas_recipient_done\n" ++
  "  add x11, x20, x8\n" ++
  "  lbu x12, 0(x11)\n" ++
  "  addi x11, x20, 64\n" ++
  "  add x11, x11, x8\n" ++
  "  lbu x13, 0(x11)\n" ++
  "  bne x12, x13, .runtime_tx_gas_not_self\n" ++
  "  addi x8, x8, 1\n" ++
  "  j .runtime_tx_gas_self_cmp\n" ++
  ".runtime_tx_gas_not_self:\n" ++
  "  li x8, 3000\n" ++             -- COLD_ACCOUNT_ACCESS
  "  add x7, x7, x8\n" ++
  "  add x10, x10, x8\n" ++        -- v0.6.0: floor anchors on base_regular_gas

  "  ld x8, 96(x20); ld x9, 104(x20); or x8, x8, x9\n" ++
  "  ld x9, 112(x20); or x8, x8, x9\n" ++
  "  ld x9, 120(x20); or x8, x8, x9\n" ++
  "  beqz x8, .runtime_tx_gas_recipient_done\n" ++
  "  li x8, 6000\n" ++             -- TRANSFER_LOG_COST + TX_VALUE_COST
  "  add x7, x7, x8\n" ++
  "  add x10, x10, x8\n" ++        -- v0.6.0: floor anchors on base_regular_gas
  ".runtime_tx_gas_recipient_done:\n" ++
  -- Message calldata drives EVM data opcodes, but a top-level CREATE has
  -- empty message.data while its transaction initcode still pays transaction
  -- data and initcode-word intrinsic gas.  Creation supplies that distinct
  -- transaction-data span through these one-shot globals; ordinary calls use
  -- the staged frame span as before.
  "  ld x8, 424(x20)\n" ++         -- x8 = frame calldata length
  "  ld x9, 416(x20)\n" ++         -- x9 = frame calldata ptr
  "  ld x12, 424(x20)\n" ++        -- x12 = transaction-data len for initcode words
  "  la x13, runtime_tx_intrinsic_data_len; ld x13, 0(x13); beqz x13, .runtime_tx_gas_data_span_ready\n" ++
  "  la x9, runtime_tx_intrinsic_data_ptr; ld x9, 0(x9); mv x8, x13; mv x12, x13\n" ++
  ".runtime_tx_gas_data_span_ready:\n" ++
  ".runtime_tx_gas_data_loop:\n" ++
  "  beqz x8, .runtime_tx_gas_create_words\n" ++
  "  lbu x11, 0(x9)\n" ++
  "  beqz x11, .runtime_tx_gas_zero_byte\n" ++
  "  addi x7, x7, 16\n" ++       -- non-zero data_cost = 4 tokens * STANDARD_TOKEN_COST(4)
  "  addi x10, x10, 64\n" ++   -- floor = 4 tokens * TX_DATA_TOKEN_FLOOR(16) = 64 per non-zero byte
  "  j .runtime_tx_gas_data_step\n" ++
  ".runtime_tx_gas_zero_byte:\n" ++
  "  addi x7, x7, 4\n" ++       -- zero-byte data_cost (count_tokens_in_data) = 1 token * 4
  -- mlp31: EIP-7976 makes the calldata FLOOR count EVERY byte uniformly at
  -- TX_DATA_TOKEN_STANDARD(4) tokens (transactions.py: floor_tokens_in_calldata =
  -- ulen(tx.data) * 4), so a zero byte adds 4 * TX_DATA_TOKEN_FLOOR(16) = 64 to the
  -- floor, NOT the EIP-7623 zero=1-token weighting (the old 16). The zero/non-zero
  -- split survives only for the non-floor data_cost accumulator (x7). The old 16 here
  -- under-counted the floor by 48 per zero byte; the gate is `bltu x6, x10` (reject if
  -- gas < floor), so the under-count was a false-accept of floor-short txs.
  "  addi x10, x10, 64\n" ++
  ".runtime_tx_gas_data_step:\n" ++
  "  addi x9, x9, 1\n" ++
  "  addi x8, x8, -1\n" ++
  "  j .runtime_tx_gas_data_loop\n" ++
  ".runtime_tx_gas_create_words:\n" ++
  "  ld x8, -8(x5)\n" ++           -- x8 = is_creation
  "  beqz x8, .runtime_tx_gas_access_list\n" ++
  "  addi x12, x12, 31\n" ++
  "  srli x12, x12, 5\n" ++        -- ceil(calldata_len / 32)
  "  slli x12, x12, 1\n" ++        -- CODE_INIT_PER_WORD = 2
  "  add x7, x7, x12\n" ++
  ".runtime_tx_gas_access_list:\n" ++
  -- Access-list counts are supplied by transaction-aware callers. Legacy and
  -- standalone runtime probes leave both labels zero, preserving the old path.
  -- tokens_in_access_list = 80 * address_count + 128 * storage_key_count.
  -- Amsterdam regular intrinsic gas includes both the legacy access-list
  -- surcharge (3000/address, 3000/storage key) and the EIP-7623 access-token
  -- floor surcharge (16 gas per token); the separate floor accumulator keeps
  -- only the calldata-floor value used by the post-refund max.
  "  la x11, runtime_tx_access_list_address_count\n" ++
  "  ld x11, 0(x11)\n" ++
  "  beqz x11, .runtime_tx_gas_access_slots\n" ++
  "  li x15, 3000\n" ++
  ".runtime_tx_gas_addr_loop:\n" ++
  "  add x7, x7, x15\n" ++
  "  addi x7, x7, 1280\n" ++
  "  addi x10, x10, 1280\n" ++
  "  addi x11, x11, -1\n" ++
  "  bnez x11, .runtime_tx_gas_addr_loop\n" ++
  ".runtime_tx_gas_access_slots:\n" ++
  "  la x11, runtime_tx_access_list_storage_key_count\n" ++
  "  ld x11, 0(x11)\n" ++
  "  beqz x11, .runtime_tx_gas_check\n" ++
  "  li x15, 3000\n" ++
  "  li x14, 2048\n" ++
  ".runtime_tx_gas_slot_loop:\n" ++
  "  add x7, x7, x15\n" ++
  "  add x7, x7, x14\n" ++
  "  add x10, x10, x14\n" ++
  "  addi x11, x11, -1\n" ++
  "  bnez x11, .runtime_tx_gas_slot_loop\n" ++
  ".runtime_tx_gas_check:\n" ++
  -- Persist the EIP-7623 calldata floor (x10) so a caller (e.g. the
  -- block-verdict gas-result capture probe) can read the exact
  -- `calldata_floor_gas_cost` this transaction was validated against.
  -- Only the validate-tx-gas path reaches this label, so x10 is the
  -- computed floor here; x11 is free (it last held a calldata byte).
  "  la x11, runtime_tx_calldata_floor\n" ++
  "  sd x10, 0(x11)\n" ++
  -- v0.6.0 (EIP-2780): the per-authorization intrinsic is the
  -- state-independent REGULAR_PER_AUTH_BASE_COST 7816 only (the v0.5.0
  -- worst-case ACCOUNT_WRITE 8000 and the 218790/auth state reserve are
  -- gone -- the exact state-dependent charges arrive via the staged
  -- runtime_tx_auth_state_refund / runtime_tx_top_frame_regular_gas
  -- cells below).
  "  la x11, runtime_tx_auth_count\n" ++
  "  ld x9, 0(x11)\n" ++
  "  beqz x9, .runtime_tx_auth_regular_charge_done\n" ++
  "  li x11, 7816\n" ++
  "  mul x9, x9, x11\n" ++
  "  add x7, x7, x9\n" ++
  ".runtime_tx_auth_regular_charge_done:\n" ++
  "  la x11, runtime_tx_intrinsic_regular\n" ++
  "  sd x7, 0(x11)\n" ++
  "  bltu x6, x7, .exit_outofgas\n" ++
  "  bltu x6, x10, .exit_outofgas\n" ++
  "  sub x6, x6, x7\n" ++
  -- nxio8 (EIP-8037): split execution gas into gas_left and the state-gas
  -- reservoir (fork.py: gas = min(TX_MAX_GAS_LIMIT - intrinsic.regular,
  -- execution_gas); state_gas_reservoir = execution_gas - gas). x7 still holds
  -- the regular intrinsic cost; x6 = execution_gas. For tx.gas ≤ 16,777,216 the
  -- reservoir is 0 and gas_left is unchanged. evm_state_gas_left was reset to 0
  -- above, so the no-reservoir fall-through needs no store.
  "  li x8, 16777216\n" ++          -- TX_MAX_GAS_LIMIT (EIP-7825 cap)
  "  bgeu x7, x8, .exit_outofgas\n" ++   -- intrinsic.regular ≥ cap: spec-invalid tx
  "  sub x8, x8, x7\n" ++           -- x8 = regular gas budget
  "  bleu x6, x8, .runtime_tx_gas_no_reservoir\n" ++
  "  sub x9, x6, x8\n" ++           -- x9 = state_gas_reservoir
  "  mv x6, x8\n" ++                -- gas_left capped at the regular budget
  "  la x11, evm_state_gas_left\n" ++
  "  sd x9, 0(x11)\n" ++
  ".runtime_tx_gas_no_reservoir:\n" ++
  -- `interpreter.py:356` runs this preparation region only at depth zero.
  -- Cut C will route child frames through this entry; until then every live
  -- caller has depth zero, so this guard is intentionally a no-op. On the
  -- depth-zero path x28 is redefined by the deferred preparation callback;
  -- on the skip path it retains the depth, but the shared bootstrap has no
  -- x28 read before dispatch begins. There is no canonical x28 contract here:
  -- the depth-zero path already leaves either zero or that callback pointer.
  "  la x28, evm_call_depth\n" ++
  "  ld x28, 0(x28)\n" ++
  "  bnez x28, .runtime_tx_top_level_message_d0_done\n" ++
  emitTopLevelMessageD0Preparation ++
  ".runtime_tx_top_level_message_d0_done:\n" ++
  -- This is the last depth-zero-only operation before `process_message`:
  -- process_transaction, not process_message, materializes the transaction's
  -- up-front sender gas debit.  Keep it above the child entry so a future
  -- child frame cannot charge the transaction's gas a second time.
  "  addi sp, sp, -16; sd ra, 0(sp); jal ra, dispatcher_seed_pending_upfront_sender_balance\n" ++
  -- The root arm takes an explicit jump rather than falling through its own
  -- body setup.  Child frames enter at `runtime_tx_child_message_entry`, below
  -- this root-only capture/value seed and stack/memory bootstrap.
  "  j .runtime_tx_shared_message_body\n" ++
  ".runtime_tx_shared_message_body:\n" ++
  -- Snapshot and pending-value staging remain the existing root path.  The
  -- child uses its current frame-local setup until the later migration.
  "  jal ra, dispatcher_capture_body_state; jal ra, dispatcher_seed_pending_value_transfer; ld ra, 0(sp); addi sp, sp, 16\n" ++
  "  mv x10, x21\n" ++
  "  la x12, evm_stack_top\n" ++
  "  la x5, evm_cur_stack_top; sd x12, 0(x5)\n" ++
  "  la x5, evm_stack_low; la x6, evm_cur_stack_low; sd x5, 0(x6)\n" ++
  "  la x13, evm_memory"

def emitRuntimeDispatcherSetup : String :=
  emitRuntimeDispatcherSetupWithInputAsm
    ("  li x10, 0x40000010\n" ++   -- INPUT_ADDR + INPUT_DATA_OFFSET
     "  li x21, 0x40000010\n")     -- M15: preserved code base (mirrors x10 init)

def emitRuntimeDispatcherCallableSetup : String :=
  -- The callable dispatcher executes one transaction in the stateless guest.
  -- Reset every auxiliary transaction journal before its dispatch.  The
  -- standalone prologue does the same; retaining any of these across callable
  -- invocations lets a preceding transaction alter the next transaction's
  -- execution evidence.
  "  la x5, evm_refund_acc; sd x0, 0(x5)\n" ++
  "  la x5, evm_selfdestruct_staged; sd x0, 0(x5)\n" ++
  "  la x5, evm_selfdestruct_seen_count; sd x0, 0(x5)\n" ++
  "  la x5, evm_selfdestruct_seen_overflow; sd x0, 0(x5)\n" ++
  "  la x5, evm_selfdestruct_destroyed_count; sd x0, 0(x5)\n" ++
  "  la x5, evm_selfdestruct_destroyed_overflow; sd x0, 0(x5)\n" ++
  "  la x5, cd_destroyed_empty_hits; sd x0, 0(x5)\n" ++
  "  la x5, create_nonce_table_count; sd x0, 0(x5)\n" ++
  "  la x5, create_nonce_table_overflow; sd x0, 0(x5)\n" ++
  "  la x5, create_nonce_undo_count; sd x0, 0(x5)\n" ++
  "  la x5, code_state_mtx_active; ld x6, 0(x5); bnez x6, .Lrtdc_code_log_kept\n" ++
  "  la x5, exec_code_effect_count; sd x0, 0(x5)\n" ++
  "  la x5, exec_code_effect_next; sd x0, 0(x5)\n" ++
  "  la x5, exec_code_effect_overflow; sd x0, 0(x5)\n" ++
  ".Lrtdc_code_log_kept:\n" ++
  "  la x5, account_state_pending_count; sd x0, 0(x5)\n" ++
  "  la x5, account_state_created_count; sd x0, 0(x5)\n" ++
  "  la x5, account_state_delete_count; sd x0, 0(x5)\n" ++
  "  la x5, account_state_overflow; sd x0, 0(x5)\n" ++
  "  la x5, evm_log_data_used; sd x0, 0(x5)\n" ++
  "  la x5, evm_log_data_overflow; sd x0, 0(x5)\n" ++
  emitRuntimeDispatcherSetupWithInputAsm
    ("  la x5, runtime_dispatcher_input_ptr\n" ++
     "  ld x6, 0(x5)\n" ++
     "  beqz x6, .Lruntime_dispatcher_default_input\n" ++
     "  mv x10, x6\n" ++
     "  mv x21, x6\n" ++
     "  j .Lruntime_dispatcher_input_ready\n" ++
     ".Lruntime_dispatcher_default_input:\n" ++
     "  li x10, 0x40000010\n" ++
     "  li x21, 0x40000010\n" ++
     ".Lruntime_dispatcher_input_ready:\n")


/-- Runtime dispatcher fetch/decode/dispatch loop. Shared by the standalone
    runtime dispatcher and the callable wrapper. -/
def emitRuntimeDispatcherLoop (depthAwareStop : Bool := false) : String :=
  "  mv x10, x21\n" ++
  "  la x12, evm_stack_top\n" ++
  "  la x5, evm_cur_stack_top; sd x12, 0(x5)\n" ++
  "  la x5, evm_stack_low; la x6, evm_cur_stack_low; sd x5, 0(x6)\n" ++
  "  la x13, evm_memory\n" ++
  ".dispatch_loop:\n" ++
  emitDispatchLoopCodeSizeStopGuard depthAwareStop ++
  "  lbu x5, 0(x10)\n" ++
  "  slli x5, x5, 3\n" ++           -- x5 = opcode * 8 (index for both tables)
  -- M30 gas charge: look up the opcode's static cost, charge it against
  -- env.gasRemaining (env+568), and route to .exit_outofgas if it would
  -- underflow. Charge-then-execute matches the spec's `charge_gas` order
  -- (so e.g. GAS reflects its own cost already deducted). x6/x7 are
  -- per-iteration scratch; x5 (opcode*8) survives for the dispatch below.
  "  la x6, opcode_gas_costs\n" ++
  "  add x6, x6, x5\n" ++
  "  ld x6, 0(x6)\n" ++             -- x6 = static gas cost
  "  ld x7, 568(x20)\n" ++          -- x7 = gas remaining
  "  bltu x7, x6, .exit_outofgas\n" ++
  "  sub x7, x7, x6\n" ++
  "  sd x7, 568(x20)\n" ++          -- gasRemaining -= cost
  "  la x6, opcode_handlers\n" ++
  "  add x6, x6, x5\n" ++
  "  ld x7, 0(x6)\n" ++
  "  jalr x1, x7, 0\n" ++
  emitDispatchResume

/-- Runtime dispatcher prologue: setup plus fetch/decode/dispatch loop. -/
def emitRuntimeDispatcherPrologue : String :=
  emitRuntimeDispatcherSetup ++ "\n" ++
  emitRuntimeDispatcherLoop

/-- bmvmx.1.6.4.2: nested-callee storage seed loop, run AFTER the callable setup
    (recipient preload-expand + #8561 re-tag + env ready) and BEFORE the dispatch
    loop. For each `callee_seed_table` entry (96 B: addrHash:32, key:32, value:32)
    it appends one 128 B persistent-exec-log entry (addrHash, slotKey, original=value,
    current=value — mirrors `exec_log_append_storage_seed`) and bumps
    env.persistentLogLength (env+448), so a nested callee's SLOAD finds its witness
    value instead of cold 0. `callee_seed_count` is 0 for every current caller (the
    top-level guest uses a different prologue; the verdict has not populated the table
    yet), so this is INERT — depth-0 / recipient behaviour is byte-identical. The
    enumeration that fills the table is 1.6.4.2.b (dispatch_tx_runtime_code). Uses only
    x5/x6/x7 (the dispatch loop re-inits them each iteration) and x28..x31 temps; never
    touches x10/x12/x13/x20/x21. -/
def emitCalleeStorageSeedLoop : String :=
  "  la x5, callee_seed_count; ld x6, 0(x5)\n" ++
  "  beqz x6, .Lcallee_seed_done\n" ++
  "  la x7, callee_seed_table\n" ++          -- x7 = src entry ptr (96 B stride)
  "  li x28, 0xa0630000\n" ++                -- x28 = persistent exec-log base
  ".Lcallee_seed_loop:\n" ++
  "  beqz x6, .Lcallee_seed_done\n" ++
  "  ld x29, 448(x20)\n" ++                  -- x29 = current entry count
  "  la x5, exec_log_seed_flag; add x5, x5, x29; li x31, 1; sb x31, 0(x5)\n" ++
  "  slli x30, x29, 7; add x30, x28, x30\n" ++   -- x30 = entry ptr = base + count*128
  -- addrHash src[0..32] -> entry[0..32]
  "  ld x31, 0(x7);  sd x31, 0(x30)\n" ++
  "  ld x31, 8(x7);  sd x31, 8(x30)\n" ++
  "  ld x31, 16(x7); sd x31, 16(x30)\n" ++
  "  ld x31, 24(x7); sd x31, 24(x30)\n" ++
  -- slotKey src[32..64] -> entry[32..64]
  "  ld x31, 32(x7); sd x31, 32(x30)\n" ++
  "  ld x31, 40(x7); sd x31, 40(x30)\n" ++
  "  ld x31, 48(x7); sd x31, 48(x30)\n" ++
  "  ld x31, 56(x7); sd x31, 56(x30)\n" ++
  -- value src[64..96] -> original entry[64..96] AND current entry[96..128]
  "  ld x31, 64(x7); sd x31, 64(x30);  sd x31, 96(x30)\n" ++
  "  ld x31, 72(x7); sd x31, 72(x30);  sd x31, 104(x30)\n" ++
  "  ld x31, 80(x7); sd x31, 80(x30);  sd x31, 112(x30)\n" ++
  "  ld x31, 88(x7); sd x31, 88(x30);  sd x31, 120(x30)\n" ++
  "  addi x29, x29, 1; sd x29, 448(x20)\n" ++    -- bump persistentLogLength
  "  addi x7, x7, 96; addi x6, x6, -1; j .Lcallee_seed_loop\n" ++
  ".Lcallee_seed_done:\n"

/-- coc3g.5 multi-hop: seed the EIP-7702 RECOVERED-AUTHORITY warm set from the
    pending authorization_list span. The span/fn are prepared by
    `dispatch_tx_runtime_code` and cleared one-shot here; standalone callers leave
    them zero so this is inert. Runs after callable setup resets
    `evm_access_account_count` (so the seed persists into execution) and before
    opcode execution. eip7702_warm_recovered_authorities applies the EXACT spec
    `validate_authorization` warming gate (chain_id, nonce<MAX, valid signature). -/
def emitTxAuthListWarmLoop : String :=
  "  la x5, runtime_tx_auth_list_ptr; ld a0, 0(x5)\n" ++
  "  la x6, runtime_tx_auth_list_len; ld a1, 0(x6)\n" ++
  "  la x7, runtime_tx_auth_warm_fn; ld x28, 0(x7)\n" ++
  "  sd x0, 0(x5); sd x0, 0(x6); sd x0, 0(x7)\n" ++
  "  beqz x28, .Ltx_auth_warm_done\n" ++
  "  beqz a0, .Ltx_auth_warm_done\n" ++
  "  beqz a1, .Ltx_auth_warm_done\n" ++
  "  jalr ra, x28, 0\n" ++
  "  # warm failure is conservative: a missed authority warm over-charges gas.\n" ++
  ".Ltx_auth_warm_done:\n" ++
  "  mv x10, x21\n"

/-- Callable runtime dispatcher entry. The dispatcher loop uses `ra` for
    opcode-handler calls, so the caller's return address is saved in the
    runtime data section and restored by the callable exit join. -/
def emitRuntimeDispatcherCallablePrologue (depthAwareStop : Bool := false) : String :=
  -- `runtime_dispatcher_prepare_only` shares the ordinary callable setup and
  -- exits at the post-preparation seam above.
  "runtime_dispatcher_prepare_only:\n" ++
  -- Mark entered before setup.  A prefix OOG takes the ordinary exceptional
  -- exit and leaves this at 1; only the explicit prefix-return writes 2.
  "  la x5, runtime_tx_prepare_prefix_status; li x6, 1; sd x6, 0(x5)\n" ++
  "  la x5, runtime_tx_prepare_only; li x6, 1; sd x6, 0(x5)\n" ++
  "  j runtime_dispatcher_call\n" ++
  "runtime_dispatcher_prepare_only_return:\n" ++
  "  la x5, runtime_dispatcher_caller_sp; ld sp, 0(x5)\n" ++
  "  la x5, runtime_dispatcher_caller_ra; ld ra, 0(x5)\n" ++
  "  ret\n" ++
  "runtime_dispatcher_call:\n" ++
  "  la x5, runtime_dispatcher_caller_ra\n" ++
  "  sd ra, 0(x5)\n" ++
  -- L3 (bmvmx.1.2.4.6.1): save caller sp before setup clobbers it with lp64_sp_top.
  "  la x5, runtime_dispatcher_caller_sp\n" ++
  "  sd sp, 0(x5)\n" ++
  emitRuntimeDispatcherCallableSetup ++ "\n" ++
  -- A top-level CREATE seeds its own nonce to one before executing initcode.
  -- BlockVerdictCreationStage marks that frame before entering this callable
  -- dispatcher, but this setup deliberately resets the per-transaction CREATE
  -- nonce table. Seed only after that reset: a nested CREATE in the constructor
  -- must derive from the top-level created account's live nonce (1), not its
  -- header-state nonce (usually 0). Non-creation callers leave the marker zero.
  "  addi sp, sp, -16\n  sd x10, 0(sp)\n" ++
  "  la t0, create_frame_flag; ld t1, 0(t0); beqz t1, .Lrtd_top_create_nonce_done\n" ++
  "  la a0, create_address_be; jal ra, create_creator_nonce_seed_one\n" ++
  ".Lrtd_top_create_nonce_done:\n" ++
  "  ld x10, 0(sp); addi sp, sp, 16\n" ++
  "  jal ra, dispatcher_reemit_pending_tl\n" ++
  emitTxAuthListWarmLoop ++ "\n" ++
  emitCalleeStorageSeedLoop ++ "\n" ++
  emitRuntimeDispatcherLoop depthAwareStop

/-- Callable runtime dispatcher text body. This is used both by standalone
    probes and by larger guests that need `runtime_dispatcher_call` linked as
    a subroutine while retaining their own `_start` entry path. -/
def emitRuntimeDispatcherCallableCore
    (registry : List OpcodeHandlerSpec)
    (exitBody : Program) : String :=
  emitRuntimeDispatcherCallablePrologue ++ "\n" ++
  emitDispatcherCallableEpilogue registry exitBody


-- Callable runtime dispatcher text for embedding into a guest that already
-- links the shared helper functions used by opcode handlers.
/-- Runtime-specific helper functions needed when embedding the runtime
    dispatcher into `stateless_guest`. The guest already links the shared
    hash/RLP/MPT/account base helpers, so this list intentionally contains only
    runtime opcode support functions and safe-fail precompile wrappers. -/
def emitRuntimeDispatcherEmbeddedHelperFunctions : String :=
  balanceAtHeaderStateRootFunction ++ "\n" ++
  nonceAtHeaderStateRootFunction ++ "\n" ++
  accountExistsAtHeaderStateRootFunction ++ "\n" ++
  accountIsEmptyAtHeaderStateRootFunction ++ "\n" ++
  extcodehashAtHeaderStateRootFunction ++ "\n" ++
  extcodecopyAtHeaderStateRootFunction ++ "\n" ++
  runtimeSameBlockDelegationCodeFunction ++ "\n" ++
  hasCodeOrNonceAtHeaderStateRootFunction ++ "\n" ++
  createStageInitcodeFrameRuntimeFunction ++ "\n" ++
  createExecuteInitcodeFrameRuntimeFunction ++ "\n" ++
  createDeployedCodeValidFunction ++ "\n" ++
  createRecordCodeEffectFunction ++ "\n" ++
  findCodeEffectByAddressFunction ++ "\n" ++
  accountStateFindFunction ++ "\n" ++
  accountStateCopyFunction ++ "\n" ++
  accountStateAppendPendingFunction ++ "\n" ++
  accountStateUpsertDurableFunction ++ "\n" ++
  codeStateFinalBalanceNonzeroFunction ++ "\n" ++
  accountStateCommitPendingFunction ++ "\n" ++
  accountStatePromoteDeleteReadsFunction ++ "\n" ++
  accountStateRecordNonstorageFunction ++ "\n" ++
  accountStateRecordCodeFunction ++ "\n" ++
  accountStateRecordAuthFunction ++ "\n" ++
  accountStatePublishSenderInclusionFunction ++ "\n" ++
  accountStateAuthCurrentFunction ++ "\n" ++
  accountStateLatestBalanceFunction ++ "\n" ++
  accountStateLatestNonceFunction ++ "\n" ++
  accountStateLookupCurrentFunction ++ "\n" ++
  accountStateCreatedContainsFunction ++ "\n" ++
  codeStateLookupCurrentFunction ++ "\n" ++
  codeStateAddressSetInsertFunction ++ "\n" ++
  codeStateAddressSetFlagFunction ++ "\n" ++
  createCreatorNonceUseFunction ++ "\n" ++
  zkvmModexpBackendImpl ++ "\n" ++
  emitModexpBnScratchData ++ "\n" ++
  ".section .text\n" ++ "\n" ++
  -- Real RIPEMD160 (0x03) software kernel for the guest closures
  -- (the guest provides `zkvm_sha256` itself, but `zkvm_ripemd160`
  -- only exists here and in the shared-helpers epilogue branch).
  zkvmRipemd160Function ++ "\n" ++
  storageAccessGasFunction ++ "\n" ++
  sstoreGasRefundOutcomeFunction ++ "\n" ++
  dispatcherTxGasSettleFunction ++ "\n" ++
  runtimeAccessAccountSeedFunction ++ "\n" ++
  runtimeAccessSeedInitialAccountsFunction ++ "\n" ++
  runtimeAccessAccountChargeFunction ++ "\n" ++
  selfdestructBalanceTransferFunction ++ "\n" ++
  eip7708SyntheticLogFunctions ++ "\n" ++
  messageValueTransferFunction ++ "\n" ++
  -- Real BLS12-381 G1 ADD/MSM kernels (see the shared-helpers branch note).
  bls12G1PrecompileFunctions ++ "\n" ++
  -- Real BN254 ecAdd/ecMul/ecPairing kernels (0x06/0x07/0x08); see the
  -- standalone-epilogue emission site for the wrapper-replacement rationale.
  bn254PrecompileFunctions ++ "\n" ++
  bn254PairingKernelFunctions ++ "\n" ++
  -- Real BLAKE2F kernel (see the shared-helpers branch note).
  blake2fKernelFunctions ++ "\n" ++
  -- Real KZG point-evaluation kernel (see the shared-helpers branch note).
  bls12KzgKernelFunctions ++ "\n" ++
  -- Real P256VERIFY kernel (see the shared-helpers branch note).
  p256VerifyKernelFunctions ++ "\n" ++
  -- Real BLS12-381 G2 ADD/MSM kernels (see the shared-helpers branch note).
  bls12G2PrecompileFunctions ++ "\n" ++
  -- Real BLS12-381 pairing kernel (see the shared-helpers branch note).
  bls12PairingKernelFunctions ++ "\n" ++
  -- Real BLS12-381 map precompiles (see the shared-helpers branch note).
  bls12MapKernelFunctions ++ "\n" ++
  -- Call-frame switching primitives (beads .61.4/.61.5, layout #8516/#8517).
  -- Linked into the guest so the CALL/CREATE child-frame descent (.61.6/.61.8)
  -- can call them. `frame_base` resolves `call_frame_arena` (the guest verdict
  -- data already defines it; BlockVerdictDataSection); `frame_depth_*` and
  -- `frame_*_regs` resolve `evm_call_depth` / `frame_save_area` added to the
  -- embedded helper data below. Inert until a CALL handler increments depth —
  -- depth-0 execution is byte-identical.
  frameBaseFunction ++ "\n" ++
  frameDepthPushFunction ++ "\n" ++
  frameDepthPopFunction ++ "\n" ++
  frameSaveRegsFunction ++ "\n" ++
  frameLoadRegsFunction ++ "\n" ++
  -- Descent/return orchestration (.61.6, #8520-#8527). `call_frame_descend`
  -- performs the CALL/STATICCALL child-frame switch; `frame_return` pops a frame
  -- and resumes the parent dispatch loop. They compose the
  -- `call_frame_enter`/`set_call_env`/`set_calldata`/`forward_gas` primitives,
  -- linked here too. Inert until a CALL handler descends (depth stays 0). The
  -- `frame_call_ctx` return-context they use is in the embedded helper data below.
  callFrameEnterFunction ++ "\n" ++
  callFrameSetCallEnvFunction ++ "\n" ++
  callFrameSetCalldataFunction ++ "\n" ++
  callFrameForwardGasFunction ++ "\n" ++
  callFrameDescendFunction ++ "\n" ++
  createFrameDescendFunction ++ "\n" ++   -- .61.8.3.5.1: CREATE-frame descent (reuses call_frame_descend)
  recordNonstorageEffectFunction ++ "\n" ++   -- i3djw.1: per-account non-storage effect producer (CALL value-transfer)
  nonstorageEffectLatestBalanceFunction ++ "\n" ++   -- yisv8 .spine.1: live-BALANCE read of the latest effect post_balance
  nonstorageEffectLatestNonceFunction ++ "\n" ++   -- bmvmx.5.5.10: live-NONCE read (CREATE seed threading)
  nonstorageEffectAggregateFunction ++ "\n" ++   -- bmvmx.5.5.7.3: O(N) per-account effect aggregation (block_verdict tail)
  frameReturnFunction ++ "\n" ++
  sparseWindowReadFunction ++ "\n" ++   -- evm-asm-0w05f.13: depth-1+ RETURN/REVERT window materialization
  sparseWindowWriteFunction   -- evm-asm-0w05f.13 surface 2: nested-caller out-window write-back

def emitRuntimeDispatcherCallableCoreSharedHelpers
    (registry : List OpcodeHandlerSpec)
    (exitBody : Program) : String :=
  emitRuntimeDispatcherCallablePrologue true ++ "\n" ++
  emitRuntimeDispatcherEmbeddedHelperFunctions ++ "\n" ++
  emitDispatcherCallableEpilogueSharedHelpers registry exitBody

/-- Runtime-only scratch labels for embedding the dispatcher in
    `stateless_guest`. Base hash/RLP/MPT/account scratch labels are omitted
    because the guest already links them. -/
def emitRuntimeDispatcherEmbeddedHelperData : String :=
  ".balign 32\n" ++
  "bal_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "bal_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "bal_addr_padded:\n  .zero 32\n" ++   -- yisv8 .spine.2: padded query addr for the live-balance scan
  ".balign 32\n" ++
  "bal_output_scratch:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "aex_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "aex_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "aie_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "aie_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "aex_predicate:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aie_predicate:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "sdai_status:\n" ++
  "  .zero 8\n" ++
  "sdai_origin_len:\n" ++
  "  .zero 8\n" ++
  "sdai_beneficiary_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "sdai_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "sdai_origin_address:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "sdai_origin_rlp:\n" ++
  "  .zero 256\n" ++
  ".balign 32\n" ++
  "sdai_beneficiary_rlp:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "sdai_transfer_status:\n" ++
  "  .zero 8\n" ++
  "sdai_transfer_origin_len:\n" ++
  "  .zero 8\n" ++
  "sdai_transfer_beneficiary_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "sdai_transfer_output:\n" ++
  "  .zero 256\n" ++
  ".balign 32\n" ++
  "sdbt_delta32:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "eahsr_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "eahsr_address_scratch:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "eahsr_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "eahsr_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70\n" ++
  ".balign 32\n" ++
  "ecc_address_scratch:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ecc_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ecc_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "eccp_codes_ptr:\n" ++
  "  .zero 8\n" ++
  "eccp_codes_len:\n" ++
  "  .zero 8\n" ++
  "ecc_match_offset:\n" ++
  "  .zero 8\n" ++
  "ecc_match_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "ecc_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70\n" ++
  ".balign 32\n" ++
  "nonce_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "nonce_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "create_nonce:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "create_init_offset:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "create_init_size:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "create_sender_be:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "create_salt_be:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "create_address_be:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "create_value_be:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "create_balance_be:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "create_creator_newbal:\n" ++
  "  .zero 32\n" ++
  emitCreateChildFrameData ++
  ".balign 8\n" ++
  "hcon_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "hcon_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "hcon_predicate:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "hcon_empty_trie_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21\n" ++
  ".balign 32\n" ++
  "hcon_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70\n" ++
  -- Call-frame switching state (beads .61.4/.61.5, #8517). `evm_call_depth` is
  -- the EVM call-depth counter (0 at top level; bumped by CALL/CREATE descent in
  -- .61.6+); `frame_save_area` is the uniform per-depth saved (pc, codebase) area
  -- (1025 entries × 16 B), indexed by depth 0..1024. These back the
  -- frame_depth_push/pop and frame_save_regs/load_regs helpers linked above.
  -- `call_frame_arena` itself lives in the guest verdict data
  -- (BlockVerdictDataSection, a standalone block after basr_accounts).
  ".balign 8\n" ++
  "evm_call_depth:\n" ++
  "  .zero 8\n" ++
  -- 4ch8f.10.3: handler-tail routing flag (0 = continue the dispatch loop;
  -- nonzero routing code read+reset by `.Ldispatch_resume`). See the
  -- flag+`ret` discipline note near `HandlerTail`.
  ".balign 8\n" ++
  "evm_halt_flag:\n" ++
  "  .zero 8\n" ++
  ".balign 16\n" ++
  "frame_save_area:\n" ++
  "  .zero 16400\n" ++
  -- `frame_call_ctx` (.61.6.6, #8527): the per-CHILD-depth call-return context
  -- (parent_x12, outOff_abs, outSize, netPopBytes) saved by `call_frame_descend`
  -- and consumed by `frame_return` (1025 entries × 32 B). Indexed by child depth.
  ".balign 32\n" ++
  "frame_call_ctx:\n" ++
  "  .zero 32800\n" ++
  -- `frame_parent_bases`: exact parent memory/env bases by CHILD depth. Depth 0
  -- can be a staged stateless replay buffer rather than the global labels.
  ".balign 16\n" ++
  "frame_parent_bases:\n" ++
  "  .zero 16400\n" ++
  -- Call descriptor + zero value word filled by the CALL descent
  -- (`callDescendFallThrough`) and consumed by `call_frame_descend`.
  ".balign 8\n" ++
  "cd_desc:\n  .zero 96\n" ++
  ".balign 32\n" ++
  "cd_zero_word:\n  .zero 32\n" ++
  -- Scratch for the value-bearing CALL balance gate (`callDescendFallThrough`):
  -- the caller address (env+0) as canonical 20-byte big-endian, and the call
  -- value + looked-up caller balance as 32-byte big-endian for the compare.
  ".balign 8\n" ++
  "cd_caller_be:\n  .zero 32\n" ++
  "cd_value_be:\n  .zero 32\n" ++
  "cd_balance_be:\n  .zero 32\n" ++
  "cd_caller_newbal:\n  .zero 32\n" ++
  -- nxio8.8: the CALL callee (`to`) as canonical 20-byte big-endian, for the
  -- EIP-8037 new-account state-gas check (is_account_alive(to)) in callDescendFallThrough.
  "cd_callee_be:\n  .zero 32\n" ++
  -- coc3g.5/.7: EIP-7702 nested-CALL delegation-follow target (the single-hop delegated
  -- address extracted from a 0xef0100||addr marker), so the nested CALL runs the TARGET's
  -- code (mirroring #9078's dtrc-path follow) instead of routing to .Lcd_fail.
  "cd_deleg_target:\n  .zero 32\n" ++
  -- fva3w: per-CALL flag set when a non-self value transfer needs an EIP-7708 Transfer log;
  -- the emit is DEFERRED (child env on descend so a revert rolls it back; parent env on the
  -- empty-callee path, committed). One-shot: cleared at CALL entry and on emit.
  "cd_xfer_log_pending:\n  .zero 8\n" ++
  -- bbow4.2.5.8: one-shot flag set when CALL/CALLCODE charged the 10300 value-transfer gas
  -- before NEW_ACCOUNT state gas. Descend consumes it to avoid a double charge; empty paths
  -- refund the 2300 stipend and clear it.
  "cd_xfer_gas_precharged:\n  .zero 8\n" ++
  "cd_new_account_charged_current:\n  .zero 8\n" ++
  "cd_callee_alive_before_value:\n  .zero 8\n" ++
  "cd_destroyed_empty_hits:\n  .zero 8\n"

/-- Runtime-bytecode `.data` section. Drops the `evm_code:` block
    (no baked bytecode); everything else matches the `.data`-baked
    variant. The static EVM stack arena is sized for the protocol
    1024-word stack depth. -/
def emitRuntimeDispatcherDataSectionCore
    (registry : List OpcodeHandlerSpec)
    (includeKeccakScratch includeSharedHelperData : Bool) : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "runtime_dispatcher_caller_ra:\n" ++
  "  .zero 8\n" ++
  "runtime_dispatcher_caller_sp:\n" ++
  "  .zero 8\n" ++
  "runtime_dispatcher_input_ptr:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_access_list_ptr:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_access_list_len:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_access_list_seed_fn:\n" ++
  "  .zero 8\n" ++
  -- coc3g.5 multi-hop: EIP-7702 authorization_list span for the post-reset
  -- recovered-authority warm seeding (populated by dispatch_tx_runtime_code,
  -- consumed by emitTxAuthListWarmLoop; zero default keeps standalone callers inert).
  "runtime_tx_auth_list_ptr:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_auth_list_len:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_auth_warm_fn:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_auth_count:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_auth_exec_fn:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_state_gas_ptr:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_auth_inner_ptr:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_auth_inner_len:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_auth_sender_ptr:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_auth_type:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_auth_state_refund:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_auth_state_charge:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_auth_regular_refund:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_create_state_charge:\n" ++
  "  .zero 8\n" ++
  runtimeSameBlockDelegationCodeData ++
  ".balign 8\n" ++
   -- t1iqb: 64-byte zero-pad staging window for the VERIFIED arena-free
   -- CALLDATALOAD (h_CALLDATALOAD body = evm_calldataload_staged). The staging
   -- loop writes the 32-byte window into bytes [0,32); the window ladder reads a
   -- calldataRegionIs footprint (window ++ 32-byte zero pad) = 64 bytes, so the
   -- buffer is 64 bytes with the tail [32,64) statically zero (.balign 8 above
   -- keeps it dword-aligned, matching the proof's buf%8=0 / tail-zero precond).
   -- Used transiently within one opcode dispatch (no re-entrancy: the dispatcher
   -- runs one opcode at a time), so a single static buffer is sound.
   "bv_cdl_stage:\n  .zero 64\n" ++
   -- coc3g.9.3 (#9458 follow-up, bv_fail=53): EMPTY_CODE_HASH (keccak "") for the
   -- callDescendFallThrough empty-code-EOA routing fix. status 5 from
   -- code_at_header_state_root means code_hash not in witness.codes; for an
   -- EXISTING EOA that code_hash is EMPTY_CODE_HASH, so the call is a valid
   -- empty-code callee (not a witness miss). ChildFrameHandlers.Lcd_callee_nocreate_
   -- compares cahsr_acct_struct.code_hash against this constant.
   ".balign 32\n" ++
   "cd_empty_code_hash:\n" ++
   "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
   "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
   "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
   "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70\n" ++
  ".balign 8\n" ++
  "txal_type:\n  .zero 8\n" ++
  "txal_inner_off:\n  .zero 8\n" ++
  "txal_span_ptr:\n  .zero 8\n" ++
  "txal_span_len:\n  .zero 8\n" ++
  "t29_offset:\n  .zero 8\n" ++
  "t29_length:\n  .zero 8\n" ++
  "t1d_offset:\n  .zero 8\n" ++
  "t1d_length:\n  .zero 8\n" ++
  "t77_offset:\n  .zero 8\n" ++
  "t77_length:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "txal_decode:\n  .zero 248\n" ++
  seedTxAccessListDataSection ++ "\n" ++
  -- EIP-7623 calldata floor persisted by the validate-tx-gas path so a
  -- caller can read the exact `calldata_floor_gas_cost` the transaction
  -- was validated against (0 when --validate-tx-gas was not requested).
  "runtime_tx_calldata_floor:\n" ++
  "  .zero 8\n" ++
  -- Nonzero only while a top-level CREATE is being dispatched: its transaction
  -- data is initcode, whereas its EVM frame calldata is empty.
  "runtime_tx_intrinsic_data_ptr:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_intrinsic_data_len:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_intrinsic_regular:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_top_frame_regular_gas:\n" ++
  "  .zero 8\n" ++
  -- Formerly known as `runtime_tx_auth_phase_applied`: this marker records
  -- reaching the post-preparation coverage point, not auth application.
  "runtime_tx_post_preparation_reached:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_post_top_frame_fn:\n" ++
  "  .zero 8\n" ++
  -- Split-call controls.  `prepare_only` is one-shot and is consumed only
  -- after the auth/preparation gas boundary succeeds; `resume_code_ptr` is
  -- written by the block verdict after it has authenticated recipient code.
  "runtime_tx_prepare_only:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_prepare_prefix_status:\n" ++
  "  .zero 8\n" ++
  -- Access-list cardinalities for tx-gas validation. Transaction-aware callers
  -- write these before `runtime_dispatcher_call`; zero defaults preserve legacy
  -- and standalone runtime inputs.
  "runtime_tx_access_list_address_count:\n" ++
  "  .zero 8\n" ++
  "runtime_tx_access_list_storage_key_count:\n" ++
  "  .zero 8\n" ++
  -- bmvmx.1.6.4.2: nested-callee storage seed table consumed by the callable
  -- dispatcher prologue's seed loop. `callee_seed_count` is 0 by default, so the
  -- loop is inert (depth-0 / recipient behaviour byte-identical) until the verdict's
  -- dispatch_tx_runtime_code (1.6.4.2.b) enumerates every non-recipient BAL account's
  -- storage into the table (count × 96 B: addrHash:32, key:32, value:32).
  ".balign 8\n" ++
  "callee_seed_count:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "callee_seed_table:\n" ++
  "  .zero 12288\n" ++   -- up to 128 entries × 96 B
  -- bmvmx.1.6.3 refund accumulation (claude-c1's lane per c2 split). evm_refund_acc is
  -- the running per-tx EIP-3529 refund counter (signed i64): the SSTORE handler adds each
  -- SSTORE's refund delta (from sstore_gas_refund_outcome) on append; reset to 0 at
  -- dispatcher setup. srfd_zero is the zero original/current buffer for a missing slot;
  -- srfd_out is the helper's output. Surfaced into the block-verdict runtime refund
  -- counter (bv_runtime_refund_counter / bv_mtx_refund), making the per-tx receipt-gas
  -- increment (receipt_inc) exact; the EIP-7778 block-gas gate stays refund-independent.
  ".balign 8\n" ++
  "evm_refund_acc:\n" ++
  "  .zero 8\n" ++
  -- .62.2.5: ECRECOVER backend surface. `ecrecover_backend_ptr` holds the
  -- address of `secp256k1_recover_pubkey_staged` when the linking closure arms
  -- it (the stateless guest in dispatch_tx_runtime_code; the focused probe in
  -- its prologue); 0 keeps the legacy empty-returndata success without linking
  -- the secp256k1 chain. ecr_abi/ecr_pubkey/ecr_hash are the staged recovery
  -- block, recovered key, and keccak output.
  ".balign 8\n" ++
  "ecrecover_backend_ptr:\n" ++
  "  .zero 8\n" ++
  "ecr_abi:\n" ++
  "  .zero 128\n" ++
  "ecr_pubkey:\n" ++
  "  .zero 64\n" ++
  "ecr_hash:\n" ++
  "  .zero 32\n" ++
  -- BN254 ecAdd/ecMul kernel constants + accelerator staging + the
  -- failed-call allotment cell (`bn254_allot_rest`), paired with
  -- `bn254PrecompileFunctions` in the dispatcher text.
  bn254FieldDataFragment ++
  bn254CurveDataFragment ++
  bls12FieldDataFragment ++
  bls12G1DataFragment ++
  bls12G2DataFragment ++
  bls12PairingAllDataFragments ++
  bls12MapDataFragment ++
  bls12KzgDataFragment ++
  blake2fDataFragment ++
  p256VerifyDataFragment ++
  bn254PairingAllDataFragments ++
  -- nxio8: EIP-8037 state-gas cells. `evm_state_gas_left` is the per-tx state-gas
  -- reservoir (fork.py: state_gas_reservoir = execution_gas - min(TX_MAX_GAS_LIMIT
  -- - intrinsic.regular, execution_gas); 0 for tx.gas ≤ 16,777,216). The SSTORE
  -- handler's charge_state_gas drains it first and spills the remainder into
  -- env.gasRemaining (vm/gas.py charge_state_gas). `evm_state_gas_spilled` tracks
  -- the portion drawn from gas_left so child-error rollback can refill gas_left
  -- before the reservoir, matching execution-specs `refill_frame_state_gas`.
  -- `evm_state_gas_used` accumulates charges. Settlement (spec: tx.gas -
  -- gas_left - state_gas_left) folds the final state_gas_left back via
  -- dispatcher_tx_gas_settle. Reset per dispatch call.
  ".balign 8\n" ++
  "evm_state_gas_left:\n" ++
  "  .zero 8\n" ++
  "evm_state_gas_used:\n" ++
  "  .zero 8\n" ++
  "evm_state_gas_spilled:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "srfd_zero:\n" ++
  "  .zero 32\n" ++
  "srfd_out:\n" ++
  "  .zero 40\n" ++
  -- bmvmx.1.6.6 enabler: per-entry block_access_index, PARALLEL to the 128 B exec-log
  -- entries at 0xa0630000 (so the existing scans are byte-identical). exec_log_txindex[i]
  -- = the tx's block_access_index for persistent-log entry i; the SSTORE handler stamps
  -- it on append. `current_block_access_index` defaults to 1 (single-tx); the multi-tx
  -- loop overwrites it per tx (system txs = 0). Sized to the persistent-log capacity
  -- ((0xa0830000-0xa0630000)/128 = 16384 entries). Consumed later by the per-account
  -- tuple-SEQUENCE comparators (c2).
  ".balign 8\n" ++
  "current_block_access_index:\n" ++
  "  .dword 1\n" ++
  ".balign 8\n" ++
  "exec_log_txindex:\n" ++
  "  .zero 131072\n" ++   -- 16384 entries × 8 B
  ".balign 8\n" ++
  "exec_log_seed_flag:\n" ++
  "  .zero 16384\n" ++    -- one provenance byte per persistent-log row; 1 = seed/preload
  ".balign 32\n" ++
  "evm_memory_layout_pad:\n" ++
  "  .zero " ++ toString runtimeMemoryLayoutPadBytes ++ "\n" ++
  ".balign 8\n" ++
  "evm_sparse_memory_count:\n  .zero 8\n" ++
  "evm_sparse_memory_next_epoch:\n  .dword 1\n" ++
  "evm_sparse_memory_epoch_by_depth:\n  .zero " ++ toString (1025 * 8) ++ "\n" ++
  "evm_sparse_memory_entries:\n  .zero " ++ toString (4096 * 56) ++ "\n" ++
  ".balign 8\n" ++
  "evm_env:\n" ++
  "  .zero 656\n" ++      -- 13 SimpleEnvField slots × 32 B + calldata/return-data
                          -- + M22/M24/M26 log-state cells + M28/M29 blob/block
                          -- cells (up to env+560) + M30 gasRemaining at env+568
                          -- + M31 account-witness context at env+576..616
                          -- + EIP-7843 SLOTNUM word at env+624..655
                          -- + M28 BLOBBASEFEE word at env+512 (32 bytes)
                          -- + M28 blobHashCount at env+544
                          -- + M29 BLOCKHASH current/count at env+552/+560
  ".balign 8\n" ++
  "evm_blob_hashes:\n" ++
  "  .zero 512\n" ++      -- M28: bounded 16 × 32-byte tx blob versioned hashes
  ".balign 8\n" ++
  "evm_block_hashes:\n" ++
  "  .zero 8192\n" ++     -- M29: 256 × 32-byte recent BLOCKHASH ancestors
  ".balign 8\n" ++
  "evm_event_logs:\n" ++
  "  .zero 1048576\n" ++   -- M26: 4096 × 256-byte bounded LOG event descriptors (v0.6.0 deposit blocks exceed 1024)
  ".balign 8\n" ++
  "evm_log_data:\n" ++
  "  .zero 1048576\n" ++   -- 8uld3.1a: per-tx FULL LOG data buffer (parallel to evm_event_logs); overflow -> evm_log_data_overflow
  ".balign 8\n" ++
  "evm_log_data_meta:\n" ++
  "  .zero 65536\n" ++    -- 8uld3.1a: 4096 logs × [u64 byte-offset into evm_log_data][u64 data_len], parallel to the descriptors
  ".balign 8\n" ++
  "evm_log_data_used:\n" ++
  "  .zero 8\n" ++        -- 8uld3.1a: bytes used in evm_log_data this tx (reset with eventLogLength)
  "evm_log_data_overflow:\n" ++
  "  .zero 8\n" ++        -- 8uld3.1a: set to 1 if a log's full data overflowed the buffer -> consumer bails conservatively
  ".balign 8\n" ++
  "system_call_mode:\n" ++
  "  .zero 8\n" ++        -- 8uld3.2.1a: when !=0, a top-level (depth-0) RETURN captures its data into system_call_returndata (for EIP-7002/7251 predeploy system calls). 0 for normal txs -> halt path byte-identical.
  ".balign 8\n" ++
  "system_call_returndata_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "system_call_returndata:\n" ++
  "  .zero " ++ toString systemCallReturndataMaxBytes ++ "\n" ++     -- 8uld3.2.1a: includes builder deposits (64x184=11776; 12 KiB cap)
  ".balign 8\n" ++
  "top_level_creation_returndata_status:\n" ++
  "  .zero 8\n" ++        -- 0=no depth-0 RETURN, 1=captured, 2=oversized RETURN (fail closed)
  ".balign 8\n" ++
  "top_level_creation_returndata_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "top_level_creation_returndata:\n" ++
  "  .zero " ++ toString topLevelCreationReturndataMaxBytes ++ "\n" ++
  emitSelfdestructData ++
  eip7708SyntheticLogTopicData ++
  (if includeSharedHelperData then storageAccessGasData else "") ++
  emitPrecompileFrameData ++
  emitModexpScratchData ++
  (if includeSharedHelperData then emitSha256Data else "") ++
  -- RIPEMD160 scratch/tables are NEW labels no guest data section provides,
  -- so they are included unconditionally (the SharedGuest closures get
  -- `zkvm_ripemd160` via `emitRuntimeDispatcherEmbeddedHelperFunctions`).
  ripemd160DataFragment ++
  (if includeKeccakScratch then
    ".balign 8\n" ++
    "zk3_state:\n" ++
    "  .zero 200\n"       -- M16: 25 × u64 keccak permutation state buffer
   else
    "") ++
  (if includeSharedHelperData then emitRuntimeAccountWitnessData else emitRuntimeDispatcherEmbeddedHelperData) ++
  ".balign 8\n" ++
  runtimeAccessAccountCountLabel ++ ":\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  runtimeAccessAccountTableLabel ++ ":\n" ++
  "  .zero " ++ toString (runtimeAccessAccountCapacity * runtimeAccessAccountRecordSize) ++ "\n" ++
  (if includeSharedHelperData then runtimeAccessAccountOutcomeData else "") ++
  runtimeAccessSeedScratchLabel ++ ":\n" ++
  "  .zero 32\n" ++
  ".balign 16\n" ++
  "lp64_stack:\n" ++
  "  .zero 262144\n" ++   -- LP64 stack for nested KECCAK/RLP/MPT/account helpers
  "lp64_sp_top:\n" ++
  ".balign 32\n" ++
  "evm_stack_guard_low:\n" ++
  s!"  .zero {evmStackGuardBytes}\n" ++
  "evm_stack_low:\n" ++
  s!"  .zero {evmStackScratchBytes}\n" ++
  "evm_stack_top:\n" ++
  "evm_stack_top_guard:\n" ++
  s!"  .zero {evmStackGuardBytes}\n" ++
  ".balign 8\n" ++
  -- Frame-relative stack bounds. Each cell holds the CURRENT frame's stack-top /
  -- stack-low ADDRESS. Statically `&evm_stack_top` / `&evm_stack_low`, so at
  -- depth 0 the under/overflow guards resolve to the same bounds as before
  -- (byte-identical output). `call_frame_descend` repoints them to the child's
  -- arena stack (`frame_base(d)+frameStackTopOff` and its low), and
  -- `frame_return` restores the parent's on pop. This makes the guards bound
  -- a child frame against its own stack (which lives in `call_frame_arena`,
  -- outside this global region) instead of spuriously firing.
  "evm_cur_stack_top:\n" ++
  "  .dword evm_stack_top\n" ++
  "evm_cur_stack_low:\n" ++
  "  .dword evm_stack_low\n" ++
  ".balign 8\n" ++
  "exp_scratch:\n" ++
  "  .zero 32\n" ++       -- EXP (0x0a): 32-byte result-accumulator frame. The
                          -- verified EXP body uses `x2`(sp)+0..24 as its running
                          -- accumulator; the dispatcher's `sp` points at
                          -- `lp64_sp_top` (top of a down-growing stack), so
                          -- `sp+0..24` would scribble into the jump table.
                          -- h_EXP's preBody repoints `x2` here and its tail
                          -- restores `sp = lp64_sp_top`.
                          -- (ADDMOD (0x08) needs no scratch symbols here: the
                          -- verified `evm_addmod_total` body parks its carry
                          -- scratch below `x12`, inside the guarded EVM stack
                          -- region — see EvmSelfCallingHandlers.lean.)
  emitBls12G1MsmDiscountTable ++
  emitBls12G2MsmDiscountTable ++
  emitGasCostTable ++ "\n" ++
  emitJumpTable registry ++ "\n" ++
  ".balign 32\n" ++
  "evm_memory:\n" ++
  "  .zero " ++ toString runtimeMemoryBytes ++ "\n"

/-- Runtime-bytecode `.data` section. Drops the `evm_code:` block
    (no baked bytecode); everything else matches the `.data`-baked
    variant. The static EVM stack arena is sized for the protocol
    1024-word stack depth. -/
def emitRuntimeDispatcherDataSection
    (registry : List OpcodeHandlerSpec) : String :=
  emitRuntimeDispatcherDataSectionCore registry true true

/-- Runtime dispatcher data for guests that already provide the shared
    `zk3_state` keccak scratch in their own data section. -/
def emitRuntimeDispatcherDataSectionSharedKeccak
    (registry : List OpcodeHandlerSpec) : String :=
  emitRuntimeDispatcherDataSectionCore registry false true

/-- Runtime dispatcher data for embedding into `stateless_guest`, which already
    links both `zk3_state` and the helper scratch records used by the runtime
    opcode helper functions. -/
def emitRuntimeDispatcherDataSectionSharedGuest
    (registry : List OpcodeHandlerSpec) : String :=
  emitRuntimeDispatcherDataSectionCore registry false false

/-- Frame/CREATE helper closure for STANDALONE runtime-dispatcher units.

    The registry handlers reference `create_frame_descend` (h_CREATE/h_CREATE2
    tails, .61.8.3.5), `u256_sub_be` (the CREATE endowment math), and
    `nonstorage_effect_latest_balance` (the live-BALANCE read, yisv8) — but
    those functions were only linked by the guest closure
    (`emitRuntimeDispatcherEmbeddedHelperFunctions`) and by probes that bundle
    them ad hoc, so the standalone `runtime_dispatcher` / callable-probe ELFs
    stopped linking when those handlers landed. This mirrors the proven probe
    bundle (see `ziskSstoreClearGasProbeUnit`). Kept OUT of
    `emitDispatcherEpilogueCore`'s shared-helpers branch: probes that already
    bundle these functions use that branch, and a second copy would be a
    duplicate-label assembler error. -/
def runtimeDispatcherStandaloneFrameHelpers : String :=
  u256SubBeFunction ++ "\n" ++
  frameBaseFunction ++ "\n" ++
  frameDepthPushFunction ++ "\n" ++
  frameDepthPopFunction ++ "\n" ++
  frameSaveRegsFunction ++ "\n" ++
  frameLoadRegsFunction ++ "\n" ++
  callFrameEnterFunction ++ "\n" ++
  callFrameSetCallEnvFunction ++ "\n" ++
  callFrameSetCalldataFunction ++ "\n" ++
  callFrameForwardGasFunction ++ "\n" ++
  callFrameDescendFunction ++ "\n" ++
  createFrameDescendFunction ++ "\n" ++
  frameReturnFunction ++ "\n" ++
  recordNonstorageEffectFunction ++ "\n" ++
  nonstorageEffectLatestBalanceFunction ++ "\n" ++
  nonstorageEffectLatestNonceFunction

/-- Frame-arena data labels for the standalone frame-helper closure
    (the guest defines these in `BlockVerdictDataSection`; the bundling
    probes each define their own copies). -/
def runtimeDispatcherStandaloneFrameData : String :=
  ".balign 8\n" ++
  "evm_call_depth:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "evm_halt_flag:\n  .zero 8\n" ++   -- 4ch8f.10.3 handler-tail routing flag
  ".balign 16\n" ++
  "frame_save_area:\n  .zero 16400\n" ++
  ".balign 32\n" ++
  "frame_call_ctx:\n  .zero 32800\n" ++
  ".balign 16\n" ++
  "frame_parent_bases:\n  .zero 16400\n" ++
  ".balign 32\n" ++
  "call_frame_arena:\n  .zero " ++ toString (0x39000 : Nat) ++ "\n" ++
  ".balign 8\n" ++
  "rb_running_block_bloom:\n  .zero 256\n" ++
  "rb_running_receipt_bloom:\n  .zero 256\n" ++
  "rb_bloom_checkpoints:\n  .zero 262144\n"

/-- Build a runtime-bytecode `BuildUnit` for `registry` + `exitBody`.
    The emitted ELF doesn't carry any bytecode — the test harness
    supplies it at runtime via `ziskemu -i <file>` (8-byte LE length
    prefix + raw bytes; see M4's input-region convention). -/
def buildRuntimeDispatchUnit
    (registry : List OpcodeHandlerSpec)
    (exitBody : Program) : BuildUnit := {
  body        := []
  prologueAsm := emitRuntimeDispatcherPrologue
  -- The frame helpers go BEFORE the epilogue: the prologue's dispatch loop
  -- ends with `j .dispatch_loop` (no fall-through into them) and every helper
  -- ends with `ret`, while the epilogue's exit join must keep falling through
  -- to the halt stub `emitBuildUnit` appends after `epilogueAsm`.
  epilogueAsm := runtimeDispatcherStandaloneFrameHelpers ++ "\n" ++
                 emitDispatcherEpilogue registry exitBody
  dataAsm     := emitRuntimeDispatcherDataSection registry ++ "\n" ++
                 runtimeDispatcherStandaloneFrameData
}

/-- Build a probe `BuildUnit` that exercises the callable runtime dispatcher
    ABI. The wrapper calls `runtime_dispatcher_call`, then writes final
    `env.gasRemaining` at `OUTPUT+240` and a return marker at `OUTPUT+248`.
    The ordinary dispatcher output prefix remains unchanged. -/
def buildRuntimeDispatchCallableProbeUnit
    (registry : List OpcodeHandlerSpec)
    (exitBody : Program) : BuildUnit := {
  body        := []
  prologueAsm :=
    "  jal ra, runtime_dispatcher_call\n" ++
    "  li t0, 0xa0010000\n" ++
    "  li t1, 0xc011ab1e\n" ++
    "  sd t1, 248(t0)             # returned-to-caller marker\n" ++
    "  la t2, evm_env\n" ++
    "  ld t3, 568(t2)\n" ++
    "  sd t3, 240(t0)             # final gasRemaining\n" ++
    "  li x17, 93\n" ++
    "  li x10, 0\n" ++
    "  ecall\n" ++
    emitRuntimeDispatcherCallablePrologue
  epilogueAsm := runtimeDispatcherStandaloneFrameHelpers ++ "\n" ++
                 emitDispatcherCallableEpilogue registry exitBody
  dataAsm     := emitRuntimeDispatcherDataSection registry ++ "\n" ++
                 runtimeDispatcherStandaloneFrameData
}

/-- Build a probe `BuildUnit` that runs one staged transaction through the
    callable runtime dispatcher and captures the dispatcher's gas results into
    stable per-transaction arrays (index 0), as required by the block-verdict
    gas-result arena (`block_verdict_gas_result_arena_prepare`).

    The transaction payload is supplied as the ordinary `pack-bytecode.py`
    runtime input (bytecode + calldata + trailers, with `--validate-tx-gas`),
    so feeding a STOP or `GAS,STOP` body exercises the post-execution gas
    surface. After `runtime_dispatcher_call` returns, the wrapper records, for
    transaction index 0:

      * `gas_left`             := `env.gasRemaining` (env+568)
      * `calldata_floor_gas_cost` := `runtime_tx_calldata_floor` (persisted by
        the validate-tx-gas path; 0 when validation was not requested)
      * `refund_counter`       := `evm_refund_acc` — the dispatcher's EIP-3529
        SSTORE refund accumulator (reset per dispatch, signed-accumulated in the
        SSTORE handler). SELFDESTRUCT refunds were removed in EIP-3529, so SSTORE
        is the only accumulation source on Amsterdam.
      * `halt_kind`            := `OUTPUT+32` (0 STOP/RETURN, 2 REVERT, …),
        captured separately so exceptional halts stay distinguishable from a
        normal STOP/RETURN.

    The captured arrays live at `rdg_*` and are also surfaced to the stable
    `OUTPUT+160` diagnostic window (within ziskemu's 256-byte `-o` dump, past
    the dispatcher's own storage/log surface which a simple STOP/empty-REVERT
    leaves zeroed) so a focused zisk probe can assert them:

      OUTPUT+160  gas_left[0]
      OUTPUT+168  refund_counter[0]
      OUTPUT+176  calldata_floor[0]
      OUTPUT+184  halt_kind
      OUTPUT+192  capture marker (0xca97c0de) -/
def buildRuntimeDispatchGasCaptureProbeUnit
    (registry : List OpcodeHandlerSpec)
    (exitBody : Program) : BuildUnit := {
  body        := []
  prologueAsm :=
    "  jal ra, runtime_dispatcher_call\n" ++
    -- nxio8: settle fold (EIP-8037 state gas + tx-error rules); a0 = effective
    -- gas_left (env[568] + evm_state_gas_left with the error folds), a1 = the
    -- effective refund counter (0 when the tx erred).
    "  jal ra, dispatcher_tx_gas_settle\n" ++
    "  mv t3, a0\n" ++
    "  mv t6, a1\n" ++
    "  la t4, rdg_gas_left\n" ++
    "  sd t3, 0(t4)\n" ++
    "  la t4, runtime_tx_calldata_floor\n" ++
    "  ld t5, 0(t4)               # EIP-7623 calldata floor\n" ++
    "  la t4, rdg_calldata_floor\n" ++
    "  sd t5, 0(t4)\n" ++
    "  la t4, rdg_refund_counter\n" ++
    "  sd t6, 0(t4)\n" ++
    "  li t0, 0xa0010000\n" ++
    "  ld t1, 32(t0)              # halt_kind from OUTPUT+32\n" ++
    "  la t4, rdg_halt_kind\n" ++
    "  sd t1, 0(t4)\n" ++
    "  sd t3, 160(t0)             # surface gas_left\n" ++
    "  sd t6, 168(t0)             # surface refund_counter\n" ++
    "  sd t5, 176(t0)             # surface calldata_floor\n" ++
    "  sd t1, 184(t0)             # surface halt_kind\n" ++
    "  li t2, 0xca97c0de\n" ++
    "  sd t2, 192(t0)             # capture marker\n" ++
    "  li x17, 93\n" ++
    "  li x10, 0\n" ++
    "  ecall\n" ++
    emitRuntimeDispatcherCallablePrologue
  epilogueAsm := runtimeDispatcherStandaloneFrameHelpers ++ "\n" ++
                 emitDispatcherCallableEpilogue registry exitBody
  dataAsm     :=
    emitRuntimeDispatcherDataSection registry ++ "\n" ++
    runtimeDispatcherStandaloneFrameData ++
    ".balign 8\n" ++
    "rdg_gas_left:\n  .zero 128\n" ++
    "rdg_refund_counter:\n  .zero 128\n" ++
    "rdg_calldata_floor:\n  .zero 128\n" ++
    "rdg_halt_kind:\n  .zero 8\n"
}

/-- Build a `BuildUnit` that runs the dispatcher over `bytecodeBytes`
    using `registry`. `exitBody` is the verified `Program` invoked
    at `.exit_label` to surface the result (usually `evmAddEpilogue`). -/
def buildDispatchUnit
    (registry : List OpcodeHandlerSpec)
    (exitBody : Program)
    (bytecodeBytes : String) : BuildUnit := {
  body        := []
  prologueAsm := emitDispatcherPrologue
  epilogueAsm := emitDispatcherEpilogue registry exitBody
  dataAsm     := emitDispatcherDataSection bytecodeBytes registry
}

end EvmAsm.Codegen
