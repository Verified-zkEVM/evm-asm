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
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Address
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.EvmOpcodes
import EvmAsm.Codegen.Programs.EvmNonce
import EvmAsm.Codegen.Programs.EvmCodes
import EvmAsm.Codegen.Programs.EvmOpcodesExtcodecopy
import EvmAsm.Codegen.Programs.EvmStorageAccessGas
import EvmAsm.Codegen.Programs.PrecompileBackendProbes
import EvmAsm.Codegen.Programs.StateCompose
import EvmAsm.Codegen.Programs.StatePredicates
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.AccountBalance

namespace EvmAsm.Codegen

open EvmAsm.Rv64

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

/-- Raw dispatcher guard for handlers that read `wordCount` EVM stack
    words before their body runs. The EVM stack grows downward from
    `evm_stack_top`; a handler needing `n` words requires
    `x12 <= evm_stack_top - 32*n`. If not, route to the exceptional
    stack-underflow exit before any body performs unchecked loads. -/
def stackUnderflowGuardAsm (wordCount : Nat) : String :=
  "  la x14, evm_stack_top\n" ++
  s!"  addi x14, x14, -{wordCount * evmStackWordBytes}\n" ++
  "  bltu x14, x12, .exit_stack_underflow"

/-- Raw dispatcher guard for handlers that push one EVM stack word. The EVM
    stack is full exactly when the live pointer has reached `evm_stack_low`;
    pushing then would decrement below the protocol 1024-word arena. -/
def stackOverflowGuardAsm : String :=
  "  la x14, evm_stack_low\n" ++
  "  bleu x12, x14, .exit_stack_overflow"

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

/-- M30 (gas metering, first slice): the **static base** gas cost of each
    EVM opcode byte, used by the dispatch loop to charge gas per instruction.

    Sourced from the standard EVM gas tiers
    (`execution-specs/src/ethereum/forks/prague/vm/gas.py`): ZERO=0,
    JUMPDEST=1, BASE=2, VERYLOW=3, LOW=5, MID=8, HIGH=10, BLOCKHASH=20,
    KECCAK256 base=30, LOG base=375, warm access=100, CREATE=32000.

    **Static base costs only** — all *dynamic* components are dropped:
    memory-expansion, copy (per-word), KECCAK/LOG per-word/per-topic, EXP
    per-byte, and cold-access surcharges (SLOAD/BALANCE/EXTCODE*/CALL use
    the warm floor of 100; SSTORE uses 100; cold +2600/+2100 not modeled).
    So state-touching ops UNDER-charge — fine for the first slice, which
    establishes the metering machinery; dynamic costs are a follow-up.

    Halt opcodes (STOP/RETURN/REVERT/INVALID/SELFDESTRUCT) and every byte
    not assigned a real opcode are 0, so trusted programs never spuriously
    run out of gas on a terminator or an unwired byte. -/
def staticGasCost (op : Nat) : Nat :=
  if 0x60 ≤ op ∧ op ≤ 0x7f then 3        -- PUSH1..PUSH32 (VERYLOW)
  else if 0x80 ≤ op ∧ op ≤ 0x8f then 3   -- DUP1..DUP16 (VERYLOW)
  else if 0x90 ≤ op ∧ op ≤ 0x9f then 3   -- SWAP1..SWAP16 (VERYLOW)
  else if 0xa0 ≤ op ∧ op ≤ 0xa4 then 375 -- LOG0..LOG4 (base)
  else match op with
    -- arithmetic
    | 0x01 => 3 | 0x03 => 3                                  -- ADD, SUB
    | 0x02 => 5 | 0x04 => 5 | 0x05 => 5 | 0x06 => 5 | 0x07 => 5  -- MUL,DIV,SDIV,MOD,SMOD
    | 0x0b => 5                                              -- SIGNEXTEND
    | 0x08 => 8 | 0x09 => 8                                  -- ADDMOD, MULMOD
    | 0x0a => 10                                             -- EXP (base)
    -- comparison & bitwise (all VERYLOW)
    | 0x10 | 0x11 | 0x12 | 0x13 | 0x14 | 0x15 => 3
    | 0x16 | 0x17 | 0x18 | 0x19 | 0x1a => 3
    | 0x1b | 0x1c | 0x1d => 3
    | 0x20 => 30                                             -- KECCAK256 (base)
    -- environment / context
    | 0x30 => 2 | 0x32 => 2 | 0x33 => 2 | 0x34 => 2 | 0x3a => 2  -- ADDRESS,ORIGIN,CALLER,CALLVALUE,GASPRICE
    | 0x35 => 3                                              -- CALLDATALOAD (VERYLOW)
    | 0x36 => 2 | 0x38 => 2 | 0x3d => 2                      -- CALLDATASIZE,CODESIZE,RETURNDATASIZE
    | 0x37 => 3 | 0x39 => 3 | 0x3e => 3                      -- CALLDATACOPY,CODECOPY,RETURNDATACOPY (base)
    | 0x31 => 100 | 0x3b => 100 | 0x3f => 100               -- BALANCE,EXTCODESIZE,EXTCODEHASH (warm floor)
    | 0x3c => 100                                            -- EXTCODECOPY (warm floor, base)
    | 0x40 => 20                                             -- BLOCKHASH
    | 0x41 | 0x42 | 0x43 | 0x44 | 0x45 | 0x46 | 0x48 | 0x4a | 0x4b => 2  -- COINBASE..BASEFEE, BLOBBASEFEE, SLOTNUM
    | 0x47 => 5                                              -- SELFBALANCE (LOW)
    | 0x49 => 3                                              -- BLOBHASH
    -- stack / memory / flow
    | 0x50 => 2                                              -- POP (BASE)
    | 0x51 | 0x52 | 0x53 => 3                                -- MLOAD,MSTORE,MSTORE8 (VERYLOW)
    | 0x54 => 100 | 0x55 => 100                              -- SLOAD,SSTORE (warm/base; dynamic dropped)
    | 0x56 => 8                                              -- JUMP (MID)
    | 0x57 => 10                                             -- JUMPI (HIGH)
    | 0x58 | 0x59 | 0x5a => 2                                -- PC,MSIZE,GAS (BASE)
    | 0x5b => 1                                              -- JUMPDEST
    | 0x5c => 100 | 0x5d => 100                              -- TLOAD,TSTORE
    | 0x5e => 3                                              -- MCOPY (base)
    | 0x5f => 2                                              -- PUSH0 (BASE)
    -- child frames (base; dynamic call/create costs dropped)
    | 0xf0 => 32000 | 0xf5 => 32000                          -- CREATE, CREATE2
    | 0xf1 | 0xf2 | 0xf4 | 0xfa => 100                       -- CALL,CALLCODE,DELEGATECALL,STATICCALL
    | 0xff => 5000                                           -- SELFDESTRUCT (base)
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
      +precompileFrameReturndataOff         first 256 bytes of returndata scratch
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
    colliding with map-Fp-to-G1 stacked PR edits around +144/+336. -/
def emitPrecompileFrameData : String :=
  ".balign 8\n" ++
  "evm_precompile_frame:\n" ++
  "  .zero 1280\n"

/-- SELFDESTRUCT runtime staging scratch.

    `evm_selfdestruct_beneficiary` stores the popped beneficiary address as
    20 canonical big-endian bytes (the low 160 bits of the EVM stack word,
    with higher bits ignored). `evm_selfdestruct_created_in_tx` is the
    transaction-local EIP-6780 marker that CREATE/CREATE2 integration will set
    before SELFDESTRUCT reaches balance/deletion handling. It defaults to zero.
    `evm_selfdestruct_staged` is a u64 flag used by the test/diagnostic surface
    until later account-access/state children consume this staged beneficiary
    directly. -/
def emitSelfdestructData : String :=
  ".balign 32\n" ++
  "evm_selfdestruct_beneficiary:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "evm_selfdestruct_created_in_tx:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "evm_selfdestruct_staged:\n" ++
  "  .zero 8\n"

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
def emitDispatcherPrologue : String :=
  "  la sp, lp64_sp_top\n" ++     -- M16: LP64 stack ptr for ECALL-bridge helpers
                                  -- (e.g. zkvm_keccak256's `addi sp, sp, -32`)
  "  la x10, evm_code\n" ++
  "  la x21, evm_code\n" ++       -- M15: preserved code base (for PC, JUMP, JUMPI)
  "  la x12, evm_stack_top\n" ++
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
  "  sd x0, 464(x20)\n" ++         -- env.transientLogLengthOff = 0
  "  sd x0, 472(x20)\n" ++         -- env.eventLogLengthOff = 0
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
  ".dispatch_loop:\n" ++
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
  "  j .dispatch_loop"

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
  "  li x16, 0xa0010000\n" ++       -- OUTPUT_ADDR
  "  sd x0, 0(x16)\n" ++            -- zero-fill result OUTPUT[0..32]
  "  sd x0, 8(x16)\n" ++            -- (exceptional/return-data-free halt,
  "  sd x0, 16(x16)\n" ++           --  surfaced deterministically)
  "  sd x0, 24(x16)\n" ++
  s!"  li x17, {kind}\n" ++         -- halt_kind
  "  sd x17, 32(x16)\n" ++
  "  j .exit_no_epilogue\n"

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
def emitDispatcherEpilogue
    (registry : List OpcodeHandlerSpec) (exitBody : Program) : String :=
  String.intercalate "\n" (registry.map OpcodeHandlerSpec.emitSubroutine) ++ "\n" ++
  -- M16/M27: hash subroutines sit BETWEEN the handler subroutines
  -- and the `h_invalid:` / `.exit_label:` blocks so it's reachable only
  -- via explicit `jal`s (not by fall-through from exitBody).
  -- Each handler subroutine ends with `ret` / `j .dispatch_loop`, so
  -- they don't fall through into these labels. The subroutines end
  -- with `ret`, returning to whoever JAL'd them.
  zkvmSha256Function ++ "\n" ++
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
  hasCodeOrNonceAtHeaderStateRootFunction ++ "\n" ++
  addressComputeCreateFunction ++ "\n" ++
  addressComputeCreate2Function ++ "\n" ++
  zkvmModexpSafeFailWrapper ++ "\n" ++
  storageAccessGasFunction ++ "\n" ++
  runtimeAccessAccountSeedFunction ++ "\n" ++
  runtimeAccessSeedInitialAccountsFunction ++ "\n" ++
  runtimeAccessAccountChargeFunction ++ "\n" ++
  zkvmBls12G1AddSafeFailWrapper ++ "\n" ++
  zkvmBls12G1MsmSafeFailWrapper ++ "\n" ++
  zkvmBn254G1AddSafeFailWrapper ++ "\n" ++
  zkvmBn254G1MulSafeFailWrapper ++ "\n" ++
  zkvmBn254PairingSafeFailWrapper ++ "\n" ++
  zkvmBlake2fSafeFailWrapper ++ "\n" ++
  zkvmKzgPointEvalSafeFailWrapper ++ "\n" ++
  zkvmSecp256r1VerifySafeFailWrapper ++ "\n" ++
  bls12SafeFailWrapper "zkvm_bls12_g2_add" "0x10d" ++ "\n" ++
  bls12SafeFailWrapper "zkvm_bls12_g2_msm" "0x10e" ++ "\n" ++
  bls12SafeFailWrapper "zkvm_bls12_pairing" "0x10f" ++ "\n" ++
  bls12SafeFailWrapper "zkvm_bls12_map_fp_to_g1" "0x110" ++ "\n" ++
  bls12SafeFailWrapper "zkvm_bls12_map_fp2_to_g2" "0x111" ++ "\n" ++
  "h_invalid:\n" ++
  "  j .exit_label\n" ++
  -- Exceptional-halt exits (reached only via `j <label>`; `h_invalid`'s
  -- `j .exit_label` above skips them, and each ends with
  -- `j .exit_no_epilogue` so none fall through into exitBody). Each
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
  emitExceptionalExit ".exit_invalid" 4 ++
  emitExceptionalExit ".exit_invalid_op" 3 ++
  emitExceptionalExit ".exit_selfdestruct" 5 ++
  emitExceptionalExit ".exit_outofgas" 6 ++
  emitExceptionalExit ".exit_stack_underflow" 7 ++
  emitExceptionalExit ".exit_stack_overflow" 8 ++
  ".exit_label:\n" ++
  emitProgram exitBody ++ "\n" ++
  ".exit_no_epilogue:\n" ++
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
  ".L_selfdestruct_diag_done:\n"

/-- `.data` section layout (starts at `0xa0000000` per
    `Driver.lean`'s `-Tdata=...`):

    ```
    evm_code:         <bytecode> (~50 B)
    .balign 32
    evm_memory:       .zero 0x10000         (64 KiB EVM memory, M7 onward)
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
  "evm_memory:\n" ++
  "  .zero 0x10000\n" ++  -- 64 KiB EVM memory, enough for Amsterdam MAX_INIT_CODE_SIZE
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
  "  .zero 4096\n" ++     -- M26: 16 × 256-byte bounded LOG event descriptors
  emitSelfdestructData ++
  storageAccessGasData ++
  emitPrecompileFrameData ++
  emitModexpScratchData ++
  emitSha256Data ++
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
  "exp_scratch:\n" ++
  "  .zero 32\n" ++       -- EXP (0x0a): 32-byte result-accumulator frame. The
                          -- verified EXP body uses `x2`(sp)+0..24 as its running
                          -- accumulator; the dispatcher's `sp` points at
                          -- `lp64_sp_top` (top of a down-growing stack), so
                          -- `sp+0..24` would scribble into the jump table.
                          -- h_EXP's preBody repoints `x2` here and its tail
  ".balign 32\n" ++
  "addmod_runtime_scratch:\n" ++
  "  .zero 128\n" ++      -- ADDMOD (0x08): two callable MOD frames for the carry path.
  ".balign 8\n" ++
  "addmod_saved_stack_ptr:\n" ++
  "  .zero 8\n" ++        -- Original EVM stack pointer across inner MOD calls.
                          -- restores `sp = lp64_sp_top`.
  emitBls12G1MsmDiscountTable ++
  emitBls12G2MsmDiscountTable ++
  emitGasCostTable ++ "\n" ++
  emitJumpTable registry

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

/-- Runtime-bytecode dispatcher prologue. Same fetch/decode/dispatch
    loop as `emitDispatcherPrologue`; differs only in how `x10` is
    initialised — pointed at the input region instead of an
    in-`.data` label. The hex literal `0x40000010` matches
    `INPUT_ADDR + INPUT_DATA_OFFSET` in `Programs.lean`. -/
def emitRuntimeDispatcherSetup : String :=
  "  la sp, lp64_sp_top\n" ++   -- M16: LP64 stack ptr for ECALL-bridge helpers
                                -- (e.g. zkvm_keccak256's `addi sp, sp, -32`)
  "  li x10, 0x40000010\n" ++   -- INPUT_ADDR + INPUT_DATA_OFFSET
  "  li x21, 0x40000010\n" ++   -- M15: preserved code base (mirrors x10 init)
  "  la x12, evm_stack_top\n" ++
  "  la x13, evm_memory\n" ++
  "  la x20, evm_env\n" ++       -- M12: env-region base (ADDRESS, CALLER, …)
  -- M21: populate env's callDataPtr / callDataLen from the input region.
  -- The input file format (pack-bytecode.py) is:
  --   [8B bytecode-length][bytecode bytes][pad to 8][8B calldata-length][calldata bytes]
  -- bytecode-length sits at INPUT_ADDR + 8 = 0x40000008. We round it up
  -- to 8-byte boundary, add to bytecode start (x10), and that's the
  -- calldata-length address. Eight bytes past it is the calldata.
  "  li x5, 0x40000008\n" ++       -- &(bytecode length)
  "  ld x5, 0(x5)\n" ++            -- x5 = bytecode length (exact)
  "  sd x5, 496(x20)\n" ++         -- M33: env.codeSize = bytecode length (CODESIZE/CODECOPY)
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
  "  sd x6, 448(x20)\n" ++         -- env.persistentLogLengthOff = preload count
  "  sd x6, 456(x20)\n" ++         -- env.persistentLogCheckpointOff = preload count
  "  sd x0, 464(x20)\n" ++         -- env.transientLogLengthOff = 0
  "  sd x0, 472(x20)\n" ++         -- env.eventLogLengthOff = 0
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
  ".preload_expand_loop:\n" ++
  "  beqz x6, .preload_expand_done\n" ++
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
  "  li x7, 21000\n" ++            -- x7 = intrinsic = TX_BASE
  "  li x10, 21000\n" ++           -- x10 = data floor = TX_BASE
  "  beqz x8, .runtime_tx_gas_no_create\n" ++
  "  li x8, 32000\n" ++            -- TX_CREATE
  "  add x7, x7, x8\n" ++
  ".runtime_tx_gas_no_create:\n" ++
  "  ld x8, 424(x20)\n" ++         -- x8 = calldata length
  "  ld x9, 416(x20)\n" ++         -- x9 = calldata ptr
  "  ld x12, 424(x20)\n" ++        -- x12 = calldata length for initcode words
  ".runtime_tx_gas_data_loop:\n" ++
  "  beqz x8, .runtime_tx_gas_create_words\n" ++
  "  lbu x11, 0(x9)\n" ++
  "  beqz x11, .runtime_tx_gas_zero_byte\n" ++
  "  addi x7, x7, 16\n" ++
  "  addi x10, x10, 40\n" ++
  "  j .runtime_tx_gas_data_step\n" ++
  ".runtime_tx_gas_zero_byte:\n" ++
  "  addi x7, x7, 4\n" ++
  "  addi x10, x10, 10\n" ++
  ".runtime_tx_gas_data_step:\n" ++
  "  addi x9, x9, 1\n" ++
  "  addi x8, x8, -1\n" ++
  "  j .runtime_tx_gas_data_loop\n" ++
  ".runtime_tx_gas_create_words:\n" ++
  "  ld x8, -8(x5)\n" ++           -- x8 = is_creation
  "  beqz x8, .runtime_tx_gas_check\n" ++
  "  addi x12, x12, 31\n" ++
  "  srli x12, x12, 5\n" ++        -- ceil(calldata_len / 32)
  "  slli x12, x12, 1\n" ++        -- CODE_INIT_PER_WORD = 2
  "  add x7, x7, x12\n" ++
  ".runtime_tx_gas_check:\n" ++
  "  bltu x6, x7, .exit_outofgas\n" ++
  "  bltu x6, x10, .exit_outofgas\n" ++
  "  sub x6, x6, x7\n" ++
  ".runtime_tx_gas_done:\n" ++
  "  sd x6, 568(x20)\n" ++          -- env.gasRemaining = execution gas
  "  ld x6, 0(x5)\n" ++            -- x6 = header_len
  "  sd x6, 584(x20)\n" ++
  "  ld x7, 8(x5)\n" ++            -- x7 = witness_state_len
  "  sd x7, 600(x20)\n" ++
  "  ld x8, 16(x5)\n" ++           -- x8 = witness_codes_len
  "  sd x8, 616(x20)\n" ++
  "  addi x5, x5, 24\n" ++         -- x5 = header ptr
  "  sd x5, 576(x20)\n" ++
  "  add x5, x5, x6\n" ++          -- x5 = witness.state ptr
  "  sd x5, 592(x20)\n" ++
  "  add x5, x5, x7\n" ++          -- x5 = witness.codes ptr
  "  sd x5, 608(x20)\n" ++
  "  jal ra, runtime_access_seed_initial_accounts\n" ++
  "  mv x10, x21\n" ++
  "  la x12, evm_stack_top\n" ++
  "  la x13, evm_memory"

/-- Runtime dispatcher prologue: setup plus fetch/decode/dispatch loop. -/
def emitRuntimeDispatcherPrologue : String :=
  emitRuntimeDispatcherSetup ++ "\n" ++
  ".dispatch_loop:\n" ++
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
  "  j .dispatch_loop"

/-- Runtime-bytecode `.data` section. Drops the `evm_code:` block
    (no baked bytecode); everything else matches the `.data`-baked
    variant. The static EVM stack arena is sized for the protocol
    1024-word stack depth. -/
def emitRuntimeDispatcherDataSection
    (registry : List OpcodeHandlerSpec) : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "evm_memory:\n" ++
  "  .zero 0x10000\n" ++  -- 64 KiB EVM memory, enough for Amsterdam MAX_INIT_CODE_SIZE
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
  "  .zero 4096\n" ++     -- M26: 16 × 256-byte bounded LOG event descriptors
  emitSelfdestructData ++
  storageAccessGasData ++
  emitPrecompileFrameData ++
  emitModexpScratchData ++
  emitSha256Data ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++      -- M16: 25 × u64 keccak permutation state buffer
  emitRuntimeAccountWitnessData ++
  ".balign 8\n" ++
  runtimeAccessAccountCountLabel ++ ":\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  runtimeAccessAccountTableLabel ++ ":\n" ++
  "  .zero " ++ toString (runtimeAccessAccountCapacity * runtimeAccessAccountRecordSize) ++ "\n" ++
  runtimeAccessAccountOutcomeData ++
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
  "exp_scratch:\n" ++
  "  .zero 32\n" ++       -- EXP (0x0a): 32-byte result-accumulator frame. The
                          -- verified EXP body uses `x2`(sp)+0..24 as its running
                          -- accumulator; the dispatcher's `sp` points at
                          -- `lp64_sp_top` (top of a down-growing stack), so
                          -- `sp+0..24` would scribble into the jump table.
                          -- h_EXP's preBody repoints `x2` here and its tail
  ".balign 32\n" ++
  "addmod_runtime_scratch:\n" ++
  "  .zero 128\n" ++      -- ADDMOD (0x08): two callable MOD frames for the carry path.
  ".balign 8\n" ++
  "addmod_saved_stack_ptr:\n" ++
  "  .zero 8\n" ++        -- Original EVM stack pointer across inner MOD calls.
                          -- restores `sp = lp64_sp_top`.
  emitBls12G1MsmDiscountTable ++
  emitBls12G2MsmDiscountTable ++
  emitGasCostTable ++ "\n" ++
  emitJumpTable registry

/-- Build a runtime-bytecode `BuildUnit` for `registry` + `exitBody`.
    The emitted ELF doesn't carry any bytecode — the test harness
    supplies it at runtime via `ziskemu -i <file>` (8-byte LE length
    prefix + raw bytes; see M4's input-region convention). -/
def buildRuntimeDispatchUnit
    (registry : List OpcodeHandlerSpec)
    (exitBody : Program) : BuildUnit := {
  body        := []
  prologueAsm := emitRuntimeDispatcherPrologue
  epilogueAsm := emitDispatcherEpilogue registry exitBody
  dataAsm     := emitRuntimeDispatcherDataSection registry
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
