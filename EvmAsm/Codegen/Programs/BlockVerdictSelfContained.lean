/-
  EvmAsm.Codegen.Programs.BlockVerdictSelfContained

  Self-containment scan for contract-recipient runtime execution
  (evm-asm-fhsxz.2.4.2.57.11.6.4.3). The contract-dispatch wiring stages the
  recipient's code, OWN storage (M22 preload), calldata, and a subset of env
  words (ADDRESS/CALLVALUE/COINBASE/NUMBER/TIMESTAMP/GASLIMIT/BASEFEE). It does
  NOT stage cross-account witness (M31), the sender (CALLER/ORIGIN), GASPRICE,
  the blockhash table, or the account's own balance (SELFBALANCE). So routing a
  contract through the dispatcher is only sound (exact gas, no false-reject)
  when its bytecode reads none of that un-staged state. This helper is the gate:
  a pushdata-aware scan that returns "self-contained" iff the bytecode contains
  none of the un-staged-state opcodes.

  Unsafe opcodes (still rejected — need un-staged state): BALANCE(0x31)
  (volatile cross-account balance, M31), SELFDESTRUCT(0xff) (beneficiary state).
  Everything else that once needed staging is now executed through real dispatch:
  ORIGIN/CALLER/GASPRICE (3vc2p.1/.2/.4), EXTCODESIZE/COPY/HASH (yisv8.2),
  SELFBALANCE (yisv8.1/.2), CREATE/CREATE2 (.61.8.3.5/.8c-3), BLOCKHASH(0x40)
  (3vc2p.3b: M29 table staged from the witness headers). PUSH1..PUSH32
  (0x60..0x7f) data bytes are skipped so push immediates are never misread as opcodes.

  SELFDESTRUCT(0xff) is rejected because its gas adds cold-beneficiary-access
  (EIP-2929) + account-creation (when the beneficiary is empty and balance>0),
  both depending on the un-staged beneficiary account; the dispatcher only
  charges the 5000 base (Dispatch.lean `0xff => 5000`), so a SELFDESTRUCT
  contract dispatched here would be under-charged.

  The message-call opcodes CALL(0xf1)/CALLCODE(0xf2)/DELEGATECALL(0xf4)/
  STATICCALL(0xfa) are NO LONGER rejected: the call-frame descent
  (callDescendFallThrough + call_frame_descend/frame_return) now executes them
  through the dispatcher, so a contract that makes nested calls routes through
  real execution rather than staying conservative. (Callee STORAGE preload for
  nested frames is still incomplete, so some nested-call rows will now FAIL the
  EEST gate where execution diverges — those failures are the follow-up work,
  bmvmx.1.7 children, not a regression of the self-contained scan itself.)
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bytecode_is_self_contained

    Calling convention:
      a0 = bytecode ptr   a1 = bytecode length
    Returns:
      a0 = 0 self-contained (safe to dispatch) / 1 uses un-staged state. -/
def bytecodeIsSelfContainedFunction : String :=
  "bytecode_is_self_contained:\n" ++
  "  mv t0, a0                    # cursor\n" ++
  "  add t1, a0, a1               # end\n" ++
  ".Lbsc_loop:\n" ++
  "  bgeu t0, t1, .Lbsc_safe\n" ++
  "  lbu t2, 0(t0)                # opcode\n" ++
  -- PUSH1..PUSH32 (0x60..0x7f): skip 1 + (op - 0x5f) bytes.
  "  li t3, 0x60; bltu t2, t3, .Lbsc_check\n" ++
  "  li t3, 0x7f; bgtu t2, t3, .Lbsc_check\n" ++
  "  addi t3, t2, -0x5f           # data byte count\n" ++
  "  addi t0, t0, 1; add t0, t0, t3; j .Lbsc_loop\n" ++
  ".Lbsc_check:\n" ++
  -- ALL un-staged-state opcodes are now ACTIVATED (execute soundly, not bail-to-BAL-replay-trust):
  --   ORIGIN(0x32)/CALLER(0x33)/GASPRICE(0x3a) (#8648); EXTCODESIZE/COPY/HASH(0x3b/0x3c/0x3f) +
  --   SELFBALANCE(0x47) + CREATE/CREATE2 (yisv8.2, #8649/#8650); BLOCKHASH(0x40) (3vc2p.4, M29
  --   recent-blockhash table reconstructed from the witness headers + staged); SELFDESTRUCT(0xff)
  --   (ee21v, selfdestructTailAsm: beneficiary access gas + new-account surcharge + balance
  --   transfer + EIP-7708 log); and BALANCE(0x31) (yisv8 .spine: live balance read from the
  --   non-storage effect log -- nonstorage_effect_latest_balance in balance_at_header_state_root,
  --   falling back to the pre-state witness when no value transfer touched the account).
  -- (The BALANCE 0x31 reject is REMOVED here; 0xff was removed by ee21v.)
  -- PREVRANDAO (0x44) ACTIVATED (ha909): stage_runtime_payload_code now copies the execution
  -- payload prev_randao Bytes32 into env word 9, so dispatched contracts read the real header mix.
  -- CHAINID (0x46) ACTIVATED (6121j.1): stage_runtime_payload_code now stages bv_chain_id into the
  -- CHAINID env word (+472 -> EvmEnv+384), so a dispatched contract reads the real chain id. Lifted.
  -- BLOBBASEFEE (0x4a) ACTIVATED (6121j.1): stage_runtime_payload_code now stages the block blob
  -- gas price (amsterdam_blob_gas_price_u256) into the payload blob_base_fee slot @+32 -> evm_env+512,
  -- so a dispatched contract reads the real value. Lifted.
  "  addi t0, t0, 1; j .Lbsc_loop\n" ++
  ".Lbsc_safe:\n" ++
  "  li a0, 0; ret\n" ++
  ".Lbsc_unsafe:\n" ++
  "  li a0, 1; ret"

/-- `zisk_bytecode_is_self_contained`: probe over hand-written bytecodes. Post-activation
    (ee21v + yisv8 + ha909 removed the last rejects) these opcodes scan self-contained (0).
    Output:
      +0  scan of PUSH1 0x07 PUSH1 0x01 SSTORE STOP (expect 0 self-contained)
      +8  scan of PUSH1 0x00 BALANCE   (60 00 31)   (expect 0 — BALANCE activated, yisv8)
      +16 scan of PUSH1 0xF1 STOP (0xF1 is push DATA, not CALL) (expect 0)
      +24 scan of PUSH1 0x00 SELFDESTRUCT (60 00 FF) (expect 0 — SELFDESTRUCT activated, ee21v)
      +32 scan of PUSH1 0x00 BLOCKHASH (60 00 40) (expect 0 — M29 staged, 3vc2p.4)
      +40 scan of PREVRANDAO STOP (44 00) (expect 0 — PREVRANDAO staged, ha909) -/
def ziskBytecodeIsSelfContainedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- code A: 60 07 60 01 55 00 (self-contained).
  "  la t0, bsc_codeA\n" ++
  "  li t1, 0x60; sb t1, 0(t0); li t1, 0x07; sb t1, 1(t0)\n" ++
  "  li t1, 0x60; sb t1, 2(t0); li t1, 0x01; sb t1, 3(t0)\n" ++
  "  li t1, 0x55; sb t1, 4(t0); sb zero, 5(t0)\n" ++
  "  la a0, bsc_codeA; li a1, 6; jal ra, bytecode_is_self_contained; sd a0, 0(s0)\n" ++
  -- code B: 60 00 31 (BALANCE -> now self-contained; yisv8 activated it via the live-balance read).
  "  la t0, bsc_codeB\n" ++
  "  li t1, 0x60; sb t1, 0(t0); sb zero, 1(t0); li t1, 0x31; sb t1, 2(t0)\n" ++
  "  la a0, bsc_codeB; li a1, 3; jal ra, bytecode_is_self_contained; sd a0, 8(s0)\n" ++
  -- code C: 60 F1 00 (0xF1 is PUSH1 data, then STOP -> self-contained).
  "  la t0, bsc_codeC\n" ++
  "  li t1, 0x60; sb t1, 0(t0); li t1, 0xF1; sb t1, 1(t0); sb zero, 2(t0)\n" ++
  "  la a0, bsc_codeC; li a1, 3; jal ra, bytecode_is_self_contained; sd a0, 16(s0)\n" ++
  -- code D: 60 00 FF (PUSH1 0 SELFDESTRUCT -> unsafe: beneficiary state is un-staged).
  "  la t0, bsc_codeD\n" ++
  "  li t1, 0x60; sb t1, 0(t0); sb zero, 1(t0); li t1, 0xFF; sb t1, 2(t0)\n" ++
  "  la a0, bsc_codeD; li a1, 3; jal ra, bytecode_is_self_contained; sd a0, 24(s0)\n" ++
  -- code E: 60 00 40 (PUSH1 0 BLOCKHASH -> NOW self-contained: M29 table staged, 3vc2p.4).
  "  la t0, bsc_codeE\n" ++
  "  li t1, 0x60; sb t1, 0(t0); sb zero, 1(t0); li t1, 0x40; sb t1, 2(t0)\n" ++
  "  la a0, bsc_codeE; li a1, 3; jal ra, bytecode_is_self_contained; sd a0, 32(s0)\n" ++
  -- code F: 44 00 (PREVRANDAO STOP -> self-contained: prev_randao env word staged, ha909).
  "  la t0, bsc_codeF\n" ++
  "  li t1, 0x44; sb t1, 0(t0); sb zero, 1(t0)\n" ++
  "  la a0, bsc_codeF; li a1, 2; jal ra, bytecode_is_self_contained; sd a0, 40(s0)\n" ++
  "  j .Lbscp_done\n" ++
  bytecodeIsSelfContainedFunction ++ "\n" ++
  ".Lbscp_done:"

def ziskBytecodeIsSelfContainedDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bsc_codeA:\n  .zero 16\n" ++
  "bsc_codeB:\n  .zero 16\n" ++
  "bsc_codeC:\n  .zero 16\n" ++
  "bsc_codeD:\n  .zero 16\n" ++
  "bsc_codeE:\n  .zero 16\n" ++
  "bsc_codeF:\n  .zero 16\n"

def ziskBytecodeIsSelfContainedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBytecodeIsSelfContainedPrologue
  dataAsm     := ziskBytecodeIsSelfContainedDataSection
}

end EvmAsm.Codegen
