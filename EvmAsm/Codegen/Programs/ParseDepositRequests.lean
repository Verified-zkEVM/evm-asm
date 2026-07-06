/-
  EvmAsm.Codegen.Programs.ParseDepositRequests

  `parse_deposit_requests` (bead evm-asm-8uld3.1, EIP-6110) — the receipt-log
  scan that, given the block's logs, concatenates the unframed deposit body of
  every valid DepositEvent. Mirrors execution-specs amsterdam
  `requests.py::parse_deposit_requests`: for each log, if its address is the
  beacon-chain `DEPOSIT_CONTRACT_ADDRESS` and its first topic is the
  `DEPOSIT_EVENT_SIGNATURE_HASH`, run `extract_deposit_data` (#8580) over the log
  data and append the 192-byte body. Non-deposit logs are skipped; a deposit log
  whose data is malformed sets the status flag (the block is invalid), matching
  the spec's hard failure there.

  This is the standalone, probe-verifiable scan (the sibling of `extract_deposit_data`,
  which also landed standalone). The remaining wiring — feeding it the block's real
  materialized receipt logs WITH FULL DATA — is execution-gated (`bmvmx.1.4`): the
  current M26 `evm_event_logs` LOG-capture descriptor truncates data to 32 bytes,
  so a full-data receipt-log source is the follow-up. The derived bytes feed the
  type-0 (`DEPOSIT_REQUEST_TYPE`) prefix + the execution-derived `requests_hash`
  (8uld3.4).

  Log-record array format (canonical big-endian; the receipt decoder canonicalizes
  to this — the M26 descriptor stores stack-word order, see EvmLogHandlers.lean):
    +0   address (20-byte BE in the low bytes, padded to 32)
    +32  topic_count (u64)
    +40  topic0 (32-byte BE)
    +72  data_len (u64)
    +80  data bytes (data_len, padded to 8 so the next record stays 8-aligned)
  record stride = 80 + roundup8(data_len).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.ExtractDepositData

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## parse_deposit_requests
    a0 = log-record array ptr (format above)   a1 = log count
    a2 = output ptr (receives N_matched × 192 bytes)   a3 = u64 status out ptr
    a0 (output) = total deposit-request bytes written (N_matched × 192).
    *status = 0 ok / 1 a deposit-event log had malformed data (block invalid). -/
def parseDepositRequestsFunction : String :=
  "parse_deposit_requests:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                    # record ptr\n" ++
  "  mv s1, a1                    # remaining log count\n" ++
  "  mv s2, a2                    # output cursor\n" ++
  "  mv s3, a2                    # output base\n" ++
  "  mv s4, a3                    # status out ptr\n" ++
  "  sd zero, 0(s4)               # status = 0 (ok)\n" ++
  ".Lpdr_loop:\n" ++
  "  beqz s1, .Lpdr_done\n" ++
  -- match address: record[0..20] == DEPOSIT_CONTRACT_ADDRESS
  "  la t0, pdr_deposit_addr\n" ++
  "  li t1, 20; li t2, 0\n" ++
  ".Lpdr_addrcmp:\n" ++
  "  beq t2, t1, .Lpdr_addr_ok\n" ++
  "  add t3, s0, t2; lbu t4, 0(t3)\n" ++
  "  add t3, t0, t2; lbu t5, 0(t3)\n" ++
  "  bne t4, t5, .Lpdr_next       # address mismatch -> not a deposit log\n" ++
  "  addi t2, t2, 1; j .Lpdr_addrcmp\n" ++
  ".Lpdr_addr_ok:\n" ++
  "  ld t0, 32(s0); beqz t0, .Lpdr_next   # topic_count == 0 -> skip\n" ++
  -- match topic0: record[40..72] == DEPOSIT_EVENT_SIGNATURE_HASH
  "  la t0, pdr_deposit_sig\n" ++
  "  li t1, 32; li t2, 0\n" ++
  ".Lpdr_sigcmp:\n" ++
  "  beq t2, t1, .Lpdr_sig_ok\n" ++
  "  add t3, s0, t2; lbu t4, 40(t3)       # byte record+40+t2 (topic0)\n" ++
  "  add t3, t0, t2; lbu t5, 0(t3)\n" ++
  "  bne t4, t5, .Lpdr_next       # topic0 mismatch -> not a deposit event\n" ++
  "  addi t2, t2, 1; j .Lpdr_sigcmp\n" ++
  ".Lpdr_sig_ok:\n" ++
  -- extract_deposit_data(record+80, data_len, out cursor)
  "  ld a1, 72(s0)                # data_len\n" ++
  "  addi a0, s0, 80              # data ptr\n" ++
  "  mv a2, s2                    # out cursor\n" ++
  "  jal ra, extract_deposit_data\n" ++
  "  bnez a0, .Lpdr_malformed     # deposit log with malformed data -> block invalid\n" ++
  "  addi s2, s2, 192             # appended one 192-byte deposit body\n" ++
  ".Lpdr_next:\n" ++
  "  ld t0, 72(s0); addi t0, t0, 7; andi t0, t0, -8; addi t0, t0, 80   # stride = 80 + roundup8(data_len)\n" ++
  "  add s0, s0, t0\n" ++
  "  addi s1, s1, -1; j .Lpdr_loop\n" ++
  ".Lpdr_malformed:\n" ++
  "  li t0, 1; sd t0, 0(s4)       # status = 1; stop (spec asserts here)\n" ++
  ".Lpdr_done:\n" ++
  "  sub a0, s2, s3               # total deposit-request bytes written\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_parse_deposit_requests`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : log count
      bytes 16..   : the log-record array (format in the module header)
    Output:
      +0  status (0 ok / 1 malformed deposit)
      +8  total deposit-request bytes written
      +16 the concatenated deposit bodies. -/
def ziskParseDepositRequestsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # log count\n" ++
  "  addi a0, a6, 16             # log array ptr\n" ++
  "  la a2, pdr_out              # output buffer\n" ++
  "  la a3, pdr_status           # status out\n" ++
  "  jal ra, parse_deposit_requests\n" ++
  "  li t0, 0xa0010000\n" ++
  "  la t1, pdr_status; ld t2, 0(t1); sd t2, 0(t0)      # status\n" ++
  "  sd a0, 8(t0)                # total bytes\n" ++
  "  la t1, pdr_out; addi t3, t0, 16; mv t4, a0\n" ++
  "  li t2, 240; bltu t4, t2, .Lpdr_dump   # clamp dump to 240B (ziskemu output cap is 256)\n" ++
  "  mv t4, t2\n" ++
  ".Lpdr_dump:\n" ++
  "  beqz t4, .Lpdr_dumpdone\n" ++
  "  lbu t5, 0(t1); sb t5, 0(t3); addi t1, t1, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lpdr_dump\n" ++
  ".Lpdr_dumpdone:\n" ++
  "  j .Lpdr_pdone\n" ++
  parseDepositRequestsFunction ++ "\n" ++
  extractDepositDataFunction ++ "\n" ++
  ".Lpdr_pdone:"

def ziskParseDepositRequestsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "pdr_deposit_addr:\n" ++   -- DEPOSIT_CONTRACT_ADDRESS (20 bytes BE)
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x21, 0x9a, 0xb5, 0x40\n" ++
  "  .byte 0x35, 0x6c, 0xbb, 0x83, 0x9c, 0xbe, 0x05, 0x30\n" ++
  "  .byte 0x3d, 0x77, 0x05, 0xfa\n" ++
  ".balign 8\n" ++
  "pdr_deposit_sig:\n" ++    -- DEPOSIT_EVENT_SIGNATURE_HASH (32 bytes BE)
  "  .byte 0x64, 0x9b, 0xbc, 0x62, 0xd0, 0xe3, 0x13, 0x42\n" ++
  "  .byte 0xaf, 0xea, 0x4e, 0x5c, 0xd8, 0x2d, 0x40, 0x49\n" ++
  "  .byte 0xe7, 0xe1, 0xee, 0x91, 0x2f, 0xc0, 0x88, 0x9a\n" ++
  "  .byte 0xa7, 0x90, 0x80, 0x3b, 0xe3, 0x90, 0x38, 0xc5\n" ++
  ".balign 8\n" ++
  "pdr_out:\n  .zero 2048\n" ++
  "pdr_status:\n  .zero 8\n"

def ziskParseDepositRequestsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskParseDepositRequestsPrologue
  dataAsm     := ziskParseDepositRequestsDataSection
}

end EvmAsm.Codegen
