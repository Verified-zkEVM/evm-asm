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
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## parse_deposit_requests
    a0 = log-record array ptr (format above)   a1 = log count
    a2 = output ptr (receives N_matched × 192 bytes)   a3 = u64 status out ptr
    a0 (output) = total deposit-request bytes written (N_matched × 192).
    *status = 0 ok / 1 a deposit-event log had malformed data (block invalid). -/
def parseDepositRequests_prog : Program :=
  [ .ADDI .x2 .x2 (-56 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x12,
    .MV .x20 .x13,
    .SD .x20 .x0 (0 : BitVec 12),
    .BEQ .x9 .x0 (brOff (GuestAddrs.parse_deposit_requests + 220) (GuestAddrs.parse_deposit_requests + 52)),
    .AUIPC .x5 (laHi GuestAddrs.pdr_deposit_addr (GuestAddrs.parse_deposit_requests + 56)),
    .ADDI .x5 .x5 (laLo GuestAddrs.pdr_deposit_addr (GuestAddrs.parse_deposit_requests + 56)),
    .LI .x6 (20 : Word),
    .LI .x7 (0 : Word),
    .BEQ .x7 .x6 (32 : BitVec 13),
    .ADD .x28 .x8 .x7,
    .LBU .x29 .x28 (0 : BitVec 12),
    .ADD .x28 .x5 .x7,
    .LBU .x30 .x28 (0 : BitVec 12),
    .BNE .x29 .x30 (brOff (GuestAddrs.parse_deposit_requests + 184) (GuestAddrs.parse_deposit_requests + 92)),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LD .x5 .x8 (32 : BitVec 12),
    .BEQ .x5 .x0 (brOff (GuestAddrs.parse_deposit_requests + 184) (GuestAddrs.parse_deposit_requests + 108)),
    .AUIPC .x5 (laHi GuestAddrs.pdr_deposit_sig (GuestAddrs.parse_deposit_requests + 112)),
    .ADDI .x5 .x5 (laLo GuestAddrs.pdr_deposit_sig (GuestAddrs.parse_deposit_requests + 112)),
    .LI .x6 (32 : Word),
    .LI .x7 (0 : Word),
    .BEQ .x7 .x6 (32 : BitVec 13),
    .ADD .x28 .x8 .x7,
    .LBU .x29 .x28 (40 : BitVec 12),
    .ADD .x28 .x5 .x7,
    .LBU .x30 .x28 (0 : BitVec 12),
    .BNE .x29 .x30 (36 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LD .x11 .x8 (72 : BitVec 12),
    .ADDI .x10 .x8 (80 : BitVec 12),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.extract_deposit_data (GuestAddrs.parse_deposit_requests + 172)),
    .BNE .x10 .x0 (36 : BitVec 13),
    .ADDI .x18 .x18 (192 : BitVec 12),
    .LD .x5 .x8 (72 : BitVec 12),
    .ADDI .x5 .x5 (7 : BitVec 12),
    .ANDI .x5 .x5 (-8 : BitVec 12),
    .ADDI .x5 .x5 (80 : BitVec 12),
    .ADD .x8 .x8 .x5,
    .ADDI .x9 .x9 (-1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.parse_deposit_requests + 52) (GuestAddrs.parse_deposit_requests + 208)),
    .LI .x5 (1 : Word),
    .SD .x20 .x5 (0 : BitVec 12),
    .SUB .x10 .x18 .x19,
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (56 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `parseDepositRequests_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def parseDepositRequests_relocs : RelocTable :=
  [ (14, .la .x5 "pdr_deposit_addr"),
    (28, .la .x5 "pdr_deposit_sig"),
    (43, .jal .x1 "extract_deposit_data") ]

def parseDepositRequestsFunction : String :=
  "parse_deposit_requests:\n" ++ emitProgramR parseDepositRequests_prog parseDepositRequests_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `parseDepositRequests_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem parseDepositRequestsFunction_eq_prog :
    parseDepositRequestsFunction = "parse_deposit_requests:\n" ++ emitProgramR parseDepositRequests_prog parseDepositRequests_relocs := rfl

#guard parseDepositRequestsFunction.startsWith "parse_deposit_requests:\n"
#guard parseDepositRequests_prog.length = 64
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


end EvmAsm.Codegen
