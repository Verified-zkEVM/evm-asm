/-
  EvmAsm.Codegen.Programs.AssembleExecutionRequests

  `assemble_execution_requests` (bead evm-asm-8uld3.4, EIP-7685) — assemble the
  SSZ `ExecutionRequests` section from the five EXECUTION-DERIVED request bodies
  (deposits via `parse_deposit_requests` #8657; withdrawals/consolidations from the
  EIP-7002/7251 system-call return data), so the existing `execution_requests_hash`
  (RequestsHash.lean) computes the post-execution `requests_hash` from what execution
  actually produced — instead of trusting the SSZ `execution_requests` input. The
  verdict then compares the derived hash to `header.requests_hash`.

  SSZ `ExecutionRequests` is an SSZ container of five variable-length byte fields,
  so its serialization is `[u32 off0]...[u32 off4][deposits][withdrawals]
  [consolidations][builder_deposits][builder_exits]` with `off0 = 20` and each
  subsequent offset advanced by the preceding body (little-endian offsets, relative
  to the section start). The bodies
  are the RAW request payloads with NO type prefix — `execution_requests_hash` adds the
  per-position type byte (0x00/0x01/0x02/0x03/0x04) when it hashes (see RequestsHash.lean).

  Standalone + probe-verifiable: the execution-gated piece is GETTING the five derived
  bodies (the deposit body is #8657; the system-call bodies need the EIP-7002/7251 system
  transactions, bmvmx.1.4 spine). This assembly + the reuse of `execution_requests_hash`
  is the compute core.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## assemble_execution_requests
    a0 = deposit body ptr        a1 = deposit body length
    a2 = withdrawal body ptr     a3 = withdrawal body length
    a4 = consolidation body ptr  a5 = consolidation body length
    a6 = output SSZ section ptr. Builder deposit/exit ptrs and lengths are supplied
    through `aer_bd_*`/`aer_be_*` globals so existing six-argument callers remain
    ABI-compatible (kept deliberately — a caller that silently loses its globals is a
    wrong-value defect r200 need not surface). a0 (output) = total SSZ section length.

    Converted to `Program` under #12011 (maintainer waived byte-identity). Five
    top-tested byte-copy loops; builder deposit/exit via `aer_bd_*`/`aer_be_*`
    globals kept deliberately for six-argument caller ABI compatibility. -/
def assembleExecutionRequests_prog : Program :=
  [ .LI .x5 (20 : Word),
    .SW .x16 .x5 (0 : BitVec 12),
    .ADD .x5 .x5 .x11,
    .SW .x16 .x5 (4 : BitVec 12),
    .ADD .x5 .x5 .x13,
    .SW .x16 .x5 (8 : BitVec 12),
    .ADD .x5 .x5 .x15,
    .SW .x16 .x5 (12 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.aer_bd_len (GuestAddrs.assemble_execution_requests + 32)),
    .ADDI .x7 .x7 (laLo GuestAddrs.aer_bd_len (GuestAddrs.assemble_execution_requests + 32)),
    .LD .x28 .x7 (0 : BitVec 12),
    .ADD .x5 .x5 .x28,
    .SW .x16 .x5 (16 : BitVec 12),
    .ADDI .x6 .x16 (20 : BitVec 12),
    .MV .x7 .x10,
    .MV .x28 .x11,
    .BEQ .x28 .x0 (28 : BitVec 13),
    .LBU .x29 .x7 (0 : BitVec 12),
    .SB .x6 .x29 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .MV .x7 .x12,
    .MV .x28 .x13,
    .BEQ .x28 .x0 (28 : BitVec 13),
    .LBU .x29 .x7 (0 : BitVec 12),
    .SB .x6 .x29 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .MV .x7 .x14,
    .MV .x28 .x15,
    .BEQ .x28 .x0 (28 : BitVec 13),
    .LBU .x29 .x7 (0 : BitVec 12),
    .SB .x6 .x29 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .AUIPC .x7 (laHi GuestAddrs.aer_bd_ptr (GuestAddrs.assemble_execution_requests + 164)),
    .ADDI .x7 .x7 (laLo GuestAddrs.aer_bd_ptr (GuestAddrs.assemble_execution_requests + 164)),
    .LD .x7 .x7 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.aer_bd_len (GuestAddrs.assemble_execution_requests + 176)),
    .ADDI .x28 .x28 (laLo GuestAddrs.aer_bd_len (GuestAddrs.assemble_execution_requests + 176)),
    .LD .x28 .x28 (0 : BitVec 12),
    .BEQ .x28 .x0 (28 : BitVec 13),
    .LBU .x29 .x7 (0 : BitVec 12),
    .SB .x6 .x29 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .AUIPC .x7 (laHi GuestAddrs.aer_be_ptr (GuestAddrs.assemble_execution_requests + 216)),
    .ADDI .x7 .x7 (laLo GuestAddrs.aer_be_ptr (GuestAddrs.assemble_execution_requests + 216)),
    .LD .x7 .x7 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.aer_be_len (GuestAddrs.assemble_execution_requests + 228)),
    .ADDI .x28 .x28 (laLo GuestAddrs.aer_be_len (GuestAddrs.assemble_execution_requests + 228)),
    .LD .x28 .x28 (0 : BitVec 12),
    .BEQ .x28 .x0 (28 : BitVec 13),
    .LBU .x29 .x7 (0 : BitVec 12),
    .SB .x6 .x29 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .LI .x10 (20 : Word),
    .ADD .x10 .x10 .x11,
    .ADD .x10 .x10 .x13,
    .ADD .x10 .x10 .x15,
    .AUIPC .x7 (laHi GuestAddrs.aer_bd_len (GuestAddrs.assemble_execution_requests + 284)),
    .ADDI .x7 .x7 (laLo GuestAddrs.aer_bd_len (GuestAddrs.assemble_execution_requests + 284)),
    .LD .x28 .x7 (0 : BitVec 12),
    .ADD .x10 .x10 .x28,
    .AUIPC .x7 (laHi GuestAddrs.aer_be_len (GuestAddrs.assemble_execution_requests + 300)),
    .ADDI .x7 .x7 (laLo GuestAddrs.aer_be_len (GuestAddrs.assemble_execution_requests + 300)),
    .LD .x28 .x7 (0 : BitVec 12),
    .ADD .x10 .x10 .x28,
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `assembleExecutionRequests_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def assembleExecutionRequests_relocs : RelocTable :=
  [ (8, .la .x7 "aer_bd_len"),
    (41, .la .x7 "aer_bd_ptr"),
    (44, .la .x28 "aer_bd_len"),
    (54, .la .x7 "aer_be_ptr"),
    (57, .la .x28 "aer_be_len"),
    (71, .la .x7 "aer_bd_len"),
    (75, .la .x7 "aer_be_len") ]

def assembleExecutionRequestsFunction : String :=
  "assemble_execution_requests:\n" ++ emitProgramR assembleExecutionRequests_prog assembleExecutionRequests_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `assembleExecutionRequests_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem assembleExecutionRequestsFunction_eq_prog :
    assembleExecutionRequestsFunction = "assemble_execution_requests:\n" ++ emitProgramR assembleExecutionRequests_prog assembleExecutionRequests_relocs := rfl

#guard assembleExecutionRequestsFunction.startsWith "assemble_execution_requests:\n"
#guard assembleExecutionRequests_prog.length = 80

/-! ## requests_hash_verify
    Verify the EIP-7685 `requests_hash` derived from the five execution-produced request
    bodies against an expected (header) hash — the post-execution check `block_verdict` runs
    once execution provides the bodies (8uld3.4: stop trusting the SSZ execution_requests).
      a0/a1 = deposit ptr/len   a2/a3 = withdrawal ptr/len   a4/a5 = consolidation ptr/len
      a6 = expected 32-byte requests_hash ptr (header value)
      a7 = scratch SSZ section buffer ptr (>= 20 + all five body lengths bytes, 8-aligned)
      a0 (output) = 0 match / 1 mismatch / 2 malformed (section rejected by SSZ length rules). -/
def requestsHashVerify_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x16,
    .MV .x9 .x17,
    .MV .x16 .x17,
    .JAL .x1 (jalOff GuestAddrs.assemble_execution_requests (GuestAddrs.requests_hash_verify + 28)),
    .MV .x11 .x10,
    .MV .x10 .x9,
    .AUIPC .x12 (laHi GuestAddrs.rhv_hash (GuestAddrs.requests_hash_verify + 40)),
    .ADDI .x12 .x12 (laLo GuestAddrs.rhv_hash (GuestAddrs.requests_hash_verify + 40)),
    .JAL .x1 (jalOff GuestAddrs.execution_requests_hash (GuestAddrs.requests_hash_verify + 48)),
    .BNE .x10 .x0 (68 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.rhv_hash (GuestAddrs.requests_hash_verify + 56)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rhv_hash (GuestAddrs.requests_hash_verify + 56)),
    .MV .x6 .x8,
    .LI .x7 (32 : Word),
    .BEQ .x7 .x0 (32 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .LBU .x29 .x6 (0 : BitVec 12),
    .BNE .x28 .x29 (28 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `requestsHashVerify_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def requestsHashVerify_relocs : RelocTable :=
  [ (7, .jal .x1 "assemble_execution_requests"),
    (10, .la .x12 "rhv_hash"),
    (12, .jal .x1 "execution_requests_hash"),
    (14, .la .x5 "rhv_hash") ]

def requestsHashVerifyFunction : String :=
  "requests_hash_verify:\n" ++ emitProgramR requestsHashVerify_prog requestsHashVerify_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `requestsHashVerify_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem requestsHashVerifyFunction_eq_prog :
    requestsHashVerifyFunction = "requests_hash_verify:\n" ++ emitProgramR requestsHashVerify_prog requestsHashVerify_relocs := rfl

#guard requestsHashVerifyFunction.startsWith "requests_hash_verify:\n"
#guard requestsHashVerify_prog.length = 36
/-- `zisk_assemble_execution_requests`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : deposit body length        (multiple of 192)
      bytes 16..24 : withdrawal body length      (multiple of 76)
      bytes 24..32 : consolidation body length   (multiple of 116)
      bytes 32..40 : builder-deposit body length (multiple of 184)
      bytes 40..48 : builder-exit body length    (multiple of 68)
      bytes 48..    : the five bodies concatenated in type order
    Output:
      +0  status (0 ok / 1 execution_requests_hash rejected the assembled section)
      +8  total SSZ section length
      +16 the derived requests_hash (32 bytes). -/
def ziskAssembleExecutionRequestsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # deposit len\n" ++
  "  ld a3, 16(a7)               # withdrawal len\n" ++
  "  ld a5, 24(a7)               # consolidation len\n" ++
  "  ld t0, 32(a7); la t1, aer_bd_len; sd t0, 0(t1)\n" ++
  "  ld t0, 40(a7); la t1, aer_be_len; sd t0, 0(t1)\n" ++
  "  addi a0, a7, 48             # deposit body ptr\n" ++
  "  add a2, a0, a1              # withdrawal body ptr\n" ++
  "  add a4, a2, a3              # consolidation body ptr\n" ++
  "  add t0, a4, a5; la t1, aer_bd_ptr; sd t0, 0(t1); la t2, aer_bd_len; ld t3, 0(t2); add t0, t0, t3; la t1, aer_be_ptr; sd t0, 0(t1)\n" ++
  "  la a6, aer_section\n" ++
  "  jal ra, assemble_execution_requests\n" ++
  "  la t0, aer_seclen; sd a0, 0(t0)        # save total length\n" ++
  "  la a0, aer_section; la t0, aer_seclen; ld a1, 0(t0); la a2, aer_hash\n" ++
  "  jal ra, execution_requests_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  la t1, aer_seclen; ld t2, 0(t1); sd t2, 8(t0)   # total length\n" ++
  "  la t1, aer_hash; addi t3, t0, 16; li t4, 32\n" ++
  ".Laerp_dump:\n" ++
  "  beqz t4, .Laerp_done\n" ++
  "  lbu t5, 0(t1); sb t5, 0(t3); addi t1, t1, 1; addi t3, t3, 1; addi t4, t4, -1; j .Laerp_dump\n" ++
  ".Laerp_done:\n" ++
  -- verify against the CORRECT (derived) hash -> 0; then corrupt it and verify -> 1.
  "  li a7, 0x40000000; ld a1, 8(a7); ld a3, 16(a7); ld a5, 24(a7)\n" ++
  "  addi a0, a7, 48; add a2, a0, a1; add a4, a2, a3\n" ++
  "  la a6, aer_hash; la a7, aer_section\n" ++
  "  jal ra, requests_hash_verify\n" ++
  "  li t0, 0xa0010000; sd a0, 48(t0)         # verify(correct) -> expect 0\n" ++
  "  la t0, aer_hash; lbu t1, 0(t0); xori t1, t1, 0xff; sb t1, 0(t0)   # corrupt the expected hash\n" ++
  "  li a7, 0x40000000; ld a1, 8(a7); ld a3, 16(a7); ld a5, 24(a7)\n" ++
  "  addi a0, a7, 48; add a2, a0, a1; add a4, a2, a3\n" ++
  "  la a6, aer_hash; la a7, aer_section\n" ++
  "  jal ra, requests_hash_verify\n" ++
  "  li t0, 0xa0010000; sd a0, 56(t0)         # verify(corrupted) -> expect 1\n" ++
  "  j .Laerp_pdone\n" ++
  assembleExecutionRequestsFunction ++ "\n" ++
  requestsHashVerifyFunction ++ "\n" ++
  executionRequestsHashFunctions ++ "\n" ++
  bgvU32leFunction ++ "\n" ++
  zkvmSha256Function ++ "\n" ++
  ".Laerp_pdone:"

def ziskAssembleExecutionRequestsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "aer_section:\n  .zero 65536\n" ++   -- room for the assembled SSZ section
  "aer_seclen:\n  .zero 8\n" ++
  "aer_bd_ptr:\n  .zero 8\naer_bd_len:\n  .zero 8\n" ++
  "aer_be_ptr:\n  .zero 8\naer_be_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "aer_hash:\n  .zero 32\n" ++
  "rhv_hash:\n  .zero 32\n" ++   -- requests_hash_verify's computed-hash scratch
  executionRequestsHashShaDataSection ++ "\n" ++
  executionRequestsHashDataSection

def ziskAssembleExecutionRequestsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAssembleExecutionRequestsPrologue
  dataAsm     := ziskAssembleExecutionRequestsDataSection
}

end EvmAsm.Codegen
