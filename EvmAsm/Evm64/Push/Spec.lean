/-
  EvmAsm.Evm64.Push.Spec

  Specs for the EVM PUSH1..PUSH32 opcode family. Three-level architecture
  per `docs/push-opcode-design.md`:

    1. Per-byte helper:        `push_one_byte_spec_within` (this file)
    2. Generic n-byte spec:    (slice 4)
    3. EvmWord/stack spec:     (slice 4 / slice 5)

  This sub-slice (#101 sub-slice, parent evm-asm-ou3t) lands only the
  level-1 building block: the 2-instruction LBU+SB pair that copies one
  byte from the EVM code region (at `codePtr + codeOff`) into the new
  stack slot (at `sp + dstOff`).

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.Push.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Per-byte helper (mirror of `dup_pair_spec_within` for LBU+SB)
-- ============================================================================

/-- Two-instruction spec for one PUSH byte: LBU x7 from EVM code at
    `codePtr + codeOff`, then SB x7 to the new stack slot at
    `sp + dstOff`.

    `codeDwordAddr` / `dstDwordAddr` are the `alignToDword` of the source
    and destination byte addresses (in general distinct). Both bytes must
    satisfy the byte-validity precondition. The post records that `x7`
    holds the freshly-loaded byte (zero-extended to 64 bits) and that the
    destination doubleword has had its target byte replaced. -/
theorem push_one_byte_spec_within
    (codePtr sp v7Old codeWord dstWordOld : Word)
    (codeDwordAddr dstDwordAddr : Word)
    (codeOff dstOff : BitVec 12) (base : Word)
    (h_code_align : alignToDword (codePtr + signExtend12 codeOff) = codeDwordAddr)
    (h_code_valid : isValidByteAccess (codePtr + signExtend12 codeOff) = true)
    (h_dst_align  : alignToDword (sp + signExtend12 dstOff) = dstDwordAddr)
    (h_dst_valid  : isValidByteAccess (sp + signExtend12 dstOff) = true) :
    let byteZext :=
      (extractByte codeWord (byteOffset (codePtr + signExtend12 codeOff))).zeroExtend 64
    cpsTripleWithin 2 base (base + 8)
      ((CodeReq.singleton base (.LBU .x7 .x10 codeOff)).union
        (CodeReq.singleton (base + 4) (.SB .x12 .x7 dstOff)))
      ((.x10 ↦ᵣ codePtr) ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7Old) **
       (codeDwordAddr ↦ₘ codeWord) ** (dstDwordAddr ↦ₘ dstWordOld))
      ((.x10 ↦ᵣ codePtr) ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ byteZext) **
       (codeDwordAddr ↦ₘ codeWord) **
       (dstDwordAddr ↦ₘ
         replaceByte dstWordOld (byteOffset (sp + signExtend12 dstOff))
           (byteZext.truncate 8))) := by
  intro byteZext
  have L := lbu_spec_gen_within .x7 .x10 codePtr v7Old codeOff base
    codeDwordAddr codeWord (by nofun) h_code_align h_code_valid
  have S := sb_spec_gen_within .x12 .x7 sp byteZext dstOff (base + 4)
    dstDwordAddr dstWordOld h_dst_align h_dst_valid
  runBlock L S

end EvmAsm.Evm64
