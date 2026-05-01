/-
  EvmAsm.Evm64.MStore8.Spec

  Slice 5 of issue #99 — MSTORE8 spec.

  MSTORE8 in the EVM writes the LOW byte of a 256-bit operand to a single
  byte of EVM memory. The slice 5 plan asks for a "single SB spec"; this
  file provides exactly that, packaged at the EVM-memory layer:

  * `evm_mstore8_kernel_spec_within` — a thin wrapper around the generic
    `sb_spec_gen_within` that carries the byte address in a register and
    leaves the dword cell holding the byte exposed as a raw `↦ₘ`. Lifting
    to `evmMemIs` (which views memory as a sequence of dword cells) is
    deferred to consumer slices that frame in/out the relevant cell.

  Memory-expansion bookkeeping is a pure-Nat update on the high-water
  mark; a one-byte access at offset `o` expands the size to
  `max sizeBytes (roundUpTo32 (o + 1))`. The lemma
  `evmMemExpand_one_byte_eq` exposes this fact for the consumer slices
  that want to thread `evmMemSizeIs` through the spec.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.MStore8.Program
import EvmAsm.Evm64.Memory
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- MSTORE8 byte-write kernel spec: composes `sb_spec_gen_within` for the
    one SB instruction. The dword cell containing the target byte is
    threaded through as a raw `↦ₘ`; consumer slices frame it in/out of
    `evmMemIs` as needed. -/
theorem evm_mstore8_kernel_spec_within
    (addrReg dataReg : Reg) (v_addr v_data : Word)
    (base : Word) (dwordAddr wordOld : Word)
    (halign : alignToDword v_addr = dwordAddr)
    (hvalid : isValidByteAccess v_addr = true) :
    let code := evm_mstore8_kernel_code addrReg dataReg base
    cpsTripleWithin 1 base (base + 4) code
      ((addrReg ↦ᵣ v_addr) ** (dataReg ↦ᵣ v_data) ** (dwordAddr ↦ₘ wordOld))
      ((addrReg ↦ᵣ v_addr) ** (dataReg ↦ᵣ v_data) **
       (dwordAddr ↦ₘ replaceByte wordOld (byteOffset v_addr) (v_data.truncate 8))) := by
  -- The SB offset is 0, so `v_addr + signExtend12 0 = v_addr`. Rewrite the
  -- generic spec hypotheses to match.
  have h_off : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have halign' : alignToDword (v_addr + signExtend12 (0 : BitVec 12)) = dwordAddr := by
    rw [h_off]; simpa using halign
  have hvalid' : isValidByteAccess (v_addr + signExtend12 (0 : BitVec 12)) = true := by
    rw [h_off]; simpa using hvalid
  have hSB := sb_spec_gen_within addrReg dataReg v_addr v_data
                (0 : BitVec 12) base dwordAddr wordOld halign' hvalid'
  -- Rewrite the byte-offset in the post via h_off.
  have hbo : byteOffset (v_addr + signExtend12 (0 : BitVec 12)) = byteOffset v_addr := by
    rw [h_off]; simp
  rw [hbo] at hSB
  exact hSB

/-! ## EVM memory expansion for a one-byte access

  MSTORE8 writes one byte at offset `o`, so the access is `(o, 1)` and
  the high-water-mark update is `max sizeBytes (roundUpTo32 (o + 1))`.
  This lemma is the pure-Nat helper the consumer slice will use to
  discharge the size update next to `evm_mstore8_kernel_spec_within`. -/

theorem evmMemExpand_one_byte_eq (sizeBytes offset : Nat) :
    evmMemExpand sizeBytes offset 1 = max sizeBytes (roundUpTo32 (offset + 1)) := by
  unfold evmMemExpand; simp

end EvmAsm.Evm64
