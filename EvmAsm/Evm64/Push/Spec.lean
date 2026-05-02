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
-- Stack slot allocation and zero-fill prefix
-- ============================================================================

def push_zero_slot_code (base : Word) : CodeReq :=
  (CodeReq.singleton base (.ADDI .x12 .x12 (-32))).union
    ((CodeReq.singleton (base + 4) (.SD .x12 .x0 0)).union
      ((CodeReq.singleton (base + 8) (.SD .x12 .x0 8)).union
        ((CodeReq.singleton (base + 12) (.SD .x12 .x0 16)).union
          (CodeReq.singleton (base + 16) (.SD .x12 .x0 24)))))

theorem push_zero_slot_code_eq_ofProg (base : Word) :
    push_zero_slot_code base =
      CodeReq.ofProg base
        (ADDI .x12 .x12 (-32) ;; SD .x12 .x0 0 ;; SD .x12 .x0 8 ;;
         SD .x12 .x0 16 ;; SD .x12 .x0 24) := by
  unfold push_zero_slot_code ADDI SD single seq
  change _ = CodeReq.ofProg base
    [.ADDI .x12 .x12 (-32), .SD .x12 .x0 0, .SD .x12 .x0 8,
     .SD .x12 .x0 16, .SD .x12 .x0 24]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  bv_addr

theorem push_zero_slot_spec_within
    (sp d0 d1 d2 d3 : Word) (base : Word) :
    let nsp := sp + signExtend12 ((-32 : BitVec 12))
    cpsTripleWithin 5 base (base + 20) (push_zero_slot_code base)
      ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       ((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x12 ↦ᵣ nsp) ** (.x0 ↦ᵣ (0 : Word)) **
       ((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word))) := by
  intro nsp
  unfold push_zero_slot_code
  have hAlloc := addi_spec_gen_same_within .x12 sp
    (-32 : BitVec 12) base (by decide)
  have hSd0 := generic_sd_spec_within .x12 .x0 nsp (0 : Word) d0
    (0 : BitVec 12) (base + 4)
  have hSd1 := generic_sd_spec_within .x12 .x0 nsp (0 : Word) d1
    (8 : BitVec 12) (base + 8)
  have hSd2 := generic_sd_spec_within .x12 .x0 nsp (0 : Word) d2
    (16 : BitVec 12) (base + 12)
  have hSd3 := generic_sd_spec_within .x12 .x0 nsp (0 : Word) d3
    (24 : BitVec 12) (base + 16)
  runBlock hAlloc hSd0 hSd1 hSd2 hSd3

theorem push_zero_slot_ofProg_spec_within
    (sp d0 d1 d2 d3 : Word) (base : Word) :
    let nsp := sp + signExtend12 ((-32 : BitVec 12))
    cpsTripleWithin 5 base (base + 20)
      (CodeReq.ofProg base
        (ADDI .x12 .x12 (-32) ;; SD .x12 .x0 0 ;; SD .x12 .x0 8 ;;
         SD .x12 .x0 16 ;; SD .x12 .x0 24))
      ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       ((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x12 ↦ᵣ nsp) ** (.x0 ↦ᵣ (0 : Word)) **
       ((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word))) := by
  intro nsp
  rw [← push_zero_slot_code_eq_ofProg]
  exact push_zero_slot_spec_within sp d0 d1 d2 d3 base

theorem evm_push_zero_slot_code_spec_within
    (n : Nat) (hn : n ≤ 32) (sp d0 d1 d2 d3 : Word) (base : Word) :
    let nsp := sp + signExtend12 ((-32 : BitVec 12))
    cpsTripleWithin 5 base (base + 20) (evm_push_code base n)
      ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       ((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x12 ↦ᵣ nsp) ** (.x0 ↦ᵣ (0 : Word)) **
       ((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word))) := by
  intro nsp
  have hPrefix := push_zero_slot_ofProg_spec_within sp d0 d1 d2 d3 base
  exact cpsTripleWithin_extend_code (h := hPrefix) (hmono := by
    unfold evm_push_code
    exact CodeReq.ofProg_mono_sub base base (evm_push n)
      (ADDI .x12 .x12 (-32) ;; SD .x12 .x0 0 ;; SD .x12 .x0 8 ;;
       SD .x12 .x0 16 ;; SD .x12 .x0 24) 0
      (by bv_omega)
      (by
        unfold evm_push ADDI SD single seq
        rfl)
      (by
        change 0 + 5 ≤ (evm_push n).length
        rw [evm_push_length]
        omega)
      (by
        rw [evm_push_length]
        omega))

/-- The four zero-filled limbs written by the PUSH allocation prefix fold to
    the EVM word value `0`. -/
theorem push_zero_slot_word_zero (nsp : Word) :
    (((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word))) =
    evmWordIs nsp (0 : EvmWord) := by
  rw [evmWordIs_zero]
  simp only [signExtend12]
  congr
  all_goals bv_decide

/-- Right-associated variant of `push_zero_slot_word_zero` for composing byte
    copy postconditions after the zero-fill prefix. -/
theorem push_zero_slot_word_zero_right (nsp : Word) (Q : Assertion) :
    (((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) ** Q) =
    (evmWordIs nsp (0 : EvmWord) ** Q) := by
  have h0 : (nsp + signExtend12 (0 : BitVec 12) : Word) = nsp := by
    unfold signExtend12; bv_decide
  have h8 : (nsp + signExtend12 (8 : BitVec 12) : Word) = nsp + 8 := by
    unfold signExtend12; bv_decide
  have h16 : (nsp + signExtend12 (16 : BitVec 12) : Word) = nsp + 16 := by
    unfold signExtend12; bv_decide
  have h24 : (nsp + signExtend12 (24 : BitVec 12) : Word) = nsp + 24 := by
    unfold signExtend12; bv_decide
  rw [h0, h8, h16, h24]
  rw [evmWordIs_zero_right]

-- ============================================================================
-- Per-byte helper (mirror of `dup_pair_spec_within` for LBU+SB)
-- ============================================================================

theorem push_one_byte_code_eq_ofProg
    (base : Word) (codeOff dstOff : BitVec 12) :
    ((CodeReq.singleton base (.LBU .x7 .x10 codeOff)).union
      (CodeReq.singleton (base + 4) (.SB .x12 .x7 dstOff))) =
    CodeReq.ofProg base
      (LBU .x7 .x10 codeOff ;; SB .x12 .x7 dstOff) := by
  unfold LBU SB single seq
  change _ =
    CodeReq.ofProg base
      [.LBU .x7 .x10 codeOff, .SB .x12 .x7 dstOff]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_singleton]

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

theorem push_one_byte_ofProg_spec_within
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
      (CodeReq.ofProg base (LBU .x7 .x10 codeOff ;; SB .x12 .x7 dstOff))
      ((.x10 ↦ᵣ codePtr) ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7Old) **
       (codeDwordAddr ↦ₘ codeWord) ** (dstDwordAddr ↦ₘ dstWordOld))
      ((.x10 ↦ᵣ codePtr) ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ byteZext) **
       (codeDwordAddr ↦ₘ codeWord) **
       (dstDwordAddr ↦ₘ
         replaceByte dstWordOld (byteOffset (sp + signExtend12 dstOff))
           (byteZext.truncate 8))) := by
  intro byteZext
  rw [← push_one_byte_code_eq_ofProg]
  exact push_one_byte_spec_within codePtr sp v7Old codeWord dstWordOld
    codeDwordAddr dstDwordAddr codeOff dstOff base
    h_code_align h_code_valid h_dst_align h_dst_valid

end EvmAsm.Evm64
