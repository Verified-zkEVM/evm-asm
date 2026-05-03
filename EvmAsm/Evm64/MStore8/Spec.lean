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
import EvmAsm.Rv64.Tactics.XSimp

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

/-- Full MSTORE8 executable spec: load the low offset and value limbs from
    the EVM stack, compute `memBase + offset`, store the low byte of the
    value, and pop the two consumed stack words. -/
theorem evm_mstore8_spec_within
    (offReg valReg addrReg memBaseReg : Reg)
    (sp memBase offOld valOld addrOld offset valueLow wordOld : Word)
    (base dwordAddr : Word)
    (hoff_ne_x0 : offReg ≠ .x0)
    (hval_ne_x0 : valReg ≠ .x0)
    (haddr_ne_x0 : addrReg ≠ .x0)
    (halign : alignToDword (memBase + offset) = dwordAddr)
    (hvalid : isValidByteAccess (memBase + offset) = true) :
    let targetAddr := memBase + offset
    cpsTripleWithin 5 base (base + 20)
      (evm_mstore8_code offReg valReg addrReg memBaseReg base)
      ((.x12 ↦ᵣ sp) ** (memBaseReg ↦ᵣ memBase) **
       (offReg ↦ᵣ offOld) ** (valReg ↦ᵣ valOld) ** (addrReg ↦ᵣ addrOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ offset) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ valueLow) **
       (dwordAddr ↦ₘ wordOld))
      ((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
       (memBaseReg ↦ᵣ memBase) **
       (offReg ↦ᵣ offset) ** (valReg ↦ᵣ valueLow) **
       (addrReg ↦ᵣ targetAddr) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ offset) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ valueLow) **
       (dwordAddr ↦ₘ
        replaceByte wordOld (byteOffset targetAddr) (valueLow.truncate 8))) := by
  intro targetAddr
  have hLoadOff := ld_spec_gen_within offReg .x12 sp offOld offset
    (0 : BitVec 12) base hoff_ne_x0
  have hLoadVal := ld_spec_gen_within valReg .x12 sp valOld valueLow
    (32 : BitVec 12) (base + 4) hval_ne_x0
  have hAdd := add_spec_gen_within addrReg memBaseReg offReg
    memBase offset addrOld (base + 8) haddr_ne_x0
  have h_zero : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have halign_store :
      alignToDword (targetAddr + signExtend12 (0 : BitVec 12)) = dwordAddr := by
    rw [h_zero]
    simpa [targetAddr] using halign
  have hvalid_store :
      isValidByteAccess (targetAddr + signExtend12 (0 : BitVec 12)) = true := by
    rw [h_zero]
    simpa [targetAddr] using hvalid
  have hStore := sb_spec_gen_within addrReg valReg targetAddr valueLow
    (0 : BitVec 12) (base + 12) dwordAddr wordOld halign_store hvalid_store
  have hStore' : cpsTripleWithin 1 (base + 12) ((base + 12) + 4)
      (CodeReq.singleton (base + 12) (.SB addrReg valReg 0))
      ((addrReg ↦ᵣ targetAddr) ** (valReg ↦ᵣ valueLow) ** (dwordAddr ↦ₘ wordOld))
      ((addrReg ↦ᵣ targetAddr) ** (valReg ↦ᵣ valueLow) **
       (dwordAddr ↦ₘ replaceByte wordOld (byteOffset targetAddr) (valueLow.truncate 8))) := by
    rw [show byteOffset (targetAddr + signExtend12 (0 : BitVec 12)) =
        byteOffset targetAddr by rw [h_zero]; simp] at hStore
    exact hStore
  have hPop := addi_spec_gen_same_within .x12 sp (64 : BitVec 12)
    (base + 16) (by nofun)
  unfold evm_mstore8_code evm_mstore8 LD ADD ADDI SB single seq
  change cpsTripleWithin 5 base (base + 20)
    (CodeReq.ofProg base
      [.LD offReg .x12 0, .LD valReg .x12 32, .ADD addrReg memBaseReg offReg,
       .SB addrReg valReg 0, .ADDI .x12 .x12 64])
    _ _
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  rw [show (base + 4 : Word) + 4 = base + 8 by bv_addr]
  rw [show (base + 8 : Word) + 4 = base + 12 by bv_addr]
  rw [show (base + 12 : Word) + 4 = base + 16 by bv_addr]
  runBlock hLoadOff hLoadVal hAdd hStore' hPop

/-- Stack-level lift of the full MSTORE8 handler. The two consumed EVM stack
    words remain owned as memory, matching the convention used by `POP`;
    `x12` advances past them and the selected memory byte is updated from the
    low byte of the value word. -/
theorem evm_mstore8_stack_spec_within
    (offReg valReg addrReg memBaseReg : Reg)
    (sp memBase offOld valOld addrOld wordOld : Word)
    (base dwordAddr : Word)
    (offsetWord valueWord : EvmWord) (rest : List EvmWord)
    (hoff_ne_x0 : offReg ≠ .x0)
    (hval_ne_x0 : valReg ≠ .x0)
    (haddr_ne_x0 : addrReg ≠ .x0)
    (halign : alignToDword (memBase + offsetWord.getLimbN 0) = dwordAddr)
    (hvalid : isValidByteAccess (memBase + offsetWord.getLimbN 0) = true) :
    let targetAddr := memBase + offsetWord.getLimbN 0
    cpsTripleWithin 5 base (base + 20)
      (evm_mstore8_code offReg valReg addrReg memBaseReg base)
      ((.x12 ↦ᵣ sp) ** (memBaseReg ↦ᵣ memBase) **
       (offReg ↦ᵣ offOld) ** (valReg ↦ᵣ valOld) ** (addrReg ↦ᵣ addrOld) **
       evmWordIs sp offsetWord ** evmWordIs (sp + 32) valueWord **
       evmStackIs (sp + 64) rest ** (dwordAddr ↦ₘ wordOld))
      ((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
       (memBaseReg ↦ᵣ memBase) **
       (offReg ↦ᵣ offsetWord.getLimbN 0) ** (valReg ↦ᵣ valueWord.getLimbN 0) **
       (addrReg ↦ᵣ targetAddr) **
       evmWordIs sp offsetWord ** evmWordIs (sp + 32) valueWord **
       evmStackIs (sp + 64) rest **
       (dwordAddr ↦ₘ
        replaceByte wordOld (byteOffset targetAddr)
          ((valueWord.getLimbN 0).truncate 8))) := by
  intro targetAddr
  let offset := offsetWord.getLimbN 0
  let valueLow := valueWord.getLimbN 0
  let frame : Assertion :=
    ((sp + 8) ↦ₘ offsetWord.getLimbN 1) **
    ((sp + 16) ↦ₘ offsetWord.getLimbN 2) **
    ((sp + 24) ↦ₘ offsetWord.getLimbN 3) **
    (((sp + 32) + 8) ↦ₘ valueWord.getLimbN 1) **
    (((sp + 32) + 16) ↦ₘ valueWord.getLimbN 2) **
    (((sp + 32) + 24) ↦ₘ valueWord.getLimbN 3) **
    evmStackIs (sp + 64) rest
  have hRaw := evm_mstore8_spec_within offReg valReg addrReg memBaseReg
    sp memBase offOld valOld addrOld offset valueLow wordOld base dwordAddr
    hoff_ne_x0 hval_ne_x0 haddr_ne_x0
    (by simpa [offset] using halign)
    (by simpa [offset] using hvalid)
  have hRawNorm : cpsTripleWithin 5 base (base + 20)
      (evm_mstore8_code offReg valReg addrReg memBaseReg base)
      ((.x12 ↦ᵣ sp) ** (memBaseReg ↦ᵣ memBase) **
       (offReg ↦ᵣ offOld) ** (valReg ↦ᵣ valOld) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset) ** ((sp + 32) ↦ₘ valueLow) ** (dwordAddr ↦ₘ wordOld))
      ((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
       (memBaseReg ↦ᵣ memBase) **
       (offReg ↦ᵣ offset) ** (valReg ↦ᵣ valueLow) **
       (addrReg ↦ᵣ targetAddr) **
       (sp ↦ₘ offset) ** ((sp + 32) ↦ₘ valueLow) **
      (dwordAddr ↦ₘ
        replaceByte wordOld (byteOffset targetAddr) (valueLow.truncate 8))) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        rw [show sp + signExtend12 (0 : BitVec 12) = sp from by
          rw [signExtend12_0]; bv_omega]
        rw [show sp + signExtend12 (32 : BitVec 12) = sp + 32 from by
          rw [signExtend12_32]]
        xperm_hyp hp)
      (fun _ hp => by
        rw [show sp + signExtend12 (0 : BitVec 12) = sp from by
          rw [signExtend12_0]; bv_omega] at hp
        rw [show sp + signExtend12 (32 : BitVec 12) = sp + 32 from by
          rw [signExtend12_32]] at hp
        xperm_hyp hp)
      hRaw
  have hFramed := cpsTripleWithin_frameR frame (by pcFree) hRawNorm
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [frame, evmWordIs] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      dsimp [frame, evmWordIs] at hp ⊢
      xperm_hyp hp)
    hFramed

/-- Stack-level MSTORE8 spec with the postcondition stack pointer normalized
    from the sign-extended ADDI immediate to the usual `sp + 64` surface form. -/
theorem evm_mstore8_stack_spec_clean_sp_within
    (offReg valReg addrReg memBaseReg : Reg)
    (sp memBase offOld valOld addrOld wordOld : Word)
    (base dwordAddr : Word)
    (offsetWord valueWord : EvmWord) (rest : List EvmWord)
    (hoff_ne_x0 : offReg ≠ .x0)
    (hval_ne_x0 : valReg ≠ .x0)
    (haddr_ne_x0 : addrReg ≠ .x0)
    (halign : alignToDword (memBase + offsetWord.getLimbN 0) = dwordAddr)
    (hvalid : isValidByteAccess (memBase + offsetWord.getLimbN 0) = true) :
    let targetAddr := memBase + offsetWord.getLimbN 0
    cpsTripleWithin 5 base (base + 20)
      (evm_mstore8_code offReg valReg addrReg memBaseReg base)
      ((.x12 ↦ᵣ sp) ** (memBaseReg ↦ᵣ memBase) **
       (offReg ↦ᵣ offOld) ** (valReg ↦ᵣ valOld) ** (addrReg ↦ᵣ addrOld) **
       evmWordIs sp offsetWord ** evmWordIs (sp + 32) valueWord **
       evmStackIs (sp + 64) rest ** (dwordAddr ↦ₘ wordOld))
      ((.x12 ↦ᵣ (sp + 64)) **
       (memBaseReg ↦ᵣ memBase) **
       (offReg ↦ᵣ offsetWord.getLimbN 0) ** (valReg ↦ᵣ valueWord.getLimbN 0) **
       (addrReg ↦ᵣ targetAddr) **
       evmWordIs sp offsetWord ** evmWordIs (sp + 32) valueWord **
       evmStackIs (sp + 64) rest **
       (dwordAddr ↦ₘ
        replaceByte wordOld (byteOffset targetAddr)
          ((valueWord.getLimbN 0).truncate 8))) := by
  intro targetAddr
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by
      have hsp : sp + signExtend12 (64 : BitVec 12) = sp + 64 := by
        rw [show signExtend12 (64 : BitVec 12) = (64 : Word) by decide]
      simpa [hsp] using hp)
    (evm_mstore8_stack_spec_within offReg valReg addrReg memBaseReg
      sp memBase offOld valOld addrOld wordOld base dwordAddr
      offsetWord valueWord rest hoff_ne_x0 hval_ne_x0 haddr_ne_x0
      halign hvalid)

/-! ## EVM memory expansion for a one-byte access

  MSTORE8 writes one byte at offset `o`, so the access is `(o, 1)` and
  the high-water-mark update is `max sizeBytes (roundUpTo32 (o + 1))`.
  This lemma is the pure-Nat helper the consumer slice will use to
  discharge the size update next to `evm_mstore8_kernel_spec_within`. -/

theorem evmMemExpand_one_byte_eq (sizeBytes offset : Nat) :
    evmMemExpand sizeBytes offset 1 = max sizeBytes (roundUpTo32 (offset + 1)) := by
  unfold evmMemExpand; simp

end EvmAsm.Evm64
