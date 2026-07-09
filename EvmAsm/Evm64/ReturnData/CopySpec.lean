/-
  EvmAsm.Evm64.ReturnData.CopySpec

  RETURNDATACOPY verification surface.

  `RevertSpec.lean` verifies the stack-form returndata bounds guard prefix:
  stack-low-limb loads, symbolic `la evm_precompile_frame`, return-data length
  load, the success fall-through, and all three invalid exits (`start+size`
  wrap, `start+size > retlen`, and the 256-byte frame cap).

  This file keeps the existing byte-copy witness
  (`evm_returndatacopy_stack_spec_within`) for the bottom-tested copy loop
  (`CopyLoopSpec.lean`) at the entry `i = 0`: given the source pointer
  (`frame+16+start`), destination pointer (`memBase+destOffset`), and byte count
  `size ≥ 1` set up in registers, it copies `srcBytes` (the in-bounds
  return-data slice) into the EVM-memory window `[destOffset, destOffset+size)`.

  Scope / glue: the RETURNDATACOPY-specific stack loads and OOB invalid routing
  are covered by the guard specs imported here. The size-0 skip and gas/MSIZE
  bookkeeping remain in handler glue, matching the CALLDATACOPY/CODECOPY proof
  boundary.
-/

import EvmAsm.Evm64.ReturnData.CopyLoopSpec
import EvmAsm.Evm64.ReturnData.RevertSpec

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace ReturnData

open EvmAsm.Rv64
open EvmAsm.Evm64.Mcopy (mcopyFwdContent mcopyFwdContent_zero mcopyFwdContent_full)

/-- `pcFree` extended to close `bytesRegion _.pcFree` leaves. -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj
    | pcFree)

/-- Shed the two running pointer registers `x17 x18` to ownership. -/
private theorem rdc_shed2 (F : Assertion) (v17 v18 : Word) :
    ∀ ps, (F ** (((.x17 : Reg) ↦ᵣ v17) ** ((.x18 : Reg) ↦ᵣ v18))) ps →
          (F ** (regOwn .x17 ** regOwn .x18)) ps := by
  apply sepConj_mono_right
  apply sepConj_mono (regIs_implies_regOwn _)
  exact regIs_implies_regOwn _

/-- **RETURNDATACOPY copy core `.proven` witness.** Copies `size = srcBytes.length`
    in-bounds return-data bytes from the frame source region into the EVM-memory
    window `[destOffset, destOffset+size)`.  `size ≥ 1` (size = 0 is the handler's
    glue `beqz` skip). -/
theorem evm_returndatacopy_stack_spec_within
    (base memBase srcBase : Word) (destOff : Nat)
    (srcBytes memBytes : List (BitVec 8)) (scratchV : Word)
    (h_pos : 1 ≤ srcBytes.length)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_mem_align : memBase.toNat % 8 = 0)
    (h_win : destOff + srcBytes.length ≤ memBytes.length)
    (h_src_over : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_mem_over : memBase.toNat + memBytes.length < 2 ^ 64)
    (h_mem_valid : ∀ k, k < memBytes.length →
      isValidByteAccess (memBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (6 * srcBytes.length) (base + 0) (base + 24)
      (evm_returndatacopy_loop_code .x18 .x17 .x16 .x19 base)
      (((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 srcBytes.length) **
       ((.x17 : Reg) ↦ᵣ srcBase) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 destOff)) **
       ((.x19 : Reg) ↦ᵣ scratchV) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase memBytes ** bytesRegion srcBase srcBytes)
      (((.x16 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x17 ** regOwn .x18 ** regOwn .x19 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase
         (memBytes.take destOff ++ srcBytes ++ memBytes.drop (destOff + srcBytes.length)) **
       bytesRegion srcBase srcBytes) := by
  obtain ⟨n, hn⟩ : ∃ n, srcBytes.length = n + 1 := ⟨srcBytes.length - 1, by omega⟩
  have hloop := evm_returndatacopy_loop_spec_within base memBase srcBase destOff n 0
    srcBytes memBytes scratchV (by omega) h_src_align h_mem_align h_win h_src_over
    h_src_valid h_mem_over h_mem_valid
  rw [mcopyFwdContent_zero memBytes srcBytes destOff (by omega),
      mcopyFwdContent_full memBytes srcBytes destOff, ← hn,
      show srcBase + BitVec.ofNat 64 0 = srcBase from by bv_omega, Nat.add_zero] at hloop
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun sState hq => by
      have k1 : ((((.x16 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          bytesRegion memBase
            (memBytes.take destOff ++ srcBytes ++ memBytes.drop (destOff + srcBytes.length)) **
          bytesRegion srcBase srcBytes ** regOwn .x19) **
          (((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcBytes.length)) **
           ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + srcBytes.length))))) sState := by
        xperm_chunked hq
      have k2 := rdc_shed2 _ _ _ sState k1
      xperm_chunked k2) hloop)

end ReturnData
end EvmAsm.Evm64
