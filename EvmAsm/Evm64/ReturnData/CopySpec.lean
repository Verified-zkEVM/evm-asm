/-
  EvmAsm.Evm64.ReturnData.CopySpec

  RETURNDATACOPY verification surface.

  `RevertSpec.lean` verifies the stack-form returndata bounds guard prefix:
  stack-low-limb loads, symbolic `la evm_precompile_frame`, return-data length
  load, the success fall-through, and both invalid exits (`start+size` wrap and
  `start+size > retlen`).

  This file keeps the byte-copy witness (`evm_returndatacopy_stack_spec_within`)
  for the bottom-tested copy loop (`CopyLoopSpec.lean`) at the entry `i = 0`:
  given the staged return-data region (anchored at the aligned frame data base
  `frame+16`), the read offset `srcOff` (the EVM `start` operand), the
  destination pointer (`memBase+destOffset`), and byte count `size ≥ 1` set up in
  registers, it copies the in-bounds slice `stagedBytes[srcOff ..< srcOff+size]`
  into the EVM-memory window `[destOffset, destOffset+size)`.

  The source offset is carried in the pointer register rather than folded into
  the region base, so it is independent of the destination offset and needs no
  `(frame+16+start) % 8 = 0` alignment side condition — see the `CopyLoopSpec`
  header.

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
open EvmAsm.Evm64.Mcopy (mcopyFwdContent mcopyFwdContent_zero)

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

/-- **RETURNDATACOPY copy core `.proven` witness.** Copies the `size` in-bounds
    return-data bytes `stagedBytes[srcOff ..< srcOff+size]` from the frame source
    region into the EVM-memory window `[destOffset, destOffset+size)`.
    `size ≥ 1` (size = 0 is the handler's glue `beqz` skip). -/
theorem evm_returndatacopy_stack_spec_within
    (base memBase srcBase : Word) (destOff srcOff size : Nat)
    (srcAll memBytes : List (BitVec 8)) (scratchV : Word)
    (h_pos : 1 ≤ size)
    (h_fits : srcOff + size ≤ srcAll.length)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_mem_align : memBase.toNat % 8 = 0)
    (h_win : destOff + size ≤ memBytes.length)
    (h_src_over : srcBase.toNat + srcAll.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcAll.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_mem_over : memBase.toNat + memBytes.length < 2 ^ 64)
    (h_mem_valid : ∀ k, k < memBytes.length →
      isValidByteAccess (memBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (6 * size) (base + 0) (base + 24)
      (evm_returndatacopy_loop_code .x18 .x17 .x16 .x19 base)
      (((.x16 : Reg) ↦ᵣ BitVec.ofNat 64 size) **
       ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
       ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 destOff)) **
       ((.x19 : Reg) ↦ᵣ scratchV) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase memBytes ** bytesRegion srcBase srcAll)
      (((.x16 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x17 ** regOwn .x18 ** regOwn .x19 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion memBase
         (memBytes.take destOff ++ (srcAll.drop srcOff).take size ++
          memBytes.drop (destOff + size)) **
       bytesRegion srcBase srcAll) := by
  obtain ⟨n, hn⟩ : ∃ n, size = n + 1 := ⟨size - 1, by omega⟩
  have hclen : ((srcAll.drop srcOff).take size).length = size :=
    rdc_slice_length srcAll srcOff size h_fits
  have hzero : mcopyFwdContent memBytes ((srcAll.drop srcOff).take size) destOff 0 = memBytes :=
    mcopyFwdContent_zero memBytes ((srcAll.drop srcOff).take size) destOff
      (by rw [hclen]; exact h_win)
  have hfull : mcopyFwdContent memBytes ((srcAll.drop srcOff).take size) destOff size
      = memBytes.take destOff ++ (srcAll.drop srcOff).take size ++
        memBytes.drop (destOff + size) := by
    unfold mcopyFwdContent
    rw [List.take_of_length_le (le_of_eq hclen)]
  have hloop := evm_returndatacopy_loop_spec_within base memBase srcBase destOff srcOff size n 0
    srcAll memBytes scratchV (by omega) h_fits h_src_align h_mem_align h_win h_src_over
    h_src_valid h_mem_over h_mem_valid
  rw [hzero, hfull, ← hn, Nat.add_zero, Nat.add_zero] at hloop
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun sState hq => by
      have k1 : ((((.x16 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          bytesRegion memBase
            (memBytes.take destOff ++ (srcAll.drop srcOff).take size ++
             memBytes.drop (destOff + size)) **
          bytesRegion srcBase srcAll ** regOwn .x19) **
          (((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + size))) **
           ((.x18 : Reg) ↦ᵣ (memBase + BitVec.ofNat 64 (destOff + size))))) sState := by
        xperm_chunked hq
      have k2 := rdc_shed2 _ _ _ sState k1
      xperm_chunked k2) hloop)

end ReturnData
end EvmAsm.Evm64
