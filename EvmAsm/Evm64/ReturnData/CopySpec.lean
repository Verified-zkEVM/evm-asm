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

/-- Shed the three scratch registers `x17 x18 x19` to ownership. -/
private theorem rdc_shed3 (F : Assertion) (v17 v18 v19 : Word) :
    ∀ ps, (F ** (((.x17 : Reg) ↦ᵣ v17) ** ((.x18 : Reg) ↦ᵣ v18) **
                 ((.x19 : Reg) ↦ᵣ v19))) ps →
          (F ** (regOwn .x17 ** regOwn .x18 ** regOwn .x19)) ps := by
  apply sepConj_mono_right
  apply sepConj_mono (regIs_implies_regOwn _)
  apply sepConj_mono (regIs_implies_regOwn _)
  exact regIs_implies_regOwn _

/-- Shed the two running pointer registers `x17 x18` to ownership. -/
private theorem rdc_shed2 (F : Assertion) (v17 v18 : Word) :
    ∀ ps, (F ** (((.x17 : Reg) ↦ᵣ v17) ** ((.x18 : Reg) ↦ᵣ v18))) ps →
          (F ** (regOwn .x17 ** regOwn .x18)) ps := by
  apply sepConj_mono_right
  apply sepConj_mono (regIs_implies_regOwn _)
  exact regIs_implies_regOwn _

/-- Pointer setup between the bounds guards and the copy loop (`base → base+20`):
    pops the three stack operands, falls through the size-zero skip (`size ≠ 0`),
    and materializes the running source pointer `frame+16+start` and destination
    pointer `memBase+destOffset`. -/
theorem evm_returndatacopy_setup_spec_within
    (base sp memBase frameAddr destOffV startV sizeV x18Old : Word)
    (h_size_ne : sizeV ≠ (0 : Word)) :
    cpsTripleWithin 5 base (base + 20)
      (evm_returndatacopy_setup_code base)
      (((.x12 : Reg) ↦ᵣ sp) ** ((.x13 : Reg) ↦ᵣ memBase) **
       ((.x14 : Reg) ↦ᵣ destOffV) ** ((.x15 : Reg) ↦ᵣ startV) **
       ((.x16 : Reg) ↦ᵣ sizeV) ** ((.x17 : Reg) ↦ᵣ frameAddr) **
       ((.x18 : Reg) ↦ᵣ x18Old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (((.x12 : Reg) ↦ᵣ (sp + 96)) ** ((.x13 : Reg) ↦ᵣ memBase) **
       ((.x14 : Reg) ↦ᵣ destOffV) ** ((.x15 : Reg) ↦ᵣ startV) **
       ((.x16 : Reg) ↦ᵣ sizeV) ** ((.x17 : Reg) ↦ᵣ (frameAddr + 16 + startV)) **
       ((.x18 : Reg) ↦ᵣ (memBase + destOffV)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) := by
  -- [0] ADDI x12 x12 96 : pop the three operands.
  have h0 := addi_spec_gen_same_within .x12 sp (BitVec.ofNat 12 96) base (by decide)
  rw [show signExtend12 (BitVec.ofNat 12 96) = (96 : Word) from by decide] at h0
  -- [1] BEQ x16 x0 40 : size ≠ 0, so the size-zero skip is not taken.
  have h1raw := beq_spec_gen_within .x16 .x0 (BitVec.ofNat 13 40) sizeV (0 : Word) (base + 4)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at h1raw
  have h1 := cpsBranchWithin_ntakenStripPure2 h1raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact h_size_ne ((sepConj_pure_right _).mp hQ).2)
  -- [2] ADDI x17 x17 16 : x17 = frame + 16.
  have h2 := addi_spec_gen_same_within .x17 frameAddr (BitVec.ofNat 12 16) (base + 8) (by decide)
  rw [show signExtend12 (BitVec.ofNat 12 16) = (16 : Word) from by decide] at h2
  -- [3] ADD x17 x17 x15 : x17 = frame + 16 + start.
  have h3 := add_spec_gen_rd_eq_rs1_within .x17 .x15 (frameAddr + 16) startV
    (base + 12) (by decide)
  -- [4] ADD x18 x13 x14 : x18 = memBase + destOffset.
  have h4 := add_spec_gen_within .x18 .x13 .x14 memBase destOffV x18Old
    (base + 16) (by decide)
  unfold evm_returndatacopy_setup_code evm_returndatacopy_setup
  change cpsTripleWithin 5 base (base + 20)
    (CodeReq.ofProg base
      [.ADDI .x12 .x12 (BitVec.ofNat 12 96),
       .BEQ .x16 .x0 (BitVec.ofNat 13 40),
       .ADDI .x17 .x17 (BitVec.ofNat 12 16),
       .ADD .x17 .x17 .x15,
       .ADD .x18 .x13 .x14])
    _ _
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  rw [show (base + 4 : Word) + 4 = base + 8 by bv_omega]
  rw [show (base + 8 : Word) + 4 = base + 12 by bv_omega]
  rw [show (base + 12 : Word) + 4 = base + 16 by bv_omega]
  runBlock h0 h1 h2 h3 h4

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

/-- The size-zero path through the setup block (`base → base+44`): the operands
    are popped and the `beqz` skip is **taken**, jumping past the copy loop
    without touching memory. Two steps; mirrors CALLDATACOPY's top-tested loop
    exiting immediately at `size = 0`. -/
theorem evm_returndatacopy_setup_zero_spec_within
    (base sp sizeV x0v : Word) (h_size_zero : sizeV = (0 : Word))
    (h_x0 : x0v = (0 : Word)) :
    cpsTripleWithin 2 base (base + 44)
      (evm_returndatacopy_setup_code base)
      (((.x12 : Reg) ↦ᵣ sp) ** ((.x16 : Reg) ↦ᵣ sizeV) ** ((.x0 : Reg) ↦ᵣ x0v))
      (((.x12 : Reg) ↦ᵣ (sp + 96)) ** ((.x16 : Reg) ↦ᵣ sizeV) **
       ((.x0 : Reg) ↦ᵣ x0v)) := by
  subst h_x0
  -- [0] ADDI x12 x12 96 : pop the three operands.
  have h0 := addi_spec_gen_same_within .x12 sp (BitVec.ofNat 12 96) base (by decide)
  rw [show signExtend12 (BitVec.ofNat 12 96) = (96 : Word) from by decide] at h0
  -- [1] BEQ x16 x0 40 : size = 0, so the skip is taken to base+44.
  have h1raw := beq_spec_gen_within .x16 .x0 (BitVec.ofNat 13 40) sizeV (0 : Word) (base + 4)
  rw [show (base + 4 : Word) + signExtend13 (BitVec.ofNat 13 40) = base + 44 from by
        rw [show signExtend13 (BitVec.ofNat 13 40) = (40 : Word) from by decide]; bv_omega]
    at h1raw
  have h1 := cpsBranchWithin_takenStripPure2 h1raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ((sepConj_pure_right _).mp hQ).2 h_size_zero)
  unfold evm_returndatacopy_setup_code evm_returndatacopy_setup
  change cpsTripleWithin 2 base (base + 44)
    (CodeReq.ofProg base
      [.ADDI .x12 .x12 (BitVec.ofNat 12 96),
       .BEQ .x16 .x0 (BitVec.ofNat 13 40),
       .ADDI .x17 .x17 (BitVec.ofNat 12 16),
       .ADD .x17 .x17 .x15,
       .ADD .x18 .x13 .x14])
    _ _
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  runBlock h0 h1

/-! ## Composed body witness -/

/-- Lift a sub-program spec's `CodeReq` to the whole RETURNDATACOPY body. -/
private theorem rdc_mono_sub
    (frameHi : BitVec 20) (frameLo : BitVec 12) (off1 off2 : BitVec 13)
    (base subBase : Word) (pre mid suf : List Instr) (idx : Nat)
    (h_prog : evm_returndatacopy frameHi frameLo off1 off2 = pre ++ mid ++ suf)
    (h_pre_len : pre.length = idx)
    (h_addr : subBase = base + BitVec.ofNat 64 (4 * idx)) :
    ∀ a i, (CodeReq.ofProg subBase mid) a = some i →
           (evm_returndatacopy_code frameHi frameLo off1 off2 base) a = some i := by
  intro a i h
  have hbound : 4 * (pre ++ mid ++ suf).length < 2 ^ 64 := by
    rw [← h_prog, evm_returndatacopy_length]; norm_num
  have haddr' : base + BitVec.ofNat 64 (4 * pre.length) = subBase := by
    rw [h_pre_len, h_addr]
  have hsub := CodeReq.ofProg_mono_subrange base pre mid suf hbound a i
    (by rw [haddr']; exact h)
  unfold evm_returndatacopy_code
  rw [h_prog]
  exact hsub

/-- **RETURNDATACOPY body `.proven` witness.**  Stack-level triple over the whole
    verified body (`base → base+80`): the bounds guards fall through, the operands
    are popped, the pointers are set up, and the copy loop writes the in-bounds
    return-data slice `stagedBytes[start ..< start+size]` into the EVM-memory
    window `[destOffset, destOffset+size)`.

    Scope matches CALLDATACOPY's registered witness: the handler's interleaved
    dynamic-gas / OOG / MSIZE glue is framed out (DRIFT TCB boundary), and the
    high-limb operand checks the handler performs in that glue region appear here
    as the `h_destOff`/`h_srcOff`/`h_size` low-limb hypotheses.  The two invalid
    exits are the companion theorems
    `evm_returndatacopy_guard_{wrap,len}_invalid_stack_spec_within`. -/
theorem evm_returndatacopy_body_pos_stack_spec_within
    (frameHi : BitVec 20) (frameLo : BitVec 12) (off1 off2 : BitVec 13)
    (base sp memBase frameAddr returnDataLen : Word)
    (destOffset dataOffset size : EvmWord) (rest : List EvmWord)
    (destOff srcOff sz : Nat)
    (srcAll memBytes : List (BitVec 8))
    (x14Old x15Old x16Old x17Old x18Old x19Old : Word)
    (hla : base + 12 + ((frameHi.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 frameLo = frameAddr)
    (h_destOff : destOffset.getLimbN 0 = BitVec.ofNat 64 destOff)
    (h_srcOff : dataOffset.getLimbN 0 = BitVec.ofNat 64 srcOff)
    (h_sizeV : size.getLimbN 0 = BitVec.ofNat 64 sz)
    (h_nowrap : ¬ BitVec.ult (dataOffset.getLimbN 0 + size.getLimbN 0)
      (dataOffset.getLimbN 0))
    (h_in_bounds : ¬ BitVec.ult returnDataLen
      (dataOffset.getLimbN 0 + size.getLimbN 0))
    (h_pos : 1 ≤ sz)
    (h_fits : srcOff + sz ≤ srcAll.length)
    (h_src_align : (frameAddr + 16).toNat % 8 = 0)
    (h_mem_align : memBase.toNat % 8 = 0)
    (h_win : destOff + sz ≤ memBytes.length)
    (h_src_over : (frameAddr + 16).toNat + srcAll.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcAll.length →
      isValidByteAccess ((frameAddr + 16) + BitVec.ofNat 64 k) = true)
    (h_mem_over : memBase.toNat + memBytes.length < 2 ^ 64)
    (h_mem_valid : ∀ k, k < memBytes.length →
      isValidByteAccess (memBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (14 + 6 * sz) base (base + 80)
      (evm_returndatacopy_code frameHi frameLo off1 off2 base)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ sp) **
       ((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ x14Old) **
       ((.x15 : Reg) ↦ᵣ x15Old) ** ((.x16 : Reg) ↦ᵣ x16Old) **
       ((.x17 : Reg) ↦ᵣ x17Old) ** ((.x18 : Reg) ↦ᵣ x18Old) **
       ((.x19 : Reg) ↦ᵣ x19Old) **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest **
       ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen) **
       bytesRegion memBase memBytes ** bytesRegion (frameAddr + 16) srcAll)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ (sp + 96)) **
       ((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ (BitVec.ofNat 64 destOff)) **
       ((.x15 : Reg) ↦ᵣ (BitVec.ofNat 64 srcOff)) ** ((.x16 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x17 ** regOwn .x18 ** regOwn .x19 **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest **
       ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen) **
       bytesRegion memBase
         (memBytes.take destOff ++ (srcAll.drop srcOff).take sz ++
          memBytes.drop (destOff + sz)) **
       bytesRegion (frameAddr + 16) srcAll) := by
  -- Code-requirement lifts for the three segments of the body image.
  have hprog : evm_returndatacopy frameHi frameLo off1 off2
      = evm_returndatacopy_revert frameHi frameLo off1 off2 ++
        (evm_returndatacopy_setup ++ evm_returndatacopy_loop .x18 .x17 .x16 .x19) := rfl
  have mono_guard := rdc_mono_sub frameHi frameLo off1 off2 base base
    [] (evm_returndatacopy_revert frameHi frameLo off1 off2)
    (evm_returndatacopy_setup ++ evm_returndatacopy_loop .x18 .x17 .x16 .x19) 0
    rfl rfl (by bv_omega)
  have mono_setup := rdc_mono_sub frameHi frameLo off1 off2 base (base + 36)
    (evm_returndatacopy_revert frameHi frameLo off1 off2) evm_returndatacopy_setup
    (evm_returndatacopy_loop .x18 .x17 .x16 .x19) 9
    (List.append_assoc _ _ _).symm
    (evm_returndatacopy_revert_length ..)
    (by bv_omega)
  have mono_loop := rdc_mono_sub frameHi frameLo off1 off2 base (base + 56)
    (evm_returndatacopy_revert frameHi frameLo off1 off2 ++ evm_returndatacopy_setup)
    (evm_returndatacopy_loop .x18 .x17 .x16 .x19) [] 14
    (by rw [hprog, List.append_nil]; exact (List.append_assoc _ _ _).symm)
    (by simp [evm_returndatacopy_revert_length, evm_returndatacopy_setup_length])
    (by bv_omega)
  -- Size as a nonzero machine word.
  have hsz_lt : sz < 2 ^ 64 := by
    have : srcAll.length < 2 ^ 64 := by omega
    omega
  have hsz_ne : BitVec.ofNat 64 sz ≠ (0 : Word) := by
    intro hc
    have := congrArg BitVec.toNat hc
    rw [BitVec.toNat_ofNat] at this
    simp at this
    omega
  -- Segment 1: the bounds guards (base → base+36).
  have hguard := evm_returndatacopy_guard_success_stack_spec_within
    frameHi frameLo off1 off2 sp base frameAddr x14Old x15Old x16Old x17Old x18Old
    x19Old destOffset dataOffset size returnDataLen rest hla h_nowrap h_in_bounds
  have hguardc := cpsTripleWithin_extend_code mono_guard hguard
  -- Segment 2: pointer setup (base+36 → base+56).
  have hsetup := evm_returndatacopy_setup_spec_within (base + 36) sp memBase frameAddr
    (destOffset.getLimbN 0) (dataOffset.getLimbN 0) (size.getLimbN 0) returnDataLen
    (by rw [h_sizeV]; exact hsz_ne)
  rw [show (base + 36 : Word) + 20 = base + 56 from by bv_omega] at hsetup
  have hsetupc := cpsTripleWithin_extend_code mono_setup hsetup
  -- Segment 3: the copy loop (base+56 → base+80).
  have hloop := evm_returndatacopy_stack_spec_within (base + 56) memBase (frameAddr + 16)
    destOff srcOff sz srcAll memBytes
    (BitVec.ofNat 64 srcOff + BitVec.ofNat 64 sz) h_pos h_fits h_src_align h_mem_align
    h_win h_src_over h_src_valid h_mem_over h_mem_valid
  rw [show (base + 56 : Word) + 0 = base + 56 from by bv_omega,
      show (base + 56 : Word) + 24 = base + 80 from by bv_omega] at hloop
  have hloopc := cpsTripleWithin_extend_code mono_loop hloop
  -- Frame the resources each segment does not touch.
  have gf := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x13 : Reg) ↦ᵣ memBase) **
     bytesRegion memBase memBytes ** bytesRegion (frameAddr + 16) srcAll)
    (by pcFreeR) hguardc
  have sf := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ (BitVec.ofNat 64 srcOff + BitVec.ofNat 64 sz)) **
     evmStackIs sp [destOffset, dataOffset, size] ** evmStackIs (sp + 96) rest **
     ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen) **
     bytesRegion memBase memBytes ** bytesRegion (frameAddr + 16) srcAll)
    (by pcFreeR) hsetupc
  have lf := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ (sp + 96)) ** ((.x13 : Reg) ↦ᵣ memBase) **
     ((.x14 : Reg) ↦ᵣ (BitVec.ofNat 64 destOff)) **
     ((.x15 : Reg) ↦ᵣ (BitVec.ofNat 64 srcOff)) **
     evmStackIs sp [destOffset, dataOffset, size] ** evmStackIs (sp + 96) rest **
     ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen))
    (by pcFreeR) hloopc
  -- Value bridges: the guard/setup specs are stated over the stack limbs, the
  -- loop entry over the `Nat` offsets.
  rw [h_destOff, h_srcOff, h_sizeV] at gf sf
  simp only [sepConj_assoc'] at gf sf lf
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) gf sf
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 lf
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => by xperm_chunked hp) s2)

/-- **RETURNDATACOPY body `.proven` witness — all sizes.**  Same statement as
    `evm_returndatacopy_body_pos_stack_spec_within` but with **no `size ≥ 1`
    gate**: at `size = 0` the guards still fall through, the operands are still
    popped, and the `beqz` skip is taken straight to the exit leaving memory
    untouched — which is exactly what the postcondition degenerates to, since
    `memBytes.take destOff ++ [] ++ memBytes.drop destOff = memBytes`.

    Covering `size = 0` is what keeps this `.proven` rather than `.conditional`:
    there is no nonvacuous input-domain precondition left on the size, matching
    CALLDATACOPY, whose top-tested loop exits immediately at zero size. -/
theorem evm_returndatacopy_body_stack_spec_within
    (frameHi : BitVec 20) (frameLo : BitVec 12) (off1 off2 : BitVec 13)
    (base sp memBase frameAddr returnDataLen : Word)
    (destOffset dataOffset size : EvmWord) (rest : List EvmWord)
    (destOff srcOff sz : Nat)
    (srcAll memBytes : List (BitVec 8))
    (x14Old x15Old x16Old x17Old x18Old x19Old : Word)
    (hla : base + 12 + ((frameHi.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 frameLo = frameAddr)
    (h_destOff : destOffset.getLimbN 0 = BitVec.ofNat 64 destOff)
    (h_srcOff : dataOffset.getLimbN 0 = BitVec.ofNat 64 srcOff)
    (h_sizeV : size.getLimbN 0 = BitVec.ofNat 64 sz)
    (h_nowrap : ¬ BitVec.ult (dataOffset.getLimbN 0 + size.getLimbN 0)
      (dataOffset.getLimbN 0))
    (h_in_bounds : ¬ BitVec.ult returnDataLen
      (dataOffset.getLimbN 0 + size.getLimbN 0))
    (h_fits : srcOff + sz ≤ srcAll.length)
    (h_src_align : (frameAddr + 16).toNat % 8 = 0)
    (h_mem_align : memBase.toNat % 8 = 0)
    (h_win : destOff + sz ≤ memBytes.length)
    (h_src_over : (frameAddr + 16).toNat + srcAll.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcAll.length →
      isValidByteAccess ((frameAddr + 16) + BitVec.ofNat 64 k) = true)
    (h_mem_over : memBase.toNat + memBytes.length < 2 ^ 64)
    (h_mem_valid : ∀ k, k < memBytes.length →
      isValidByteAccess (memBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (14 + 6 * sz) base (base + 80)
      (evm_returndatacopy_code frameHi frameLo off1 off2 base)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ sp) **
       ((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ x14Old) **
       ((.x15 : Reg) ↦ᵣ x15Old) ** ((.x16 : Reg) ↦ᵣ x16Old) **
       ((.x17 : Reg) ↦ᵣ x17Old) ** ((.x18 : Reg) ↦ᵣ x18Old) **
       ((.x19 : Reg) ↦ᵣ x19Old) **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest **
       ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen) **
       bytesRegion memBase memBytes ** bytesRegion (frameAddr + 16) srcAll)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ (sp + 96)) **
       ((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ (BitVec.ofNat 64 destOff)) **
       ((.x15 : Reg) ↦ᵣ (BitVec.ofNat 64 srcOff)) ** ((.x16 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x17 ** regOwn .x18 ** regOwn .x19 **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest **
       ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen) **
       bytesRegion memBase
         (memBytes.take destOff ++ (srcAll.drop srcOff).take sz ++
          memBytes.drop (destOff + sz)) **
       bytesRegion (frameAddr + 16) srcAll) := by
  rcases Nat.eq_zero_or_pos sz with hz | hpos
  · -- `size = 0`: guards fall through, operands pop, the `beqz` skip is taken.
    subst hz
    have hmem : memBytes.take destOff ++ (srcAll.drop srcOff).take 0 ++
        memBytes.drop (destOff + 0) = memBytes := by
      simp [List.take_append_drop]
    rw [hmem]
    have hprog : evm_returndatacopy frameHi frameLo off1 off2
        = evm_returndatacopy_revert frameHi frameLo off1 off2 ++
          (evm_returndatacopy_setup ++ evm_returndatacopy_loop .x18 .x17 .x16 .x19) := rfl
    have mono_guard := rdc_mono_sub frameHi frameLo off1 off2 base base
      [] (evm_returndatacopy_revert frameHi frameLo off1 off2)
      (evm_returndatacopy_setup ++ evm_returndatacopy_loop .x18 .x17 .x16 .x19) 0
      rfl rfl (by bv_omega)
    have mono_setup := rdc_mono_sub frameHi frameLo off1 off2 base (base + 36)
      (evm_returndatacopy_revert frameHi frameLo off1 off2) evm_returndatacopy_setup
      (evm_returndatacopy_loop .x18 .x17 .x16 .x19) 9
      (List.append_assoc _ _ _).symm
      (evm_returndatacopy_revert_length ..)
      (by bv_omega)
    have hsz0 : size.getLimbN 0 = (0 : Word) := by
      rw [h_sizeV]; decide
    -- Segment 1: the bounds guards (base → base+36).
    have hguard := evm_returndatacopy_guard_success_stack_spec_within
      frameHi frameLo off1 off2 sp base frameAddr x14Old x15Old x16Old x17Old x18Old
      x19Old destOffset dataOffset size returnDataLen rest hla h_nowrap h_in_bounds
    have hguardc := cpsTripleWithin_extend_code mono_guard hguard
    -- Segment 2: pop + taken skip (base+36 → base+80).
    have hzeroSpec := evm_returndatacopy_setup_zero_spec_within (base + 36) sp
      (BitVec.ofNat 64 0) (0 : Word) (by decide) rfl
    rw [show (base + 36 : Word) + 44 = base + 80 from by bv_omega] at hzeroSpec
    have hzeroc := cpsTripleWithin_extend_code mono_setup hzeroSpec
    have gf := cpsTripleWithin_frameR
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x13 : Reg) ↦ᵣ memBase) **
       bytesRegion memBase memBytes ** bytesRegion (frameAddr + 16) srcAll)
      (by pcFreeR) hguardc
    have zf := cpsTripleWithin_frameR
      (((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ (BitVec.ofNat 64 destOff)) **
       ((.x15 : Reg) ↦ᵣ (BitVec.ofNat 64 srcOff)) ** ((.x17 : Reg) ↦ᵣ frameAddr) **
       ((.x18 : Reg) ↦ᵣ returnDataLen) **
       ((.x19 : Reg) ↦ᵣ (BitVec.ofNat 64 srcOff + BitVec.ofNat 64 0)) **
       evmStackIs sp [destOffset, dataOffset, size] ** evmStackIs (sp + 96) rest **
       ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen) **
       bytesRegion memBase memBytes ** bytesRegion (frameAddr + 16) srcAll)
      (by pcFreeR) hzeroc
    rw [h_destOff, h_srcOff, h_sizeV] at gf
    simp only [sepConj_assoc'] at gf zf
    have s := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) gf zf
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun sState hq => by
        have k1 : ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ (sp + 96)) **
            ((.x13 : Reg) ↦ᵣ memBase) ** ((.x14 : Reg) ↦ᵣ (BitVec.ofNat 64 destOff)) **
            ((.x15 : Reg) ↦ᵣ (BitVec.ofNat 64 srcOff)) **
            ((.x16 : Reg) ↦ᵣ (BitVec.ofNat 64 0)) **
            evmStackIs sp [destOffset, dataOffset, size] **
            evmStackIs (sp + 96) rest **
            ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen) **
            bytesRegion memBase memBytes ** bytesRegion (frameAddr + 16) srcAll) **
            (((.x17 : Reg) ↦ᵣ frameAddr) ** ((.x18 : Reg) ↦ᵣ returnDataLen) **
             ((.x19 : Reg) ↦ᵣ (BitVec.ofNat 64 srcOff + BitVec.ofNat 64 0)))) sState := by
          xperm_chunked hq
        have k2 := rdc_shed3 _ _ _ _ sState k1
        rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from by decide] at k2
        xperm_chunked k2) s)
  · exact evm_returndatacopy_body_pos_stack_spec_within frameHi frameLo off1 off2
      base sp memBase frameAddr returnDataLen destOffset dataOffset size rest
      destOff srcOff sz srcAll memBytes x14Old x15Old x16Old x17Old x18Old x19Old
      hla h_destOff h_srcOff h_sizeV h_nowrap h_in_bounds hpos h_fits h_src_align
      h_mem_align h_win h_src_over h_src_valid h_mem_over h_mem_valid

end ReturnData
end EvmAsm.Evm64
