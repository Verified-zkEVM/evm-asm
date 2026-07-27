/-
  EvmAsm.Evm64.ReturnData.RevertSpec

  Verified prefix for the RETURNDATACOPY handler's returndata bounds guard.
  This covers the stack-low-limb loads, symbolic `la evm_precompile_frame`,
  returndata length load, `start + size` computation, and the two
  `.exit_invalid` checks (`start + size` wrap, `start + size > retlen`) that
  precede gas/MSIZE and the byte-copy loop in the emitted handler. (The old
  256-byte frame-cap check was dropped in #10160 once the guest staged the full
  child return data.)
-/

import EvmAsm.Evm64.ReturnData.RevertProgram
import EvmAsm.Evm64.ReturnData.SizeProgram
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace ReturnData

open EvmAsm.Rv64

/-- `returnDataSizeOff` as a sign-extended LD immediate. -/
private theorem signExtend12_returnDataSizeOff_guard :
    signExtend12 (BitVec.ofNat 12 returnDataSizeOff) =
      BitVec.ofNat 64 returnDataSizeOff := by
  rw [signExtend12_ofNat_small (by decide)]

/-- The fall-through path of the RETURNDATACOPY returndata guard. It loads the
    three low stack limbs, materializes the frame pointer, loads the returndata
    length, computes `start + size`, and proves all three `bltu` guards fall
    through. -/
theorem evm_returndatacopy_guard_success_spec_within
    (frameHi : BitVec 20) (frameLo : BitVec 12)
    (off1 off2 : BitVec 13)
    (sp base frameAddr x14Old x15Old x16Old x17Old x18Old x19Old : Word)
    (destOffset dataOffset size returnDataLen : Word)
    (hla : base + 12 + ((frameHi.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 frameLo = frameAddr)
    (h_nowrap : ¬ BitVec.ult (dataOffset + size) dataOffset)
    (h_in_bounds : ¬ BitVec.ult returnDataLen (dataOffset + size)) :
    let code := evm_returndatacopy_revert_code frameHi frameLo off1 off2 base
    cpsTripleWithin 9 base (base + 36) code
      ((.x12 ↦ᵣ sp) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ x15Old) **
       (.x16 ↦ᵣ x16Old) ** (.x17 ↦ᵣ x17Old) ** (.x18 ↦ᵣ x18Old) **
       (.x19 ↦ᵣ x19Old) **
       (sp ↦ₘ destOffset) ** ((sp + 32) ↦ₘ dataOffset) **
       ((sp + 64) ↦ₘ size) **
       ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen))
      ((.x12 ↦ᵣ sp) ** (.x14 ↦ᵣ destOffset) ** (.x15 ↦ᵣ dataOffset) **
       (.x16 ↦ᵣ size) ** (.x17 ↦ᵣ frameAddr) ** (.x18 ↦ᵣ returnDataLen) **
       (.x19 ↦ᵣ (dataOffset + size)) **
       (sp ↦ₘ destOffset) ** ((sp + 32) ↦ₘ dataOffset) **
       ((sp + 64) ↦ₘ size) **
       ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen)) := by
  intro code
  have hld_dest := ld_spec_gen_within .x14 .x12 sp x14Old destOffset
    (0 : BitVec 12) base (by decide)
  simp only [signExtend12_0] at hld_dest
  have hld_start := ld_spec_gen_within .x15 .x12 sp x15Old dataOffset
    (32 : BitVec 12) (base + 4) (by decide)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) by decide] at hld_start
  have hld_size := ld_spec_gen_within .x16 .x12 sp x16Old size
    (64 : BitVec 12) (base + 8) (by decide)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) by decide] at hld_size
  let laTmp : Word :=
    (base + 12) + ((frameHi.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
  have hauipc := auipc_spec_gen_within .x17 x17Old frameHi (base + 12) (by decide)
  change cpsTripleWithin 1 (base + 12) ((base + 12) + 4)
      (CodeReq.singleton (base + 12) (.AUIPC .x17 frameHi))
      (.x17 ↦ᵣ x17Old) (.x17 ↦ᵣ laTmp) at hauipc
  have haddi := addi_spec_gen_same_within .x17 laTmp frameLo (base + 16) (by decide)
  rw [show laTmp + signExtend12 frameLo = frameAddr from by
      dsimp [laTmp]
      exact hla] at haddi
  have hld_len := ld_spec_gen_within .x18 .x17 frameAddr x18Old returnDataLen
    (BitVec.ofNat 12 returnDataSizeOff) (base + 20) (by decide)
  simp only [signExtend12_returnDataSizeOff_guard] at hld_len
  have hadd_end := add_spec_gen_within .x19 .x15 .x16 dataOffset size x19Old
    (base + 24) (by decide)
  have hbltu_wrap_raw := bltu_spec_gen_within .x19 .x15 off1
    (dataOffset + size) dataOffset (base + 28)
  rw [show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at hbltu_wrap_raw
  have hbltu_wrap := cpsBranchWithin_ntakenStripPure2 hbltu_wrap_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact h_nowrap ((sepConj_pure_right _).mp hQ).2)
  have hbltu_len_raw := bltu_spec_gen_within .x18 .x19 off2
    returnDataLen (dataOffset + size) (base + 32)
  rw [show (base + 32 : Word) + 4 = base + 36 from by bv_omega] at hbltu_len_raw
  have hbltu_len := cpsBranchWithin_ntakenStripPure2 hbltu_len_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact h_in_bounds ((sepConj_pure_right _).mp hQ).2)
  subst code
  unfold evm_returndatacopy_revert_code evm_returndatacopy_revert
  change cpsTripleWithin 9 base (base + 36)
    (CodeReq.ofProg base
      [.LD .x14 .x12 0,
       .LD .x15 .x12 (BitVec.ofNat 12 32),
       .LD .x16 .x12 (BitVec.ofNat 12 64),
       .AUIPC .x17 frameHi,
       .ADDI .x17 .x17 frameLo,
       .LD .x18 .x17 (BitVec.ofNat 12 returnDataSizeOff),
       .ADD .x19 .x15 .x16,
       .BLTU .x19 .x15 off1,
       .BLTU .x18 .x19 off2])
    _ _
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  rw [show (base + 4 : Word) + 4 = base + 8 by bv_omega]
  rw [show (base + 8 : Word) + 4 = base + 12 by bv_omega]
  rw [show (base + 12 : Word) + 4 = base + 16 by bv_omega]
  rw [show (base + 16 : Word) + 4 = base + 20 by bv_omega]
  rw [show (base + 20 : Word) + 4 = base + 24 by bv_omega]
  rw [show (base + 24 : Word) + 4 = base + 28 by bv_omega]
  rw [show (base + 28 : Word) + 4 = base + 32 by bv_omega]
  runBlock hld_dest hld_start hld_size hauipc haddi hld_len hadd_end
    hbltu_wrap hbltu_len

/-- First failure path of the RETURNDATACOPY returndata guard:
    `start + size` wraps below `start`, so the first `bltu` routes to
    `.exit_invalid`. -/
theorem evm_returndatacopy_guard_wrap_invalid_spec_within
    (frameHi : BitVec 20) (frameLo : BitVec 12)
    (off1 off2 : BitVec 13)
    (sp base frameAddr x14Old x15Old x16Old x17Old x18Old x19Old : Word)
    (destOffset dataOffset size returnDataLen : Word)
    (hla : base + 12 + ((frameHi.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 frameLo = frameAddr)
    (h_wrap : BitVec.ult (dataOffset + size) dataOffset) :
    let code := evm_returndatacopy_revert_code frameHi frameLo off1 off2 base
    cpsTripleWithin 8 base (base + 28 + signExtend13 off1) code
      ((.x12 ↦ᵣ sp) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ x15Old) **
       (.x16 ↦ᵣ x16Old) ** (.x17 ↦ᵣ x17Old) ** (.x18 ↦ᵣ x18Old) **
       (.x19 ↦ᵣ x19Old) **
       (sp ↦ₘ destOffset) ** ((sp + 32) ↦ₘ dataOffset) **
       ((sp + 64) ↦ₘ size) **
       ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen))
      ((.x12 ↦ᵣ sp) ** (.x14 ↦ᵣ destOffset) ** (.x15 ↦ᵣ dataOffset) **
       (.x16 ↦ᵣ size) ** (.x17 ↦ᵣ frameAddr) ** (.x18 ↦ᵣ returnDataLen) **
       (.x19 ↦ᵣ (dataOffset + size)) **
       (sp ↦ₘ destOffset) ** ((sp + 32) ↦ₘ dataOffset) **
       ((sp + 64) ↦ₘ size) **
       ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen)) := by
  intro code
  have hld_dest := ld_spec_gen_within .x14 .x12 sp x14Old destOffset
    (0 : BitVec 12) base (by decide)
  simp only [signExtend12_0] at hld_dest
  have hld_start := ld_spec_gen_within .x15 .x12 sp x15Old dataOffset
    (32 : BitVec 12) (base + 4) (by decide)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) by decide] at hld_start
  have hld_size := ld_spec_gen_within .x16 .x12 sp x16Old size
    (64 : BitVec 12) (base + 8) (by decide)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) by decide] at hld_size
  let laTmp : Word :=
    (base + 12) + ((frameHi.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
  have hauipc := auipc_spec_gen_within .x17 x17Old frameHi (base + 12) (by decide)
  change cpsTripleWithin 1 (base + 12) ((base + 12) + 4)
      (CodeReq.singleton (base + 12) (.AUIPC .x17 frameHi))
      (.x17 ↦ᵣ x17Old) (.x17 ↦ᵣ laTmp) at hauipc
  have haddi := addi_spec_gen_same_within .x17 laTmp frameLo (base + 16) (by decide)
  rw [show laTmp + signExtend12 frameLo = frameAddr from by
      dsimp [laTmp]
      exact hla] at haddi
  have hld_len := ld_spec_gen_within .x18 .x17 frameAddr x18Old returnDataLen
    (BitVec.ofNat 12 returnDataSizeOff) (base + 20) (by decide)
  simp only [signExtend12_returnDataSizeOff_guard] at hld_len
  have hadd_end := add_spec_gen_within .x19 .x15 .x16 dataOffset size x19Old
    (base + 24) (by decide)
  have hbltu_wrap_raw := bltu_spec_gen_within .x19 .x15 off1
    (dataOffset + size) dataOffset (base + 28)
  have hbltu_wrap := cpsBranchWithin_takenStripPure2 hbltu_wrap_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ((sepConj_pure_right _).mp hQ).2 h_wrap)
  subst code
  unfold evm_returndatacopy_revert_code evm_returndatacopy_revert
  change cpsTripleWithin 8 base (base + 28 + signExtend13 off1)
    (CodeReq.ofProg base
      [.LD .x14 .x12 0,
       .LD .x15 .x12 (BitVec.ofNat 12 32),
       .LD .x16 .x12 (BitVec.ofNat 12 64),
       .AUIPC .x17 frameHi,
       .ADDI .x17 .x17 frameLo,
       .LD .x18 .x17 (BitVec.ofNat 12 returnDataSizeOff),
       .ADD .x19 .x15 .x16,
       .BLTU .x19 .x15 off1,
       .BLTU .x18 .x19 off2])
    _ _
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  rw [show (base + 4 : Word) + 4 = base + 8 by bv_omega]
  rw [show (base + 8 : Word) + 4 = base + 12 by bv_omega]
  rw [show (base + 12 : Word) + 4 = base + 16 by bv_omega]
  rw [show (base + 16 : Word) + 4 = base + 20 by bv_omega]
  rw [show (base + 20 : Word) + 4 = base + 24 by bv_omega]
  rw [show (base + 24 : Word) + 4 = base + 28 by bv_omega]
  runBlock hld_dest hld_start hld_size hauipc haddi hld_len hadd_end hbltu_wrap

/-- Second failure path of the RETURNDATACOPY returndata guard:
    `start + size` does not wrap, but exceeds the stored returndata length. -/
theorem evm_returndatacopy_guard_len_invalid_spec_within
    (frameHi : BitVec 20) (frameLo : BitVec 12)
    (off1 off2 : BitVec 13)
    (sp base frameAddr x14Old x15Old x16Old x17Old x18Old x19Old : Word)
    (destOffset dataOffset size returnDataLen : Word)
    (hla : base + 12 + ((frameHi.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 frameLo = frameAddr)
    (h_nowrap : ¬ BitVec.ult (dataOffset + size) dataOffset)
    (h_oob : BitVec.ult returnDataLen (dataOffset + size)) :
    let code := evm_returndatacopy_revert_code frameHi frameLo off1 off2 base
    cpsTripleWithin 9 base (base + 32 + signExtend13 off2) code
      ((.x12 ↦ᵣ sp) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ x15Old) **
       (.x16 ↦ᵣ x16Old) ** (.x17 ↦ᵣ x17Old) ** (.x18 ↦ᵣ x18Old) **
       (.x19 ↦ᵣ x19Old) **
       (sp ↦ₘ destOffset) ** ((sp + 32) ↦ₘ dataOffset) **
       ((sp + 64) ↦ₘ size) **
       ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen))
      ((.x12 ↦ᵣ sp) ** (.x14 ↦ᵣ destOffset) ** (.x15 ↦ᵣ dataOffset) **
       (.x16 ↦ᵣ size) ** (.x17 ↦ᵣ frameAddr) ** (.x18 ↦ᵣ returnDataLen) **
       (.x19 ↦ᵣ (dataOffset + size)) **
       (sp ↦ₘ destOffset) ** ((sp + 32) ↦ₘ dataOffset) **
       ((sp + 64) ↦ₘ size) **
       ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen)) := by
  intro code
  have hld_dest := ld_spec_gen_within .x14 .x12 sp x14Old destOffset
    (0 : BitVec 12) base (by decide)
  simp only [signExtend12_0] at hld_dest
  have hld_start := ld_spec_gen_within .x15 .x12 sp x15Old dataOffset
    (32 : BitVec 12) (base + 4) (by decide)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) by decide] at hld_start
  have hld_size := ld_spec_gen_within .x16 .x12 sp x16Old size
    (64 : BitVec 12) (base + 8) (by decide)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) by decide] at hld_size
  let laTmp : Word :=
    (base + 12) + ((frameHi.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
  have hauipc := auipc_spec_gen_within .x17 x17Old frameHi (base + 12) (by decide)
  change cpsTripleWithin 1 (base + 12) ((base + 12) + 4)
      (CodeReq.singleton (base + 12) (.AUIPC .x17 frameHi))
      (.x17 ↦ᵣ x17Old) (.x17 ↦ᵣ laTmp) at hauipc
  have haddi := addi_spec_gen_same_within .x17 laTmp frameLo (base + 16) (by decide)
  rw [show laTmp + signExtend12 frameLo = frameAddr from by
      dsimp [laTmp]
      exact hla] at haddi
  have hld_len := ld_spec_gen_within .x18 .x17 frameAddr x18Old returnDataLen
    (BitVec.ofNat 12 returnDataSizeOff) (base + 20) (by decide)
  simp only [signExtend12_returnDataSizeOff_guard] at hld_len
  have hadd_end := add_spec_gen_within .x19 .x15 .x16 dataOffset size x19Old
    (base + 24) (by decide)
  have hbltu_wrap_raw := bltu_spec_gen_within .x19 .x15 off1
    (dataOffset + size) dataOffset (base + 28)
  rw [show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at hbltu_wrap_raw
  have hbltu_wrap := cpsBranchWithin_ntakenStripPure2 hbltu_wrap_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact h_nowrap ((sepConj_pure_right _).mp hQ).2)
  have hbltu_len_raw := bltu_spec_gen_within .x18 .x19 off2
    returnDataLen (dataOffset + size) (base + 32)
  have hbltu_len := cpsBranchWithin_takenStripPure2 hbltu_len_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ((sepConj_pure_right _).mp hQ).2 h_oob)
  subst code
  unfold evm_returndatacopy_revert_code evm_returndatacopy_revert
  change cpsTripleWithin 9 base (base + 32 + signExtend13 off2)
    (CodeReq.ofProg base
      [.LD .x14 .x12 0,
       .LD .x15 .x12 (BitVec.ofNat 12 32),
       .LD .x16 .x12 (BitVec.ofNat 12 64),
       .AUIPC .x17 frameHi,
       .ADDI .x17 .x17 frameLo,
       .LD .x18 .x17 (BitVec.ofNat 12 returnDataSizeOff),
       .ADD .x19 .x15 .x16,
       .BLTU .x19 .x15 off1,
       .BLTU .x18 .x19 off2])
    _ _
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  rw [show (base + 4 : Word) + 4 = base + 8 by bv_omega]
  rw [show (base + 8 : Word) + 4 = base + 12 by bv_omega]
  rw [show (base + 12 : Word) + 4 = base + 16 by bv_omega]
  rw [show (base + 16 : Word) + 4 = base + 20 by bv_omega]
  rw [show (base + 20 : Word) + 4 = base + 24 by bv_omega]
  rw [show (base + 24 : Word) + 4 = base + 28 by bv_omega]
  rw [show (base + 28 : Word) + 4 = base + 32 by bv_omega]
  runBlock hld_dest hld_start hld_size hauipc haddi hld_len hadd_end
    hbltu_wrap hbltu_len

/-- Stack-form lift of the RETURNDATACOPY guard success path. The stack is not
    popped by this prefix; it only exposes the low limbs that later gas/MSIZE
    glue and the copy loop consume. -/
theorem evm_returndatacopy_guard_success_stack_spec_within
    (frameHi : BitVec 20) (frameLo : BitVec 12)
    (off1 off2 : BitVec 13)
    (sp base frameAddr x14Old x15Old x16Old x17Old x18Old x19Old : Word)
    (destOffset dataOffset size : EvmWord) (returnDataLen : Word)
    (rest : List EvmWord)
    (hla : base + 12 + ((frameHi.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 frameLo = frameAddr)
    (h_nowrap : ¬ BitVec.ult (dataOffset.getLimbN 0 + size.getLimbN 0)
      (dataOffset.getLimbN 0))
    (h_in_bounds : ¬ BitVec.ult returnDataLen
      (dataOffset.getLimbN 0 + size.getLimbN 0)) :
    let code := evm_returndatacopy_revert_code frameHi frameLo off1 off2 base
    cpsTripleWithin 9 base (base + 36) code
      ((.x12 ↦ᵣ sp) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ x15Old) **
       (.x16 ↦ᵣ x16Old) ** (.x17 ↦ᵣ x17Old) ** (.x18 ↦ᵣ x18Old) **
       (.x19 ↦ᵣ x19Old) **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest **
       ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen))
      ((.x12 ↦ᵣ sp) ** (.x14 ↦ᵣ destOffset.getLimbN 0) **
       (.x15 ↦ᵣ dataOffset.getLimbN 0) ** (.x16 ↦ᵣ size.getLimbN 0) **
       (.x17 ↦ᵣ frameAddr) ** (.x18 ↦ᵣ returnDataLen) **
       (.x19 ↦ᵣ (dataOffset.getLimbN 0 + size.getLimbN 0)) **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest **
       ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen)) := by
  intro code
  let frame : Assertion :=
    ((sp + 8) ↦ₘ destOffset.getLimbN 1) **
    ((sp + 16) ↦ₘ destOffset.getLimbN 2) **
    ((sp + 24) ↦ₘ destOffset.getLimbN 3) **
    (((sp + 32) + 8) ↦ₘ dataOffset.getLimbN 1) **
    (((sp + 32) + 16) ↦ₘ dataOffset.getLimbN 2) **
    (((sp + 32) + 24) ↦ₘ dataOffset.getLimbN 3) **
    (((sp + 64) + 8) ↦ₘ size.getLimbN 1) **
    (((sp + 64) + 16) ↦ₘ size.getLimbN 2) **
    (((sp + 64) + 24) ↦ₘ size.getLimbN 3) **
    evmStackIs (sp + 96) rest
  have hRaw := evm_returndatacopy_guard_success_spec_within
    frameHi frameLo off1 off2 sp base frameAddr x14Old x15Old x16Old
    x17Old x18Old x19Old (destOffset.getLimbN 0) (dataOffset.getLimbN 0)
    (size.getLimbN 0) returnDataLen hla h_nowrap h_in_bounds
  have hFramePC : frame.pcFree := by
    dsimp [frame]
    pcFree
  have hFramed := cpsTripleWithin_frameR frame hFramePC hRaw
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [evmStackIs_triple_flat] at hp
      dsimp [frame, evmWordIs] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      rw [evmStackIs_triple_flat]
      dsimp [frame, evmWordIs] at hp ⊢
      xperm_hyp hp)
    hFramed

/-- Stack-form lift of the `start + size` wrap invalid guard path. -/
theorem evm_returndatacopy_guard_wrap_invalid_stack_spec_within
    (frameHi : BitVec 20) (frameLo : BitVec 12)
    (off1 off2 : BitVec 13)
    (sp base frameAddr x14Old x15Old x16Old x17Old x18Old x19Old : Word)
    (destOffset dataOffset size : EvmWord) (returnDataLen : Word)
    (rest : List EvmWord)
    (hla : base + 12 + ((frameHi.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 frameLo = frameAddr)
    (h_wrap : BitVec.ult (dataOffset.getLimbN 0 + size.getLimbN 0)
      (dataOffset.getLimbN 0)) :
    let code := evm_returndatacopy_revert_code frameHi frameLo off1 off2 base
    cpsTripleWithin 8 base (base + 28 + signExtend13 off1) code
      ((.x12 ↦ᵣ sp) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ x15Old) **
       (.x16 ↦ᵣ x16Old) ** (.x17 ↦ᵣ x17Old) ** (.x18 ↦ᵣ x18Old) **
       (.x19 ↦ᵣ x19Old) **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest **
       ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen))
      ((.x12 ↦ᵣ sp) ** (.x14 ↦ᵣ destOffset.getLimbN 0) **
       (.x15 ↦ᵣ dataOffset.getLimbN 0) ** (.x16 ↦ᵣ size.getLimbN 0) **
       (.x17 ↦ᵣ frameAddr) ** (.x18 ↦ᵣ returnDataLen) **
       (.x19 ↦ᵣ (dataOffset.getLimbN 0 + size.getLimbN 0)) **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest **
       ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen)) := by
  intro code
  let frame : Assertion :=
    ((sp + 8) ↦ₘ destOffset.getLimbN 1) **
    ((sp + 16) ↦ₘ destOffset.getLimbN 2) **
    ((sp + 24) ↦ₘ destOffset.getLimbN 3) **
    (((sp + 32) + 8) ↦ₘ dataOffset.getLimbN 1) **
    (((sp + 32) + 16) ↦ₘ dataOffset.getLimbN 2) **
    (((sp + 32) + 24) ↦ₘ dataOffset.getLimbN 3) **
    (((sp + 64) + 8) ↦ₘ size.getLimbN 1) **
    (((sp + 64) + 16) ↦ₘ size.getLimbN 2) **
    (((sp + 64) + 24) ↦ₘ size.getLimbN 3) **
    evmStackIs (sp + 96) rest
  have hRaw := evm_returndatacopy_guard_wrap_invalid_spec_within
    frameHi frameLo off1 off2 sp base frameAddr x14Old x15Old x16Old
    x17Old x18Old x19Old (destOffset.getLimbN 0) (dataOffset.getLimbN 0)
    (size.getLimbN 0) returnDataLen hla h_wrap
  have hFramePC : frame.pcFree := by
    dsimp [frame]
    pcFree
  have hFramed := cpsTripleWithin_frameR frame hFramePC hRaw
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [evmStackIs_triple_flat] at hp
      dsimp [frame, evmWordIs] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      rw [evmStackIs_triple_flat]
      dsimp [frame, evmWordIs] at hp ⊢
      xperm_hyp hp)
    hFramed

/-- Stack-form lift of the returndata-length invalid guard path. -/
theorem evm_returndatacopy_guard_len_invalid_stack_spec_within
    (frameHi : BitVec 20) (frameLo : BitVec 12)
    (off1 off2 : BitVec 13)
    (sp base frameAddr x14Old x15Old x16Old x17Old x18Old x19Old : Word)
    (destOffset dataOffset size : EvmWord) (returnDataLen : Word)
    (rest : List EvmWord)
    (hla : base + 12 + ((frameHi.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 frameLo = frameAddr)
    (h_nowrap : ¬ BitVec.ult (dataOffset.getLimbN 0 + size.getLimbN 0)
      (dataOffset.getLimbN 0))
    (h_oob : BitVec.ult returnDataLen
      (dataOffset.getLimbN 0 + size.getLimbN 0)) :
    let code := evm_returndatacopy_revert_code frameHi frameLo off1 off2 base
    cpsTripleWithin 9 base (base + 32 + signExtend13 off2) code
      ((.x12 ↦ᵣ sp) ** (.x14 ↦ᵣ x14Old) ** (.x15 ↦ᵣ x15Old) **
       (.x16 ↦ᵣ x16Old) ** (.x17 ↦ᵣ x17Old) ** (.x18 ↦ᵣ x18Old) **
       (.x19 ↦ᵣ x19Old) **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest **
       ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen))
      ((.x12 ↦ᵣ sp) ** (.x14 ↦ᵣ destOffset.getLimbN 0) **
       (.x15 ↦ᵣ dataOffset.getLimbN 0) ** (.x16 ↦ᵣ size.getLimbN 0) **
       (.x17 ↦ᵣ frameAddr) ** (.x18 ↦ᵣ returnDataLen) **
       (.x19 ↦ᵣ (dataOffset.getLimbN 0 + size.getLimbN 0)) **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest **
       ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ returnDataLen)) := by
  intro code
  let frame : Assertion :=
    ((sp + 8) ↦ₘ destOffset.getLimbN 1) **
    ((sp + 16) ↦ₘ destOffset.getLimbN 2) **
    ((sp + 24) ↦ₘ destOffset.getLimbN 3) **
    (((sp + 32) + 8) ↦ₘ dataOffset.getLimbN 1) **
    (((sp + 32) + 16) ↦ₘ dataOffset.getLimbN 2) **
    (((sp + 32) + 24) ↦ₘ dataOffset.getLimbN 3) **
    (((sp + 64) + 8) ↦ₘ size.getLimbN 1) **
    (((sp + 64) + 16) ↦ₘ size.getLimbN 2) **
    (((sp + 64) + 24) ↦ₘ size.getLimbN 3) **
    evmStackIs (sp + 96) rest
  have hRaw := evm_returndatacopy_guard_len_invalid_spec_within
    frameHi frameLo off1 off2 sp base frameAddr x14Old x15Old x16Old
    x17Old x18Old x19Old (destOffset.getLimbN 0) (dataOffset.getLimbN 0)
    (size.getLimbN 0) returnDataLen hla h_nowrap h_oob
  have hFramePC : frame.pcFree := by
    dsimp [frame]
    pcFree
  have hFramed := cpsTripleWithin_frameR frame hFramePC hRaw
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [evmStackIs_triple_flat] at hp
      dsimp [frame, evmWordIs] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      rw [evmStackIs_triple_flat]
      dsimp [frame, evmWordIs] at hp ⊢
      xperm_hyp hp)
    hFramed

end ReturnData
end EvmAsm.Evm64
