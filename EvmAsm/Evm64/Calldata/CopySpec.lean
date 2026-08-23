/-
  EvmAsm.Evm64.Calldata.CopySpec

  Partial stack-level specification for the EVM `CALLDATACOPY` opcode
  (GH #104, bead `evm-asm-54bh8`).

  This slice proves the straight-line executable preamble of
  `evm_calldatacopy`: it pops the three stack arguments, exposes
  `env.callDataPtr` / `env.callDataLen`, and initializes the loop
  registers in the shape consumed by the pure `CopyMemory` byte-write
  helpers. The dynamic byte loop and full EVM-memory lift remain a
  follow-up.
-/

import EvmAsm.Evm64.Calldata.CopyProgram
import EvmAsm.Evm64.Calldata.CopyMemory
import EvmAsm.Evm64.Environment.Assertion
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace Calldata

open EvmAsm.Rv64
open EvmAsm.Evm64.EvmEnv
  (callDataPtrOff callDataLenOff envIs envIs_callDataPtrLen_split
   envIsCallDataPtrLenRest)

/-- The executable CALLDATACOPY preamble, separated from the loop so its
    stack effect can be proved independently. -/
def evm_calldatacopy_preamble
    (envBaseReg memBaseReg destReg srcReg cntReg cdpReg endReg : Reg) :
    Program :=
  LD destReg .x12 0 ;;
  LD srcReg .x12 32 ;;
  LD cntReg .x12 64 ;;
  ADDI .x12 .x12 (BitVec.ofNat 12 96) ;;
  LD cdpReg envBaseReg (BitVec.ofNat 12 callDataPtrOff) ;;
  LD endReg envBaseReg (BitVec.ofNat 12 callDataLenOff) ;;
  ADD endReg endReg cdpReg ;;
  ADD destReg memBaseReg destReg ;;
  ADD srcReg cdpReg srcReg

/-- `CodeReq` for the CALLDATACOPY preamble. -/
abbrev evm_calldatacopy_preamble_code
    (envBaseReg memBaseReg destReg srcReg cntReg cdpReg endReg : Reg)
    (base : Word) : CodeReq :=
  CodeReq.ofProg base
    (evm_calldatacopy_preamble envBaseReg memBaseReg destReg srcReg
      cntReg cdpReg endReg)

/-- The CALLDATACOPY preamble is exactly the first nine instructions. -/
theorem evm_calldatacopy_preamble_length
    (envBaseReg memBaseReg destReg srcReg cntReg cdpReg endReg : Reg) :
    (evm_calldatacopy_preamble envBaseReg memBaseReg destReg srcReg
      cntReg cdpReg endReg).length = 9 := by
  simp [evm_calldatacopy_preamble, LD, ADDI, ADD, single, seq]

theorem signExtend12_callDataPtrOff :
    signExtend12 (BitVec.ofNat 12 callDataPtrOff) =
      BitVec.ofNat 64 callDataPtrOff := by
  rw [signExtend12_ofNat_small (by decide)]

theorem signExtend12_callDataLenOff :
    signExtend12 (BitVec.ofNat 12 callDataLenOff) =
      BitVec.ofNat 64 callDataLenOff := by
  rw [signExtend12_ofNat_small (by decide)]

/-- Raw preamble spec: load the low limbs of the three stack arguments,
    pop three EVM words, load calldata base/length from the env block,
    then initialize absolute destination/source pointers and calldata end. -/
theorem evm_calldatacopy_preamble_spec_within
    (envBaseReg memBaseReg destReg srcReg cntReg cdpReg endReg : Reg)
    (hdest_ne_x0 : destReg ≠ .x0)
    (hsrc_ne_x0 : srcReg ≠ .x0)
    (hcnt_ne_x0 : cntReg ≠ .x0)
    (hcdp_ne_x0 : cdpReg ≠ .x0)
    (hend_ne_x0 : endReg ≠ .x0)
    (sp base envAddr memBase destOld srcOld cntOld cdpOld endOld : Word)
    (destOffset dataOffset size callDataPtr callDataLen : Word) :
    let code := evm_calldatacopy_preamble_code envBaseReg memBaseReg
      destReg srcReg cntReg cdpReg endReg base
    cpsTripleWithin 9 base (base + 36) code
      ((.x12 ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) **
       (memBaseReg ↦ᵣ memBase) ** (destReg ↦ᵣ destOld) **
       (srcReg ↦ᵣ srcOld) ** (cntReg ↦ᵣ cntOld) **
       (cdpReg ↦ᵣ cdpOld) ** (endReg ↦ᵣ endOld) **
       (sp ↦ₘ destOffset) ** ((sp + 32) ↦ₘ dataOffset) **
       ((sp + 64) ↦ₘ size) **
       ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ callDataPtr) **
       ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ callDataLen))
      ((.x12 ↦ᵣ (sp + 96)) ** (envBaseReg ↦ᵣ envAddr) **
       (memBaseReg ↦ᵣ memBase) ** (destReg ↦ᵣ (memBase + destOffset)) **
       (srcReg ↦ᵣ (callDataPtr + dataOffset)) ** (cntReg ↦ᵣ size) **
       (cdpReg ↦ᵣ callDataPtr) ** (endReg ↦ᵣ (callDataLen + callDataPtr)) **
       (sp ↦ₘ destOffset) ** ((sp + 32) ↦ₘ dataOffset) **
       ((sp + 64) ↦ₘ size) **
       ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ callDataPtr) **
       ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ callDataLen)) := by
  have hLoadDest := ld_spec_gen_within destReg .x12 sp destOld destOffset
    (0 : BitVec 12) base hdest_ne_x0
  have hLoadSrc := ld_spec_gen_within srcReg .x12 sp srcOld dataOffset
    (32 : BitVec 12) (base + 4) hsrc_ne_x0
  have hLoadCnt := ld_spec_gen_within cntReg .x12 sp cntOld size
    (64 : BitVec 12) (base + 8) hcnt_ne_x0
  have hPop := addi_spec_gen_same_within .x12 sp
    (BitVec.ofNat 12 96) (base + 12) (by nofun)
  have hLoadPtr := ld_spec_gen_within cdpReg envBaseReg envAddr cdpOld
    callDataPtr (BitVec.ofNat 12 callDataPtrOff) (base + 16) hcdp_ne_x0
  simp only [signExtend12_callDataPtrOff] at hLoadPtr
  have hLoadLen := ld_spec_gen_within endReg envBaseReg envAddr endOld
    callDataLen (BitVec.ofNat 12 callDataLenOff) (base + 20) hend_ne_x0
  simp only [signExtend12_callDataLenOff] at hLoadLen
  have hAddEnd := add_spec_gen_rd_eq_rs1_within endReg cdpReg
    callDataLen callDataPtr (base + 24) hend_ne_x0
  have hAddDest := add_spec_gen_rd_eq_rs2_within destReg memBaseReg
    memBase destOffset (base + 28) hdest_ne_x0
  have hAddSrc := add_spec_gen_rd_eq_rs2_within srcReg cdpReg
    callDataPtr dataOffset (base + 32) hsrc_ne_x0
  simp only [signExtend12_0] at hLoadDest
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) by decide] at hLoadSrc
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) by decide] at hLoadCnt
  rw [show sp + signExtend12 (BitVec.ofNat 12 96) = sp + 96 by
    rw [show signExtend12 (BitVec.ofNat 12 96) = (96 : Word) by decide]] at hPop
  unfold evm_calldatacopy_preamble_code evm_calldatacopy_preamble
  change cpsTripleWithin 9 base (base + 36)
    (CodeReq.ofProg base
      [.LD destReg .x12 0, .LD srcReg .x12 32, .LD cntReg .x12 64,
       .ADDI .x12 .x12 (BitVec.ofNat 12 96),
       .LD cdpReg envBaseReg (BitVec.ofNat 12 callDataPtrOff),
       .LD endReg envBaseReg (BitVec.ofNat 12 callDataLenOff),
       .ADD endReg endReg cdpReg, .ADD destReg memBaseReg destReg,
       .ADD srcReg cdpReg srcReg])
    _ _
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  rw [show (base + 4 : Word) + 4 = base + 8 by bv_addr]
  rw [show (base + 8 : Word) + 4 = base + 12 by bv_addr]
  rw [show (base + 12 : Word) + 4 = base + 16 by bv_addr]
  rw [show (base + 16 : Word) + 4 = base + 20 by bv_addr]
  rw [show (base + 20 : Word) + 4 = base + 24 by bv_addr]
  rw [show (base + 24 : Word) + 4 = base + 28 by bv_addr]
  rw [show (base + 28 : Word) + 4 = base + 32 by bv_addr]
  runBlock hLoadDest hLoadSrc hLoadCnt hPop hLoadPtr hLoadLen hAddEnd hAddDest hAddSrc

/-- Stack-form lift of the CALLDATACOPY preamble. The postcondition exposes
    the low-limb stack arguments, the absolute destination/source registers
    used by the byte loop, and keeps the consumed stack words owned below the
    advanced `x12` pointer. -/
theorem evm_calldatacopy_preamble_stack_spec_within
    (envBaseReg memBaseReg destReg srcReg cntReg cdpReg endReg : Reg)
    (hdest_ne_x0 : destReg ≠ .x0)
    (hsrc_ne_x0 : srcReg ≠ .x0)
    (hcnt_ne_x0 : cntReg ≠ .x0)
    (hcdp_ne_x0 : cdpReg ≠ .x0)
    (hend_ne_x0 : endReg ≠ .x0)
    (sp base envAddr memBase destOld srcOld cntOld cdpOld endOld : Word)
    (env : EvmEnv) (destOffset dataOffset size : EvmWord)
    (rest : List EvmWord) :
    let code := evm_calldatacopy_preamble_code envBaseReg memBaseReg
      destReg srcReg cntReg cdpReg endReg base
    cpsTripleWithin 9 base (base + 36) code
      ((.x12 ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) **
       (memBaseReg ↦ᵣ memBase) ** (destReg ↦ᵣ destOld) **
       (srcReg ↦ᵣ srcOld) ** (cntReg ↦ᵣ cntOld) **
       (cdpReg ↦ᵣ cdpOld) ** (endReg ↦ᵣ endOld) **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest ** envIs envAddr env)
      ((.x12 ↦ᵣ (sp + 96)) ** (envBaseReg ↦ᵣ envAddr) **
       (memBaseReg ↦ᵣ memBase) **
       (destReg ↦ᵣ (memBase + destOffset.getLimbN 0)) **
       (srcReg ↦ᵣ (env.callDataPtr + dataOffset.getLimbN 0)) **
       (cntReg ↦ᵣ size.getLimbN 0) **
       (cdpReg ↦ᵣ env.callDataPtr) **
       (endReg ↦ᵣ (env.callDataLen + env.callDataPtr)) **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest ** envIs envAddr env) := by
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
    evmStackIs (sp + 96) rest **
    envIsCallDataPtrLenRest envAddr env
  have hRaw := evm_calldatacopy_preamble_spec_within
    envBaseReg memBaseReg destReg srcReg cntReg cdpReg endReg
    hdest_ne_x0 hsrc_ne_x0 hcnt_ne_x0 hcdp_ne_x0 hend_ne_x0
    sp base envAddr memBase destOld srcOld cntOld cdpOld endOld
    (destOffset.getLimbN 0) (dataOffset.getLimbN 0) (size.getLimbN 0)
    env.callDataPtr env.callDataLen
  have hFramePC : frame.pcFree := by
    dsimp [frame]
    pcFree
    · exact pcFree_evmStackIs
    · unfold envIsCallDataPtrLenRest
      pcFree
  have hFramed := cpsTripleWithin_frameR frame hFramePC hRaw
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [evmStackIs_triple_flat, envIs_callDataPtrLen_split envAddr env] at hp
      dsimp [frame, evmWordIs] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      rw [evmStackIs_triple_flat, envIs_callDataPtrLen_split envAddr env]
      dsimp [frame, evmWordIs] at hp ⊢
      xperm_hyp hp)
    hFramed

/--
The separated CALLDATACOPY preamble CodeReq is the prefix of the full
`evm_calldatacopy_code` program.

Distinctive token:
Calldata.CopySpec.evm_calldatacopy_preamble_code_sub_full #104.
-/
theorem evm_calldatacopy_preamble_code_sub_full
    (envBaseReg memBaseReg destReg srcReg cntReg cdpReg endReg byteReg : Reg)
    (base : Word) :
    ∀ a i,
      (evm_calldatacopy_preamble_code envBaseReg memBaseReg destReg srcReg
        cntReg cdpReg endReg base) a = some i →
      (evm_calldatacopy_code envBaseReg memBaseReg destReg srcReg cntReg
        cdpReg endReg byteReg base) a = some i := by
  exact CodeReq.ofProg_mono_sub base base
    (evm_calldatacopy envBaseReg memBaseReg destReg srcReg cntReg cdpReg
      endReg byteReg)
    (evm_calldatacopy_preamble envBaseReg memBaseReg destReg srcReg cntReg
      cdpReg endReg)
    0
    (by simp)
    (by
      unfold evm_calldatacopy evm_calldatacopy_preamble
      rfl)
    (by
      rw [evm_calldatacopy_preamble_length, evm_calldatacopy_length]
      omega)
    (by
      rw [evm_calldatacopy_length]
      norm_num)

/--
Full-code version of `evm_calldatacopy_preamble_stack_spec_within`, useful
for composing the preamble with later loop specs over `evm_calldatacopy_code`.
-/
theorem evm_calldatacopy_full_code_preamble_stack_spec_within
    (envBaseReg memBaseReg destReg srcReg cntReg cdpReg endReg byteReg : Reg)
    (hdest_ne_x0 : destReg ≠ .x0)
    (hsrc_ne_x0 : srcReg ≠ .x0)
    (hcnt_ne_x0 : cntReg ≠ .x0)
    (hcdp_ne_x0 : cdpReg ≠ .x0)
    (hend_ne_x0 : endReg ≠ .x0)
    (sp base envAddr memBase destOld srcOld cntOld cdpOld endOld : Word)
    (env : EvmEnv) (destOffset dataOffset size : EvmWord)
    (rest : List EvmWord) :
    let code := evm_calldatacopy_code envBaseReg memBaseReg
      destReg srcReg cntReg cdpReg endReg byteReg base
    cpsTripleWithin 9 base (base + 36) code
      ((.x12 ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) **
       (memBaseReg ↦ᵣ memBase) ** (destReg ↦ᵣ destOld) **
       (srcReg ↦ᵣ srcOld) ** (cntReg ↦ᵣ cntOld) **
       (cdpReg ↦ᵣ cdpOld) ** (endReg ↦ᵣ endOld) **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest ** envIs envAddr env)
      ((.x12 ↦ᵣ (sp + 96)) ** (envBaseReg ↦ᵣ envAddr) **
       (memBaseReg ↦ᵣ memBase) **
       (destReg ↦ᵣ (memBase + destOffset.getLimbN 0)) **
       (srcReg ↦ᵣ (env.callDataPtr + dataOffset.getLimbN 0)) **
       (cntReg ↦ᵣ size.getLimbN 0) **
       (cdpReg ↦ᵣ env.callDataPtr) **
       (endReg ↦ᵣ (env.callDataLen + env.callDataPtr)) **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest ** envIs envAddr env) := by
  intro code
  exact cpsTripleWithin_extend_code
    (h := evm_calldatacopy_preamble_stack_spec_within
      envBaseReg memBaseReg destReg srcReg cntReg cdpReg endReg
      hdest_ne_x0 hsrc_ne_x0 hcnt_ne_x0 hcdp_ne_x0 hend_ne_x0
      sp base envAddr memBase destOld srcOld cntOld cdpOld endOld env
      destOffset dataOffset size rest)
    (hmono := evm_calldatacopy_preamble_code_sub_full
      envBaseReg memBaseReg destReg srcReg cntReg cdpReg endReg byteReg base)

/-- Partial memory-effect bridge for the bytes the loop is meant to write:
    at each destination-relative index below `size`, the byte selected by the
    CALLDATACOPY memory helper is the executable calldata byte at
    `dataOffset + i` (or zero if that source byte is out of bounds). -/
theorem evm_calldatacopy_partial_memory_effect
    (data : List (BitVec 8)) (destOffset dataOffset size : EvmWord)
    {i : Nat} (h : i < size.toNat) :
    let args := CallDataCopyArgs.copyArgs destOffset dataOffset size
    CallDataCopyMemory.copyWriteByteAt data args
        (CallDataCopyMemory.destinationStart args + i) =
      Calldata.callDataByte data (dataOffset.toNat + i) := by
  intro args
  exact CallDataCopyMemory.copyWriteByteAt_at_destination_add_eq_callDataByte h

end Calldata
end EvmAsm.Evm64
