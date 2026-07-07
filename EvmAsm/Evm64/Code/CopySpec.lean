/-
  EvmAsm.Evm64.Code.CopySpec

  Straight-line preamble specification for the EVM `CODECOPY` opcode
  (`Code/CopyProgram.lean`), the sibling of `Calldata/CopySpec.lean`.

  The preamble (the first 8 instructions of `evm_codecopy`) pops the three
  stack arguments, reads the running-bytecode length from the dispatcher's
  `codeSizeIs` cell at `env + codeSizeOff`, and initializes the loop
  registers: absolute destination pointer (`memBase + destOffset`), absolute
  source pointer (`codeBase + dataOffset`), byte counter (`size` low limb),
  and one-past-the-end source bound (`codeSize + codeBase`).

  Differences from the CALLDATACOPY preamble: the source base lives in a
  caller-preserved register (`codeBaseReg`, the dispatcher's `x21`) instead
  of being loaded from `env.callDataPtr`, so the preamble is 8 instructions
  instead of 9 and there is no `cdpReg`; and the source length comes from
  the raw `codeSizeIs` cell rather than a typed `envIs` field.
-/

import EvmAsm.Evm64.Code.CopyProgram
import EvmAsm.Evm64.Code.SizeSpec
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace Code

open EvmAsm.Rv64

/-- The executable CODECOPY preamble (the first 8 instructions of
    `evm_codecopy`), separated from the loop so its stack effect can be
    proved independently. -/
def evm_codecopy_preamble
    (envBaseReg memBaseReg codeBaseReg destReg srcReg cntReg endReg : Reg) :
    Program :=
  LD destReg .x12 0 ;;
  LD srcReg .x12 32 ;;
  LD cntReg .x12 64 ;;
  ADDI .x12 .x12 (BitVec.ofNat 12 96) ;;
  LD endReg envBaseReg (BitVec.ofNat 12 codeSizeOff) ;;
  ADD endReg endReg codeBaseReg ;;
  ADD destReg memBaseReg destReg ;;
  ADD srcReg codeBaseReg srcReg

/-- `CodeReq` for the CODECOPY preamble. -/
abbrev evm_codecopy_preamble_code
    (envBaseReg memBaseReg codeBaseReg destReg srcReg cntReg endReg : Reg)
    (base : Word) : CodeReq :=
  CodeReq.ofProg base
    (evm_codecopy_preamble envBaseReg memBaseReg codeBaseReg destReg srcReg
      cntReg endReg)

/-- The CODECOPY preamble is exactly the first eight instructions. -/
theorem evm_codecopy_preamble_length
    (envBaseReg memBaseReg codeBaseReg destReg srcReg cntReg endReg : Reg) :
    (evm_codecopy_preamble envBaseReg memBaseReg codeBaseReg destReg srcReg
      cntReg endReg).length = 8 := by
  simp [evm_codecopy_preamble, LD, ADDI, ADD, single, seq,
    Program.length_append]

private theorem signExtend12_codeSizeOff' :
    signExtend12 (BitVec.ofNat 12 codeSizeOff) =
      BitVec.ofNat 64 codeSizeOff := by
  rw [signExtend12_ofNat_small (by decide)]

/-- Raw preamble spec: load the low limbs of the three stack arguments,
    pop three EVM words, load the running-code length from the env block,
    then initialize the absolute destination/source pointers and the
    one-past-the-end source bound `codeSize + codeBase`. -/
theorem evm_codecopy_preamble_spec_within
    (envBaseReg memBaseReg codeBaseReg destReg srcReg cntReg endReg : Reg)
    (hdest_ne_x0 : destReg ≠ .x0)
    (hsrc_ne_x0 : srcReg ≠ .x0)
    (hcnt_ne_x0 : cntReg ≠ .x0)
    (hend_ne_x0 : endReg ≠ .x0)
    (sp base envAddr memBase codeBase destOld srcOld cntOld endOld : Word)
    (destOffset dataOffset size codeSizeW : Word) :
    let code := evm_codecopy_preamble_code envBaseReg memBaseReg codeBaseReg
      destReg srcReg cntReg endReg base
    cpsTripleWithin 8 base (base + 32) code
      ((.x12 ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) **
       (memBaseReg ↦ᵣ memBase) ** (codeBaseReg ↦ᵣ codeBase) **
       (destReg ↦ᵣ destOld) ** (srcReg ↦ᵣ srcOld) **
       (cntReg ↦ᵣ cntOld) ** (endReg ↦ᵣ endOld) **
       (sp ↦ₘ destOffset) ** ((sp + 32) ↦ₘ dataOffset) **
       ((sp + 64) ↦ₘ size) **
       ((envAddr + BitVec.ofNat 64 codeSizeOff) ↦ₘ codeSizeW))
      ((.x12 ↦ᵣ (sp + 96)) ** (envBaseReg ↦ᵣ envAddr) **
       (memBaseReg ↦ᵣ memBase) ** (codeBaseReg ↦ᵣ codeBase) **
       (destReg ↦ᵣ (memBase + destOffset)) **
       (srcReg ↦ᵣ (codeBase + dataOffset)) ** (cntReg ↦ᵣ size) **
       (endReg ↦ᵣ (codeSizeW + codeBase)) **
       (sp ↦ₘ destOffset) ** ((sp + 32) ↦ₘ dataOffset) **
       ((sp + 64) ↦ₘ size) **
       ((envAddr + BitVec.ofNat 64 codeSizeOff) ↦ₘ codeSizeW)) := by
  have hLoadDest := ld_spec_gen_within destReg .x12 sp destOld destOffset
    (0 : BitVec 12) base hdest_ne_x0
  have hLoadSrc := ld_spec_gen_within srcReg .x12 sp srcOld dataOffset
    (32 : BitVec 12) (base + 4) hsrc_ne_x0
  have hLoadCnt := ld_spec_gen_within cntReg .x12 sp cntOld size
    (64 : BitVec 12) (base + 8) hcnt_ne_x0
  have hPop := addi_spec_gen_same_within .x12 sp
    (BitVec.ofNat 12 96) (base + 12) (by nofun)
  have hLoadEnd := ld_spec_gen_within endReg envBaseReg envAddr endOld
    codeSizeW (BitVec.ofNat 12 codeSizeOff) (base + 16) hend_ne_x0
  simp only [signExtend12_codeSizeOff'] at hLoadEnd
  have hAddEnd := add_spec_gen_rd_eq_rs1_within endReg codeBaseReg
    codeSizeW codeBase (base + 20) hend_ne_x0
  have hAddDest := add_spec_gen_rd_eq_rs2_within destReg memBaseReg
    memBase destOffset (base + 24) hdest_ne_x0
  have hAddSrc := add_spec_gen_rd_eq_rs2_within srcReg codeBaseReg
    codeBase dataOffset (base + 28) hsrc_ne_x0
  simp only [signExtend12_0] at hLoadDest
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) by decide] at hLoadSrc
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) by decide] at hLoadCnt
  rw [show sp + signExtend12 (BitVec.ofNat 12 96) = sp + 96 by
    rw [show signExtend12 (BitVec.ofNat 12 96) = (96 : Word) by decide]] at hPop
  unfold evm_codecopy_preamble_code evm_codecopy_preamble
  change cpsTripleWithin 8 base (base + 32)
    (CodeReq.ofProg base
      [.LD destReg .x12 0, .LD srcReg .x12 32, .LD cntReg .x12 64,
       .ADDI .x12 .x12 (BitVec.ofNat 12 96),
       .LD endReg envBaseReg (BitVec.ofNat 12 codeSizeOff),
       .ADD endReg endReg codeBaseReg, .ADD destReg memBaseReg destReg,
       .ADD srcReg codeBaseReg srcReg])
    _ _
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  rw [show (base + 4 : Word) + 4 = base + 8 by bv_addr]
  rw [show (base + 8 : Word) + 4 = base + 12 by bv_addr]
  rw [show (base + 12 : Word) + 4 = base + 16 by bv_addr]
  rw [show (base + 16 : Word) + 4 = base + 20 by bv_addr]
  rw [show (base + 20 : Word) + 4 = base + 24 by bv_addr]
  rw [show (base + 24 : Word) + 4 = base + 28 by bv_addr]
  runBlock hLoadDest hLoadSrc hLoadCnt hPop hLoadEnd hAddEnd hAddDest hAddSrc

/-- Stack-form lift of the CODECOPY preamble. The postcondition exposes the
    low-limb stack arguments, the absolute destination/source registers used
    by the byte loop, and keeps the consumed stack words owned below the
    advanced `x12` pointer. -/
theorem evm_codecopy_preamble_stack_spec_within
    (envBaseReg memBaseReg codeBaseReg destReg srcReg cntReg endReg : Reg)
    (hdest_ne_x0 : destReg ≠ .x0)
    (hsrc_ne_x0 : srcReg ≠ .x0)
    (hcnt_ne_x0 : cntReg ≠ .x0)
    (hend_ne_x0 : endReg ≠ .x0)
    (sp base envAddr memBase codeBase destOld srcOld cntOld endOld
      codeSizeW : Word)
    (destOffset dataOffset size : EvmWord)
    (rest : List EvmWord) :
    let code := evm_codecopy_preamble_code envBaseReg memBaseReg codeBaseReg
      destReg srcReg cntReg endReg base
    cpsTripleWithin 8 base (base + 32) code
      ((.x12 ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) **
       (memBaseReg ↦ᵣ memBase) ** (codeBaseReg ↦ᵣ codeBase) **
       (destReg ↦ᵣ destOld) ** (srcReg ↦ᵣ srcOld) **
       (cntReg ↦ᵣ cntOld) ** (endReg ↦ᵣ endOld) **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest ** codeSizeIs envAddr codeSizeW)
      ((.x12 ↦ᵣ (sp + 96)) ** (envBaseReg ↦ᵣ envAddr) **
       (memBaseReg ↦ᵣ memBase) ** (codeBaseReg ↦ᵣ codeBase) **
       (destReg ↦ᵣ (memBase + destOffset.getLimbN 0)) **
       (srcReg ↦ᵣ (codeBase + dataOffset.getLimbN 0)) **
       (cntReg ↦ᵣ size.getLimbN 0) **
       (endReg ↦ᵣ (codeSizeW + codeBase)) **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest ** codeSizeIs envAddr codeSizeW) := by
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
  have hRaw := evm_codecopy_preamble_spec_within
    envBaseReg memBaseReg codeBaseReg destReg srcReg cntReg endReg
    hdest_ne_x0 hsrc_ne_x0 hcnt_ne_x0 hend_ne_x0
    sp base envAddr memBase codeBase destOld srcOld cntOld endOld
    (destOffset.getLimbN 0) (dataOffset.getLimbN 0) (size.getLimbN 0)
    codeSizeW
  have hFramePC : frame.pcFree := by
    dsimp [frame]
    pcFree
  have hFramed := cpsTripleWithin_frameR frame hFramePC hRaw
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [evmStackIs_triple_flat] at hp
      dsimp [frame, evmWordIs, codeSizeIs] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      rw [evmStackIs_triple_flat]
      dsimp [frame, evmWordIs, codeSizeIs] at hp ⊢
      xperm_hyp hp)
    hFramed

/--
The separated CODECOPY preamble CodeReq is the prefix of the full
`evm_codecopy_code` program.

Distinctive token: Code.CopySpec.evm_codecopy_preamble_code_sub_full.
-/
theorem evm_codecopy_preamble_code_sub_full
    (envBaseReg memBaseReg codeBaseReg destReg srcReg cntReg endReg
      byteReg : Reg) (base : Word) :
    ∀ a i,
      (evm_codecopy_preamble_code envBaseReg memBaseReg codeBaseReg destReg
        srcReg cntReg endReg base) a = some i →
      (evm_codecopy_code envBaseReg memBaseReg codeBaseReg destReg srcReg
        cntReg endReg byteReg base) a = some i := by
  exact CodeReq.ofProg_mono_sub base base
    (evm_codecopy envBaseReg memBaseReg codeBaseReg destReg srcReg cntReg
      endReg byteReg)
    (evm_codecopy_preamble envBaseReg memBaseReg codeBaseReg destReg srcReg
      cntReg endReg)
    0
    (by simp)
    (by
      unfold evm_codecopy evm_codecopy_preamble
      rfl)
    (by
      rw [evm_codecopy_preamble_length, evm_codecopy_length]
      omega)
    (by
      rw [evm_codecopy_length]
      norm_num)

/--
Full-code version of `evm_codecopy_preamble_stack_spec_within`, useful for
composing the preamble with the loop spec over `evm_codecopy_code`.
-/
theorem evm_codecopy_full_code_preamble_stack_spec_within
    (envBaseReg memBaseReg codeBaseReg destReg srcReg cntReg endReg
      byteReg : Reg)
    (hdest_ne_x0 : destReg ≠ .x0)
    (hsrc_ne_x0 : srcReg ≠ .x0)
    (hcnt_ne_x0 : cntReg ≠ .x0)
    (hend_ne_x0 : endReg ≠ .x0)
    (sp base envAddr memBase codeBase destOld srcOld cntOld endOld
      codeSizeW : Word)
    (destOffset dataOffset size : EvmWord)
    (rest : List EvmWord) :
    let code := evm_codecopy_code envBaseReg memBaseReg codeBaseReg destReg
      srcReg cntReg endReg byteReg base
    cpsTripleWithin 8 base (base + 32) code
      ((.x12 ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) **
       (memBaseReg ↦ᵣ memBase) ** (codeBaseReg ↦ᵣ codeBase) **
       (destReg ↦ᵣ destOld) ** (srcReg ↦ᵣ srcOld) **
       (cntReg ↦ᵣ cntOld) ** (endReg ↦ᵣ endOld) **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest ** codeSizeIs envAddr codeSizeW)
      ((.x12 ↦ᵣ (sp + 96)) ** (envBaseReg ↦ᵣ envAddr) **
       (memBaseReg ↦ᵣ memBase) ** (codeBaseReg ↦ᵣ codeBase) **
       (destReg ↦ᵣ (memBase + destOffset.getLimbN 0)) **
       (srcReg ↦ᵣ (codeBase + dataOffset.getLimbN 0)) **
       (cntReg ↦ᵣ size.getLimbN 0) **
       (endReg ↦ᵣ (codeSizeW + codeBase)) **
       evmStackIs sp [destOffset, dataOffset, size] **
       evmStackIs (sp + 96) rest ** codeSizeIs envAddr codeSizeW) := by
  intro code
  exact cpsTripleWithin_extend_code
    (h := evm_codecopy_preamble_stack_spec_within
      envBaseReg memBaseReg codeBaseReg destReg srcReg cntReg endReg
      hdest_ne_x0 hsrc_ne_x0 hcnt_ne_x0 hend_ne_x0
      sp base envAddr memBase codeBase destOld srcOld cntOld endOld
      codeSizeW destOffset dataOffset size rest)
    (hmono := evm_codecopy_preamble_code_sub_full
      envBaseReg memBaseReg codeBaseReg destReg srcReg cntReg endReg
      byteReg base)

end Code
end EvmAsm.Evm64
