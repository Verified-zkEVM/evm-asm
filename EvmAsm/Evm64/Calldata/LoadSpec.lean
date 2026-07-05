/-
  EvmAsm.Evm64.Calldata.LoadSpec

  The public CALLDATALOAD stack spec (GH #104): zero arm, dispatch/arm
  merge, and the top-level `evm_calldataload_stack_spec_within` — THE
  registry witness for the CALLDATALOAD `.proven` flip.

  Layers:
    * `calldataload_zero_arm_spec_within` — the 4 `SD x0` stores of the
      out-of-bounds arm (`base + 428 → base + 444`), writing the zero
      word over the popped offset slot in place.
    * `calldataload_merged_spec_within` — the dispatch branch
      (`LoadDispatch.lean`) merged with the window arm
      (`LoadWindowArm.lean`) and the zero arm via
      `cpsBranchWithin_merge_same_cr`: from the raw operand cells to the
      four output limbs of `callDataLoadWord data offsetWord.toNat`,
      scratch registers shed to `regOwn`.  The branch facts are consumed
      by the Slice-1 out-of-bounds corollaries: on the window arm the
      flag decomposition gives the in-bounds index, on the zero arm it
      gives `callDataLoadWord … = 0`.
    * `evm_calldataload_stack_spec_within` — the `evmStackIs` / `envIs`
      lift: pops the 256-bit offset, pushes
      `callDataLoadWord data offsetWord.toNat` (SP unchanged — pop 1 /
      push 1), with the calldata modeled by `calldataRegionIs` and the
      env block framed through `envIs_callDataPtrLen_split`.

  Every 256-bit offset is covered: in-bounds windows (including the
  straddle `offset < len < offset + 32`, zero-backed by the region's
  32-byte pad), low-limb out-of-bounds, and upper-limb offsets ≥ 2^64.
  The only non-register hypotheses are the static resource-shape facts
  `h_len` (the byte list matches the env length field) and `h_wf`
  (the region is aligned / in range) — no operand-domain restriction.
-/

import EvmAsm.Evm64.Calldata.LoadDispatch
import EvmAsm.Evm64.Calldata.LoadWindowArm

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace Calldata

open EvmAsm.Rv64
open EvmAsm.Evm64.EvmEnv

/-! ## Pure plumbing -/

/-- Peel a pure `⌜fact⌝` from the right of the precondition into an
    ambient hypothesis (same shape as the DIV v6 merge plumbing). -/
private theorem cpsTripleWithin_of_pure_imp
    {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} {fact : Prop}
    (h : fact → cpsTripleWithin nSteps entry exit_ cr P Q) :
    cpsTripleWithin nSteps entry exit_ cr (P ** ⌜fact⌝) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, hpq⟩ := hPR
  obtain ⟨h1, h2, hd, hunion, hPF, hR_⟩ := hpq
  have hpf := (sepConj_pure_right h1).1 hPF
  exact h hpf.2 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hunion, hpf.1, hR_⟩ hpc

/-- The window output word at the decoded offset argument is the pure
    CALLDATALOAD semantics. -/
private theorem calldataload_window_word_eq
    (data : List (BitVec 8)) (offsetWord : EvmWord) :
    calldataLoadWindowOutputWordFromArgs data
        (CallDataLoadArgs.loadArgs offsetWord) =
      callDataLoadWord data offsetWord.toNat := by
  rw [calldataLoadWindowOutputWordFromArgs_eq_loadedWordFromArgs,
    CallDataLoadArgs.loadedWordFromArgs_eq, CallDataLoadArgs.loadArgs_offset]

/-- Rewrite one window-arm output limb into a limb of the pure
    CALLDATALOAD word (upper offset limbs zero, so the low limb IS the
    offset).  Limb 0 is window quarter `w = 24`. -/
private theorem calldataload_out_limb0
    (data : List (BitVec 8)) (offsetWord : EvmWord)
    (h_upper : offsetWord.getLimbN 1 ||| offsetWord.getLimbN 2 |||
      offsetWord.getLimbN 3 = 0) :
    calldataloadOutputLimb data (offsetWord.getLimbN 0).toNat 24 =
      (callDataLoadWord data offsetWord.toNat).getLimbN 0 := by
  have h_nat : offsetWord.toNat = (offsetWord.getLimbN 0).toNat :=
    toNat_eq_getLimbN0_toNat_of_upper_or_zero h_upper
  rw [← calldataload_window_word_eq data offsetWord,
    getLimbN_calldataLoadWindowOutputWordFromArgs_0, ← h_nat]
  unfold calldataloadOutputLimb
  simp only [CallDataLoadArgs.windowByteFromArgs_eq,
    CallDataLoadArgs.loadArgs_offset, Nat.add_assoc, Nat.reduceAdd]

private theorem calldataload_out_limb1
    (data : List (BitVec 8)) (offsetWord : EvmWord)
    (h_upper : offsetWord.getLimbN 1 ||| offsetWord.getLimbN 2 |||
      offsetWord.getLimbN 3 = 0) :
    calldataloadOutputLimb data (offsetWord.getLimbN 0).toNat 16 =
      (callDataLoadWord data offsetWord.toNat).getLimbN 1 := by
  have h_nat : offsetWord.toNat = (offsetWord.getLimbN 0).toNat :=
    toNat_eq_getLimbN0_toNat_of_upper_or_zero h_upper
  rw [← calldataload_window_word_eq data offsetWord,
    getLimbN_calldataLoadWindowOutputWordFromArgs_1, ← h_nat]
  unfold calldataloadOutputLimb
  simp only [CallDataLoadArgs.windowByteFromArgs_eq,
    CallDataLoadArgs.loadArgs_offset, Nat.add_assoc, Nat.reduceAdd]

private theorem calldataload_out_limb2
    (data : List (BitVec 8)) (offsetWord : EvmWord)
    (h_upper : offsetWord.getLimbN 1 ||| offsetWord.getLimbN 2 |||
      offsetWord.getLimbN 3 = 0) :
    calldataloadOutputLimb data (offsetWord.getLimbN 0).toNat 8 =
      (callDataLoadWord data offsetWord.toNat).getLimbN 2 := by
  have h_nat : offsetWord.toNat = (offsetWord.getLimbN 0).toNat :=
    toNat_eq_getLimbN0_toNat_of_upper_or_zero h_upper
  rw [← calldataload_window_word_eq data offsetWord,
    getLimbN_calldataLoadWindowOutputWordFromArgs_2, ← h_nat]
  unfold calldataloadOutputLimb
  simp only [CallDataLoadArgs.windowByteFromArgs_eq,
    CallDataLoadArgs.loadArgs_offset, Nat.add_assoc, Nat.reduceAdd]

private theorem calldataload_out_limb3
    (data : List (BitVec 8)) (offsetWord : EvmWord)
    (h_upper : offsetWord.getLimbN 1 ||| offsetWord.getLimbN 2 |||
      offsetWord.getLimbN 3 = 0) :
    calldataloadOutputLimb data (offsetWord.getLimbN 0).toNat 0 =
      (callDataLoadWord data offsetWord.toNat).getLimbN 3 := by
  have h_nat : offsetWord.toNat = (offsetWord.getLimbN 0).toNat :=
    toNat_eq_getLimbN0_toNat_of_upper_or_zero h_upper
  rw [← calldataload_window_word_eq data offsetWord,
    getLimbN_calldataLoadWindowOutputWordFromArgs_3, ← h_nat]
  unfold calldataloadOutputLimb
  simp only [CallDataLoadArgs.windowByteFromArgs_eq,
    CallDataLoadArgs.loadArgs_offset, Nat.add_assoc, Nat.reduceAdd]

/-- Shed the eight scratch registers of the merged postcondition to
    ownership, keeping the kept atoms pointwise. -/
private theorem calldataload_shed_scratch
    (envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg)
    (sp envAddr c0 c1 c2 c3 : Word) (env : EvmEnv)
    (data : List (BitVec 8))
    (vOff vAddr vByte vAcc vCdp vLen vFlag vTmp : Word) :
    ∀ ps,
      (((.x12 : Reg) ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       (sp ↦ₘ c0) ** ((sp + 8) ↦ₘ c1) **
       ((sp + 16) ↦ₘ c2) ** ((sp + 24) ↦ₘ c3) **
       ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ env.callDataPtr) **
       ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ env.callDataLen) **
       calldataRegionIs env.callDataPtr data **
       (offReg ↦ᵣ vOff) ** (addrReg ↦ᵣ vAddr) ** (byteReg ↦ᵣ vByte) **
       (accReg ↦ᵣ vAcc) ** (cdpReg ↦ᵣ vCdp) ** (lenReg ↦ᵣ vLen) **
       (flagReg ↦ᵣ vFlag) ** (tmpReg ↦ᵣ vTmp)) ps →
      (((.x12 : Reg) ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       (sp ↦ₘ c0) ** ((sp + 8) ↦ₘ c1) **
       ((sp + 16) ↦ₘ c2) ** ((sp + 24) ↦ₘ c3) **
       ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ env.callDataPtr) **
       ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ env.callDataLen) **
       calldataRegionIs env.callDataPtr data **
       regOwn offReg ** regOwn addrReg ** regOwn byteReg **
       regOwn accReg ** regOwn cdpReg ** regOwn lenReg **
       regOwn flagReg ** regOwn tmpReg) ps := by
  iterate 10 apply sepConj_mono_right
  iterate 7 apply sepConj_mono (regIs_implies_regOwn _)
  exact regIs_implies_regOwn _

/-! ## The zero arm -/

/-- The out-of-bounds zero arm (`base + 428 → base + 444`, falling
    through to the common exit): write the zero word over the popped
    offset slot in place. -/
theorem calldataload_zero_arm_spec_within
    (envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg)
    (sp base m0 m1 m2 m3 : Word) :
    cpsTripleWithin 4 (base + 428) (base + 444)
      (evm_calldataload_code envBaseReg offReg byteReg accReg addrReg
        cdpReg lenReg flagReg tmpReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (sp ↦ₘ m0) ** ((sp + 8) ↦ₘ m1) **
       ((sp + 16) ↦ₘ m2) ** ((sp + 24) ↦ₘ m3))
      (((.x12 : Reg) ↦ᵣ sp) ** (sp ↦ₘ (0 : Word)) **
       ((sp + 8) ↦ₘ (0 : Word)) ** ((sp + 16) ↦ₘ (0 : Word)) **
       ((sp + 24) ↦ₘ (0 : Word))) := by
  have h0 := sd_x0_spec_gen_within .x12 sp m0 (0 : BitVec 12) (base + 428)
  simp only [signExtend12_0] at h0
  have h1 := sd_x0_spec_gen_within .x12 sp m1 (8 : BitVec 12) (base + 432)
  simp only [signExtend12_8] at h1
  have h2 := sd_x0_spec_gen_within .x12 sp m2 (16 : BitVec 12) (base + 436)
  simp only [signExtend12_16] at h2
  have h3 := sd_x0_spec_gen_within .x12 sp m3 (24 : BitVec 12) (base + 440)
  simp only [signExtend12_24] at h3
  refine cpsTripleWithin_extend_code
    (cr := CodeReq.ofProg (base + 428)
      [.SD .x12 .x0 0, .SD .x12 .x0 8, .SD .x12 .x0 16, .SD .x12 .x0 24])
    (hmono := fun a i h =>
      evm_calldataload_zero_arm_code_sub_full envBaseReg offReg byteReg
        accReg addrReg cdpReg lenReg flagReg tmpReg base a i h) ?_
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_singleton]
  rw [show (base + 428 : Word) + 4 = base + 432 by bv_addr]
  rw [show (base + 432 : Word) + 4 = base + 436 by bv_addr]
  rw [show (base + 436 : Word) + 4 = base + 440 by bv_addr]
  runBlock h0 h1 h2 h3

/-! ## The merged triple -/

/-- The dispatch-shape assertion threading the merge: the fixed
    registers, the operand-slot offset limbs, the env pointer/length
    cells, the calldata region, the window scratch registers, and the
    four dispatch registers at parametric values (`old` values at entry,
    post-dispatch values at the arm entries). -/
private def calldataloadDispatchShape
    (envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg)
    (sp envAddr vCdp vLen vFlag vTmp offVal addrVal byteVal accVal : Word)
    (env : EvmEnv) (offsetWord : EvmWord) (data : List (BitVec 8)) :
    Assertion :=
  ((.x12 : Reg) ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  (sp ↦ₘ offsetWord.getLimbN 0) ** ((sp + 8) ↦ₘ offsetWord.getLimbN 1) **
  ((sp + 16) ↦ₘ offsetWord.getLimbN 2) **
  ((sp + 24) ↦ₘ offsetWord.getLimbN 3) **
  ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ env.callDataPtr) **
  ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ env.callDataLen) **
  calldataRegionIs env.callDataPtr data **
  (offReg ↦ᵣ offVal) ** (addrReg ↦ᵣ addrVal) ** (byteReg ↦ᵣ byteVal) **
  (accReg ↦ᵣ accVal) ** (cdpReg ↦ᵣ vCdp) ** (lenReg ↦ᵣ vLen) **
  (flagReg ↦ᵣ vFlag) ** (tmpReg ↦ᵣ vTmp)

private theorem calldataloadDispatchShape_unfold
    {envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg}
    {sp envAddr vCdp vLen vFlag vTmp offVal addrVal byteVal accVal : Word}
    {env : EvmEnv} {offsetWord : EvmWord} {data : List (BitVec 8)} :
    calldataloadDispatchShape envBaseReg offReg byteReg accReg addrReg
        cdpReg lenReg flagReg tmpReg sp envAddr vCdp vLen vFlag vTmp
        offVal addrVal byteVal accVal env offsetWord data =
      (((.x12 : Reg) ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       (sp ↦ₘ offsetWord.getLimbN 0) **
       ((sp + 8) ↦ₘ offsetWord.getLimbN 1) **
       ((sp + 16) ↦ₘ offsetWord.getLimbN 2) **
       ((sp + 24) ↦ₘ offsetWord.getLimbN 3) **
       ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ env.callDataPtr) **
       ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ env.callDataLen) **
       calldataRegionIs env.callDataPtr data **
       (offReg ↦ᵣ offVal) ** (addrReg ↦ᵣ addrVal) ** (byteReg ↦ᵣ byteVal) **
       (accReg ↦ᵣ accVal) ** (cdpReg ↦ᵣ vCdp) ** (lenReg ↦ᵣ vLen) **
       (flagReg ↦ᵣ vFlag) ** (tmpReg ↦ᵣ vTmp)) := rfl

/-- The merged postcondition: the four output limbs of the pure
    CALLDATALOAD word over the popped operand slot, all scratch
    registers shed to ownership, region and env cells untouched. -/
def calldataloadMergedPost
    (envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg)
    (sp envAddr : Word) (env : EvmEnv) (out : EvmWord)
    (data : List (BitVec 8)) : Assertion :=
  ((.x12 : Reg) ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  (sp ↦ₘ out.getLimbN 0) ** ((sp + 8) ↦ₘ out.getLimbN 1) **
  ((sp + 16) ↦ₘ out.getLimbN 2) ** ((sp + 24) ↦ₘ out.getLimbN 3) **
  ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ env.callDataPtr) **
  ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ env.callDataLen) **
  calldataRegionIs env.callDataPtr data **
  regOwn offReg ** regOwn addrReg ** regOwn byteReg **
  regOwn accReg ** regOwn cdpReg ** regOwn lenReg **
  regOwn flagReg ** regOwn tmpReg

theorem calldataloadMergedPost_unfold
    {envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg}
    {sp envAddr : Word} {env : EvmEnv} {out : EvmWord}
    {data : List (BitVec 8)} :
    calldataloadMergedPost envBaseReg offReg byteReg accReg addrReg
        cdpReg lenReg flagReg tmpReg sp envAddr env out data =
      (((.x12 : Reg) ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       (sp ↦ₘ out.getLimbN 0) ** ((sp + 8) ↦ₘ out.getLimbN 1) **
       ((sp + 16) ↦ₘ out.getLimbN 2) ** ((sp + 24) ↦ₘ out.getLimbN 3) **
       ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ env.callDataPtr) **
       ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ env.callDataLen) **
       calldataRegionIs env.callDataPtr data **
       regOwn offReg ** regOwn addrReg ** regOwn byteReg **
       regOwn accReg ** regOwn cdpReg ** regOwn lenReg **
       regOwn flagReg ** regOwn tmpReg) := rfl

/-- CALLDATALOAD over the full program, raw-cell form: dispatch branch
    merged with the window and zero arms.  From the popped offset limbs
    in the operand slot to the four output limbs of
    `callDataLoadWord data offsetWord.toNat`, all scratch registers shed
    to ownership.  107 steps, `base → base + 444`. -/
theorem calldataload_merged_spec_within
    (envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg)
    (h_off_ne_x0 : offReg ≠ .x0) (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_cdp_ne_x0 : cdpReg ≠ .x0) (h_len_ne_x0 : lenReg ≠ .x0)
    (h_flag_ne_x0 : flagReg ≠ .x0) (h_tmp_ne_x0 : tmpReg ≠ .x0)
    (sp base envAddr offOld addrOld byteOld accOld cdpOld lenOld flagOld
      tmpOld : Word)
    (env : EvmEnv) (offsetWord : EvmWord) (data : List (BitVec 8))
    (h_len : data.length = env.callDataLen.toNat)
    (h_wf : CalldataRegionWf env.callDataPtr data) :
    cpsTripleWithin 107 base (base + 444)
      (evm_calldataload_code envBaseReg offReg byteReg accReg addrReg
        cdpReg lenReg flagReg tmpReg base)
      (calldataloadDispatchShape envBaseReg offReg byteReg accReg addrReg
        cdpReg lenReg flagReg tmpReg sp envAddr cdpOld lenOld flagOld
        tmpOld offOld addrOld byteOld accOld env offsetWord data)
      (calldataloadMergedPost envBaseReg offReg byteReg accReg addrReg
        cdpReg lenReg flagReg tmpReg sp envAddr env
        (callDataLoadWord data offsetWord.toNat) data) := by
  -- The dispatch branch, framed with the window scratch registers and
  -- the calldata region.
  have h_br := calldataload_dispatch_branch_spec_within envBaseReg offReg
    byteReg accReg addrReg cdpReg lenReg flagReg tmpReg
    h_cdp_ne_x0 h_len_ne_x0 h_flag_ne_x0 h_tmp_ne_x0
    sp base envAddr cdpOld lenOld flagOld tmpOld
    (offsetWord.getLimbN 0) (offsetWord.getLimbN 1)
    (offsetWord.getLimbN 2) (offsetWord.getLimbN 3)
    env.callDataPtr env.callDataLen
  have h_brf := cpsBranchWithin_frameR
    ((offReg ↦ᵣ offOld) ** (addrReg ↦ᵣ addrOld) ** (byteReg ↦ᵣ byteOld) **
     (accReg ↦ᵣ accOld) ** calldataRegionIs env.callDataPtr data)
    (pcFree_sepConj (by pcFree)
      (pcFree_sepConj (by pcFree)
        (pcFree_sepConj (by pcFree)
          (pcFree_sepConj (by pcFree)
            (calldataRegionIs_pcFree env.callDataPtr data))))) h_br
  -- The window (fall-through) arm, given the in-bounds branch fact.
  have h_win_inner :
      calldataload_oobFlagW (offsetWord.getLimbN 0) (offsetWord.getLimbN 1)
          (offsetWord.getLimbN 2) (offsetWord.getLimbN 3)
          env.callDataLen = (0 : Word) →
      cpsTripleWithin 95 (base + 48) (base + 444)
        (evm_calldataload_code envBaseReg offReg byteReg accReg addrReg
          cdpReg lenReg flagReg tmpReg base)
        (calldataloadDispatchShape envBaseReg offReg byteReg accReg
          addrReg cdpReg lenReg flagReg tmpReg sp envAddr
          env.callDataPtr env.callDataLen
          (calldataload_oobFlagW (offsetWord.getLimbN 0)
            (offsetWord.getLimbN 1) (offsetWord.getLimbN 2)
            (offsetWord.getLimbN 3) env.callDataLen)
          (calldataload_oobBit (offsetWord.getLimbN 0) env.callDataLen)
          offOld addrOld byteOld accOld env offsetWord data)
        (calldataloadMergedPost envBaseReg offReg byteReg accReg addrReg
          cdpReg lenReg flagReg tmpReg sp envAddr env
          (callDataLoadWord data offsetWord.toNat) data) := by
    intro h_flag
    obtain ⟨h_upper, h_lt⟩ := calldataload_oobFlagW_eq_zero_iff.mp h_flag
    have h_off : (offsetWord.getLimbN 0).toNat < data.length := by
      rw [h_len]; exact BitVec.lt_def.mp h_lt
    have h_arm := calldataload_window_arm_spec_within envBaseReg offReg
      byteReg accReg addrReg cdpReg lenReg flagReg tmpReg
      sp base env.callDataPtr (offsetWord.getLimbN 0)
      offOld addrOld byteOld accOld
      (offsetWord.getLimbN 1) (offsetWord.getLimbN 2)
      (offsetWord.getLimbN 3) data
      h_off_ne_x0 h_addr_ne_x0 h_byte_ne_x0 h_acc_ne_x0 h_wf h_off
    have h_armf := cpsTripleWithin_frameR
      ((envBaseReg ↦ᵣ envAddr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       (lenReg ↦ᵣ env.callDataLen) **
       (flagReg ↦ᵣ calldataload_oobFlagW (offsetWord.getLimbN 0)
         (offsetWord.getLimbN 1) (offsetWord.getLimbN 2)
         (offsetWord.getLimbN 3) env.callDataLen) **
       (tmpReg ↦ᵣ calldataload_oobBit (offsetWord.getLimbN 0)
         env.callDataLen) **
       ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ env.callDataPtr) **
       ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ env.callDataLen))
      (by pcFree) h_arm
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) h_armf
    · rw [calldataloadDispatchShape_unfold] at hp
      rw [calldataloadWindowArmPre_unfold]
      xperm_hyp hp
    · rw [calldataloadWindowArmPost_unfold, calldataloadArmMid_unfold] at hq
      rw [calldataloadMergedPost_unfold,
        ← calldataload_out_limb0 data offsetWord h_upper,
        ← calldataload_out_limb1 data offsetWord h_upper,
        ← calldataload_out_limb2 data offsetWord h_upper,
        ← calldataload_out_limb3 data offsetWord h_upper]
      refine calldataload_shed_scratch envBaseReg offReg byteReg accReg
        addrReg cdpReg lenReg flagReg tmpReg sp envAddr
        (calldataloadOutputLimb data (offsetWord.getLimbN 0).toNat 24)
        (calldataloadOutputLimb data (offsetWord.getLimbN 0).toNat 16)
        (calldataloadOutputLimb data (offsetWord.getLimbN 0).toNat 8)
        (calldataloadOutputLimb data (offsetWord.getLimbN 0).toNat 0)
        env data
        (offsetWord.getLimbN 0)
        (env.callDataPtr + offsetWord.getLimbN 0)
        ((callDataByte data
          ((offsetWord.getLimbN 0).toNat + 0 + 7)).zeroExtend 64)
        (calldataloadOutputLimb data (offsetWord.getLimbN 0).toNat 0)
        env.callDataPtr env.callDataLen
        (calldataload_oobFlagW (offsetWord.getLimbN 0)
          (offsetWord.getLimbN 1) (offsetWord.getLimbN 2)
          (offsetWord.getLimbN 3) env.callDataLen)
        (calldataload_oobBit (offsetWord.getLimbN 0) env.callDataLen)
        _ ?_
      xperm_hyp hq
  have h_win := cpsTripleWithin_of_pure_imp h_win_inner
  -- The zero (taken) arm, given the out-of-bounds branch fact.
  have h_zero_inner :
      calldataload_oobFlagW (offsetWord.getLimbN 0) (offsetWord.getLimbN 1)
          (offsetWord.getLimbN 2) (offsetWord.getLimbN 3)
          env.callDataLen ≠ (0 : Word) →
      cpsTripleWithin 95 (base + 428) (base + 444)
        (evm_calldataload_code envBaseReg offReg byteReg accReg addrReg
          cdpReg lenReg flagReg tmpReg base)
        (calldataloadDispatchShape envBaseReg offReg byteReg accReg
          addrReg cdpReg lenReg flagReg tmpReg sp envAddr
          env.callDataPtr env.callDataLen
          (calldataload_oobFlagW (offsetWord.getLimbN 0)
            (offsetWord.getLimbN 1) (offsetWord.getLimbN 2)
            (offsetWord.getLimbN 3) env.callDataLen)
          (calldataload_oobBit (offsetWord.getLimbN 0) env.callDataLen)
          offOld addrOld byteOld accOld env offsetWord data)
        (calldataloadMergedPost envBaseReg offReg byteReg accReg addrReg
          cdpReg lenReg flagReg tmpReg sp envAddr env
          (callDataLoadWord data offsetWord.toNat) data) := by
    intro h_flag_ne
    have h_out0 : callDataLoadWord data offsetWord.toNat = 0 := by
      by_cases h_upper : offsetWord.getLimbN 1 ||| offsetWord.getLimbN 2 |||
          offsetWord.getLimbN 3 = 0
      · refine callDataLoadWord_zero_of_low_ge_len h_len h_upper ?_
        intro h_lt
        exact h_flag_ne (calldataload_oobFlagW_eq_zero_iff.mpr
          ⟨h_upper, h_lt⟩)
      · exact callDataLoadWord_zero_of_upper_or_ne_zero h_len h_upper
    have h_zarm := calldataload_zero_arm_spec_within envBaseReg offReg
      byteReg accReg addrReg cdpReg lenReg flagReg tmpReg sp base
      (offsetWord.getLimbN 0) (offsetWord.getLimbN 1)
      (offsetWord.getLimbN 2) (offsetWord.getLimbN 3)
    have h_zarmf := cpsTripleWithin_frameR
      ((envBaseReg ↦ᵣ envAddr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       (offReg ↦ᵣ offOld) ** (addrReg ↦ᵣ addrOld) **
       (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (cdpReg ↦ᵣ env.callDataPtr) ** (lenReg ↦ᵣ env.callDataLen) **
       (flagReg ↦ᵣ calldataload_oobFlagW (offsetWord.getLimbN 0)
         (offsetWord.getLimbN 1) (offsetWord.getLimbN 2)
         (offsetWord.getLimbN 3) env.callDataLen) **
       (tmpReg ↦ᵣ calldataload_oobBit (offsetWord.getLimbN 0)
         env.callDataLen) **
       ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ env.callDataPtr) **
       ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ env.callDataLen) **
       calldataRegionIs env.callDataPtr data)
      (pcFree_sepConj (by pcFree)
        (pcFree_sepConj (by pcFree)
          (pcFree_sepConj (by pcFree)
            (pcFree_sepConj (by pcFree)
              (pcFree_sepConj (by pcFree)
                (pcFree_sepConj (by pcFree)
                  (pcFree_sepConj (by pcFree)
                    (pcFree_sepConj (by pcFree)
                      (pcFree_sepConj (by pcFree)
                        (pcFree_sepConj (by pcFree)
                          (pcFree_sepConj (by pcFree)
                            (pcFree_sepConj (by pcFree)
                              (calldataRegionIs_pcFree
                                env.callDataPtr data))))))))))))) h_zarm
    refine cpsTripleWithin_mono_nSteps (by decide)
      (cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) h_zarmf)
    · rw [calldataloadDispatchShape_unfold] at hp
      xperm_hyp hp
    · rw [calldataloadMergedPost_unfold, h_out0]
      simp only [EvmWord.getLimbN_zero]
      refine calldataload_shed_scratch envBaseReg offReg byteReg accReg
        addrReg cdpReg lenReg flagReg tmpReg sp envAddr
        (0 : Word) (0 : Word) (0 : Word) (0 : Word) env data
        offOld addrOld byteOld accOld
        env.callDataPtr env.callDataLen
        (calldataload_oobFlagW (offsetWord.getLimbN 0)
          (offsetWord.getLimbN 1) (offsetWord.getLimbN 2)
          (offsetWord.getLimbN 3) env.callDataLen)
        (calldataload_oobBit (offsetWord.getLimbN 0) env.callDataLen)
        _ ?_
      xperm_hyp hq
  have h_zero := cpsTripleWithin_of_pure_imp h_zero_inner
  -- Merge: realign the fact atoms of the framed branch posts onto the
  -- arms' `P ** ⌜fact⌝` shape and combine.
  have h_merged := cpsBranchWithin_merge_same_cr h_brf
    (cpsTripleWithin_weaken (fun _ hp => by
        rw [calldataloadDispatchShape_unfold]
        xperm_hyp hp)
      (fun _ hq => hq) h_zero)
    (cpsTripleWithin_weaken (fun _ hp => by
        rw [calldataloadDispatchShape_unfold]
        xperm_hyp hp)
      (fun _ hq => hq) h_win)
  exact cpsTripleWithin_weaken (fun _ hp => by
      rw [calldataloadDispatchShape_unfold] at hp
      xperm_hyp hp)
    (fun _ hq => hq) h_merged

/-! ## The public stack spec -/

/-- **The public CALLDATALOAD stack spec** (`0x35`), over the full
    bounds-checked program `evm_calldataload` (entry `base`, common exit
    `base + 444`): pops the 256-bit offset and pushes
    `callDataLoadWord data offsetWord.toNat` in place (SP unchanged —
    pop 1 / push 1), with the calldata bytes modeled by
    `calldataRegionIs env.callDataPtr data` (the 32-byte zero pad covers
    windows that straddle the calldata end) and the env block framed
    through `envIs`.

    Covers EVERY offset: in-bounds (including the straddle), low-limb
    out-of-bounds (`offset_lo ≥ len`), and upper-limb offsets ≥ 2^64 —
    the out-of-bounds arms yield the zero word, matching the pure
    semantics.  The only non-register hypotheses are the static
    resource-shape facts `h_len` and `h_wf` — there is no
    operand-domain restriction.  This is the CALLDATALOAD `.proven`
    registry witness. -/
theorem evm_calldataload_stack_spec_within
    (envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg)
    (h_off_ne_x0 : offReg ≠ .x0) (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_cdp_ne_x0 : cdpReg ≠ .x0) (h_len_ne_x0 : lenReg ≠ .x0)
    (h_flag_ne_x0 : flagReg ≠ .x0) (h_tmp_ne_x0 : tmpReg ≠ .x0)
    (sp base envAddr offOld addrOld byteOld accOld cdpOld lenOld flagOld
      tmpOld : Word)
    (env : EvmEnv) (offsetWord : EvmWord) (rest : List EvmWord)
    (data : List (BitVec 8))
    (h_len : data.length = env.callDataLen.toNat)
    (h_wf : CalldataRegionWf env.callDataPtr data) :
    cpsTripleWithin 107 base (base + 444)
      (evm_calldataload_code envBaseReg offReg byteReg accReg addrReg
        cdpReg lenReg flagReg tmpReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       (offReg ↦ᵣ offOld) ** (addrReg ↦ᵣ addrOld) ** (byteReg ↦ᵣ byteOld) **
       (accReg ↦ᵣ accOld) ** (cdpReg ↦ᵣ cdpOld) ** (lenReg ↦ᵣ lenOld) **
       (flagReg ↦ᵣ flagOld) ** (tmpReg ↦ᵣ tmpOld) **
       evmStackIs sp (offsetWord :: rest) **
       envIs envAddr env **
       calldataRegionIs env.callDataPtr data)
      (((.x12 : Reg) ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn offReg ** regOwn addrReg ** regOwn byteReg **
       regOwn accReg ** regOwn cdpReg ** regOwn lenReg **
       regOwn flagReg ** regOwn tmpReg **
       evmStackIs sp (callDataLoadWord data offsetWord.toNat :: rest) **
       envIs envAddr env **
       calldataRegionIs env.callDataPtr data) := by
  have h_merged := calldataload_merged_spec_within envBaseReg offReg
    byteReg accReg addrReg cdpReg lenReg flagReg tmpReg
    h_off_ne_x0 h_addr_ne_x0 h_byte_ne_x0 h_acc_ne_x0
    h_cdp_ne_x0 h_len_ne_x0 h_flag_ne_x0 h_tmp_ne_x0
    sp base envAddr offOld addrOld byteOld accOld cdpOld lenOld flagOld
    tmpOld env offsetWord data h_len h_wf
  have h_framed := cpsTripleWithin_frameR
    (evmStackIs (sp + 32) rest ** envIsCallDataPtrLenRest envAddr env)
    (pcFree_sepConj pcFree_evmStackIs (by
      unfold envIsCallDataPtrLenRest
      pcFree)) h_merged
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) h_framed
  · rw [evmStackIs_cons, envIs_callDataPtrLen_split envAddr env] at hp
    rw [calldataloadDispatchShape_unfold]
    dsimp only [evmWordIs] at hp
    xperm_hyp hp
  · rw [calldataloadMergedPost_unfold] at hq
    rw [evmStackIs_cons, envIs_callDataPtrLen_split envAddr env]
    dsimp only [evmWordIs]
    xperm_hyp hq

end Calldata
end EvmAsm.Evm64
