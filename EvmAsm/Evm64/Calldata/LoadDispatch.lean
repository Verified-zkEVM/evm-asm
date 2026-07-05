/-
  EvmAsm.Evm64.Calldata.LoadDispatch

  Dispatch branch spec for the full bounds-checked CALLDATALOAD program
  (GH #104): the 11 straight-line instructions of
  `evm_calldataload_dispatch` compute the out-of-bounds flag
  (OR-reduced upper offset limbs, OR'd with the `off_lo ≥u len` bit),
  and the trailing `BNE` turns it into a two-exit `cpsBranchWithin`:

    taken   (flag ≠ 0, out of bounds)  → `base + 428` (the zero arm)
    ntaken  (flag = 0, in bounds)      → `base + 48`  (the window arm)

  The pure flag value is `calldataload_oobFlagW` /
  `calldataload_oobFlag`, whose zero test decomposes
  (`calldataload_oobFlag_eq_zero_iff`) into exactly the hypothesis pair
  consumed by the Slice-1 out-of-bounds corollaries in
  `LoadWindowWord.lean` (`h_upper : l1 ||| l2 ||| l3 = 0` and the
  BitVec `<` bound on the low limb).

  The stack/`envIs` lift is deferred to the arm-merge slice
  (`LoadSpec.lean`), which composes this branch with the window and
  zero arms before lifting the merged triple to the public form.
-/

import EvmAsm.Evm64.Calldata.LoadFullProgram
import EvmAsm.Evm64.Calldata.LoadWindowWord
import EvmAsm.Evm64.Calldata.CopySpec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace Calldata

open EvmAsm.Rv64
open EvmAsm.Evm64.EvmEnv (callDataPtrOff callDataLenOff)

/-! ## The pure out-of-bounds flag -/

/-- The `SLTU`+`SLTIU` (seqz) bound bit: `1` when the low offset limb is
    at or past the calldata length, `0` when strictly below it. -/
def calldataload_oobBit (l0 len : Word) : Word :=
  if BitVec.ult l0 len then 0 else 1

/-- Raw-word form of the CALLDATALOAD out-of-bounds dispatch flag: the
    OR of the three upper offset limbs and the bound bit.  This is the
    exact value `flagReg` holds when the dispatch `BNE` executes. -/
def calldataload_oobFlagW (l0 l1 l2 l3 len : Word) : Word :=
  l1 ||| l2 ||| l3 ||| calldataload_oobBit l0 len

/-- `EvmWord`-level out-of-bounds dispatch flag, at the limbs of the
    popped 256-bit offset word. -/
def calldataload_oobFlag (offsetWord : EvmWord) (len : Word) : Word :=
  calldataload_oobFlagW (offsetWord.getLimbN 0) (offsetWord.getLimbN 1)
    (offsetWord.getLimbN 2) (offsetWord.getLimbN 3) len

/-- The `SLTIU tmp tmp 1` (seqz) output over the `SLTU` output folds to
    `calldataload_oobBit`. -/
theorem calldataload_sltiu_seqz_eq (l0 len : Word) :
    (if BitVec.ult (if BitVec.ult l0 len then (1 : Word) else 0)
        (signExtend12 (1 : BitVec 12)) then (1 : Word) else (0 : Word)) =
      calldataload_oobBit l0 len := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
  unfold calldataload_oobBit
  by_cases h : BitVec.ult l0 len <;> simp [h]

/-- The bound bit is zero exactly when the low limb is strictly below
    the calldata length. -/
theorem calldataload_oobBit_eq_zero_iff {l0 len : Word} :
    calldataload_oobBit l0 len = 0 ↔ l0 < len := by
  unfold calldataload_oobBit
  by_cases h : BitVec.ult l0 len
  · simp only [h, if_true]
    simpa [BitVec.ult] using h
  · simp only [h]
    constructor
    · intro h_eq; exact absurd h_eq (by decide)
    · intro h_lt
      exact absurd (by simpa [BitVec.ult] using h_lt) h

/-- The raw dispatch flag is zero exactly when all upper offset limbs
    are zero AND the low limb is strictly below the calldata length —
    the hypothesis pair the Slice-1 OOB corollaries key on. -/
theorem calldataload_oobFlagW_eq_zero_iff {l0 l1 l2 l3 len : Word} :
    calldataload_oobFlagW l0 l1 l2 l3 len = 0 ↔
      (l1 ||| l2 ||| l3 = 0 ∧ l0 < len) := by
  unfold calldataload_oobFlagW
  constructor
  · intro h
    obtain ⟨h_upper, h_bit⟩ := BitVec.or_eq_zero_iff.mp h
    exact ⟨h_upper, calldataload_oobBit_eq_zero_iff.mp h_bit⟩
  · intro ⟨h_upper, h_lt⟩
    exact BitVec.or_eq_zero_iff.mpr
      ⟨h_upper, calldataload_oobBit_eq_zero_iff.mpr h_lt⟩

/-- `EvmWord`-level zero test of the dispatch flag. -/
theorem calldataload_oobFlag_eq_zero_iff {offsetWord : EvmWord} {len : Word} :
    calldataload_oobFlag offsetWord len = 0 ↔
      (offsetWord.getLimbN 1 ||| offsetWord.getLimbN 2 |||
          offsetWord.getLimbN 3 = 0 ∧
        offsetWord.getLimbN 0 < len) :=
  calldataload_oobFlagW_eq_zero_iff

/-! ## The straight-line dispatch block -/

/-- Raw spec of the 11 straight-line dispatch instructions
    (`base → base + 44`, everything before the `BNE`): load
    `callDataPtr`/`callDataLen` from the env block, OR-reduce the three
    upper offset limbs from the stack slot, and fold in the
    `off_lo ≥u len` bound bit, leaving the out-of-bounds flag in
    `flagReg`.  All memory cells are read-only. -/
theorem calldataload_dispatch_block_spec_within
    (envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg)
    (h_cdp_ne_x0 : cdpReg ≠ .x0)
    (h_len_ne_x0 : lenReg ≠ .x0)
    (h_flag_ne_x0 : flagReg ≠ .x0)
    (h_tmp_ne_x0 : tmpReg ≠ .x0)
    (sp base envAddr cdpOld lenOld flagOld tmpOld : Word)
    (l0 l1 l2 l3 callDataPtr callDataLen : Word) :
    let code := evm_calldataload_code envBaseReg offReg byteReg accReg
      addrReg cdpReg lenReg flagReg tmpReg base
    cpsTripleWithin 11 base (base + 44) code
      ((.x12 ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) **
       (cdpReg ↦ᵣ cdpOld) ** (lenReg ↦ᵣ lenOld) **
       (flagReg ↦ᵣ flagOld) ** (tmpReg ↦ᵣ tmpOld) **
       (sp ↦ₘ l0) ** ((sp + 8) ↦ₘ l1) **
       ((sp + 16) ↦ₘ l2) ** ((sp + 24) ↦ₘ l3) **
       ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ callDataPtr) **
       ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ callDataLen))
      ((.x12 ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) **
       (cdpReg ↦ᵣ callDataPtr) ** (lenReg ↦ᵣ callDataLen) **
       (flagReg ↦ᵣ calldataload_oobFlagW l0 l1 l2 l3 callDataLen) **
       (tmpReg ↦ᵣ calldataload_oobBit l0 callDataLen) **
       (sp ↦ₘ l0) ** ((sp + 8) ↦ₘ l1) **
       ((sp + 16) ↦ₘ l2) ** ((sp + 24) ↦ₘ l3) **
       ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ callDataPtr) **
       ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ callDataLen)) := by
  intro code
  -- Per-instruction specs, at their concrete addresses.
  have h0 := ld_spec_gen_within cdpReg envBaseReg envAddr cdpOld
    callDataPtr (BitVec.ofNat 12 callDataPtrOff) base h_cdp_ne_x0
  simp only [signExtend12_callDataPtrOff] at h0
  have h1 := ld_spec_gen_within lenReg envBaseReg envAddr lenOld
    callDataLen (BitVec.ofNat 12 callDataLenOff) (base + 4) h_len_ne_x0
  simp only [signExtend12_callDataLenOff] at h1
  have h2 := ld_spec_gen_within flagReg .x12 sp flagOld l1
    (8 : BitVec 12) (base + 8) h_flag_ne_x0
  simp only [signExtend12_8] at h2
  have h3 := ld_spec_gen_within tmpReg .x12 sp tmpOld l2
    (16 : BitVec 12) (base + 12) h_tmp_ne_x0
  simp only [signExtend12_16] at h3
  have h4 := or_spec_gen_rd_eq_rs1_within flagReg tmpReg l1 l2
    (base + 16) h_flag_ne_x0
  have h5 := ld_spec_gen_within tmpReg .x12 sp l2 l3
    (24 : BitVec 12) (base + 20) h_tmp_ne_x0
  simp only [signExtend12_24] at h5
  have h6 := or_spec_gen_rd_eq_rs1_within flagReg tmpReg (l1 ||| l2) l3
    (base + 24) h_flag_ne_x0
  have h7 := ld_spec_gen_within tmpReg .x12 sp l3 l0
    (0 : BitVec 12) (base + 28) h_tmp_ne_x0
  simp only [signExtend12_0] at h7
  have h8 := sltu_spec_gen_rd_eq_rs1_within tmpReg lenReg l0 callDataLen
    (base + 32) h_tmp_ne_x0
  have h9 := sltiu_spec_gen_same_within tmpReg
    (if BitVec.ult l0 callDataLen then (1 : Word) else 0)
    (1 : BitVec 12) (base + 36) h_tmp_ne_x0
  rw [calldataload_sltiu_seqz_eq l0 callDataLen] at h9
  have h10 := or_spec_gen_rd_eq_rs1_within flagReg tmpReg
    ((l1 ||| l2) ||| l3) (calldataload_oobBit l0 callDataLen)
    (base + 40) h_flag_ne_x0
  -- The 11-instruction prefix as its own code requirement, then extend
  -- into the full program via the prefix slice.
  refine cpsTripleWithin_extend_code
    (cr := CodeReq.ofProg base
      [.LD cdpReg envBaseReg (BitVec.ofNat 12 callDataPtrOff),
       .LD lenReg envBaseReg (BitVec.ofNat 12 callDataLenOff),
       .LD flagReg .x12 8,
       .LD tmpReg .x12 16,
       .OR flagReg flagReg tmpReg,
       .LD tmpReg .x12 24,
       .OR flagReg flagReg tmpReg,
       .LD tmpReg .x12 0,
       .SLTU tmpReg tmpReg lenReg,
       .SLTIU tmpReg tmpReg 1,
       .OR flagReg flagReg tmpReg])
    (hmono := fun a i h => CodeReq.ofProg_mono_sub base base
      (evm_calldataload envBaseReg offReg byteReg accReg addrReg cdpReg
        lenReg flagReg tmpReg)
      _ 0
      (by simp)
      (by unfold evm_calldataload evm_calldataload_dispatch; rfl)
      (by rw [evm_calldataload_length]; simp)
      (by rw [evm_calldataload_length]; omega) a i h)
    ?_
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  rw [show (base + 4 : Word) + 4 = base + 8 by bv_addr]
  rw [show (base + 8 : Word) + 4 = base + 12 by bv_addr]
  rw [show (base + 12 : Word) + 4 = base + 16 by bv_addr]
  rw [show (base + 16 : Word) + 4 = base + 20 by bv_addr]
  rw [show (base + 20 : Word) + 4 = base + 24 by bv_addr]
  rw [show (base + 24 : Word) + 4 = base + 28 by bv_addr]
  rw [show (base + 28 : Word) + 4 = base + 32 by bv_addr]
  rw [show (base + 32 : Word) + 4 = base + 36 by bv_addr]
  rw [show (base + 36 : Word) + 4 = base + 40 by bv_addr]
  show cpsTripleWithin 11 base (base + 44) _ _
    ((.x12 ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) **
     (cdpReg ↦ᵣ callDataPtr) ** (lenReg ↦ᵣ callDataLen) **
     (flagReg ↦ᵣ ((l1 ||| l2) ||| l3 |||
        calldataload_oobBit l0 callDataLen)) **
     (tmpReg ↦ᵣ calldataload_oobBit l0 callDataLen) **
     (sp ↦ₘ l0) ** ((sp + 8) ↦ₘ l1) **
     ((sp + 16) ↦ₘ l2) ** ((sp + 24) ↦ₘ l3) **
     ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ callDataPtr) **
     ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ callDataLen))
  runBlock h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

/-! ## The dispatch branch -/

theorem calldataload_bne_taken_addr {base : Word} :
    (base + 44 : Word) + signExtend13 (BitVec.ofNat 13 384) = base + 428 := by
  rw [show signExtend13 (BitVec.ofNat 13 384) = (384 : Word) from by decide]
  bv_omega

/-- Dispatch block ;; BNE over the full CALLDATALOAD code (12 steps,
    `base` → branch): if the out-of-bounds flag is nonzero branch to the
    zero arm at `base + 428`; else fall through to the window arm at
    `base + 48`.  Both exits carry the corresponding pure fact about
    `calldataload_oobFlagW`, which `calldataload_oobFlagW_eq_zero_iff`
    decomposes for the arm proofs. -/
theorem calldataload_dispatch_branch_spec_within
    (envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg)
    (h_cdp_ne_x0 : cdpReg ≠ .x0)
    (h_len_ne_x0 : lenReg ≠ .x0)
    (h_flag_ne_x0 : flagReg ≠ .x0)
    (h_tmp_ne_x0 : tmpReg ≠ .x0)
    (sp base envAddr cdpOld lenOld flagOld tmpOld : Word)
    (l0 l1 l2 l3 callDataPtr callDataLen : Word) :
    cpsBranchWithin 12 base
      (evm_calldataload_code envBaseReg offReg byteReg accReg addrReg
        cdpReg lenReg flagReg tmpReg base)
      ((.x12 ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) **
       (cdpReg ↦ᵣ cdpOld) ** (lenReg ↦ᵣ lenOld) **
       (flagReg ↦ᵣ flagOld) ** (tmpReg ↦ᵣ tmpOld) **
       (sp ↦ₘ l0) ** ((sp + 8) ↦ₘ l1) **
       ((sp + 16) ↦ₘ l2) ** ((sp + 24) ↦ₘ l3) **
       ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ callDataPtr) **
       ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ callDataLen))
      (base + 428)
        ((.x12 ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) **
         (cdpReg ↦ᵣ callDataPtr) ** (lenReg ↦ᵣ callDataLen) **
         (flagReg ↦ᵣ calldataload_oobFlagW l0 l1 l2 l3 callDataLen) **
         (tmpReg ↦ᵣ calldataload_oobBit l0 callDataLen) **
         (sp ↦ₘ l0) ** ((sp + 8) ↦ₘ l1) **
         ((sp + 16) ↦ₘ l2) ** ((sp + 24) ↦ₘ l3) **
         ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ callDataPtr) **
         ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ callDataLen) **
         ⌜calldataload_oobFlagW l0 l1 l2 l3 callDataLen ≠ (0 : Word)⌝)
      (base + 48)
        ((.x12 ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) **
         (cdpReg ↦ᵣ callDataPtr) ** (lenReg ↦ᵣ callDataLen) **
         (flagReg ↦ᵣ calldataload_oobFlagW l0 l1 l2 l3 callDataLen) **
         (tmpReg ↦ᵣ calldataload_oobBit l0 callDataLen) **
         (sp ↦ₘ l0) ** ((sp + 8) ↦ₘ l1) **
         ((sp + 16) ↦ₘ l2) ** ((sp + 24) ↦ₘ l3) **
         ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ callDataPtr) **
         ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ callDataLen) **
         ⌜calldataload_oobFlagW l0 l1 l2 l3 callDataLen = (0 : Word)⌝) := by
  -- The straight-line block, framed with x0 (untouched before the BNE).
  have hblk := calldataload_dispatch_block_spec_within envBaseReg offReg
    byteReg accReg addrReg cdpReg lenReg flagReg tmpReg
    h_cdp_ne_x0 h_len_ne_x0 h_flag_ne_x0 h_tmp_ne_x0
    sp base envAddr cdpOld lenOld flagOld tmpOld
    l0 l1 l2 l3 callDataPtr callDataLen
  have hblkf := cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word))) (by pcFree) hblk
  -- The BNE at base + 44, extended into the full code and framed with
  -- everything the branch does not touch.
  have hbne := bne_spec_gen_within flagReg .x0 (BitVec.ofNat 13 384)
    (calldataload_oobFlagW l0 l1 l2 l3 callDataLen) (0 : Word) (base + 44)
  rw [calldataload_bne_taken_addr,
    show (base + 44 : Word) + 4 = base + 48 from by bv_omega] at hbne
  have hbnee := cpsBranchWithin_extend_code (hmono := by
    intro a i h
    exact CodeReq.singleton_mono
      (evm_calldataload_lookup_bne envBaseReg offReg byteReg accReg
        addrReg cdpReg lenReg flagReg tmpReg base) a i h) hbne
  have hbnef := cpsBranchWithin_frameR
    ((.x12 ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) **
     (cdpReg ↦ᵣ callDataPtr) ** (lenReg ↦ᵣ callDataLen) **
     (tmpReg ↦ᵣ calldataload_oobBit l0 callDataLen) **
     (sp ↦ₘ l0) ** ((sp + 8) ↦ₘ l1) **
     ((sp + 16) ↦ₘ l2) ** ((sp + 24) ↦ₘ l3) **
     ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ callDataPtr) **
     ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ callDataLen))
    (by pcFree) hbnee
  -- Align the block postcondition to the framed BNE precondition, seq,
  -- and restore the public atom order on all three assertions.
  have hblkf' := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by xperm_hyp hq)
    (Q' := ((flagReg ↦ᵣ calldataload_oobFlagW l0 l1 l2 l3 callDataLen) **
        (.x0 ↦ᵣ (0 : Word))) **
      ((.x12 ↦ᵣ sp) ** (envBaseReg ↦ᵣ envAddr) **
       (cdpReg ↦ᵣ callDataPtr) ** (lenReg ↦ᵣ callDataLen) **
       (tmpReg ↦ᵣ calldataload_oobBit l0 callDataLen) **
       (sp ↦ₘ l0) ** ((sp + 8) ↦ₘ l1) **
       ((sp + 16) ↦ₘ l2) ** ((sp + 24) ↦ₘ l3) **
       ((envAddr + BitVec.ofNat 64 callDataPtrOff) ↦ₘ callDataPtr) **
       ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ callDataLen)))
    hblkf
  have hbr := cpsTripleWithin_seq_cpsBranchWithin_same_cr hblkf' hbnef
  refine cpsBranchWithin_weaken ?_ ?_ ?_ hbr
  · intro h hp; xperm_hyp hp
  · intro h hq; xperm_hyp hq
  · intro h hq; xperm_hyp hq

end Calldata
end EvmAsm.Evm64
