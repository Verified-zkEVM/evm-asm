/-
  EvmAsm.Evm64.Calldata.LoadWindowArm

  The window arm of the bounds-checked CALLDATALOAD program (GH #104):
  entry `base + calldataloadWindowOff` (the dispatch fall-through), exit
  `base + calldataloadExitOff` (via the trailing `JAL x0`), over
  `evm_calldataload_code`, with the calldata modeled by `calldataRegionIs`.

  Construction:
    * `calldataload_region_one_limb_spec_within` — one 8-byte window quarter
      read against the region: extract the backing dword pair
      (`calldataRegionIs_quarter_pair`), run the transported MLOAD one-limb
      engine (`mload_one_limb_unaligned_spec_within`) with the
      `calldataRegion_limb_window_ok` side conditions, decode the packed limb
      to `callDataByte` values, and fold the pair back into the region.
    * `arm_step_q{0..3}` — the four quarters in canonical
      `calldataloadArmMid` midpoint shape.
    * `calldataload_window_arm_core_spec_within` — prologue + four quarters
      over `evm_calldataload_window_code` (94 steps).
    * `calldataload_window_arm_spec_within` — transported into the full
      program code and sequenced with the exit `JAL` (95 steps,
      `base + 48 → base + 444`).

  The 32-byte pad of the region (`paddedCallData`) is what makes the single
  in-bounds hypothesis `offLo.toNat < data.length` sufficient: a window that
  straddles the calldata end reads zero-backed pad cells, so the packed
  output limbs are `callDataByte` (zero past the end) with no per-byte
  bounds dispatch.
-/

import EvmAsm.Evm64.Calldata.Region
import EvmAsm.Evm64.Calldata.LoadStackCode
import EvmAsm.Evm64.Calldata.LoadFullProgram
import EvmAsm.Evm64.MLoad.UnalignedSpec
import EvmAsm.Rv64.SAsm.CtrlSpecs

namespace EvmAsm.Evm64
namespace Calldata

open EvmAsm.Rv64

/-! ## Output limb values -/

/-- Big-endian packed output limb for window quarter `w`: the eight calldata
    bytes `offN + w .. offN + w + 7` (zero past the end of `data`). -/
def calldataloadOutputLimb (data : List (BitVec 8)) (offN w : Nat) : Word :=
  mloadPackedLimb
    (callDataByte data (offN + w))
    (callDataByte data (offN + w + 1))
    (callDataByte data (offN + w + 2))
    (callDataByte data (offN + w + 3))
    (callDataByte data (offN + w + 4))
    (callDataByte data (offN + w + 5))
    (callDataByte data (offN + w + 6))
    (callDataByte data (offN + w + 7))

/-- Bridge to the decoded-argument window bytes consumed by the
    `calldataLoadWindowOutputWordFromArgs` stack folds. -/
theorem calldataloadOutputLimb_eq_windowBytes
    (data : List (BitVec 8)) (args : CallDataLoadArgs.Args) (w : Nat) :
    calldataloadOutputLimb data (CallDataLoadArgs.offsetNat args) w =
      mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args w)
        (CallDataLoadArgs.windowByteFromArgs data args (w + 1))
        (CallDataLoadArgs.windowByteFromArgs data args (w + 2))
        (CallDataLoadArgs.windowByteFromArgs data args (w + 3))
        (CallDataLoadArgs.windowByteFromArgs data args (w + 4))
        (CallDataLoadArgs.windowByteFromArgs data args (w + 5))
        (CallDataLoadArgs.windowByteFromArgs data args (w + 6))
        (CallDataLoadArgs.windowByteFromArgs data args (w + 7)) := by
  simp only [calldataloadOutputLimb, CallDataLoadArgs.windowByteFromArgs,
    Nat.add_assoc]

/-- Decode the engine's packed limb over the quarter's region pair into the
    pure output limb. -/
private theorem quarter_packed_limb_eq (data : List (BitVec 8)) (offLo : Word)
    (w : Nat) (h_off : offLo.toNat < data.length)
    (h_w_mod : w % 8 = 0) (h_w_le : w ≤ 24) :
    mloadPackedLimbFromDwordPair
      (packBytes (((paddedCallData data).drop
        (8 * ((offLo.toNat + w) / 8))).take 8))
      (packBytes (((paddedCallData data).drop
        (8 * ((offLo.toNat + w) / 8) + 8)).take 8))
      (offLo.toNat % 8)
      = calldataloadOutputLimb data offLo.toNat w := by
  unfold mloadPackedLimbFromDwordPair calldataloadOutputLimb
  rw [calldataRegion_dwordPair_byte data offLo w 0 h_off h_w_mod h_w_le
        (by omega),
      calldataRegion_dwordPair_byte data offLo w 1 h_off h_w_mod h_w_le
        (by omega),
      calldataRegion_dwordPair_byte data offLo w 2 h_off h_w_mod h_w_le
        (by omega),
      calldataRegion_dwordPair_byte data offLo w 3 h_off h_w_mod h_w_le
        (by omega),
      calldataRegion_dwordPair_byte data offLo w 4 h_off h_w_mod h_w_le
        (by omega),
      calldataRegion_dwordPair_byte data offLo w 5 h_off h_w_mod h_w_le
        (by omega),
      calldataRegion_dwordPair_byte data offLo w 6 h_off h_w_mod h_w_le
        (by omega),
      calldataRegion_dwordPair_byte data offLo w 7 h_off h_w_mod h_w_le
        (by omega)]
  simp only [Nat.add_zero]

/-! ## One window quarter against the region -/

/-- One 8-byte window quarter of the CALLDATALOAD window arm, with the
    calldata modeled by `calldataRegionIs`: extract the backing dword pair,
    run the transported MLOAD one-limb engine, decode the packed bytes to
    `callDataByte`, fold the pair back. -/
theorem calldataload_region_one_limb_spec_within
    (addrReg byteReg accReg : Reg)
    (cdp offLo sp byteOld accOld dstOld : Word)
    (data : List (BitVec 8)) (w : Nat)
    (off0 off1 off2 off3 off4 off5 off6 off7 dstOff : BitVec 12) (qb : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_off : offLo.toNat < data.length)
    (h_w_mod : w % 8 = 0) (h_w_le : w ≤ 24)
    (h_window : mloadLimbWindowOk (cdp + offLo)
      (cdp + BitVec.ofNat 64 (8 * ((offLo.toNat + w) / 8)))
      (cdp + BitVec.ofNat 64 (8 * ((offLo.toNat + w) / 8) + 8))
      (offLo.toNat % 8) off0 off1 off2 off3 off4 off5 off6 off7) :
    cpsTripleWithin 23 qb (qb + 92)
      (mloadOneLimbCode addrReg byteReg accReg
        off0 off1 off2 off3 off4 off5 off6 off7 dstOff qb)
      ((addrReg ↦ᵣ (cdp + offLo)) ** (byteReg ↦ᵣ byteOld) **
       (accReg ↦ᵣ accOld) ** ((.x12 : Reg) ↦ᵣ sp) **
       ((sp + signExtend12 dstOff) ↦ₘ dstOld) **
       calldataRegionIs cdp data)
      ((addrReg ↦ᵣ (cdp + offLo)) **
       (byteReg ↦ᵣ ((callDataByte data (offLo.toNat + w + 7)).zeroExtend 64)) **
       (accReg ↦ᵣ calldataloadOutputLimb data offLo.toNat w) **
       ((.x12 : Reg) ↦ᵣ sp) **
       ((sp + signExtend12 dstOff) ↦ₘ calldataloadOutputLimb data offLo.toNat w) **
       calldataRegionIs cdp data) := by
  obtain ⟨front, rest, h_front, h_rest, heq⟩ :=
    calldataRegionIs_quarter_pair cdp offLo data w h_w_le h_off
  rw [heq]
  have eng := mload_one_limb_unaligned_spec_within addrReg byteReg accReg
    (cdp + offLo) accOld byteOld
    (packBytes (((paddedCallData data).drop
      (8 * ((offLo.toNat + w) / 8))).take 8))
    (packBytes (((paddedCallData data).drop
      (8 * ((offLo.toNat + w) / 8) + 8)).take 8))
    (cdp + BitVec.ofNat 64 (8 * ((offLo.toNat + w) / 8)))
    (cdp + BitVec.ofNat 64 (8 * ((offLo.toNat + w) / 8) + 8))
    sp dstOld off0 off1 off2 off3 off4 off5 off6 off7 dstOff
    (offLo.toNat % 8) qb h_byte_ne_x0 h_acc_ne_x0 h_window
  rw [mloadOneLimbUnalignedPre_unfold, mloadOneLimbUnalignedPost_unfold] at eng
  simp only [] at eng
  rw [calldataRegion_dwordPair_byte data offLo w 7 h_off h_w_mod h_w_le
        (by omega),
      quarter_packed_limb_eq data offLo w h_off h_w_mod h_w_le] at eng
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (front ** rest)
      (pcFree_sepConj h_front h_rest) eng)

/-! ## Canonical midpoint shape -/

/-- Canonical assertion threading the window arm: the fixed registers, the
    four output/operand stack cells, and the region as one folded atom. -/
def calldataloadArmMid
    (offReg byteReg accReg addrReg cdpReg : Reg)
    (sp cdp offLo byteVal accVal c0 c1 c2 c3 : Word)
    (data : List (BitVec 8)) : Assertion :=
  ((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offLo) ** (cdpReg ↦ᵣ cdp) **
  (addrReg ↦ᵣ (cdp + offLo)) ** (byteReg ↦ᵣ byteVal) ** (accReg ↦ᵣ accVal) **
  (sp ↦ₘ c0) ** ((sp + 8) ↦ₘ c1) ** ((sp + 16) ↦ₘ c2) ** ((sp + 24) ↦ₘ c3) **
  calldataRegionIs cdp data

theorem calldataloadArmMid_unfold
    {offReg byteReg accReg addrReg cdpReg : Reg}
    {sp cdp offLo byteVal accVal c0 c1 c2 c3 : Word}
    {data : List (BitVec 8)} :
    calldataloadArmMid offReg byteReg accReg addrReg cdpReg
        sp cdp offLo byteVal accVal c0 c1 c2 c3 data =
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offLo) ** (cdpReg ↦ᵣ cdp) **
       (addrReg ↦ᵣ (cdp + offLo)) ** (byteReg ↦ᵣ byteVal) **
       (accReg ↦ᵣ accVal) **
       (sp ↦ₘ c0) ** ((sp + 8) ↦ₘ c1) ** ((sp + 16) ↦ₘ c2) **
       ((sp + 24) ↦ₘ c3) **
       calldataRegionIs cdp data) := rfl

private theorem calldataloadArmMid_pcFree
    (offReg byteReg accReg addrReg cdpReg : Reg)
    (sp cdp offLo byteVal accVal c0 c1 c2 c3 : Word)
    (data : List (BitVec 8)) :
    (calldataloadArmMid offReg byteReg accReg addrReg cdpReg
      sp cdp offLo byteVal accVal c0 c1 c2 c3 data).pcFree := by
  rw [calldataloadArmMid_unfold]
  refine pcFree_sepConj (by pcFree) ?_
  refine pcFree_sepConj (by pcFree) ?_
  refine pcFree_sepConj (by pcFree) ?_
  refine pcFree_sepConj (by pcFree) ?_
  refine pcFree_sepConj (by pcFree) ?_
  refine pcFree_sepConj (by pcFree) ?_
  refine pcFree_sepConj (by pcFree) ?_
  refine pcFree_sepConj (by pcFree) ?_
  refine pcFree_sepConj (by pcFree) ?_
  exact pcFree_sepConj (by pcFree) (calldataRegionIs_pcFree cdp data)

/-! ## The four quarters in midpoint shape -/

section ArmSteps

variable (offReg byteReg accReg addrReg cdpReg : Reg)
variable (sp cdp offLo byteOld accOld l1 l2 l3 : Word)
variable (data : List (BitVec 8)) (wbase : Word)

/-- Window quarter 0 (`w = 24`, immediates `24..31`, output cell `sp`). -/
private theorem arm_step_q0
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_wf : CalldataRegionWf cdp data)
    (h_off : offLo.toNat < data.length) :
    cpsTripleWithin 23 (wbase + 8) (wbase + 100)
      (mloadOneLimbCode addrReg byteReg accReg
        24 25 26 27 28 29 30 31 0 (wbase + 8))
      (calldataloadArmMid offReg byteReg accReg addrReg cdpReg
        sp cdp offLo byteOld accOld offLo l1 l2 l3 data)
      (calldataloadArmMid offReg byteReg accReg addrReg cdpReg
        sp cdp offLo
        ((callDataByte data (offLo.toNat + 24 + 7)).zeroExtend 64)
        (calldataloadOutputLimb data offLo.toNat 24)
        (calldataloadOutputLimb data offLo.toNat 24) l1 l2 l3 data) := by
  have h_core := calldataload_region_one_limb_spec_within addrReg byteReg accReg
    cdp offLo sp byteOld accOld offLo data 24
    24 25 26 27 28 29 30 31 0 (wbase + 8)
    h_byte_ne_x0 h_acc_ne_x0 h_off (by decide) (by decide)
    (calldataRegion_limb_window_ok_q0 cdp offLo data h_wf h_off)
  rw [show (wbase + 8) + 92 = wbase + 100 from by bv_omega,
      show sp + signExtend12 (0 : BitVec 12) = sp from by
        rw [signExtend12_0]; bv_omega] at h_core
  rw [calldataloadArmMid_unfold, calldataloadArmMid_unfold]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR
      ((offReg ↦ᵣ offLo) ** (cdpReg ↦ᵣ cdp) **
       ((sp + 8) ↦ₘ l1) ** ((sp + 16) ↦ₘ l2) ** ((sp + 24) ↦ₘ l3))
      (by pcFree) h_core)

/-- Window quarter 1 (`w = 16`, immediates `16..23`, output cell `sp + 8`). -/
private theorem arm_step_q1
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_wf : CalldataRegionWf cdp data)
    (h_off : offLo.toNat < data.length) :
    cpsTripleWithin 23 (wbase + 100) (wbase + 192)
      (mloadOneLimbCode addrReg byteReg accReg
        16 17 18 19 20 21 22 23 8 (wbase + 100))
      (calldataloadArmMid offReg byteReg accReg addrReg cdpReg
        sp cdp offLo
        ((callDataByte data (offLo.toNat + 24 + 7)).zeroExtend 64)
        (calldataloadOutputLimb data offLo.toNat 24)
        (calldataloadOutputLimb data offLo.toNat 24) l1 l2 l3 data)
      (calldataloadArmMid offReg byteReg accReg addrReg cdpReg
        sp cdp offLo
        ((callDataByte data (offLo.toNat + 16 + 7)).zeroExtend 64)
        (calldataloadOutputLimb data offLo.toNat 16)
        (calldataloadOutputLimb data offLo.toNat 24)
        (calldataloadOutputLimb data offLo.toNat 16) l2 l3 data) := by
  have h_core := calldataload_region_one_limb_spec_within addrReg byteReg accReg
    cdp offLo sp
    ((callDataByte data (offLo.toNat + 24 + 7)).zeroExtend 64)
    (calldataloadOutputLimb data offLo.toNat 24) l1 data 16
    16 17 18 19 20 21 22 23 8 (wbase + 100)
    h_byte_ne_x0 h_acc_ne_x0 h_off (by decide) (by decide)
    (calldataRegion_limb_window_ok_q1 cdp offLo data h_wf h_off)
  rw [show (wbase + 100) + 92 = wbase + 192 from by bv_omega,
      show sp + signExtend12 (8 : BitVec 12) = sp + 8 from by
        rw [signExtend12_8]] at h_core
  rw [calldataloadArmMid_unfold, calldataloadArmMid_unfold]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR
      ((offReg ↦ᵣ offLo) ** (cdpReg ↦ᵣ cdp) **
       (sp ↦ₘ calldataloadOutputLimb data offLo.toNat 24) **
       ((sp + 16) ↦ₘ l2) ** ((sp + 24) ↦ₘ l3))
      (by pcFree) h_core)

/-- Window quarter 2 (`w = 8`, immediates `8..15`, output cell `sp + 16`). -/
private theorem arm_step_q2
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_wf : CalldataRegionWf cdp data)
    (h_off : offLo.toNat < data.length) :
    cpsTripleWithin 23 (wbase + 192) (wbase + 284)
      (mloadOneLimbCode addrReg byteReg accReg
        8 9 10 11 12 13 14 15 16 (wbase + 192))
      (calldataloadArmMid offReg byteReg accReg addrReg cdpReg
        sp cdp offLo
        ((callDataByte data (offLo.toNat + 16 + 7)).zeroExtend 64)
        (calldataloadOutputLimb data offLo.toNat 16)
        (calldataloadOutputLimb data offLo.toNat 24)
        (calldataloadOutputLimb data offLo.toNat 16) l2 l3 data)
      (calldataloadArmMid offReg byteReg accReg addrReg cdpReg
        sp cdp offLo
        ((callDataByte data (offLo.toNat + 8 + 7)).zeroExtend 64)
        (calldataloadOutputLimb data offLo.toNat 8)
        (calldataloadOutputLimb data offLo.toNat 24)
        (calldataloadOutputLimb data offLo.toNat 16)
        (calldataloadOutputLimb data offLo.toNat 8) l3 data) := by
  have h_core := calldataload_region_one_limb_spec_within addrReg byteReg accReg
    cdp offLo sp
    ((callDataByte data (offLo.toNat + 16 + 7)).zeroExtend 64)
    (calldataloadOutputLimb data offLo.toNat 16) l2 data 8
    8 9 10 11 12 13 14 15 16 (wbase + 192)
    h_byte_ne_x0 h_acc_ne_x0 h_off (by decide) (by decide)
    (calldataRegion_limb_window_ok_q2 cdp offLo data h_wf h_off)
  rw [show (wbase + 192) + 92 = wbase + 284 from by bv_omega,
      show sp + signExtend12 (16 : BitVec 12) = sp + 16 from by
        rw [signExtend12_16]] at h_core
  rw [calldataloadArmMid_unfold, calldataloadArmMid_unfold]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR
      ((offReg ↦ᵣ offLo) ** (cdpReg ↦ᵣ cdp) **
       (sp ↦ₘ calldataloadOutputLimb data offLo.toNat 24) **
       ((sp + 8) ↦ₘ calldataloadOutputLimb data offLo.toNat 16) **
       ((sp + 24) ↦ₘ l3))
      (by pcFree) h_core)

/-- Window quarter 3 (`w = 0`, immediates `0..7`, output cell `sp + 24`). -/
private theorem arm_step_q3
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_wf : CalldataRegionWf cdp data)
    (h_off : offLo.toNat < data.length) :
    cpsTripleWithin 23 (wbase + 284) (wbase + 376)
      (mloadOneLimbCode addrReg byteReg accReg
        0 1 2 3 4 5 6 7 24 (wbase + 284))
      (calldataloadArmMid offReg byteReg accReg addrReg cdpReg
        sp cdp offLo
        ((callDataByte data (offLo.toNat + 8 + 7)).zeroExtend 64)
        (calldataloadOutputLimb data offLo.toNat 8)
        (calldataloadOutputLimb data offLo.toNat 24)
        (calldataloadOutputLimb data offLo.toNat 16)
        (calldataloadOutputLimb data offLo.toNat 8) l3 data)
      (calldataloadArmMid offReg byteReg accReg addrReg cdpReg
        sp cdp offLo
        ((callDataByte data (offLo.toNat + 0 + 7)).zeroExtend 64)
        (calldataloadOutputLimb data offLo.toNat 0)
        (calldataloadOutputLimb data offLo.toNat 24)
        (calldataloadOutputLimb data offLo.toNat 16)
        (calldataloadOutputLimb data offLo.toNat 8)
        (calldataloadOutputLimb data offLo.toNat 0) data) := by
  have h_core := calldataload_region_one_limb_spec_within addrReg byteReg accReg
    cdp offLo sp
    ((callDataByte data (offLo.toNat + 8 + 7)).zeroExtend 64)
    (calldataloadOutputLimb data offLo.toNat 8) l3 data 0
    0 1 2 3 4 5 6 7 24 (wbase + 284)
    h_byte_ne_x0 h_acc_ne_x0 h_off (by decide) (by decide)
    (calldataRegion_limb_window_ok_q3 cdp offLo data h_wf h_off)
  rw [show (wbase + 284) + 92 = wbase + 376 from by bv_omega,
      show sp + signExtend12 (24 : BitVec 12) = sp + 24 from by
        rw [signExtend12_24]] at h_core
  rw [calldataloadArmMid_unfold, calldataloadArmMid_unfold]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR
      ((offReg ↦ᵣ offLo) ** (cdpReg ↦ᵣ cdp) **
       (sp ↦ₘ calldataloadOutputLimb data offLo.toNat 24) **
       ((sp + 8) ↦ₘ calldataloadOutputLimb data offLo.toNat 16) **
       ((sp + 16) ↦ₘ calldataloadOutputLimb data offLo.toNat 8))
      (by pcFree) h_core)

end ArmSteps

/-! ## Window arm over the window code -/

/-- Precondition of the window arm at the dispatch fall-through: the window
    scratch registers at arbitrary old values, the operand stack cells, and
    the calldata region.  `offLo` is the offset low limb the dispatch left in
    the `sp` cell; the upper limbs `l1 l2 l3` sit untouched in the higher
    cells. -/
def calldataloadWindowArmPre
    (offReg byteReg accReg addrReg cdpReg : Reg)
    (sp cdp offLo offOld addrOld byteOld accOld l1 l2 l3 : Word)
    (data : List (BitVec 8)) : Assertion :=
  ((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) ** (cdpReg ↦ᵣ cdp) **
  (addrReg ↦ᵣ addrOld) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
  (sp ↦ₘ offLo) ** ((sp + 8) ↦ₘ l1) ** ((sp + 16) ↦ₘ l2) **
  ((sp + 24) ↦ₘ l3) **
  calldataRegionIs cdp data

theorem calldataloadWindowArmPre_unfold
    {offReg byteReg accReg addrReg cdpReg : Reg}
    {sp cdp offLo offOld addrOld byteOld accOld l1 l2 l3 : Word}
    {data : List (BitVec 8)} :
    calldataloadWindowArmPre offReg byteReg accReg addrReg cdpReg
        sp cdp offLo offOld addrOld byteOld accOld l1 l2 l3 data =
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) ** (cdpReg ↦ᵣ cdp) **
       (addrReg ↦ᵣ addrOld) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (sp ↦ₘ offLo) ** ((sp + 8) ↦ₘ l1) ** ((sp + 16) ↦ₘ l2) **
       ((sp + 24) ↦ₘ l3) **
       calldataRegionIs cdp data) := rfl

/-- Postcondition of the window arm: the four output limbs of
    `callDataLoadWord` in the operand stack cells (the pad makes each limb
    `callDataByte`-exact even when the window straddles the calldata end),
    scratch registers at their final concrete values, region untouched. -/
def calldataloadWindowArmPost
    (offReg byteReg accReg addrReg cdpReg : Reg)
    (sp cdp offLo : Word) (data : List (BitVec 8)) : Assertion :=
  calldataloadArmMid offReg byteReg accReg addrReg cdpReg
    sp cdp offLo
    ((callDataByte data (offLo.toNat + 0 + 7)).zeroExtend 64)
    (calldataloadOutputLimb data offLo.toNat 0)
    (calldataloadOutputLimb data offLo.toNat 24)
    (calldataloadOutputLimb data offLo.toNat 16)
    (calldataloadOutputLimb data offLo.toNat 8)
    (calldataloadOutputLimb data offLo.toNat 0) data

theorem calldataloadWindowArmPost_unfold
    {offReg byteReg accReg addrReg cdpReg : Reg}
    {sp cdp offLo : Word} {data : List (BitVec 8)} :
    calldataloadWindowArmPost offReg byteReg accReg addrReg cdpReg
        sp cdp offLo data =
      calldataloadArmMid offReg byteReg accReg addrReg cdpReg
        sp cdp offLo
        ((callDataByte data (offLo.toNat + 0 + 7)).zeroExtend 64)
        (calldataloadOutputLimb data offLo.toNat 0)
        (calldataloadOutputLimb data offLo.toNat 24)
        (calldataloadOutputLimb data offLo.toNat 16)
        (calldataloadOutputLimb data offLo.toNat 8)
        (calldataloadOutputLimb data offLo.toNat 0) data := rfl

/-- The window arm over the in-bounds window code: prologue (2 steps) plus
    the four region quarters (4 × 23 steps). -/
theorem calldataload_window_arm_core_spec_within
    (offReg byteReg accReg addrReg cdpReg : Reg)
    (sp cdp offLo offOld addrOld byteOld accOld l1 l2 l3 : Word)
    (data : List (BitVec 8)) (wbase : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_wf : CalldataRegionWf cdp data)
    (h_off : offLo.toNat < data.length) :
    cpsTripleWithin 94 wbase (wbase + 376)
      (evm_calldataload_window_code offReg byteReg accReg addrReg cdpReg wbase)
      (calldataloadWindowArmPre offReg byteReg accReg addrReg cdpReg
        sp cdp offLo offOld addrOld byteOld accOld l1 l2 l3 data)
      (calldataloadWindowArmPost offReg byteReg accReg addrReg cdpReg
        sp cdp offLo data) := by
  -- Prologue: load the offset low limb, resolve `addrReg = cdp + offLo`;
  -- framed with the untouched window scratch and region.
  have h_pro := calldataload_window_prologue_stack_spec_within
    offReg byteReg accReg addrReg cdpReg
    sp offLo offOld addrOld cdp wbase h_off_ne_x0 h_addr_ne_x0
  have h_pro_f := cpsTripleWithin_frameR
    ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
     ((sp + 8) ↦ₘ l1) ** ((sp + 16) ↦ₘ l2) ** ((sp + 24) ↦ₘ l3) **
     calldataRegionIs cdp data)
    (pcFree_sepConj (by pcFree)
      (pcFree_sepConj (by pcFree)
        (pcFree_sepConj (by pcFree)
          (pcFree_sepConj (by pcFree)
            (pcFree_sepConj (by pcFree)
              (calldataRegionIs_pcFree cdp data)))))) h_pro
  have h_pro_w : cpsTripleWithin 2 wbase (wbase + 8)
      (evm_calldataload_window_code offReg byteReg accReg addrReg cdpReg wbase)
      (calldataloadWindowArmPre offReg byteReg accReg addrReg cdpReg
        sp cdp offLo offOld addrOld byteOld accOld l1 l2 l3 data)
      (calldataloadArmMid offReg byteReg accReg addrReg cdpReg
        sp cdp offLo byteOld accOld offLo l1 l2 l3 data) := by
    rw [calldataloadWindowArmPre_unfold, calldataloadArmMid_unfold]
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      h_pro_f
  -- The four quarters, chained through the ladder's one-limb sequence.
  have h_quads := calldataload_window_one_limb_sequence_stack_spec_within
    offReg byteReg accReg addrReg cdpReg wbase
    (arm_step_q0 offReg byteReg accReg addrReg cdpReg
      sp cdp offLo byteOld accOld l1 l2 l3 data wbase
      h_byte_ne_x0 h_acc_ne_x0 h_wf h_off)
    (arm_step_q1 offReg byteReg accReg addrReg cdpReg
      sp cdp offLo l1 l2 l3 data wbase
      h_byte_ne_x0 h_acc_ne_x0 h_wf h_off)
    (arm_step_q2 offReg byteReg accReg addrReg cdpReg
      sp cdp offLo l2 l3 data wbase
      h_byte_ne_x0 h_acc_ne_x0 h_wf h_off)
    (arm_step_q3 offReg byteReg accReg addrReg cdpReg
      sp cdp offLo l3 data wbase
      h_byte_ne_x0 h_acc_ne_x0 h_wf h_off)
  rw [calldataloadWindowArmPost_unfold]
  exact cpsTripleWithin_seq_same_cr h_pro_w h_quads

/-! ## Window arm over the full program -/

/-- The window arm of `evm_calldataload`: from the dispatch fall-through at
    `base + calldataloadWindowOff` to the common exit at
    `base + calldataloadExitOff` (via the trailing `JAL x0`), over the full
    program code, with the calldata modeled by `calldataRegionIs`. -/
theorem calldataload_window_arm_spec_within
    (envBaseReg offReg byteReg accReg addrReg cdpReg lenReg flagReg
      tmpReg : Reg)
    (sp base cdp offLo offOld addrOld byteOld accOld l1 l2 l3 : Word)
    (data : List (BitVec 8))
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_wf : CalldataRegionWf cdp data)
    (h_off : offLo.toNat < data.length) :
    cpsTripleWithin 95 (base + 48) (base + 444)
      (evm_calldataload_code envBaseReg offReg byteReg accReg addrReg
        cdpReg lenReg flagReg tmpReg base)
      (calldataloadWindowArmPre offReg byteReg accReg addrReg cdpReg
        sp cdp offLo offOld addrOld byteOld accOld l1 l2 l3 data)
      (calldataloadWindowArmPost offReg byteReg accReg addrReg cdpReg
        sp cdp offLo data) := by
  -- Transport the window-code arm core into the full program code.
  have h_core := calldataload_window_arm_core_spec_within
    offReg byteReg accReg addrReg cdpReg
    sp cdp offLo offOld addrOld byteOld accOld l1 l2 l3 data
    (base + BitVec.ofNat 64 calldataloadWindowOff)
    h_off_ne_x0 h_addr_ne_x0 h_byte_ne_x0 h_acc_ne_x0 h_wf h_off
  have h_core' := cpsTripleWithin_extend_code
    (cr' := evm_calldataload_code envBaseReg offReg byteReg accReg addrReg
      cdpReg lenReg flagReg tmpReg base)
    (hmono := fun a i h =>
      evm_calldataload_window_code_sub_full envBaseReg offReg byteReg accReg
        addrReg cdpReg lenReg flagReg tmpReg base a i h)
    h_core
  rw [show base + BitVec.ofNat 64 calldataloadWindowOff = base + 48 from rfl,
      show (base + 48 : Word) + 376 = base + 424 from by bv_omega] at h_core'
  -- The exit jump: `JAL x0 20` at `base + 424` is a pure PC move.
  have h_jal := EvmAsm.Rv64.SAsm.jal0_spec_pcFree (20 : BitVec 21) (base + 424)
    (P := calldataloadWindowArmPost offReg byteReg accReg addrReg cdpReg
      sp cdp offLo data)
    (by
      rw [calldataloadWindowArmPost_unfold]
      exact calldataloadArmMid_pcFree offReg byteReg accReg addrReg cdpReg
        sp cdp offLo _ _ _ _ _ _ data)
  rw [show (base + 424 : Word) + signExtend21 (20 : BitVec 21) = base + 444
        from by rw [show signExtend21 (20 : BitVec 21) = (20 : Word) from by
          decide]; bv_omega] at h_jal
  have h_jal' := cpsTripleWithin_extend_code
    (cr' := evm_calldataload_code envBaseReg offReg byteReg accReg addrReg
      cdpReg lenReg flagReg tmpReg base)
    (hmono := fun a i h =>
      CodeReq.singleton_mono
        (evm_calldataload_lookup_jal envBaseReg offReg byteReg accReg addrReg
          cdpReg lenReg flagReg tmpReg base) a i h)
    h_jal
  exact cpsTripleWithin_seq_same_cr h_core' h_jal'

end Calldata
end EvmAsm.Evm64
