/-
  Teer second walk_init (auth list) under applied prest.
  AfterValueNonzero → AfterWalkInit2Save via InnerSetup2 + short WI.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerFrontValueNonzero
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkInit2
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.SAsm.RwSubwindow
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
open EvmAsm.Codegen.TxTypeDispatchSpec
  (teerTxTypeDispatch txSlice ambientAbsOff loadPtr_add_rel_eq)
open EvmAsm.Codegen.TxIntrinsicStateGasSpec (nTypeSteps)

private abbrev nWalkNextCycle : Nat := 2 + (1 + 87) + 1 + 1
private abbrev nWalkNext5CycleOnly : Nat := 2 + (1 + 87) + 1
private abbrev nValueNonzeroCyclePub : Nat := 2 + (1 + 87) + 1 + 4
private abbrev nWalkInit2Short : Nat := 1 + 15 + 1 + 2
private abbrev nInnerSetup2 : Nat := 7
private abbrev nWalkInit2FromValue : Nat := nInnerSetup2 + nWalkInit2Short

private abbrev nFrontToWalkNext5Bne : Nat :=
  ((34 + (6 + (1 + nTypeSteps) + 1)) + (5 + 7)) + (1 + 15 + 1 + 2) +
    nWalkNextCycle * 5 + nWalkNext5CycleOnly
private abbrev nFrontToRecipientSave : Nat := nFrontToWalkNext5Bne + 8
private abbrev nFrontToValueNonzero : Nat := nFrontToRecipientSave + nValueNonzeroCyclePub
private abbrev nFrontToWalkInit2Save : Nat := nFrontToValueNonzero + nWalkInit2FromValue

local macro "pcf" : tactic => `(tactic|
  repeat first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_emp
    | exact pcFree_pure
    | exact pcFree_frameSlotsSaved
    | exact bytesRegion_pcFree _ _)

/-- InnerSetup2 with regOwn x6 (vnz post has regOwn x6). -/
theorem teerInnerSetup2_ownTemps
    (loadPtr lenW innerVal v5 v10 v11 v21 v22 : Word) :
    cpsTripleWithin nInnerSetup2 AfterValueNonzero AtWalkInit2 teerLinkedEarly
      ((.x5 ↦ᵣ v5) ** regOwn .x6 ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        (InnerOffAddr ↦ₘ innerVal))
      ((.x5 ↦ᵣ InnerOffAddr) ** (.x6 ↦ᵣ innerVal) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ loadPtr + innerVal) ** (.x11 ↦ᵣ lenW - innerVal) **
        (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
        (InnerOffAddr ↦ₘ innerVal)) := by
  have h0 (v6 : Word) :
      cpsTripleWithin nInnerSetup2 AfterValueNonzero AtWalkInit2 teerLinkedEarly
        ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
          (InnerOffAddr ↦ₘ innerVal))
        ((.x5 ↦ᵣ InnerOffAddr) ** (.x6 ↦ᵣ innerVal) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x10 ↦ᵣ loadPtr + innerVal) ** (.x11 ↦ᵣ lenW - innerVal) **
          (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
          (InnerOffAddr ↦ₘ innerVal)) :=
    teerInnerSetup2 loadPtr lenW innerVal v5 v6 v10 v11 v21 v22
  have h := cpsTripleWithin_of_forall_regIs_to_regOwn
    (r := .x6)
    (P := (.x5 ↦ᵣ v5) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
      (InnerOffAddr ↦ₘ innerVal))
    (fun v6 =>
      cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) (h0 v6))
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq) h

/-- Short WI2 success with regOwn temps (x12/x28/x29/x30/x31). -/
theorem teerWalkInit2ShortSuccess_ownTemps
    (listBase listLen t0 t1 t2 : Word)
    (bs : List (BitVec 8)) (listOff : Nat) (old1 v21 v22 : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : listOff < bs.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (listBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (listBase + BitVec.ofNat 64 listOff) + listLen) :
    let cur := (listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12)
    let endW := (listBase + BitVec.ofNat 64 listOff) + listLen
    cpsTripleWithin nWalkInit2Short AtWalkInit2 AfterWalkInit2Save teerLinkedEarly
      ((.x1 ↦ᵣ old1) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
        (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
        regOwn .x12 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
      ((.x1 ↦ᵣ LinkWalkInit2) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endW) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
  intro cur endW
  have hcore (a2 t3 t4 t5 t6 : Word) :
      cpsTripleWithin nWalkInit2Short AtWalkInit2 AfterWalkInit2Save teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
          teerWalkInit2Prest listBase listLen a2 t0 t1 t2 t3 t4 t5 t6 bs listOff)
        ((.x1 ↦ᵣ LinkWalkInit2) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
          (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endW) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
    have h0 := teerWalkInit2ShortSuccess listBase listLen a2 t0 t1 t2 t3 t4 t5 t6
      bs listOff old1 v21 v22 hsalign hoff hover hvalid hlen h_ge h_hi h_exact
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun s hq => ?_) h0
    -- mono x30/x31 regIs→regOwn
    have hq1 :
        ((.x30 ↦ᵣ t5) ** (.x31 ↦ᵣ t6) **
          ((.x1 ↦ᵣ LinkWalkInit2) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
            (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endW) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
            regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) s := by
      xperm_hyp hq
    have hq2 :=
      (sepConj_mono (regIs_implies_regOwn .x30)
        (sepConj_mono (regIs_implies_regOwn .x31) (fun _ h => h))) s hq1
    xperm_hyp hq2
  have hcore' (a2 t3 t4 t5 t6 : Word) :
      cpsTripleWithin nWalkInit2Short AtWalkInit2 AfterWalkInit2Save teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
          (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
          (.x12 ↦ᵣ a2) ** (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4) **
          (.x30 ↦ᵣ t5) ** (.x31 ↦ᵣ t6) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
        ((.x1 ↦ᵣ LinkWalkInit2) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
          (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endW) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
    refine cpsTripleWithin_weaken (fun s hp => ?_) (fun _ hq => hq)
      (hcore a2 t3 t4 t5 t6)
    unfold teerWalkInit2Prest teerWalkInitPrest at *
    xperm_hyp hp
  have h3031 (a2 t3 t4 : Word) :
      cpsTripleWithin nWalkInit2Short AtWalkInit2 AfterWalkInit2Save teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
          (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
          (.x12 ↦ᵣ a2) ** (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4) **
          regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
        ((.x1 ↦ᵣ LinkWalkInit2) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
          (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endW) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
    have h := cpsTripleWithin_of_forall_regIs_to_regOwn2
      (r1 := .x30) (r2 := .x31)
      (P := (.x1 ↦ᵣ old1) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
        (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
        (.x12 ↦ᵣ a2) ** (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
      (fun t5 t6 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (hcore' a2 t3 t4 t5 t6))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h
  have h2829 (a2 : Word) :
      cpsTripleWithin nWalkInit2Short AtWalkInit2 AfterWalkInit2Save teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
          (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
          (.x12 ↦ᵣ a2) **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
        ((.x1 ↦ᵣ LinkWalkInit2) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
          (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endW) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
    have h := cpsTripleWithin_of_forall_regIs_to_regOwn2
      (r1 := .x28) (r2 := .x29)
      (P := (.x1 ↦ᵣ old1) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
        (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
        (.x12 ↦ᵣ a2) ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
      (fun t3 t4 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (h3031 a2 t3 t4))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h
  have h := cpsTripleWithin_of_forall_regIs_to_regOwn
    (r := .x12)
    (P := (.x1 ↦ᵣ old1) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
      (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
      (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (fun a2 =>
      cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) (h2829 a2))
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq) h

/-- Leaf: AfterValueNonzero → AfterWalkInit2Save (InnerSetup2 + short WI2). -/
theorem teerWalkInit2FromValue
    (listBase listLen loadPtr lenW innerVal : Word)
    (bs : List (BitVec 8)) (listOff : Nat)
    (old1 v5 v10 v11 v21 v22 : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : listOff < bs.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (listBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (listBase + BitVec.ofNat 64 listOff) + listLen)
    (ha0 : loadPtr + innerVal = listBase + BitVec.ofNat 64 listOff)
    (hlenEq : lenW - innerVal = listLen) :
    let cur := (listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12)
    let endW := (listBase + BitVec.ofNat 64 listOff) + listLen
    cpsTripleWithin nWalkInit2FromValue AfterValueNonzero AfterWalkInit2Save
      teerLinkedEarly
      ((.x1 ↦ᵣ old1) ** (.x5 ↦ᵣ v5) ** regOwn .x6 ** regOwn .x7 **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
        (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        regOwn .x12 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
        (InnerOffAddr ↦ₘ innerVal))
      ((.x1 ↦ᵣ LinkWalkInit2) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endW) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (InnerOffAddr ↦ₘ innerVal) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
  intro cur endW
  have hsetup := teerInnerSetup2_ownTemps loadPtr lenW innerVal v5 v10 v11 v21 v22
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) ** regOwn .x7 **
      regOwn .x12 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) hsetup
  -- ShortSuccess with concrete t2, then lift x7
  have hwi0 (t2' : Word) :
      cpsTripleWithin nWalkInit2Short AtWalkInit2 AfterWalkInit2Save
        teerLinkedEarly
        ((.x1 ↦ᵣ old1) **
          (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
          (.x10 ↦ᵣ loadPtr + innerVal) ** (.x11 ↦ᵣ lenW - innerVal) **
          (.x5 ↦ᵣ InnerOffAddr) ** (.x6 ↦ᵣ innerVal) ** (.x7 ↦ᵣ t2') **
          regOwn .x12 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
        ((.x1 ↦ᵣ LinkWalkInit2) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
          (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endW) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
    have hwi := teerWalkInit2ShortSuccess_ownTemps listBase listLen
      InnerOffAddr innerVal t2' bs listOff old1
      (loadPtr + innerVal) (lenW - innerVal)
      hsalign hoff hover hvalid hlen h_ge h_hi h_exact
    refine cpsTripleWithin_weaken (fun s hp => ?_) (fun _ hq => hq) hwi
    have hp' :
        ((.x1 ↦ᵣ old1) ** (.x21 ↦ᵣ loadPtr + innerVal) **
          (.x22 ↦ᵣ lenW - innerVal) **
          (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
          (.x11 ↦ᵣ listLen) **
          (.x5 ↦ᵣ InnerOffAddr) ** (.x6 ↦ᵣ innerVal) ** (.x7 ↦ᵣ t2') **
          regOwn .x12 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) s := by
      simpa [ha0, hlenEq] using hp
    xperm_hyp hp'
  have hwi' : cpsTripleWithin nWalkInit2Short AtWalkInit2 AfterWalkInit2Save
      teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
        (.x10 ↦ᵣ loadPtr + innerVal) ** (.x11 ↦ᵣ lenW - innerVal) **
        (.x5 ↦ᵣ InnerOffAddr) ** (.x6 ↦ᵣ innerVal) ** regOwn .x7 **
        regOwn .x12 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
      ((.x1 ↦ᵣ LinkWalkInit2) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endW) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
    have h := cpsTripleWithin_of_forall_regIs_to_regOwn
      (r := .x7)
      (P := (.x1 ↦ᵣ old1) **
        (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
        (.x10 ↦ᵣ loadPtr + innerVal) ** (.x11 ↦ᵣ lenW - innerVal) **
        (.x5 ↦ᵣ InnerOffAddr) ** (.x6 ↦ᵣ innerVal) **
        regOwn .x12 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
      (fun t2' =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (hwi0 t2'))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h
  have hwiF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) ** (InnerOffAddr ↦ₘ innerVal))
    (by pcf) hwi'
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hsetupF hwiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

#print axioms teerInnerSetup2_ownTemps
#print axioms teerWalkInit2ShortSuccess_ownTemps
#print axioms teerWalkInit2FromValue


/-- Ambient through FromValue (drops focus regs). -/
def teerWalkInit2Ambient
    (spVal spC _loadPtr _lenW balPtr balLenW chainIdW : Word)
    (s : TeerSaved) (_regionBase : Word) (_bs balBytes : List (BitVec 8))
    (_innerVal endW : Word) (s7 s11 cursorV : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
    (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
    (.x23 ↦ᵣ s7) **
    (.x24 ↦ᵣ cursorV) ** (.x25 ↦ᵣ endW) **
    (.x26 ↦ᵣ (0 : Word)) **
    (.x27 ↦ᵣ s11) **
    frameSlotsSaved teerFrame spC (teerSavedVals s) **
    (TypeAddr ↦ₘ (4 : Word)) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    stackFree spVal 6 **
    bytesRegion balPtr balBytes **
    memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
    memOwn ValueNonzeroAddr **
    teerScratchWithoutVnzOwn

private theorem pcFree_teerWalkInit2Ambient
    (spVal spC _loadPtr _lenW balPtr balLenW chainIdW : Word)
    (s : TeerSaved) (regionBase : Word) (bs balBytes : List (BitVec 8))
    (innerVal endW : Word) (s7 s11 cursorV : Word) :
    (teerWalkInit2Ambient spVal spC _loadPtr _lenW balPtr balLenW chainIdW
      s regionBase bs balBytes innerVal endW s7 s11 cursorV).pcFree := by
  unfold teerWalkInit2Ambient; pcf

def teerWalkInit2Focus
    (regionBase : Word) (bs : List (BitVec 8))
    (old1 v5 v10 v11 v21 v22 loadPtr lenW innerVal : Word) : Assertion :=
  (.x1 ↦ᵣ old1) ** (.x5 ↦ᵣ v5) ** regOwn .x6 ** regOwn .x7 **
    (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
    (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
    (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
    regOwn .x12 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
    (InnerOffAddr ↦ₘ innerVal)

def teerWalkInit2BodyPost
    (regionBase : Word) (bs : List (BitVec 8))
    (listOff : Nat) (listLen loadPtr lenW innerVal : Word) : Assertion :=
  let cur := (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12)
  let endL := (regionBase + BitVec.ofNat 64 listOff) + listLen
  (.x1 ↦ᵣ LinkWalkInit2) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endL) **
    (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endL) **
    (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
    (InnerOffAddr ↦ₘ innerVal) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs

/-- ValueNonzero flat body (no pure). -/
def teerValueNonzeroFlatRest
    (spVal spC loadPtr lenW balPtr balLenW chainIdW : Word)
    (s : TeerSaved) (regionBase : Word) (bs balBytes : List (BitVec 8))
    (innerVal endW : Word) (s7 s11 next lenV cursorV : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
    (.x1 ↦ᵣ LinkWalkNextValue) **
    (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
    (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
    (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
    (.x23 ↦ᵣ s7) **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenV) **
    (.x24 ↦ᵣ cursorV) ** (.x25 ↦ᵣ endW) **
    (.x26 ↦ᵣ (0 : Word)) **
    (.x27 ↦ᵣ s11) **
    frameSlotsSaved teerFrame spC (teerSavedVals s) **
    (.x0 ↦ᵣ (0 : Word)) **
    (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
    (.x30 ↦ᵣ (if BitVec.ult (0 : Word) lenV then (1 : Word) else 0)) **
    (.x5 ↦ᵣ ValueNonzeroAddr) **
    regOwn .x6 ** regOwn .x7 **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
    stackFree spVal 6 **
    bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
    memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
    memOwn ValueNonzeroAddr **
    teerScratchWithoutVnzOwn

theorem teerValueNonzeroFlatRest_to_wi2Pre
    (spVal spC loadPtr lenW balPtr balLenW chainIdW : Word)
    (s : TeerSaved) (regionBase : Word) (bs balBytes : List (BitVec 8))
    (innerVal endW : Word) (s7 s11 next lenV cursorV : Word) :
    ∀ h,
      (teerValueNonzeroFlatRest spVal spC loadPtr lenW balPtr balLenW chainIdW
          s regionBase bs balBytes innerVal endW s7 s11 next lenV cursorV) h →
      (teerWalkInit2Focus regionBase bs
          LinkWalkNextValue ValueNonzeroAddr next (0 : Word)
          (loadPtr + innerVal) (lenW - innerVal) loadPtr lenW innerVal **
        teerWalkInit2Ambient spVal spC loadPtr lenW balPtr balLenW chainIdW
          s regionBase bs balBytes innerVal endW s7 s11 cursorV) h := by
  intro h hp
  unfold teerValueNonzeroFlatRest at hp
  -- mono x12, x30 regIs→regOwn then xperm into Focus**Ambient
  have hp1 :
      ((.x12 ↦ᵣ lenV) **
        (.x30 ↦ᵣ (if BitVec.ult (0 : Word) lenV then (1 : Word) else 0)) **
        ((.x2 ↦ᵣ spC) **
          (.x1 ↦ᵣ LinkWalkNextValue) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
          (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
          (.x23 ↦ᵣ s7) **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) **
          (.x24 ↦ᵣ cursorV) ** (.x25 ↦ᵣ endW) **
          (.x26 ↦ᵣ (0 : Word)) **
          (.x27 ↦ᵣ s11) **
          frameSlotsSaved teerFrame spC (teerSavedVals s) **
          (.x0 ↦ᵣ (0 : Word)) **
          (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
          (.x5 ↦ᵣ ValueNonzeroAddr) **
          regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
          stackFree spVal 6 **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
          memOwn ValueNonzeroAddr **
          teerScratchWithoutVnzOwn)) h := by
    xperm_hyp hp
  have hp2 :=
    (sepConj_mono (regIs_implies_regOwn .x12)
      (sepConj_mono (regIs_implies_regOwn .x30) (fun _ hx => hx))) h hp1
  unfold teerWalkInit2Focus teerWalkInit2Ambient
  xperm_hyp hp2

/-- FromValue framed under ambient. -/
theorem teerWalkInit2FromValue_framed
    (listBase listLen loadPtr lenW innerVal : Word)
    (bs : List (BitVec 8)) (listOff : Nat)
    (old1 v5 v10 v11 v21 v22 : Word)
    (Amb : Assertion) (hAmb : Amb.pcFree)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : listOff < bs.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (listBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (listBase + BitVec.ofNat 64 listOff) + listLen)
    (ha0 : loadPtr + innerVal = listBase + BitVec.ofNat 64 listOff)
    (hlenEq : lenW - innerVal = listLen) :
    cpsTripleWithin nWalkInit2FromValue AfterValueNonzero AfterWalkInit2Save
      teerLinkedEarly
      (teerWalkInit2Focus listBase bs old1 v5 v10 v11 v21 v22 loadPtr lenW innerVal **
        Amb)
      (teerWalkInit2BodyPost listBase bs listOff listLen loadPtr lenW innerVal **
        Amb) := by
  have h0 := teerWalkInit2FromValue listBase listLen loadPtr lenW innerVal
    bs listOff old1 v5 v10 v11 v21 v22
    hsalign hoff hover hvalid hlen h_ge h_hi h_exact ha0 hlenEq
  have hF := cpsTripleWithin_frameR Amb hAmb h0
  refine cpsTripleWithin_weaken (fun _ hp => by
      unfold teerWalkInit2Focus at hp; xperm_hyp hp)
    (fun s hq => by
      unfold teerWalkInit2BodyPost
      xperm_hyp hq) hF

#print axioms teerWalkInit2FromValue_framed
#print axioms teerValueNonzeroFlatRest_to_wi2Pre

theorem teerWalkInit2_applied
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true)
    (listOff : Nat)
    (ha0 : loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2 =
      regionBase + BitVec.ofNat 64 listOff)
    (hoffL : listOff < bs.length)
    (hoverL : regionBase.toNat + listOff < 2 ^ 64)
    (hvalidL : isValidByteAccess (regionBase + BitVec.ofNat 64 listOff) = true)
    (hlenL : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoffL).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
    (srcOff0 : Nat)
    (hcur0 : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOff0)
    (hoff0 : srcOff0 < bs.length)
    (hover0 : regionBase.toNat + srcOff0 < 2 ^ 64)
    (hvalid0I : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff0) = true)
    (hss0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        srcOff0 + 1 < bs.length ∧ regionBase.toNat + (srcOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hdec0 : ∃ next len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len0)
    (hinb0 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff0)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff1 : Nat)
    (hoff1 : srcOff1 < bs.length)
    (hover1 : regionBase.toNat + srcOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff1) = true)
    (hss1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < bs.length ∧ regionBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hdec1 : ∃ next len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len1)
    (hinb1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff2 : Nat)
    (hoff2 : srcOff2 < bs.length)
    (hover2 : regionBase.toNat + srcOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff2) = true)
    (hss2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < bs.length ∧ regionBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hdec2 : ∃ next len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len2)
    (hinb2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff3 : Nat)
    (hoff3 : srcOff3 < bs.length)
    (hover3 : regionBase.toNat + srcOff3 < 2 ^ 64)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff3) = true)
    (hss3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < bs.length ∧ regionBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hdec3 : ∃ next len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff4 : Nat)
    (hoff4 : srcOff4 < bs.length)
    (hover4 : regionBase.toNat + srcOff4 < 2 ^ 64)
    (hvalid4 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff4) = true)
    (hss4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < bs.length ∧ regionBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff5 : Nat)
    (hoff5 : srcOff5 < bs.length)
    (hover5 : regionBase.toNat + srcOff5 < 2 ^ 64)
    (hvalid5 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff5) = true)
    (hss5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < bs.length ∧ regionBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len5)
    (hinb5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1)
    (hbridge1 : ∀ next1 len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 srcOff2)
    (hbridge2 : ∀ next2 len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 srcOff3)
    (hbridge3 : ∀ next3 len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 srcOff4)
    (hbridge4 : ∀ next4 len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 srcOff5)
    (srcOffV : Nat)
    (hoffV : srcOffV < bs.length)
    (hoverV : regionBase.toNat + srcOffV < 2 ^ 64)
    (hvalidV : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffV) = true)
    (hssV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        srcOffV + 1 < bs.length ∧ regionBase.toNat + (srcOffV + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1)) = true)
    (hlsV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xc0 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hllV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xf8 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hdecV : ∃ next lenV : Word,
      rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenV)
    (hinbV : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffV)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge5 : ∀ next5 len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next5 len5 →
      next5 = regionBase + BitVec.ofNat 64 srcOffV) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    let listLen := lenW - innerVal
    let endW := (regionBase + BitVec.ofNat 64 listOff) + listLen
    let cursorV := regionBase + BitVec.ofNat 64 srcOffV
    let cur := (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12)
    let endL := (regionBase + BitVec.ofNat 64 listOff) + listLen
    cpsTripleWithin nFrontToWalkInit2Save
      E AfterWalkInit2Save teerLinkedEarly
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nTeerStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
        (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) ** (.x26 ↦ᵣ s10) **
        (.x27 ↦ᵣ s11) **
        (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
        (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      (((.x2 ↦ᵣ spC) **
          (.x1 ↦ᵣ LinkWalkInit2) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
          (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endL) **
          (.x23 ↦ᵣ s7) **
          (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endL) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x24 ↦ᵣ cursorV) ** (.x25 ↦ᵣ endW) **
          (.x26 ↦ᵣ (0 : Word)) **
          (.x27 ↦ᵣ s11) **
          frameSlotsSaved teerFrame spC (teerSavedVals s) **
          (.x0 ↦ᵣ (0 : Word)) **
          (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          stackFree spVal 6 **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
          memOwn ValueNonzeroAddr **
          teerScratchWithoutVnzOwn)) := by
  intro s innerVal listLen endW cursorV cur endL
  have hvnz := teerValueNonzero_applied ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    halign hbound hover hvalid0 listOff ha0 hoffL hoverL hvalidL hlenL
    h_ge h_hi h_exact srcOff0 hcur0 hoff0 hover0 hvalid0I hss0 hls0 hll0 hdec0 hinb0
    srcOff1 hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
    srcOff2 hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
    srcOff3 hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
    srcOff4 hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
    srcOff5 hoff5 hover5 hvalid5 hss5 hls5 hll5 hdec5 hinb5
    hbridge hbridge1 hbridge2 hbridge3 hbridge4
    srcOffV hoffV hoverV hvalidV hssV hlsV hllV hdecV hinbV hbridge5
  let Flat (p : Word × Word) : Assertion :=
    teerValueNonzeroFlatRest spVal spC loadPtr lenW balPtr balLenW chainIdW
      s regionBase bs balBytes innerVal endW s7 s11 p.1 p.2 cursorV **
    ⌜rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
      endW p.1 p.2⌝
  have hvnzE :
      cpsTripleWithin nFrontToValueNonzero E AfterValueNonzero teerLinkedEarly
        ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
          stackFree spVal nTeerStackDwords **
          (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
          (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
          (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
          (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) ** (.x26 ↦ᵣ s10) **
          (.x27 ↦ᵣ s11) **
          (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
          (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
          (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          teerScratchOwn **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
        (fun h => ∃ p : Word × Word, Flat p h) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hvnz
    obtain ⟨next, lenV, hq'⟩ := hq
    refine ⟨(next, lenV), ?_⟩
    -- value applied: (flat atoms ** pure); Flat = FlatRest ** pure
    dsimp only [Flat]
    have hq1 :
        ((teerValueNonzeroFlatRest spVal spC loadPtr lenW balPtr balLenW chainIdW
            s regionBase bs balBytes innerVal endW s7 s11 next lenV cursorV) **
          ⌜rlpItemDecode bs srcOffV cursorV endW next lenV⌝) h := by
      unfold teerValueNonzeroFlatRest
      -- value applied uses (regionBase+srcOffV); cursorV is that let
      simpa [cursorV] using hq'
    exact hq1
  let Wi2Post : Assertion :=
    teerWalkInit2BodyPost regionBase bs listOff listLen loadPtr lenW innerVal **
      teerWalkInit2Ambient spVal spC loadPtr lenW balPtr balLenW chainIdW
        s regionBase bs balBytes innerVal endW s7 s11 cursorV
  have hstep (p : Word × Word) :
      cpsTripleWithin nWalkInit2FromValue AfterValueNonzero AfterWalkInit2Save
        teerLinkedEarly (Flat p) Wi2Post := by
    dsimp only [Flat]
    have hswap :
        cpsTripleWithin nWalkInit2FromValue AfterValueNonzero AfterWalkInit2Save
          teerLinkedEarly
          (⌜rlpItemDecode bs srcOffV cursorV
              endW p.1 p.2⌝ **
            teerValueNonzeroFlatRest spVal spC loadPtr lenW balPtr balLenW chainIdW
              s regionBase bs balBytes innerVal endW s7 s11 p.1 p.2 cursorV)
          Wi2Post := by
      refine cpsTripleWithin_pure_pre (fun _hpure => ?_)
      have hF := teerWalkInit2FromValue_framed regionBase listLen loadPtr lenW
        innerVal bs listOff LinkWalkNextValue ValueNonzeroAddr p.1 (0 : Word)
        (loadPtr + innerVal) (lenW - innerVal)
        (teerWalkInit2Ambient spVal spC loadPtr lenW balPtr balLenW chainIdW
          s regionBase bs balBytes innerVal endW s7 s11 cursorV)
        (pcFree_teerWalkInit2Ambient spVal spC loadPtr lenW balPtr balLenW
          chainIdW s regionBase bs balBytes innerVal endW s7 s11 cursorV)
        (by simpa using halign) hoffL hoverL hvalidL hlenL h_ge h_hi h_exact
        (by simpa [innerVal] using ha0) rfl
      refine cpsTripleWithin_weaken
        (teerValueNonzeroFlatRest_to_wi2Pre
          spVal spC loadPtr lenW balPtr balLenW chainIdW s regionBase bs balBytes
          innerVal endW s7 s11 p.1 p.2 cursorV)
        (fun _ hq => by
          dsimp only [Wi2Post] at *
          exact hq) hF
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) hswap
  have hseq := cpsTripleWithin_seq_exists_same_cr hvnzE hstep
  have hseq' := cpsTripleWithin_mono_nSteps
    (by decide : nFrontToValueNonzero + nWalkInit2FromValue ≤ nFrontToWalkInit2Save)
    hseq
  -- Flatten Wi2Post to applied-style flat post
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hseq'
  dsimp only [Wi2Post] at hq
  unfold teerWalkInit2BodyPost teerWalkInit2Ambient at hq
  xperm_hyp hq

#print axioms teerWalkInit2_applied


/-- Ambient through FromValue (drops focus regs). -/
def teerWalkInit2AmbientIs
    (spVal spC _loadPtr _lenW balPtr balLenW chainIdW : Word)
    (s : TeerSaved) (_regionBase : Word) (_bs balBytes : List (BitVec 8))
    (_innerVal endW : Word) (s7 s11 cursorV : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
    (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
    (.x23 ↦ᵣ s7) **
    (.x24 ↦ᵣ cursorV) ** (.x25 ↦ᵣ endW) **
    (.x26 ↦ᵣ (0 : Word)) **
    (.x27 ↦ᵣ s11) **
    frameSlotsSaved teerFrame spC (teerSavedVals s) **
    (TypeAddr ↦ₘ (4 : Word)) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    stackFree spVal 6 **
    bytesRegion balPtr balBytes **
    memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
    memOwn ValueNonzeroAddr **
    teerScratchZeroIs ** teerScratchRestWithoutVnzOwn

private theorem pcFree_teerWalkInit2AmbientIs
    (spVal spC _loadPtr _lenW balPtr balLenW chainIdW : Word)
    (s : TeerSaved) (regionBase : Word) (bs balBytes : List (BitVec 8))
    (innerVal endW : Word) (s7 s11 cursorV : Word) :
    (teerWalkInit2AmbientIs spVal spC _loadPtr _lenW balPtr balLenW chainIdW
      s regionBase bs balBytes innerVal endW s7 s11 cursorV).pcFree := by
  unfold teerWalkInit2AmbientIs; pcf

def teerValueNonzeroFlatRestIs
    (spVal spC loadPtr lenW balPtr balLenW chainIdW : Word)
    (s : TeerSaved) (regionBase : Word) (bs balBytes : List (BitVec 8))
    (innerVal endW : Word) (s7 s11 next lenV cursorV : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
    (.x1 ↦ᵣ LinkWalkNextValue) **
    (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
    (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
    (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
    (.x23 ↦ᵣ s7) **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenV) **
    (.x24 ↦ᵣ cursorV) ** (.x25 ↦ᵣ endW) **
    (.x26 ↦ᵣ (0 : Word)) **
    (.x27 ↦ᵣ s11) **
    frameSlotsSaved teerFrame spC (teerSavedVals s) **
    (.x0 ↦ᵣ (0 : Word)) **
    (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
    (.x30 ↦ᵣ (if BitVec.ult (0 : Word) lenV then (1 : Word) else 0)) **
    (.x5 ↦ᵣ ValueNonzeroAddr) **
    regOwn .x6 ** regOwn .x7 **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
    stackFree spVal 6 **
    bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
    memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
    memOwn ValueNonzeroAddr **
    teerScratchZeroIs ** teerScratchRestWithoutVnzOwn

theorem teerValueNonzeroFlatRestIs_to_wi2Pre
    (spVal spC loadPtr lenW balPtr balLenW chainIdW : Word)
    (s : TeerSaved) (regionBase : Word) (bs balBytes : List (BitVec 8))
    (innerVal endW : Word) (s7 s11 next lenV cursorV : Word) :
    ∀ h,
      (teerValueNonzeroFlatRestIs spVal spC loadPtr lenW balPtr balLenW chainIdW
          s regionBase bs balBytes innerVal endW s7 s11 next lenV cursorV) h →
      (teerWalkInit2Focus regionBase bs
          LinkWalkNextValue ValueNonzeroAddr next (0 : Word)
          (loadPtr + innerVal) (lenW - innerVal) loadPtr lenW innerVal **
        teerWalkInit2AmbientIs spVal spC loadPtr lenW balPtr balLenW chainIdW
          s regionBase bs balBytes innerVal endW s7 s11 cursorV) h := by
  intro h hp
  unfold teerValueNonzeroFlatRestIs at hp
  -- mono x12, x30 regIs→regOwn then xperm into Focus**Ambient
  have hp1 :
      ((.x12 ↦ᵣ lenV) **
        (.x30 ↦ᵣ (if BitVec.ult (0 : Word) lenV then (1 : Word) else 0)) **
        ((.x2 ↦ᵣ spC) **
          (.x1 ↦ᵣ LinkWalkNextValue) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
          (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
          (.x23 ↦ᵣ s7) **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) **
          (.x24 ↦ᵣ cursorV) ** (.x25 ↦ᵣ endW) **
          (.x26 ↦ᵣ (0 : Word)) **
          (.x27 ↦ᵣ s11) **
          frameSlotsSaved teerFrame spC (teerSavedVals s) **
          (.x0 ↦ᵣ (0 : Word)) **
          (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
          (.x5 ↦ᵣ ValueNonzeroAddr) **
          regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
          stackFree spVal 6 **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
          memOwn ValueNonzeroAddr **
          teerScratchZeroIs ** teerScratchRestWithoutVnzOwn)) h := by
    xperm_hyp hp
  have hp2 :=
    (sepConj_mono (regIs_implies_regOwn .x12)
      (sepConj_mono (regIs_implies_regOwn .x30) (fun _ hx => hx))) h hp1
  unfold teerWalkInit2Focus teerWalkInit2AmbientIs
  xperm_hyp hp2


#print axioms teerValueNonzeroFlatRestIs_to_wi2Pre

theorem teerWalkInit2_applied_is
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true)
    (listOff : Nat)
    (ha0 : loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2 =
      regionBase + BitVec.ofNat 64 listOff)
    (hoffL : listOff < bs.length)
    (hoverL : regionBase.toNat + listOff < 2 ^ 64)
    (hvalidL : isValidByteAccess (regionBase + BitVec.ofNat 64 listOff) = true)
    (hlenL : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoffL).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
    (srcOff0 : Nat)
    (hcur0 : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOff0)
    (hoff0 : srcOff0 < bs.length)
    (hover0 : regionBase.toNat + srcOff0 < 2 ^ 64)
    (hvalid0I : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff0) = true)
    (hss0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        srcOff0 + 1 < bs.length ∧ regionBase.toNat + (srcOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hdec0 : ∃ next len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len0)
    (hinb0 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff0)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff1 : Nat)
    (hoff1 : srcOff1 < bs.length)
    (hover1 : regionBase.toNat + srcOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff1) = true)
    (hss1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < bs.length ∧ regionBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hdec1 : ∃ next len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len1)
    (hinb1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff2 : Nat)
    (hoff2 : srcOff2 < bs.length)
    (hover2 : regionBase.toNat + srcOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff2) = true)
    (hss2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < bs.length ∧ regionBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hdec2 : ∃ next len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len2)
    (hinb2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff3 : Nat)
    (hoff3 : srcOff3 < bs.length)
    (hover3 : regionBase.toNat + srcOff3 < 2 ^ 64)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff3) = true)
    (hss3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < bs.length ∧ regionBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hdec3 : ∃ next len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff4 : Nat)
    (hoff4 : srcOff4 < bs.length)
    (hover4 : regionBase.toNat + srcOff4 < 2 ^ 64)
    (hvalid4 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff4) = true)
    (hss4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < bs.length ∧ regionBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff5 : Nat)
    (hoff5 : srcOff5 < bs.length)
    (hover5 : regionBase.toNat + srcOff5 < 2 ^ 64)
    (hvalid5 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff5) = true)
    (hss5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < bs.length ∧ regionBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len5)
    (hinb5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1)
    (hbridge1 : ∀ next1 len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 srcOff2)
    (hbridge2 : ∀ next2 len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 srcOff3)
    (hbridge3 : ∀ next3 len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 srcOff4)
    (hbridge4 : ∀ next4 len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 srcOff5)
    (srcOffV : Nat)
    (hoffV : srcOffV < bs.length)
    (hoverV : regionBase.toNat + srcOffV < 2 ^ 64)
    (hvalidV : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffV) = true)
    (hssV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        srcOffV + 1 < bs.length ∧ regionBase.toNat + (srcOffV + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1)) = true)
    (hlsV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xc0 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hllV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xf8 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hdecV : ∃ next lenV : Word,
      rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenV)
    (hinbV : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffV)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge5 : ∀ next5 len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next5 len5 →
      next5 = regionBase + BitVec.ofNat 64 srcOffV) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    let listLen := lenW - innerVal
    let endW := (regionBase + BitVec.ofNat 64 listOff) + listLen
    let cursorV := regionBase + BitVec.ofNat 64 srcOffV
    let cur := (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12)
    let endL := (regionBase + BitVec.ofNat 64 listOff) + listLen
    cpsTripleWithin nFrontToWalkInit2Save
      E AfterWalkInit2Save teerLinkedEarly
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nTeerStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
        (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) ** (.x26 ↦ᵣ s10) **
        (.x27 ↦ᵣ s11) **
        (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
        (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      (((.x2 ↦ᵣ spC) **
          (.x1 ↦ᵣ LinkWalkInit2) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
          (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endL) **
          (.x23 ↦ᵣ s7) **
          (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endL) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x24 ↦ᵣ cursorV) ** (.x25 ↦ᵣ endW) **
          (.x26 ↦ᵣ (0 : Word)) **
          (.x27 ↦ᵣ s11) **
          frameSlotsSaved teerFrame spC (teerSavedVals s) **
          (.x0 ↦ᵣ (0 : Word)) **
          (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          stackFree spVal 6 **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
          memOwn ValueNonzeroAddr **
          teerScratchZeroIs ** teerScratchRestWithoutVnzOwn)) := by
  intro s innerVal listLen endW cursorV cur endL
  have hvnz := teerValueNonzero_applied_is ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    halign hbound hover hvalid0 listOff ha0 hoffL hoverL hvalidL hlenL
    h_ge h_hi h_exact srcOff0 hcur0 hoff0 hover0 hvalid0I hss0 hls0 hll0 hdec0 hinb0
    srcOff1 hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
    srcOff2 hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
    srcOff3 hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
    srcOff4 hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
    srcOff5 hoff5 hover5 hvalid5 hss5 hls5 hll5 hdec5 hinb5
    hbridge hbridge1 hbridge2 hbridge3 hbridge4
    srcOffV hoffV hoverV hvalidV hssV hlsV hllV hdecV hinbV hbridge5
  let Flat (p : Word × Word) : Assertion :=
    teerValueNonzeroFlatRestIs spVal spC loadPtr lenW balPtr balLenW chainIdW
      s regionBase bs balBytes innerVal endW s7 s11 p.1 p.2 cursorV **
    ⌜rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
      endW p.1 p.2⌝
  have hvnzE :
      cpsTripleWithin nFrontToValueNonzero E AfterValueNonzero teerLinkedEarly
        ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
          stackFree spVal nTeerStackDwords **
          (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
          (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
          (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
          (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) ** (.x26 ↦ᵣ s10) **
          (.x27 ↦ᵣ s11) **
          (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
          (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
          (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          teerScratchOwn **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
        (fun h => ∃ p : Word × Word, Flat p h) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hvnz
    obtain ⟨next, lenV, hq'⟩ := hq
    refine ⟨(next, lenV), ?_⟩
    -- value applied: (flat atoms ** pure); Flat = FlatRest ** pure
    dsimp only [Flat]
    have hq1 :
        ((teerValueNonzeroFlatRestIs spVal spC loadPtr lenW balPtr balLenW chainIdW
            s regionBase bs balBytes innerVal endW s7 s11 next lenV cursorV) **
          ⌜rlpItemDecode bs srcOffV cursorV endW next lenV⌝) h := by
      unfold teerValueNonzeroFlatRestIs
      -- value applied uses (regionBase+srcOffV); cursorV is that let
      simpa [cursorV] using hq'
    exact hq1
  let Wi2Post : Assertion :=
    teerWalkInit2BodyPost regionBase bs listOff listLen loadPtr lenW innerVal **
      teerWalkInit2AmbientIs spVal spC loadPtr lenW balPtr balLenW chainIdW
        s regionBase bs balBytes innerVal endW s7 s11 cursorV
  have hstep (p : Word × Word) :
      cpsTripleWithin nWalkInit2FromValue AfterValueNonzero AfterWalkInit2Save
        teerLinkedEarly (Flat p) Wi2Post := by
    dsimp only [Flat]
    have hswap :
        cpsTripleWithin nWalkInit2FromValue AfterValueNonzero AfterWalkInit2Save
          teerLinkedEarly
          (⌜rlpItemDecode bs srcOffV cursorV
              endW p.1 p.2⌝ **
            teerValueNonzeroFlatRestIs spVal spC loadPtr lenW balPtr balLenW chainIdW
              s regionBase bs balBytes innerVal endW s7 s11 p.1 p.2 cursorV)
          Wi2Post := by
      refine cpsTripleWithin_pure_pre (fun _hpure => ?_)
      have hF := teerWalkInit2FromValue_framed regionBase listLen loadPtr lenW
        innerVal bs listOff LinkWalkNextValue ValueNonzeroAddr p.1 (0 : Word)
        (loadPtr + innerVal) (lenW - innerVal)
        (teerWalkInit2AmbientIs spVal spC loadPtr lenW balPtr balLenW chainIdW
          s regionBase bs balBytes innerVal endW s7 s11 cursorV)
        (pcFree_teerWalkInit2AmbientIs spVal spC loadPtr lenW balPtr balLenW
          chainIdW s regionBase bs balBytes innerVal endW s7 s11 cursorV)
        (by simpa using halign) hoffL hoverL hvalidL hlenL h_ge h_hi h_exact
        (by simpa [innerVal] using ha0) rfl
      refine cpsTripleWithin_weaken
        (teerValueNonzeroFlatRestIs_to_wi2Pre
          spVal spC loadPtr lenW balPtr balLenW chainIdW s regionBase bs balBytes
          innerVal endW s7 s11 p.1 p.2 cursorV)
        (fun _ hq => by
          dsimp only [Wi2Post] at *
          exact hq) hF
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) hswap
  have hseq := cpsTripleWithin_seq_exists_same_cr hvnzE hstep
  have hseq' := cpsTripleWithin_mono_nSteps
    (by decide : nFrontToValueNonzero + nWalkInit2FromValue ≤ nFrontToWalkInit2Save)
    hseq
  -- Flatten Wi2Post to applied-style flat post
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hseq'
  dsimp only [Wi2Post] at hq
  unfold teerWalkInit2BodyPost teerWalkInit2AmbientIs at hq
  xperm_hyp hq

#print axioms teerWalkInit2_applied


#print axioms teerWalkInit2_applied_is

end EvmAsm.Codegen.TxEip7702TeerSpec
