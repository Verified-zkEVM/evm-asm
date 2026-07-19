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
    (spVal spC loadPtr lenW balPtr balLenW chainIdW : Word)
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

end EvmAsm.Codegen.TxEip7702TeerSpec
