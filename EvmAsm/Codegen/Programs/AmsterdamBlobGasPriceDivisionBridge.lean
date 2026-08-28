/-
  Machine/model bridge for the restoring division in `amsterdam_blob_gas_price_u256`.

  Body3 carries the emitted bit loop as `divst`, while the pure K70 model
  carries the same restoring recurrence as `divBitRun` and folds it through
  `divLimbFrom`/`div384by64`.  The machine uses signed-zero testing and the
  complementary unsigned comparison; the first theorem below makes that
  representation difference explicit before the recursive fold is tied.
-/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody3Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceModel

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceDivisionBridge

open EvmAsm.Rv64
open EvmAsm.Codegen.AmsterdamBlobGasPrice
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody3Spec

set_option maxRecDepth 8000

theorem slt_zero_iff (x : BitVec 64) :
    BitVec.slt x 0 = true ↔ 2 ^ 63 ≤ x.toNat := by
  rw [BitVec.slt_eq_decide, BitVec.toInt_eq_toNat_bmod]
  have h0 : ((0 : BitVec 64)).toInt = 0 := by decide
  rw [h0]
  simp only [decide_eq_true_eq, Int.bmod]
  have hlt : x.toNat < 2 ^ 64 := x.isLt
  omega

theorem slt_zero_eq_msb (x : Word) : BitVec.slt x (0 : Word) = x.msb := by
  have hsl : BitVec.slt x (0 : Word) = true ↔ 2 ^ 63 ≤ x.toNat := slt_zero_iff x
  rw [BitVec.msb_eq_decide]
  cases hs : BitVec.slt x (0 : Word)
  · have hnot : ¬ 2 ^ 63 ≤ x.toNat :=
      fun h => Bool.noConfusion (hs ▸ hsl.mpr h)
    have h63 : 2 ^ (64 - 1) = (2 ^ 63 : Nat) := by decide
    rw [h63]
    simp
    omega
  · have hge : 2 ^ 63 ≤ x.toNat := hsl.mp hs
    have h63 : 2 ^ (64 - 1) = (2 ^ 63 : Nat) := by decide
    rw [h63]
    simp
    exact hge

theorem ult_eq_not_ule (x y : Word) :
    BitVec.ult x y = !(BitVec.ule y x) := by
  by_cases h : x.toNat < y.toNat
  · have hnot : ¬ y.toNat ≤ x.toNat := by omega
    simp [BitVec.ult, BitVec.ule, h, hnot]
  · have hle : y.toNat ≤ x.toNat := by omega
    simp [BitVec.ult, BitVec.ule, h, hle]

theorem divst_eq_divBitRun (dv r0 t0 q0 : Word) (j : Nat) :
    divst dv r0 t0 q0 j = divBitRun dv r0 t0 q0 j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [divst, divBitRun]
    rw [ih]
    simp only [divBitStep]
    rw [slt_zero_eq_msb]
    let r1 : Word := (divBitRun dv r0 t0 q0 j).1 <<< (1 : Nat) +
      (if (divBitRun dv r0 t0 q0 j).2.1.msb then (1 : Word) else 0)
    change (if BitVec.ult r1 dv then r1 else r1 - dv,
        (divBitRun dv r0 t0 q0 j).2.1 <<< (1 : Nat),
        (divBitRun dv r0 t0 q0 j).2.2 <<< (1 : Nat) +
          (if BitVec.ult r1 dv then (0 : Word) else 1)) =
      (if BitVec.ule dv r1 then
          (r1 - dv, (divBitRun dv r0 t0 q0 j).2.1 <<< (1 : Nat),
            (divBitRun dv r0 t0 q0 j).2.2 <<< (1 : Nat) + 1)
        else
          (r1, (divBitRun dv r0 t0 q0 j).2.1 <<< (1 : Nat),
            (divBitRun dv r0 t0 q0 j).2.2 <<< (1 : Nat)))
    rw [ult_eq_not_ule]
    by_cases h : BitVec.ule dv r1 = true
    · simp [h]
    · simp [h]

def divstLimbFrom (d rem : Word) : List Word → List Word × Word
  | [] => ([], rem)
  | a :: rest =>
      let z := divst d rem a 0 64
      let (qs, rf) := divstLimbFrom d z.1 rest
      (z.2.2 :: qs, rf)

theorem divstLimbFrom_eq_divLimbFrom (d rem : Word) (ws : List Word) :
    divstLimbFrom d rem ws = divLimbFrom d rem ws := by
  induction ws generalizing rem with
  | nil => rfl
  | cons a rest ih =>
    simp only [divstLimbFrom, divLimbFrom]
    rw [divst_eq_divBitRun]
    rw [ih]

def divst384by64 (d : Word) (ws : List Word) : List Word × Word :=
  let (qsRev, rf) := divstLimbFrom d 0 ws.reverse
  (qsRev.reverse, rf)

theorem divst384by64_eq_div384by64 (d : Word) (ws : List Word) :
    divst384by64 d ws = div384by64 d ws := by
  simp only [divst384by64, div384by64]
  rw [divstLimbFrom_eq_divLimbFrom]

def divstSix (d p0 p1 p2 p3 p4 p5 : Word) : List Word × Word :=
  let z0 := divst d (0 : Word) p5 (0 : Word) 64
  let z1 := divst d z0.1 p4 (0 : Word) 64
  let z2 := divst d z1.1 p3 (0 : Word) 64
  let z3 := divst d z2.1 p2 (0 : Word) 64
  let z4 := divst d z3.1 p1 (0 : Word) 64
  let z5 := divst d z4.1 p0 (0 : Word) 64
  ([z5.2.2, z4.2.2, z3.2.2, z2.2.2, z1.2.2, z0.2.2], z5.1)

theorem divstSix_eq_div384by64 (d p0 p1 p2 p3 p4 p5 : Word) :
    divstSix d p0 p1 p2 p3 p4 p5 = div384by64 d [p0, p1, p2, p3, p4, p5] := by
  rw [← divst384by64_eq_div384by64]
  rfl

#print axioms divst_eq_divBitRun
#print axioms divstLimbFrom_eq_divLimbFrom
#print axioms divst384by64_eq_div384by64
#print axioms divstSix_eq_div384by64

end EvmAsm.Codegen.AmsterdamBlobGasPriceDivisionBridge
