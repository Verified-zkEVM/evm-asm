/-
  EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceMem

  Assertion-layer helpers for the `amsterdam_blob_gas_price_u256` discharge
  (issue #12346, item 7): the 48-byte working buffers are carried as
  `cellsOf` chains of dword cells (the form the LD/SD specs consume), with
  conversions to and from `bytesRegion` at the routine boundary, and to the
  `cellsOwn` ownership chains used by the uniform overflow exit and by
  `scratchPost`.
-/

import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceModel
import EvmAsm.Codegen.Programs.HeaderValidateExcessBlobGasSpec
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.SAsm.AbiFrameOwn

namespace EvmAsm.Codegen.AmsterdamBlobGasPrice

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec

/-- A limb list as a chain of dword memory cells. -/
def cellsOf (base : Word) : List Word → Assertion
  | [] => empAssertion
  | w :: ws => (base ↦ₘ w) ** cellsOf (base + 8) ws

/-- Ownership of `k` consecutive dword cells. -/
def cellsOwn (base : Word) : Nat → Assertion
  | 0 => empAssertion
  | k + 1 => memOwn base ** cellsOwn (base + 8) k

theorem cellsOf_pcFree (base : Word) (ws : List Word) : (cellsOf base ws).pcFree := by
  induction ws generalizing base with
  | nil => exact pcFree_emp
  | cons w ws ih => exact pcFree_sepConj pcFree_memIs (ih (base + 8))

theorem cellsOwn_pcFree (base : Word) (k : Nat) : (cellsOwn base k).pcFree := by
  induction k generalizing base with
  | zero => exact pcFree_emp
  | succ k ih => exact pcFree_sepConj pcFree_memOwn (ih (base + 8))

theorem cellsOf_add_ofNat (base : Word) (i j : Nat) :
    (base + BitVec.ofNat 64 i) + BitVec.ofNat 64 j =
      base + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem cellsOf_cons (base : Word) (w : Word) (ws : List Word) :
    cellsOf base (w :: ws) = ((base ↦ₘ w) ** cellsOf (base + 8) ws) := rfl

theorem cellsOf_append (base : Word) (xs ys : List Word) :
    cellsOf base (xs ++ ys) =
      (cellsOf base xs ** cellsOf (base + BitVec.ofNat 64 (8 * xs.length)) ys) := by
  induction xs generalizing base with
  | nil =>
    simp only [List.nil_append, cellsOf, List.length_nil, sepConj_emp_left']
    rw [show base + BitVec.ofNat 64 (8 * 0) = base from by bv_omega]
  | cons x xs ih =>
    simp only [List.cons_append, cellsOf_cons, List.length_cons, ih]
    rw [show (base + 8) + BitVec.ofNat 64 (8 * xs.length) =
        base + BitVec.ofNat 64 (8 * (xs.length + 1)) from by bv_omega]
    rw [sepConj_assoc']

theorem cellsOf_snoc_split (base : Word) (low : List Word) (a : Word)
    (done : List Word) :
    cellsOf base (low ++ a :: done) =
      (cellsOf base low ** ((base + BitVec.ofNat 64 (8 * low.length)) ↦ₘ a) **
        cellsOf (base + BitVec.ofNat 64 (8 * (low.length + 1))) done) := by
  rw [cellsOf_append base low (a :: done), cellsOf_cons]
  rw [show (base + BitVec.ofNat 64 (8 * low.length)) + 8 =
      base + BitVec.ofNat 64 (8 * (low.length + 1)) from by bv_omega]

/-- The cell chain is exactly the little-endian byte region of the limbs. -/
theorem cellsOf_eq_bytesRegion (base : Word) (ws : List Word) :
    cellsOf base ws = bytesRegion base (limbsBytes ws) := by
  induction ws generalizing base with
  | nil => rfl
  | cons w ws ih =>
    rw [show limbsBytes (w :: ws) = limbBytes w ++ limbsBytes ws from rfl]
    have hlen : (limbBytes w ++ limbsBytes ws).length = 8 * (ws.length + 1) := by
      rw [List.length_append, limbBytes_length, limbsBytes_length]
      omega
    have hdiv : (8 * (ws.length + 1) + 7) / 8 = ws.length + 1 := by omega
    have hdiv2 : ((limbsBytes ws).length + 7) / 8 = ws.length := by
      rw [limbsBytes_length]
      omega
    rw [bytesRegion, hlen, hdiv]
    rw [show bytesRegionAux base (ws.length + 1) (limbBytes w ++ limbsBytes ws) =
        ((base ↦ₘ packBytes ((limbBytes w ++ limbsBytes ws).take 8)) **
          bytesRegionAux (base + 8) ws.length
            ((limbBytes w ++ limbsBytes ws).drop 8)) from rfl]
    have htake : (limbBytes w ++ limbsBytes ws).take 8 = limbBytes w := by
      rw [List.take_append_of_le_length (by rw [limbBytes_length]),
        List.take_of_length_le (by rw [limbBytes_length])]
    have hdrop : (limbBytes w ++ limbsBytes ws).drop 8 = limbsBytes ws := by
      rw [List.drop_append_of_le_length (by rw [limbBytes_length]),
        show (limbBytes w).drop 8 = ([] : List (BitVec 8)) from
          List.drop_eq_nil_of_le (by rw [limbBytes_length]), List.nil_append]
    rw [htake, hdrop, packBytes_limbBytes, cellsOf_cons, ih (base + 8), bytesRegion,
      hdiv2]

theorem cellsOf_imp_cellsOwn (base : Word) (ws : List Word) :
    ∀ h, cellsOf base ws h → cellsOwn base ws.length h := by
  induction ws generalizing base with
  | nil =>
    intro h hh
    exact hh
  | cons w ws ih =>
    intro h hh
    obtain ⟨h1, h2, hd, hu, hw, hrest⟩ := hh
    exact ⟨h1, h2, hd, hu, ⟨w, hw⟩, ih (base + 8) h2 hrest⟩

theorem bytesRegion_imp_cellsOwn (base : Word) (bs : List (BitVec 8)) (k : Nat)
    (hlen : bs.length = 8 * k) :
    ∀ h, bytesRegion base bs h → cellsOwn base k h := by
  induction k generalizing base bs with
  | zero =>
    intro h hh
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    exact hh
  | succ k ih =>
    intro h hh
    have hdiv : (bs.length + 7) / 8 = k + 1 := by omega
    rw [bytesRegion, hdiv] at hh
    rw [show bytesRegionAux base (k + 1) bs =
        ((base ↦ₘ packBytes (bs.take 8)) ** bytesRegionAux (base + 8) k (bs.drop 8))
        from rfl] at hh
    obtain ⟨h1, h2, hd, hu, hw, hrest⟩ := hh
    refine ⟨h1, h2, hd, hu, ⟨packBytes (bs.take 8), hw⟩, ?_⟩
    have hlen' : (bs.drop 8).length = 8 * k := by
      rw [List.length_drop]
      omega
    have hdiv' : ((bs.drop 8).length + 7) / 8 = k := by omega
    rw [show bytesRegionAux (base + 8) k (bs.drop 8) =
        bytesRegion (base + 8) (bs.drop 8) from by
      rw [bytesRegion, hdiv']] at hrest
    exact ih (base + 8) (bs.drop 8) hlen' h2 hrest

/-- The six-cell chain, unfolded for `xperm`. -/
theorem cellsOf_six (base : Word) (w0 w1 w2 w3 w4 w5 : Word) :
    cellsOf base [w0, w1, w2, w3, w4, w5] =
      ((base ↦ₘ w0) ** ((base + 8 ↦ₘ w1) ** ((base + 16 ↦ₘ w2) **
        ((base + 24 ↦ₘ w3) ** ((base + 32 ↦ₘ w4) ** (base + 40 ↦ₘ w5)))))) := by
  funext h
  simp only [cellsOf, sepConj_emp_right']
  rw [show (base + 8) + 8 = base + 16 from by bv_omega,
    show (base + 16) + 8 = base + 24 from by bv_omega,
    show (base + 24) + 8 = base + 32 from by bv_omega,
    show (base + 32) + 8 = base + 40 from by bv_omega]

/-- The six-cell ownership chain, unfolded for `xperm`. -/
theorem cellsOwn_six (base : Word) :
    cellsOwn base 6 =
      (memOwn base ** (memOwn (base + 8) ** (memOwn (base + 16) **
        (memOwn (base + 24) ** (memOwn (base + 32) ** memOwn (base + 40)))))) := by
  funext h
  simp only [cellsOwn, sepConj_emp_right']
  rw [show (base + 8) + 8 = base + 16 from by bv_omega,
    show (base + 16) + 8 = base + 24 from by bv_omega,
    show (base + 24) + 8 = base + 32 from by bv_omega,
    show (base + 32) + 8 = base + 40 from by bv_omega]

end EvmAsm.Codegen.AmsterdamBlobGasPrice
