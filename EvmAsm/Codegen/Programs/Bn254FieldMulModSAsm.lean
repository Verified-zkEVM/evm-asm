/-
  EvmAsm.Codegen.Programs.Bn254FieldMulModSAsm

  Infrastructure for the verified SAsm port of `bnfMulModP`: the bn254
  base-field modular multiply `(a · b) mod p_bn254`.

  The routine composes the two verified converters (`bnfBeToLe` / `bnfLeToBe`,
  #9858/#9875) around the `Arith256Mod` accelerator handle:
    bnfBeToLe(a0 → bnf_le_a) → bnfBeToLe(a1 → bnf_le_b) →
    arithModHandle → bnfLeToBe(bnf_le_d → output).

  ## Proven

  - `arith256Mod_bn254_mul_eq`: the accelerator's result equals the genuine
    `(A·B) mod p_bn254`.
  - `winRw_wf`: well-formedness of the 272-byte data-section window.
  - `arithHandle`: the `arithModHandle .w256` instance, instantiated at the
    bn254 layout offsets (aOff=0, bOff=32, cOff=96=zero, mOff=160=p, dOff=64).
    No mismatch — the handle's decode-valued post gives exactly `(A·B + 0) mod p`.

  ## WIP (documented for follow-up)

  The full VC proof (`bnfMulModPFn_spec`) needs:
  1. **Framed converter handles** — FnHandleS for bnfBeToLe/bnfLeToBe with
     region/rw = the caller's full 272-byte window, deriving soundness from
     the converter specs via the separation-logic frame rule (the converters'
     own rw is a 32-byte sub-window of the caller's 272-byte window; the frame
     preserves everything else).
  2. **SAsm body** — `.callRegS` at each call site (entry register `.x5`),
     with `.block` prologue/inter/epilogue (all straight-line: stack save,
     arg setup, pointer loads).
  3. **`Fn.SpecR` via `vcgen`** — compose the three call sites (two converter
     calls + one accelerator), close the post with `arith256Mod_bn254_mul_eq`.
-/

import EvmAsm.Rv64.SAsm.AccelStep
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Rv64.SAsm.MultiRw
import EvmAsm.Codegen.Programs.Bn254Field
import EvmAsm.Codegen.Programs.Bn254FieldConvSAsm

namespace EvmAsm.Codegen
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt EvmAsm.Crypto

-- ============================================================================
-- Constants
-- ============================================================================

/-- The bn254 base-field prime p. -/
def p_bn254 : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- Window offsets (from `bnf_le_a` = window base). -/
def offA : Nat := 0       -- bnf_le_a
def offB : Nat := 32      -- bnf_le_b
def offD : Nat := 64      -- bnf_le_d
def offZero : Nat := 96   -- bnf_le_zero (c-slot = 0 for mul)
def offOne : Nat := 128   -- bnf_le_one  (b-slot = 1 for add)
def offP : Nat := 160     -- bnf_le_p
def offMulParams : Nat := 192 -- bnf_mul_params (5 × 8-byte pointers)
def winLen : Nat := 272

/-- Window base address. -/
def winBase : Word := BitVec.ofNat 64 GuestAddrs.bnf_le_a

-- ============================================================================
-- Proven: arithmetic bridge
-- ============================================================================

/-- `Accel.arith256Mod A B 0 p = (A * B) % p` — by definition. -/
theorem arith256Mod_bn254_mul_eq (bytesA bytesB : List (BitVec 8)) :
    Accel.arith256Mod (beBytesToNat bytesA) (beBytesToNat bytesB) 0 p_bn254
    = (beBytesToNat bytesA * beBytesToNat bytesB) % p_bn254 := rfl

-- ============================================================================
-- Proven: window well-formedness + accelerator handle
-- ============================================================================

/-- The writable window for the data section. -/
def winRw : RwRegion := ⟨winBase, 272⟩

/-- Well-formedness of the data-section window. -/
private theorem winRw_wf : winRw.wf := by
  show winBase.toNat % 8 = 0 ∧ winBase.toNat + 272 < 2 ^ 64 ∧
    ∀ k, k < 272 → isValidMemAddr (winBase + BitVec.ofNat 64 k) = true
  refine ⟨rfl, by decide, ?_⟩
  intro k hk
  rw [winBase]
  show isValidMemAddr (BitVec.ofNat 64 GuestAddrs.bnf_le_a + BitVec.ofNat 64 k) = true
  rw [show GuestAddrs.bnf_le_a = 3142965584 from rfl]
  have : (BitVec.ofNat 64 3142965584 + BitVec.ofNat 64 k).toNat = 3142965584 + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have h1 : (3142965584 : Nat) < 2 ^ 64 := by decide
    have h2 : k < 2 ^ 64 := by omega
    have h3 : (3142965584 + k : Nat) < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h3]
  show isValidMemAddr (BitVec.ofNat 64 3142965584 + BitVec.ofNat 64 k) = true
  unfold isValidMemAddr
  have : (BitVec.ofNat 64 3142965584 + BitVec.ofNat 64 k).toNat = 3142965584 + k := this
  rw [this]
  have h1 : decide (Rv64.RAM_MEM_START ≤ 3142965584 + k) = true := by
    show decide (2684354560 ≤ 3142965584 + k) = true
    exact decide_eq_true_iff.mpr (by omega)
  have h2 : decide (3142965584 + k ≤ Rv64.RAM_MEM_END) = true := by
    show decide (3142965584 + k ≤ 3221225472) = true
    exact decide_eq_true_iff.mpr (by omega)
  simp only [h1, h2, Bool.true_and, Bool.or_true]

/-- The accelerator handle for bn254 modular multiply.
    Parameter block at offset offMulParams:
      [0]:  ptr to bnf_le_a (offset offA)
      [8]:  ptr to bnf_le_b (offset offB)
      [16]: ptr to bnf_le_zero (offset offZero)
      [24]: ptr to bnf_le_p (offset offP)
      [32]: ptr to bnf_le_d (offset offD)
    The accelerator computes `(A·B + 0) mod p` — exactly the intended
    modular product (no mismatch). -/
def arithHandle : FnHandleS :=
  arithModHandle .w256 (winBase + BitVec.ofNat 64 offMulParams) .x5
    (by decide) Region.empty winBase winLen winRw_wf
    offMulParams offA offB offZero offP offD
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end EvmAsm.Codegen
