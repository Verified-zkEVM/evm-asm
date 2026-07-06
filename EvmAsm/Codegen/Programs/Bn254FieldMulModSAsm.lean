/-
  EvmAsm.Codegen.Programs.Bn254FieldMulModSAsm

  Infrastructure for the verified SAsm port of `bnfMulModP`: the bn254
  base-field modular multiply `(a · b) mod p_bn254`.

  The routine composes the two verified converters (`bnfBeToLe` / `bnfLeToBe`,
  #9858/#9875) around the `Arith256Mod` accelerator handle (`.11.6 arithModHandle`):
    bnfBeToLe(a0 → bnf_le_a) → bnfBeToLe(a1 → bnf_le_b) →
    arithModHandle → bnfLeToBe(bnf_le_d → output).

  This file provides the arithmetic bridge (the accelerator's result, read
  through the bn254 modulus, equals the genuine modular product in the
  `Accel`/`.38.1` Nat vocabulary).  The full VC proof (composing the
  converter retSpecs + the accelerator handle via framed FnHandleS over
  the 272-byte data window) is WIP.

  Handle instantiation check (no mismatch): the arithModHandle's
  decode-valued post writes `Accel.arith256Mod(wsNat aOff, wsNat bOff,
  wsNat cOff, wsNat mOff)` to `dOff`.  With bn254 mul params:
    aOff=0(bnf_le_a), bOff=32(bnf_le_b), cOff=96(bnf_le_zero=0),
    mOff=160(bnf_le_p=p), dOff=64(bnf_le_d).
  This gives `(A·B + 0) mod p` — exactly the intended modular product.
-/

import EvmAsm.Rv64.SAsm.AccelStep
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Bn254Field
import EvmAsm.Codegen.Programs.Bn254FieldConvSAsm

namespace EvmAsm.Codegen
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

-- ============================================================================
-- Constants
-- ============================================================================

/-- The bn254 base-field prime p. -/
def p_bn254 : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- Window offsets (from `bnf_le_a`). -/
def offA : Nat := 0      -- bnf_le_a
def offB : Nat := 32     -- bnf_le_b
def offD : Nat := 64     -- bnf_le_d
def offZero : Nat := 96  -- bnf_le_zero (c-slot = 0 for mul)
def offOne : Nat := 128  -- bnf_le_one  (b-slot = 1 for add)
def offP : Nat := 160    -- bnf_le_p
def offMulParams : Nat := 192  -- bnf_mul_params (5 × 8-byte pointers)
def winLen : Nat := 272       -- total window size

-- ============================================================================
-- Arithmetic bridge
-- ============================================================================

/-- The accelerator's result, read through the bn254 modulus, equals the
    genuine modular product in the Nat vocabulary.  This is the key
    arithmetic identity that connects `Accel.arith256Mod` (the accelerator's
    decode-valued post) to the spec's `(A·B) mod p_bn254`. -/
theorem arith256Mod_bn254_mul_eq (bytesA bytesB : List (BitVec 8)) :
    Accel.arith256Mod (beBytesToNat bytesA) (beBytesToNat bytesB) 0 p_bn254
    = (beBytesToNat bytesA * beBytesToNat bytesB) % p_bn254 := by
  -- Accel.arith256Mod a b c m = (a * b + c) % m by definition
  rfl

-- ============================================================================
-- WIP: the full VC proof
-- ============================================================================
--
-- The remaining work to complete `bnfMulModPFn_spec`:
--
-- 1. Framed converter handles: FnHandleS for bnfBeToLe/bnfLeToBe with
--    region/rw = the caller's full window, derived from the converter
--    specs via the frame rule.
--
-- 2. arithModHandle instance: arithModHandle .w256 accelEntry .x5 with
--    pOff=offMulParams, aOff=offA, bOff=offB, cOff=offZero, mOff=offP,
--    dOff=offD.
--
-- 3. SAsm body: prologue + .callRegS(be2le_a) + inter + .callRegS(be2le_b)
--    + accel_setup + .callRegS(accel) + post-accel + .callRegS(le2be) +
--    epilogue.
--
-- 4. Fn.SpecR via vcgen, closing the post with:
--    beBytesToNat(output) = (beBytesToNat(A) · beBytesToNat(B)) mod p_bn254
--    via the converter specs + arith256Mod_bn254_mul_eq.

end EvmAsm.Codegen
