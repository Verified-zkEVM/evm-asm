/-
  EvmAsm.Rv64.RLP.Phase2LongLoopGeneral

  EL.3 Phase 2 (long form) — foundations for the general n-iteration closure
  of the long-form length loop:
    * parametric counter arithmetic (the documented `BitVec.ofNat n` blocker),
    * the loop accumulator `rlpLoopAcc` and the byte list `rlpLoopByteList`
      (both advancing `ptr` by `+1`, matching the loop body), and
    * `rlpLoopAcc_zero_eq_fromBytesBE`: the accumulator started at `0` decodes
      to the pure-spec `Nat.fromBytesBE` of the bytes read (for `n ≤ 8`,
      i.e. no 64-bit overflow).

  These are the reusable substrate for the operational (cpsTriple) general loop
  closure that a unified single-item decoder applies at the runtime
  length-of-length.
-/

import EvmAsm.Rv64.RLP.Phase2LongLoopOne
import EvmAsm.Rv64.RLP.Phase2LongLengthBridge
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

-- ============================================================================
-- Parametric counter arithmetic
-- ============================================================================

/-- The loop's counter decrement, parametric in `n`: `(n+1) - 1 = n` as words. -/
theorem word_ofNat_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- A successor counter `n+1 ≤ 2^64-1` is nonzero as a word (loop guard). -/
theorem word_ofNat_succ_ne_zero (n : Nat) (h : n + 1 < 18446744073709551616) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  have ht : (BitVec.ofNat 64 (n + 1) : Word).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat]; omega
  intro hc
  rw [hc] at ht
  simp at ht

/-- `ofNat (i+1) = ofNat i + 1` as words — for pointer/counter re-indexing. -/
theorem word_ofNat_add_one (i : Nat) :
    BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 i + 1 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

-- ============================================================================
-- Loop accumulator and byte list (both advance `ptr` by +1, as the body does)
-- ============================================================================

/-- `x11` after `n` iterations of the loop body starting from `(len, ptr)`:
    each step shifts left a byte and adds `mem[ptr]`, advancing `ptr`. -/
def rlpLoopAcc (wordVal : Word) : Word → Word → Nat → Word
  | len, _,   0       => len
  | len, ptr, (k + 1) =>
      rlpLoopAcc wordVal
        ((len <<< 8) + (extractByte wordVal (byteOffset ptr)).zeroExtend 64)
        (ptr + 1) k

/-- One-step unfolding equations for `rlpLoopAcc` (used for `rw`, since a bare
    `rfl` on a symbolic count loops). -/
theorem rlpLoopAcc_zero (wordVal len ptr : Word) :
    rlpLoopAcc wordVal len ptr 0 = len := rfl

theorem rlpLoopAcc_succ (wordVal len ptr : Word) (k : Nat) :
    rlpLoopAcc wordVal len ptr (k + 1)
      = rlpLoopAcc wordVal
          ((len <<< 8) + (extractByte wordVal (byteOffset ptr)).zeroExtend 64)
          (ptr + 1) k := rfl

/-- The `n` bytes read by the loop from `ptr`, most-significant (first read)
    first — structurally aligned with `rlpLoopAcc`. -/
def rlpLoopByteList (wordVal : Word) : Word → Nat → List EvmAsm.EL.RLP.Byte
  | _,   0       => []
  | ptr, (k + 1) => extractByte wordVal (byteOffset ptr)
                      :: rlpLoopByteList wordVal (ptr + 1) k

theorem rlpLoopByteList_length (wordVal ptr : Word) (n : Nat) :
    (rlpLoopByteList wordVal ptr n).length = n := by
  induction n generalizing ptr with
  | zero => rfl
  | succ k ih => simp [rlpLoopByteList, ih]

-- ============================================================================
-- Bridge: rlpLoopAcc (from 0) decodes to the pure-spec Nat.fromBytesBE
-- ============================================================================

/-- Mod-form accumulator invariant: after `n` iterations from `(len, ptr)`,
    `x11 = (len * 256^n + fromBytesBE bytes) mod 2^64`. -/
theorem rlpLoopAcc_toNat (wordVal : Word) (n : Nat) (len ptr : Word) :
    (rlpLoopAcc wordVal len ptr n).toNat
      = (len.toNat * 256 ^ n
          + Nat.fromBytesBE (rlpLoopByteList wordVal ptr n)) % 2 ^ 64 := by
  induction n generalizing len ptr with
  | zero =>
    simp only [rlpLoopAcc, rlpLoopByteList, Nat.fromBytesBE, pow_zero, Nat.mul_one,
      Nat.add_zero]
    exact (Nat.mod_eq_of_lt len.isLt).symm
  | succ k ih =>
    rw [rlpLoopAcc, ih,
        show rlpLoopByteList wordVal ptr (k + 1)
          = extractByte wordVal (byteOffset ptr)
              :: rlpLoopByteList wordVal (ptr + 1) k from rfl,
        show Nat.fromBytesBE (extractByte wordVal (byteOffset ptr)
              :: rlpLoopByteList wordVal (ptr + 1) k)
          = (extractByte wordVal (byteOffset ptr)).toNat
              * 256 ^ (rlpLoopByteList wordVal (ptr + 1) k).length
            + Nat.fromBytesBE (rlpLoopByteList wordVal (ptr + 1) k) from rfl,
        rlpLoopByteList_length]
    -- First-iteration accumulator value, mod 2^64.
    have hlen' :
        ((len <<< 8) + (extractByte wordVal (byteOffset ptr)).zeroExtend 64).toNat
          ≡ len.toNat * 256 + (extractByte wordVal (byteOffset ptr)).toNat
            [MOD 2 ^ 64] := by
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
        Nat.shiftLeft_eq, show (2 : Nat) ^ 8 = 256 from rfl]
      calc (len.toNat * 256 % 2 ^ 64
              + (extractByte wordVal (byteOffset ptr)).toNat % 2 ^ 64) % 2 ^ 64
          ≡ len.toNat * 256 % 2 ^ 64
              + (extractByte wordVal (byteOffset ptr)).toNat % 2 ^ 64 [MOD 2 ^ 64] :=
            Nat.mod_modEq _ _
        _ ≡ len.toNat * 256 + (extractByte wordVal (byteOffset ptr)).toNat [MOD 2 ^ 64] :=
            Nat.ModEq.add (Nat.mod_modEq _ _) (Nat.mod_modEq _ _)
    -- Big-endian step: shift the running value, add the new byte.
    have h1 := (hlen'.mul_right (256 ^ k)).add_right
      (Nat.fromBytesBE (rlpLoopByteList wordVal (ptr + 1) k))
    have h2 : (len.toNat * 256 + (extractByte wordVal (byteOffset ptr)).toNat) * 256 ^ k
            + Nat.fromBytesBE (rlpLoopByteList wordVal (ptr + 1) k)
          = len.toNat * 256 ^ (k + 1)
            + ((extractByte wordVal (byteOffset ptr)).toNat * 256 ^ k
              + Nat.fromBytesBE (rlpLoopByteList wordVal (ptr + 1) k)) := by ring
    rw [h2] at h1
    exact h1

/-- `rlpLoopAcc 0 ptr n = ofNat (fromBytesBE (byteList))`: the accumulator
    started at `0` decodes to the pure-spec big-endian value (both sides are the
    mod-`2^64` truncation, so this holds for every `n`; for `n ≤ 8` the value is
    `< 2^64` and the truncation is the identity). -/
theorem rlpLoopAcc_zero_eq_fromBytesBE (wordVal ptr : Word) (n : Nat) :
    rlpLoopAcc wordVal 0 ptr n
      = BitVec.ofNat 64 (Nat.fromBytesBE (rlpLoopByteList wordVal ptr n)) := by
  apply BitVec.eq_of_toNat_eq
  rw [rlpLoopAcc_toNat, BitVec.toNat_ofNat,
    show ((0 : Word).toNat) = 0 from rfl, Nat.zero_mul, Nat.zero_add]

-- ============================================================================
-- General n-iteration closure (operational cpsTriple, by induction)
-- ============================================================================

/-- Loop closure for an arbitrary iteration count `n = k + 1 ∈ [1,8]`, general
    accumulator `len`. Proved by induction on `k`: the do-while runs the body
    once then BNEs, so entry counter `k+1` ⇒ exactly `k+1` iterations. -/
theorem rlp_phase2_long_loop_succ_spec_within (k : Nat) (hk : k + 1 ≤ 8)
    (len ptr v12Old wordVal dwordAddr base : Word) (back : BitVec 13)
    (hwin : ∀ i, i < k + 1 →
        alignToDword (ptr + BitVec.ofNat 64 i) = dwordAddr
        ∧ isValidByteAccess (ptr + BitVec.ofNat 64 i) = true)
    (hback : (base + 20) + signExtend13 back = base) :
    cpsTripleWithin (6 * (k + 1)) base (base + 24)
      (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ BitVec.ofNat 64 (k + 1)) **
       (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
      ((.x11 ↦ᵣ rlpLoopAcc wordVal len ptr (k + 1)) **
       (.x13 ↦ᵣ (ptr + BitVec.ofNat 64 (k + 1))) ** (.x14 ↦ᵣ (0 : Word)) **
       (.x12 ↦ᵣ
         (extractByte wordVal (byteOffset (ptr + BitVec.ofNat 64 k))).zeroExtend 64) **
       (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
  induction k generalizing len ptr v12Old with
  | zero =>
    obtain ⟨ha0, hv0⟩ := hwin 0 (by omega)
    rw [show (ptr + BitVec.ofNat 64 0) = ptr by simp] at ha0 hv0
    have one := rlp_phase2_long_loop_one_byte_spec_within len ptr v12Old wordVal
      dwordAddr base back ha0 hv0
    simp only [rlp_phase2_long_loop_one_byte_post_unfold] at one
    rw [rlpLoopAcc_succ, rlpLoopAcc_zero,
        show (BitVec.ofNat 64 (0 + 1) : Word) = 1 from rfl,
        show (ptr + BitVec.ofNat 64 0) = ptr by simp]
    exact one
  | succ k ih =>
    obtain ⟨ha0, hv0⟩ := hwin 0 (by omega)
    rw [show (ptr + BitVec.ofNat 64 0) = ptr by simp] at ha0 hv0
    have body := rlp_phase2_long_loop_body_spec_within len ptr
      (BitVec.ofNat 64 (k + 1 + 1)) v12Old wordVal dwordAddr base back ha0 hv0
    rw [word_ofNat_succ_dec (k + 1)] at body
    have hne : BitVec.ofNat 64 (k + 1) ≠ (0 : Word) :=
      word_ofNat_succ_ne_zero k (by omega)
    have h_absurd : ∀ hp,
        rlp_phase2_long_loop_body_post len ptr (BitVec.ofNat 64 (k + 1 + 1))
          ((extractByte wordVal (byteOffset ptr)).zeroExtend 64)
          wordVal dwordAddr ((BitVec.ofNat 64 (k + 1) : Word) = 0) hp → False :=
      fun hp hpost => absurd (rlp_phase2_long_loop_body_post_pure hp hpost) hne
    have tri1 := cpsBranchWithin_takenPath body h_absurd
    rw [hback] at tri1
    have tri1' : cpsTripleWithin 6 base base
        (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
        ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ BitVec.ofNat 64 (k + 1 + 1)) **
         (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
        ((.x11 ↦ᵣ ((len <<< 8) + (extractByte wordVal (byteOffset ptr)).zeroExtend 64)) **
         (.x13 ↦ᵣ (ptr + 1)) **
         (.x14 ↦ᵣ BitVec.ofNat 64 (k + 1)) **
         (.x12 ↦ᵣ (extractByte wordVal (byteOffset ptr)).zeroExtend 64) **
         (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) :=
      cpsTripleWithin_weaken
        (fun _ hp => hp)
        (fun h hp => by
          simp only [rlp_phase2_long_loop_body_post_unfold] at hp
          rw [word_ofNat_succ_dec (k + 1)] at hp
          open EvmAsm.Rv64.Tactics in xperm_pure hp)
        tri1
    have hwin' : ∀ i, i < k + 1 →
        alignToDword ((ptr + 1) + BitVec.ofNat 64 i) = dwordAddr
        ∧ isValidByteAccess ((ptr + 1) + BitVec.ofNat 64 i) = true := by
      intro i hi
      have h := hwin (i + 1) (by omega)
      rwa [word_ofNat_add_one i,
        show (ptr + (BitVec.ofNat 64 i + 1)) = (ptr + 1) + BitVec.ofNat 64 i by bv_omega] at h
    have ihspec := ih (by omega)
      ((len <<< 8) + (extractByte wordVal (byteOffset ptr)).zeroExtend 64)
      (ptr + 1) ((extractByte wordVal (byteOffset ptr)).zeroExtend 64) hwin'
    have composed :=
      cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) tri1' ihspec
    rw [show (6 * (k + 1 + 1)) = 6 + 6 * (k + 1) by ring,
        rlpLoopAcc_succ wordVal len ptr (k + 1),
        show (ptr + BitVec.ofNat 64 (k + 1 + 1)) = (ptr + 1) + BitVec.ofNat 64 (k + 1) by
          rw [word_ofNat_add_one (k + 1)]; bv_omega,
        show (extractByte wordVal (byteOffset (ptr + BitVec.ofNat 64 (k + 1)))).zeroExtend 64
          = (extractByte wordVal (byteOffset ((ptr + 1) + BitVec.ofNat 64 k))).zeroExtend 64 by
          rw [word_ofNat_add_one k,
            show (ptr + (BitVec.ofNat 64 k + 1)) = (ptr + 1) + BitVec.ofNat 64 k by bv_omega]]
    exact composed

/-- General `n ∈ [1,8]` loop closure, accumulator started at `0`, decoded length
    stated against the pure spec `Nat.fromBytesBE`. The form a unified
    single-item decoder applies at the runtime length-of-length. -/
theorem rlp_phase2_long_loop_n_byte_spec_within (n : Nat) (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (ptr v12Old wordVal dwordAddr base : Word) (back : BitVec 13)
    (hwin : ∀ i, i < n →
        alignToDword (ptr + BitVec.ofNat 64 i) = dwordAddr
        ∧ isValidByteAccess (ptr + BitVec.ofNat 64 i) = true)
    (hback : (base + 20) + signExtend13 back = base) :
    cpsTripleWithin (6 * n) base (base + 24)
      (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ BitVec.ofNat 64 n) **
       (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
      ((.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (rlpLoopByteList wordVal ptr n))) **
       (.x13 ↦ᵣ (ptr + BitVec.ofNat 64 n)) ** (.x14 ↦ᵣ (0 : Word)) **
       (.x12 ↦ᵣ
         (extractByte wordVal (byteOffset (ptr + BitVec.ofNat 64 (n - 1)))).zeroExtend 64) **
       (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have core := rlp_phase2_long_loop_succ_spec_within k hn8 0 ptr v12Old wordVal
    dwordAddr base back hwin hback
  rw [rlpLoopAcc_zero_eq_fromBytesBE wordVal ptr (k + 1)] at core
  rw [show (k + 1 - 1) = k from rfl]
  exact core

-- Sanity: the parametric closure instantiated at `n = 3` matches the shape of
-- the hand-unrolled three-byte closure (same 18-step bound, `base → base+24`).
example : (6 * 3) = 18 := rfl

end EvmAsm.Rv64.RLP
