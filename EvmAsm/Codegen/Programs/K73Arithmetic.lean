/-
  Arithmetic bridge for the K73 whole-routine contract.

  The linked divider writes one quotient byte per iteration.  This file
  records the kernel-checked bridge from that state machine to the reference
  big-endian quotient, so the route post can expose the actual bytes produced
  by the machine rather than reusing an input/output witness.
-/

import EvmAsm.Codegen.Programs.U256DivU64BeSAsm
import EvmAsm.EL.RLP.Properties
import EvmAsm.Stateless.SpecRef.Crypto
import EvmAsm.Rv64.RemuNat
import EvmAsm.Evm64.EvmWordArith.KnuthTheoremB
import EvmAsm.Crypto.BeBytesArith

namespace EvmAsm.Codegen.HeaderBaseFeeSpec

open EvmAsm.Codegen
open EvmAsm.Codegen.U256DivU64BeSAsm

theorem k73_div_test_num_eq (rem : Word) (byte : BitVec 8)
    (hrem : rem.toNat < 2 ^ 56) :
    ((rem <<< (8 : Nat)) ||| byte.zeroExtend 64) =
      BitVec.ofNat 64 (rem.toNat * 256 + byte.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hshift : rem.toNat <<< 8 < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 8 = 256 by norm_num]
    nlinarith [hrem]
  rw [Nat.mod_eq_of_lt hshift]
  have hbyte : byte.toNat % 2 ^ 64 = byte.toNat :=
    Nat.mod_eq_of_lt (by omega)
  rw [hbyte]
  rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.shiftLeft_eq]
  have hsum : rem.toNat <<< 8 + byte.toNat < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hsum]
  rw [← Nat.shiftLeft_add_eq_or_of_lt byte.isLt]

theorem k73_natToBytesBE_succ (k n : Nat) :
    EvmAsm.Stateless.SpecRef.natToBytesBE (k + 1) n =
      EvmAsm.Stateless.SpecRef.natToBytesBE k (n / 256) ++
        [BitVec.ofNat 8 (n % 256)] := by
  induction k generalizing n with
  | zero =>
      simp only [Nat.zero_add]
      change [BitVec.ofNat 8 (n >>> 0)] =
        EvmAsm.Stateless.SpecRef.natToBytesBE 0 (n / 256) ++
          [BitVec.ofNat 8 (n % 256)]
      simp only [EvmAsm.Stateless.SpecRef.natToBytesBE, List.range_zero,
        Nat.shiftRight_zero]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp
  | succ k ih =>
      have hshift : n >>> (8 * (k + 1)) = (n / 256) >>> (8 * k) := by
        rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
        rw [Nat.mul_add, Nat.pow_add]
        norm_num
        rw [Nat.div_div_eq_div_mul]
        rw [Nat.mul_comm (2 ^ (8 * k)) 256]
      have hhead (m x : Nat) :
          EvmAsm.Stateless.SpecRef.natToBytesBE (m + 1) x =
            BitVec.ofNat 8 (x >>> (8 * m)) ::
              EvmAsm.Stateless.SpecRef.natToBytesBE m x := by
        simp [EvmAsm.Stateless.SpecRef.natToBytesBE, List.range_succ,
          List.reverse_append]
      rw [hhead (k + 1) n, hhead k (n / 256), hshift, ih]
      rfl

/-! The current divider performs a restoring bit loop inside each byte.  These
    lemmas expose the arithmetic of that loop without reverting the model to
    the old single DIVU/REMU step. -/

def k73_bitPrefix (byte : Word) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      (((byte >>> 7) &&& (1 : Word)).toNat) * 2 ^ n +
        k73_bitPrefix (byte <<< 1) n

theorem k73_shift_or_num (x y : Word) (hy : y.toNat < 2)
    (hx : x.toNat * 2 < 2 ^ 64) :
    (x <<< 1 ||| y).toNat = x.toNat * 2 + y.toNat := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft]
  have hsh : x.toNat <<< 1 = x.toNat * 2 := by rw [Nat.shiftLeft_eq]
  rw [hsh, Nat.mod_eq_of_lt hx, ← hsh,
    ← Nat.shiftLeft_add_eq_or_of_lt hy]

theorem k73_div_bit_step_num (bit b rem : Word)
    (hbit : bit.toNat ≤ 1) (hb : b ≠ 0)
    (hrem : rem.toNat < b.toNat)
    (hbnd : b.toNat ≤ 2 ^ 56) :
    (divBitStep bit b rem).1.toNat =
        (rem.toNat * 2 + bit.toNat) / b.toNat ∧
    (divBitStep bit b rem).2.toNat =
        (rem.toNat * 2 + bit.toNat) % b.toNat := by
  have hbitlt : bit.toNat < 2 := by omega
  have hshift : (rem <<< 1 ||| bit).toNat =
      rem.toNat * 2 + bit.toNat :=
    k73_shift_or_num rem bit hbitlt (by omega)
  have hhigh : (rem >>> 63).toNat = 0 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    apply Nat.div_eq_of_lt
    omega
  have hhighWord : rem >>> 63 = (0 : Word) :=
    BitVec.eq_of_toNat_eq hhigh
  by_cases hlt : (rem <<< 1 ||| bit).ult b = true
  · have hstep :
        divBitStep bit b rem = ((0 : Word), rem <<< 1 ||| bit) := by
      unfold divBitStep
      simp [hlt, hhighWord]
    rw [hstep]
    change (0 : Word).toNat = _ ∧ (rem <<< 1 ||| bit).toNat = _
    have hnumlt : rem.toNat * 2 + bit.toNat < b.toNat := by
      rw [← hshift]
      exact BitVec.ult_iff_toNat_lt.mp hlt
    constructor
    · simp
      rw [Nat.div_eq_of_lt hnumlt]
    · rw [hshift]
      exact (Nat.mod_eq_of_lt hnumlt).symm
  · have hltNat : ¬ (rem <<< 1 ||| bit).toNat < b.toNat := by
      intro h
      apply hlt
      exact BitVec.ult_iff_toNat_lt.mpr h
    have hnotNat : b.toNat ≤ (rem <<< 1 ||| bit).toNat := by omega
    have hbpos : 0 < b.toNat := by
      have hbn : b.toNat ≠ 0 := by
        intro hz
        apply hb
        exact BitVec.eq_of_toNat_eq hz
      omega
    have hnumge : b.toNat ≤ rem.toNat * 2 + bit.toNat := by
      rw [← hshift]
      exact hnotNat
    have hq : (rem.toNat * 2 + bit.toNat) / b.toNat = 1 := by
      apply (Nat.div_eq_iff hbpos).2
      constructor <;> omega
    have hstep :
        divBitStep bit b rem = ((1 : Word), (rem <<< 1 ||| bit) - b) := by
      unfold divBitStep
      simp [hlt, hhighWord]
      change b &&& BitVec.allOnes 64 = b
      exact BitVec.and_allOnes
    rw [hstep]
    change (1 : Word).toNat = _ ∧ ((rem <<< 1 ||| bit) - b).toNat = _
    constructor
    · simp
      exact hq.symm
    · rw [BitVec.toNat_sub, hshift]
      have hdiff : rem.toNat * 2 + bit.toNat - b.toNat < 2 ^ 64 := by
        omega
      have hsub :
          (2 ^ 64 - b.toNat + (rem.toNat * 2 + bit.toNat)) % 2 ^ 64 =
            rem.toNat * 2 + bit.toNat - b.toNat := by
        rw [show 2 ^ 64 - b.toNat +
            (rem.toNat * 2 + bit.toNat) =
            2 ^ 64 + (rem.toNat * 2 + bit.toNat - b.toNat) by omega]
        rw [Nat.add_mod_left]
        exact Nat.mod_eq_of_lt hdiff
      rw [hsub]
      have hdiffb : rem.toNat * 2 + bit.toNat - b.toNat < b.toNat := by
        omega
      have hmod : (rem.toNat * 2 + bit.toNat) % b.toNat =
          (rem.toNat * 2 + bit.toNat - b.toNat) % b.toNat := by
        rw [Nat.mod_eq_sub_mod hnumge]
      rw [hmod, Nat.mod_eq_of_lt hdiffb]

theorem k73_div_shift (n b c m : Nat) (hb : 0 < b) :
    (n * 2 ^ m + c) / b =
        (n / b) * 2 ^ m + (n % b * 2 ^ m + c) / b ∧
    (n * 2 ^ m + c) % b =
        (n % b * 2 ^ m + c) % b := by
  have hn : n = b * (n / b) + n % b := (Nat.div_add_mod n b).symm
  have he :
      (b * (n / b) + n % b) * 2 ^ m + c =
        b * ((n / b) * 2 ^ m) + (n % b * 2 ^ m + c) := by
    ring
  constructor
  · calc
      (n * 2 ^ m + c) / b =
          ((b * (n / b) + n % b) * 2 ^ m + c) / b := by rw [← hn]
      _ = _ := by rw [he, Nat.mul_add_div hb]
  · calc
      (n * 2 ^ m + c) % b =
          ((b * (n / b) + n % b) * 2 ^ m + c) % b := by rw [← hn]
      _ = _ := by rw [he, Nat.mul_add_mod]

theorem k73_bitPrefix_zeroExtend (byte : BitVec 8) :
    k73_bitPrefix (BitVec.zeroExtend 64 byte) 8 = byte.toNat := by
  have hbyte : byte.toNat < 256 := by omega
  interval_cases hx : byte.toNat <;>
    simp_all [k73_bitPrefix, BitVec.toNat_ushiftRight,
      BitVec.toNat_shiftLeft, BitVec.toNat_and,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]

theorem k73_div_byte_step_aux_num (byte b rem q : Word) :
    ∀ n : Nat, n ≤ 8 →
      q.toNat < 2 ^ (8 - n) →
      0 < b.toNat →
      rem.toNat < b.toNat →
      b.toNat ≤ 2 ^ 56 →
      (divByteStepAux byte b rem q n).1.toNat =
          q.toNat * 2 ^ n +
            (rem.toNat * 2 ^ n + k73_bitPrefix byte n) / b.toNat ∧
      (divByteStepAux byte b rem q n).2.toNat =
          (rem.toNat * 2 ^ n + k73_bitPrefix byte n) % b.toNat := by
  intro n
  induction n generalizing byte rem q with
  | zero =>
      intro _ hq hb hrem hbnd
      simp [divByteStepAux, k73_bitPrefix,
        Nat.div_eq_of_lt hrem, Nat.mod_eq_of_lt hrem]
  | succ n ih =>
      intro hn hq hb hrem hbnd
      let bit : Word := (byte >>> 7) &&& (1 : Word)
      have hbit : bit.toNat ≤ 1 := by
        dsimp [bit]
        simp [BitVec.toNat_ushiftRight]
        omega
      have hb0 : b ≠ 0 := by
        intro h_zero
        have hbn : b.toNat = 0 := by simp [h_zero]
        omega
      have hstep := k73_div_bit_step_num bit b rem hbit hb0 hrem hbnd
      have hbpos : 0 < b.toNat := hb
      have hnumlt2 : rem.toNat * 2 + bit.toNat < 2 * b.toNat := by
        omega
      have hquotlt :
          (rem.toNat * 2 + bit.toNat) / b.toNat < 2 := by
        exact (Nat.div_lt_iff_lt_mul hbpos).2 hnumlt2
      have hquotle :
          (rem.toNat * 2 + bit.toNat) / b.toNat ≤ 1 := by omega
      have hstepbit : (divBitStep bit b rem).1.toNat ≤ 1 := by
        rw [hstep.1]
        exact hquotle
      have hstepbitlt : (divBitStep bit b rem).1.toNat < 2 := by omega
      have hq256 : q.toNat < 256 := by
        calc
          q.toNat < 2 ^ (8 - (n + 1)) := hq
          _ ≤ 2 ^ 8 :=
            Nat.pow_le_pow_right Nat.zero_lt_two (Nat.sub_le _ _)
          _ = 256 := by norm_num
      have hqshift :
          ((q <<< 1) ||| (divBitStep bit b rem).1).toNat =
            q.toNat * 2 + (divBitStep bit b rem).1.toNat :=
        k73_shift_or_num q _ hstepbitlt (by omega)
      have hrem1 : (divBitStep bit b rem).2.toNat < b.toNat := by
        rw [hstep.2]
        exact Nat.mod_lt _ hbpos
      have hn0 : n ≤ 8 := by omega
      have hpow : 8 - n = (8 - (n + 1)) + 1 := by omega
      let c : Nat := 2 ^ (8 - (n + 1))
      have hqc : q.toNat < c := by simpa [c] using hq
      have hq2 : q.toNat * 2 + 1 < 2 * c := by omega
      have hq'c :
          q.toNat * 2 +
              (rem.toNat * 2 + bit.toNat) / b.toNat < 2 * c :=
        lt_of_le_of_lt (Nat.add_le_add_left hquotle _) hq2
      have hq' :
          q.toNat * 2 +
              (rem.toNat * 2 + bit.toNat) / b.toNat <
            2 * 2 ^ (8 - (n + 1)) := by simpa [c] using hq'c
      have hq1 :
          ((q <<< 1) ||| (divBitStep bit b rem).1).toNat <
            2 ^ (8 - n) := by
        rw [hqshift, hstep.1]
        calc
          q.toNat * 2 +
                (rem.toNat * 2 + bit.toNat) / b.toNat <
              2 * 2 ^ (8 - (n + 1)) := hq'
          _ = 2 ^ (8 - n) := by
            rw [hpow, Nat.pow_succ]
            ring
      have hih := ih (byte <<< 1) (divBitStep bit b rem).2
        ((q <<< 1) ||| (divBitStep bit b rem).1)
        hn0 hq1 hb hrem1 hbnd
      change
        (divByteStepAux (byte <<< 1) b (divBitStep bit b rem).2
          ((q <<< 1) ||| (divBitStep bit b rem).1) n).1.toNat = _ ∧
        (divByteStepAux (byte <<< 1) b (divBitStep bit b rem).2
          ((q <<< 1) ||| (divBitStep bit b rem).1) n).2.toNat = _
      rw [hih.1, hih.2]
      have hprefix :
          k73_bitPrefix byte (n + 1) =
            bit.toNat * 2 ^ n + k73_bitPrefix (byte <<< 1) n := by
        rfl
      have hdiv := k73_div_shift
        (rem.toNat * 2 + bit.toNat) b.toNat
        (k73_bitPrefix (byte <<< 1) n) n hbpos
      constructor
      · calc
          (((q <<< 1) ||| (divBitStep bit b rem).1).toNat) * 2 ^ n +
              ((divBitStep bit b rem).2.toNat * 2 ^ n +
                k73_bitPrefix (byte <<< 1) n) / b.toNat =
              q.toNat * 2 ^ (n + 1) +
                (((rem.toNat * 2 + bit.toNat) / b.toNat) * 2 ^ n +
                  ((divBitStep bit b rem).2.toNat * 2 ^ n +
                    k73_bitPrefix (byte <<< 1) n) / b.toNat) := by
                rw [hqshift, hstep.1]
                ring
          _ = q.toNat * 2 ^ (n + 1) +
                ((rem.toNat * 2 + bit.toNat) * 2 ^ n +
                  k73_bitPrefix (byte <<< 1) n) / b.toNat := by
                rw [hstep.2]
                rw [← hdiv.1]
          _ = q.toNat * 2 ^ (n + 1) +
                (rem.toNat * 2 ^ (n + 1) +
                  k73_bitPrefix byte (n + 1)) / b.toNat := by
                rw [hprefix]
                rw [Nat.pow_succ]
                ring
      · calc
          ((divBitStep bit b rem).2.toNat * 2 ^ n +
            k73_bitPrefix (byte <<< 1) n) % b.toNat =
              ((rem.toNat * 2 + bit.toNat) * 2 ^ n +
                k73_bitPrefix (byte <<< 1) n) % b.toNat := by
                  rw [hstep.2]
                  rw [← hdiv.2]
          _ = (rem.toNat * 2 ^ (n + 1) +
            k73_bitPrefix byte (n + 1)) % b.toNat := by
              rw [hprefix]
              rw [Nat.pow_succ]
              ring

theorem k73_div_byte_step_word_num (byte : BitVec 8) (b rem : Word)
    (hb : b ≠ 0) (hrem : rem.toNat < b.toNat)
    (hbnd : b.toNat ≤ 2 ^ 56) :
    (divByteStepWord byte b rem).1.toNat =
        (rem.toNat * 256 + byte.toNat) / b.toNat ∧
    (divByteStepWord byte b rem).2.toNat =
        (rem.toNat * 256 + byte.toNat) % b.toNat := by
  have hbpos : 0 < b.toNat := by
    have hb0 : b.toNat ≠ 0 := by
      intro hz
      apply hb
      exact BitVec.eq_of_toNat_eq hz
    omega
  have haux := k73_div_byte_step_aux_num
    (BitVec.zeroExtend 64 byte) b rem 0 8
    (by omega) (by simp) hbpos hrem hbnd
  have hprefix := k73_bitPrefix_zeroExtend byte
  simpa [divByteStepWord, hprefix] using haux

theorem k73_div_byte_step_num (byte : BitVec 8) (b rem : Word)
    (hb : b ≠ 0) (hrem : rem.toNat < b.toNat)
    (hbnd : b.toNat ≤ 2 ^ 56) :
    (divByteStep byte b rem).1.toNat =
        (rem.toNat * 256 + byte.toNat) / b.toNat ∧
    (divByteStep byte b rem).2.toNat =
        (rem.toNat * 256 + byte.toNat) % b.toNat := by
  have hq : (rem.toNat * 256 + byte.toNat) / b.toNat < 256 := by
    apply (Nat.div_lt_iff_lt_mul (by omega)).2
    omega
  unfold divByteStep
  constructor
  · rw [BitVec.toNat_setWidth]
    rw [(k73_div_byte_step_word_num byte b rem hb hrem hbnd).1]
    exact Nat.mod_eq_of_lt hq
  · exact (k73_div_byte_step_word_num byte b rem hb hrem hbnd).2

theorem k73_div_digit_recurrence (n b c : Nat) (hb : 0 < b) :
    (n * 256 + c) / b = (n / b) * 256 + ((n % b) * 256 + c) / b ∧
    (n * 256 + c) % b = ((n % b) * 256 + c) % b := by
  have hn : n = b * (n / b) + n % b := (Nat.div_add_mod n b).symm
  constructor
  · have he :
        (b * (n / b) + n % b) * 256 + c =
          b * ((n / b) * 256) + ((n % b) * 256 + c) := by ring
    calc
      (n * 256 + c) / b =
          ((b * (n / b) + n % b) * 256 + c) / b := by rw [← hn]
      _ = (n / b) * 256 + ((n % b) * 256 + c) / b := by
        rw [he, Nat.mul_add_div hb]
  · have he :
        (b * (n / b) + n % b) * 256 + c =
          b * ((n / b) * 256) + ((n % b) * 256 + c) := by ring
    calc
      (n * 256 + c) % b =
          ((b * (n / b) + n % b) * 256 + c) % b := by rw [← hn]
      _ = ((n % b) * 256 + c) % b := by
        rw [he, Nat.mul_add_mod]

theorem k73_set_prefix_append (q tail : List (BitVec 8)) (k : Nat)
    (hq : q.length = k) (ht : k < (q ++ tail).length) (x : BitVec 8) :
    (q ++ tail).set k x = q ++ x :: tail.drop 1 := by
  rw [List.set_eq_take_cons_drop x ht]
  rw [List.take_append_of_le_length (by omega)]
  rw [List.drop_append]
  have hqle : q.length ≤ k := by omega
  have hqdrop : k + 1 ≥ q.length := by omega
  have htq : q.take k = q := (List.take_eq_self_iff q).2 hqle
  have hdq : q.drop (k + 1) = [] := (List.drop_eq_nil_iff).2 hqdrop
  rw [htq, hdq]
  simp [hq]

theorem k73_div_byte_step_byte (byte : BitVec 8) (b rem : Word)
    (hb : b ≠ 0) (hrem : rem.toNat < b.toNat)
    (hbnd : b.toNat ≤ 2 ^ 56) :
    (divByteStep byte b rem).1 =
      BitVec.ofNat 8 ((rem.toNat * 256 + byte.toNat) / b.toNat) := by
  have hnum := k73_div_byte_step_num byte b rem hb hrem hbnd
  have hq : (rem.toNat * 256 + byte.toNat) / b.toNat < 256 := by
    apply (Nat.div_lt_iff_lt_mul (by omega)).2
    omega
  apply BitVec.eq_of_toNat_eq
  rw [hnum.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]

theorem k73_div_state_closed (a orig : List (BitVec 8)) (b : Word)
    (ha : a.length = 32) (ho : orig.length = 32)
    (hb : 0 < b.toNat) (hbnd : b.toNat ≤ 2 ^ 56) :
    ∀ k : Nat, k ≤ 32 →
      (divState a orig b k).1 =
          EvmAsm.Stateless.SpecRef.natToBytesBE k
              (EvmAsm.Crypto.beBytesToNat (a.take k) / b.toNat) ++ orig.drop k ∧
      (divState a orig b k).2.toNat =
          EvmAsm.Crypto.beBytesToNat (a.take k) % b.toNat := by
  intro k
  induction k with
  | zero =>
      intro _
      simp [divState, EvmAsm.Crypto.beBytesToNat,
        EvmAsm.Stateless.SpecRef.natToBytesBE]
  | succ k ih =>
      intro hk
      have hk0 : k ≤ 32 := by omega
      have hka : k < a.length := by rw [ha]; omega
      have htake : a.take (k + 1) = a.take k ++ [a.getD k 0] := by
        rw [List.take_succ_eq_append_getElem hka,
          List.getElem_eq_getD 0]
      have hprefix :
          EvmAsm.Crypto.beBytesToNat (a.take (k + 1)) =
            EvmAsm.Crypto.beBytesToNat (a.take k) * 256 +
              (a.getD k 0).toNat := by
        rw [htake, EvmAsm.Crypto.beBytesToNat_append]
        simp [EvmAsm.Crypto.beBytesToNat]
      have hih := ih hk0
      have hrem : (divState a orig b k).2.toNat < b.toNat := by
        rw [hih.2]
        exact Nat.mod_lt _ (by omega)
      have hrem56 : (divState a orig b k).2.toNat < 2 ^ 56 := by
        have hb_le : b.toNat ≤ 2 ^ 56 := hbnd
        omega
      have hb0 : b ≠ 0 := by
        intro hz
        subst hz
        simp at hb
      have hstep := k73_div_byte_step_num (a.getD k 0) b
        (divState a orig b k).2 hb0 hrem hbnd
      have hstepByte := k73_div_byte_step_byte (a.getD k 0) b
        (divState a orig b k).2 hb0 hrem hbnd
      change (divState a orig b k).1.set k
          (divByteStep (a.getD k 0) b (divState a orig b k).2).1 = _ ∧
        (divByteStep (a.getD k 0) b (divState a orig b k).2).2.toNat = _
      rw [hih.1]
      have hstepByte' := hstepByte
      rw [hih.2] at hstepByte'
      have hstepRem' := hstep.2
      rw [hih.2] at hstepRem'
      have hdiv := k73_div_digit_recurrence
        (EvmAsm.Crypto.beBytesToNat (a.take k)) b.toNat
        (a.getD k 0).toNat hb
      constructor
      · rw [hstepByte']
        have hqLen := EvmAsm.Stateless.SpecRef.natToBytesBE_length k
          (EvmAsm.Crypto.beBytesToNat (a.take k) / b.toNat)
        have htail : k < (EvmAsm.Stateless.SpecRef.natToBytesBE k
            (EvmAsm.Crypto.beBytesToNat (a.take k) / b.toNat) ++ orig.drop k).length := by
          rw [List.length_append, hqLen, List.length_drop]
          omega
        rw [k73_set_prefix_append _ _ k hqLen htail]
        rw [hprefix]
        rw [hdiv.1]
        rw [k73_natToBytesBE_succ]
        rw [List.drop_drop]
        have hdigit :
            (EvmAsm.Crypto.beBytesToNat (a.take k) % b.toNat * 256 +
              (a.getD k 0).toNat) / b.toNat < 256 := by
          apply (Nat.div_lt_iff_lt_mul (by omega)).2
          omega
        have hqnext :
            (EvmAsm.Crypto.beBytesToNat (a.take k) / b.toNat * 256 +
              (EvmAsm.Crypto.beBytesToNat (a.take k) % b.toNat * 256 +
                (a.getD k 0).toNat) / b.toNat) / 256 =
              EvmAsm.Crypto.beBytesToNat (a.take k) / b.toNat := by
          rw [show EvmAsm.Crypto.beBytesToNat (a.take k) / b.toNat * 256 =
              256 * (EvmAsm.Crypto.beBytesToNat (a.take k) / b.toNat) by ring,
            Nat.add_comm]
          rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < (256 : Nat))]
          rw [Nat.div_eq_of_lt hdigit]
          simp
        have hqrem :
            (EvmAsm.Crypto.beBytesToNat (a.take k) / b.toNat * 256 +
              (EvmAsm.Crypto.beBytesToNat (a.take k) % b.toNat * 256 +
                (a.getD k 0).toNat) / b.toNat) % 256 =
              (EvmAsm.Crypto.beBytesToNat (a.take k) % b.toNat * 256 +
                (a.getD k 0).toNat) / b.toNat := by
          rw [show EvmAsm.Crypto.beBytesToNat (a.take k) / b.toNat * 256 =
              256 * (EvmAsm.Crypto.beBytesToNat (a.take k) / b.toNat) by ring,
            Nat.add_comm, Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt hdigit
        rw [hqnext, hqrem]
        simp [List.append_assoc]
      · rw [hstepRem']
        rw [hprefix, hdiv.2]

theorem k73_bytesBEtoNat_eq_beBytesToNat (bs : List (BitVec 8)) :
    EvmAsm.Stateless.SpecRef.bytesBEtoNat bs =
      EvmAsm.Crypto.beBytesToNat bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [EvmAsm.Stateless.SpecRef.bytesBEtoNat,
        EvmAsm.EL.RLP.Nat.fromBytesBE]
      rw [EvmAsm.Crypto.beBytesToNat_cons]
      have ih' : EvmAsm.EL.RLP.Nat.fromBytesBE bs =
          EvmAsm.Crypto.beBytesToNat bs := ih
      rw [ih']

theorem k73_quot_bytes_natToBytesBE
    (a orig : List (BitVec 8)) (b : Word)
    (ha : a.length = 32) (ho : orig.length = 32)
    (hb : 0 < b.toNat) (hbnd : b.toNat ≤ 2 ^ 56) :
    u256DivU64BeQuotBytes a orig b =
      EvmAsm.Stateless.SpecRef.natToBytesBE 32
        (EvmAsm.Crypto.beBytesToNat a / b.toNat) := by
  have h := k73_div_state_closed a orig b ha ho hb hbnd 32 (by omega)
  change (divState a orig b 32).1 = _
  have htake : a.take 32 = a :=
    (List.take_eq_self_iff a).2 (by omega)
  have hdrop : orig.drop 32 = [] :=
    (List.drop_eq_nil_iff).2 (by omega)
  rw [h.1, htake, hdrop]
  simp

/-! The machine's fixed-width byte buffer is the reference's natural number
    encoding, provided the input already fits the buffer.  These lemmas are
    deliberately stated over the byte representation: callers need to
    identify the bytes written by the divider, not just its numeric quotient. -/

theorem k73_split_mod (n A B : Nat) (hA : 0 < A) (hB : 0 < B) :
    n % (A * B) = (n / A % B) * A + n % A := by
  have hn : n = A * (n / A) + n % A := (Nat.div_add_mod n A).symm
  have hq : n / A = B * (n / A / B) + (n / A) % B :=
    (Nat.div_add_mod (n / A) B).symm
  have hmod : n % A < A := Nat.mod_lt _ hA
  have hdiv : n / A % B < B := Nat.mod_lt _ hB
  calc
    n % (A * B) =
        (A * (B * (n / A / B) + (n / A) % B) + n % A) % (A * B) := by
          congr 1
          calc
            n = A * (n / A) + n % A := hn
            _ = A * (B * (n / A / B) + (n / A) % B) + n % A := by
              exact congrArg (fun t => A * t + n % A) hq
    _ = ((A * ((n / A) % B) + n % A) +
        (A * B) * (n / A / B)) % (A * B) := by
          congr 1
          ring
    _ = (A * ((n / A) % B) + n % A) % (A * B) := by
          rw [Nat.add_mul_mod_self_left]
    _ = A * ((n / A) % B) + n % A := by
          rw [Nat.mod_eq_of_lt]
          nlinarith
    _ = (n / A % B) * A + n % A := by ring

theorem k73_fixed_bytes_value (k n : Nat) :
    EvmAsm.Crypto.beBytesToNat
        (EvmAsm.Stateless.SpecRef.natToBytesBE k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [EvmAsm.Crypto.beBytesToNat,
      EvmAsm.Stateless.SpecRef.natToBytesBE, Nat.mod_one]
  | succ k ih =>
      rw [k73_natToBytesBE_succ,
        EvmAsm.Crypto.beBytesToNat_append]
      rw [ih]
      simp [EvmAsm.Crypto.beBytesToNat]
      have hsplit := k73_split_mod n 256 (256 ^ k) (by decide)
        (by positivity)
      simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using hsplit.symm

theorem k73_bytes_inj_same_length :
    ∀ xs ys : List (BitVec 8), xs.length = ys.length →
      EvmAsm.Crypto.beBytesToNat xs = EvmAsm.Crypto.beBytesToNat ys → xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: as, b :: bs, hlen, hval => by
      have htail_len : as.length = bs.length := by
        simp only [List.length_cons] at hlen
        omega
      have ha := EvmAsm.Crypto.beBytesToNat_cons a as
      have hb := EvmAsm.Crypto.beBytesToNat_cons b bs
      have hta0 := EvmAsm.Crypto.beBytesToNat_lt as
      have htb0 := EvmAsm.Crypto.beBytesToNat_lt bs
      have hpow : (2 : Nat) ^ (8 * as.length) = 256 ^ as.length := by
        rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]
      have hta : EvmAsm.Crypto.beBytesToNat as < 256 ^ as.length := by
        rw [← hpow]
        exact hta0
      have htb0' := htb0
      rw [← htail_len] at htb0'
      have htb : EvmAsm.Crypto.beBytesToNat bs < 256 ^ as.length := by
        rw [← hpow]
        exact htb0'
      have hEq : a.toNat * 256 ^ as.length +
          EvmAsm.Crypto.beBytesToNat as =
          b.toNat * 256 ^ as.length +
          EvmAsm.Crypto.beBytesToNat bs := by
        rw [ha, hb, ← htail_len] at hval
        exact hval
      have hT : 0 < 256 ^ as.length := by positivity
      have habNat : a.toNat = b.toNat := by
        nlinarith [a.isLt, b.isLt]
      have hab : a = b := BitVec.eq_of_toNat_eq habNat
      have htail : EvmAsm.Crypto.beBytesToNat as =
          EvmAsm.Crypto.beBytesToNat bs := by
        nlinarith [hEq]
      subst b
      exact congrArg (fun t => a :: t)
        (k73_bytes_inj_same_length as bs htail_len htail)

theorem k73_fixed_bytes_bound (bs : List (BitVec 8)) :
    EvmAsm.Stateless.SpecRef.bytesBEtoNat bs < 256 ^ bs.length := by
  have hb := k73_bytesBEtoNat_eq_beBytesToNat bs
  have hraw := EvmAsm.Crypto.beBytesToNat_lt bs
  have hp : (2 : Nat) ^ (8 * bs.length) = 256 ^ bs.length := by
    rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]
  calc
    EvmAsm.Stateless.SpecRef.bytesBEtoNat bs =
        EvmAsm.Crypto.beBytesToNat bs := hb
    _ < 2 ^ (8 * bs.length) := hraw
    _ = 256 ^ bs.length := hp

theorem k73_fixed_bytes_repr (bs : List (BitVec 8)) (hlen : bs.length = 32) :
    EvmAsm.Stateless.SpecRef.natToBytesBE 32
        (EvmAsm.Stateless.SpecRef.bytesBEtoNat bs) = bs := by
  apply k73_bytes_inj_same_length
  · simp [EvmAsm.Stateless.SpecRef.natToBytesBE, hlen]
  · calc
      EvmAsm.Crypto.beBytesToNat
          (EvmAsm.Stateless.SpecRef.natToBytesBE 32
            (EvmAsm.Stateless.SpecRef.bytesBEtoNat bs)) =
          EvmAsm.Stateless.SpecRef.bytesBEtoNat bs % 256 ^ 32 :=
        k73_fixed_bytes_value 32
          (EvmAsm.Stateless.SpecRef.bytesBEtoNat bs)
      _ = EvmAsm.Stateless.SpecRef.bytesBEtoNat bs := by
        have hbound := k73_fixed_bytes_bound bs
        rw [hlen] at hbound
        exact Nat.mod_eq_of_lt hbound
      _ = EvmAsm.Crypto.beBytesToNat bs :=
        k73_bytesBEtoNat_eq_beBytesToNat bs

end EvmAsm.Codegen.HeaderBaseFeeSpec
