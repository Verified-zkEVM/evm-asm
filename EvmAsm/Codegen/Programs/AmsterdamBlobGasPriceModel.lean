/-
  EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceModel

  Pure model of `amsterdam_blob_gas_price_u256` (issue #12346, item 7).

  This file contains no separation-logic content: it defines the word-level
  arithmetic the routine performs (6-limb little-endian accumulate,
  multiply-by-u64 with carry, 384-bit restoring division by a u64 divisor,
  big-endian byte emission) and the fueled loop model `priceLoopFuel` that
  mirrors the machine's control flow exactly, including its overflow exits.

  The crux lemmas are:

  * `divBitRun_spec` / `div384by64_spec` — the restoring division is exact.
  * `priceLoopFuel_done_taylor` — whenever the machine's loop reaches its
    `acc = 0` exit with a final sum below the 256-bit output bound, the
    SpecRef model `taylor384Aux` agrees and returns `some (sum / D)`.  Note
    the converse is not needed (and the `i ≥ 496` overflow exit is not
    model-correlated): the K70 contract's status-1 arm carries output
    ownership only, so any machine overflow exit is acceptable regardless
    of the model.
-/

import EvmAsm.Evm64.EvmWordArith.MultiLimb
import EvmAsm.Rv64.ByteOps
import EvmAsm.Stateless.SpecRef.TaylorExponential
import Mathlib.Data.List.GetD

set_option exponentiation.threshold 384
set_option maxRecDepth 8000

namespace EvmAsm.Codegen.AmsterdamBlobGasPrice

open EvmAsm.Rv64
open EvmAsm.Stateless.SpecRef
open EvmAsm.Evm64.EvmWord

/-! ## Little-endian limb lists -/

/-- Value of a little-endian 64-bit limb list. -/
def limbsToNat : List Word → Nat
  | [] => 0
  | w :: ws => w.toNat + 2 ^ 64 * limbsToNat ws

/-- `n` as `k` little-endian 64-bit limbs (least significant first). -/
def natToLimbs : Nat → Nat → List Word
  | 0, _ => []
  | k + 1, n => BitVec.ofNat 64 n :: natToLimbs k (n / 2 ^ 64)

theorem limbsToNat_cons (w : Word) (ws : List Word) :
    limbsToNat (w :: ws) = w.toNat + 2 ^ 64 * limbsToNat ws := rfl

theorem natToLimbs_length (k n : Nat) : (natToLimbs k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [natToLimbs, ih]

theorem limbsToNat_lt (ws : List Word) (k : Nat) (hlen : ws.length = k) :
    limbsToNat ws < 2 ^ (64 * k) := by
  induction ws generalizing k with
  | nil => subst hlen; simp [limbsToNat]
  | cons w ws ih =>
    cases k with
    | zero => simp at hlen
    | succ k =>
      have h' := ih k (by simpa using hlen)
      have hw := w.isLt
      have hpow : 2 ^ (64 * (k + 1)) = 2 ^ 64 * 2 ^ (64 * k) := by
        rw [show 64 * (k + 1) = 64 * k + 64 from by ring, pow_add, Nat.mul_comm]
      simp only [limbsToNat]
      omega

theorem limbsToNat_append (xs ys : List Word) :
    limbsToNat (xs ++ ys) = limbsToNat xs + 2 ^ (64 * xs.length) * limbsToNat ys := by
  induction xs with
  | nil => simp [limbsToNat]
  | cons x xs ih =>
    simp only [List.cons_append, limbsToNat, List.length_cons, ih]
    have hpow : 2 ^ (64 * (xs.length + 1)) = 2 ^ 64 * 2 ^ (64 * xs.length) := by
      rw [show 64 * (xs.length + 1) = 64 * xs.length + 64 from by ring, pow_add,
        Nat.mul_comm]
    rw [hpow]
    ring

theorem limbsToNat_natToLimbs (k n : Nat) (h : n < 2 ^ (64 * k)) :
    limbsToNat (natToLimbs k n) = n := by
  induction k generalizing n with
  | zero =>
    have h0 : n = 0 := by
      have h1 : 2 ^ (64 * 0) = 1 := by decide
      rw [h1] at h
      omega
    subst h0
    rfl
  | succ k ih =>
    have hdiv : n / 2 ^ 64 < 2 ^ (64 * k) := by
      have hpow : 2 ^ (64 * (k + 1)) = 2 ^ 64 * 2 ^ (64 * k) := by
        rw [show 64 * (k + 1) = 64 * k + 64 from by ring, pow_add, Nat.mul_comm]
      rw [hpow] at h
      omega
    simp only [natToLimbs, limbsToNat_cons, ih (n / 2 ^ 64) hdiv]
    have hmod : (BitVec.ofNat 64 n).toNat = n % 2 ^ 64 := BitVec.toNat_ofNat _ _
    rw [hmod]
    omega

theorem natToLimbs_getElem (k n j : Nat) (hj : j < k) :
    (natToLimbs k n)[j]'(by rw [natToLimbs_length]; exact hj) =
      BitVec.ofNat 64 (n / 2 ^ (64 * j)) := by
  induction k generalizing n j with
  | zero => omega
  | succ k ih =>
    cases j with
    | zero =>
      simp only [natToLimbs, List.getElem_cons_zero, Nat.mul_zero, pow_zero,
        Nat.div_one]
    | succ j =>
      have hj' : j < k := by omega
      simp only [natToLimbs, List.getElem_cons_succ]
      rw [ih (n / 2 ^ 64) j hj', Nat.div_div_eq_div_mul]
      have hexp : (2 : Nat) ^ 64 * 2 ^ (64 * j) = 2 ^ (64 * (j + 1)) := by
        rw [← pow_add]
        congr 1
        ring
      rw [hexp]

/-- Fixed-length limb lists are determined by their value. -/
theorem natToLimbs_eq_of_limbsToNat (ws : List Word) (k n : Nat)
    (hlen : ws.length = k) (hn : n < 2 ^ (64 * k)) (hval : limbsToNat ws = n) :
    ws = natToLimbs k n := by
  induction ws generalizing k n with
  | nil =>
    subst hlen
    simp [limbsToNat] at hval
    subst hval
    rfl
  | cons w ws ih =>
    cases k with
    | zero => simp at hlen
    | succ k =>
      have hlen' : ws.length = k := by simpa using hlen
      have hval' : w.toNat + 2 ^ 64 * limbsToNat ws = n := hval
      have hlt_ws : limbsToNat ws < 2 ^ (64 * k) := limbsToNat_lt ws k hlen'
      have hw : w = BitVec.ofNat 64 n := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat]
        omega
      have hn' : n / 2 ^ 64 < 2 ^ (64 * k) := by
        have hpow : 2 ^ (64 * (k + 1)) = 2 ^ 64 * 2 ^ (64 * k) := by
          rw [show 64 * (k + 1) = 64 * k + 64 from by ring, pow_add, Nat.mul_comm]
        rw [hpow] at hn
        omega
      have hrest : ws = natToLimbs k (n / 2 ^ 64) :=
        ih k (n / 2 ^ 64) hlen' hn' (by omega)
      rw [hw, hrest]
      rfl

/-- Value of a most-significant-first limb list. -/
def msbVal : List Word → Nat
  | [] => 0
  | w :: ws => w.toNat * 2 ^ (64 * ws.length) + msbVal ws

theorem msbVal_eq_limbsToNat_reverse (ws : List Word) :
    msbVal ws = limbsToNat ws.reverse := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [msbVal, List.reverse_cons, limbsToNat_append, ih, limbsToNat,
      List.length_reverse]
    ring

/-! ## Byte encodings -/

/-- The 8 little-endian bytes of a word. -/
def limbBytes (w : Word) : List (BitVec 8) :=
  (List.range 8).map fun i => extractByte w i

/-- The little-endian bytes of a limb list. -/
def limbsBytes : List Word → List (BitVec 8)
  | [] => []
  | w :: ws => limbBytes w ++ limbsBytes ws

theorem limbBytes_length (w : Word) : (limbBytes w).length = 8 := by
  simp [limbBytes]

theorem limbsBytes_length (ws : List Word) :
    (limbsBytes ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [limbsBytes, limbBytes_length, ih]; omega

/-- Two words with the same eight bytes are equal. -/
theorem word_eq_of_extractByte_eq {a b : Word}
    (h : ∀ k, k < 8 → extractByte a k = extractByte b k) : a = b := by
  rw [BitVec.eq_of_getLsbD_eq_iff]
  intro i hi
  have hge : i / 8 < 8 := by omega
  have hb := h (i / 8) hge
  have key : ∀ (w : Word), w.getLsbD i = (extractByte w (i / 8)).getLsbD (i % 8) := by
    intro w
    have hmod : i % 8 < 8 := Nat.mod_lt _ (by decide)
    have hi8 : i = (i / 8) * 8 + i % 8 := by omega
    conv_lhs => rw [hi8]
    simp only [extractByte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    simp [hmod]
  rw [key a, key b, hb]

theorem packBytes_limbBytes (w : Word) : packBytes (limbBytes w) = w := by
  apply word_eq_of_extractByte_eq
  intro k hk
  rw [extractByte_packBytes _ k hk (by rw [limbBytes_length]; exact hk)]
  simp [limbBytes]

theorem limbsBytes_getD (ws : List Word) (j : Nat) (hj : j < 8 * ws.length) :
    (limbsBytes ws).getD j 0 = extractByte (ws.getD (j / 8) 0) (j % 8) := by
  induction ws generalizing j with
  | nil => simp at hj
  | cons w ws ih =>
    have h8 : (limbBytes w).length = 8 := limbBytes_length w
    by_cases hj8 : j < 8
    · have hdiv : j / 8 = 0 := Nat.div_eq_of_lt hj8
      have hmod : j % 8 = j := Nat.mod_eq_of_lt hj8
      rw [show limbsBytes (w :: ws) = limbBytes w ++ limbsBytes ws from rfl,
        List.getD_append _ _ _ _ (by rw [h8]; exact hj8)]
      have hb : (limbBytes w).getD j 0 = extractByte w j := by
        rw [List.getD_eq_getElem _ _ (by rw [h8]; exact hj8)]
        simp only [limbBytes, List.getElem_map, List.getElem_range]
      rw [hb, hmod, hdiv, List.getD_cons_zero]
    · have hj' : j - 8 < 8 * ws.length := by
        have hlen : (w :: ws).length = ws.length + 1 := rfl
        omega
      have hdiv : j / 8 = (j - 8) / 8 + 1 := by omega
      have hmod : (j - 8) % 8 = j % 8 := by omega
      rw [show limbsBytes (w :: ws) = limbBytes w ++ limbsBytes ws from rfl,
        List.getD_append_right _ _ _ _ (by rw [h8]; omega), h8]
      rw [ih (j - 8) hj', hmod, hdiv, List.getD_cons_succ]

/-- The canonical 32-byte big-endian encoding of a 256-bit value. -/
def beBytes32OfNat (n : Nat) : List (BitVec 8) :=
  (List.range 32).map fun i => BitVec.ofNat 8 (n / 256 ^ (31 - i))

theorem beBytes32OfNat_length (n : Nat) : (beBytes32OfNat n).length = 32 := by
  simp [beBytes32OfNat]

theorem extractByte_ofNat (x : Nat) (b : Nat) (hb : b < 8) :
    extractByte (BitVec.ofNat 64 x) b = BitVec.ofNat 8 (x / 2 ^ (8 * b)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [extractByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have h1 : (x % 2 ^ 64) / 2 ^ (b * 8) % 2 ^ 8 = x / 2 ^ (8 * b) % 2 ^ 8 := by
    have hb8 : b * 8 = 8 * b := by ring
    rw [hb8]
    have hsplit : (2 : Nat) ^ 64 = 2 ^ (64 - 8 * b) * 2 ^ (8 * b) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hsplit, Nat.mod_mul_left_div_self, Nat.mod_mod_of_dvd _
      (Nat.pow_dvd_pow 2 (by omega))]
  rw [h1]

/-- The low 32 bytes of the little-endian encoding of `q < 2^256`, indexed
    from the top, are the canonical big-endian encoding. -/
theorem beBytes32OfNat_getD (q : Nat) (j : Nat) (hj : j < 32) :
    (beBytes32OfNat q).getD j 0 = BitVec.ofNat 8 (q / 256 ^ (31 - j)) := by
  rw [List.getD_eq_getElem _ _ (by rw [beBytes32OfNat_length]; exact hj)]
  simp only [beBytes32OfNat, List.getElem_map, List.getElem_range]

/-- The limb-list form of the byte-encoding lemma. -/
theorem beBytes32OfNat_getD_of_limbs (q : Nat) (hq : q < 2 ^ 256)
    (qs : List Word) (hqs : qs.length = 6) (hval : limbsToNat qs = q)
    (j : Nat) (hj : j < 32) :
    (beBytes32OfNat q).getD j 0 = (limbsBytes qs).getD (31 - j) 0 := by
  have hq384 : q < 2 ^ (64 * 6) := by
    have h : 2 ^ (64 * 6) = 2 ^ 384 := by decide
    rw [h]
    omega
  have hqs' : qs = natToLimbs 6 q := natToLimbs_eq_of_limbsToNat qs 6 q hqs hq384 hval
  rw [beBytes32OfNat_getD q j hj, limbsBytes_getD qs (31 - j) (by rw [hqs]; omega)]
  subst hqs'
  rw [List.getD_eq_getElem _ _ (by rw [natToLimbs_length]; omega :
      (31 - j) / 8 < (natToLimbs 6 q).length),
    natToLimbs_getElem 6 q ((31 - j) / 8) (by omega),
    extractByte_ofNat _ _ (by omega)]
  have h3 : 256 ^ (31 - j) = 2 ^ (8 * (31 - j)) := by
    rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_mul]
  have h4 : 8 * (31 - j) = 64 * ((31 - j) / 8) + 8 * ((31 - j) % 8) := by
    have := Nat.div_add_mod (31 - j) 8
    omega
  rw [h3, h4, pow_add, ← Nat.div_div_eq_div_mul]

/-- The big-endian output equals the reversed low 32 little-endian bytes. -/
theorem map_getD_limbsBytes_eq_beBytes32OfNat (q : Nat) (hq : q < 2 ^ 256)
    (qs : List Word) (hqs : qs.length = 6) (hval : limbsToNat qs = q) :
    (List.range 32).map (fun j => (limbsBytes qs).getD (31 - j) 0) =
      beBytes32OfNat q := by
  apply List.ext_getElem
  · simp [beBytes32OfNat]
  · intro i h1 h2
    have hi : i < 32 := by simpa using h1
    rw [List.getElem_map, List.getElem_range, ← beBytes32OfNat_getD_of_limbs q hq
      qs hqs hval i hi]
    rw [List.getD_eq_getElem _ _ (by rw [beBytes32OfNat_length]; exact hi)]

/-! ## 6-limb accumulate (the `sum += acc` block) -/

/-- One limb of the accumulate: input limbs `a` (acc) and `s` (sum) plus carry
    `c ∈ {0, 1}`; returns the new sum limb and the carry out, exactly as the
    machine computes them (`x30` and `x5`). -/
def addLimbStep (a s c : Word) : Word × Word :=
  let lo := a + s
  let c1 : Word := if BitVec.ult lo a then 1 else 0
  let lo2 := lo + c
  let c2 : Word := if BitVec.ult lo2 lo then 1 else 0
  (lo2, c1 ||| c2)

/-- Carry out of a two-operand word addition, as a Nat. -/
theorem sltu_add_carry (x y : Word) :
    (if BitVec.ult (x + y) x then (1 : Word) else 0).toNat = (x.toNat + y.toNat) / 2 ^ 64 := by
  rw [BitVec.ult_eq_decide, BitVec.toNat_add]
  by_cases h : x.toNat + y.toNat < 2 ^ 64
  · rw [Nat.mod_eq_of_lt h, decide_eq_false (by omega)]
    show ((0 : Word)).toNat = (x.toNat + y.toNat) / 2 ^ 64
    rw [Nat.div_eq_of_lt h]
    decide
  · have hx := x.isLt
    have hy := y.isLt
    have hm : (x.toNat + y.toNat) % 2 ^ 64 = x.toNat + y.toNat - 2 ^ 64 := by omega
    rw [hm, decide_eq_true (by omega)]
    show ((1 : Word)).toNat = (x.toNat + y.toNat) / 2 ^ 64
    have h1 : (x.toNat + y.toNat) / 2 ^ 64 = 1 := by omega
    rw [h1]
    decide

theorem addLimbStep_spec (a s c : Word) (hc : c.toNat ≤ 1) :
    (addLimbStep a s c).1.toNat = (a.toNat + s.toNat + c.toNat) % 2 ^ 64 ∧
      (addLimbStep a s c).2.toNat = (a.toNat + s.toNat + c.toNat) / 2 ^ 64 := by
  have ha := a.isLt; have hs := s.isLt
  simp only [addLimbStep]
  have hlo : (a + s).toNat = (a.toNat + s.toNat) % 2 ^ 64 := BitVec.toNat_add _ _
  have hc1 : (if BitVec.ult (a + s) a then (1 : Word) else 0).toNat =
      (a.toNat + s.toNat) / 2 ^ 64 := sltu_add_carry a s
  have hc2 : (if BitVec.ult ((a + s) + c) (a + s) then (1 : Word) else 0).toNat =
      ((a.toNat + s.toNat) % 2 ^ 64 + c.toNat) / 2 ^ 64 := by
    have h := sltu_add_carry (a + s) c
    rwa [hlo] at h
  have hsum : (a.toNat + s.toNat + c.toNat) / 2 ^ 64 =
      (a.toNat + s.toNat) / 2 ^ 64 +
        ((a.toNat + s.toNat) % 2 ^ 64 + c.toNat) / 2 ^ 64 := by
    have h := Nat.add_div (a := a.toNat + s.toNat) (b := c.toNat) (c := 2 ^ 64)
      (by decide : 0 < 2 ^ 64)
    have hc0 : c.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by omega)
    have hcmod : c.toNat % 2 ^ 64 = c.toNat := Nat.mod_eq_of_lt (by omega)
    omega
  have huv : (a.toNat + s.toNat) / 2 ^ 64 +
      ((a.toNat + s.toNat) % 2 ^ 64 + c.toNat) / 2 ^ 64 ≤ 1 := by
    omega
  have hor : ((if BitVec.ult (a + s) a then (1 : Word) else 0) |||
      (if BitVec.ult ((a + s) + c) (a + s) then (1 : Word) else 0)).toNat =
      (a.toNat + s.toNat + c.toNat) / 2 ^ 64 := by
    rw [BitVec.toNat_or, hc1, hc2, hsum]
    set u := (a.toNat + s.toNat) / 2 ^ 64 with hu
    set v := ((a.toNat + s.toNat) % 2 ^ 64 + c.toNat) / 2 ^ 64 with hv
    have hu1 : u ≤ 1 := by omega
    have hv1 : v ≤ 1 := by omega
    have huv1 : u + v ≤ 1 := huv
    interval_cases u <;> interval_cases v <;> first | omega | decide
  have h1 : (a + s + c).toNat = (a.toNat + s.toNat + c.toNat) % 2 ^ 64 := by
    rw [BitVec.toNat_add, hlo]
    conv_rhs => rw [show a.toNat + s.toNat + c.toNat =
        (a.toNat + s.toNat) + c.toNat from rfl]
    rw [Nat.add_mod, Nat.mod_mod (n := 2 ^ 64), ← Nat.add_mod]
  exact ⟨h1, hor⟩

/-- The 6-limb accumulate over limb lists (low limb first). -/
def add384Run : List Word → List Word → Word → List Word × Word
  | a :: as, s :: ss, c =>
      let (s', c') := addLimbStep a s c
      let (ss', cf) := add384Run as ss c'
      (s' :: ss', cf)
  | _, _, c => ([], c)

theorem add384Run_length (as ss : List Word) (c : Word) (hlen : as.length = ss.length) :
    (add384Run as ss c).1.length = as.length := by
  induction as generalizing ss c with
  | nil => rfl
  | cons a as ih =>
    cases ss with
    | nil => simp at hlen
    | cons s ss =>
      simp only [add384Run, List.length_cons]
      rw [ih ss _ (by simpa using hlen)]

theorem add384Run_spec (as ss : List Word) (c : Word) (hc : c.toNat ≤ 1)
    (hlen : as.length = ss.length) :
    limbsToNat (add384Run as ss c).1 +
        (add384Run as ss c).2.toNat * 2 ^ (64 * as.length) =
      limbsToNat as + limbsToNat ss + c.toNat ∧
      (add384Run as ss c).2.toNat ≤ 1 := by
  induction as generalizing ss c with
  | nil =>
    have hss : ss = [] := by simpa using hlen.symm
    subst hss
    simp [add384Run, limbsToNat]; omega
  | cons a as ih =>
    cases ss with
    | nil => simp at hlen
    | cons s ss =>
      have hlen' : as.length = ss.length := by simpa using hlen
      obtain ⟨hstep1, hstep2⟩ := addLimbStep_spec a s c hc
      have hc' : (addLimbStep a s c).2.toNat ≤ 1 := by
        rw [hstep2]
        have ha := a.isLt; have hs := s.isLt
        omega
      obtain ⟨hrec, hcf⟩ := ih ss (addLimbStep a s c).2 hc' hlen'
      have hpow : 2 ^ (64 * (as.length + 1)) = 2 ^ 64 * 2 ^ (64 * as.length) := by
        rw [show 64 * (as.length + 1) = 64 * as.length + 64 from by ring, pow_add,
          Nat.mul_comm]
      simp only [add384Run, limbsToNat_cons, List.length_cons, hpow]
      have hdivmod := Nat.div_add_mod (a.toNat + s.toNat + c.toNat) (2 ^ 64)
      have htotal : (addLimbStep a s c).1.toNat +
          2 ^ 64 * limbsToNat (add384Run as ss (addLimbStep a s c).2).1 +
          (add384Run as ss (addLimbStep a s c).2).2.toNat *
            (2 ^ 64 * 2 ^ (64 * as.length)) =
          (addLimbStep a s c).1.toNat +
            2 ^ 64 * (addLimbStep a s c).2.toNat +
            2 ^ 64 * (limbsToNat as + limbsToNat ss) := by
        calc (addLimbStep a s c).1.toNat +
            2 ^ 64 * limbsToNat (add384Run as ss (addLimbStep a s c).2).1 +
            (add384Run as ss (addLimbStep a s c).2).2.toNat *
              (2 ^ 64 * 2 ^ (64 * as.length))
          = (addLimbStep a s c).1.toNat +
            2 ^ 64 * (limbsToNat (add384Run as ss (addLimbStep a s c).2).1 +
              (add384Run as ss (addLimbStep a s c).2).2.toNat *
                2 ^ (64 * as.length)) := by ring
        _ = (addLimbStep a s c).1.toNat +
            2 ^ 64 * (limbsToNat as + limbsToNat ss +
              (addLimbStep a s c).2.toNat) := by rw [hrec]
        _ = (addLimbStep a s c).1.toNat +
            2 ^ 64 * (addLimbStep a s c).2.toNat +
            2 ^ 64 * (limbsToNat as + limbsToNat ss) := by ring
      rw [htotal]
      omega

/-- The final carry of the accumulate is nonzero iff the sum does not fit in
    384 bits (the machine's `bnez t0` overflow exit). -/
theorem add384_carry_iff (as ss : List Word)
    (hlen : as.length = 6) (hlen2 : ss.length = 6) :
    (add384Run as ss 0).2.toNat ≠ 0 ↔
      2 ^ 384 ≤ limbsToNat as + limbsToNat ss := by
  obtain ⟨hrec, hcf⟩ := add384Run_spec as ss 0 (by simp) (by rw [hlen, hlen2])
  have hlt : limbsToNat (add384Run as ss 0).1 < 2 ^ 384 := by
    have hlen3 : (add384Run as ss 0).1.length = 6 := by
      rw [add384Run_length as ss 0 (by rw [hlen, hlen2])]; exact hlen
    have := limbsToNat_lt (add384Run as ss 0).1 6 hlen3
    simpa using this
  have hz : (0 : Word).toNat = 0 := by decide
  rw [hz] at hrec
  simp only [hlen, Nat.add_zero] at hrec
  have hpow : 2 ^ (64 * 6) = 2 ^ 384 := by decide
  rw [hpow] at hrec
  constructor
  · intro hne
    have hpos : 0 < (add384Run as ss 0).2.toNat := Nat.pos_of_ne_zero hne
    omega
  · intro hge hzero
    rw [hzero] at hrec
    omega

/-! ## 6-limb multiply by u64 (the `prod = acc * excess` block) -/

/-- One limb of the multiply: input limb `a`, multiplier `e`, carry `c`;
    returns the product limb and the carry out.  The machine's per-limb
    overflow branch is provably dead whenever `c ≤ 2^64 - 1`
    (`mulLimbStep_spec`), so it is not modelled. -/
def mulLimbStep (a e c : Word) : Word × Word :=
  let lo := a * e
  let hi := rv64_mulhu a e
  let s1 := lo + c
  let c1 : Word := if BitVec.ult s1 lo then 1 else 0
  (s1, hi + c1)

/-- The machine's per-limb overflow flag (the `bnez t4` after the carry
    chain): provably always clear on the machine's execution path. -/
def mulLimbOvf (a e c : Word) : Word :=
  let lo := a * e
  let hi := rv64_mulhu a e
  let s1 := lo + c
  let c1 : Word := if BitVec.ult s1 lo then 1 else 0
  let s2 := hi + c1
  if BitVec.ult s2 hi then 1 else 0

theorem mulLimbStep_spec (a e c : Word) (hc : c.toNat ≤ 2 ^ 64 - 1) :
    (mulLimbStep a e c).1.toNat = (a.toNat * e.toNat + c.toNat) % 2 ^ 64 ∧
      (mulLimbStep a e c).2.toNat = (a.toNat * e.toNat + c.toNat) / 2 ^ 64 ∧
      mulLimbOvf a e c = 0 := by
  have ha := a.isLt; have he := e.isLt
  have hTbound : a.toNat * e.toNat + c.toNat ≤ 2 ^ 128 - 2 ^ 64 := by
    have : a.toNat * e.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hlo : (a * e).toNat = (a.toNat * e.toNat) % 2 ^ 64 := BitVec.toNat_mul _ _
  have hhi : (rv64_mulhu a e).toNat = (a.toNat * e.toNat) / 2 ^ 64 := rv64_mulhu_toNat
  have hs1 : ((a * e) + c).toNat = (a.toNat * e.toNat + c.toNat) % 2 ^ 64 := by
    rw [BitVec.toNat_add, hlo]
    conv_rhs => rw [show a.toNat * e.toNat + c.toNat =
        (a.toNat * e.toNat) + c.toNat from rfl]
    rw [Nat.add_mod, Nat.mod_mod (n := 2 ^ 64), ← Nat.add_mod]
  have hc1 : (if BitVec.ult ((a * e) + c) (a * e) then (1 : Word) else 0).toNat =
      ((a.toNat * e.toNat) % 2 ^ 64 + c.toNat) / 2 ^ 64 := by
    have h := sltu_add_carry (a * e) c
    rwa [hlo] at h
  have hTdiv : (a.toNat * e.toNat + c.toNat) / 2 ^ 64 =
      (rv64_mulhu a e).toNat +
        (if BitVec.ult ((a * e) + c) (a * e) then (1 : Word) else 0).toNat := by
    rw [hhi, hc1]
    have h := Nat.add_div (a := a.toNat * e.toNat) (b := c.toNat) (c := 2 ^ 64)
      (by decide : 0 < 2 ^ 64)
    have hc0 : c.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by omega)
    have hcmod : c.toNat % 2 ^ 64 = c.toNat := Nat.mod_eq_of_lt (by omega)
    omega
  have hs2 : ((rv64_mulhu a e) +
      (if BitVec.ult ((a * e) + c) (a * e) then (1 : Word) else 0)).toNat =
      (a.toNat * e.toNat + c.toNat) / 2 ^ 64 := by
    rw [BitVec.toNat_add, ← hTdiv]
    exact Nat.mod_eq_of_lt (by omega)
  have hovf : mulLimbOvf a e c = 0 := by
    have hs2le : (a.toNat * e.toNat + c.toNat) / 2 ^ 64 ≤ 2 ^ 64 - 1 := by omega
    have hnot : BitVec.ult ((rv64_mulhu a e) +
        (if BitVec.ult ((a * e) + c) (a * e) then (1 : Word) else 0))
        (rv64_mulhu a e) = false := by
      rw [BitVec.ult_eq_decide, hs2, hhi, decide_eq_false (by omega)]
    simp only [mulLimbOvf, hnot, Bool.false_eq_true, if_false]
  exact ⟨hs1, hs2, hovf⟩

/-- The 6-limb multiply over the accumulator limbs (low limb first). -/
def mul384Run : List Word → Word → Word → List Word × Word
  | a :: as, e, c =>
      let (p, c') := mulLimbStep a e c
      let (ps, cf) := mul384Run as e c'
      (p :: ps, cf)
  | [], _, c => ([], c)

theorem mul384Run_length (as : List Word) (e c : Word) :
    (mul384Run as e c).1.length = as.length := by
  induction as generalizing c with
  | nil => rfl
  | cons a as ih => simp [mul384Run, ih]

theorem mul384Run_spec (as : List Word) (e c : Word) (hc : c.toNat ≤ 2 ^ 64 - 1) :
    limbsToNat (mul384Run as e c).1 +
        (mul384Run as e c).2.toNat * 2 ^ (64 * as.length) =
      limbsToNat as * e.toNat + c.toNat ∧
      (mul384Run as e c).2.toNat ≤ 2 ^ 64 - 1 := by
  induction as generalizing c with
  | nil => simp [mul384Run, limbsToNat]; omega
  | cons a as ih =>
    obtain ⟨hp, hc', hovf⟩ := mulLimbStep_spec a e c hc
    have hcb : (mulLimbStep a e c).2.toNat ≤ 2 ^ 64 - 1 := by
      rw [hc']
      have hTbound : a.toNat * e.toNat + c.toNat ≤ 2 ^ 128 - 2 ^ 64 := by
        have ha := a.isLt; have he := e.isLt
        have : a.toNat * e.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        omega
      omega
    obtain ⟨hrec, hcf⟩ := ih (mulLimbStep a e c).2 hcb
    have hpow : 2 ^ (64 * (as.length + 1)) = 2 ^ 64 * 2 ^ (64 * as.length) := by
      rw [show 64 * (as.length + 1) = 64 * as.length + 64 from by ring, pow_add,
        Nat.mul_comm]
    simp only [mul384Run, limbsToNat_cons, List.length_cons, hpow]
    have hdivmod := Nat.div_add_mod (a.toNat * e.toNat + c.toNat) (2 ^ 64)
    have htotal : (mulLimbStep a e c).1.toNat +
        2 ^ 64 * limbsToNat (mul384Run as e (mulLimbStep a e c).2).1 +
        (mul384Run as e (mulLimbStep a e c).2).2.toNat *
          (2 ^ 64 * 2 ^ (64 * as.length)) =
        (mulLimbStep a e c).1.toNat +
          2 ^ 64 * (mulLimbStep a e c).2.toNat +
          2 ^ 64 * (limbsToNat as * e.toNat) := by
      calc (mulLimbStep a e c).1.toNat +
          2 ^ 64 * limbsToNat (mul384Run as e (mulLimbStep a e c).2).1 +
          (mul384Run as e (mulLimbStep a e c).2).2.toNat *
            (2 ^ 64 * 2 ^ (64 * as.length))
        = (mulLimbStep a e c).1.toNat +
          2 ^ 64 * (limbsToNat (mul384Run as e (mulLimbStep a e c).2).1 +
            (mul384Run as e (mulLimbStep a e c).2).2.toNat *
              2 ^ (64 * as.length)) := by ring
      _ = (mulLimbStep a e c).1.toNat +
          2 ^ 64 * (limbsToNat as * e.toNat +
            (mulLimbStep a e c).2.toNat) := by rw [hrec]
      _ = (mulLimbStep a e c).1.toNat +
          2 ^ 64 * (mulLimbStep a e c).2.toNat +
          2 ^ 64 * (limbsToNat as * e.toNat) := by ring
    have hdistr : (a.toNat + 2 ^ 64 * limbsToNat as) * e.toNat =
        a.toNat * e.toNat + 2 ^ 64 * (limbsToNat as * e.toNat) := by ring
    rw [htotal, hdistr]
    omega

/-- The final carry of the multiply is nonzero iff the product does not fit
    in 384 bits (the machine's `bnez t6` overflow exit). -/
theorem mul384_carry_iff (as : List Word) (e : Word)
    (hlen : as.length = 6) :
    (mul384Run as e 0).2.toNat ≠ 0 ↔
      2 ^ 384 ≤ limbsToNat as * e.toNat := by
  obtain ⟨hrec, hcf⟩ := mul384Run_spec as e 0 (by simp)
  have hlt : limbsToNat (mul384Run as e 0).1 < 2 ^ 384 := by
    have hlen3 : (mul384Run as e 0).1.length = 6 := by
      rw [mul384Run_length]; exact hlen
    have := limbsToNat_lt (mul384Run as e 0).1 6 hlen3
    simpa using this
  have hz : (0 : Word).toNat = 0 := by decide
  rw [hz] at hrec
  simp only [hlen, Nat.add_zero] at hrec
  have hpow : 2 ^ (64 * 6) = 2 ^ 384 := by decide
  rw [hpow] at hrec
  constructor
  · intro hne
    have hpos : 0 < (mul384Run as e 0).2.toNat := Nat.pos_of_ne_zero hne
    omega
  · intro hge hzero
    rw [hzero] at hrec
    omega

/-! ## Restoring division by a u64 divisor -/

/-- One bit of the restoring division, exactly as the machine computes it
    (`x6` remainder, `x7` shifting dividend limb, `x28` quotient). -/
def divBitStep (d r w q : Word) : Word × Word × Word :=
  let r1 := (r <<< (1 : Nat)) + (if w.msb then 1 else 0)
  let w1 := w <<< (1 : Nat)
  if BitVec.ule d r1 then (r1 - d, w1, (q <<< (1 : Nat)) + 1) else (r1, w1, q <<< (1 : Nat))

/-- The bit loop, `k` iterations from the given state. -/
def divBitRun (d r w q : Word) : Nat → Word × Word × Word
  | 0 => (r, w, q)
  | k + 1 =>
      let (r1, w1, q1) := divBitRun d r w q k
      divBitStep d r1 w1 q1

theorem divBitRun_w (d r w q : Word) (k : Nat) :
    (divBitRun d r w q k).2.1 = w <<< k := by
  induction k with
  | zero => simp [divBitRun, BitVec.shiftLeft_zero]
  | succ k ih =>
    have h1 : (divBitStep d (divBitRun d r w q k).1 (divBitRun d r w q k).2.1
        (divBitRun d r w q k).2.2).2.1 = (divBitRun d r w q k).2.1 <<< (1 : Nat) := by
      by_cases hcase : BitVec.ule d ((divBitRun d r w q k).1 <<< (1 : Nat) +
        (if (divBitRun d r w q k).2.1.msb then (1 : Word) else 0))
      · rw [show divBitStep d (divBitRun d r w q k).1 (divBitRun d r w q k).2.1
            (divBitRun d r w q k).2.2 =
            (((divBitRun d r w q k).1 <<< (1 : Nat)) +
              (if (divBitRun d r w q k).2.1.msb then (1 : Word) else 0) - d,
             (divBitRun d r w q k).2.1 <<< (1 : Nat),
             ((divBitRun d r w q k).2.2 <<< (1 : Nat)) + 1) from by
          dsimp only [divBitStep]
          rw [if_pos hcase]]
      · rw [show divBitStep d (divBitRun d r w q k).1 (divBitRun d r w q k).2.1
            (divBitRun d r w q k).2.2 =
            (((divBitRun d r w q k).1 <<< (1 : Nat)) +
              (if (divBitRun d r w q k).2.1.msb then (1 : Word) else 0),
             (divBitRun d r w q k).2.1 <<< (1 : Nat),
             (divBitRun d r w q k).2.2 <<< (1 : Nat)) from by
          dsimp only [divBitStep]
          rw [if_neg hcase]]
    rw [show divBitRun d r w q (k + 1) =
        divBitStep d (divBitRun d r w q k).1 (divBitRun d r w q k).2.1
          (divBitRun d r w q k).2.2 from rfl,
      h1, ih, ← BitVec.shiftLeft_add]

theorem msb_iff_toNat (x : Word) : x.msb = decide (2 ^ 63 ≤ x.toNat) := by
  rw [BitVec.msb_eq_decide]

/-- The bit consumed at iteration `k`: the sign bit of the shifted dividend. -/
theorem msb_shiftLeft_toNat (w : Word) (k : Nat) (hk : k ≤ 63) :
    (if (w <<< k).msb then (1 : Word) else 0).toNat =
      (w.toNat / 2 ^ (63 - k)) % 2 := by
  have hw := w.isLt
  have hdecomp := Nat.div_add_mod w.toNat (2 ^ (63 - k))
  set a := w.toNat / 2 ^ (63 - k)
  set b := w.toNat % 2 ^ (63 - k)
  have hb2 : b < 2 ^ (63 - k) := Nat.mod_lt _ (by positivity)
  have hpow : (2 : Nat) ^ (63 - k) * 2 ^ k = 2 ^ 63 := by
    rw [← Nat.pow_add]; congr 1; omega
  have hbk : b * 2 ^ k < 2 ^ 63 := by
    calc b * 2 ^ k < 2 ^ (63 - k) * 2 ^ k :=
        Nat.mul_lt_mul_of_pos_right hb2 (by positivity)
      _ = 2 ^ 63 := hpow
  have h1 : w.toNat = a * 2 ^ (63 - k) + b := by
    have h2 := Nat.div_add_mod w.toNat (2 ^ (63 - k))
    rw [Nat.mul_comm] at h2
    exact h2.symm
  have hkey : w.toNat * 2 ^ k = (a % 2) * 2 ^ 63 + b * 2 ^ k + (a / 2) * 2 ^ 64 := by
    have ha := Nat.div_add_mod a 2
    have h2 : a * 2 ^ (63 - k) * 2 ^ k = a * 2 ^ 63 := by
      rw [← hpow]; ring
    calc w.toNat * 2 ^ k = (a * 2 ^ (63 - k) + b) * 2 ^ k := by rw [h1]
      _ = a * 2 ^ (63 - k) * 2 ^ k + b * 2 ^ k := by ring
      _ = a * 2 ^ 63 + b * 2 ^ k := by rw [h2]
      _ = (a % 2) * 2 ^ 63 + b * 2 ^ k + (a / 2) * 2 ^ 64 := by omega
  have hmod : (w.toNat * 2 ^ k) % 2 ^ 64 = (a % 2) * 2 ^ 63 + b * 2 ^ k := by
    rw [hkey, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (by omega)
  have hshl : (w <<< k).toNat = (a % 2) * 2 ^ 63 + b * 2 ^ k := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hmod]
  rw [msb_iff_toNat, hshl]
  by_cases h2 : a % 2 = 1
  · rw [h2, decide_eq_true (by omega : 2 ^ 63 ≤ 1 * 2 ^ 63 + b * 2 ^ k)]
    decide
  · have h0 : a % 2 = 0 := by omega
    rw [h0, decide_eq_false (by omega : ¬ 2 ^ 63 ≤ 0 * 2 ^ 63 + b * 2 ^ k)]
    decide

theorem divBitRun_spec (d r w : Word) (hd : 0 < d.toNat) (hd63 : d.toNat ≤ 2 ^ 63)
    (hr : r.toNat < d.toNat) (k : Nat) (hk : k ≤ 64) :
    r.toNat * 2 ^ k + w.toNat / 2 ^ (64 - k) =
      (divBitRun d r w 0 k).2.2.toNat * d.toNat + (divBitRun d r w 0 k).1.toNat ∧
      (divBitRun d r w 0 k).1.toNat < d.toNat ∧
      (divBitRun d r w 0 k).2.2.toNat < 2 ^ k := by
  induction k with
  | zero =>
    have hw := w.isLt
    simp [divBitRun, hr]
    omega
  | succ k ih =>
    have hk' : k ≤ 64 := by omega
    obtain ⟨heq, hlt, hq⟩ := ih hk'
    have hwk : (divBitRun d r w 0 k).2.1 = w <<< k := divBitRun_w d r w 0 k
    have hbit : (if (divBitRun d r w 0 k).2.1.msb then (1 : Word) else 0).toNat =
        (w.toNat / 2 ^ (63 - k)) % 2 := by
      rw [hwk]
      exact msb_shiftLeft_toNat w k (by omega)
    set rk := (divBitRun d r w 0 k).1 with hrk
    set qk := (divBitRun d r w 0 k).2.2 with hqk
    set b := (w.toNat / 2 ^ (63 - k)) % 2 with hb
    have hb1 : b ≤ 1 := by
      have h2 := Nat.mod_lt (w.toNat / 2 ^ (63 - k)) (by decide : (0 : Nat) < 2)
      omega
    have hprefix : w.toNat / 2 ^ (64 - (k + 1)) =
        2 * (w.toNat / 2 ^ (64 - k)) + b := by
      have h1 : 64 - (k + 1) = 63 - k := by omega
      have h2 : 64 - k = (63 - k) + 1 := by omega
      rw [h1, h2, hb]
      have hdd : (2 : Nat) ^ ((63 - k) + 1) = 2 ^ (63 - k) * 2 := by ring
      rw [hdd, ← Nat.div_div_eq_div_mul]
      have h3 := Nat.div_add_mod (w.toNat / 2 ^ (63 - k)) 2
      exact h3.symm
    have hr1v : ((rk <<< (1 : Nat)) +
        (if (divBitRun d r w 0 k).2.1.msb then (1 : Word) else 0)).toNat =
        2 * rk.toNat + b := by
      have h1 : (rk <<< (1 : Nat)).toNat = (2 * rk.toNat) % 2 ^ 64 := by
        rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
        ring_nf
      rw [hb, BitVec.toNat_add, h1, hbit]
      have h2rk : 2 * rk.toNat < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt h2rk]
      exact Nat.mod_eq_of_lt (by omega)
    have hdiv : r.toNat * 2 ^ (k + 1) + w.toNat / 2 ^ (64 - (k + 1)) =
        qk.toNat * (2 * d.toNat) + (2 * rk.toNat + b) := by
      rw [hprefix]
      have h2 : r.toNat * 2 ^ (k + 1) = 2 * (r.toNat * 2 ^ k) := by ring
      rw [h2, show 2 * (r.toNat * 2 ^ k) + (2 * (w.toNat / 2 ^ (64 - k)) + b) =
          2 * (r.toNat * 2 ^ k + w.toNat / 2 ^ (64 - k)) + b from by ring, heq]
      ring
    have hqk_bound : 2 * qk.toNat + 1 < 2 ^ 64 := by
      have h63 : 2 ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    by_cases hcase : BitVec.ule d ((rk <<< (1 : Nat)) +
        (if (divBitRun d r w 0 k).2.1.msb then (1 : Word) else 0))
    · have hdle : d.toNat ≤ 2 * rk.toNat + b := by
        have h := BitVec.ule_iff_toNat_le.mp hcase
        rwa [hr1v] at h
      have hnew : divBitRun d r w 0 (k + 1) =
          ((rk <<< (1 : Nat)) + (if (divBitRun d r w 0 k).2.1.msb then 1 else 0) - d,
           (divBitRun d r w 0 k).2.1 <<< (1 : Nat),
           (qk <<< (1 : Nat)) + 1) := by
        show divBitStep d rk (divBitRun d r w 0 k).2.1 qk = _
        dsimp only [divBitStep]
        rw [if_pos hcase]
      have hrd : (((rk <<< (1 : Nat)) +
          (if (divBitRun d r w 0 k).2.1.msb then (1 : Word) else 0)) - d).toNat =
          2 * rk.toNat + b - d.toNat := by
        rw [BitVec.toNat_sub, hr1v]
        have h3 : (2 ^ 64 - d.toNat + (2 * rk.toNat + b)) % 2 ^ 64 =
            2 * rk.toNat + b - d.toNat := by omega
        exact h3
      refine ⟨?_, ?_, ?_⟩
      · rw [hnew]
        dsimp only
        have hq1 : ((qk <<< (1 : Nat)) + 1).toNat = 2 * qk.toNat + 1 := by
          have h1 : (qk <<< (1 : Nat)).toNat = (2 * qk.toNat) % 2 ^ 64 := by
            rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
            ring_nf
          rw [BitVec.toNat_add, h1]
          rw [Nat.mod_eq_of_lt (by omega : 2 * qk.toNat < 2 ^ 64)]
          have h1t : (1 : Word).toNat = 1 := by decide
          rw [h1t]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hq1, hrd, hdiv]
        have h3 : (2 * qk.toNat + 1) * d.toNat = qk.toNat * (2 * d.toNat) + d.toNat := by
          ring
        rw [h3]
        omega
      · rw [hnew]
        dsimp only
        rw [hrd]
        omega
      · rw [hnew]
        dsimp only
        have hq1 : ((qk <<< (1 : Nat)) + 1).toNat = 2 * qk.toNat + 1 := by
          have h1 : (qk <<< (1 : Nat)).toNat = (2 * qk.toNat) % 2 ^ 64 := by
            rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
            ring_nf
          rw [BitVec.toNat_add, h1]
          rw [Nat.mod_eq_of_lt (by omega : 2 * qk.toNat < 2 ^ 64)]
          have h1t : (1 : Word).toNat = 1 := by decide
          rw [h1t]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hq1]
        have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        rw [h2]
        omega
    · have hgt : 2 * rk.toNat + b < d.toNat := by
        by_contra hcon
        have hcon' : d.toNat ≤ 2 * rk.toNat + b := by omega
        exact hcase (BitVec.ule_iff_toNat_le.mpr (by rwa [hr1v]))
      have hnew : divBitRun d r w 0 (k + 1) =
          ((rk <<< (1 : Nat)) + (if (divBitRun d r w 0 k).2.1.msb then 1 else 0),
           (divBitRun d r w 0 k).2.1 <<< (1 : Nat),
           qk <<< (1 : Nat)) := by
        show divBitStep d rk (divBitRun d r w 0 k).2.1 qk = _
        dsimp only [divBitStep]
        rw [if_neg hcase]
      refine ⟨?_, ?_, ?_⟩
      · rw [hnew]
        dsimp only
        have hq1 : (qk <<< (1 : Nat)).toNat = 2 * qk.toNat := by
          have h1 : (qk <<< (1 : Nat)).toNat = (2 * qk.toNat) % 2 ^ 64 := by
            rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
            ring_nf
          rw [h1]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hq1, hr1v, hdiv]
        ring
      · rw [hnew]
        dsimp only
        rw [hr1v]
        exact hgt
      · rw [hnew]
        dsimp only
        have hq1 : (qk <<< (1 : Nat)).toNat = 2 * qk.toNat := by
          have h1 : (qk <<< (1 : Nat)).toNat = (2 * qk.toNat) % 2 ^ 64 := by
            rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
            ring_nf
          rw [h1]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hq1]
        have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        rw [h2]
        omega

/-- After the full 64 iterations the machine has divided `r·2^64 + w` by `d`. -/
theorem divBitRun_64 (d r w : Word) (hd : 0 < d.toNat) (hd63 : d.toNat ≤ 2 ^ 63)
    (hr : r.toNat < d.toNat) :
    r.toNat * 2 ^ 64 + w.toNat =
      (divBitRun d r w 0 64).2.2.toNat * d.toNat + (divBitRun d r w 0 64).1.toNat ∧
      (divBitRun d r w 0 64).1.toNat < d.toNat := by
  obtain ⟨h1, h2, _⟩ := divBitRun_spec d r w hd hd63 hr 64 (le_refl 64)
  simpa using And.intro h1 h2

/-- The limb loop's pure model over a most-significant-first limb list. -/
def divLimbFrom (d rem : Word) : List Word → List Word × Word
  | [] => ([], rem)
  | a :: rest =>
      let (r', _, q) := divBitRun d rem a 0 64
      let (qs, rf) := divLimbFrom d r' rest
      (q :: qs, rf)

theorem divLimbFrom_length (d rem : Word) (ws : List Word) :
    (divLimbFrom d rem ws).1.length = ws.length := by
  induction ws generalizing rem with
  | nil => rfl
  | cons a rest ih => simp [divLimbFrom, ih]

theorem divLimbFrom_spec (d rem : Word) (hd : 0 < d.toNat) (hd63 : d.toNat ≤ 2 ^ 63)
    (hrem : rem.toNat < d.toNat) (ws : List Word) :
    rem.toNat * 2 ^ (64 * ws.length) + msbVal ws =
      msbVal (divLimbFrom d rem ws).1 * d.toNat + (divLimbFrom d rem ws).2.toNat ∧
      (divLimbFrom d rem ws).2.toNat < d.toNat := by
  induction ws generalizing rem with
  | nil =>
    simp [divLimbFrom, msbVal, hrem]
  | cons a rest ih =>
    obtain ⟨h64, hrlt⟩ := divBitRun_64 d rem a hd hd63 hrem
    obtain ⟨hrec, hrf⟩ := ih (divBitRun d rem a 0 64).1 hrlt
    have hpow : 2 ^ (64 * (rest.length + 1)) = 2 ^ 64 * 2 ^ (64 * rest.length) := by
      rw [show 64 * (rest.length + 1) = 64 * rest.length + 64 from by ring, pow_add,
        Nat.mul_comm]
    simp only [divLimbFrom, msbVal, List.length_cons, hpow]
    refine ⟨?_, hrf⟩
    have hlen : (divLimbFrom d (divBitRun d rem a 0 64).1 rest).1.length =
        rest.length := divLimbFrom_length _ _ _
    rw [hlen]
    have h2 : rem.toNat * (2 ^ 64 * 2 ^ (64 * rest.length)) +
        (a.toNat * 2 ^ (64 * rest.length) + msbVal rest) =
        (rem.toNat * 2 ^ 64 + a.toNat) * 2 ^ (64 * rest.length) + msbVal rest := by
      rw [← Nat.mul_assoc rem.toNat (2 ^ 64) (2 ^ (64 * rest.length)),
        Nat.add_mul (rem.toNat * 2 ^ 64) a.toNat (2 ^ (64 * rest.length)),
        Nat.add_assoc]
    rw [h2, h64]
    have h3 : ((divBitRun d rem a 0 64).2.2.toNat * d.toNat +
        (divBitRun d rem a 0 64).1.toNat) * 2 ^ (64 * rest.length) + msbVal rest =
        (divBitRun d rem a 0 64).2.2.toNat * 2 ^ (64 * rest.length) * d.toNat +
          ((divBitRun d rem a 0 64).1.toNat * 2 ^ (64 * rest.length) + msbVal rest) := by
      rw [Nat.add_mul ((divBitRun d rem a 0 64).2.2.toNat * d.toNat)
        (divBitRun d rem a 0 64).1.toNat (2 ^ (64 * rest.length)),
        Nat.mul_assoc (divBitRun d rem a 0 64).2.2.toNat d.toNat
          (2 ^ (64 * rest.length)),
        Nat.mul_comm d.toNat (2 ^ (64 * rest.length)),
        Nat.mul_assoc (divBitRun d rem a 0 64).2.2.toNat (2 ^ (64 * rest.length))
          d.toNat, Nat.add_assoc]
    rw [h3, hrec]
    have h4 : (divBitRun d rem a 0 64).2.2.toNat * 2 ^ (64 * rest.length) * d.toNat +
        (msbVal (divLimbFrom d (divBitRun d rem a 0 64).1 rest).1 * d.toNat +
          (divLimbFrom d (divBitRun d rem a 0 64).1 rest).2.toNat) =
        ((divBitRun d rem a 0 64).2.2.toNat * 2 ^ (64 * rest.length) +
          msbVal (divLimbFrom d (divBitRun d rem a 0 64).1 rest).1) * d.toNat +
          (divLimbFrom d (divBitRun d rem a 0 64).1 rest).2.toNat := by
      rw [Nat.add_mul ((divBitRun d rem a 0 64).2.2.toNat * 2 ^ (64 * rest.length))
        (msbVal (divLimbFrom d (divBitRun d rem a 0 64).1 rest).1) d.toNat,
        Nat.add_assoc]
    exact h4

/-- The machine's in-place 384-bit division by a u64 divisor: input limbs
    little-endian, quotient limbs little-endian, and the final remainder. -/
def div384by64 (d : Word) (ws : List Word) : List Word × Word :=
  let (qsRev, rf) := divLimbFrom d 0 ws.reverse
  (qsRev.reverse, rf)

theorem div384by64_length (d : Word) (ws : List Word) :
    (div384by64 d ws).1.length = ws.length := by
  simp [div384by64, divLimbFrom_length]

theorem div384by64_spec (d : Word) (ws : List Word)
    (hd : 0 < d.toNat) (hd63 : d.toNat ≤ 2 ^ 63) :
    limbsToNat ws = limbsToNat (div384by64 d ws).1 * d.toNat +
      (div384by64 d ws).2.toNat ∧ (div384by64 d ws).2.toNat < d.toNat := by
  have h0 : (0 : Word).toNat = 0 := by decide
  obtain ⟨hrec, hrf⟩ := divLimbFrom_spec d 0 hd hd63 (by rw [h0]; exact hd) ws.reverse
  rw [h0] at hrec
  simp only [div384by64]
  have h1 : msbVal ws.reverse = limbsToNat ws := by
    rw [msbVal_eq_limbsToNat_reverse, List.reverse_reverse]
  have h2 : msbVal (divLimbFrom d 0 ws.reverse).1 =
      limbsToNat (divLimbFrom d 0 ws.reverse).1.reverse :=
    msbVal_eq_limbsToNat_reverse _
  rw [h1, h2] at hrec
  simp only [zero_mul, Nat.zero_add] at hrec
  exact ⟨hrec, hrf⟩

theorem div384by64_quot (d : Word) (ws : List Word)
    (hd : 0 < d.toNat) (hd63 : d.toNat ≤ 2 ^ 63) :
    limbsToNat (div384by64 d ws).1 = limbsToNat ws / d.toNat := by
  obtain ⟨h1, h2⟩ := div384by64_spec d ws hd hd63
  have h3 : limbsToNat (div384by64 d ws).1 * d.toNat ≤ limbsToNat ws := by omega
  have h4 : limbsToNat ws < (limbsToNat (div384by64 d ws).1 + 1) * d.toNat := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  exact (Nat.div_eq_of_lt_le h3 h4).symm

/-! ## The fueled loop model -/

/-- Outcome of the machine's Taylor loop. -/
inductive PriceLoopOut where
  | done (finalSum : Nat)
  | ovf
  deriving DecidableEq

/-! ## Initial-state reachability at the iteration cap

`priceLoopFuel` is deliberately useful at arbitrary loop states, but its
overflow result alone cannot identify which arm fired.  In particular, the
synthetic state `i = 496, acc = 1, output = 0` reaches the cap in the fueled
model even though the exact bounded recurrence would still return `some 0`.
That state is not reachable from the entry state.  The prefix below records
the exact Nat recurrence from the entry `(i, acc, output) = (1, D, 0)` after a
fixed number of successful rounds.  Its monotonicity and the measured
prefix boundary pair `2076461206 / 2076461207` are **prefix-conditioned**:
after exactly 495 successful rounds the accumulator is `0` at the former
numerator
 and `1` at the latter, with the latter prefix output already at least
 `taylorOutputBound`.  It is therefore not the raw `taylorExp384` boundary
 `2073394370 / 2073394371`, which concerns the eventual 256-bit result of the
 full recurrence.  The prefix pair lets the cap arm be correlated with the
 model only after this reachability relation has been supplied by the
 outer-loop invariant. -/

def priceLoopPrefix (num : Nat) : Nat → Nat × Nat
  | 0 => (taylorDenominator, 0)
  | k + 1 =>
      let s := priceLoopPrefix num k
      (s.1 * num / (taylorDenominator * (k + 1)), s.2 + s.1)

theorem priceLoopPrefix_mono
    {num₁ num₂ k : Nat} (h_num : num₁ ≤ num₂) :
    (priceLoopPrefix num₁ k).1 ≤ (priceLoopPrefix num₂ k).1 ∧
      (priceLoopPrefix num₁ k).2 ≤ (priceLoopPrefix num₂ k).2 := by
  induction k with
  | zero =>
    exact ⟨le_rfl, le_rfl⟩
  | succ k ih =>
    simp only [priceLoopPrefix]
    obtain ⟨h_acc, h_output⟩ := ih
    constructor
    · apply Nat.div_le_div_right
      exact Nat.mul_le_mul h_acc h_num
    · exact Nat.add_le_add h_output h_acc

theorem priceLoopPrefix_cap_output_ge {num : Nat}
    (h_acc : 0 < (priceLoopPrefix num 495).1) :
    taylorOutputBound ≤ (priceLoopPrefix num 495).2 := by
  have h_lower : 2076461207 ≤ num := by
    by_contra h_not
    have h_num : num ≤ 2076461206 := by omega
    have h_acc_le := (priceLoopPrefix_mono (k := 495) h_num).1
    have h_zero : (priceLoopPrefix 2076461206 495).1 = 0 := by decide
    omega
  have h_output_mono := (priceLoopPrefix_mono (k := 495) h_lower).2
  have h_output_boundary :
      taylorOutputBound ≤ (priceLoopPrefix 2076461207 495).2 := by decide
  exact le_trans h_output_boundary h_output_mono

theorem priceLoopPrefix_cap_model_none {num : Nat}
    (h_acc : 0 < (priceLoopPrefix num 495).1) :
    taylor384Aux num taylorDenominator 496
        (priceLoopPrefix num 495).1
        (priceLoopPrefix num 495).2 = none := by
  have h_output := priceLoopPrefix_cap_output_ge h_acc
  have h_acc_ne : (priceLoopPrefix num 495).1 ≠ 0 := by omega
  have h_sum :
      taylorOutputBound ≤
        (priceLoopPrefix num 495).2 + (priceLoopPrefix num 495).1 :=
    le_trans h_output (Nat.le_add_right _ _)
  rw [taylor384Aux.eq_1, if_neg h_acc_ne, if_pos h_sum]

/-- The machine's Taylor loop as a pure fueled recursion, mirroring the
    guard order exactly: `acc = 0` exit, `i ≥ 496` exit, 384-bit sum
    overflow, 384-bit product overflow.  The `D·i ≥ 2^64` machine check is
    absent because it is provably dead while `i < 496`
    (`taylorDenominator * 495 < 2^64`). -/
def priceLoopFuel (num : Nat) : Nat → Nat → Nat → Nat → PriceLoopOut
  | 0, _, _, _ => .ovf
  | fuel + 1, i, acc, output =>
      if acc = 0 then .done output
      else if 496 ≤ i then .ovf
      else if taylorWord384Bound ≤ output + acc then .ovf
      else if taylorWord384Bound ≤ acc * num then .ovf
      else priceLoopFuel num fuel (i + 1) (acc * num / (taylorDenominator * i))
        (output + acc)

/-- The final sum of a `done` run dominates every intermediate `output + acc`. -/
theorem priceLoopFuel_done_ge (num : Nat) :
    ∀ (fuel i acc output S : Nat),
      priceLoopFuel num fuel i acc output = .done S → output + acc ≤ S := by
  intro fuel
  induction fuel with
  | zero =>
    intro i acc output S h
    simp [priceLoopFuel] at h
  | succ fuel ih =>
    intro i acc output S h
    simp only [priceLoopFuel] at h
    by_cases hacc : acc = 0
    · rw [if_pos hacc] at h
      simp at h
      omega
    · rw [if_neg hacc] at h
      by_cases hi : 496 ≤ i
      · rw [if_pos hi] at h
        simp at h
      · rw [if_neg hi] at h
        by_cases hsum : taylorWord384Bound ≤ output + acc
        · rw [if_pos hsum] at h
          simp at h
        · rw [if_neg hsum] at h
          by_cases hprod : taylorWord384Bound ≤ acc * num
          · rw [if_pos hprod] at h
            simp at h
          · rw [if_neg hprod] at h
            have hle := ih (i + 1) (acc * num / (taylorDenominator * i))
              (output + acc) S h
            exact Nat.le_trans (Nat.le_add_right _ _) hle

/- A done result cannot cross the 384-bit sum bound when the current output is
   below it.  The recursive branch gets exactly the next-state output bound
   from the current sum guard.  The separate 256-bit representability check
   belongs to the exit-divide tail, which consumes the completed sum. -/
theorem priceLoopFuel_done_word384_bound (num : Nat) :
    ∀ (fuel i acc output S : Nat),
      output < taylorWord384Bound →
      priceLoopFuel num fuel i acc output = .done S →
        S < taylorWord384Bound := by
  intro fuel
  induction fuel with
  | zero =>
    intro i acc output S _ h
    simp [priceLoopFuel] at h
  | succ fuel ih =>
    intro i acc output S h_output h
    simp only [priceLoopFuel] at h
    by_cases h_acc : acc = 0
    · rw [if_pos h_acc] at h
      simp only [PriceLoopOut.done.injEq] at h
      simpa [h] using h_output
    · rw [if_neg h_acc] at h
      by_cases h_i : 496 ≤ i
      · rw [if_pos h_i] at h
        simp at h
      · rw [if_neg h_i] at h
        by_cases h_sum : taylorWord384Bound ≤ output + acc
        · rw [if_pos h_sum] at h
          simp at h
        · rw [if_neg h_sum] at h
          by_cases h_prod : taylorWord384Bound ≤ acc * num
          · rw [if_pos h_prod] at h
            simp at h
          · rw [if_neg h_prod] at h
            apply ih (i + 1) (acc * num / (taylorDenominator * i))
              (output + acc) S
            · exact Nat.lt_of_not_ge h_sum
            · exact h

/-- Crux: whenever the machine loop reaches its `acc = 0` exit with a final
    sum below the 256-bit output bound, the SpecRef bounded model agrees and
    returns `some (sum / D)`. -/
theorem priceLoopFuel_done_taylor (num : Nat) :
    ∀ (fuel i acc output S : Nat),
      priceLoopFuel num fuel i acc output = .done S →
        S < taylorOutputBound →
        taylor384Aux num taylorDenominator i acc output =
          some (S / taylorDenominator) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i acc output S h _
    simp [priceLoopFuel] at h
  | succ fuel ih =>
    intro i acc output S h hS
    simp only [priceLoopFuel] at h
    by_cases hacc : acc = 0
    · rw [if_pos hacc] at h
      simp only [PriceLoopOut.done.injEq] at h
      subst h
      rw [taylor384Aux.eq_1, if_pos hacc, if_pos hS]
    · rw [if_neg hacc] at h
      by_cases hi : 496 ≤ i
      · rw [if_pos hi] at h
        simp at h
      · rw [if_neg hi] at h
        by_cases hsum : taylorWord384Bound ≤ output + acc
        · rw [if_pos hsum] at h
          simp at h
        · rw [if_neg hsum] at h
          by_cases hprod : taylorWord384Bound ≤ acc * num
          · rw [if_pos hprod] at h
            simp at h
          · rw [if_neg hprod] at h
            have hge := priceLoopFuel_done_ge num fuel (i + 1)
              (acc * num / (taylorDenominator * i)) (output + acc) S h
            have hle : output + acc ≤ S := Nat.le_trans (Nat.le_add_right _ _) hge
            have hout : ¬ taylorOutputBound ≤ output + acc := by omega
            have hih := ih (i + 1) (acc * num / (taylorDenominator * i))
              (output + acc) S h hS
            rw [taylor384Aux.eq_1, if_neg hacc, if_neg hout, if_neg hprod]
            exact hih

/-- The canonical output bytes of the routine: the 32-byte big-endian
    encoding of the model price when it exists.  The status-1 arm of the K70
    contract ignores `outBytes`, so the `none` case is arbitrary. -/
def priceBytes (excess : Word) : List (BitVec 8) :=
  match taylorExp384 excess.toNat with
  | some p => beBytes32OfNat p
  | none => List.replicate 32 0

theorem priceBytes_length (excess : Word) : (priceBytes excess).length = 32 := by
  simp only [priceBytes]
  split
  · exact beBytes32OfNat_length _
  · simp

#print axioms priceLoopFuel_done_word384_bound
#print axioms priceLoopPrefix_mono
#print axioms priceLoopPrefix_cap_output_ge
#print axioms priceLoopPrefix_cap_model_none

end EvmAsm.Codegen.AmsterdamBlobGasPrice
