/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakBridge

  Pure bridge: operational `keccakBodyDigest` (guest sponge post of
  `zkvm_keccak256_spec_within`) equals SpecRef `keccak256`.

  Statement domain matches the machine triple:
    `input.length = keccakAbsorbStep * N + rem` with `rem < keccakAbsorbStep`
  (`keccakAbsorbStep = 136 = keccakRateBytes`).

  No machine edits. No emitted-guest changes. No maxRecDepth raise —
  concrete KATs are split like #12045/#12048.

  Load-bearing consumer: #12038 transaction signing-hash names
  `keccakBodyDigest_eq_specref` as a dependency. Other rewrite sites
  (KECCAK256 opcode, CREATE2, trie keys) also benefit.
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakBody
import EvmAsm.Codegen.Proofs.HashBridgeKeccakDword
import EvmAsm.Codegen.Proofs.HashBridgeKeccakOuter
import EvmAsm.Codegen.Proofs.HashBridgeKeccakPure
import EvmAsm.Codegen.Proofs.HashBridgeKeccakSpec
import EvmAsm.Codegen.Proofs.HashBridgeKeccakTail
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.SAsm.AccelStep
import EvmAsm.Rv64.SAsm.KeccakStep
import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.MultiRw
import EvmAsm.Rv64.SAsm.RaSpill
import EvmAsm.Stateless.SpecRef.Crypto
import Mathlib.Tactic.Ring

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Stateless.SpecRef

/-! ## Endian helpers: `dwordBytes` ↔ `natToBytesLE` -/

private theorem range8_eq : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by
  decide

private theorem extractByte_toNat_div (w : Word) (j : Nat) (_hj : j < 8) :
    (extractByte w j).toNat = w.toNat / 256 ^ j % 256 := by
  simp only [extractByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  have h8j : 2 ^ (j * 8) = 256 ^ j := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; ring
  rw [Nat.shiftRight_eq_div_pow, h8j]

private theorem extractByte_eq_ofNat_shift (w : Word) (j : Nat) (hj : j < 8) :
    extractByte w j = BitVec.ofNat 8 (w.toNat >>> (8 * j)) := by
  apply BitVec.eq_of_toNat_eq
  rw [extractByte_toNat_div w j hj, BitVec.toNat_ofNat]
  have hsh : w.toNat >>> (8 * j) = w.toNat / 2 ^ (8 * j) :=
    Nat.shiftRight_eq_div_pow _ _
  have hpow : (2 : Nat) ^ (8 * j) = 256 ^ j := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  rw [hsh, hpow]

/-- `dwordBytes` is the LE byte view used by SpecRef `natToBytesLE 8`. -/
theorem dwordBytes_eq_natToBytesLE (w : Word) :
    dwordBytes w = natToBytesLE 8 w.toNat := by
  simp only [dwordBytes, natToBytesLE, range8_eq, List.map_cons, List.map_nil]
  simp only [
    extractByte_eq_ofNat_shift w 0 (by omega),
    extractByte_eq_ofNat_shift w 1 (by omega),
    extractByte_eq_ofNat_shift w 2 (by omega),
    extractByte_eq_ofNat_shift w 3 (by omega),
    extractByte_eq_ofNat_shift w 4 (by omega),
    extractByte_eq_ofNat_shift w 5 (by omega),
    extractByte_eq_ofNat_shift w 6 (by omega),
    extractByte_eq_ofNat_shift w 7 (by omega)]

/-! ## Pad suffix under machine `rem` -/

private theorem keccakPad_suffix_rem_max (msg : Bytes)
    (hrem : msg.length % keccakRateBytes = keccakRateBytes - 1) :
    (keccakPad msg).drop msg.length = [(0x81 : Byte)] := by
  unfold keccakPad
  have hpad : keccakRateBytes - msg.length % keccakRateBytes = 1 := by
    rw [hrem]; simp [keccakRateBytes]
  simp only [hpad, ↓reduceIte]
  rw [List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]

private theorem keccakPad_suffix_rem_lt (msg : Bytes)
    (hrem : msg.length % keccakRateBytes ≠ keccakRateBytes - 1) :
    (keccakPad msg).drop msg.length =
      (0x01 : Byte) ::
        List.replicate (keccakRateBytes - msg.length % keccakRateBytes - 2) (0 : Byte) ++
        [(0x80 : Byte)] := by
  unfold keccakPad
  have hmod : msg.length % keccakRateBytes < keccakRateBytes :=
    Nat.mod_lt _ (by simp [keccakRateBytes])
  have hpad : keccakRateBytes - msg.length % keccakRateBytes ≠ 1 := by
    intro h
    exact hrem (by omega)
  simp only [hpad, ↓reduceIte]
  rw [List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]

theorem keccakPad_suffix_of_mod (msg : Bytes) :
    let rem := msg.length % keccakRateBytes
    (keccakPad msg).drop msg.length =
      if rem = keccakRateBytes - 1 then [(0x81 : Byte)]
      else (0x01 : Byte) ::
        List.replicate (keccakRateBytes - rem - 2) (0 : Byte) ++
        [(0x80 : Byte)] := by
  dsimp only
  by_cases hrem : msg.length % keccakRateBytes = keccakRateBytes - 1
  · simp only [hrem, ↓reduceIte]
    exact keccakPad_suffix_rem_max msg hrem
  · simp only [hrem, ↓reduceIte]
    exact keccakPad_suffix_rem_lt msg hrem

/-- Guest pad at `rem = 135` collapses the two domain writes to `0x81`. -/
theorem keccakGuestPad_rem135 (st : List (BitVec 8)) (hst : 135 < st.length) :
    keccakGuestPad st 135 =
      setBytes st 135 [st.getD 135 0 ^^^ (0x81 : BitVec 8)] := by
  unfold keccakGuestPad
  rw [setBytes_singleton, setBytes_singleton]
  have hget :
      (st.set 135 (st.getD 135 0 ^^^ (1 : BitVec 8))).getD 135 0 =
        st.getD 135 0 ^^^ (1 : BitVec 8) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega)]
    rfl
  rw [hget]
  have hxor (b : BitVec 8) :
      (b ^^^ (1 : BitVec 8)) ^^^ (0x80 : BitVec 8) = b ^^^ (0x81 : BitVec 8) := by
    -- 1 ^^^ 0x80 = 0x81 definitionally on BitVec 8
    rw [BitVec.xor_assoc]; rfl
  rw [hxor, List.set_set, ← setBytes_singleton]

/-! ## `bytesLEtoNat` of `dwordBytes` recovers `toNat` -/

private theorem shiftRight_succ_byte (n i : Nat) :
    n >>> (8 * (i + 1)) = (n / 256) >>> (8 * i) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  -- LHS: n / 2^(8*(i+1)); RHS: (n/256) / 2^(8*i) = n / (256 * 2^(8*i))
  have hpow : (2 : Nat) ^ (8 * (i + 1)) = 256 * 2 ^ (8 * i) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
  rw [hpow, ← Nat.div_div_eq_div_mul]

/-- `n % (b * c) = n % b + b * ((n / b) % c)` when `0 < b` and `0 < c`. -/
private theorem mod_mul_split (n b c : Nat) (hb : 0 < b) (hc : 0 < c) :
    n % (b * c) = n % b + b * ((n / b) % c) := by
  set q := n / b
  set r := n % b
  set q2 := q % c
  set r2 := q / c
  have hn : n = r + b * q := by
    change n = n % b + b * (n / b); exact (Nat.mod_add_div n b).symm
  have hq : q = q2 + c * r2 := by
    change q = q % c + c * (q / c); exact (Nat.mod_add_div q c).symm
  have hr_lt : r < b := by change n % b < b; exact Nat.mod_lt n hb
  have hq2_lt : q2 < c := by change q % c < c; exact Nat.mod_lt q hc
  have hsum_lt : r + b * q2 < b * c := by
    have h1 : b * q2 + r < b * q2 + b := Nat.add_lt_add_left hr_lt _
    have h2 : b * q2 + b = b * (q2 + 1) := by ring
    have h3 : b * (q2 + 1) ≤ b * c :=
      Nat.mul_le_mul_left b (Nat.succ_le_of_lt hq2_lt)
    -- r + b*q2 = b*q2 + r
    have hcomm : r + b * q2 = b * q2 + r := Nat.add_comm _ _
    omega
  have hn' : n = (r + b * q2) + (b * c) * r2 := by
    calc
      n = r + b * q := hn
      _ = r + b * (q2 + c * r2) := by rw [hq]
      _ = r + b * q2 + b * (c * r2) := by ring
      _ = r + b * q2 + (b * c) * r2 := by ring
  -- Fold lets back so the goal mentions n%b etc.
  show n % (b * c) = n % b + b * ((n / b) % c)
  calc
    n % (b * c) = ((r + b * q2) + (b * c) * r2) % (b * c) := by rw [hn']
    _ = (r + b * q2) % (b * c) := by rw [Nat.add_mul_mod_self_left]
    _ = r + b * q2 := Nat.mod_eq_of_lt hsum_lt
    _ = n % b + b * ((n / b) % c) := by rfl

/-- `bytesLEtoNat (natToBytesLE w n) = n % 256^w`. -/
private theorem bytesLEtoNat_natToBytesLE (width n : Nat) :
    bytesLEtoNat (natToBytesLE width n) = n % 256 ^ width := by
  induction width generalizing n with
  | zero =>
    simp only [natToBytesLE, List.range_zero, List.map_nil, bytesLEtoNat, Nat.pow_zero,
      Nat.mod_one]
  | succ w ih =>
    simp only [natToBytesLE, List.range_succ_eq_map, List.map_cons, List.map_map,
      bytesLEtoNat]
    have h0 : (BitVec.ofNat 8 (n >>> 0)).toNat = n % 256 := by
      simp [BitVec.toNat_ofNat, Nat.shiftRight_zero]
    have hcomp :
        ((fun i => BitVec.ofNat 8 (n >>> (8 * i))) ∘ Nat.succ) =
          fun i => BitVec.ofNat 8 (n >>> (8 * (i + 1))) := rfl
    rw [hcomp]
    have htail :
        (List.range w).map (fun i => BitVec.ofNat 8 (n >>> (8 * (i + 1)))) =
          natToBytesLE w (n / 256) := by
      simp only [natToBytesLE]
      refine List.map_congr_left ?_
      intro i _
      congr 1
      exact shiftRight_succ_byte n i
    rw [h0, htail, ih]
    have hpow : (256 : Nat) ^ (w + 1) = 256 * 256 ^ w := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have hpow_pos : 0 < 256 ^ w := Nat.pow_pos (by decide)
    rw [hpow, mod_mul_split n 256 (256 ^ w) (by decide) hpow_pos]

private theorem bytesLEtoNat_dwordBytes (w : Word) :
    bytesLEtoNat (dwordBytes w) = w.toNat := by
  rw [dwordBytes_eq_natToBytesLE, bytesLEtoNat_natToBytesLE]
  have hlt : w.toNat < 256 ^ 8 := by
    have := w.isLt
    change w.toNat < 2 ^ 64 at this
    change w.toNat < (2 ^ 8) ^ 8
    rwa [← Nat.pow_mul]
  exact Nat.mod_eq_of_lt hlt

theorem packBytes_toNat_of_length_8 (bs : List (BitVec 8)) (h : bs.length = 8) :
    (packBytes bs).toNat = bytesLEtoNat bs := by
  have hdb : dwordBytes (packBytes bs) = bs := dwordBytes_packBytes bs h
  have hle := bytesLEtoNat_dwordBytes (packBytes bs)
  rw [← hle, hdb]

/-! ## Digest copy = first 32 bytes -/

private theorem setBytes_at0_full (bs ns : List (BitVec 8))
    (h : ns.length = bs.length) :
    setBytes bs 0 ns = ns := by
  have hslot := setBytes_slot bs ns 0 (by omega)
  simp only [List.drop_zero] at hslot
  -- hslot : (setBytes bs 0 ns).take ns.length = ns
  have hlen : (setBytes bs 0 ns).length = ns.length := by
    rw [length_setBytes, h]
  have htake : (setBytes bs 0 ns).take ns.length = setBytes bs 0 ns :=
    List.take_of_length_le (Nat.le_of_eq hlen)
  rwa [htake] at hslot

/-- `take (m+n) = take m ++ (drop m).take n`. -/
private theorem take_add_eq (l : List (BitVec 8)) (m n : Nat) :
    l.take (m + n) = l.take m ++ (l.drop m).take n := by
  induction m generalizing l with
  | zero => simp
  | succ m ih =>
    cases l with
    | nil => simp
    | cons x xs =>
      simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      rw [show m + 1 + n = (m + n) + 1 from by omega, List.take_succ_cons]
      exact congrArg (List.cons x) (ih xs)

/-- Four-chunk split of `take 32` (left-assoc `++`, matches setBytes_append peel). -/
private theorem take32_chunks (st : List (BitVec 8)) (_hst : 32 ≤ st.length) :
    st.take 8 ++ (st.drop 8).take 8 ++ (st.drop 16).take 8 ++ (st.drop 24).take 8 =
      st.take 32 := by
  -- ++ is left-assoc: ((a++b)++c)++d
  have h16 : st.take 8 ++ (st.drop 8).take 8 = st.take 16 := by
    rw [show 16 = 8 + 8 from rfl, take_add_eq]
  have h24 :
      st.take 8 ++ (st.drop 8).take 8 ++ (st.drop 16).take 8 = st.take 24 := by
    rw [h16, show 24 = 16 + 8 from rfl, take_add_eq]
  rw [h24, show 32 = 24 + 8 from rfl, take_add_eq]

/-- Right-assoc form for `List.flatMap` nesting. -/
private theorem take32_chunks_right (st : List (BitVec 8)) (hst : 32 ≤ st.length) :
    st.take 8 ++
        ((st.drop 8).take 8 ++ ((st.drop 16).take 8 ++ (st.drop 24).take 8)) =
      st.take 32 := by
  -- Convert left-assoc chunks via append_assoc (finite, no simp loop)
  have h := take32_chunks st hst
  -- h: ((a++b)++c)++d = take32
  -- want: a++(b++(c++d)) = take32
  have h1 :
      st.take 8 ++ (st.drop 8).take 8 ++ (st.drop 16).take 8 ++ (st.drop 24).take 8 =
        st.take 8 ++
          ((st.drop 8).take 8 ++ ((st.drop 16).take 8 ++ (st.drop 24).take 8)) := by
    -- expand both sides via two append_assoc applications
    calc
      st.take 8 ++ (st.drop 8).take 8 ++ (st.drop 16).take 8 ++ (st.drop 24).take 8
          = (st.take 8 ++ (st.drop 8).take 8 ++ (st.drop 16).take 8) ++
              (st.drop 24).take 8 := rfl
      _ = (st.take 8 ++ ((st.drop 8).take 8 ++ (st.drop 16).take 8)) ++
              (st.drop 24).take 8 := by
            congr 1
            exact List.append_assoc _ _ _
      _ = st.take 8 ++ (((st.drop 8).take 8 ++ (st.drop 16).take 8) ++
              (st.drop 24).take 8) := List.append_assoc _ _ _
      _ = st.take 8 ++ ((st.drop 8).take 8 ++ ((st.drop 16).take 8 ++
              (st.drop 24).take 8)) := by
            congr 1
            exact List.append_assoc _ _ _
  exact h1.symm.trans h

/-- Four successive dword splices into a zero buffer recover `st.take 32`. -/
theorem keccakDigestCopy_eq_take32 (st : List (BitVec 8)) (hst : 32 ≤ st.length) :
    keccakDigestCopy st = st.take 32 := by
  unfold keccakDigestCopy
  simp only [List.drop_zero]
  have h0 : (st.take 8).length = 8 := by
    rw [List.length_take, min_eq_left (by omega)]
  have h8 : ((st.drop 8).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, min_eq_left (by omega)]
  have h16l : ((st.drop 16).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, min_eq_left (by omega)]
  -- Left-assoc concat: setBytes_append peels the rightmost chunk each time
  have hchain :
      setBytes (List.replicate 32 (0 : BitVec 8)) 0
          (st.take 8 ++ (st.drop 8).take 8 ++ (st.drop 16).take 8 ++
            (st.drop 24).take 8) =
        setBytes
          (setBytes
            (setBytes
              (setBytes (List.replicate 32 (0 : BitVec 8)) 0 (st.take 8))
              8 ((st.drop 8).take 8))
            16 ((st.drop 16).take 8))
          24 ((st.drop 24).take 8) := by
    -- Peel d, then c, then b (rightmost first for left-assoc xs++ys)
    rw [setBytes_append]
    -- setBytes (setBytes k (a++b++c)) |(a++b++c)| d
    rw [setBytes_append]
    rw [setBytes_append]
    simp only [List.length_append, h0, h8, h16l, Nat.zero_add]
  rw [← hchain, take32_chunks st hst, setBytes_at0_full]
  rw [List.length_take, List.length_replicate, min_eq_left hst]

private theorem map_take_eq {α β : Type _} (f : α → β) (l : List α) (n : Nat) :
    (l.map f).take n = (l.take n).map f := by
  induction l generalizing n with
  | nil => cases n <;> simp
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.map_cons, List.take_succ_cons, List.map_cons]
      rw [ih]

/-- Squeeze of the 25-lane dword decode of a 200-byte state is `st.take 32`. -/
theorem keccakSqueeze32_of_stateBytes (st : List (BitVec 8)) (hst : st.length = 200) :
    keccakSqueeze32 (keccakDwords st 0) = st.take 32 := by
  unfold keccakSqueeze32 keccakDwords wsDword
  simp only [Nat.zero_add]
  have htake :
      ((List.range 25).map fun i =>
          packBytes ((st.drop (8 * i)).take 8)).take 4 =
        (List.range 4).map fun i =>
          packBytes ((st.drop (8 * i)).take 8) := by
    rw [map_take_eq]
    have hr : (List.range 25).take 4 = List.range 4 := by decide
    rw [hr]
  rw [htake]
  have hlane (i : Nat) (_hi : i < 4) :
      natToBytesLE 8 (packBytes ((st.drop (8 * i)).take 8)).toNat =
        (st.drop (8 * i)).take 8 := by
    have hlen : ((st.drop (8 * i)).take 8).length = 8 := by
      rw [List.length_take, List.length_drop, min_eq_left (by omega)]
    rw [← dwordBytes_eq_natToBytesLE, dwordBytes_packBytes _ hlen]
  -- Expand map/flatMap on [0,1,2,3] by hand to avoid simp recursion
  have hr4 : List.range 4 = [0, 1, 2, 3] := by decide
  rw [hr4]
  simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [hlane 0 (by omega), hlane 1 (by omega), hlane 2 (by omega), hlane 3 (by omega)]
  -- drop (8*0) = drop 0
  simp only [Nat.mul_zero, List.drop_zero]
  exact take32_chunks_right st (by omega)

/-! ## Full-state overwrite = `keccakStateBytes ∘ keccakF ∘ keccakDwords` -/

theorem setBytes_keccakBytes_eq_stateBytes (st : List (BitVec 8))
    (hst : st.length = 200) :
    setBytes st 0 (keccakBytes st 0) =
      keccakStateBytes (Accel.keccakF (keccakDwords st 0)) := by
  have hlen : (keccakBytes st 0).length = 200 := length_keccakBytes st 0
  have hfull := setBytes_at0_full st (keccakBytes st 0) (by rw [hlen, hst])
  rw [hfull]
  rfl


/-- Length of `flatMap dwordBytes` over a lane list. -/
private theorem length_flatMap_dwordBytes_lanes (st : List (BitVec 64)) :
    (st.flatMap dwordBytes).length = 8 * st.length := by
  induction st with
  | nil => simp
  | cons y ys ih =>
    simp only [List.flatMap_cons, List.length_append, length_dwordBytes,
      List.length_cons, ih]
    omega

/-- The `i`-th 8-byte window of `flatMap dwordBytes st` is `dwordBytes st[i]`. -/
private theorem flatMap_dwordBytes_drop_take (st : List (BitVec 64)) (i : Nat)
    (hi : i < st.length) :
    ((st.flatMap dwordBytes).drop (8 * i)).take 8 = dwordBytes st[i] := by
  induction st generalizing i with
  | nil =>
    exact False.elim (Nat.not_lt_zero i hi)
  | cons y ys ih =>
    cases i with
    | zero =>
      simp only [List.flatMap_cons, Nat.mul_zero, List.drop_zero]
      have hlen : (dwordBytes y).length = 8 := length_dwordBytes y
      rw [List.take_append_of_le_length (by omega)]
      exact List.take_of_length_le (by omega)
    | succ i =>
      simp only [List.flatMap_cons]
      have hlen : (dwordBytes y).length = 8 := length_dwordBytes y
      have hdrop :
          ((dwordBytes y ++ ys.flatMap dwordBytes).drop (8 * (i + 1))) =
            (ys.flatMap dwordBytes).drop (8 * i) := by
        have heq : 8 * (i + 1) = 8 + 8 * i := by omega
        rw [heq, List.drop_append]
        have hnil : (dwordBytes y).drop (8 + 8 * i) = [] :=
          List.drop_of_length_le (by omega)
        rw [hnil, List.nil_append, hlen]
        congr 1
        omega
      rw [hdrop]
      exact ih i (by simp at hi; omega)

/-- Recover 25 lanes from their LE byte image. -/
theorem keccakDwords_of_stateBytes (st : List (BitVec 64))
    (hst : st.length = 25) :
    keccakDwords (keccakStateBytes st) 0 = st := by
  unfold keccakDwords keccakStateBytes wsDword
  simp only [Nat.zero_add]
  apply List.ext_getElem
  · simp [List.length_map, List.length_range, hst]
  · intro i hi _
    simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range]
    have hi' : i < st.length := by omega
    rw [flatMap_dwordBytes_drop_take st i hi', packBytes_dwordBytes]


/-! ## XOR dword absorb ↔ SpecRef `keccakAbsorbBlock` -/

private theorem bytesLEtoNat_lt_pow64 (bs : List (BitVec 8)) (h : bs.length = 8) :
    bytesLEtoNat bs < 2 ^ 64 := by
  have hbound : ∀ (xs : List (BitVec 8)), bytesLEtoNat xs < 256 ^ xs.length := by
    intro xs
    induction xs with
    | nil => simp [bytesLEtoNat]
    | cons b bs ih =>
      simp only [bytesLEtoNat, List.length_cons]
      have hb : b.toNat < 256 := b.isLt
      have hpow : (256 : Nat) ^ (bs.length + 1) = 256 * 256 ^ bs.length := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow]
      have : bytesLEtoNat bs < 256 ^ bs.length := ih
      omega
  have := hbound bs
  rw [h] at this
  change bytesLEtoNat bs < (2 ^ 8) ^ 8 at this
  rwa [← Nat.pow_mul] at this

private theorem packBytes_eq_ofNat_bytesLE (bs : List (BitVec 8)) (h : bs.length = 8) :
    packBytes bs = BitVec.ofNat 64 (bytesLEtoNat bs) := by
  apply BitVec.eq_of_toNat_eq
  rw [packBytes_toNat_of_length_8 bs h, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (bytesLEtoNat_lt_pow64 bs h)]

/-- `getByteAt` of a full list at `8*lane+off` equals the window byte. -/
private theorem getByteAt_lane_window (xs : List (BitVec 8)) (lane off : Nat)
    (hx : xs.length = 200) (hl : lane < 25) (ho : off < 8) :
    getByteAt xs (8 * lane + off) =
      getByteAt ((xs.drop (8 * lane)).take 8) off := by
  unfold getByteAt
  have hxj : 8 * lane + off < xs.length := by omega
  have hwin : off < ((xs.drop (8 * lane)).take 8).length := by
    simp [List.length_take, List.length_drop, hx]; omega
  rw [dif_pos hxj, dif_pos hwin]
  -- xs[8*lane+off] = (drop)[off] = (take 8 drop)[off]
  have hdrop : (xs.drop (8 * lane))[off]'(by simp [List.length_drop, hx]; omega) =
      xs[8 * lane + off] :=
    List.getElem_drop (xs := xs) (i := 8 * lane) (j := off)
  have htake : ((xs.drop (8 * lane)).take 8)[off]'(by
      simp [List.length_take, List.length_drop, hx]; omega) =
      (xs.drop (8 * lane))[off]'(by simp [List.length_drop, hx]; omega) :=
    List.getElem_take (xs := xs.drop (8 * lane)) (j := 8) (i := off)
  exact (htake.trans hdrop).symm

/-- Window equality for all 25 lanes ⇒ full 200-byte equality via getByteAt. -/
private theorem eq_of_lane_windows {xs ys : List (BitVec 8)}
    (hx : xs.length = 200) (hy : ys.length = 200)
    (h : ∀ i, i < 25 → ((xs.drop (8 * i)).take 8) = ((ys.drop (8 * i)).take 8)) :
    xs = ys := by
  apply List.ext_getElem
  · rw [hx, hy]
  · intro j hjx hjy
    have hj200 : j < 200 := by rwa [hx] at hjx
    let lane := j / 8
    let off := j % 8
    have hl : lane < 25 := by dsimp [lane]; omega
    have ho : off < 8 := by dsimp [off]; exact Nat.mod_lt j (by decide)
    have hj_eq : j = 8 * lane + off := by
      dsimp [lane, off]; exact (Nat.div_add_mod j 8).symm
    have hwin := h lane hl
    have hxg : getByteAt xs j = xs[j] := by unfold getByteAt; rw [dif_pos hjx]
    have hyg : getByteAt ys j = ys[j] := by unfold getByteAt; rw [dif_pos hjy]
    have hxw := getByteAt_lane_window xs lane off hx hl ho
    have hyw := getByteAt_lane_window ys lane off hy hl ho
    -- getByteAt xs j = getByteAt window_xs off = getByteAt window_ys off = getByteAt ys j
    have : getByteAt xs j = getByteAt ys j := by
      rw [hj_eq, hxw, hyw, hwin]
    rw [← hxg, ← hyg, this]

/-- Lanes ≥ q untouched. -/
private theorem xorDwordsUpTo_lane_ge (st blk : List (BitVec 8)) (q j : Nat)
    (hst : st.length = 200) (hj : q ≤ j) (_hj8 : 8 * (j + 1) ≤ 200) :
    ((xorDwordsUpTo st blk q).drop (8 * j)).take 8 =
      ((st.drop (8 * j)).take 8) := by
  induction q generalizing st with
  | zero => rfl
  | succ q ih =>
    -- xorDwordsUpTo st blk (q+1) = xorDwordAt (xorDwordsUpTo st blk q) q v
    change
      ((xorDwordAt (xorDwordsUpTo st blk q) q
          (packBytes ((blk.drop (8 * q)).take 8))).drop (8 * j)).take 8 =
        ((st.drop (8 * j)).take 8)
    unfold xorDwordAt
    set st' := xorDwordsUpTo st blk q
    -- write ends at 8*(q+1) ≤ 8*j since q+1 ≤ j
    have hdrop := setBytes_drop_of_le
      (dwordBytes
        (packBytes ((st'.drop (8 * q)).take 8) ^^^
          packBytes ((blk.drop (8 * q)).take 8)))
      st' (8 * q) (8 * j) (by rw [length_dwordBytes]; omega)
    rw [hdrop]
    -- st' = xorDwordsUpTo st blk q; IH on original st
    exact ih st hst (by omega)

/-- Lane j < q holds XOR. -/
private theorem xorDwordsUpTo_lane_lt (st blk : List (BitVec 8)) (q j : Nat)
    (hst : st.length = 200) (hblk : 8 * q ≤ blk.length)
    (hj : j < q) (hj8 : 8 * (j + 1) ≤ 200) :
    ((xorDwordsUpTo st blk q).drop (8 * j)).take 8 =
      dwordBytes
        (packBytes ((st.drop (8 * j)).take 8) ^^^
          packBytes ((blk.drop (8 * j)).take 8)) := by
  induction q generalizing st with
  | zero => omega
  | succ q ih =>
    change
      ((xorDwordAt (xorDwordsUpTo st blk q) q
          (packBytes ((blk.drop (8 * q)).take 8))).drop (8 * j)).take 8 =
        dwordBytes
          (packBytes ((st.drop (8 * j)).take 8) ^^^
            packBytes ((blk.drop (8 * j)).take 8))
    unfold xorDwordAt
    set st' := xorDwordsUpTo st blk q
    have hst' : st'.length = 200 := by
      simp only [st']; rw [xorDwordsUpTo_length]; exact hst
    by_cases hjq : j = q
    · subst hjq
      have hprev :
          ((st'.drop (8 * j)).take 8) = ((st.drop (8 * j)).take 8) :=
        xorDwordsUpTo_lane_ge st blk j j hst (Nat.le_refl _) hj8
      set ns :=
        dwordBytes
          (packBytes ((st'.drop (8 * j)).take 8) ^^^
            packBytes ((blk.drop (8 * j)).take 8))
      have hns : ns.length = 8 := by simp [ns, length_dwordBytes]
      have hns' :
          ns =
            dwordBytes
              (packBytes ((st.drop (8 * j)).take 8) ^^^
                packBytes ((blk.drop (8 * j)).take 8)) := by
        dsimp only [ns]; rw [hprev]
      -- Match goal to setBytes form (drop `have old :=` sugar)
      change ((setBytes st' (8 * j) ns).drop (8 * j)).take 8 =
        dwordBytes
          (packBytes ((st.drop (8 * j)).take 8) ^^^
            packBytes ((blk.drop (8 * j)).take 8))
      have hslot := setBytes_slot st' ns (8 * j) (by omega)
      simpa [hns, hns'] using hslot
    · -- earlier: write after window
      have hj' : j < q := by omega
      have hblk' : 8 * q ≤ blk.length := by omega
      set ns :=
        dwordBytes
          (packBytes ((st'.drop (8 * q)).take 8) ^^^
            packBytes ((blk.drop (8 * q)).take 8))
      have hns : ns.length = 8 := by simp [ns, length_dwordBytes]
      -- drop then take: write is at 8*q > 8*j+8-1
      have hdrop := setBytes_drop_of_ge ns st' (8 * q) (8 * j) (by omega)
      rw [hdrop]
      have hk : 8 * q - 8 * j = 8 * (q - j) := by omega
      rw [hk]
      have htake := setBytes_take_of_ge ns (st'.drop (8 * j)) (8 * (q - j)) 8
        (by omega)
      rw [htake]
      exact ih st hst hblk' hj'

private def absorbLaneVec (st blk : List (BitVec 8)) : List (BitVec 64) :=
  List.zipWith (· ^^^ ·) (keccakDwords st 0)
    (((List.range 17).map fun i =>
        BitVec.ofNat 64 (bytesLEtoNat ((blk.drop (8 * i)).take 8))) ++
      List.replicate 8 (0 : BitVec 64))

private theorem absorbLaneVec_length (st blk : List (BitVec 8)) :
    (absorbLaneVec st blk).length = 25 := by
  simp only [absorbLaneVec, List.length_zipWith, keccakDwords, List.length_map,
    List.length_range, List.length_append, List.length_replicate]
  decide

private theorem absorbLaneVec_eq_absorbBlock (st blk : List (BitVec 8)) :
    absorbLaneVec st blk = keccakAbsorbBlock (keccakDwords st 0) blk := by
  unfold absorbLaneVec keccakAbsorbBlock
  rfl

private theorem absorb_blk_lane (blk : List (BitVec 8)) (i : Nat)
    (_hi : i < 17) (hblk : 8 * (i + 1) ≤ blk.length) :
    BitVec.ofNat 64 (bytesLEtoNat ((blk.drop (8 * i)).take 8)) =
      packBytes ((blk.drop (8 * i)).take 8) :=
  (packBytes_eq_ofNat_bytesLE _ (by simp [List.length_take, List.length_drop]; omega)).symm

private theorem absorbLaneVec_get_lt (st blk : List (BitVec 8)) (i : Nat)
    (hi : i < 17) (hst : st.length = 200) (hblk : 8 * (i + 1) ≤ blk.length) :
    (absorbLaneVec st blk)[i]'(by rw [absorbLaneVec_length]; omega) =
      packBytes ((st.drop (8 * i)).take 8) ^^^
        packBytes ((blk.drop (8 * i)).take 8) := by
  simp only [absorbLaneVec]
  have hz : i <
      (List.zipWith (· ^^^ ·) (keccakDwords st 0)
        (((List.range 17).map fun i =>
            BitVec.ofNat 64 (bytesLEtoNat ((blk.drop (8 * i)).take 8))) ++
          List.replicate 8 (0 : BitVec 64))).length := by
    simp [List.length_zipWith, keccakDwords, List.length_map, List.length_range,
      List.length_append, List.length_replicate]; omega
  rw [List.getElem_zipWith (h := hz)]
  apply congrArg₂ (· ^^^ ·)
  · simp [keccakDwords, wsDword, Nat.zero_add]
  · rw [List.getElem_append_left (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range]
    exact absorb_blk_lane blk i hi hblk

private theorem absorbLaneVec_get_ge (st blk : List (BitVec 8)) (i : Nat)
    (hi : 17 ≤ i) (hi25 : i < 25) (_hst : st.length = 200) :
    (absorbLaneVec st blk)[i]'(by rw [absorbLaneVec_length]; exact hi25) =
      packBytes ((st.drop (8 * i)).take 8) := by
  simp only [absorbLaneVec]
  have hz : i <
      (List.zipWith (· ^^^ ·) (keccakDwords st 0)
        (((List.range 17).map fun i =>
            BitVec.ofNat 64 (bytesLEtoNat ((blk.drop (8 * i)).take 8))) ++
          List.replicate 8 (0 : BitVec 64))).length := by
    simp [List.length_zipWith, keccakDwords, List.length_map, List.length_range,
      List.length_append]; omega
  rw [List.getElem_zipWith (h := hz)]
  -- Unfold keccakDwords on the left operand of ^^^ (same i-proof as goal).
  simp only [keccakDwords, wsDword, List.getElem_map, List.getElem_range]
  -- Right operand of ^^^ is the zero pad.
  have hlenR :
      i <
        (((List.range 17).map fun i =>
            BitVec.ofNat 64 (bytesLEtoNat ((blk.drop (8 * i)).take 8))) ++
          List.replicate 8 (0 : BitVec 64)).length := by
    simp [List.length_append, List.length_map, List.length_range]; omega
  have hb :
      (((List.range 17).map fun i =>
          BitVec.ofNat 64 (bytesLEtoNat ((blk.drop (8 * i)).take 8))) ++
        List.replicate 8 (0 : BitVec 64))[i]'(hlenR) = (0 : BitVec 64) := by
    have hmap : (((List.range 17).map fun i =>
          BitVec.ofNat 64 (bytesLEtoNat ((blk.drop (8 * i)).take 8)))).length = 17 := by
      simp [List.length_map, List.length_range]
    rw [List.getElem_append_right (by omega)]
    -- Goal: (replicate 8 0)[i - 17] = 0
    have hi8 : i - 17 < 8 := by omega
    simpa [hmap] using
      (List.getElem_replicate (n := 8) (a := (0 : BitVec 64)) (i := i - 17) hi8)
  -- Rewrite right of ^^^ then simplify x ^^^ 0.
  conv => lhs; rhs; rw [hb]
  simp

/-- `xorDwordsUpTo 17` equals SpecRef absorb-block byte image. -/
theorem xorDwordsUpTo_eq_absorbBlock_bytes (st blk : List (BitVec 8))
    (hst : st.length = 200) (hblk : blk.length = 136) :
    xorDwordsUpTo st blk 17 =
      keccakStateBytes (keccakAbsorbBlock (keccakDwords st 0) blk) := by
  rw [← absorbLaneVec_eq_absorbBlock]
  have hL : (xorDwordsUpTo st blk 17).length = 200 := by
    rw [xorDwordsUpTo_length, hst]
  have hR : (keccakStateBytes (absorbLaneVec st blk)).length = 200 := by
    unfold keccakStateBytes
    rw [length_flatMap_dwordBytes_lanes, absorbLaneVec_length]
  apply eq_of_lane_windows hL hR
  intro i hi
  have hRwin :
      ((keccakStateBytes (absorbLaneVec st blk)).drop (8 * i)).take 8 =
        dwordBytes ((absorbLaneVec st blk)[i]'(by rw [absorbLaneVec_length]; exact hi)) :=
    flatMap_dwordBytes_drop_take (absorbLaneVec st blk) i
      (by rw [absorbLaneVec_length]; exact hi)
  -- Avoid `by rw [hblk]; omega` — rw alone can close 136≤136 and leave omega with no goals.
  have hblk17 : 8 * 17 ≤ blk.length := by omega
  by_cases hlt : i < 17
  · -- Rate
    have hblk_i : 8 * (i + 1) ≤ blk.length := by omega
    calc
      ((xorDwordsUpTo st blk 17).drop (8 * i)).take 8
          = dwordBytes
              (packBytes ((st.drop (8 * i)).take 8) ^^^
                packBytes ((blk.drop (8 * i)).take 8)) :=
            xorDwordsUpTo_lane_lt st blk 17 i hst hblk17 hlt (by omega)
      _ = dwordBytes
              ((absorbLaneVec st blk)[i]'(by rw [absorbLaneVec_length]; exact hi)) := by
            refine congrArg dwordBytes ?_
            exact (absorbLaneVec_get_lt st blk i hlt hst hblk_i).symm
      _ = ((keccakStateBytes (absorbLaneVec st blk)).drop (8 * i)).take 8 := hRwin.symm
  · -- Capacity
    calc
      ((xorDwordsUpTo st blk 17).drop (8 * i)).take 8
          = ((st.drop (8 * i)).take 8) :=
            xorDwordsUpTo_lane_ge st blk 17 i hst (Nat.le_of_not_lt hlt) (by omega)
      _ = dwordBytes (packBytes ((st.drop (8 * i)).take 8)) :=
            (dwordBytes_packBytes _
              (by simp [List.length_take, List.length_drop, hst]; omega)).symm
      _ = dwordBytes
              ((absorbLaneVec st blk)[i]'(by rw [absorbLaneVec_length]; exact hi)) := by
            refine congrArg dwordBytes ?_
            exact (absorbLaneVec_get_ge st blk i (Nat.le_of_not_lt hlt) hi hst).symm
      _ = ((keccakStateBytes (absorbLaneVec st blk)).drop (8 * i)).take 8 := hRwin.symm

/-- Guest one-block permute = SpecRef absorbBlock then keccakF as bytes. -/
theorem keccakPermuteAbsorbed_eq (st0 blk : List (BitVec 8))
    (hst : st0.length = 200) (hblk : blk.length = 136) :
    keccakPermuteAbsorbed st0 blk =
      keccakStateBytes
        (Accel.keccakF (keccakAbsorbBlock (keccakDwords st0 0) blk)) := by
  unfold keccakPermuteAbsorbed keccakXorAbsorbed
  rw [xorDwordsUpTo_eq_absorbBlock_bytes st0 blk hst hblk]
  have hab_len : (keccakAbsorbBlock (keccakDwords st0 0) blk).length = 25 := by
    unfold keccakAbsorbBlock
    simp [List.length_zipWith, keccakDwords, List.length_map, List.length_range,
      List.length_append, List.length_replicate]
  have hstB : (keccakStateBytes (keccakAbsorbBlock (keccakDwords st0 0) blk)).length = 200 := by
    unfold keccakStateBytes
    rw [length_flatMap_dwordBytes_lanes, hab_len]
  rw [setBytes_keccakBytes_eq_stateBytes _ hstB,
    keccakDwords_of_stateBytes _ hab_len]

/-! ## Prefix fold = SpecRef absorb of N full blocks -/

private theorem length_drop_le_of_succ_le (n len fuel : Nat) (hn : 0 < n)
    (h : len ≤ fuel + 1) : len - n ≤ fuel := by
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl _)
  | succ n =>
    -- len - (n+1) ≤ fuel from len ≤ fuel+1
    omega

/-- `chunkBytesAux` is independent of surplus fuel once `bs.length ≤ fuel`. -/
private theorem chunkBytesAux_fuel_irrel (n : Nat) (hn : 0 < n) :
    ∀ (fuel1 fuel2 : Nat) (bs : Bytes),
      bs.length ≤ fuel1 → bs.length ≤ fuel2 →
        chunkBytesAux fuel1 n bs = chunkBytesAux fuel2 n bs := by
  intro fuel1
  induction fuel1 with
  | zero =>
    intro fuel2 bs h1 _h2
    have hnil : bs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h1)
    subst hnil
    cases fuel2 <;> rfl
  | succ f1 ih =>
    intro fuel2 bs h1 h2
    cases fuel2 with
    | zero =>
      have hnil : bs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h2)
      subst hnil; rfl
    | succ f2 =>
      match bs with
      | [] => rfl
      | b :: bs' =>
        simp only [chunkBytesAux]
        have hd1 : (List.drop n (b :: bs')).length ≤ f1 := by
          rw [List.length_drop]; exact length_drop_le_of_succ_le n _ f1 hn h1
        have hd2 : (List.drop n (b :: bs')).length ≤ f2 := by
          rw [List.length_drop]; exact length_drop_le_of_succ_le n _ f2 hn h2
        congr 1
        exact ih f2 _ hd1 hd2

/-- One-step unfold of `chunkBytes` when the input is long enough. -/
theorem chunkBytes_cons (n : Nat) (bs : Bytes)
    (hn : 0 < n) (hlen : n ≤ bs.length) :
    chunkBytes n bs = bs.take n :: chunkBytes n (bs.drop n) := by
  cases bs with
  | nil =>
    simp only [List.length_nil] at hlen
    exact absurd hlen (Nat.not_le_of_gt hn)
  | cons b bs' =>
    unfold chunkBytes
    -- aux (len+1) on nonempty unfolds by rfl
    have hunf :
        chunkBytesAux ((b :: bs').length + 1) n (b :: bs') =
          (b :: bs').take n :: chunkBytesAux (b :: bs').length n ((b :: bs').drop n) :=
      rfl
    rw [hunf]
    congr 1
    change chunkBytesAux (b :: bs').length n ((b :: bs').drop n) =
      chunkBytesAux (((b :: bs').drop n).length + 1) n ((b :: bs').drop n)
    refine chunkBytesAux_fuel_irrel n hn _ _ _ ?_ ?_
    · rw [List.length_drop]; exact Nat.sub_le _ _
    · rw [List.length_drop]; exact Nat.le_succ _

/-- `chunkBytes n ys = [ys]` when `ys.length = n > 0`. -/
private theorem chunkBytes_singleton (n : Nat) (ys : List (BitVec 8))
    (hn : 0 < n) (hys : ys.length = n) :
    chunkBytes n ys = [ys] := by
  have h := chunkBytes_cons n ys hn (by omega)
  rw [h, List.take_of_length_le (by omega), List.drop_eq_nil_of_le (by omega),
    chunkBytes_nil]

/-- Append one full rate block onto an exact multiple-of-rate prefix. -/
private theorem chunkBytes_append_block (k : Nat) (xs ys : List (BitVec 8))
    (hxs : xs.length = 136 * k) (hys : ys.length = 136) :
    chunkBytes 136 (xs ++ ys) = chunkBytes 136 xs ++ [ys] := by
  induction k generalizing xs with
  | zero =>
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    simp only [List.nil_append, chunkBytes_nil]
    exact chunkBytes_singleton 136 ys (by omega) hys
  | succ k ih =>
    have hge : 136 ≤ xs.length := by omega
    have hcons := chunkBytes_cons 136 (xs ++ ys) (by omega) (by
      simp only [List.length_append, hxs, hys]; omega)
    rw [hcons, List.take_append_of_le_length hge, List.drop_append_of_le_length hge]
    have hrest : (xs.drop 136).length = 136 * k := by
      rw [List.length_drop, hxs]; omega
    rw [ih (xs.drop 136) hrest, chunkBytes_cons 136 xs (by omega) hge, List.cons_append]

/-- SpecRef block list after `k+1` full rate blocks grows by one block. -/
private theorem keccakAbsorbBlocks_succ (input : List (BitVec 8)) (k : Nat)
    (hfit : 136 * (k + 1) ≤ input.length) :
    keccakAbsorbBlocks input (k + 1) =
      keccakAbsorbBlocks input k ++
        [(input.drop (136 * k)).take 136] := by
  unfold keccakAbsorbBlocks
  simp only [keccakRateBytes]
  have hsplit : input.take (136 * (k + 1)) =
      input.take (136 * k) ++ (input.drop (136 * k)).take 136 := by
    have hsum : 136 * k + 136 = 136 * (k + 1) := by omega
    rw [← hsum, List.take_add]
  rw [hsplit]
  refine chunkBytes_append_block k (input.take (136 * k))
    ((input.drop (136 * k)).take 136) ?_ ?_
  · rw [List.length_take]; omega
  · rw [List.length_take, List.length_drop]; omega

/-- Absorb of `bs ++ [blk]` is one more F∘absorbBlock step. -/
private theorem keccakAbsorb_snoc (st : List (BitVec 64)) (bs : List Bytes)
    (blk : Bytes) :
    keccakAbsorb st (bs ++ [blk]) =
      Accel.keccakF (keccakAbsorbBlock (keccakAbsorb st bs) blk) := by
  induction bs generalizing st with
  | nil => simp [keccakAbsorb]
  | cons b rest ih => simp [keccakAbsorb, ih]

/-- Guest N-block prefix equals SpecRef absorbed-state bytes. -/
theorem keccakAbsorbedPrefix_eq_state (input : List (BitVec 8)) (N : Nat)
    (hfit : keccakAbsorbStep * N ≤ input.length) :
    keccakAbsorbedPrefix input N = keccakAbsorbedState input N := by
  induction N with
  | zero =>
    simp only [keccakAbsorbedPrefix]
    exact (keccakAbsorbedState_zero input).symm
  | succ k ih =>
    have hfitk : keccakAbsorbStep * k ≤ input.length := by
      simp only [keccakAbsorbStep] at hfit ⊢; omega
    have hfit' : 136 * (k + 1) ≤ input.length := by
      simp only [keccakAbsorbStep] at hfit; omega
    have hblk_len :
        ((input.drop (keccakAbsorbStep * k)).take keccakAbsorbStep).length = 136 := by
      simp only [keccakAbsorbStep, List.length_take, List.length_drop]; omega
    simp only [keccakAbsorbedPrefix]
    set st := keccakAbsorbedPrefix input k
    set blk := (input.drop (keccakAbsorbStep * k)).take keccakAbsorbStep
    have hst : st.length = 200 := keccakAbsorbedPrefix_length input k
    rw [keccakPermuteAbsorbed_eq st blk hst hblk_len, ih hfitk]
    unfold keccakAbsorbedState
    have hblocks : keccakAbsorbBlocks input (k + 1) =
        keccakAbsorbBlocks input k ++ [blk] := by
      simpa [blk, keccakAbsorbStep] using keccakAbsorbBlocks_succ input k hfit'
    rw [hblocks, keccakAbsorb_snoc]
    have hstAbs :
        (keccakAbsorb (List.replicate 25 (0 : BitVec 64))
          (keccakAbsorbBlocks input k)).length = 25 :=
      keccakAbsorb_length _ _ (by simp)
    rw [keccakDwords_of_stateBytes _ hstAbs]

/-! ## Last rate block + pad split (pure) -/

private theorem length_mod_rate (N rem : Nat) (hrem : rem < 136) :
    (136 * N + rem) % 136 = rem := by
  -- (k*m + r) % m = r when r < m
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem]

/-- SpecRef final rate block under domain `len = 136*N + rem`.
    Same shape as `keccakPad` suffix after the N-block prefix. -/
def keccakLastRateBlock (input : List (BitVec 8)) (N rem : Nat) : List (BitVec 8) :=
  let tail := (input.drop (136 * N)).take rem
  let padLen := 136 - rem
  let pad : List (BitVec 8) :=
    if padLen = 1 then [(0x81 : BitVec 8)]
    else (0x01 : BitVec 8) ::
      List.replicate (padLen - 2) (0 : BitVec 8) ++
      [(0x80 : BitVec 8)]
  tail ++ pad

private theorem keccakPadSuffix_length (padLen : Nat) (hpos : 0 < padLen) :
    (if padLen = 1 then [(0x81 : BitVec 8)]
      else (0x01 : BitVec 8) ::
        List.replicate (padLen - 2) (0 : BitVec 8) ++
        [(0x80 : BitVec 8)]).length = padLen := by
  split_ifs with h
  · subst h; rfl
  · -- padLen ≥ 2: (0x01 :: zeros) ++ [0x80]
    have hge : 2 ≤ padLen := by
      cases padLen with
      | zero => exact absurd hpos (Nat.lt_irrefl _)
      | succ n =>
        cases n with
        | zero => exact absurd rfl h
        | succ _ => exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
    -- length = 1 + (padLen - 2) + 1 = padLen
    change
      (((0x01 : BitVec 8) :: List.replicate (padLen - 2) (0 : BitVec 8)) ++
        [(0x80 : BitVec 8)]).length = padLen
    rw [List.length_append, List.length_cons, List.length_replicate,
      List.length_cons, List.length_nil]
    omega

theorem keccakLastRateBlock_length (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 136 * N + rem)
    (hrem : rem < 136) :
    (keccakLastRateBlock input N rem).length = 136 := by
  unfold keccakLastRateBlock
  have htl : ((input.drop (136 * N)).take rem).length = rem := by
    rw [List.length_take, List.length_drop, hlen, min_eq_left (by omega)]
  have hpad := keccakPadSuffix_length (136 - rem) (by omega)
  rw [List.length_append, htl, hpad]; omega

/-- Full last rate block = drop of padded message after N full blocks. -/
theorem keccakLastRateBlock_eq_pad_drop (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 136 * N + rem)
    (hrem : rem < 136) :
    (keccakPad input).drop (136 * N) = keccakLastRateBlock input N rem := by
  unfold keccakLastRateBlock keccakPad
  have hle : 136 * N ≤ input.length := by omega
  rw [List.drop_append_of_le_length hle]
  have htake : (input.drop (136 * N)).take rem = input.drop (136 * N) := by
    apply List.take_of_length_le
    rw [List.length_drop, hlen]; omega
  rw [htake]
  have hmod : input.length % 136 = rem := by
    rw [hlen]; exact length_mod_rate N rem hrem
  -- Both sides: drop ++ pad, with padLen = 136 - (len % 136) = 136 - rem
  simp only [keccakRateBytes, hmod]

/-- Chunks of the padded message = N full blocks ++ last rate block. -/
theorem keccakPad_chunks_split (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 136 * N + rem)
    (hrem : rem < 136) :
    chunkBytes keccakRateBytes (keccakPad input) =
      keccakAbsorbBlocks input N ++ [keccakLastRateBlock input N rem] := by
  have htake :
      (keccakPad input).take (136 * N) = input.take (136 * N) := by
    unfold keccakPad
    exact List.take_append_of_le_length (by omega)
  have hdrop := keccakLastRateBlock_eq_pad_drop input N rem hlen hrem
  have hsplit : keccakPad input =
      (keccakPad input).take (136 * N) ++
        (keccakPad input).drop (136 * N) :=
    (List.take_append_drop (136 * N) (keccakPad input)).symm
  conv_lhs => rw [hsplit, htake, hdrop]
  unfold keccakAbsorbBlocks
  simp only [keccakRateBytes]
  refine chunkBytes_append_block N (input.take (136 * N))
    (keccakLastRateBlock input N rem) ?_ ?_
  · rw [List.length_take]; omega
  · exact keccakLastRateBlock_length input N rem hlen hrem

/-! ## Guest rem+pad = dword-XOR of last rate block -/

private theorem nat_xor_mod_256 (x y : Nat) :
    (x ^^^ y) % 256 = (x % 256) ^^^ (y % 256) := by
  have hx : x % 256 = (BitVec.ofNat 8 x).toNat := by
    simp only [BitVec.toNat_ofNat, Nat.reducePow]
  have hy : y % 256 = (BitVec.ofNat 8 y).toNat := by
    simp only [BitVec.toNat_ofNat, Nat.reducePow]
  have hxy : (x ^^^ y) % 256 = (BitVec.ofNat 8 (x ^^^ y)).toNat := by
    simp only [BitVec.toNat_ofNat, Nat.reducePow]
  rw [hx, hy, hxy, BitVec.ofNat_xor, BitVec.toNat_xor]

private theorem extractByte_xor (a b : Word) (j : Nat) (_hj : j < 8) :
    extractByte (a ^^^ b) j = extractByte a j ^^^ extractByte b j := by
  apply BitVec.eq_of_toNat_eq
  simp only [extractByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_xor]
  rw [Nat.shiftRight_xor_distrib]
  exact nat_xor_mod_256 _ _

private theorem dwordBytes_xor (a b : Word) :
    dwordBytes (a ^^^ b) =
      List.zipWith (· ^^^ ·) (dwordBytes a) (dwordBytes b) := by
  -- Expand both sides to concrete 8-lists via range8_eq
  simp only [dwordBytes, range8_eq, List.map_cons, List.map_nil, List.zipWith]
  simp only [
    extractByte_xor a b 0 (by omega), extractByte_xor a b 1 (by omega),
    extractByte_xor a b 2 (by omega), extractByte_xor a b 3 (by omega),
    extractByte_xor a b 4 (by omega), extractByte_xor a b 5 (by omega),
    extractByte_xor a b 6 (by omega), extractByte_xor a b 7 (by omega)]

private theorem getByteAt_eq_getD (bs : List (BitVec 8)) (i : Nat) :
    getByteAt bs i = bs.getD i 0 := by
  simp only [getByteAt, List.getD_eq_getElem?_getD]
  by_cases h : i < bs.length
  · rw [dif_pos h, List.getElem?_eq_getElem h, Option.getD_some]
  · rw [dif_neg h, List.getElem?_eq_none (Nat.ge_of_not_lt h), Option.getD_none]

private theorem getByteAt_of_lt (bs : List (BitVec 8)) (i : Nat)
    (h : i < bs.length) : getByteAt bs i = bs[i] := by
  simp only [getByteAt, dif_pos h]

private theorem getByteAt_zipWith_xor (as bs : List (BitVec 8)) (i : Nat)
    (ha : as.length = 8) (hb : bs.length = 8) (hi : i < 8) :
    getByteAt (List.zipWith (· ^^^ ·) as bs) i =
      getByteAt as i ^^^ getByteAt bs i := by
  have hlen : (List.zipWith (· ^^^ ·) as bs).length = 8 := by
    simp [List.length_zipWith, ha, hb]
  rw [getByteAt_of_lt _ _ (by omega), getByteAt_of_lt _ _ (by omega),
    getByteAt_of_lt _ _ (by omega), List.getElem_zipWith]

/-- Rate-window byte of `xorDwordsUpTo … 17`. -/
private theorem xorDwordsUpTo17_get_lt (st blk : List (BitVec 8)) (i : Nat)
    (hst : st.length = 200) (hblk : blk.length = 136) (hi : i < 136) :
    getByteAt (xorDwordsUpTo st blk 17) i =
      getByteAt st i ^^^ getByteAt blk i := by
  let lane := i / 8
  let off := i % 8
  have hl : lane < 17 := by dsimp [lane]; omega
  have ho : off < 8 := by dsimp [off]; exact Nat.mod_lt i (by decide)
  have hi_eq : i = 8 * lane + off := by dsimp [lane, off]; exact (Nat.div_add_mod i 8).symm
  have hwin := xorDwordsUpTo_lane_lt st blk 17 lane hst (by omega) hl (by omega)
  have hL : getByteAt (xorDwordsUpTo st blk 17) i =
      getByteAt (((xorDwordsUpTo st blk 17).drop (8 * lane)).take 8) off := by
    rw [hi_eq]; exact getByteAt_lane_window _ lane off
      (by rw [xorDwordsUpTo_length, hst]) (by omega) ho
  have hRs : getByteAt st i =
      getByteAt ((st.drop (8 * lane)).take 8) off := by
    rw [hi_eq]; exact getByteAt_lane_window st lane off hst (by omega) ho
  have hRb : getByteAt blk i =
      getByteAt ((blk.drop (8 * lane)).take 8) off := by
    -- specialized window for length-136 blk (getByteAt_lane_window wants len=200)
    rw [hi_eq]
    unfold getByteAt
    have hxj : 8 * lane + off < blk.length := by omega
    have hwin' : off < ((blk.drop (8 * lane)).take 8).length := by
      simp [List.length_take, List.length_drop, hblk]; omega
    rw [dif_pos hxj, dif_pos hwin', List.getElem_take, List.getElem_drop]
  rw [hL, hwin, dwordBytes_xor]
  have has : ((st.drop (8 * lane)).take 8).length = 8 := by
    simp [List.length_take, List.length_drop, hst]; omega
  have hbs : ((blk.drop (8 * lane)).take 8).length = 8 := by
    simp [List.length_take, List.length_drop, hblk]; omega
  rw [getByteAt_zipWith_xor _ _ off
    (by simp [length_dwordBytes]) (by simp [length_dwordBytes]) ho,
    dwordBytes_packBytes _ has, dwordBytes_packBytes _ hbs, hRs, hRb]

private theorem xorDwordsUpTo17_get_ge (st blk : List (BitVec 8)) (i : Nat)
    (hst : st.length = 200) (hi : 136 ≤ i) (hi' : i < 200) :
    getByteAt (xorDwordsUpTo st blk 17) i = getByteAt st i := by
  let lane := i / 8
  let off := i % 8
  have hl : 17 ≤ lane := by dsimp [lane]; omega
  have ho : off < 8 := by dsimp [off]; exact Nat.mod_lt i (by decide)
  have hi_eq : i = 8 * lane + off := by dsimp [lane, off]; exact (Nat.div_add_mod i 8).symm
  have hwin := xorDwordsUpTo_lane_ge st blk 17 lane hst hl (by omega)
  have hL : getByteAt (xorDwordsUpTo st blk 17) i =
      getByteAt (((xorDwordsUpTo st blk 17).drop (8 * lane)).take 8) off := by
    rw [hi_eq]; exact getByteAt_lane_window _ lane off
      (by rw [xorDwordsUpTo_length, hst]) (by omega) ho
  have hR : getByteAt st i =
      getByteAt ((st.drop (8 * lane)).take 8) off := by
    rw [hi_eq]; exact getByteAt_lane_window st lane off hst (by omega) ho
  rw [hL, hwin, hR]

/-- Length-200 lists equal when getByteAt agrees on 0..199. -/
private theorem eq_of_getByteAt_200 (as bs : List (BitVec 8))
    (ha : as.length = 200) (hb : bs.length = 200)
    (h : ∀ i, i < 200 → getByteAt as i = getByteAt bs i) : as = bs := by
  apply List.ext_getElem
  · omega
  · intro i hi _
    have hi' : i < 200 := by omega
    have := h i hi'
    simp only [getByteAt, dif_pos (by omega : i < as.length),
      dif_pos (by omega : i < bs.length)] at this
    exact this

/-- `xorBytesUpTo` byte view. -/
private theorem xorBytesUpTo_get (st inp : List (BitVec 8)) (q i : Nat)
    (hst : q ≤ st.length) (hinp : q ≤ inp.length) :
    getByteAt (xorBytesUpTo st inp q) i =
      if i < q then getByteAt st i ^^^ getByteAt inp i
      else getByteAt st i := by
  induction q generalizing i with
  | zero => simp only [xorBytesUpTo, Nat.not_lt_zero, ↓reduceIte]
  | succ n ih =>
    simp only [xorBytesUpTo]
    set st' := xorBytesUpTo st inp n with hst'
    have hlen' : st'.length = st.length := by
      simpa [st'] using xorBytesUpTo_length st inp n
    have hfit : n + [(inp.getD n 0) ^^^ (st'.getD n 0)].length ≤ st'.length := by
      simp only [List.length_singleton]; omega
    rw [getByteAt_setBytes _ st' n i hfit]
    simp only [List.length_singleton] at hfit ⊢
    by_cases heq : i = n
    · -- at write index n
      cases heq
      have hwin : n ≤ n ∧ n < n + 1 := ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
      rw [if_pos hwin, show n - n = 0 from Nat.sub_self _]
      have hb : getByteAt [(inp.getD n 0) ^^^ (st'.getD n 0)] 0 =
          (inp.getD n 0) ^^^ (st'.getD n 0) := by
        simp only [getByteAt, List.length_singleton,
          dif_pos (by decide : (0:Nat) < 1), List.getElem_cons_zero]
      rw [hb]
      have hih := ih n (by omega) (by omega)
      have hnlt : ¬ n < n := Nat.lt_irrefl _
      rw [if_neg hnlt] at hih
      rw [if_pos (Nat.lt_succ_self n), ← getByteAt_eq_getD inp n,
        ← getByteAt_eq_getD st' n, hih]
      ac_rfl
    · by_cases hi : i < n
      · have hnot : ¬ (n ≤ i ∧ i < n + 1) := by omega
        rw [if_neg hnot, if_pos (Nat.lt_succ_of_lt hi)]
        have hih := ih i (by omega) (by omega)
        rwa [if_pos hi] at hih
      · have hnot : ¬ (n ≤ i ∧ i < n + 1) := by omega
        have hnlt : ¬ i < n + 1 := by omega
        rw [if_neg hnot, if_neg hnlt]
        have hih := ih i (by omega) (by omega)
        rwa [if_neg (by omega : ¬ i < n)] at hih

/-- Guest pad byte view. -/
private theorem keccakGuestPad_get (st : List (BitVec 8)) (rem i : Nat)
    (hst : 136 ≤ st.length) (hrem : rem < 136) :
    getByteAt (keccakGuestPad st rem) i =
      getByteAt st i ^^^
        (if i = rem then (1 : BitVec 8) else (0 : BitVec 8)) ^^^
        (if i = 135 then (0x80 : BitVec 8) else (0 : BitVec 8)) := by
  unfold keccakGuestPad
  set b1 : BitVec 8 := (st.getD rem 0) ^^^ (1 : BitVec 8)
  set st1 := setBytes st rem [b1] with hst1
  have hfit1 : rem + [b1].length ≤ st.length := by
    simp only [List.length_singleton]; omega
  have hlen1 : st1.length = st.length := by
    simp only [st1, length_setBytes, List.length_singleton]
  have hget1 (j : Nat) :
      getByteAt st1 j = if j = rem then b1 else getByteAt st j := by
    dsimp only [st1]
    rw [getByteAt_setBytes _ st rem j hfit1]
    simp only [List.length_singleton]
    by_cases hj : j = rem
    · cases hj
      have hwin : rem ≤ rem ∧ rem < rem + 1 := ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
      rw [if_pos hwin, show rem - rem = 0 from Nat.sub_self _]
      simp only [getByteAt, List.length_singleton,
        dif_pos (by decide : (0:Nat) < 1), List.getElem_cons_zero, if_true]
    · have hnot : ¬ (rem ≤ j ∧ j < rem + 1) := by omega
      rw [if_neg hnot, if_neg hj]
  have hfit2 : 135 + (1:Nat) ≤ st1.length := by omega
  change getByteAt (setBytes st1 135 [(st1.getD 135 0) ^^^ (0x80 : BitVec 8)]) i = _
  rw [getByteAt_setBytes _ st1 135 i (by simp [List.length_singleton]; omega)]
  simp only [List.length_singleton]
  by_cases h135 : i = 135
  · cases h135
    have hwin : 135 ≤ 135 ∧ 135 < 135 + 1 := ⟨Nat.le_refl _, by omega⟩
    rw [if_pos hwin, show 135 - 135 = 0 from rfl]
    have hb : getByteAt [(st1.getD 135 0) ^^^ (0x80 : BitVec 8)] 0 =
        (st1.getD 135 0) ^^^ (0x80 : BitVec 8) := by
      simp only [getByteAt, List.length_singleton,
        dif_pos (by decide : (0:Nat) < 1), List.getElem_cons_zero]
    rw [hb, ← getByteAt_eq_getD st1 135, hget1 135]
    by_cases hr : rem = 135
    · cases hr
      simp only [if_true, b1, getByteAt_eq_getD]
    · simp only [if_neg (Ne.symm hr), if_neg hr, if_true]
      ac_rfl
  · have hnot : ¬ (135 ≤ i ∧ i < 135 + 1) := by omega
    rw [if_neg hnot, if_neg h135, hget1 i]
    by_cases hr : i = rem
    · cases hr
      simp only [if_true, b1, getByteAt_eq_getD]
      ac_rfl
    · simp only [if_neg hr]
      ac_rfl

/-- Concrete pad-suffix list (matches keccakPad branch). -/
private def keccakPadSuffix (padLen : Nat) : List (BitVec 8) :=
  if padLen = 1 then [(0x81 : BitVec 8)]
  else (0x01 : BitVec 8) ::
    List.replicate (padLen - 2) (0 : BitVec 8) ++ [(0x80 : BitVec 8)]

private theorem keccakPadSuffix_eq_def (padLen : Nat) :
    keccakPadSuffix padLen =
      (if padLen = 1 then [(0x81 : BitVec 8)]
        else (0x01 : BitVec 8) ::
          List.replicate (padLen - 2) (0 : BitVec 8) ++
          [(0x80 : BitVec 8)]) := rfl

private theorem keccakPadSuffix_length' (padLen : Nat) (hpos : 0 < padLen) :
    (keccakPadSuffix padLen).length = padLen := by
  simpa [keccakPadSuffix] using keccakPadSuffix_length padLen hpos

private theorem keccakPadSuffix_get (padLen j : Nat)
    (hpos : 0 < padLen) (hj : j < padLen) :
    getByteAt (keccakPadSuffix padLen) j =
      if padLen = 1 then (0x81 : BitVec 8)
      else if j = 0 then (1 : BitVec 8)
      else if j + 1 = padLen then (0x80 : BitVec 8)
      else (0 : BitVec 8) := by
  by_cases h1 : padLen = 1
  · cases h1
    have hj0 : j = 0 := by omega
    cases hj0
    simp only [keccakPadSuffix, if_true, getByteAt, List.length_singleton,
      dif_pos (by decide : (0:Nat) < 1), List.getElem_cons_zero]
  · have hge : 2 ≤ padLen := by omega
    simp only [if_neg h1]
    set mid := List.replicate (padLen - 2) (0 : BitVec 8)
    have hsu : keccakPadSuffix padLen =
        ((0x01 : BitVec 8) :: mid) ++ [(0x80 : BitVec 8)] := by
      simp only [keccakPadSuffix, if_neg h1, mid]
    have hlen_left : ((0x01 : BitVec 8) :: mid).length = padLen - 1 := by
      simp only [List.length_cons, mid, List.length_replicate]; omega
    have hj' : j < (((0x01 : BitVec 8) :: mid) ++ [(0x80 : BitVec 8)]).length := by
      simp only [List.length_append, List.length_singleton, hlen_left]; omega
    -- Rewrite getByteAt through hsu
    have hget : getByteAt (keccakPadSuffix padLen) j =
        getByteAt (((0x01 : BitVec 8) :: mid) ++ [(0x80 : BitVec 8)]) j := by
      simp only [hsu]
    rw [hget, getByteAt_of_lt _ _ hj']
    by_cases hj0 : j = 0
    · cases hj0
      have hlt : (0:Nat) < ((0x01 : BitVec 8) :: mid).length := by
        simp only [List.length_cons]; omega
      rw [List.getElem_append_left hlt, List.getElem_cons_zero]
      simp only [↓reduceIte]
    · by_cases hlast : j + 1 = padLen
      · have hj_eq : j = ((0x01 : BitVec 8) :: mid).length := by omega
        rw [List.getElem_concat_length (l := (0x01 : BitVec 8) :: mid)
          (a := (0x80 : BitVec 8)) (i := j) hj_eq hj']
        simp only [if_neg hj0, if_pos hlast]
      · have hlt : j < ((0x01 : BitVec 8) :: mid).length := by omega
        rw [List.getElem_append_left hlt]
        cases j with
        | zero => exact absurd rfl hj0
        | succ j' =>
          simp only [List.getElem_cons_succ, mid, List.getElem_replicate,
            if_neg hj0, if_neg hlast]

/-- Last rate-block byte view. -/
private theorem keccakLastRateBlock_get (input : List (BitVec 8)) (N rem i : Nat)
    (hlen : input.length = 136 * N + rem) (hrem : rem < 136) (hi : i < 136) :
    getByteAt (keccakLastRateBlock input N rem) i =
      (if i < rem then getByteAt input (136 * N + i) else (0 : BitVec 8)) ^^^
        (if i = rem then (1 : BitVec 8) else (0 : BitVec 8)) ^^^
        (if i = 135 then (0x80 : BitVec 8) else (0 : BitVec 8)) := by
  unfold keccakLastRateBlock
  set tail := (input.drop (136 * N)).take rem
  set padLen := 136 - rem
  have htail_len : tail.length = rem := by
    simp only [tail, List.length_take, List.length_drop, hlen, Nat.add_sub_cancel_left,
      min_eq_left (Nat.le_refl rem)]
  have hpad_len : (keccakPadSuffix padLen).length = padLen :=
    keccakPadSuffix_length' padLen (by omega)
  -- Replace inline pad if with keccakPadSuffix
  change getByteAt (tail ++ keccakPadSuffix padLen) i = _
  have hi' : i < (tail ++ keccakPadSuffix padLen).length := by
    simp only [List.length_append, htail_len, hpad_len, padLen]; omega
  rw [getByteAt_of_lt _ _ hi']
  by_cases hi_rem : i < rem
  · have hlt : i < tail.length := by omega
    rw [List.getElem_append_left hlt, if_pos hi_rem]
    have : tail[i] = input[136 * N + i] := by
      simp only [tail]
      have hdrop : i < (input.drop (136 * N)).length := by
        simp [List.length_drop, hlen]; omega
      rw [List.getElem_take, List.getElem_drop]
    rw [this]
    have hin : 136 * N + i < input.length := by omega
    rw [← getByteAt_of_lt input _ hin]
    have hn1 : i ≠ rem := by omega
    have hn2 : i ≠ 135 := by omega
    simp only [if_neg hn1, if_neg hn2]
    ac_rfl
  · have hge : tail.length ≤ i := by omega
    rw [List.getElem_append_right hge, if_neg hi_rem]
    have hj : i - rem < (keccakPadSuffix padLen).length := by
      simp only [hpad_len, padLen, htail_len] at *; omega
    have hidx : i - tail.length = i - rem := by omega
    simp only [htail_len] at *
    rw [← getByteAt_of_lt (keccakPadSuffix padLen) (i - rem) hj]
    have hpg := keccakPadSuffix_get padLen (i - rem) (by omega) (by omega)
    rw [hpg]
    by_cases h135r : rem = 135
    · cases h135r
      have : i = 135 := by omega
      cases this
      simp only [if_true, Nat.sub_self]
      decide
    · have hne1 : ¬ (padLen = 1) := by dsimp [padLen]; omega
      simp only [if_neg hne1]
      by_cases hj0 : i - rem = 0
      · have : i = rem := by omega
        cases this
        simp only [if_true, Nat.sub_self, hj0, if_neg h135r]
        decide
      · by_cases hlast : (i - rem) + 1 = padLen
        · have : i = 135 := by dsimp [padLen] at hlast; omega
          cases this
          simp only [if_neg hj0, if_pos hlast]
          have hnrem : ¬ (135 = rem) := by omega
          simp only [if_neg hnrem]
          ac_rfl
        · simp only [if_neg hj0, if_neg hlast]
          have hnrem : i ≠ rem := by omega
          have hn135 : i ≠ 135 := by
            intro heq; cases heq; exact hlast (by dsimp [padLen]; omega)
          simp only [if_neg hnrem, if_neg hn135]
          ac_rfl

/-- Guest rem-XOR + pad equals dword-XOR of last rate block into prefix state. -/
private theorem keccakGuestFinal_eq_xorDwords
    (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = 136 * N + rem) (hrem : rem < 136) :
    let pref := keccakAbsorbedPrefix input N
    let tail := (input.drop (136 * N)).take rem
    keccakGuestPad (keccakRemAbsorbed pref tail rem) rem =
      xorDwordsUpTo pref (keccakLastRateBlock input N rem) 17 := by
  intro pref tail
  have hpref_len : pref.length = 200 := keccakAbsorbedPrefix_length input N
  have htail_len : tail.length = rem := by
    simp only [tail, List.length_take, List.length_drop, hlen, Nat.add_sub_cancel_left,
      min_eq_left (Nat.le_refl rem)]
  have hblk_len : (keccakLastRateBlock input N rem).length = 136 :=
    keccakLastRateBlock_length input N rem hlen hrem
  have hL : (keccakGuestPad (keccakRemAbsorbed pref tail rem) rem).length = 200 := by
    unfold keccakGuestPad keccakRemAbsorbed
    split_ifs <;> simp only [length_setBytes, xorBytesUpTo_length, hpref_len]
  have hR : (xorDwordsUpTo pref (keccakLastRateBlock input N rem) 17).length = 200 := by
    rw [xorDwordsUpTo_length, hpref_len]
  -- residual byte of tail at i (when i < rem)
  have htail_byte (i : Nat) (hi_rem : i < rem) :
      getByteAt tail i = getByteAt input (136 * N + i) := by
    have hti : i < tail.length := by
      rw [htail_len]; exact hi_rem
    have hin : 136 * N + i < input.length := by
      rw [hlen]; omega
    rw [getByteAt_of_lt tail i hti, getByteAt_of_lt input _ hin]
    dsimp only [tail]
    have hdrop : i < (input.drop (136 * N)).length := by
      simp only [List.length_drop, hlen, Nat.add_sub_cancel_left]; omega
    -- (take rem xs)[i] = xs[i] = input[136*N+i]
    simp only [List.getElem_take, List.getElem_drop]
  apply eq_of_getByteAt_200 _ _ hL hR
  intro i hi
  -- Expand RHS
  have hRget :
      getByteAt (xorDwordsUpTo pref (keccakLastRateBlock input N rem) 17) i =
        if i < 136 then
          getByteAt pref i ^^^ getByteAt (keccakLastRateBlock input N rem) i
        else getByteAt pref i := by
    by_cases hi136 : i < 136
    · rw [if_pos hi136,
        xorDwordsUpTo17_get_lt pref _ i hpref_len hblk_len hi136]
    · rw [if_neg hi136,
        xorDwordsUpTo17_get_ge pref _ i hpref_len (Nat.le_of_not_lt hi136) hi]
  -- Expand last-block byte when i < 136
  have hblk_get (hi136 : i < 136) :
      getByteAt (keccakLastRateBlock input N rem) i =
        (if i < rem then getByteAt input (136 * N + i) else (0 : BitVec 8)) ^^^
          (if i = rem then (1 : BitVec 8) else (0 : BitVec 8)) ^^^
          (if i = 135 then (0x80 : BitVec 8) else (0 : BitVec 8)) :=
    keccakLastRateBlock_get input N rem i hlen hrem hi136
  -- Expand LHS via RemAbsorbed cases
  by_cases hr : rem = 0
  · cases hr
    simp only [keccakRemAbsorbed, if_true] at hL ⊢
    rw [keccakGuestPad_get pref 0 i (by omega) (by decide), hRget]
    by_cases hi136 : i < 136
    · rw [if_pos hi136, hblk_get hi136]
      simp only [Nat.not_lt_zero, ↓reduceIte]
      set p0 : BitVec 8 := if i = 0 then (1 : BitVec 8) else 0
      set p135 : BitVec 8 := if i = 135 then (0x80 : BitVec 8) else 0
      -- pref ^^^ p0 ^^^ p135 = pref ^^^ (0 ^^^ p0 ^^^ p135)
      change getByteAt pref i ^^^ p0 ^^^ p135 =
        getByteAt pref i ^^^ (((0 : BitVec 8) ^^^ p0) ^^^ p135)
      simp [BitVec.zero_xor]
      ac_rfl
    · rw [if_neg hi136]
      have hn0 : i ≠ 0 := by omega
      have hn135 : i ≠ 135 := by omega
      simp only [if_neg hn0, if_neg hn135]
      simp [BitVec.xor_zero]
  · -- rem > 0
    have hrem_ne : rem ≠ 0 := hr
    rw [show keccakRemAbsorbed pref tail rem = xorBytesUpTo pref tail rem by
          simp only [keccakRemAbsorbed, if_neg hrem_ne]]
    have hxor_len : (xorBytesUpTo pref tail rem).length = 200 := by
      simp only [xorBytesUpTo_length, hpref_len]
    have hst_ge136 : 136 ≤ (xorBytesUpTo pref tail rem).length := by omega
    rw [keccakGuestPad_get (xorBytesUpTo pref tail rem) rem i hst_ge136 hrem]
    have hrem_le_pref : rem ≤ pref.length := by omega
    have hrem_le_t : rem ≤ tail.length := by omega
    rw [xorBytesUpTo_get pref tail rem i hrem_le_pref hrem_le_t]
    rw [hRget]
    by_cases hi136 : i < 136
    · rw [if_pos hi136, hblk_get hi136]
      by_cases hi_rem : i < rem
      · have hnrem : i ≠ rem := by omega
        have hn135 : i ≠ 135 := by omega
        simp only [if_pos hi_rem, if_neg hnrem, if_neg hn135, htail_byte i hi_rem]
        ac_rfl
      · simp only [if_neg hi_rem]
        by_cases heq : i = rem
        · -- i = rem: pad mark 0x01; if rem=135 also 0x80 → 0x81
          cases heq
          by_cases hr135 : rem = 135
          · cases hr135
            simp only [↓reduceIte]
            ac_rfl
          · simp only [↓reduceIte, if_neg hr135]
            ac_rfl
        · by_cases hi135 : i = 135
          · cases hi135
            simp only [if_neg heq, ↓reduceIte]
            ac_rfl
          · simp only [if_neg heq, if_neg hi135]
            ac_rfl
    · rw [if_neg hi136]
      have hnrem : i ≠ rem := by omega
      have hn135 : i ≠ 135 := by omega
      have hnlt : ¬ i < rem := by omega
      simp only [if_neg hnlt, if_neg hnrem, if_neg hn135]
      simp [BitVec.xor_zero]

private abbrev keccakSt0 : List (BitVec 64) := List.replicate 25 (0 : BitVec 64)

/-- Final sponge after guest rem+pad+F equals SpecRef absorb of padded message. -/
private theorem keccakBodyFinalState_eq
    (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = keccakAbsorbStep * N + rem)
    (hrem : rem < keccakAbsorbStep) :
    setBytes
        (keccakGuestPad (keccakBodyPrePad input N rem) rem)
        0
        (keccakBytes (keccakGuestPad (keccakBodyPrePad input N rem) rem) 0) =
      keccakStateBytes
        (keccakAbsorb keccakSt0 (chunkBytes keccakRateBytes (keccakPad input))) := by
  have hrem' : rem < 136 := by simp only [keccakAbsorbStep] at hrem; exact hrem
  have hlen' : input.length = 136 * N + rem := by
    simp only [keccakAbsorbStep] at hlen; exact hlen
  have hfitN : keccakAbsorbStep * N ≤ input.length := by
    simp only [keccakAbsorbStep] at hlen ⊢; omega
  set pref := keccakAbsorbedPrefix input N
  set tail := (input.drop (136 * N)).take rem
  set last := keccakLastRateBlock input N rem
  have hpre : keccakBodyPrePad input N rem = keccakRemAbsorbed pref tail rem := by
    simp only [keccakBodyPrePad, pref, tail, keccakAbsorbStep]
  have hfinal :
      keccakGuestPad (keccakBodyPrePad input N rem) rem =
        xorDwordsUpTo pref last 17 := by
    rw [hpre]
    exact keccakGuestFinal_eq_xorDwords input N rem hlen' hrem'
  -- guest rem+pad+F = permuteAbsorbed pref last
  have hperm :
      setBytes
          (keccakGuestPad (keccakBodyPrePad input N rem) rem)
          0
          (keccakBytes (keccakGuestPad (keccakBodyPrePad input N rem) rem) 0) =
        keccakPermuteAbsorbed pref last := by
    simp only [keccakPermuteAbsorbed, keccakXorAbsorbed, hfinal]
  rw [hperm]
  have hpref_len : pref.length = 200 := keccakAbsorbedPrefix_length input N
  have hblk_len : last.length = 136 :=
    keccakLastRateBlock_length input N rem hlen' hrem'
  rw [keccakPermuteAbsorbed_eq pref last hpref_len hblk_len]
  -- dwords pref = absorb of N full blocks
  have hpref_eq : pref = keccakAbsorbedState input N :=
    keccakAbsorbedPrefix_eq_state input N hfitN
  have habsN_len :
      (keccakAbsorb keccakSt0 (keccakAbsorbBlocks input N)).length = 25 :=
    keccakAbsorb_length _ _ (by simp [keccakSt0])
  have hdwords :
      keccakDwords pref 0 =
        keccakAbsorb keccakSt0 (keccakAbsorbBlocks input N) := by
    rw [hpref_eq]
    unfold keccakAbsorbedState
    exact keccakDwords_of_stateBytes _ habsN_len
  -- pad chunks = N blocks ++ [last]
  have hblocks :
      chunkBytes keccakRateBytes (keccakPad input) =
        keccakAbsorbBlocks input N ++ [last] :=
    keccakPad_chunks_split input N rem hlen' hrem'
  have hsnoc :=
    keccakAbsorb_snoc keccakSt0 (keccakAbsorbBlocks input N) last
  -- Goal: stateBytes (F (absorbBlock (dwords pref) last))
  --      = stateBytes (absorb (chunk (pad input)))
  rw [hdwords, hblocks, hsnoc]

/-- Top bridge under machine domain. -/
theorem keccakBodyDigest_eq_specref (input : List (BitVec 8)) (N rem : Nat)
    (hlen : input.length = keccakAbsorbStep * N + rem)
    (hrem : rem < keccakAbsorbStep) :
    keccakBodyDigest input N rem = keccak256 input := by
  unfold keccakBodyDigest
  set padded := keccakGuestPad (keccakBodyPrePad input N rem) rem
  set finalSt := setBytes padded 0 (keccakBytes padded 0)
  have hfinal_len : finalSt.length = 200 := by
    dsimp only [finalSt, padded]
    unfold keccakGuestPad
    simp only [length_setBytes]
    have hp : (keccakBodyPrePad input N rem).length = 200 := by
      simp only [keccakBodyPrePad, keccakRemAbsorbed]
      split_ifs <;> simp [xorBytesUpTo_length, keccakAbsorbedPrefix_length]
    simp only [hp]
  have hge32 : 32 ≤ finalSt.length := by omega
  change keccakDigestCopy finalSt = _
  rw [keccakDigestCopy_eq_take32 finalSt hge32]
  have hfs : finalSt =
      keccakStateBytes
        (keccakAbsorb keccakSt0 (chunkBytes keccakRateBytes (keccakPad input))) := by
    dsimp only [finalSt, padded]
    exact keccakBodyFinalState_eq input N rem hlen hrem
  rw [hfs]
  have habs_len25 :
      (keccakAbsorb keccakSt0
        (chunkBytes keccakRateBytes (keccakPad input))).length = 25 :=
    keccakAbsorb_length _ _ (by simp [keccakSt0])
  have habs_len200 :
      (keccakStateBytes
        (keccakAbsorb keccakSt0
          (chunkBytes keccakRateBytes (keccakPad input)))).length = 200 := by
    simp only [keccakStateBytes, length_flatMap_dwordBytes_lanes, habs_len25]
  -- take32 (stateBytes absorb) = squeeze32 (dwords (stateBytes absorb))
  --                            = squeeze32 absorb
  --                            = keccak256
  rw [← keccakSqueeze32_of_stateBytes _ habs_len200,
    keccakDwords_of_stateBytes _ habs_len25]
  exact (keccak256_eq_squeeze_absorb input).symm

/-- Consumer form: N/rem recovered from length. -/
theorem keccakBodyDigest_div_eq_specref (input : List (BitVec 8)) :
    keccakBodyDigest input (input.length / 136) (input.length % 136) =
      keccak256 input :=
  keccakBodyDigest_eq_specref input (input.length / 136) (input.length % 136)
    (by
      simp only [keccakAbsorbStep]
      exact (Nat.div_add_mod input.length 136).symm)
    (by
      simp only [keccakAbsorbStep]
      exact Nat.mod_lt _ (by decide))

end EvmAsm.Codegen.Proofs
