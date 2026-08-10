import EvmAsm.Codegen.Programs.U256MulU64Be.Common

/-!
# Outer multiply loop spec for `u256_mul_u64_be`

The outer loop (hdr at `mulBase + 80`, 32 iterations) folds one big-endian
byte of `a` per iteration into the 40-byte little-endian accumulator at
`u256m_acc`.  Per iteration: load byte `a[31-i]`, multiply by `b` (MUL/MULHU),
an 8-iteration ripple loop adds the low 64 bits into `acc[i..i+8)`, a final
step adds MULHU into `acc[i+8]`.  The carry-propagate loop at `+200` is
provably dead: the running carry is always 0 there.

Layout (byte offsets from `mulBase`):
- `+76`: `LI x20, 0` (init); hdr `+80`: `LI x5, 32`; guard `+84`:
  `BEQ x20, x5, +156` (taken -> `+240`).
- `+88..+100`: `LI x5,31; SUB x5,x5,x20; ADD x5,x8,x5; LBU x5,0(x5)`.
- `+104`: `BEQ x5, x0, +128` (zero-byte skip, taken -> `+232`).
- `+108..+124`: `MUL x6,x5,x9; MULHU x7,x5,x9; ADD x28,x19,x20; LI x29,8;
  LI x30,0`.
- ripple hdr `+128` (11-instr body, `BNE x29, x0, -40` back-edge at `+168`).
- mulhu-add `+172..+196` (7 instrs); carry guard `+200`:
  `BEQ x30, x0, +32` (always taken -> `+232`).
- continue `+232`: `ADDI x20,x20,1; JAL x0,-156` -> `+80`.
-/

namespace EvmAsm.Codegen.U256MulU64Be

open EvmAsm Rv64 Rv64.SAsm

/-! ## §1 Word helpers -/

theorem sub_31_ofNat (i : Nat) (_hi : i < 32) :
    (31 : Word) - BitVec.ofNat 64 i = BitVec.ofNat 64 (31 - i) := by
  bv_omega

theorem outerCtr_succ (i : Nat) (_hi : i < 32) :
    BitVec.ofNat 64 i + Rv64.signExtend12 (1 : BitVec 12)
      = BitVec.ofNat 64 (i + 1) := by
  rw [show Rv64.signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
  bv_omega

theorem outerCtr_ne (i : Nat) (hi : i < 32) :
    BitVec.ofNat 64 i ≠ BitVec.ofNat 64 32 := by
  intro h
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)] at h1
  simp at h1
  omega

theorem rippleCtr_dec (k : Nat) (hk : k < 8) :
    BitVec.ofNat 64 (8 - k) + Rv64.signExtend12 (-1 : BitVec 12)
      = BitVec.ofNat 64 (8 - (k + 1)) := by
  rw [show Rv64.signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
  bv_omega

theorem rippleCtr_ne (k : Nat) (hk : k < 7) :
    BitVec.ofNat 64 (8 - (k + 1)) ≠ 0 := by
  intro h
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 - (k + 1) < 2 ^ 64)] at h1
  simp at h1
  omega

theorem rippleCtr_eq_zero (k : Nat) (hk : k = 7) :
    BitVec.ofNat 64 (8 - (k + 1)) = 0 := by
  rw [hk]; decide

theorem accCursor1_succ (i k : Nat) (_h : i + k < 40) :
    accBase + BitVec.ofNat 64 (i + k) + Rv64.signExtend12 (1 : BitVec 12)
      = accBase + BitVec.ofNat 64 (i + k + 1) := by
  rw [show Rv64.signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    BitVec.add_assoc]
  congr 1
  bv_omega

theorem accBase_toNat : accBase.toNat = 0xa4386860 := by decide

theorem accBase_valid_byte (j : Nat) (hj : j < 40) :
    isValidByteAccess (accBase + BitVec.ofNat 64 j) = true := by
  have hj64 : j % 2 ^ 64 = j := Nat.mod_eq_of_lt (by omega)
  have hto : (accBase + BitVec.ofNat 64 j).toNat = 0xa4386860 + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hj64, accBase_toNat,
      Nat.mod_eq_of_lt (by omega : 0xa4386860 + j < 2 ^ 64)]
  show isValidMemAddr _ = true
  unfold isValidMemAddr
  rw [hto]
  have e1 : Rv64.MEM_START = 0x20 := rfl
  have e2 : Rv64.MEM_END = 0x78000000 := rfl
  have e3 : Rv64.INPUT_MEM_START = 0x40000000 := rfl
  have e4 : Rv64.INPUT_MEM_END = 0x40002000 := rfl
  have e5 : Rv64.RAM_MEM_START = 0xa0000000 := rfl
  have e6 : Rv64.RAM_MEM_END = 0xc0000000 := rfl
  rw [e1, e2, e3, e4, e5, e6,
    show decide (0xa0000000 ≤ 0xa4386860 + j) = true from by
      rw [decide_eq_true_eq]; omega,
    show decide (0xa4386860 + j ≤ 0xc0000000) = true from by
      rw [decide_eq_true_eq]; omega]
  simp

theorem accBase_no_overflow (j : Nat) (hj : j < 40) :
    accBase.toNat + j < 2 ^ 64 := by
  rw [accBase_toNat]; omega

/-! ## §2 Nat algebra -/

/-- One ripple byte-step, at the `leBytesToNat` level.  `Mk = M0 / 256^k`,
`Mk1 = M0 / 256^(k+1)`, `O = 256^i * 256^k`, `ak` the old byte, `v` the stored
byte, `ck/ck1` the carries. -/
theorem ripple_nat (le0 X Mk Mk1 ck ak v ck1 O : Nat)
    (hdiv : Mk = 256 * Mk1 + Mk % 256)
    (hv : v = (ak + Mk % 256 + ck) % 256)
    (hck1 : ck1 = (ak + Mk % 256 + ck) / 256)
    (h1 : Mk * O + ck * O ≤ le0 + X) :
    le0 + X - Mk * O - ck * O + O * v - O * ak
    = le0 + X - Mk1 * (256 * O) - ck1 * (256 * O) := by
  obtain ⟨m, hm⟩ : ∃ m, m = Mk % 256 := ⟨Mk % 256, rfl⟩
  rw [← hm] at hv hck1 hdiv
  have hs : ak + m + ck = v + 256 * ck1 := by
    rw [hv, hck1]; exact (Nat.mod_add_div _ 256).symm
  have hsO : ak * O + m * O + ck * O = v * O + 256 * ck1 * O := by
    have h := congrArg (· * O) hs
    simp only [Nat.add_mul] at h
    rw [h]
  have hA : Mk * O = 256 * Mk1 * O + m * O := by
    conv_lhs => rw [hdiv]
    ring
  rw [show Mk1 * (256 * O) = 256 * Mk1 * O from by ring,
    show ck1 * (256 * O) = 256 * ck1 * O from by ring, hA,
    show O * v = v * O from Nat.mul_comm _ _,
    show O * ak = ak * O from Nat.mul_comm _ _]
  clear hm hv hck1 hdiv hs
  omega

/-- `M0 / 256^k` in terms of `M0 / 256^(k+1)`. -/
theorem div_pow_succ (M0 k : Nat) :
    M0 / 256 ^ k = 256 * (M0 / 256 ^ (k + 1)) + M0 / 256 ^ k % 256 := by
  have h := Nat.div_add_mod (M0 / 256 ^ k) 256
  rw [Nat.div_div_eq_div_mul, ← pow_succ] at h
  omega

/-- The full 72-bit product splits into MUL low and MULHU high parts. -/
theorem mul_split (byte b : Word) :
    byte.toNat * b.toNat
      = (byte.toNat * b.toNat) % 2 ^ 64 + 2 ^ 64 * (byte.toNat * b.toNat / 2 ^ 64) := by
  have h := Nat.div_add_mod (byte.toNat * b.toNat) (2 ^ 64)
  omega

/-- MULHU output bound: `M / 2^64 ≤ 254` when `M = byte.toNat * b.toNat`. -/
theorem mulhu_le_254 (byte b : Word) (hb : byte.toNat ≤ 255) :
    byte.toNat * b.toNat / 2 ^ 64 ≤ 254 := by
  have hb2 : b.toNat ≤ 2 ^ 64 - 1 := by have h := BitVec.isLt b; omega
  have hM : byte.toNat * b.toNat ≤ 255 * (2 ^ 64 - 1) := Nat.mul_le_mul hb hb2
  omega

/-- The stored mulhu-add byte carries nothing: `(q + c) / 256 = 0`. -/
theorem mulhu_add_carry_zero (q c : Nat) (hq : q ≤ 254) (hc : c ≤ 1) :
    (q + c) / 256 = 0 := by omega

/-- The stored mulhu-add byte is exact: `(q + c) % 256 = q + c`. -/
theorem mulhu_add_byte_exact (q c : Nat) (hq : q ≤ 254) (hc : c ≤ 1) :
    (q + c) % 256 = q + c := by omega

/-- Little-endian take-succ: one more digit appended. -/
theorem leBytesToNat_take_succ (bs : List (BitVec 8)) (i : Nat) (hi : i < bs.length) :
    leBytesToNat (bs.take (i + 1))
      = leBytesToNat (bs.take i) + 256 ^ i * (bs[i]'hi).toNat := by
  rw [List.take_add, List.take_one_drop_eq_of_lt_length hi, leBytesToNat_append,
    List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  simp [leBytesToNat]

/-- Big-endian index into the reversed list. -/
theorem reverse_getElem (bs : List (BitVec 8)) (i : Nat) (hi : i < bs.length)
    (hlen : bs.length = 32) :
    (bs.reverse[i]'(by rw [List.length_reverse]; omega)) = bs[31 - i]'(by omega) := by
  rw [List.getElem_reverse]
  simp [hlen]

/-! ## §3  The ripple: functional byte state + value identity

    The 8-round ripple's accumulator bytes and carry are deterministic
    functions of the round count, so we track them as pure recursive
    functions (`mulCarry`, `rippleState`) — mirroring
    `U256AddBeSAsm.addCarryState`.  The machine-level loop invariant then
    needs no `leBytesToNat` algebra; the value identity
    (`leBytesToNat_rippleState`) is a standalone list lemma. -/

/-- Ripple carry sequence: `c_0 = 0`,
    `c_{k+1} = (accE[i+k] + (M0 / 256^k) % 256 + c_k) / 256`. -/
def mulCarry (accE : List (BitVec 8)) (M0 i : Nat) : Nat → Nat
  | 0 => 0
  | (k + 1) =>
    ((accE.getD (i + k) 0).toNat + (M0 / 256 ^ k) % 256 + mulCarry accE M0 i k) / 256

/-- Acc bytes after `k` ripple rounds: byte `i + k` replaced by the low byte
    of `accE[i+k] + (M0/256^k) % 256 + c_k`. -/
def rippleState (accE : List (BitVec 8)) (M0 i : Nat) : Nat → List (BitVec 8)
  | 0 => accE
  | (k + 1) => (rippleState accE M0 i k).set (i + k)
      (BitVec.ofNat 8
        ((accE.getD (i + k) 0).toNat + (M0 / 256 ^ k) % 256 + mulCarry accE M0 i k))

@[simp] theorem rippleState_zero (accE : List (BitVec 8)) (M0 i : Nat) :
    rippleState accE M0 i 0 = accE := rfl

theorem rippleState_succ (accE : List (BitVec 8)) (M0 i k : Nat) :
    rippleState accE M0 i (k + 1) = (rippleState accE M0 i k).set (i + k)
      (BitVec.ofNat 8
        ((accE.getD (i + k) 0).toNat + (M0 / 256 ^ k) % 256 + mulCarry accE M0 i k)) := rfl

theorem length_rippleState (accE : List (BitVec 8)) (M0 i k : Nat) :
    (rippleState accE M0 i k).length = accE.length := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rippleState_succ, List.length_set, ih]

private theorem getD_set_ne {l : List (BitVec 8)} {i j : Nat}
    {b d : BitVec 8} (h : i ≠ j) :
    (l.set i b).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h,
    List.getD_eq_getElem?_getD]

private theorem getD_eq_getElem' {l : List (BitVec 8)} {j : Nat} {d : BitVec 8}
    (hj : j < l.length) : l.getD j d = l[j]'hj := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

/-- Bytes at or past `i + k` are untouched by the first `k` rounds. -/
theorem getD_rippleState_of_ge (accE : List (BitVec 8)) (M0 i k j : Nat)
    (h : i + k ≤ j) :
    (rippleState accE M0 i k).getD j 0 = accE.getD j 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [rippleState_succ, getD_set_ne (by omega), ih (by omega)]

theorem getElem_rippleState_of_ge (accE : List (BitVec 8)) (M0 i k j : Nat)
    (h : i + k ≤ j) (hj : j < accE.length) :
    (rippleState accE M0 i k)[j]'(by rw [length_rippleState]; exact hj)
      = accE[j]'hj := by
  have h1 := getD_rippleState_of_ge accE M0 i k j h
  rw [getD_eq_getElem' (d := (0 : BitVec 8))
      (by rw [length_rippleState]; exact hj)] at h1
  rw [getD_eq_getElem' hj] at h1
  exact h1

theorem mulCarry_le_one (accE : List (BitVec 8)) (M0 i k : Nat) :
    mulCarry accE M0 i k ≤ 1 := by
  induction k with
  | zero => simp [mulCarry]
  | succ k ih =>
      have hbyte : (accE.getD (i + k) 0).toNat ≤ 255 := by
        have := (accE.getD (i + k) (0 : BitVec 8)).isLt; omega
      have hm : (M0 / 256 ^ k) % 256 ≤ 255 := by
        have := Nat.mod_lt (M0 / 256 ^ k) (by decide : 0 < 256); omega
      have hdiv : ((accE.getD (i + k) 0).toNat + (M0 / 256 ^ k) % 256 +
          mulCarry accE M0 i k) / 256 ≤ (255 + 255 + 1) / 256 :=
        Nat.div_le_div_right (by omega)
      have : (255 + 255 + 1) / 256 = 1 := by decide
      rw [show mulCarry accE M0 i (k + 1)
          = ((accE.getD (i + k) 0).toNat + (M0 / 256 ^ k) % 256 +
              mulCarry accE M0 i k) / 256 from rfl]
      omega

/-- Byte `j` contributes at least `256^j · bs[j]` to the little-endian value. -/
theorem leBytesToNat_getElem_le (bs : List (BitVec 8)) (j : Nat) (hj : j < bs.length) :
    256 ^ j * (bs[j]'hj).toNat ≤ leBytesToNat bs := by
  have e := leBytesToNat_eq_take_add bs j (Nat.le_of_lt hj)
  have hd : leBytesToNat (bs.drop j)
      = (bs[j]'hj).toNat + 256 * leBytesToNat (bs.drop (j + 1)) := by
    rw [List.drop_eq_getElem_cons hj, leBytesToNat_cons]
  rw [hd, Nat.mul_add] at e
  omega

/-- **Value identity of the ripple** (additive form; subtractive forms are
    vacuous under `Nat` truncated subtraction): after `k` rounds,
    `le_k + (M0/256^k + c_k) · 256^(i+k) = le_0 + M0 · 256^i`. -/
theorem leBytesToNat_rippleState (accE : List (BitVec 8)) (M0 i k : Nat)
    (hlen : accE.length = 40) (hi : i < 32) (hk : k ≤ 8) :
    leBytesToNat (rippleState accE M0 i k)
        + (M0 / 256 ^ k + mulCarry accE M0 i k) * 256 ^ (i + k)
      = leBytesToNat accE + M0 * 256 ^ i := by
  induction k with
  | zero => simp [mulCarry]
  | succ k ih =>
      have hk8 : k ≤ 8 := by omega
      have ihk := ih hk8
      have hjk : i + k < accE.length := by omega
      have hjk' : i + k < (rippleState accE M0 i k).length := by
        rw [length_rippleState]; exact hjk
      have hv : (BitVec.ofNat 8
          ((accE.getD (i + k) 0).toNat + (M0 / 256 ^ k) % 256 + mulCarry accE M0 i k)).toNat
          = ((accE[i + k]'hjk).toNat + (M0 / 256 ^ k) % 256 + mulCarry accE M0 i k) % 256 := by
        rw [BitVec.toNat_ofNat, show (2 : Nat) ^ 8 = 256 from by decide,
          getD_eq_getElem' hjk]
      have hck1 : mulCarry accE M0 i (k + 1)
          = ((accE[i + k]'hjk).toNat + (M0 / 256 ^ k) % 256 + mulCarry accE M0 i k) / 256 := by
        show ((accE.getD (i + k) 0).toNat + (M0 / 256 ^ k) % 256 + mulCarry accE M0 i k) / 256 = _
        rw [getD_eq_getElem' hjk]
      -- The additive link: `O·v + (Mk1 + ck1)·(256·O) = (Mk + ck)·O + O·ak`.
      have hs : (accE[i + k]'hjk).toNat + (M0 / 256 ^ k) % 256 + mulCarry accE M0 i k
          = (BitVec.ofNat 8 ((accE.getD (i + k) 0).toNat + (M0 / 256 ^ k) % 256 +
              mulCarry accE M0 i k)).toNat + 256 * mulCarry accE M0 i (k + 1) := by
        rw [hv, hck1]; omega
      have hsO := congrArg (· * 256 ^ (i + k)) hs
      simp only [Nat.add_mul] at hsO
      have hA : (M0 / 256 ^ k) * 256 ^ (i + k)
          = (256 * (M0 / 256 ^ (k + 1))) * 256 ^ (i + k)
            + (M0 / 256 ^ k) % 256 * 256 ^ (i + k) := by
        conv_lhs => rw [div_pow_succ M0 k]
        ring
      have hlink : 256 ^ (i + k) *
            (BitVec.ofNat 8 ((accE.getD (i + k) 0).toNat + (M0 / 256 ^ k) % 256 +
              mulCarry accE M0 i k)).toNat
          + (M0 / 256 ^ (k + 1) + mulCarry accE M0 i (k + 1)) * (256 * 256 ^ (i + k))
          = (M0 / 256 ^ k + mulCarry accE M0 i k) * 256 ^ (i + k)
            + 256 ^ (i + k) * (accE[i + k]'hjk).toNat := by
        rw [show (M0 / 256 ^ (k + 1) + mulCarry accE M0 i (k + 1)) * (256 * 256 ^ (i + k))
            = (256 * (M0 / 256 ^ (k + 1))) * 256 ^ (i + k)
              + (256 * mulCarry accE M0 i (k + 1)) * 256 ^ (i + k) from by ring,
          show (M0 / 256 ^ k + mulCarry accE M0 i k) * 256 ^ (i + k)
            = (M0 / 256 ^ k) * 256 ^ (i + k) + mulCarry accE M0 i k * 256 ^ (i + k) from
            Nat.add_mul _ _ _,
          show 256 ^ (i + k) *
              (BitVec.ofNat 8 ((accE.getD (i + k) 0).toNat + (M0 / 256 ^ k) % 256 +
                mulCarry accE M0 i k)).toNat
            = (BitVec.ofNat 8 ((accE.getD (i + k) 0).toNat + (M0 / 256 ^ k) % 256 +
                mulCarry accE M0 i k)).toNat * 256 ^ (i + k) from Nat.mul_comm _ _,
          show 256 ^ (i + k) * (accE[i + k]'hjk).toNat
            = (accE[i + k]'hjk).toNat * 256 ^ (i + k) from Nat.mul_comm _ _,
          hA]
        omega
      -- Set-step, then close with the link and the induction hypothesis.
      have hle : 256 ^ (i + k) * ((rippleState accE M0 i k)[i + k]'hjk').toNat
          ≤ leBytesToNat (rippleState accE M0 i k) :=
        leBytesToNat_getElem_le _ _ hjk'
      rw [getElem_rippleState_of_ge accE M0 i k (i + k) (by omega) hjk] at hle
      rw [rippleState_succ,
        leBytesToNat_set _ _ _ hjk',
        getElem_rippleState_of_ge accE M0 i k (i + k) (by omega) hjk]
      rw [show 256 ^ (i + (k + 1)) = 256 * 256 ^ (i + k) from by ring]
      omega

end EvmAsm.Codegen.U256MulU64Be
