/-
Pure byte-list / Nat machinery for the `u256_mul_u64_be` port.

The 256-bit accumulator lives in guest memory as a 40-byte little-endian
window at `u256m_acc`; the multiply loops maintain the invariant that its
`leBytesToNat` value tracks a partial product.  This file collects the
fold algebra (append/set/take/drop), zero-detection facts, and the BitVec
byte-operation wrappers (`&&& 255`, `>>> 8`, `MUL`/`MULHU`) those
invariants are stated with.
-/
import EvmAsm.Crypto.PowLadder
import EvmAsm.Rv64.Instructions
import EvmAsm.Evm64.EvmWordArith.MultiLimb
import Mathlib.Tactic.Ring
import Init.Data.List.Nat.TakeDrop

namespace EvmAsm.Codegen.U256MulU64Be

/-- Little-endian byte-list interpretation: the first byte is least significant. -/
def leBytesToNat : List (BitVec 8) → Nat
  | [] => 0
  | b :: rest => b.toNat + 256 * leBytesToNat rest

@[simp] theorem leBytesToNat_nil : leBytesToNat [] = 0 := rfl

@[simp] theorem leBytesToNat_cons (b : BitVec 8) (rest : List (BitVec 8)) :
    leBytesToNat (b :: rest) = b.toNat + 256 * leBytesToNat rest := rfl

theorem leBytesToNat_append (xs ys : List (BitVec 8)) :
    leBytesToNat (xs ++ ys) = leBytesToNat xs + 256 ^ xs.length * leBytesToNat ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.cons_append, leBytesToNat_cons, ih, List.length_cons]
      rw [Nat.pow_succ]
      ring

theorem leBytesToNat_append_singleton (bs : List (BitVec 8)) (b : BitVec 8) :
    leBytesToNat (bs ++ [b]) = leBytesToNat bs + 256 ^ bs.length * b.toNat := by
  rw [leBytesToNat_append]; simp

theorem leBytesToNat_lt : (bs : List (BitVec 8)) → leBytesToNat bs < 256 ^ bs.length := by
  intro bs
  induction bs with
  | nil => simp
  | cons b rest ih =>
      simp only [leBytesToNat_cons, List.length_cons, Nat.pow_succ]
      have hb : b.toNat < 256 := b.isLt
      have hpos : 0 < 256 ^ rest.length := Nat.pow_pos (by decide)
      have h1 : 256 * leBytesToNat rest + 256 ≤ 256 * 256 ^ rest.length := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left 256 (Nat.succ_le_of_lt ih)
      omega

/-- `(c + T * 256 * q) % (T * 256) = c` for `c` below the modulus. -/
theorem add_pow256_mul_mod (c T q : Nat) (h : c < T * 256) :
    (c + T * 256 * q) % (T * 256) = c := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

theorem leBytesToNat_take (bs : List (BitVec 8)) (n : Nat) :
    leBytesToNat (bs.take n) = leBytesToNat bs % 256 ^ n := by
  induction bs generalizing n with
  | nil => simp
  | cons b rest ih =>
      cases n with
      | zero => simp [Nat.mod_one]
      | succ n =>
          simp only [List.take_succ_cons, leBytesToNat_cons, ih]
          have hb : b.toNat < 256 := b.isLt
          have hpos : 0 < 256 ^ n := Nat.pow_pos (by decide)
          have hR : leBytesToNat rest % 256 ^ n < 256 ^ n := Nat.mod_lt _ hpos
          have hlt : b.toNat + 256 * (leBytesToNat rest % 256 ^ n) < 256 ^ n * 256 := by
            omega
          conv_rhs => rw [Nat.pow_succ, ← Nat.div_add_mod (leBytesToNat rest) (256 ^ n)]
          rw [Nat.mul_add]
          have key : b.toNat + (256 * (256 ^ n * (leBytesToNat rest / 256 ^ n)) +
              256 * (leBytesToNat rest % 256 ^ n)) =
              b.toNat + 256 * (leBytesToNat rest % 256 ^ n) +
                256 ^ n * 256 * (leBytesToNat rest / 256 ^ n) := by ring
          rw [key, add_pow256_mul_mod _ _ _ hlt]

theorem leBytesToNat_eq_take_add (bs : List (BitVec 8)) (n : Nat) (hn : n ≤ bs.length) :
    leBytesToNat bs = leBytesToNat (bs.take n) + 256 ^ n * leBytesToNat (bs.drop n) := by
  conv_lhs => rw [← List.take_append_drop n bs]
  rw [leBytesToNat_append, List.length_take, Nat.min_eq_left hn]

theorem leBytesToNat_set (bs : List (BitVec 8)) (j : Nat) (v : BitVec 8)
    (hj : j < bs.length) :
    leBytesToNat (bs.set j v) =
      leBytesToNat bs + 256 ^ j * v.toNat - 256 ^ j * (bs[j]'hj).toNat := by
  have hdecomp : bs = bs.take j ++ bs[j]'hj :: bs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j bs]
    rw [List.drop_eq_getElem_cons hj]
  have hset : bs.set j v = bs.take j ++ v :: bs.drop (j + 1) := by
    rw [List.set_eq_take_append_cons_drop, if_pos hj]
  have hlen : (bs.take j).length = j := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have lhs : leBytesToNat (bs.set j v) =
      leBytesToNat (bs.take j) + 256 ^ j * v.toNat +
        256 ^ (j + 1) * leBytesToNat (bs.drop (j + 1)) := by
    rw [hset, leBytesToNat_append, leBytesToNat_cons, hlen]
    ring
  have rhs : leBytesToNat bs =
      leBytesToNat (bs.take j) + 256 ^ j * (bs[j]'hj).toNat +
        256 ^ (j + 1) * leBytesToNat (bs.drop (j + 1)) := by
    conv_lhs => rw [hdecomp]
    rw [leBytesToNat_append, leBytesToNat_cons, hlen]
    ring
  rw [lhs, rhs]
  generalize 256 ^ j * (bs[j]'hj).toNat = P
  generalize 256 ^ j * v.toNat = Q
  omega

theorem leBytesToNat_pos_of_ne_zero {bs : List (BitVec 8)} {j : Nat} (hj : j < bs.length)
    (hv : (bs[j]'hj).toNat ≠ 0) : 256 ^ j ≤ leBytesToNat bs := by
  have hdecomp : bs = bs.take j ++ bs[j]'hj :: bs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j bs]
    rw [List.drop_eq_getElem_cons hj]
  have hlen : (bs.take j).length = j := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  rw [hdecomp, leBytesToNat_append, leBytesToNat_cons, hlen, Nat.mul_add]
  have h1 : 1 ≤ (bs[j]'hj).toNat := Nat.pos_of_ne_zero hv
  have h2 : 256 ^ j ≤ 256 ^ j * (bs[j]'hj).toNat := by
    conv_lhs => rw [← Nat.mul_one (256 ^ j)]
    exact Nat.mul_le_mul_left _ h1
  omega

theorem leBytesToNat_eq_zero : (bs : List (BitVec 8)) →
    leBytesToNat bs = 0 ↔ ∀ b ∈ bs, b.toNat = 0 := by
  intro bs
  induction bs with
  | nil => simp
  | cons b rest ih =>
      simp only [leBytesToNat_cons, List.forall_mem_cons]
      constructor
      · intro h
        obtain ⟨h1, h2⟩ := Nat.add_eq_zero_iff.mp h
        exact ⟨h1, ih.mp ((Nat.mul_eq_zero.mp h2).resolve_left (by decide))⟩
      · rintro ⟨h1, h2⟩
        rw [h1, ih.mpr h2]

theorem leBytesToNat_eq_zero_of_all_zero {bs : List (BitVec 8)}
    (h : ∀ b ∈ bs, b.toNat = 0) : leBytesToNat bs = 0 :=
  (leBytesToNat_eq_zero bs).mpr h

/-- `256 ^ n = 2 ^ (8 * n)`; lets `256`-scale and `2`-scale bounds interact. -/
theorem pow256_eq (n : Nat) : 256 ^ n = 2 ^ (8 * n) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]

/-- `foldl` with a nonzero initial accumulator, used to relate `beBytesToNat` to the
little-endian fold. -/
theorem beBytesToNat_foldl_init (init : Nat) (bs : List (BitVec 8)) :
    bs.foldl (fun acc b => acc * 256 + b.toNat) init =
      init * 256 ^ bs.length + Crypto.beBytesToNat bs := by
  induction bs generalizing init with
  | nil => simp [Crypto.beBytesToNat]
  | cons b rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih, Nat.pow_succ]
      conv_rhs => rw [Crypto.beBytesToNat, List.foldl_cons, ih]
      ring

theorem beBytesToNat_cons (b : BitVec 8) (rest : List (BitVec 8)) :
    Crypto.beBytesToNat (b :: rest) =
      b.toNat * 256 ^ rest.length + Crypto.beBytesToNat rest := by
  rw [Crypto.beBytesToNat, List.foldl_cons, beBytesToNat_foldl_init]
  ring

theorem leBytesToNat_reverse (bs : List (BitVec 8)) :
    leBytesToNat bs.reverse = Crypto.beBytesToNat bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
      rw [List.reverse_cons, leBytesToNat_append_singleton, List.length_reverse, ih,
        beBytesToNat_cons, Nat.mul_comm, Nat.add_comm]

/-! ### BitVec byte-operation wrappers -/

/-- `signExtend12 255 = 255` (255 < 2^11, so no sign extension). -/
@[simp] theorem signExtend12_255 : Rv64.signExtend12 (255 : BitVec 12) = (255 : Word) := by decide

/-- Low byte of a 64-bit word as a Nat. -/
theorem toNat_and_255 (x : Word) : (x &&& 255#64).toNat = x.toNat % 256 := by
  have h255 : (255#64).toNat = 2 ^ 8 - 1 := by decide
  rw [BitVec.toNat_and, h255, Nat.and_two_pow_sub_one_eq_mod]

/-- Logical shift-right by 8 as Nat division. -/
theorem toNat_shiftRight_8 (x : Word) : (x >>> 8).toNat = x.toNat / 256 := by
  simp [Nat.shiftRight_eq_div_pow]

/-- The `MULHU` result as a Nat: the high 64 bits of the 128-bit product. -/
theorem mulhu_toNat (x y : Word) : (Rv64.rv64_mulhu x y).toNat = x.toNat * y.toNat / 2 ^ 64 :=
  Evm64.EvmWord.rv64_mulhu_toNat

/-- The `MUL` result as a Nat: the low 64 bits of the product. -/
theorem mul_toNat (x y : Word) : (x * y).toNat = (x.toNat * y.toNat) % 2 ^ 64 :=
  BitVec.toNat_mul x y

end EvmAsm.Codegen.U256MulU64Be
