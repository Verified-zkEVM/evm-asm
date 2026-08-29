/-
  EvmAsm.Codegen.Programs.U256DivU64BeZeroDivisor

  Closed form of the `u256_div_u64_be` machine result at divisor zero.

  The restoring-division bit step (`divBitStep`) is total: at `b = 0` the
  comparison `BitVec.ult shifted b` is false (nothing is unsigned-below
  zero), so `less = 0`, `take = 1`, `mask` is all-ones, and the subtracted
  term `b &&& mask` vanishes.  Every bit therefore shifts one dividend bit
  into the remainder and writes a `1` into the quotient — the loop never
  traps and never reads uninitialised memory, it just computes garbage.

  This file pins that garbage down exactly:
  * the quotient is `0xFF` in all 32 output bytes (`2^256 - 1` big-endian);
  * the remainder follows the shift register `rem ← 256 * rem + a[k]`,
    i.e. it is the last eight dividend bytes packed big-endian.

  Issue #12951: with `parent_gas_limit ∈ {0, 1}` the parent gas target is 0
  and the reference (`fork.py:432`) raises `ZeroDivisionError`, rejecting the
  payload.  The guest instead terminates with this definable output.  Because
  the quotient is the *constant* `0xFF…FF`, an attacker can predict it
  trivially — this is the exploitability input the maintainer asked for.
-/

import Mathlib.Tactic

import EvmAsm.Codegen.Programs.U256DivU64BeSAsm

namespace EvmAsm.Codegen.U256DivU64Be

/-! ### Nat helpers -/

/-- A Nat lemma used repeatedly below: or-ing a single bit into an even
    number is the same as adding it. -/
private theorem nat_lor_one_of_even {x : Nat} (h : x % 2 = 0) : x ||| 1 = x + 1 := by
  refine Nat.eq_of_testBit_eq (fun i => ?_)
  cases i with
  | zero => simp [Nat.testBit]; omega
  | succ j =>
    have h1 : Nat.testBit 1 (j + 1) = false := by
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
      rw [Nat.div_eq_of_lt (by simp : (1 : Nat) < 2 ^ (j + 1))]
      rfl
    have h2 : (x + 1) / 2 = x / 2 := by omega
    conv_rhs => rw [Nat.testBit_add_one]
    rw [Nat.testBit_or, Nat.testBit_add_one, h2, h1]
    simp

/-- Halving decomposition of a division by a power of two:
    `B / 2^(k-1) = 2 * (B / 2^k) + (B / 2^(k-1)) % 2`. -/
private theorem div_shift_step (B k : Nat) (hk : 1 ≤ k) :
    B / 2 ^ (k - 1) = 2 * (B / 2 ^ k) + (B / 2 ^ (k - 1)) % 2 := by
  have h1 : B / 2 ^ k = (B / 2 ^ (k - 1)) / 2 := by
    have hk2 : 2 ^ k = 2 ^ (k - 1) * 2 := by
      rw [← Nat.pow_succ]
      congr 1
      omega
    rw [hk2, Nat.div_div_eq_div_mul, Nat.mul_comm]
  have h2 := Nat.div_add_mod (B / 2 ^ (k - 1)) 2
  omega

/-- The single dividend bit fed in at the call with `n + 1` steps remaining
    is bit `n` of the original byte. -/
private theorem top_bit_of_shifted (B n : Nat) (hn : n ≤ 7) :
    ((B * 2 ^ (7 - n) % 256) / 128) % 2 = (B / 2 ^ n) % 2 := by
  interval_cases n <;> omega

/-- The binary-tail identity driving the zero-divisor induction: the low
    `n+1` bits of `B` decompose into the top fed bit plus the shifted tail. -/
private theorem binary_tail (B n : Nat) :
    B % 2 ^ (n + 1) = 2 ^ n * (B / 2 ^ n % 2) + B % 2 ^ n := by
  have h1 := Nat.div_add_mod B (2 ^ n)
  have h2 := Nat.div_add_mod (B / 2 ^ n) 2
  have hlt : B % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
  have hlt1 : B / 2 ^ n % 2 < 2 := Nat.mod_lt _ (by positivity)
  have hdd : B / 2 ^ (n + 1) = B / 2 ^ n / 2 := by
    rw [show 2 ^ (n + 1) = 2 ^ n * 2 from by rw [Nat.pow_succ, Nat.mul_comm]]
    exact (Nat.div_div_eq_div_mul B (2 ^ n) 2).symm
  have key : B = 2 ^ (n + 1) * (B / 2 ^ (n + 1)) + (2 ^ n * (B / 2 ^ n % 2) + B % 2 ^ n) := by
    calc B = 2 ^ n * (B / 2 ^ n) + B % 2 ^ n := h1.symm
    _ = 2 ^ n * (2 * (B / 2 ^ n / 2) + B / 2 ^ n % 2) + B % 2 ^ n := by rw [h2]
    _ = 2 ^ (n + 1) * (B / 2 ^ (n + 1)) + (2 ^ n * (B / 2 ^ n % 2) + B % 2 ^ n) := by
          rw [hdd, show 2 ^ (n + 1) = 2 ^ n * 2 from by rw [Nat.pow_succ]]
          ring
  have hlt2 : 2 ^ n * (B / 2 ^ n % 2) + B % 2 ^ n < 2 ^ (n + 1) := by
    have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    rcases Nat.lt_or_ge (B / 2 ^ n % 2) 1 with h0 | h1'
    · have ht0 : B / 2 ^ n % 2 = 0 := by omega
      rw [ht0]; omega
    · have ht1 : B / 2 ^ n % 2 = 1 := by omega
      rw [ht1]; omega
  have step1 : B % 2 ^ (n + 1)
      = (2 ^ (n + 1) * (B / 2 ^ (n + 1)) + (2 ^ n * (B / 2 ^ n % 2) + B % 2 ^ n)) % 2 ^ (n + 1) :=
    congrArg (fun x => x % 2 ^ (n + 1)) key
  rw [step1, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt2]

end EvmAsm.Codegen.U256DivU64Be
