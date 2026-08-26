/-
  EvmAsm.Evm64.DivMod.Spec.N3V5HvSmall

  The n=3 small-divisor fact `2 * val256 v0 v1 v2 0 < 2^256` (the `hv_small`
  hypothesis of `mulsubN4_c3_le_one_of_plus_two_of_v_lt` / the n3 carry-from-shape
  discharges), from the normalized n=3 divisor bound `val256 v0 v1 v2 0 < 2^192`
  (`n3_val256_v_lt_pow192`).  n3 mirror of `n2_two_val256_v_lt_pow256`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N3V5RemainderLt

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- For the n=3 (three-limb, `v3=0`) divisor, `2 * val256 v0 v1 v2 0 < 2^256`. -/
theorem n3_two_val256_v_lt_pow256 (v0 v1 v2 : Word) :
    2 * val256 v0 v1 v2 0 < 2 ^ 256 := by
  have h := n3_val256_v_lt_pow192 v0 v1 v2
  have he : (2 : Nat) ^ 256 = 2 * (2 ^ 192 * 2 ^ 63) := by norm_num
  rw [he]
  have hp : 0 < (2 : Nat) ^ 63 := by positivity
  calc 2 * val256 v0 v1 v2 0 < 2 * 2 ^ 192 := by omega
    _ ≤ 2 * (2 ^ 192 * 2 ^ 63) := by
        have : (2 : Nat) ^ 192 ≤ 2 ^ 192 * 2 ^ 63 := Nat.le_mul_of_pos_right _ hp
        omega

end EvmAsm.Evm64
