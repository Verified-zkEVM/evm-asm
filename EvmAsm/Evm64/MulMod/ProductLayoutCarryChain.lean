import EvmAsm.Evm64.MulMod.ProductLayoutCall15

namespace EvmAsm.Evm64

/-- Quotient accumulated by four sequential low-word additions. -/
theorem mulModProductLayoutCarryChainQuot4
    (feed lo30 lo21 lo12 lo03 : Nat) :
    let w := 2 ^ 64
    let q0 := (feed + lo30) / w
    let r0 := (feed + lo30) % w
    let q1 := (r0 + lo21) / w
    let r1 := (r0 + lo21) % w
    let q2 := (r1 + lo12) / w
    let r2 := (r1 + lo12) % w
    let q3 := (r2 + lo03) / w
    (feed + lo30 + lo21 + lo12 + lo03) / w = q0 + q1 + q2 + q3 := by
  intro w q0 r0 q1 r1 q2 r2 q3
  have h_w : 0 < w := by norm_num [w]
  have h0 : w * q0 + r0 = feed + lo30 := Nat.div_add_mod (feed + lo30) w
  have h1 : w * q1 + r1 = r0 + lo21 := Nat.div_add_mod (r0 + lo21) w
  have h2 : w * q2 + r2 = r1 + lo12 := Nat.div_add_mod (r1 + lo12) w
  have h3 : w * q3 + (r2 + lo03) % w = r2 + lo03 := Nat.div_add_mod (r2 + lo03) w
  have h_rem : (r2 + lo03) % w < w := Nat.mod_lt _ h_w
  have h_sum : feed + lo30 + lo21 + lo12 + lo03 =
      w * (q0 + q1 + q2 + q3) + (r2 + lo03) % w := by
    subst w
    norm_num at h0 h1 h2 h3 ⊢
    omega
  rw [h_sum]
  have h_div : ((r2 + lo03) % w + w * (q0 + q1 + q2 + q3)) / w =
      q0 + q1 + q2 + q3 := by
    rw [show w * (q0 + q1 + q2 + q3) = (q0 + q1 + q2 + q3) * w by
      rw [Nat.mul_comm]]
    rw [Nat.add_mul_div_right _ _ h_w]
    rw [Nat.div_eq_of_lt h_rem, Nat.zero_add]
  simpa [Nat.add_comm] using h_div

/-- High word accumulated by the column-3 sequential carry chain. -/
theorem mulModProductLayoutCarryChainHigh4ModEq
    (hi feed lo30 mu30 lo21 mu21 lo12 mu12 lo03 mu03 : Nat) :
    let feed06 := (feed + lo30) % 2 ^ 64
    let feed07 := (feed06 + lo21) % 2 ^ 64
    let feed08 := (feed07 + lo12) % 2 ^ 64
    ((((hi + (mu30 + (feed + lo30) / 2 ^ 64) % 2 ^ 64) % 2 ^ 64 +
          (mu21 + (feed06 + lo21) / 2 ^ 64) % 2 ^ 64) % 2 ^ 64 +
        (mu12 + (feed07 + lo12) / 2 ^ 64) % 2 ^ 64) % 2 ^ 64 +
      (mu03 + (feed08 + lo03) / 2 ^ 64) % 2 ^ 64) % 2 ^ 64 =
        (hi + mu30 + mu21 + mu12 + mu03 +
          (feed + lo30 + lo21 + lo12 + lo03) / 2 ^ 64) % 2 ^ 64 := by
  intro feed06 feed07 feed08
  have hq := mulModProductLayoutCarryChainQuot4 feed lo30 lo21 lo12 lo03
  dsimp only at hq
  rw [hq]
  subst feed08
  subst feed07
  subst feed06
  norm_num
  omega

end EvmAsm.Evm64
