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

/-- Low quotient word after adding three 128-bit product fragments to a low/high pair. -/
theorem mulModProductLayoutCarryLowAfterThreeAdditions
    (x mu20 lo20 mu11 lo11 mu02 lo02 : Nat) :
    let w := 2 ^ 64
    let r0 := x % w
    let q0 := x / w % w
    let r1 := (r0 + lo20) % w
    let q1 := (q0 + (mu20 + (r0 + lo20) / w) % w) % w
    let r2 := (r1 + lo11) % w
    let q2 := (q1 + (mu11 + (r1 + lo11) / w) % w) % w
    let q3 := (q2 + (mu02 + (r2 + lo02) / w) % w) % w
    q3 = (mu02 * w + lo02 + (mu11 * w + lo11) + (mu20 * w + lo20) + x) /
        w % w := by
  intro w r0 q0 r1 q1 r2 q2 q3
  have h_w : 0 < w := by norm_num [w]
  have h0 : w * (x / w) + r0 = x := Nat.div_add_mod x w
  have h1 : w * ((r0 + lo20) / w) + r1 = r0 + lo20 :=
    Nat.div_add_mod (r0 + lo20) w
  have h2 : w * ((r1 + lo11) / w) + r2 = r1 + lo11 :=
    Nat.div_add_mod (r1 + lo11) w
  have h3 : w * ((r2 + lo02) / w) + (r2 + lo02) % w = r2 + lo02 :=
    Nat.div_add_mod (r2 + lo02) w
  have h_rem : (r2 + lo02) % w < w := Nat.mod_lt _ h_w
  have h_sum : mu02 * w + lo02 + (mu11 * w + lo11) + (mu20 * w + lo20) + x =
      w * (x / w + mu20 + (r0 + lo20) / w + mu11 + (r1 + lo11) / w +
        mu02 + (r2 + lo02) / w) + (r2 + lo02) % w := by
    subst w
    norm_num at h0 h1 h2 h3 ⊢
    omega
  rw [h_sum]
  subst q3
  subst q2
  subst q1
  subst r2
  subst r1
  subst q0
  subst r0
  norm_num
  omega



/-- High carry word after adding three 128-bit addends to a two-word accumulator. -/
theorem mulModProductLayoutCarryHighFromTwoWordAccumulator
    (lo hi mu20 lo20 mu11 lo11 mu02 lo02 : Nat)
    (hlo : lo < 2 ^ 64) (hhi : hi < 2 ^ 64)
    (h20 : mu20 + (lo + lo20) / 2 ^ 64 < 2 ^ 64)
    (h11 : mu11 + ((lo + lo20) % 2 ^ 64 + lo11) / 2 ^ 64 < 2 ^ 64)
    (h02 : mu02 + (((lo + lo20) % 2 ^ 64 + lo11) % 2 ^ 64 + lo02) / 2 ^ 64 < 2 ^ 64) :
    let w := 2 ^ 64
    let lo1 := (lo + lo20) % w
    let hi1 := (hi + (mu20 + (lo + lo20) / w) % w) % w
    let c1 := (hi + (mu20 + (lo + lo20) / w) % w) / w
    let lo2 := (lo1 + lo11) % w
    let hi2 := (hi1 + (mu11 + (lo1 + lo11) / w) % w) % w
    let c2 := (hi1 + (mu11 + (lo1 + lo11) / w) % w) / w
    let c3 := (hi2 + (mu02 + (lo2 + lo02) / w) % w) / w
    ((c1 + c2) % w + c3) % w =
      ((mu02 * w + lo02 + (mu11 * w + lo11) + (mu20 * w + lo20) + (hi * w + lo)) /
        w / w) % w := by
  intro w lo1 hi1 c1 lo2 hi2 c2 c3
  subst c3
  subst c2
  subst hi2
  subst lo2
  subst c1
  subst hi1
  subst lo1
  subst w
  norm_num at hlo hhi h20 h11 h02 ⊢
  omega

/-- High carry word when the three addends are known 64x64 product fragments. -/
theorem mulModProductLayoutCarryHighFromTwoWordAccumulatorProducts
    (lo hi mu20 lo20 mu11 lo11 mu02 lo02 : Nat)
    (hlo : lo < 2 ^ 64) (hhi : hi < 2 ^ 64)
    (hp20 : mu20 * 2 ^ 64 + lo20 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (hp11 : mu11 * 2 ^ 64 + lo11 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (hp02 : mu02 * 2 ^ 64 + lo02 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) :
    let w := 2 ^ 64
    let lo1 := (lo + lo20) % w
    let hi1 := (hi + (mu20 + (lo + lo20) / w) % w) % w
    let c1 := (hi + (mu20 + (lo + lo20) / w) % w) / w
    let lo2 := (lo1 + lo11) % w
    let hi2 := (hi1 + (mu11 + (lo1 + lo11) / w) % w) % w
    let c2 := (hi1 + (mu11 + (lo1 + lo11) / w) % w) / w
    let c3 := (hi2 + (mu02 + (lo2 + lo02) / w) % w) / w
    ((c1 + c2) % w + c3) % w =
      ((mu02 * w + lo02 + (mu11 * w + lo11) + (mu20 * w + lo20) + (hi * w + lo)) /
        w / w) % w := by
  apply mulModProductLayoutCarryHighFromTwoWordAccumulator
  · exact hlo
  · exact hhi
  · norm_num at hlo hp20 ⊢
    omega
  · have h_lo1 : (lo + lo20) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
    norm_num at h_lo1 hp11 ⊢
    omega
  · have h_lo1 : (lo + lo20) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
    have h_lo2 : ((lo + lo20) % 2 ^ 64 + lo11) % 2 ^ 64 < 2 ^ 64 :=
      Nat.mod_lt _ (by norm_num)
    norm_num at h_lo2 hp02 ⊢
    omega

/-- Low word of the column-2 carry generated by three lower product columns. -/
theorem mulModProductLayoutColumn2CarryLowModEq
    (mu00 lo00 lo10 mu10 lo20 mu20 lo01 mu01 lo11 mu11 lo02 mu02 : Nat)
    (hlo00 : lo00 < 2 ^ 64) (hlo01 : lo01 < 2 ^ 64)
    (hp00 : mu00 * 2 ^ 64 + lo00 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (hp10 : mu10 * 2 ^ 64 + lo10 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (hp01 : mu01 * 2 ^ 64 + lo01 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) :
    (((mu10 + (mu00 + lo10) / 2 ^ 64 + lo20) % 2 ^ 64 +
       (mu01 + ((mu00 + lo10) % 2 ^ 64 + lo01) / 2 ^ 64) % 2 ^ 64) / 2 ^ 64 +
      (mu11 +
        ((mu10 + (mu00 + lo10) / 2 ^ 64 + lo20 +
          (mu01 + ((mu00 + lo10) % 2 ^ 64 + lo01) / 2 ^ 64)) % 2 ^ 64 +
         lo11) / 2 ^ 64) +
      (mu20 + ((mu10 + (mu00 + lo10) / 2 ^ 64) % 2 ^ 64 + lo20) / 2 ^ 64) +
      (mu02 +
        ((mu10 + (mu00 + lo10) / 2 ^ 64 + lo20 +
          (mu01 + ((mu00 + lo10) % 2 ^ 64 + lo01) / 2 ^ 64) + lo11) % 2 ^ 64 +
         lo02) / 2 ^ 64)) % 2 ^ 64 =
    (mu02 * 2 ^ 64 + lo02 + (mu11 * 2 ^ 64 + lo11) + (mu20 * 2 ^ 64 + lo20) +
      (mu01 * 2 ^ 64 + lo01 + (mu10 * 2 ^ 64 + lo10) +
        (mu00 * 2 ^ 64 + lo00) / 2 ^ 64) / 2 ^ 64) / 2 ^ 64 % 2 ^ 64 := by
  omega


end EvmAsm.Evm64
