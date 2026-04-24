/-
  EvmAsm.Evm64.EvmWordArith.MulCorrect

  Bridge lemma: the column-organized schoolbook multiply from evm_mul_spec
  produces the correct limbs of (a * b : EvmWord).

  Column structure (NOT a linear carry chain like ADD):
    Col0: b[0] × {a[0],a[1],a[2],a[3]} → initializes r0, r1 partial, r2 partial, r3 partial
    Col1: b[1] × {a[0],a[1],a[2]}      → finalizes r1, updates r2, r3 partial
    Col2: b[2] × {a[0],a[1]}            → finalizes r2, updates r3
    Col3: b[3] × {a[0]}                 → finalizes r3

  Reference mapping (evm_mul_spec postcondition → result limbs):
    sp+32 ↦ c0_r0      → (a*b).getLimb 0
    sp+40 ↦ c1_r1      → (a*b).getLimb 1
    sp+48 ↦ c2_r2      → (a*b).getLimb 2
    sp+56 ↦ r3_final   → (a*b).getLimb 3

  Proof strategy — each limb uses a progressively heavier machinery:

    Limb 0 (`mul_correct_limb0`):
      Direct `BitVec.eq_of_toNat_eq` + `norm_num`.
      The lowest limb is just `a0 * b0` mod 2^64, no carries involved.

    Limb 1 (`mul_correct_limb1`):
      Shared helper `limb_mod_div_cancel` + `norm_num` with `rv64_mulhu_toNat`,
      `mul_toNat`, `toNat_eq_limb_sum`, closed by `ring`/`omega`. Two-column
      contribution (a0*b1 + a1*b0 + carry), still no explicit carry atom.

    Limb 2 (`mul_correct_limb2`):
      Same skeleton as limb 1 plus `carry_toNat` for the col0→col1 carry
      passing through this column.

    Limb 3 (`mul_correct_limb3`) — the main event (~450 lines):
      Euclidean linearization: every `x.toNat = (a+b) % 2^64` /
      `carry = (a+b) / 2^64` pair is combined into `carry*W + x = a+b`
      via `div_mod_eq`, producing only LINEAR equations for omega.
      Structural pieces:
        * `schoolbook_limb3` — expands the full 4×4 product and telescopes
          the carry chain using `carry_telescoping` + `low_part_bound` to
          get `P / 2^192 % 2^64 = (D3 + C3) % 2^64`.
        * `carry_chain_limb3` — runs the implementation's actual carry
          chain (22 toNat unfoldings for col0+col1+col2+col3) and reduces
          the final equation to `carry_chain_mod_eq` (pure Nat identity).
        * `carry_chain_mod_eq` — closed by omega after flattening the
          nested div/mods via `qC{1,2,3}_simp_helper`.
-/

import EvmAsm.Evm64.EvmWordArith.MultiLimb
import EvmAsm.Evm64.EvmWordArith.Arithmetic

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord


-- Abbreviations
private abbrev W := (2:Nat)^64

-- ============================================================================
-- MUL correctness: column-organized schoolbook multiply produces (a * b) limbs
-- ============================================================================

-- ============================================================================
-- Helper: mod/div chain identity
-- For limb k: P % W^4 / W^k % W = P / W^k % W
-- ============================================================================

private theorem limb_mod_div_cancel (P : Nat) (k : Nat) (hk : k < 4) :
    P % (2^256) / 2^(64*k) % 2^64 = P / 2^(64*k) % 2^64 := by
  have h : 2^256 = 2^(64*k) * 2^(256 - 64*k) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [h, Nat.mod_mul_right_div_self]
  have h2 : 2^(256 - 64*k) = 2^64 * 2^(256 - 64*k - 64) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [h2, Nat.mod_mul_right_mod]

-- ============================================================================
-- Limb 0: (a*b).getLimb 0 = a0 * b0
-- ============================================================================

theorem mul_correct_limb0 (a b : EvmWord) :
    (a * b).getLimb 0 = a.getLimb 0 * b.getLimb 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [getLimb, BitVec.extractLsb'_toNat, BitVec.toNat_mul, Nat.shiftRight_eq_div_pow]
  norm_num

-- ============================================================================
-- Limb 1: (a*b).getLimb 1 = c0_r1 + c1_lo
-- where c0_r1 = rv64_mulhu a0 b0 + a1 * b0
-- c1_lo = a0 * b1
-- ============================================================================
theorem mul_correct_limb1 (a b : EvmWord) :
    let a0 := a.getLimb 0; let a1 := a.getLimb 1
    let b0 := b.getLimb 0; let b1 := b.getLimb 1
    let c0_hi_a0b0 := rv64_mulhu a0 b0
    let c0_lo_a1b0 := a1 * b0
    let c0_r1 := c0_hi_a0b0 + c0_lo_a1b0
    let c1_lo := a0 * b1
    let c1_r1 := c0_r1 + c1_lo
    (a * b).getLimb 1 = c1_r1 := by
  refine' BitVec.eq_of_toNat_eq _;
  convert limb_mod_div_cancel ( a.toNat * b.toNat ) 1 ( by decide ) using 1;
  · rw [ getLimb ];
    norm_num [ Nat.shiftRight_eq_div_pow ];
  · rw [ toNat_eq_limb_sum a, toNat_eq_limb_sum b ];
    norm_num [ BitVec.toNat_add, BitVec.toNat_mul, rv64_mulhu_toNat, mul_toNat ];
    ring_nf;
    omega

-- ============================================================================
-- Limb 2
-- ============================================================================
theorem mul_correct_limb2 (a b : EvmWord) :
    let a0 := a.getLimb 0; let a1 := a.getLimb 1; let a2 := a.getLimb 2
    let b0 := b.getLimb 0; let b1 := b.getLimb 1; let b2 := b.getLimb 2
    let c0_hi_a0b0 := rv64_mulhu a0 b0
    let c0_lo_a1b0 := a1 * b0
    let c0_hi_a1b0 := rv64_mulhu a1 b0
    let c0_r1 := c0_hi_a0b0 + c0_lo_a1b0
    let c0_c1 := if BitVec.ult c0_r1 c0_lo_a1b0 then (1 : Word) else 0
    let c0_lo_a2b0 := a2 * b0
    let c0_r2 := c0_hi_a1b0 + c0_c1 + c0_lo_a2b0
    let c1_lo := a0 * b1
    let c1_hi := rv64_mulhu a0 b1
    let c1_r1 := c0_r1 + c1_lo
    let c1_c1 := if BitVec.ult c1_r1 c1_lo then (1 : Word) else 0
    let c1_rc := c1_hi + c1_c1
    let c1_r2a := c0_r2 + c1_rc
    let c1_lo2 := a1 * b1
    let c1_r2 := c1_r2a + c1_lo2
    let c2_lo := a0 * b2
    let c2_r2 := c1_r2 + c2_lo
    (a * b).getLimb 2 = c2_r2 := by
  refine' BitVec.eq_of_toNat_eq _;
  convert limb_mod_div_cancel ( a.toNat * b.toNat ) 2 ( by decide ) using 1;
  · unfold EvmWord.getLimb;
    norm_num [ Nat.shiftRight_eq_div_pow ];
  · rw [ toNat_eq_limb_sum a, toNat_eq_limb_sum b ];
    norm_num [ BitVec.toNat_add, BitVec.toNat_mul, rv64_mulhu_toNat, mul_toNat, carry_toNat ] ; ring_nf; omega;

-- ============================================================================
-- Limb 3 helpers
-- ============================================================================

/-- Recombine div/mod into a single linear equation: q*W + r = x.
    Used to convert nested div/mod pairs into flat linear constraints for omega. -/
private theorem div_mod_eq (W : Nat) {x q r : Nat} (hq : q = x / W) (hr : r = x % W) :
    q * W + r = x := by subst hq; subst hr; rw [Nat.mul_comm]; exact Nat.div_add_mod x W

/-- Mod-flattening: (a % W + b) % W = (a + b) % W for W = 2^64.
    Extracted so omega runs in a clean context (no let-defs). -/
private theorem mod_add_cancel_left (a b : Nat) :
    (a % 2^64 + b) % 2^64 = (a + b) % 2^64 := by omega

private theorem mod_add_cancel_right (a b : Nat) :
    (a + b % 2^64) % 2^64 = (a + b) % 2^64 := by omega

/-- 4×4 schoolbook product expansion into digit columns. Extracted so `ring`
    runs in its own heartbeat budget. -/
private theorem product_expansion (a0 a1 a2 a3 b0 b1 b2 b3 W : Nat) :
    (a0 + a1 * W + a2 * W^2 + a3 * W^3) * (b0 + b1 * W + b2 * W^2 + b3 * W^3) =
    a0*b0 + (a0*b1 + a1*b0) * W + (a0*b2 + a1*b1 + a2*b0) * W^2 +
    (a0*b3 + a1*b2 + a2*b1 + a3*b0) * W^3 +
    (a1*b3 + a2*b2 + a3*b1) * W^4 + (a2*b3 + a3*b2) * W^5 + a3*b3 * W^6 := by ring

/-- Geometric series: (W-1)(1+W+W²) + 1 = W³. Avoids Nat subtraction issues
    by using `1 + (W-1) = W` rewrites. -/
private theorem geo_series_identity (W : Nat) (hW : 0 < W) :
    (W - 1) + (W - 1) * W + (W - 1) * W ^ 2 + 1 = W ^ 3 := by
  have h1 : 1 + (W - 1) = W := by omega
  calc (W - 1) + (W - 1) * W + (W - 1) * W ^ 2 + 1
      = ((W - 1) + 1) + (W - 1) * W + (W - 1) * W ^ 2 := by ring
    _ = W + (W - 1) * W + (W - 1) * W ^ 2 := by rw [show (W - 1) + 1 = W from by omega]
    _ = W * (1 + (W - 1)) + (W - 1) * W ^ 2 := by ring
    _ = W * W + (W - 1) * W ^ 2 := by rw [h1]
    _ = W ^ 2 * (1 + (W - 1)) := by ring
    _ = W ^ 2 * W := by rw [h1]
    _ = W ^ 3 := by ring

/-- Carry telescoping: D0 + D1·W + D2·W² = (residues) + C3·W³.
    Extracted so `ring` sees plain parameters, not `set` definitions. -/
private theorem carry_telescoping (D0 D1 D2 C1 C2 C3 W : Nat)
    (h0 : W * C1 + D0 % W = D0)
    (h1 : W * C2 + (D1 + C1) % W = D1 + C1)
    (h2 : W * C3 + (D2 + C2) % W = D2 + C2) :
    D0 + D1 * W + D2 * W^2 =
    D0 % W + (D1 + C1) % W * W + (D2 + C2) % W * W^2 + C3 * W^3 := by
  have e1 : D1 + C1 = (D1 + C1) % W + W * C2 := by linarith [h1]
  have e2 : D2 + C2 = (D2 + C2) % W + W * C3 := by linarith [h2]
  calc D0 + D1 * W + D2 * W^2
      = (D0 % W + W * C1) + D1 * W + D2 * W^2      := by linarith [h0]
    _ = D0 % W + (D1 + C1) * W + D2 * W^2           := by ring
    _ = D0 % W + ((D1 + C1) % W + W * C2) * W + D2 * W^2 := by rw [← e1]
    _ = D0 % W + (D1 + C1) % W * W + (D2 + C2) * W^2    := by ring
    _ = D0 % W + (D1 + C1) % W * W + ((D2 + C2) % W + W * C3) * W^2 := by rw [← e2]
    _ = D0 % W + (D1 + C1) % W * W + (D2 + C2) % W * W^2 + C3 * W^3 := by ring

/-- Low part bound: sum of three remainder·weight terms < W³.
    Extracted so `omega` sees plain parameters, not `set` definitions. -/
private theorem low_part_bound (D0 D1C1 D2C2 W : Nat) (hW : 0 < W)
    (hm0 : D0 % W < W) (hm1 : D1C1 % W < W) (hm2 : D2C2 % W < W) :
    D0 % W + D1C1 % W * W + D2C2 % W * W^2 < W^3 := by
  have b0 : D0 % W ≤ W - 1 := by omega
  have b1 : D1C1 % W * W ≤ (W - 1) * W :=
    Nat.mul_le_mul_right W (by omega)
  have b2 : D2C2 % W * W ^ 2 ≤ (W - 1) * W ^ 2 :=
    Nat.mul_le_mul_right (W ^ 2) (by omega)
  have geo := geo_series_identity W hW
  linarith [b0, b1, b2, geo]

/-- Schoolbook identity: the full product divided at limb 3 equals (D3 + C3) mod W,
    where C3 is the cascading carry from lower columns. Proven structurally
    via carry telescoping (no omega on the full expression). -/
private theorem schoolbook_limb3 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    let P := (a0 + a1 * 2^64 + a2 * 2^128 + a3 * 2^192) *
             (b0 + b1 * 2^64 + b2 * 2^128 + b3 * 2^192)
    let D0 := a0 * b0
    let D1 := a0 * b1 + a1 * b0
    let D2 := a0 * b2 + a1 * b1 + a2 * b0
    let D3 := a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0
    let C1 := D0 / 2^64
    let C2 := (D1 + C1) / 2^64
    let C3 := (D2 + C2) / 2^64
    P / 2^192 % 2^64 = (D3 + C3) % 2^64 := by

  dsimp only
  set W := (2:Nat)^64
  have h128 : (2:Nat)^128 = W^2 := by norm_num [W]
  have h192 : (2:Nat)^192 = W^3 := by norm_num [W]
  rw [h128, h192]
  set D0 := a0 * b0
  set D1 := a0 * b1 + a1 * b0
  set D2 := a0 * b2 + a1 * b1 + a2 * b0
  set D3 := a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0
  set C1 := D0 / W
  set C2 := (D1 + C1) / W
  set C3 := (D2 + C2) / W
  set P := (a0 + a1 * W + a2 * W ^ 2 + a3 * W ^ 3) *
           (b0 + b1 * W + b2 * W ^ 2 + b3 * W ^ 3)

  have hP : P = D0 + D1 * W + D2 * W^2 + D3 * W^3 +
    (a1*b3 + a2*b2 + a3*b1) * W^4 + (a2*b3 + a3*b2) * W^5 + a3*b3 * W^6 := by
    simp only [P, D0, D1, D2, D3]
    exact product_expansion a0 a1 a2 a3 b0 b1 b2 b3 W

  have hW : (0:Nat) < W := by positivity
  have h_tel : D0 + D1 * W + D2 * W^2 =
      D0 % W + (D1 + C1) % W * W + (D2 + C2) % W * W^2 + C3 * W^3 :=
    carry_telescoping D0 D1 D2 C1 C2 C3 W
      (Nat.div_add_mod D0 W) (Nat.div_add_mod (D1 + C1) W) (Nat.div_add_mod (D2 + C2) W)

  have hlow : D0 % W + (D1 + C1) % W * W + (D2 + C2) % W * W^2 < W^3 :=
    low_part_bound D0 (D1 + C1) (D2 + C2) W hW
      (Nat.mod_lt D0 hW) (Nat.mod_lt (D1 + C1) hW) (Nat.mod_lt (D2 + C2) hW)

  set low := D0 % W + (D1 + C1) % W * W + (D2 + C2) % W * W^2
  set D4 := a1*b3 + a2*b2 + a3*b1
  set D5 := a2*b3 + a3*b2
  set D6 := a3*b3
  have hP2 : P = low + ((D3 + C3) + D4 * W + D5 * W^2 + D6 * W^3) * W^3 := by
    rw [hP, h_tel]; ring
  set high := (D3 + C3) + D4 * W + D5 * W^2 + D6 * W^3
  have hDiv : P / W^3 = high := by
    rw [hP2, Nat.add_mul_div_right _ _ (by positivity : (0:Nat) < W^3),
        Nat.div_eq_of_lt hlow, Nat.zero_add]
  rw [hDiv, show high = (D3 + C3) + (D4 + D5 * W + D6 * W^2) * W from by ring,
      Nat.add_mul_mod_self_right]

/-- Generic algebraic identity: `(a*W + b)/W = a + b/W`. -/
private theorem qC1_simp_helper (a b : ℕ) (hb : b < 2 ^ 64) :
    (a * 2 ^ 64 + b) / 2 ^ 64 = a := by omega

/-- Generic: `(a*W + b + (c*W + d) + e) / W = a + c + (b + d + e) / W`. -/
private theorem qC2_simp_helper (a b c d e : ℕ) :
    (a * 2 ^ 64 + b + (c * 2 ^ 64 + d) + e) / 2 ^ 64 = a + c + (b + d + e) / 2 ^ 64 := by omega

/-- Generic: `(a*W + b + (c*W + d) + (e*W + f) + (g + h + i)) / W = a + c + e + (b + d + f + g + h + i) / W`. -/
private theorem qC3_simp_helper (a b c d e f g h i : ℕ) :
    (a * 2 ^ 64 + b + (c * 2 ^ 64 + d) + (e * 2 ^ 64 + f) + (g + h + i)) / 2 ^ 64 =
    a + c + e + (b + d + f + g + h + i) / 2 ^ 64 := by omega

/-- After simp-flattening, the carry-chain mod equation reduces to this pure
    Nat identity. Proved in a clean context (no let-defs) so `generalize h :`
    and `omega` can flatten nested div/mod into linear constraints. -/
private theorem carry_chain_mod_eq
    (mu00 lo00 lo10 mu10 lo20 mu20 lo30
     lo01 mu01 lo11 mu11
     lo02 mu02 lo21 lo12 lo03 mu03 mu12 mu21 mu30 : Nat)
    -- Leaf bounds actually needed by omega (others are derivable)
    (hb_mu00 : mu00 < 2 ^ 64) (hb_lo00 : lo00 < 2 ^ 64)
    (hb_lo10 : lo10 < 2 ^ 64) (hb_mu10 : mu10 < 2 ^ 64)
    (hb_lo01 : lo01 < 2 ^ 64) (hb_mu01 : mu01 < 2 ^ 64)
    -- Product-consistency bounds (only the ones omega needs for the carry chain)
    (hp00 : mu00 * 2 ^ 64 + lo00 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (hp10 : mu10 * 2 ^ 64 + lo10 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (hp01 : mu01 * 2 ^ 64 + lo01 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) :
    (((mu10 + (mu00 + lo10) / 2 ^ 64 + lo20) % 2 ^ 64 +
       (mu01 + ((mu00 + lo10) % 2 ^ 64 + lo01) / 2 ^ 64) % 2 ^ 64) / 2 ^ 64 +
      (mu11 +
        ((mu10 + (mu00 + lo10) / 2 ^ 64 + lo20 +
          (mu01 + ((mu00 + lo10) % 2 ^ 64 + lo01) / 2 ^ 64)) % 2 ^ 64 +
         lo11) / 2 ^ 64) +
      lo21 +
      (mu20 + ((mu10 + (mu00 + lo10) / 2 ^ 64) % 2 ^ 64 + lo20) / 2 ^ 64 + lo30) +
      (mu02 +
        ((mu10 + (mu00 + lo10) / 2 ^ 64 + lo20 +
          (mu01 + ((mu00 + lo10) % 2 ^ 64 + lo01) / 2 ^ 64) + lo11) % 2 ^ 64 +
         lo02) / 2 ^ 64 +
       lo12) +
      lo03) % 2 ^ 64 =
    (mu03 * 2 ^ 64 + lo03 + (mu12 * 2 ^ 64 + lo12) +
      (mu21 * 2 ^ 64 + lo21) + (mu30 * 2 ^ 64 + lo30) +
      (mu02 * 2 ^ 64 + lo02 + (mu11 * 2 ^ 64 + lo11) +
        (mu20 * 2 ^ 64 + lo20) +
        (mu01 * 2 ^ 64 + lo01 + (mu10 * 2 ^ 64 + lo10) +
          (mu00 * 2 ^ 64 + lo00) / 2 ^ 64) / 2 ^ 64) / 2 ^ 64) % 2 ^ 64 := by
  -- Simplify RHS via generic helpers (each omega runs in clean top-level context)
  rw [qC1_simp_helper mu00 lo00 hb_lo00]
  rw [qC2_simp_helper mu01 lo01 mu10 lo10 mu00]
  rw [qC3_simp_helper mu02 lo02 mu11 lo11 mu20 lo20 mu01 mu10
        ((lo01 + lo10 + mu00) / 2 ^ 64)]
  -- RHS now has only 2 nested divs (was 3). Main omega closes the LHS-RHS equivalence.
  omega

/-- The carry chain implementation produces the correct column sum mod 2^64.
    This is the BitVec → Nat direction: all ult-carries become (x+y)/2^64. -/
private theorem carry_chain_limb3 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    let c0_hi_a0b0 := rv64_mulhu a0 b0
    let c0_lo_a1b0 := a1 * b0
    let c0_hi_a1b0 := rv64_mulhu a1 b0
    let c0_r1 := c0_hi_a0b0 + c0_lo_a1b0
    let c0_c1 := if BitVec.ult c0_r1 c0_lo_a1b0 then (1 : Word) else 0
    let c0_lo_a2b0 := a2 * b0
    let c0_hi_a2b0 := rv64_mulhu a2 b0
    let c0_r2 := c0_hi_a1b0 + c0_c1 + c0_lo_a2b0
    let c0_c2 := if BitVec.ult c0_r2 c0_lo_a2b0 then (1 : Word) else 0
    let c0_r3p := c0_hi_a2b0 + c0_c2 + a3 * b0
    let c1_lo := a0 * b1
    let c1_hi := rv64_mulhu a0 b1
    let c1_r1 := c0_r1 + c1_lo
    let c1_c1 := if BitVec.ult c1_r1 c1_lo then (1 : Word) else 0
    let c1_rc := c1_hi + c1_c1
    let c1_r2a := c0_r2 + c1_rc
    let c1_cr1 := if BitVec.ult c1_r2a c1_rc then (1 : Word) else 0
    let c1_lo2 := a1 * b1
    let c1_hi2 := rv64_mulhu a1 b1
    let c1_r2 := c1_r2a + c1_lo2
    let c1_cr2 := if BitVec.ult c1_r2 c1_lo2 then (1 : Word) else 0
    let c1_rc2 := c1_hi2 + c1_cr2
    let c1_r3p := c1_cr1 + c1_rc2 + a2 * b1 + c0_r3p
    let c2_lo := a0 * b2
    let c2_hi := rv64_mulhu a0 b2
    let c2_r2 := c1_r2 + c2_lo
    let c2_c := if BitVec.ult c2_r2 c2_lo then (1 : Word) else 0
    let c2_rc := c2_hi + c2_c + a1 * b2
    let c2_r3 := c1_r3p + c2_rc
    let r3_final := c2_r3 + a0 * b3
    let D0 := a0.toNat * b0.toNat
    let D1 := a0.toNat * b1.toNat + a1.toNat * b0.toNat
    let D2 := a0.toNat * b2.toNat + a1.toNat * b1.toNat + a2.toNat * b0.toNat
    let D3 := a0.toNat * b3.toNat + a1.toNat * b2.toNat + a2.toNat * b1.toNat + a3.toNat * b0.toNat
    let C1 := D0 / 2^64
    let C2 := (D1 + C1) / 2^64
    let C3 := (D2 + C2) / 2^64
    r3_final.toNat = (D3 + C3) % 2^64 := by
  -- Bring all let-bindings into the local context as named definitions
  intro c0_hi_a0b0 c0_lo_a1b0 c0_hi_a1b0 c0_r1 c0_c1 c0_lo_a2b0 c0_hi_a2b0 c0_r2 c0_c2 c0_r3p
        c1_lo c1_hi c1_r1 c1_c1 c1_rc c1_r2a c1_cr1 c1_lo2 c1_hi2 c1_r2 c1_cr2 c1_rc2 c1_r3p
        c2_lo c2_hi c2_r2 c2_c c2_rc c2_r3 r3_final
        D0 D1 D2 D3 C1 C2 C3
  -- Phase 2: col0 carry chain
  have h_c0_r1 : c0_r1.toNat = ((rv64_mulhu a0 b0).toNat + (a1 * b0).toNat) % 2^64 :=
    BitVec.toNat_add (rv64_mulhu a0 b0) (a1 * b0)
  have h_c0_c1 : c0_c1.toNat = ((rv64_mulhu a0 b0).toNat + (a1 * b0).toNat) / 2^64 :=
    carry_toNat
  -- expand inner sums so omega sees them, not opaque atoms
  have h_sum10_c1 : (rv64_mulhu a1 b0 + c0_c1).toNat =
      ((rv64_mulhu a1 b0).toNat + c0_c1.toNat) % 2^64 :=
    BitVec.toNat_add (rv64_mulhu a1 b0) c0_c1
  have h_c0_r2 : c0_r2.toNat = ((rv64_mulhu a1 b0 + c0_c1).toNat + (a2 * b0).toNat) % 2^64 :=
    BitVec.toNat_add (rv64_mulhu a1 b0 + c0_c1) (a2 * b0)
  have h_c0_c2 : c0_c2.toNat = ((rv64_mulhu a1 b0 + c0_c1).toNat + (a2 * b0).toNat) / 2^64 :=
    carry_toNat
  -- c0_r3p = c0_hi_a2b0 + c0_c2 + a3 * b0
  have h_sum20_c2 : (rv64_mulhu a2 b0 + c0_c2).toNat =
      ((rv64_mulhu a2 b0).toNat + c0_c2.toNat) % 2^64 :=
    BitVec.toNat_add (rv64_mulhu a2 b0) c0_c2
  have h_c0_r3p : c0_r3p.toNat = ((rv64_mulhu a2 b0 + c0_c2).toNat + (a3 * b0).toNat) % 2^64 :=
    BitVec.toNat_add (rv64_mulhu a2 b0 + c0_c2) (a3 * b0)
  -- Phase 3: col1 r1/c1 carries
  have h_c1_c1 : c1_c1.toNat = (c0_r1.toNat + (a0 * b1).toNat) / 2^64 :=
    carry_toNat
  -- c1_rc = c1_hi + c1_c1 = rv64_mulhu a0 b1 + c1_c1
  have h_c1_rc : c1_rc.toNat = ((rv64_mulhu a0 b1).toNat + c1_c1.toNat) % 2^64 :=
    BitVec.toNat_add (rv64_mulhu a0 b1) c1_c1
  -- c1_r2a = c0_r2 + c1_rc
  have h_c1_r2a : c1_r2a.toNat = (c0_r2.toNat + c1_rc.toNat) % 2^64 :=
    BitVec.toNat_add c0_r2 c1_rc
  have h_c1_cr1 : c1_cr1.toNat = (c0_r2.toNat + c1_rc.toNat) / 2^64 :=
    carry_toNat
  -- c1_r2 = c1_r2a + c1_lo2 = c1_r2a + a1 * b1
  have h_c1_r2 : c1_r2.toNat = (c1_r2a.toNat + (a1 * b1).toNat) % 2^64 :=
    BitVec.toNat_add c1_r2a (a1 * b1)
  have h_c1_cr2 : c1_cr2.toNat = (c1_r2a.toNat + (a1 * b1).toNat) / 2^64 :=
    carry_toNat
  -- c1_rc2 = c1_hi2 + c1_cr2 = rv64_mulhu a1 b1 + c1_cr2
  have h_c1_rc2 : c1_rc2.toNat = ((rv64_mulhu a1 b1).toNat + c1_cr2.toNat) % 2^64 :=
    BitVec.toNat_add (rv64_mulhu a1 b1) c1_cr2
  -- c1_r3p outer split
  have h_c1_r3p : c1_r3p.toNat = ((c1_cr1 + c1_rc2 + a2 * b1).toNat + c0_r3p.toNat) % 2^64 :=
    BitVec.toNat_add (c1_cr1 + c1_rc2 + a2 * b1) c0_r3p
  -- expand the inner 3-way sum
  have h_c1_inner : (c1_cr1 + c1_rc2 + a2 * b1).toNat =
      ((c1_cr1 + c1_rc2).toNat + (a2 * b1).toNat) % 2^64 :=
    BitVec.toNat_add (c1_cr1 + c1_rc2) (a2 * b1)
  have h_c1_cr1rc2 : (c1_cr1 + c1_rc2).toNat = (c1_cr1.toNat + c1_rc2.toNat) % 2^64 :=
    BitVec.toNat_add c1_cr1 c1_rc2
  -- col2 carry chain
  have h_c2_c : c2_c.toNat = (c1_r2.toNat + (a0 * b2).toNat) / 2^64 :=
    carry_toNat
  have h_c2_rc_inner : (rv64_mulhu a0 b2 + c2_c).toNat = ((rv64_mulhu a0 b2).toNat + c2_c.toNat) % 2^64 :=
    BitVec.toNat_add (rv64_mulhu a0 b2) c2_c
  have h_c2_rc : c2_rc.toNat = ((rv64_mulhu a0 b2 + c2_c).toNat + (a1 * b2).toNat) % 2^64 :=
    BitVec.toNat_add (rv64_mulhu a0 b2 + c2_c) (a1 * b2)
  have h_c2_r3 : c2_r3.toNat = (c1_r3p.toNat + c2_rc.toNat) % 2^64 :=
    BitVec.toNat_add c1_r3p c2_rc
  -- col3: r3_final = c2_r3 + a0 * b3
  have h_r3 : r3_final.toNat = (c2_r3.toNat + (a0 * b3).toNat) % 2^64 :=
    BitVec.toNat_add c2_r3 (a0 * b3)
  -- Euclidean approach: convert every div/mod pair into carry*W + result = inputs
  -- so the final omega sees only LINEAR equations (no nested div/mod).
  -- Leaf full products (mulhu * W + mul_lo = product)
  have fp00 := mul_full_product a0 b0
  have fp10 := mul_full_product a1 b0
  have fp20 := mul_full_product a2 b0
  have fp01 := mul_full_product a0 b1
  have fp11 := mul_full_product a1 b1
  have fp02 := mul_full_product a0 b2
  have fp30 := mul_full_product a3 b0
  have fp21 := mul_full_product a2 b1
  have fp12 := mul_full_product a1 b2
  have fp03 := mul_full_product a0 b3
  -- RHS: express D_k in terms of full products (eliminates nonlinear a_i*b_j)
  have hD0 : D0 = (rv64_mulhu a0 b0).toNat * 2^64 + (a0 * b0).toNat := fp00.symm
  have hD1 : D1 = (rv64_mulhu a0 b1).toNat * 2^64 + (a0 * b1).toNat +
      ((rv64_mulhu a1 b0).toNat * 2^64 + (a1 * b0).toNat) :=
    congrArg₂ (· + ·) fp01.symm fp10.symm
  have hD2 : D2 = (rv64_mulhu a0 b2).toNat * 2^64 + (a0 * b2).toNat +
      ((rv64_mulhu a1 b1).toNat * 2^64 + (a1 * b1).toNat) +
      ((rv64_mulhu a2 b0).toNat * 2^64 + (a2 * b0).toNat) :=
    congrArg₂ (· + ·) (congrArg₂ (· + ·) fp02.symm fp11.symm) fp20.symm
  have hD3 : D3 = (rv64_mulhu a0 b3).toNat * 2^64 + (a0 * b3).toNat +
      ((rv64_mulhu a1 b2).toNat * 2^64 + (a1 * b2).toNat) +
      ((rv64_mulhu a2 b1).toNat * 2^64 + (a2 * b1).toNat) +
      ((rv64_mulhu a3 b0).toNat * 2^64 + (a3 * b0).toNat) :=
    congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) fp03.symm fp12.symm) fp21.symm) fp30.symm
  -- All equations are now linear. Reduce to mod-congruence, then extract to private lemma.
  -- Step 1: r3_final.toNat = (sum) % W, so suffices to show (sum) % W = (D3+C3) % W
  have h_suffices : (c2_r3.toNat + (a0 * b3).toNat) % 2^64 = (D3 + C3) % 2^64 := by
    -- Unfold C/D let-defs (rfl-based, safe in this context)
    have hC3_def : C3 = (D2 + C2) / 2^64 := rfl
    have hC2_def : C2 = (D1 + C1) / 2^64 := rfl
    have hC1_def : C1 = D0 / 2^64 := rfl
    -- simp only on goal: expand all .toNat, flatten nested %, expand RHS
    simp only [
      h_c2_r3, h_c2_rc, h_c2_rc_inner, h_c1_r3p, h_c1_inner, h_c1_cr1rc2,
      h_c1_rc2, h_c0_r3p, h_sum20_c2, h_c1_cr1, h_c1_cr2, h_c2_c, h_c0_c2,
      h_c0_r2, h_c1_r2a, h_c1_r2, h_sum10_c1, h_c1_rc, h_c1_c1,
      h_c0_r1, h_c0_c1,
      mod_add_cancel_left, mod_add_cancel_right,
      hC3_def, hC2_def, hC1_def, hD3, hD2, hD1, hD0]
    -- Apply private theorem directly with .toNat values; bounds from BitVec.isLt
    -- Product bounds: each full product = a.toNat * b.toNat ≤ (2^64-1)*(2^64-1)
    have prod_bound : ∀ (x y : Word),
        (rv64_mulhu x y).toNat * 2^64 + (x * y).toNat ≤ (2^64 - 1) * (2^64 - 1) := by
      intro x y
      rw [mul_full_product x y]
      exact Nat.mul_le_mul (by have := x.isLt; omega) (by have := y.isLt; omega)
    exact carry_chain_mod_eq
      (rv64_mulhu a0 b0).toNat (a0 * b0).toNat (a1 * b0).toNat (rv64_mulhu a1 b0).toNat
      (a2 * b0).toNat (rv64_mulhu a2 b0).toNat (a3 * b0).toNat
      (a0 * b1).toNat (rv64_mulhu a0 b1).toNat (a1 * b1).toNat (rv64_mulhu a1 b1).toNat
      (a0 * b2).toNat (rv64_mulhu a0 b2).toNat (a2 * b1).toNat (a1 * b2).toNat
      (a0 * b3).toNat (rv64_mulhu a0 b3).toNat (rv64_mulhu a1 b2).toNat
      (rv64_mulhu a2 b1).toNat (rv64_mulhu a3 b0).toNat
      (rv64_mulhu a0 b0).isLt (a0 * b0).isLt (a1 * b0).isLt (rv64_mulhu a1 b0).isLt
      (a0 * b1).isLt (rv64_mulhu a0 b1).isLt
      (prod_bound a0 b0) (prod_bound a1 b0) (prod_bound a0 b1)
  exact h_r3.trans h_suffices

-- ============================================================================
-- Limb 3
-- ============================================================================

theorem mul_correct_limb3 (a b : EvmWord) :
    let a0 := a.getLimb 0; let a1 := a.getLimb 1; let a2 := a.getLimb 2; let a3 := a.getLimb 3
    let b0 := b.getLimb 0; let b1 := b.getLimb 1; let b2 := b.getLimb 2; let b3 := b.getLimb 3
    let c0_hi_a0b0 := rv64_mulhu a0 b0
    let c0_lo_a1b0 := a1 * b0
    let c0_hi_a1b0 := rv64_mulhu a1 b0
    let c0_r1 := c0_hi_a0b0 + c0_lo_a1b0
    let c0_c1 := if BitVec.ult c0_r1 c0_lo_a1b0 then (1 : Word) else 0
    let c0_lo_a2b0 := a2 * b0
    let c0_hi_a2b0 := rv64_mulhu a2 b0
    let c0_r2 := c0_hi_a1b0 + c0_c1 + c0_lo_a2b0
    let c0_c2 := if BitVec.ult c0_r2 c0_lo_a2b0 then (1 : Word) else 0
    let c0_r3p := c0_hi_a2b0 + c0_c2 + a3 * b0
    let c1_lo := a0 * b1
    let c1_hi := rv64_mulhu a0 b1
    let c1_r1 := c0_r1 + c1_lo
    let c1_c1 := if BitVec.ult c1_r1 c1_lo then (1 : Word) else 0
    let c1_rc := c1_hi + c1_c1
    let c1_r2a := c0_r2 + c1_rc
    let c1_cr1 := if BitVec.ult c1_r2a c1_rc then (1 : Word) else 0
    let c1_lo2 := a1 * b1
    let c1_hi2 := rv64_mulhu a1 b1
    let c1_r2 := c1_r2a + c1_lo2
    let c1_cr2 := if BitVec.ult c1_r2 c1_lo2 then (1 : Word) else 0
    let c1_rc2 := c1_hi2 + c1_cr2
    let c1_r3p := c1_cr1 + c1_rc2 + a2 * b1 + c0_r3p
    let c2_lo := a0 * b2
    let c2_hi := rv64_mulhu a0 b2
    let c2_r2 := c1_r2 + c2_lo
    let c2_c := if BitVec.ult c2_r2 c2_lo then (1 : Word) else 0
    let c2_rc := c2_hi + c2_c + a1 * b2
    let c2_r3 := c1_r3p + c2_rc
    let r3_final := c2_r3 + a0 * b3
    (a * b).getLimb 3 = r3_final := by
  -- Bring the signature's let-bindings into scope
  intro a0 a1 a2 a3 b0 b1 b2 b3
        c0_hi_a0b0 c0_lo_a1b0 c0_hi_a1b0 c0_r1 c0_c1 c0_lo_a2b0 c0_hi_a2b0 c0_r2 c0_c2 c0_r3p
        c1_lo c1_hi c1_r1 c1_c1 c1_rc c1_r2a c1_cr1 c1_lo2 c1_hi2 c1_r2 c1_cr2 c1_rc2 c1_r3p
        c2_lo c2_hi c2_r2 c2_c c2_rc c2_r3 r3_final
  apply BitVec.eq_of_toNat_eq
  -- Step 1: LHS = P / 2^192 % 2^64
  have hLHS : ((a * b).getLimb 3).toNat =
      (a.toNat * b.toNat) / 2^192 % 2^64 := by
    simp only [getLimb, BitVec.extractLsb'_toNat, BitVec.toNat_mul, Nat.shiftRight_eq_div_pow]
    -- `↑3 * 64` and `64 * 3` are defEq (both = 192) so `exact` closes via defEq matching
    exact limb_mod_div_cancel (a.toNat * b.toNat) 3 (by decide)
  -- Step 2: RHS = (D3 + C3) % 2^64 via carry chain
  have hRHS := carry_chain_limb3 a0 a1 a2 a3 b0 b1 b2 b3
  -- Step 3: P / 2^192 % 2^64 = (D3 + C3) % 2^64 via schoolbook
  have hSB := schoolbook_limb3
    a0.toNat a1.toNat a2.toNat a3.toNat b0.toNat b1.toNat b2.toNat b3.toNat
  -- Combine: LHS = P/W³%W = (D3+C3)%W = RHS
  rw [hLHS, toNat_eq_limb_sum a, toNat_eq_limb_sum b]
  dsimp only at hSB
  rw [hSB]
  exact hRHS.symm

-- ============================================================================
-- Main theorem combining all four limbs
-- ============================================================================

theorem mul_correct (a b : EvmWord):
    let a0 := a.getLimb 0; let a1 := a.getLimb 1; let a2 := a.getLimb 2; let a3 := a.getLimb 3;
    let b0 := b.getLimb 0; let b1 := b.getLimb 1; let b2 := b.getLimb 2; let b3 := b.getLimb 3;
    -- Col0 intermediates
    let c0_r0 := a0 * b0
    let c0_hi_a0b0 := rv64_mulhu a0 b0
    let c0_lo_a1b0 := a1 * b0
    let c0_hi_a1b0 := rv64_mulhu a1 b0
    let c0_r1 := c0_hi_a0b0 + c0_lo_a1b0
    let c0_c1 := if BitVec.ult c0_r1 c0_lo_a1b0 then (1 : Word) else 0
    let c0_lo_a2b0 := a2 * b0
    let c0_hi_a2b0 := rv64_mulhu a2 b0
    let c0_r2 := c0_hi_a1b0 + c0_c1 + c0_lo_a2b0
    let c0_c2 := if BitVec.ult c0_r2 c0_lo_a2b0 then (1 : Word) else 0
    let c0_r3p := c0_hi_a2b0 + c0_c2 + a3 * b0
    -- Col1 intermediates
    let c1_lo := a0 * b1
    let c1_hi := rv64_mulhu a0 b1
    let c1_r1 := c0_r1 + c1_lo
    let c1_c1 := if BitVec.ult c1_r1 c1_lo then (1 : Word) else 0
    let c1_rc := c1_hi + c1_c1
    let c1_r2a := c0_r2 + c1_rc
    let c1_cr1 := if BitVec.ult c1_r2a c1_rc then (1 : Word) else 0
    let c1_lo2 := a1 * b1
    let c1_hi2 := rv64_mulhu a1 b1
    let c1_r2 := c1_r2a + c1_lo2
    let c1_cr2 := if BitVec.ult c1_r2 c1_lo2 then (1 : Word) else 0
    let c1_rc2 := c1_hi2 + c1_cr2
    let c1_r3p := c1_cr1 + c1_rc2 + a2 * b1 + c0_r3p
    -- Col2 intermediates
    let c2_lo := a0 * b2
    let c2_hi := rv64_mulhu a0 b2
    let c2_r2 := c1_r2 + c2_lo
    let c2_c := if BitVec.ult c2_r2 c2_lo then (1 : Word) else 0
    let c2_rc := c2_hi + c2_c + a1 * b2
    let c2_r3 := c1_r3p + c2_rc
    -- Col3
    let r3_final := c2_r3 + a0 * b3
    (a * b).getLimb 0 = c0_r0 ∧
    (a * b).getLimb 1 = c1_r1 ∧
    (a * b).getLimb 2 = c2_r2 ∧
    (a * b).getLimb 3 = r3_final := by
  exact ⟨mul_correct_limb0 a b, mul_correct_limb1 a b, mul_correct_limb2 a b, mul_correct_limb3 a b⟩


end EvmWord

end EvmAsm.Evm64
