/-
  EvmAsm.Evm64.EvmWordArith.DivN4Carry2C3UTopPlusOne

  U4-general double-addback progress bridge: under the val256 `+2` overestimate
  against the FULL five-limb dividend and the first-addback-zero branch forcing
  `c3 = uTop + 1`, the `isAddbackCarry2Nz` predicate holds.

  U4-general counterpart of `isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero`
  (DivN4Overestimate), which is `c3 = 1` / `U4 = 0`-specific.  Same structure, but
  routed through the generalised second-carry lemma `addbackN4_second_carry_one_gen`
  (#7662).  Bead `evm-asm-wbc4i.8.2.2`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN4SecondCarryGen

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- U4-general: `isAddbackCarry2Nz` from the full-dividend `+2` overestimate and
    `c3 = uTop + 1` on the first-addback-zero branch. -/
theorem isAddbackCarry2Nz_of_overestimate_c3_uTop_plus_one_of_carry_zero
    (q v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : q.toNat ≤
      (uTop.toNat * 2 ^ 256 + val256 u0 u1 u2 u3) / val256 v0 v1 v2 v3 + 2)
    (hc3_of_carry_zero :
      addbackN4_carry
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
        v0 v1 v2 v3 = 0 →
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = uTop.toNat + 1) :
    isAddbackCarry2Nz q v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  dsimp [isAddbackCarry2Nz]
  intro hcarry_zero
  let ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3
  let abTop := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
    (uTop - ms.2.2.2.2) v0 v1 v2 v3
  let abZero := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
    0 v0 v1 v2 v3
  have hc3 : ms.2.2.2.2.toNat = uTop.toNat + 1 := by
    subst ms
    exact hc3_of_carry_zero hcarry_zero
  have hsecond := addbackN4_second_carry_one_gen q v0 v1 v2 v3 u0 u1 u2 u3 uTop
    hbnz hq_over hc3 hcarry_zero
  simp only [] at hsecond
  have h_indep := addbackN4_fst4_u4_indep
    ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
    (uTop - ms.2.2.2.2) 0 v0 v1 v2 v3
  rcases h_indep with ⟨h0, h1, h2, h3⟩
  have hsecond_top :
      (addbackN4_carry abTop.1 abTop.2.1 abTop.2.2.1 abTop.2.2.2.1
        v0 v1 v2 v3).toNat = 1 := by
    rw [h0, h1, h2, h3]
    exact hsecond
  intro hzero
  rw [hzero] at hsecond_top
  norm_num at hsecond_top

end EvmAsm.Evm64
