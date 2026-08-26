/-
  EvmAsm.Evm64.DivMod.Spec.N4QOutConservationGen

  U4-general n=4 v5 call-addback value conservation:
    `UNormValV5 = QOutV5·BNormVal + IterRNormValV5`
  for ANY `U4` (no `U4 = 0`), given the borrow/carry2 runtime conditions and
  `qHat ≥ 2`.

  This is the U4-general counterpart of `n4CallAddbackBeqQOutV5_conservation_compact`
  (CallAddbackRuntimeV5), which routes through the `U4 = 0`-only `+1` `hq_over`.
  Here we instantiate the U4-general iterate conservation
  `iterWithDoubleAddback_val256_conservation_gen` (#7653) to the n=4 call forms,
  discharging its premises:
  * `hc3_of_borrow` via `n4CallAddbackBeq_c3_eq_uTop_plus_one_of_borrow` (#7656),
  * the second-carry predicate via `n4CallAddbackBeqCarry2Nz_of_runtimeV5`,
  * `uTop` no-wrap via `n4CallAddbackBeqU4_lt_pow63_of_shift_nz`;
  then folding `(iterWithDoubleAddback …).1 = QOutV5` via
  `n4CallAddbackBeqIterWithDoubleAddback_qOutV5_of_runtime_borrow`.

  `qHat ≥ 2` is taken as a hypothesis (it holds on the U4 ≥ 1 addback path; the
  U4 = 0 path is handled by the existing `qHat ≤ 1` chain).
  Bead `evm-asm-wbc4i.8.2.2`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N4C3EqUTopPlusOne
public import EvmAsm.Evm64.EvmWordArith.DivN4IterConservationGen
public import EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntimeV5

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- U4-general n=4 call-addback value conservation, from the U4-general iterate
    conservation (#7653) instantiated to the n=4 call forms. -/
theorem n4CallAddbackBeqQOutV5_conservation_compact_gen {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (h_borrow : isAddbackBorrowN4CallV5Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV5Evm a b)
    (hq_ge_2 : 2 ≤ (n4CallAddbackBeqQHatV5 a b).toNat) :
    n4CallAddbackBeqUNormValV5 a b =
      (n4CallAddbackBeqQOutV5 a b).toNat * n4CallAddbackBeqBNormVal b +
        n4CallAddbackBeqIterRNormValV5 a b := by
  have huTop : (n4CallAddbackBeqU4 a b).toNat + 1 < 2 ^ 64 := by
    have := n4CallAddbackBeqU4_lt_pow63_of_shift_nz (a := a) hshift_nz; omega
  have hconsv := iterWithDoubleAddback_val256_conservation_gen
    (n4CallAddbackBeqQHatV5 a b)
    (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
    (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
    (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
    (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)
    (n4CallAddbackBeqU4 a b) huTop
    (n4CallAddbackBeq_c3_eq_uTop_plus_one_of_borrow hb3nz hshift_nz hcall)
    (n4CallAddbackBeqCarry2Nz_of_runtimeV5 h_carry2)
    hq_ge_2
  simp only [] at hconsv
  rw [n4CallAddbackBeqIterWithDoubleAddback_qOutV5_of_runtime_borrow h_borrow] at hconsv
  unfold n4CallAddbackBeqUNormValV5 n4CallAddbackBeqBNormVal n4CallAddbackBeqIterRNormValV5
    n4CallAddbackBeqIterOutV5
  linarith [hconsv]

end EvmAsm.Evm64
