/-
  EvmAsm.Evm64.EvmWordLimbAttr

  Declares the `evmword_limb` simp set used for `EvmWord` limb algebra
  (`getLimb` / `fromLimbs` / `getLimbN` round-trips and the bitwise-op
  distribution lemmas).

  Split into its own file because Lean 4 does not allow a simp attribute to be
  used in the file that declares it; `Evm64/Basic.lean` imports this file and
  tags the limb lemmas `@[evmword_limb, grind =]`. Downstream proofs can then
  normalize limb expressions with `simp [evmword_limb]`, and `grind` discovers
  the same round-trips via the `@[grind =]` E-matching patterns.
-/

import Lean.Meta.Tactic.Simp.RegisterCommand

/-- Simp set for `EvmWord` limb algebra: `(fromLimbs f).getLimb i = f i`,
    `fromLimbs (v.getLimb) = v`, and `getLimb` distributing over `&&&`/`|||`/
    `^^^`/`~~~`. The same lemmas are also `@[grind =]`. -/
register_simp_attr evmword_limb
