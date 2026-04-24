/-
  EvmAsm.Evm64.DivMod.LoopDefs

  Backwards-compatible hub that re-exports the three split sub-files:
    * `LoopDefs.Iter` — pure Word/Prop-level computations and predicates
    * `LoopDefs.Post` — Assertion-valued postcondition defs
    * `LoopDefs.Bundle` — Assertion-valued precondition bundles

  Existing downstream modules `import EvmAsm.Evm64.DivMod.LoopDefs` and see
  the same names as before; the split is purely for build parallelism and
  editor responsiveness (issue #312).
-/

-- `Post` transitively imports `Iter`.
import EvmAsm.Evm64.DivMod.LoopDefs.Post
import EvmAsm.Evm64.DivMod.LoopDefs.Bundle
