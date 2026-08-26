/-
  EvmAsm.Rv64.Tactics.XPermChunked

  Opt-in surface for chunked sepConj permutation experiments.
-/

module

public import Lean
public import EvmAsm.Rv64.Tactics.XPerm
meta import Lean
meta import EvmAsm.Rv64.Tactics.XPerm

@[expose] public section

open Lean Meta Elab Tactic

namespace EvmAsm.Rv64.Tactics

/--
`xperm_chunked h` has the same user-facing semantics as `xperm_hyp h`:
given `h : P s`, close a goal `Q s` when `P` and `Q` are sepConj
permutations.

This prototype is deliberately opt-in. It routes through the existing
proved permutation builder so call sites can migrate one at a time while
the chunk partition pre-pass evolves behind the same surface.
-/
macro "xperm_chunked" hyp:ident : tactic =>
  `(tactic| exact (congrFun (show _ = _ by xperm) _).mp $hyp)

/-- Debug spelling reserved by the chunked-xperm design. -/
macro "xperm_chunked" hyp:ident "only" : tactic =>
  `(tactic| exact (congrFun (show _ = _ by xperm) _).mp $hyp)

/-- Debug spelling reserved by the chunked-xperm design. -/
macro "xperm_chunked" hyp:ident "with" "strict" : tactic =>
  `(tactic| exact (congrFun (show _ = _ by xperm) _).mp $hyp)

end EvmAsm.Rv64.Tactics
