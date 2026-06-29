/-
  EvmAsm.Rv64.Tactics.WP

  Thin tactic surface for WP/CFG certificates.  The proof search/calculation
  lives in the certificate constructors; this tactic consumes the resulting
  object and closes the corresponding CPS goal.
-/

import Lean
import EvmAsm.Rv64.WP.CFG

namespace EvmAsm.Rv64.Tactics

open Lean Elab Tactic

/-- Close a `cpsTripleWithin` goal with a `WP.Triple`/`WP.CFG.Cert`.

    Example:
    ```
    wp_rv64 myCfg
    ```
    elaborates to `exact myCfg.sound`. -/
syntax (name := wpRv64Tac) "wp_rv64 " term : tactic

macro_rules
  | `(tactic| wp_rv64 $cfg:term) =>
      `(tactic| exact ($cfg).sound)

/-- Display the computed precondition field of a WP/CFG certificate. -/
syntax (name := wpRv64Cmd) "#wp_rv64 " term : command

macro_rules
  | `(#wp_rv64 $cfg:term) =>
      `(#check ($cfg).pre)

end EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64.Tactics.WPTests

open EvmAsm.Rv64

example {entry exit_ : Word} {cr : CodeReq} {post : Assertion}
    (cfg : EvmAsm.Rv64.WP.Triple entry exit_ cr post) :
    cpsTripleWithin cfg.nSteps entry exit_ cr cfg.pre post := by
  wp_rv64 cfg

end EvmAsm.Rv64.Tactics.WPTests
