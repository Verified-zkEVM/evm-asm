/-
  EvmAsm.Rv32.Tactics.LiftSpec

  Tactic for lifting limb-level cpsTriple specs to stack-level goals.

  ## Usage

  ```
  have h_main := evm_and_spec sp base (a.getLimb 0) ... hvalid
  liftSpec h_main post_simp [EvmWord.getLimb_and]
  ```

  ## What It Does

  1. The goal should be `cpsTriple entry exit goalPre goalPost`
  2. `h_main` should be `cpsTriple entry exit mainPre mainPost`
  3. Applies `cpsTriple_consequence` with `h_main`
  4. In the pre/post lambdas: unfolds `evmWordIs`/`evmStackIs`, normalizes
     addresses via `BitVec.add_assoc`, then permutes via `xperm_hyp`
-/

import EvmAsm.Rv32.Tactics.RunBlock
import EvmAsm.Evm32.Stack

namespace EvmAsm.Tactics

open Lean Elab Tactic

/-- Normalize BitVec address arithmetic: `(a + b) + c → a + (b + c)`.
    Uses `BitVec.add_assoc` for reassociation. Literal sums like `32 + 4`
    are definitionally equal to `36`, so no further reduction is needed. -/
syntax "norm_addr" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| norm_addr) =>
    `(tactic| try simp only [BitVec.add_assoc])
  | `(tactic| norm_addr $loc) =>
    `(tactic| try simp only [BitVec.add_assoc] $loc)

/-- `liftSpec h` lifts a limb-level cpsTriple spec `h` to a stack-level goal by
    unfolding `evmWordIs`/`evmStackIs`, normalizing addresses, and permuting.
    Optional `post_simp [lemmas]` applies additional simp lemmas to the postcondition
    (e.g., `EvmWord.getLimb_and` to push operations through limb extraction). -/
syntax "liftSpec" ident ("post_simp" "[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| liftSpec $h) =>
    `(tactic|
      exact cpsTriple_consequence _ _ _ _ _ _ _
        (fun _h _hp => by
          simp only [evmWordIs, evmStackIs, evmStackIs_cons, evmStackIs_nil] at _hp
          norm_addr at _hp
          xperm_hyp _hp)
        (fun _h _hq => by
          simp only [evmWordIs, evmStackIs, evmStackIs_cons, evmStackIs_nil]
          norm_addr
          xperm_hyp _hq)
        $h)
  | `(tactic| liftSpec $h post_simp [$lemmas,*]) =>
    `(tactic|
      exact cpsTriple_consequence _ _ _ _ _ _ _
        (fun _h _hp => by
          simp only [evmWordIs, evmStackIs, evmStackIs_cons, evmStackIs_nil] at _hp
          norm_addr at _hp
          xperm_hyp _hp)
        (fun _h _hq => by
          simp only [evmWordIs, evmStackIs, evmStackIs_cons, evmStackIs_nil, $lemmas,*]
          norm_addr
          xperm_hyp _hq)
        $h)

end EvmAsm.Tactics
