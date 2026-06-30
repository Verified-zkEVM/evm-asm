/-
  EvmAsm.Rv64.Tactics.WPAttr

  Declares the `rv64_wp` simp set used by `wp_rv64_link` to expose
  WP-calculator handoff shapes before separation-frame permutation.
-/

import Lean.Meta.Tactic.Simp.RegisterCommand

/-- Simp set for WP-generated handoff definitions.  Keep this focused on small
    assertion-shape definitions that make adjacent CFG fragments line up. -/
register_simp_attr rv64_wp
