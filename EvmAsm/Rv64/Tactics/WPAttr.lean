/-
  EvmAsm.Rv64.Tactics.WPAttr

  Declares the `rv64_wp` simp set used by `wp_rv64_link` to expose
  WP-calculator handoff shapes before separation-frame permutation.
-/

import Lean.Meta.Tactic.Simp.RegisterCommand

namespace EvmAsm.Rv64.Tactics

/-- Simp set for WP-generated handoff definitions.  Keep this focused on small
    assertion-shape definitions that make adjacent CFG fragments line up. -/
register_simp_attr rv64_wp

/-- Environment extension storing the theorem names tagged with
    `@[rv64_wp_entails]`, in registration order. -/
initialize rv64WpEntailsExt : Lean.SimplePersistentEnvExtension Lean.Name (Array Lean.Name) ←
  Lean.registerSimplePersistentEnvExtension {
    addEntryFn := fun state declName => state.push declName
    addImportedFn := fun entries => entries.foldl (init := #[]) fun acc es => acc ++ es
  }

/-- Entailment hint database used by `wp_rv64_link` after WP preconditions have
    been simplified with `rv64_wp`.  Theorems tagged here should have target
    type `WP.Entails P Q`, with all arguments inferable from the goal. -/
initialize Lean.registerBuiltinAttribute {
  name := `rv64_wp_entails
  descr := "WP entailment hints used by wp_rv64_link"
  applicationTime := .afterTypeChecking
  add := fun declName stx _attrKind => do
    Lean.Attribute.Builtin.ensureNoArgs stx
    Lean.modifyEnv fun env => rv64WpEntailsExt.addEntry env declName
}

end EvmAsm.Rv64.Tactics
