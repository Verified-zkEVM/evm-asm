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

/-- Environment extension storing theorem names tagged with `@[rv64_wp_dead]`.
    These are contradiction hints for unreachable WP exits. -/
initialize rv64WpDeadExt : Lean.SimplePersistentEnvExtension Lean.Name (Array Lean.Name) ←
  Lean.registerSimplePersistentEnvExtension {
    addEntryFn := fun state declName => state.push declName
    addImportedFn := fun entries => entries.foldl (init := #[]) fun acc es => acc ++ es
  }

/-- Dead-exit hint database used by `wp_rv64_dead`. Theorems tagged here should
    prove goals of shape `∀ h, P h → False`, with all non-target arguments
    inferable from local hypotheses. -/
initialize Lean.registerBuiltinAttribute {
  name := `rv64_wp_dead
  descr := "WP unreachable-exit hints used by wp_rv64_dead"
  applicationTime := .afterTypeChecking
  add := fun declName stx _attrKind => do
    Lean.Attribute.Builtin.ensureNoArgs stx
    Lean.modifyEnv fun env => rv64WpDeadExt.addEntry env declName
}

end EvmAsm.Rv64.Tactics
