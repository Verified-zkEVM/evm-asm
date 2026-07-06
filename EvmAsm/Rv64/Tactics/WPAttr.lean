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

/-- Environment extension storing theorem names tagged with
    `@[rv64_wp_disjoint]`. These are code-range disjointness hints for WP
    composition side conditions that are too semantic for the structural prover. -/
initialize rv64WpDisjointExt : Lean.SimplePersistentEnvExtension Lean.Name (Array Lean.Name) ←
  Lean.registerSimplePersistentEnvExtension {
    addEntryFn := fun state declName => state.push declName
    addImportedFn := fun entries => entries.foldl (init := #[]) fun acc es => acc ++ es
  }

/-- Disjointness hint database used by `wp_rv64_disjoint` after local hypotheses
    and structural code-shape proving. Theorems tagged here should prove goals
    of shape `CodeReq.Disjoint cr1 cr2`, with side conditions inferable from
    the local context. -/
initialize Lean.registerBuiltinAttribute {
  name := `rv64_wp_disjoint
  descr := "WP code disjointness hints used by wp_rv64_disjoint"
  applicationTime := .afterTypeChecking
  add := fun declName stx _attrKind => do
    Lean.Attribute.Builtin.ensureNoArgs stx
    Lean.modifyEnv fun env => rv64WpDisjointExt.addEntry env declName
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


/-- Environment extension storing theorem/definition names tagged with
    `@[rv64_wp_cert]`.  These are WP certificate constructors whose arguments
    can be inferred from the target and local static facts. -/
initialize rv64WpCertExt : Lean.SimplePersistentEnvExtension Lean.Name (Array Lean.Name) ←
  Lean.registerSimplePersistentEnvExtension {
    addEntryFn := fun state declName => state.push declName
    addImportedFn := fun entries => entries.foldl (init := #[]) fun acc es => acc ++ es
  }

/-- Certificate hint database used by `wp_rv64_cert`.  Declarations tagged here
    should return `WP.Triple`/`WP.CFG.Cert`, `WP.Branch`, or `WP.NBranch`, with
    proof arguments inferable from local hypotheses. -/
initialize Lean.registerBuiltinAttribute {
  name := `rv64_wp_cert
  descr := "WP certificate constructors used by wp_rv64_cert"
  applicationTime := .afterTypeChecking
  add := fun declName stx _attrKind => do
    Lean.Attribute.Builtin.ensureNoArgs stx
    Lean.modifyEnv fun env => rv64WpCertExt.addEntry env declName
}

end EvmAsm.Rv64.Tactics
