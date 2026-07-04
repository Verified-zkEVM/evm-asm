/-
  port_check_axioms.lean — per-module kernel axiom audit.

  Usage:  lake env lean --run scripts/port_check_axioms.lean <Module.Name>

  Collects the axioms behind every theorem DECLARED IN the given module
  (kernel truth via `Lean.CollectAxioms`, the same engine as
  `#print axioms`) and fails unless each theorem rests only on the
  three classical axioms: `propext`, `Classical.choice`, `Quot.sound`.

  This is the per-file complement of `scripts/check-axioms.sh` (which
  audits the Progress registry witnesses): `scripts/port-check.sh`
  calls it so a routine-port PR can be gated file-locally before the
  registry ever references it.
-/
import Lean

open Lean

def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- Minimal `MonadEnv` carrier so we can run `Lean.collectAxioms`
    against an imported environment without spinning up `CoreM`. -/
abbrev EnvM := ReaderT Environment Id

instance : MonadEnv EnvM where
  getEnv := read
  modifyEnv _ := pure ()

unsafe def main (args : List String) : IO UInt32 := do
  let [modStr] := args
    | do IO.eprintln "usage: port_check_axioms <Module.Name>"; return 2
  let modName := modStr.toName
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := modName }] {} (trustLevel := 1024)
  let some modIdx := env.getModuleIdx? modName
    | do IO.eprintln s!"port_check_axioms: module {modName} not found after import"; return 2
  let data := env.header.moduleData[modIdx.toNat]!
  let mut checked := 0
  let mut bad := 0
  for n in data.constNames do
    match env.find? n with
    | some (.thmInfo _) =>
      let axs : Array Name := (collectAxioms n : EnvM _).run env
      let extra := axs.toList.filter (fun a => ¬ allowedAxioms.contains a)
      checked := checked + 1
      if extra ≠ [] then
        bad := bad + 1
        IO.println s!"FORBIDDEN {n}: {extra}"
    | _ => pure ()
  if bad > 0 then
    IO.eprintln s!"port_check_axioms: {bad}/{checked} theorems in {modName} carry non-classical axioms"
    return 1
  IO.println s!"port_check_axioms: OK ({checked} theorems in {modName}, classical axioms only)"
  return 0
