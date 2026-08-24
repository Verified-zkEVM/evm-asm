/-
Copyright (c) 2026 EvmAsm Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# Sat sweep: satisfiability-witness coverage census for named `Assertion` definitions

Issue #12740 established that for an opaque `Assertion` (`PartialState → Prop`)
no sound and complete syntactic machine-check for atom occupancy can exist,
and that the checkable instrument is a **kernel-checked satisfiability
witness** per named precondition definition: a theorem proving
`∃ h : PartialState, foo_pre … h` (or `Assertion.holdsFor` on a concrete
state).  A pre that double-supplies an atom is unsatisfiable, so no witness
exists and the obligation fails regardless of opacity — this is the
anti-vacuity instrument for the "sepConj double-own" failure mode that a
green build provably cannot detect.

This tool is the **census half** of that instrument: it walks the compiled
environment (the same data the kernel checked — no source-text heuristics,
so a regex census cannot substitute; see #12740 for the measured 20x
disagreement between grep patterns) and reports, for every `def` whose
declared result type is `Assertion`:

* whether a witness **twin** exists under the naming conventions
  `foo_pre_sat` / `foo_pre_satisfiable`, and
* whether that twin **name-references** the pre constant — the twin's type
  must contain the pre constant itself.  A twin that merely restates the
  pre and inhabits the restatement is a tautology (the `_eq_prog`
  self-tie shape) and is reported separately as `restated`, NOT as
  coverage.  Name-reference is checked structurally from the elaborated
  twin type, not by review convention.

Coverage is the fraction of named `Assertion` definitions with a
name-referencing twin.  The tool is **advisory by construction**: it always
exits 0 on a successful walk so it can be seeded green at today's coverage
and promoted only when the fraction and the audit classes are understood
(repo steering policy: never hard-gate a heuristic that red-lights day one).

Scope caveats, deliberately the same as axiomsweep's:
* only definitions whose *stored declared type* is literally `Assertion`
  are counted — a def whose type was inferred as `PartialState → Prop`
  without an `Assertion` ascription is invisible to the const-match (the
  honest census counts ascriptions; regex over-counts, this under-counts);
* `example`s never enter the environment; files not transitively imported
  by the roots are invisible (`check-unimported.sh` keeps the graph
  orphan-free);
* twins are matched by exact name (`_sat`/`_satisfiable` suffix, private
  mangling included); a witness named differently than its pre is an
  untwinned row here even if it inhabits the pre.

Modes (run after `lake build`):

```
lake exe satsweep               # summary + coverage fraction
lake exe satsweep --out r.json  # also write the full per-definition report
lake exe satsweep --verbose     # also print every untwinned / restated name
```
-/

open Lean

namespace SatSweep

/-- Root modules swept when no `--root` is given. -/
def defaultRoots : Array Name := #[`EvmAsm]

/-- The assertion type constant this census keys on. -/
def assertionName : Name := `EvmAsm.Rv64.Assertion

/-- Naming conventions for the satisfiability-witness twin of a pre. -/
def twinSuffixes : List String := ["_sat", "_satisfiable"]

/-- Strip `∀`/`→` binders (and mdata) to expose a type's result. -/
def peelForall : Expr → Expr
  | .forallE _ _ b _ => peelForall b
  | .mdata _ e => peelForall e
  | e => e

/-- A `def` whose declared result type is literally the `Assertion`
constant (see the docstring caveat about ascription vs inference). -/
def isAssertionDef (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ => (peelForall ci.type).isConstOf assertionName
  | _ => false

/-- Structural occurs-check: does constant `n` occur anywhere in `e`?
This is the name-reference test for twin theorems. -/
partial def occurs (n : Name) : Expr → Bool
  | .const c _ => c == n
  | .app f a => occurs n f || occurs n a
  | .lam _ t b _ => occurs n t || occurs n b
  | .forallE _ t b _ => occurs n t || occurs n b
  | .letE _ t v b _ => occurs n t || occurs n v || occurs n b
  | .mdata _ e => occurs n e
  | .proj _ _ e => occurs n e
  | _ => false

/-- Whether to report a constant: skip compiler-internal auxiliaries,
keep private declarations under their environment (mangled) names so twin
lookup stays in the same namespace.  Mirrors axiomsweep's policy. -/
def isReportable (n : Name) : Bool :=
  !n.hasMacroScopes && !((privateToUserName? n).getD n).isInternalDetail

/-- One row of the per-definition report. -/
structure Entry where
  name : String
  module : String
  line : Option Nat
  /-- `covered`: a twin exists and name-references this constant.
  `restated`: a twin exists but its type does not mention this constant
  (tautology-shaped — audit before trusting it). `untwinned`: no twin
  under either suffix convention. -/
  status : String
  deriving ToJson

/-- Classify one Assertion-valued definition against the environment. -/
def classify (env : Environment) (c : Name) : String :=
  let twin := twinSuffixes.findSome? fun suffix =>
    let twinName := c.appendAfter suffix
    match env.find? twinName with
    | some (.thmInfo ti) => some (twinName, ti)
    | _ => none
  match twin with
  | none => "untwinned"
  | some (_, ti) => if occurs c ti.type then "covered" else "restated"

/-- Enumerate the reportable `Assertion`-valued definitions of every module
under `roots` and classify each. -/
def buildEntries (roots : Array Name) : CoreM (Array Entry × Nat) := do
  let env ← getEnv
  let mut targets : Array (Name × Name) := #[]
  let mut seen : Std.HashSet Name := {}
  let mut moduleCount := 0
  for (mname, mdata) in env.header.moduleNames.zip env.header.moduleData do
    if roots.any (·.isPrefixOf mname) then
      moduleCount := moduleCount + 1
      for c in mdata.constNames do
        if isReportable c && !seen.contains c then
          match env.find? c with
          | some ci =>
              if isAssertionDef ci then
                seen := seen.insert c
                targets := targets.push (c, mname)
          | none => pure ()
  let mut entries : Array Entry := #[]
  for (c, mname) in targets do
    let line := (← findDeclarationRanges? c).map (·.range.pos.line)
    entries := entries.push {
      name := c.toString
      module := mname.toString
      line := line
      status := classify env c }
  return (entries.qsort (fun a b => a.name < b.name), moduleCount)

structure Config where
  roots : Array Name := #[]
  out? : Option String := none
  verbose : Bool := false

def parseArgs : List String → Config → Except String Config
  | [], cfg => .ok cfg
  | "--out" :: path :: rest, cfg => parseArgs rest { cfg with out? := some path }
  | "--verbose" :: rest, cfg => parseArgs rest { cfg with verbose := true }
  | "--root" :: mod :: rest, cfg =>
      parseArgs rest { cfg with roots := cfg.roots.push mod.toName }
  | arg :: _, _ => .error s!"satsweep: unknown or incomplete argument: {arg}\n\
      usage: lake exe satsweep [--out FILE] [--verbose] [--root MOD]*"

end SatSweep

open SatSweep in
unsafe def main (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args {} with
    | .ok cfg => pure cfg
    | .error e => IO.eprintln e; return 2
  let roots := if cfg.roots.isEmpty then defaultRoots else cfg.roots
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← try
      importModules (roots.map ({ module := · })) {} (trustLevel := 1024)
        (loadExts := true)
    catch e =>
      IO.eprintln s!"satsweep: cannot import root modules {roots}: {e.toString}\n\
        (run after `lake build`; roots must be importable modules)"
      return (2 : UInt32)
  let ((entries, moduleCount), _) ← (buildEntries roots).toIO
    { fileName := "<satsweep>", fileMap := default } { env }
  let covered := entries.filter (·.status == "covered")
  let restated := entries.filter (·.status == "restated")
  let untwinned := entries.filter (·.status == "untwinned")
  let pct : Float :=
    100.0 * (covered.size.toFloat / (max 1 entries.size).toFloat)
  IO.println s!"satsweep: {entries.size} named Assertion-valued definitions \
    across {moduleCount} modules under {roots}"
  IO.println s!"  covered   (name-referencing twin): {covered.size}"
  IO.println s!"  restated  (twin w/o name-reference — audit): {restated.size}"
  IO.println s!"  untwinned (no _sat/_satisfiable twin):        {untwinned.size}"
  IO.println s!"  coverage: {pct.round / 100.0} (advisory census; exit 0 always)"
  if cfg.verbose then
    if !restated.isEmpty then
      IO.println "restated twins:"
      for e in restated do IO.println s!"  {e.name} ({e.module}:{e.line.getD 0})"
    if !untwinned.isEmpty then
      IO.println "untwinned definitions:"
      for e in untwinned do IO.println s!"  {e.name} ({e.module}:{e.line.getD 0})"
  if let some out := cfg.out? then
    let report := Json.mkObj [
      ("roots", toJson (roots.map (·.toString))),
      ("definitionCount", toJson entries.size),
      ("covered", toJson covered.size),
      ("restated", toJson restated.size),
      ("untwinned", toJson untwinned.size),
      ("definitions", toJson entries)]
    IO.FS.writeFile out (report.pretty ++ "\n")
    IO.println s!"satsweep: wrote report to {out}"
  return 0
