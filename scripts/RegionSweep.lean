/-
Copyright (c) 2026 EvmAsm Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# Region sweep: duplicate resource occupancy in separating conjunctions (#12740)

`SatSweep` answers whether a named `Assertion` has a kernel-checked witness.
`FootSweep` answers whether an at-risk contract exposes the registers and
bytes that its code touches.  This executable is the small automatic middle
ground: it walks the *elaborated* `sepConj` trees and looks for two recognised
atoms whose resource footprints overlap.

The result is deliberately a **Tier B advisory census**, not a complete
decision procedure for `Assertion := PartialState → Prop`.  A lambda, an
unregistered assertion wrapper, a data-driven frame, or an opaque assertion
parameter is reported as unaudited rather than guessed.  The four controls in
`selfTest` are structural Expr terms, so they do not introduce axioms or
depend on a theorem that could itself be vacuous:

* `wrong_pin_control`: `regOwn x5 ** regIs x5 v`;
* the descriptor/bridge shape: two equal `bytesRegion` atoms;
* the chain-encoding buffer shape: `memOwn p ** memIs p v`;
* the chain/BSS residual shape: a one-dword `bytesRegion` overlapping
  `memOwn` at the same base.

The sweep only claims an overlap inside one separating-conjunction component.
It does not compare a pre with a post, and it does not merge alternatives
under logical conjunction.  Consequently a positive row is a review lead,
not a proof that every possible instantiation is unsatisfiable; a clean row
does not certify an opaque component.  Theorems whose outer proposition is a
negation (for example a deliberately proved `..._false` separation lemma) are
not contracts and are excluded structurally from the census.

Modes (run after `lake build`):

```
lake exe regionsweep                 # advisory census
lake exe regionsweep --self-test     # four planted overlap controls
lake exe regionsweep --verbose       # print every finding
lake exe regionsweep --out r.json    # write the report
```
-/

open Lean

namespace RegionSweep

/-! ## Names and environment resolution -/

def defaultRoots : Array Name := #[`EvmAsm]

structure Names where
  assertion : Name
  sepConj : Name
  regOwn : Name
  regIs : Name
  memOwn : Name
  memIs : Name
  bytesRegion : Name
  assertPure : Name
  empAssertion : Name

def nameCandidates : List (String × List String) :=
  [ ("assertion", ["EvmAsm.Rv64.Assertion", "RiscvZkvm.Rv64.Assertion"])
  , ("sepConj", ["EvmAsm.Rv64.sepConj", "RiscvZkvm.Rv64.sepConj"])
  , ("regOwn", ["EvmAsm.Rv64.regOwn", "RiscvZkvm.Rv64.regOwn"])
  , ("regIs", ["EvmAsm.Rv64.regIs", "RiscvZkvm.Rv64.regIs"])
  , ("memOwn", ["EvmAsm.Rv64.memOwn", "RiscvZkvm.Rv64.memOwn"])
  , ("memIs", ["EvmAsm.Rv64.memIs", "RiscvZkvm.Rv64.memIs"])
  , ("bytesRegion", ["EvmAsm.Rv64.bytesRegion", "EvmAsm.Rv64.MemRegion.bytesRegion",
      "RiscvZkvm.Rv64.bytesRegion"])
  , ("assertPure", ["EvmAsm.Rv64.assertPure", "RiscvZkvm.Rv64.assertPure"])
  , ("empAssertion", ["EvmAsm.Rv64.empAssertion", "RiscvZkvm.Rv64.empAssertion"]) ]

def resolveNames (env : Environment) : Except (Array String) Names := do
  let mut missing : Array String := #[]
  let mut resolved : Std.HashMap String Name := {}
  for (role, candidates) in nameCandidates do
    let mut found : Option Name := none
    for candidate in candidates do
      if env.find? candidate.toName |>.isSome then
        found := some candidate.toName
    match found with
    | some n => resolved := resolved.insert role n
    | none => missing := missing.push s!"{role} (tried {candidates})"
  if !missing.isEmpty then throw missing
  return {
    assertion := resolved["assertion"]!
    sepConj := resolved["sepConj"]!
    regOwn := resolved["regOwn"]!
    regIs := resolved["regIs"]!
    memOwn := resolved["memOwn"]!
    memIs := resolved["memIs"]!
    bytesRegion := resolved["bytesRegion"]!
    assertPure := resolved["assertPure"]!
    empAssertion := resolved["empAssertion"]! }

structure Ctx where
  env : Environment
  names : Names

/-! ## Expression utilities -/

def peelForall : Expr → Expr
  | .forallE _ _ b _ => peelForall b
  | .mdata _ e => peelForall e
  | e => e

def headConst? : Expr → Option Name
  | .app f _ => headConst? f
  | .mdata _ e => headConst? e
  | .const c _ => some c
  | _ => none

def isReportable (n : Name) : Bool :=
  !n.hasMacroScopes && !((privateToUserName? n).getD n).isInternalDetail

def isAssertionDef (ctx : Ctx) (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ => (peelForall ci.type).isConstOf ctx.names.assertion
  | _ => false

def isNegativeTheorem (e : Expr) : Bool :=
  match headConst? (peelForall e) with
  | some c => c == `Not
  | none => false

def isExcludedTheorem : ConstantInfo → Bool
  | .thmInfo ti => isNegativeTheorem ti.type
  | _ => false

/-! ## Footprints -/

inductive FootFamily where
  | register
  | dword
  deriving Repr

structure Footprint where
  family : FootFamily
  /-- Register identity, or the first dword address of a memory span. -/
  base : Expr
  /-- Number of dwords for a byte region; `some 1` for a singleton cell. -/
  span : Option Nat
  /-- The original byte-list expression, retained for unresolved regions. -/
  shape : Option Expr

instance : Inhabited Footprint :=
  ⟨{ family := .register, base := .bvar 0, span := none, shape := none }⟩

def optExprEq : Option Expr → Option Expr → Bool
  | none, none => true
  | some a, some b => a == b
  | _, _ => false

def familyEq : FootFamily → FootFamily → Bool
  | .register, .register => true
  | .dword, .dword => true
  | _, _ => false

def footprintMayOverlap (a b : Footprint) : Bool :=
  if !familyEq a.family b.family || !(a.base == b.base) then false
  else
    match a.family, a.span, b.span with
    | .register, _, _ => true
    | .dword, some na, some nb => na > 0 && nb > 0
    | .dword, _, _ => true

def familyName : FootFamily → String
  | .register => "register"
  | .dword => "memory"

def exprSummary (e : Expr) : String :=
  match headConst? e with
  | some c => c.toString
  | none => "<expression>"

def footprintDescription (f : Footprint) : String :=
  let span := match f.span with
    | some n => s!"{n} dword(s)"
    | none => "unknown-size region"
  s!"{familyName f.family} at {exprSummary f.base} ({span})"

/-- A same-register pair is a definite ownership collision: `regOwn` and
    `regIs` both consume the one register resource.  A same-base memory pair
    with two known positive spans is likewise definite; an unknown extent
    remains only a possible overlap. -/
def overlapKind (a b : Footprint) : String :=
  match a.family, b.family, a.span, b.span with
  | .register, .register, _, _ => "definite duplicate register occupancy"
  | .dword, .dword, some na, some nb =>
      if na > 0 && nb > 0 then "definite memory overlap" else "possible overlap"
  | _, _, _, _ => "possible overlap"

/-! ## Literal list lengths -/

/-- Evaluate only the list fragment needed for a byte-region extent.  An
unknown list is retained as an unresolved footprint rather than guessed. -/
partial def listLength? (env : Environment) (fuel : Nat) (e : Expr) : Option Nat :=
  if fuel == 0 then none
  else
    let e := e.headBeta
    match headConst? e with
    | some c =>
        if c == `List.nil then some 0
        else if c == `List.cons then
          match e.getAppArgs with
          | #[_, _, tail] => (listLength? env (fuel - 1) tail).map (· + 1)
          | _ => none
        else if c == `List.append || c == `HAppend.hAppend then
          let args := e.getAppArgs
          if args.size < 2 then none
          else
            match listLength? env (fuel - 1) args[args.size - 2]!,
                listLength? env (fuel - 1) args[args.size - 1]! with
            | some a, some b => some (a + b)
            | _, _ => none
        else
          match env.find? c with
          | some (.defnInfo di) =>
              let body := (e.getAppArgs.foldl (fun v a => v.app a) di.value).headBeta
              listLength? env (fuel - 1) body
          | _ => none
    | none => none

def bytesDwordCount? (ctx : Ctx) (bytes : Expr) : Option Nat :=
  (listLength? ctx.env 80 bytes).map fun n => (n + 7) / 8

/-! ## Alias expansion and component extraction -/

def unfoldDefnApp (env : Environment) (c : Name) (e : Expr) : Expr :=
  match env.find? c with
  | some (.defnInfo di) =>
      (e.getAppArgs.foldl (fun v a => v.app a) di.value).headBeta
  | _ => e

structure Component where
  footprints : Array Footprint
  /-- Reasons why some assertion leaves were not auditable.  Keeping the
      reason, rather than a bare Boolean, makes the coverage boundary visible
      in the report and gives future extensions a target to remove. -/
  opaqueReasons : Array String
  deriving Inhabited

def mergeComponent (a b : Component) : Component :=
  { footprints := a.footprints ++ b.footprints
    opaqueReasons := a.opaqueReasons ++ b.opaqueReasons }

def emptyComponent : Component := { footprints := #[], opaqueReasons := #[] }

def singletonComponent (f : Footprint) : Component :=
  { footprints := #[f], opaqueReasons := #[] }

def opaqueComponent (reason : String) : Component :=
  { footprints := #[], opaqueReasons := #[reason] }

def atomFootprint (ctx : Ctx) (c : Name) (args : Array Expr)
    : Option Footprint × Option String :=
  if c == ctx.names.regOwn || c == ctx.names.regIs then
    match args[0]? with
    | some r => (some { family := .register, base := r, span := none, shape := none }, none)
    | none => (none, some "malformed register atom")
  else if c == ctx.names.memOwn || c == ctx.names.memIs then
    match args[0]? with
    | some p => (some { family := .dword, base := p, span := some 1, shape := none }, none)
    | none => (none, some "malformed memory atom")
  else if c == ctx.names.bytesRegion then
    match args[0]?, args[1]? with
    | some p, some bs =>
        let span := bytesDwordCount? ctx bs
        (some { family := .dword, base := p, span := span, shape := some bs },
          match span with
          | some _ => none
          | none => some "unknown byte-region length")
    | _, _ => (none, some "malformed byte-region atom")
  else (none, none)

/-- Extract the recognised atoms from one `sepConj` component.  Unknown
assertion leaves make the component partially unaudited but do not hide
duplicate pairs among atoms that are visible. -/
partial def collectComponent (ctx : Ctx) (fuel : Nat) (e : Expr)
    : Component :=
  if fuel == 0 then opaqueComponent "recursion-depth limit"
  else
    let e := e.headBeta
    match e with
    | .mdata _ b => collectComponent ctx fuel b
    | .lam _ _ b _ => collectComponent ctx (fuel - 1) b
    | .forallE _ _ b _ => collectComponent ctx (fuel - 1) b
    | .app .. =>
        match headConst? e with
        | none => opaqueComponent "application with unresolved head"
        | some c =>
            let args := e.getAppArgs
            if c == ctx.names.sepConj then
              args.foldl (init := emptyComponent) fun acc arg =>
                mergeComponent acc (collectComponent ctx (fuel - 1) arg)
            else
              let (atom?, reason?) := atomFootprint ctx c args
              match atom? with
              | some f =>
                  { footprints := #[f]
                    opaqueReasons := match reason? with
                      | some reason => #[reason]
                      | none => #[] }
              | none =>
                  if c == ctx.names.empAssertion then emptyComponent
                  else if c == ctx.names.assertPure then
                    -- `assertPure` contributes no resource of its own; all
                    -- assertion arguments remain in this component.
                    args.foldl (init := emptyComponent) fun acc arg =>
                      mergeComponent acc (collectComponent ctx (fuel - 1) arg)
                  else
                    match ctx.env.find? c with
                    | some (.defnInfo di) =>
                        if isAssertionDef ctx (.defnInfo di) then
                          collectComponent ctx (fuel - 1) (unfoldDefnApp ctx.env c e)
                        else opaqueComponent "opaque/non-Assertion application"
                    | _ => opaqueComponent "unresolved assertion application"
    | .proj _ _ b => collectComponent ctx (fuel - 1) b
    | .letE _ _ _ _ _ => opaqueComponent "let-bound assertion"
    | _ => emptyComponent

/-! ## Component discovery -/

/-- Find each top-level separating-conjunction component independently.  A
direct `sepConj` is consumed as one unit; its children are not discovered a
second time, which prevents duplicate rows from nested traversal. -/
partial def findComponents (ctx : Ctx) (fuel : Nat) (e : Expr)
    (acc : Array Component) : Array Component :=
  if fuel == 0 then acc
  else
    let e := e.headBeta
    match e with
    | .mdata _ b => findComponents ctx fuel b acc
    | .lam _ t b _ =>
        findComponents ctx (fuel - 1) b (findComponents ctx (fuel - 1) t acc)
    | .forallE _ t b _ =>
        findComponents ctx (fuel - 1) b (findComponents ctx (fuel - 1) t acc)
    | .letE _ t v b _ =>
        findComponents ctx (fuel - 1) b
          (findComponents ctx (fuel - 1) v (findComponents ctx (fuel - 1) t acc))
    | .app .. =>
        match headConst? e with
        | none => acc
        | some c =>
            if c == ctx.names.sepConj then
              acc.push (collectComponent ctx (fuel - 1) e)
            else if c == ctx.names.regOwn || c == ctx.names.regIs
                || c == ctx.names.memOwn || c == ctx.names.memIs
                || c == ctx.names.bytesRegion || c == ctx.names.empAssertion then
              -- A singleton atom cannot contain a separating conjunction.
              acc
            else
              match ctx.env.find? c with
              | some (.defnInfo di) =>
                  if isAssertionDef ctx (.defnInfo di) then
                    findComponents ctx (fuel - 1)
                      (unfoldDefnApp ctx.env c e) acc
                  else
                    e.getAppArgs.foldl (init := acc) fun a x =>
                      findComponents ctx (fuel - 1) x a
              | _ =>
                  e.getAppArgs.foldl (init := acc) fun a x =>
                    findComponents ctx (fuel - 1) x a
    | .proj _ _ b => findComponents ctx (fuel - 1) b acc
    | _ => acc

def duplicatePairs (footprints : Array Footprint)
    : Array (Footprint × Footprint) := Id.run do
  let mut out : Array (Footprint × Footprint) := #[]
  for i in [:footprints.size] do
    for j in [i + 1:footprints.size] do
      if footprintMayOverlap footprints[i]! footprints[j]! then
        out := out.push (footprints[i]!, footprints[j]!)
  return out

/-! ## Self-test -/

def mkSep (n : Names) (a b : Expr) : Expr :=
  mkApp2 (mkConst n.sepConj) a b

def mkApp1 (f a : Expr) : Expr := mkApp f a

def joinStrings (items : Array String) : String :=
  items.foldl (fun acc item => if acc.isEmpty then item else acc ++ ", " ++ item) ""

def selfTest (ctx : Ctx) : Bool × Array String := Id.run do
  let mut ok := true
  let mut log : Array String := #[]
  let n := ctx.names
  let x5 := mkConst `EvmAsm.Rv64.Reg.x5
  let base := mkConst `selfTest.base
  let value := .lit (.natVal 0)
  let regOwn := mkApp1 (mkConst n.regOwn) x5
  let regIs := mkApp2 (mkConst n.regIs) x5 value
  let memOwn := mkApp1 (mkConst n.memOwn) base
  let memIs := mkApp2 (mkConst n.memIs) base value
  let nil := mkConst `List.nil
  let bytes8 := mkApp3 (mkConst `List.cons) (mkConst `BitVec) value nil
  let bytes := mkApp2 (mkConst n.bytesRegion) base bytes8
  let controls : Array (String × Expr) := #[
    ("wrong_pin_control", mkSep n regOwn regIs),
    ("descriptor_bridge_duplicate_bytes_region_control", mkSep n bytes bytes),
    ("chain_encoding_duplicate_mem_region_control", mkSep n memOwn memIs),
    ("chain_bss_mixed_region_control", mkSep n bytes memOwn)]
  let mut passed := 0
  for (name, expression) in controls do
    let component := collectComponent ctx 80 expression
    if !(duplicatePairs component.footprints).isEmpty then
      passed := passed + 1
      log := log.push s!"pass: {name}"
    else
      ok := false
      log := log.push s!"FAIL: {name} was not detected"
  let clean := mkSep n (mkApp1 (mkConst n.regOwn) x5)
    (mkApp1 (mkConst n.memOwn) (mkConst `selfTest.other))
  let cleanComponent := collectComponent ctx 80 clean
  if (duplicatePairs cleanComponent.footprints).isEmpty then
    log := log.push "pass: clean component has no false overlap"
  else
    ok := false
    log := log.push "FAIL: clean component reported an overlap"
  if passed == controls.size then
    log := log.push s!"region sweep controls: {passed}/{controls.size}"
  else
    ok := false
    log := log.push s!"FAIL: region sweep controls: {passed}/{controls.size}"
  return (ok, log)

/-! ## Environment census -/

structure Finding where
  name : String
  module : String
  line : Option Nat
  component : Nat
  detail : String
  deriving ToJson

structure SweepResult where
  declarationCount : Nat
  moduleCount : Nat
  componentCount : Nat
  auditedCount : Nat
  opaqueCount : Nat
  findingCount : Nat
  auditedFindingCount : Nat
  partialFindingCount : Nat
  excludedNegativeTheoremCount : Nat
  findings : Array Finding

def enumerateDecls (env : Environment) (roots : Array Name)
    : Array (Name × Name) := Id.run do
  let mut result : Array (Name × Name) := #[]
  let mut seen : Std.HashSet Name := {}
  for (mname, mdata) in env.header.moduleNames.zip env.header.moduleData do
    if roots.any (·.isPrefixOf mname) then
      for c in mdata.constNames do
        if isReportable c && !seen.contains c then
          seen := seen.insert c
          result := result.push (c, mname)
  return result

def declarationExpr (ctx : Ctx) (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .thmInfo ti => some ti.type
  | .defnInfo di => if isAssertionDef ctx ci then some di.value else none
  | _ => none

def sweep (ctx : Ctx) (roots : Array Name) : CoreM SweepResult := do
  let env := ctx.env
  let decls := enumerateDecls env roots
  let mut moduleCount : Nat := 0
  for (m, _) in env.header.moduleNames.zip env.header.moduleData do
    if roots.any (·.isPrefixOf m) then moduleCount := moduleCount + 1
  let mut componentCount : Nat := 0
  let mut auditedCount : Nat := 0
  let mut opaqueCount : Nat := 0
  let mut excludedNegativeTheoremCount : Nat := 0
  let mut findings : Array Finding := #[]
  for (c, mname) in decls do
    let some ci := env.find? c | continue
    if isExcludedTheorem ci then
      excludedNegativeTheoremCount := excludedNegativeTheoremCount + 1
      continue
    let some expression := declarationExpr ctx ci | continue
    let components := findComponents ctx 1000 expression #[]
    let line := (← findDeclarationRanges? c).map (·.range.pos.line)
    for (componentData, component) in components.zipIdx do
      componentCount := componentCount + 1
      let unresolved := !componentData.opaqueReasons.isEmpty
      if unresolved then opaqueCount := opaqueCount + 1 else auditedCount := auditedCount + 1
      let auditDetail := if unresolved then
          s!" (component partially unaudited: {joinStrings componentData.opaqueReasons})"
        else ""
      for (left, right) in duplicatePairs componentData.footprints do
        findings := findings.push {
          name := c.toString
          module := mname.toString
          line := line
          component := component
          detail := s!"{overlapKind left right}: {footprintDescription left} and \
            {footprintDescription right}{auditDetail}" }
  let auditedFindingCount := findings.foldl
    (fun n f => if f.detail.contains "partially unaudited" then n else n + 1) 0
  let partialFindingCount := findings.size - auditedFindingCount
  return {
    declarationCount := decls.size
    moduleCount := moduleCount
    componentCount := componentCount
    auditedCount := auditedCount
    opaqueCount := opaqueCount
    findingCount := findings.size
    auditedFindingCount := auditedFindingCount
    partialFindingCount := partialFindingCount
    excludedNegativeTheoremCount := excludedNegativeTheoremCount
    findings := findings }

/-! ## CLI -/

structure Config where
  roots : Array Name := #[]
  out? : Option String := none
  verbose : Bool := false
  selfTestOnly : Bool := false

def parseArgs : List String → Config → Except String Config
  | [], cfg => .ok cfg
  | "--out" :: path :: rest, cfg => parseArgs rest { cfg with out? := some path }
  | "--verbose" :: rest, cfg => parseArgs rest { cfg with verbose := true }
  | "--self-test" :: rest, cfg => parseArgs rest { cfg with selfTestOnly := true }
  | "--root" :: module :: rest, cfg =>
      parseArgs rest { cfg with roots := cfg.roots.push module.toName }
  | arg :: _, _ => .error s!"regionsweep: unknown or incomplete argument: {arg}\n\\
      usage: lake exe regionsweep [--out FILE] [--verbose] [--self-test] [--root MOD]*"

end RegionSweep

open RegionSweep in
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
      IO.eprintln s!"regionsweep: cannot import root modules {roots}: {e.toString}"
      return 2
  let names ← match resolveNames env with
    | .ok n => pure n
    | .error missing =>
        IO.eprintln s!"regionsweep: unresolved core names: {missing.toList}"
        return 2
  let ctx := { env := env, names := names }
  let (stOk, stLog) := selfTest ctx
  for line in stLog do IO.println line
  if cfg.selfTestOnly then
    if stOk then IO.println "regionsweep self-test: PASS"; return 0
    else IO.eprintln "regionsweep self-test: FAIL"; return 2
  if !stOk then
    IO.eprintln "regionsweep: self-test failed; refusing to report (infra)"
    return 2
  let (result, _) ← (sweep ctx roots).toIO
    { fileName := "<regionsweep>", fileMap := default } { env }
  IO.println s!"regionsweep: {result.declarationCount} declarations across \
    {result.moduleCount} modules under {roots}"
  IO.println s!"  sepConj components: {result.componentCount}"
  IO.println s!"  audited components: {result.auditedCount}"
  IO.println s!"  partially unaudited components: {result.opaqueCount}"
  IO.println s!"  possible duplicate occupancies: {result.findingCount}"
  IO.println s!"    audited atom pairs: {result.auditedFindingCount}"
  IO.println s!"    partially unaudited atom pairs: {result.partialFindingCount}"
  IO.println s!"  negative/contradiction theorems excluded: \
    {result.excludedNegativeTheoremCount}"
  if cfg.verbose then
    for finding in result.findings do
      IO.println s!"  [region-overlap] {finding.name} \
        ({finding.module}:{finding.line.getD 0}) component {finding.component}: \
        {finding.detail}"
  if let some out := cfg.out? then
    let report := Json.mkObj [
      ("roots", toJson (roots.map (·.toString))),
      ("declarationCount", toJson result.declarationCount),
      ("moduleCount", toJson result.moduleCount),
      ("componentCount", toJson result.componentCount),
      ("auditedCount", toJson result.auditedCount),
      ("opaqueCount", toJson result.opaqueCount),
      ("findingCount", toJson result.findingCount),
      ("auditedFindingCount", toJson result.auditedFindingCount),
      ("partialFindingCount", toJson result.partialFindingCount),
      ("excludedNegativeTheoremCount", toJson result.excludedNegativeTheoremCount),
      ("findings", toJson result.findings)]
    IO.FS.writeFile out (report.pretty ++ "\n")
    IO.println s!"regionsweep: wrote report to {out}"
  IO.println "regionsweep: advisory census; exit 0 always"
  return 0
