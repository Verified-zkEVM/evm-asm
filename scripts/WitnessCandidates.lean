/-
  witness-candidates -- statement-keyed axiom-witness census (#12210 part 2)

  This is deliberately a separate executable.  It imports the elaborated EvmAsm
  environment at runtime instead of becoming part of the Progress registry, which
  would create the exact registry cycle this check is meant to detect.
-/
import Lean
import EvmAsm.Rv64.CPSSpec

open Lean Meta

namespace WitnessCandidates

def trimAscii (s : String) : String := s.trimAscii.toString

def cpsHeads : List Name := [
  ``EvmAsm.Rv64.cpsTripleWithin,
  ``EvmAsm.Rv64.cpsBranchWithin,
  ``EvmAsm.Rv64.cpsNBranchWithin,
  ``EvmAsm.Rv64.cpsHaltTripleWithin
]

def isReportable (n : Name) : Bool :=
  !n.hasMacroScopes && !n.toString.startsWith "_private." &&
    !((privateToUserName? n).getD n).isInternalDetail

partial def peelForall (ty : Expr) : Expr :=
  match ty with
  | .forallE _ _ body _ => peelForall body
  | .letE _ _ value body _ => peelForall (body.instantiate1 value)
  | .mdata _ body => peelForall body
  | _ => ty

partial def reduceHead (env : Environment) (e : Expr)
    (seen : Std.HashSet Name := {}) : Option Name :=
  let body := peelForall e
  match body.getAppFn.constName? with
  | none => none
  | some n =>
      if cpsHeads.contains n then some n
      else if seen.contains n then some n
      else
        match env.find? n with
        | some (.defnInfo info) =>
            let reduced := body.getAppArgs.foldl
              (init := info.value) fun f arg =>
                match f with
                | .lam _ _ body _ => body.instantiate1 arg
                | _ => f
            reduceHead env reduced (seen.insert n)
        | _ => some n

def sourceLine (n : Name) : CoreM (Option Nat) := do
  return (← findDeclarationRanges? n).map (·.range.pos.line)

structure Candidate where
  name : String
  module : String
  line : Nat
  shape : String
  codeReq : String
  codeReqOfProg : Bool
  deriving ToJson

def codeReqIndex (head : Name) : Nat :=
  if head == ``EvmAsm.Rv64.cpsTripleWithin then 3
  else if head == ``EvmAsm.Rv64.cpsHaltTripleWithin then 2
  else 2

partial def containsCodeReqOfProg (e : Expr) : Bool :=
  match e with
  | .const n _ => n == ``EvmAsm.Rv64.CodeReq.ofProg
  | .app f a => containsCodeReqOfProg f || containsCodeReqOfProg a
  | .lam _ ty body _ => containsCodeReqOfProg ty || containsCodeReqOfProg body
  | .forallE _ ty body _ => containsCodeReqOfProg ty || containsCodeReqOfProg body
  | .letE _ ty value body _ =>
      containsCodeReqOfProg ty || containsCodeReqOfProg value || containsCodeReqOfProg body
  | .mdata _ body => containsCodeReqOfProg body
  | .proj _ _ body => containsCodeReqOfProg body
  | _ => false

def codeReqInfo (head : Name) (ty : Expr) : String × Bool :=
  let body := peelForall ty
  let args := body.getAppArgs
  match args[codeReqIndex head]? with
  | some cr => (cr.getAppFn.constName?.map (·.toString) |>.getD "<expression>", containsCodeReqOfProg cr)
  | none => ("<missing>", false)

def qualifiedRegistryNames : IO (Std.HashSet String) := do
  let mut out : Std.HashSet String := {}
  let path := "EvmAsm/Progress/AxiomWitnesses.lean"
  if !(← System.FilePath.pathExists path) then
    throw <| IO.Error.userError s!"missing {path}"
  for line in (← IO.FS.readFile path).splitOn "\n" do
    let line := trimAscii line
    if line.startsWith "#print axioms " then
      out := out.insert (trimAscii (line.drop "#print axioms ".length).toString)
  return out

def candidateRows (env : Environment) : CoreM (Array Candidate) := do
  let mut names : Std.HashMap Name String := {}
  for (mname, mdata) in env.header.moduleNames.zip env.header.moduleData do
    for n in mdata.constNames do
      if n.toString.startsWith "EvmAsm.Codegen." && isReportable n then
        names := names.insert n mname.toString
  let mut rows : Array Candidate := #[]
  for (n, module) in names.toList do
    let some ci := env.find? n | continue
    let some head := reduceHead env ci.type | continue
    if !cpsHeads.contains head then continue
    let shape := head.toString
    let line := (← sourceLine n).getD 0
    let (codeReq, codeReqOfProg) := codeReqInfo head ci.type
    rows := rows.push { name := n.toString, module, line, shape, codeReq, codeReqOfProg }
  return rows.qsort (fun a b => a.name < b.name)

def readManifest (path : String) : IO (Std.HashMap String (String × String)) := do
  if !(← System.FilePath.pathExists path) then
    throw <| IO.Error.userError s!"missing manifest {path}"
  let mut out : Std.HashMap String (String × String) := {}
  let mut previous : Option String := none
  for line in (← IO.FS.readFile path).splitOn "\n" do
    let line := trimAscii line
    if line.isEmpty || line.startsWith "#" then continue
    let fields := line.splitOn "\t"
    if fields.length != 3 then
      throw <| IO.Error.userError s!"malformed manifest row: {line}"
    let name := trimAscii fields[0]!
    let kind := trimAscii fields[1]!
    let reason := trimAscii fields[2]!
    if name.isEmpty || kind.isEmpty || reason.isEmpty then
      throw <| IO.Error.userError s!"manifest row has empty field: {line}"
    if kind == "needs-review" || kind == "needs-classification" then
      throw <| IO.Error.userError s!"manifest row still has placeholder kind: {name}"
    if out.contains name then
      throw <| IO.Error.userError s!"duplicate manifest name: {name}"
    if !name.contains "." then
      throw <| IO.Error.userError s!"manifest name is not qualified: {name}"
    if let some prev := previous then
      if !(prev < name) then
        throw <| IO.Error.userError s!"manifest is not strictly sorted: {prev} then {name}"
    previous := some name
    out := out.insert name (kind, reason)
  if out.isEmpty then
    throw <| IO.Error.userError s!"manifest is empty: {path}"
  return out

def writeManifest (path : String) (rows : Array Candidate) : IO Unit := do
  let mut text := "# statement-keyed CPS candidates excluded from the witness registry\n"
  text := text ++ "# name<TAB>kind<TAB>non-empty reviewed reason\n"
  text := text ++ "# This is an unreviewed draft: --check rejects placeholder kinds until each row is classified.\n\n"
  for row in rows do
    text := text ++ s!"{row.name}\tneeds-review\tInitial Part 2 baseline; classify against the landed shape classifier before registry promotion.\n"
  IO.FS.writeFile path text

structure Config where
  check : Bool := false
  out? : Option String := none
  writeExclusions : Bool := false
  initializeExclusions : Bool := false
  exclusions : String := "scripts/axiom-witness-candidates-exclusions.tsv"

def parseArgs : List String → Config → Except String Config
  | [], cfg => .ok cfg
  | "--check" :: rest, cfg => parseArgs rest { cfg with check := true }
  | "--out" :: p :: rest, cfg => parseArgs rest { cfg with out? := some p }
  | "--write-exclusions" :: rest, cfg => parseArgs rest { cfg with writeExclusions := true }
  | "--initialize-exclusions" :: rest, cfg => parseArgs rest { cfg with initializeExclusions := true }
  | "--exclusions" :: p :: rest, cfg => parseArgs rest { cfg with exclusions := p }
  | arg :: _, _ => .error s!"unknown argument {arg}"

unsafe def main (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args {} with
    | .ok c => pure c
    | .error e => IO.eprintln s!"witness-candidates: {e}"; return (2 : UInt32)
  if cfg.initializeExclusions && !cfg.writeExclusions then
    IO.eprintln "witness-candidates: --initialize-exclusions requires --write-exclusions"
    return (2 : UInt32)
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← try
      importModules #[{ module := `EvmAsm }] {} (trustLevel := 1024) (loadExts := true)
    catch e =>
      IO.eprintln s!"witness-candidates: cannot import EvmAsm: {e.toString}"
      return (2 : UInt32)
  let (rows, _) ← (candidateRows env).toIO
    { fileName := "<witness-candidates>", fileMap := default } { env }
  let registry ← qualifiedRegistryNames
  let mut environmentNames : Std.HashSet String := {}
  for (_, mdata) in env.header.moduleNames.zip env.header.moduleData do
    for n in mdata.constNames do
      environmentNames := environmentNames.insert n.toString
  for regName in registry.toList do
    if !regName.contains "." then
      IO.eprintln s!"witness-candidates: ambiguous unqualified registry proof ref: {regName}"
      return (1 : UInt32)
    if !environmentNames.contains regName then
      IO.eprintln s!"witness-candidates: stale registry proof ref: {regName}"
      return (1 : UInt32)
  let mut candidates : Std.HashSet String := {}
  for row in rows do candidates := candidates.insert row.name
  let mut registered : Std.HashSet String := {}
  for row in rows do
    if registry.contains row.name then registered := registered.insert row.name
  let unregistered := rows.filter fun row => !registry.contains row.name
  if let some path := cfg.out? then
    let mut text := "name\tmodule\tline\tshape\tcodeReq\tcodeReq_ofProg\tregistered\n"
    for row in rows do
      text := text ++ s!"{row.name}\t{row.module}\t{row.line}\t{row.shape}\t{row.codeReq}\t{row.codeReqOfProg}\t{registry.contains row.name}\n"
    IO.FS.writeFile path text
    IO.println s!"witness-candidates: wrote {path} ({rows.size} candidates)"
  IO.println s!"witness-candidates: {rows.size} CPS candidates; registered={registered.size}; unregistered={unregistered.size}"
  if !unregistered.isEmpty && !cfg.check then
    for row in unregistered do IO.println s!"  UNREGISTERED {row.name} ({row.module}:{row.line}) {row.shape}"
  if cfg.writeExclusions then
    let manifestExists ← System.FilePath.pathExists cfg.exclusions
    if !manifestExists then
      if !cfg.initializeExclusions then
        IO.eprintln "witness-candidates: exclusions missing; use --initialize-exclusions in a reviewed change"
        return 1
      writeManifest cfg.exclusions unregistered
      IO.println s!"witness-candidates: initialized {cfg.exclusions} ({unregistered.size} entries)"
    else
      IO.eprintln "witness-candidates: refusing to overwrite an existing exclusions manifest"
      return 1
  if cfg.check then
    let exclusions? ← try
      let exclusions ← readManifest cfg.exclusions
      pure (some exclusions)
    catch e =>
      IO.eprintln s!"witness-candidates: {e.toString}"
      pure none
    let some exclusions := exclusions? | return (2 : UInt32)
    let mut failed := false
    for row in rows do
      let inReg := registry.contains row.name
      let inEx := exclusions.contains row.name
      if inReg == inEx then
        failed := true
        IO.eprintln s!"witness-candidates: ownership failure for {row.name} (registry={inReg}, exclusion={inEx})"
    for (name, _) in exclusions.toList do
      if !candidates.contains name then
        failed := true
        IO.eprintln s!"witness-candidates: stale exclusion {name}"
    let mut needsWitness : Array String := #[]
    for (name, (kind, _)) in exclusions.toList do
      if kind == "needs-witness" then needsWitness := needsWitness.push name
    if !needsWitness.isEmpty then
      IO.println s!"witness-candidates: actionable unregistered whole-routine/public CPS declarations: {needsWitness.size}"
      for name in needsWitness do IO.println s!"  NEEDS-WITNESS {name}"
    if failed then return 1
    IO.println "witness-candidates: check passed (every candidate has exactly one owner)"
  return 0

end WitnessCandidates

unsafe def main (args : List String) : IO UInt32 := WitnessCandidates.main args
