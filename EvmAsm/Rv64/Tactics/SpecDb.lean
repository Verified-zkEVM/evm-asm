/-
  EvmAsm.Rv64.Tactics.SpecDb

  Persistent database mapping instruction constructors to spec theorems.
  Used by `runBlock` (auto mode) to resolve specs automatically.

  ## Usage

  Tag single-instruction specs with `@[spec_gen_rv64]`:
  ```
  @[spec_gen_rv64]
  theorem lw_spec_gen_rv64 (rd rs1 : Reg) ... :
      cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.LW rd rs1 offset)) (...) (...) := ...
  ```

  The instruction constructor (e.g., `EvmAsm.Rv64.Instr.LW`) is auto-detected
  from the `CodeReq.singleton` argument, or (for backward compatibility) from
  an `instrAt` atom in the precondition. Supports `cpsTripleWithin`,
  `cpsBranchWithin`, `cpsNBranchWithin`, and `cpsHaltTripleWithin`; historical
  unbounded shapes are accepted while the migration is in progress.

  ## Diagnostics

  ```
  #spec_db_rv64  -- prints all registered specs grouped by instruction
  ```

  ## Requirements for `@[spec_gen_rv64]` specs

  - Must be a bounded CPS spec (`cpsTripleWithin`, `cpsBranchWithin`,
    `cpsNBranchWithin`, or `cpsHaltTripleWithin`) or a historical unbounded
    compatibility wrapper during migration
  - The CodeReq argument must be `CodeReq.singleton addr instr`, OR
    the precondition must contain an `instrAt` (`↦ᵢ`) atom (backward compat)
  - The instruction must be a concrete constructor application (e.g., `.ADD .x7 .x7 .x6`)
  - Multiple specs per instruction are allowed (tried in registration order)
-/

import Lean

open Lean Meta

namespace EvmAsm.Rv64.Tactics

-- ============================================================================
-- Section 1: Data Structures
-- ============================================================================

/-- Entry in the instruction spec database.
    Maps an instruction constructor to a spec theorem. -/
structure SpecGenEntry where
  /-- Full name of the instruction constructor (e.g., `EvmAsm.Rv64.Instr.ADD`) -/
  instrCtor : Name
  /-- Full name of the spec theorem (e.g., `EvmAsm.add_spec_gen_rv64_rd_eq_rs1`) -/
  specName : Name
  deriving Inhabited, BEq

-- ============================================================================
-- Section 2: Persistent Environment Extension
-- ============================================================================

/-- The persistent environment extension storing registered spec entries. -/
initialize specGenExt : SimplePersistentEnvExtension SpecGenEntry (Array SpecGenEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state entry => state.push entry
    addImportedFn := fun entries => entries.foldl (init := #[]) fun acc es => acc ++ es
  }

/-- Look up all spec entries for a given instruction constructor name. -/
def findSpecsForInstr (env : Environment) (instrCtor : Name) : Array SpecGenEntry :=
  (specGenExt.getState env).filter (·.instrCtor == instrCtor)

/-- Get all registered spec entries. -/
def getAllSpecs (env : Environment) : Array SpecGenEntry :=
  specGenExt.getState env

-- ============================================================================
-- Section 3: Type Parsing (no MetaM needed)
-- ============================================================================

/-- Flatten a nested `sepConj` expression to a list of atoms (simplified, pure). -/
private partial def flattenSepConjPure (e : Expr) : List Expr :=
  if e.isAppOfArity `EvmAsm.Rv64.sepConj 2 then
    let args := e.getAppArgs
    flattenSepConjPure args[0]! ++ flattenSepConjPure args[1]!
  else [e]

/-- Find the first `instrAt addr instr` atom and return the constructor name of `instr`. -/
private def findInstrCtorInPre (pre : Expr) : Option Name :=
  let atoms := flattenSepConjPure pre
  atoms.findSome? fun atom =>
    if atom.isAppOfArity `EvmAsm.Rv64.instrAt 2 then
      let instr := atom.getAppArgs[1]!
      let head := instr.getAppFn
      match head with
      | .const name _ => some name
      | _ => none
    else none

/-- Extract the instruction constructor from `CodeReq.singleton addr instr`. -/
private def findInstrCtorInCodeReq (cr : Expr) : Option Name :=
  if cr.isAppOfArity `EvmAsm.Rv64.CodeReq.singleton 2 then
    let instr := cr.getAppArgs[1]!
    let head := instr.getAppFn
    match head with
    | .const name _ => some name
    | _ => none
  else none

/-- Extract the instruction constructor from a spec theorem's type.
    Strips ∀ binders and looks for bounded CPS specs.
    Checks both the `cr` (CodeReq.singleton) argument and the `instrAt` atoms
    in the precondition for backward compatibility. -/
private partial def extractInstrCtorFromType (type : Expr) : Option Name :=
  match type with
  | .forallE _ _ body _ => extractInstrCtorFromType body
  | _ =>
    -- Try cpsTripleWithin nSteps entry exit cr pre post (6 args)
    if type.isAppOfArity `EvmAsm.Rv64.cpsTripleWithin 6 then
      let cr := type.getAppArgs[3]!
      let pre := type.getAppArgs[4]!
      findInstrCtorInCodeReq cr |>.orElse fun () => findInstrCtorInPre pre
    -- Try cpsBranchWithin nSteps addr cr pre takenTarget takenPost notTakenTarget notTakenPost (8 args)
    else if type.isAppOfArity `EvmAsm.Rv64.cpsBranchWithin 8 then
      let cr := type.getAppArgs[2]!
      let pre := type.getAppArgs[3]!
      findInstrCtorInCodeReq cr |>.orElse fun () => findInstrCtorInPre pre
    -- Try cpsNBranchWithin nSteps addr cr pre exits (5 args)
    else if type.isAppOfArity `EvmAsm.Rv64.cpsNBranchWithin 5 then
      let cr := type.getAppArgs[2]!
      let pre := type.getAppArgs[3]!
      findInstrCtorInCodeReq cr |>.orElse fun () => findInstrCtorInPre pre
    -- Try cpsHaltTripleWithin nSteps addr cr pre post (5 args)
    else if type.isAppOfArity `EvmAsm.Rv64.cpsHaltTripleWithin 5 then
      let cr := type.getAppArgs[2]!
      let pre := type.getAppArgs[3]!
      findInstrCtorInCodeReq cr |>.orElse fun () => findInstrCtorInPre pre
    else none

-- ============================================================================
-- Section 4: Attribute Registration
-- ============================================================================

/-- `@[spec_gen_rv64]` attribute: registers an instruction spec in the database.
    The instruction constructor is auto-detected from either the `CodeReq.singleton`
    argument or (for backward compatibility) from an `instrAt` atom in the precondition.

    Usage:
    ```
    @[spec_gen_rv64]
    theorem lw_spec_gen_rv64 ... : cpsTripleWithin 1 ... (CodeReq.singleton addr (.LW ...)) ... ... := ...
    ```
-/
initialize registerBuiltinAttribute {
  name := `spec_gen_rv64
  descr := "Register an instruction spec for automatic lookup by runBlock"
  applicationTime := .afterTypeChecking
  add := fun declName _stx _attrKind => do
    let env ← getEnv
    let some info := env.find? declName
      | throwError "spec_gen_rv64: unknown declaration {declName}"
    match extractInstrCtorFromType info.type with
    | some instrCtor =>
      modifyEnv fun env => specGenExt.addEntry env { instrCtor, specName := declName }
    | none =>
      throwError "spec_gen_rv64: could not detect instruction constructor in {declName}.\n\
        The theorem must be a cpsTripleWithin/cpsBranchWithin/cpsNBranchWithin/cpsHaltTripleWithin \
        with a CodeReq.singleton \
        or instrAt atom for the instruction."
}

-- ============================================================================
-- Section 5: Diagnostics
-- ============================================================================

/-- `#spec_db_rv64` command: print all registered instruction specs. -/
elab "#spec_db_rv64" : command => do
  let env ← getEnv
  let entries := getAllSpecs env
  if entries.isEmpty then
    logInfo "No specs registered. Use @[spec_gen_rv64] to register instruction specs."
  else
    let mut msg := m!"Registered instruction specs ({entries.size} total):\n"
    -- Group by instruction constructor
    let mut seen : Std.HashMap Name (Array Name) := {}
    for entry in entries do
      match seen.get? entry.instrCtor with
      | some arr => seen := seen.insert entry.instrCtor (arr.push entry.specName)
      | none => seen := seen.insert entry.instrCtor #[entry.specName]
    for (instrCtor, specs) in seen.toList do
      msg := msg ++ m!"  {instrCtor}:\n"
      for spec in specs do
        msg := msg ++ m!"    {spec}\n"
    logInfo msg

end EvmAsm.Rv64.Tactics
