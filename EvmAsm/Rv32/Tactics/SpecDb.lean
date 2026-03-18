/-
  EvmAsm.Rv32.Tactics.SpecDb

  Persistent database mapping instruction constructors to spec theorems.
  Used by `runBlock` (auto mode) to resolve specs automatically.

  ## Usage

  Tag single-instruction specs with `@[spec_gen]`:
  ```
  @[spec_gen]
  theorem lw_spec_gen (rd rs1 : Reg) ... :
      cpsTriple addr (addr + 4)
        ((addr ↦ᵢ .LW rd rs1 offset) ** ...) (...) := ...
  ```

  The instruction constructor (e.g., `EvmAsm.Instr.LW`) is auto-detected
  from the `instrAt` atom in the precondition. Supports `cpsTriple`,
  `cpsBranch`, and `cpsHaltTriple`.

  ## Diagnostics

  ```
  #spec_db  -- prints all registered specs grouped by instruction
  ```

  ## Requirements for `@[spec_gen]` specs

  - Must be a `cpsTriple`, `cpsBranch`, or `cpsHaltTriple`
  - Precondition must contain exactly one `instrAt` (`↦ᵢ`) atom
  - The instruction must be a concrete constructor application (e.g., `.ADD .x7 .x7 .x6`)
  - Multiple specs per instruction are allowed (tried in registration order)
-/

import Lean

open Lean Meta

namespace EvmAsm.Tactics

-- ============================================================================
-- Section 1: Data Structures
-- ============================================================================

/-- Entry in the instruction spec database.
    Maps an instruction constructor to a spec theorem. -/
structure SpecGenEntry where
  /-- Full name of the instruction constructor (e.g., `EvmAsm.Instr.ADD`) -/
  instrCtor : Name
  /-- Full name of the spec theorem (e.g., `EvmAsm.add_spec_gen_rd_eq_rs1`) -/
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
  if e.isAppOfArity `EvmAsm.sepConj 2 then
    let args := e.getAppArgs
    flattenSepConjPure args[0]! ++ flattenSepConjPure args[1]!
  else [e]

/-- Find the first `instrAt addr instr` atom and return the constructor name of `instr`.
    Also checks `CodeReq.singleton addr instr` for the new CodeReq-based specs. -/
private def findInstrCtorInPre (pre : Expr) : Option Name :=
  let atoms := flattenSepConjPure pre
  atoms.findSome? fun atom =>
    if atom.isAppOfArity `EvmAsm.instrAt 2 then
      let instr := atom.getAppArgs[1]!
      let head := instr.getAppFn
      match head with
      | .const name _ => some name
      | _ => none
    else none

/-- Extract the instruction constructor from a CodeReq expression.
    Handles `CodeReq.singleton addr instr` — returns the constructor name of `instr`. -/
private def findInstrCtorInCr (cr : Expr) : Option Name :=
  if cr.isAppOfArity `EvmAsm.CodeReq.singleton 2 then
    let instr := cr.getAppArgs[1]!
    let head := instr.getAppFn
    match head with
    | .const name _ => some name
    | _ => none
  else none

/-- Extract the instruction constructor from a spec theorem's type.
    Strips ∀ binders and looks for `cpsTriple _ _ cr _ _` (5 args, CodeReq in position 2)
    or the legacy `instrAt`-in-precondition patterns. -/
private partial def extractInstrCtorFromType (type : Expr) : Option Name :=
  match type with
  | .forallE _ _ body _ => extractInstrCtorFromType body
  | _ =>
    -- New style: cpsTriple entry exit cr P Q (5 args), cr is index 2
    if type.isAppOfArity `EvmAsm.cpsTriple 5 then
      findInstrCtorInCr type.getAppArgs[2]!
    -- New style: cpsBranch entry cr P exit_t Q_t exit_f Q_f (7 args), cr is index 1
    else if type.isAppOfArity `EvmAsm.cpsBranch 7 then
      findInstrCtorInCr type.getAppArgs[1]!
    -- New style: cpsHaltTriple entry cr P Q (4 args), cr is index 1
    else if type.isAppOfArity `EvmAsm.cpsHaltTriple 4 then
      findInstrCtorInCr type.getAppArgs[1]!
    -- Legacy: cpsTriple entry exit pre post (4 args), instrAt in pre
    else if type.isAppOfArity `EvmAsm.cpsTriple 4 then
      findInstrCtorInPre type.getAppArgs[2]!
    -- Legacy: cpsBranch addr pre takenTarget takenPost notTakenTarget notTakenPost (6 args)
    else if type.isAppOfArity `EvmAsm.cpsBranch 6 then
      findInstrCtorInPre type.getAppArgs[1]!
    -- Legacy: cpsHaltTriple addr pre post (3 args)
    else if type.isAppOfArity `EvmAsm.cpsHaltTriple 3 then
      findInstrCtorInPre type.getAppArgs[1]!
    else none

-- ============================================================================
-- Section 4: Attribute Registration
-- ============================================================================

/-- `@[spec_gen]` attribute: registers an instruction spec in the database.
    The instruction constructor is auto-detected from the theorem's precondition.

    Usage:
    ```
    @[spec_gen]
    theorem lw_spec_gen ... : cpsTriple ... ((addr ↦ᵢ .LW ...) ** ...) ... := ...
    ```
-/
initialize registerBuiltinAttribute {
  name := `spec_gen
  descr := "Register an instruction spec for automatic lookup by runBlock"
  applicationTime := .afterTypeChecking
  add := fun declName _stx _attrKind => do
    let env ← getEnv
    let some info := env.find? declName
      | throwError "spec_gen: unknown declaration {declName}"
    match extractInstrCtorFromType info.type with
    | some instrCtor =>
      modifyEnv fun env => specGenExt.addEntry env { instrCtor, specName := declName }
    | none =>
      throwError "spec_gen: could not detect instruction constructor in {declName}.\n\
        The theorem must be a cpsTriple/cpsBranch/cpsHaltTriple with an instrAt atom in its precondition."
}

-- ============================================================================
-- Section 5: Diagnostics
-- ============================================================================

/-- `#spec_db` command: print all registered instruction specs. -/
elab "#spec_db" : command => do
  let env ← getEnv
  let entries := getAllSpecs env
  if entries.isEmpty then
    logInfo "No specs registered. Use @[spec_gen] to register instruction specs."
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

end EvmAsm.Tactics
