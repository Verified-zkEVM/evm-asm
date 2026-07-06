/-
  EvmAsm.Codegen.Cli

  Argument parsing and top-level `main` for `lake exe codegen`.

  Usage:
    codegen --program <name> [--halt sp1|linux93] [-o <basename>] [--asm-only]
    codegen --test-case <name> [--halt sp1|linux93] [-o <basename>] [--asm-only]
    codegen --list-test-cases

  The `--program` mode emits a registered `BuildUnit` from
  `Programs.lookupProgram`. The `--test-case` mode wraps a registered
  bytecode from `Tests.Cases.opcodeTestCases` through the M5b
  dispatcher (`tinyInterpRegistry`); used by the generic regression
  runner `scripts/codegen-opcodes-check.sh`.

  Writes `<basename>.s` and, unless `--asm-only`, also `<basename>.o` and
  `<basename>.elf` produced by `Driver.assembleAndLink`.
-/

import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs
import EvmAsm.Codegen.Driver
import EvmAsm.Codegen.Tests.Cases

namespace EvmAsm.Codegen.Cli

open EvmAsm.Codegen
open EvmAsm.Codegen.Driver

/-- Subcommand selected by the CLI flags. `program` wraps a named
    `BuildUnit`; `testCase` wraps a bytecode from the test registry
    through the dispatcher; `listTestCases` prints names line-by-line
    for the bash runner. -/
inductive Mode where
  | program
  | testCase
  | listTestCases

structure Options where
  mode     : Mode            := .program
  /-- Name of the program (when `mode = .program`) or test case
      (when `mode = .testCase`). Empty in `.listTestCases` mode. -/
  target   : String          := ""
  halt     : HaltConv        := .linux93
  outBase  : System.FilePath := "gen-out/out"
  asmOnly  : Bool            := false

def usage : String :=
  let progs := ", ".intercalate knownProgramNames
  let cases := ", ".intercalate Tests.testCaseNames
  "usage:\n" ++
  "  codegen --program <name> [--halt sp1|linux93] [-o <basename>] [--asm-only]\n" ++
  "  codegen --test-case <name> [--halt sp1|linux93] [-o <basename>] [--asm-only]\n" ++
  "  codegen --list-test-cases\n" ++
  s!"known programs: {progs}\n" ++
  s!"known test cases: {cases}"

def parseArgs : List String → Options → Except String Options
  | [], opts =>
      match opts.mode with
      | .listTestCases => .ok opts
      | _              =>
          if opts.target.isEmpty then .error "missing --program or --test-case"
          else .ok opts
  | "--program" :: v :: rest, opts =>
      parseArgs rest { opts with mode := .program, target := v }
  | "--test-case" :: v :: rest, opts =>
      parseArgs rest { opts with mode := .testCase, target := v }
  | "--list-test-cases" :: rest, opts =>
      parseArgs rest { opts with mode := .listTestCases }
  | "--halt" :: v :: rest, opts =>
      match HaltConv.ofString? v with
      | some hc => parseArgs rest { opts with halt := hc }
      | none    => .error s!"unknown --halt value: {v} (use sp1 | linux93)"
  | "-o" :: v :: rest, opts
  | "--out" :: v :: rest, opts =>
      parseArgs rest { opts with outBase := v }
  | "--asm-only" :: rest, opts =>
      parseArgs rest { opts with asmOnly := true }
  | "--help" :: _, _ | "-h" :: _, _ =>
      .error "help"
  | bad :: _, _ =>
      .error s!"unknown argument or missing value: {bad}"

/-- Common emit/assemble/link path shared by `--program` and `--test-case`. -/
def emitAndLink (unit : BuildUnit) (opts : Options) : IO UInt32 := do
  let text := emitBuildUnit opts.halt unit
  let asmPath : System.FilePath := opts.outBase.toString ++ ".s"
  writeAsmFile asmPath text
  IO.println s!"wrote {asmPath}"
  if opts.asmOnly then
    return 0
  try
    let (objPath, elfPath) ← assembleAndLink asmPath
    IO.println s!"wrote {objPath}"
    IO.println s!"wrote {elfPath}"
    return (0 : UInt32)
  catch e =>
    IO.eprintln s!"codegen: {e}"
    IO.eprintln "codegen: hint: install the riscv64 cross toolchain (e.g. `brew install riscv64-elf-binutils`) or pass --asm-only"
    return (1 : UInt32)

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error msg => do
      if msg ≠ "help" then IO.eprintln s!"codegen: {msg}"
      IO.eprintln usage
      return (if msg = "help" then 0 else 1)
  | .ok opts => do
      match opts.mode with
      | .listTestCases => do
          -- TSV: `<name>\t<expectedOutHex>\t<bytecode>` per line.
          -- The bytecode column lets the M8.5 runtime-bytecode runner
          -- pack a ziskemu `-i <file>` payload without re-parsing
          -- Lean. Backwards-compatible with the M6a 2-column reader
          -- as long as it uses `read -r name expected` (extra fields
          -- just get dropped).
          for tc in Tests.opcodeTestCases do
            -- M21..M31/selfdestruct-staging: 21-column TSV. Columns:
            --   1 name, 2 expectedOutHex, 3 bytecode, 4 calldata,
            --   5 storage, 6 blobBaseFee (M28), 7 blobHashes (M28),
            --   8 blockNumber (M29), 9 blockHashes (M29),
            --   10 env (simple-env trailer),
            --   11 expectedHaltKind,
            --   12 expectedPersistentLogLength (M24),
            --   13 expectedTransientLogLength (M24),
            --   14 expectedPostStorage (M25 — slot data at OUTPUT+56),
            --   15 expectedEventLogCount (M26 — OUTPUT+56),
            --   16 expectedEventLogFirst (M26 — descriptor at OUTPUT+64),
            --   17 gasLimit (M30 — pack-bytecode.py --gas),
            --   18 expectedReturnDataCopied (M31 — OUTPUT+248),
            --   19 expectedReturnDataLength (M31 — OUTPUT+64),
            --   20 expectedReturnDataHex (M31 — bytes at OUTPUT+72),
            --   21 expectedSelfdestructBeneficiary (OUTPUT+56).
            -- All cols beyond 3 are optional; the bash runner asserts
            -- only the ones with non-empty values.
            IO.println
              s!"{tc.name}\t{tc.expectedOutHex}\t{tc.bytecode}\t{tc.calldata}\t{tc.storage}\t{tc.blobBaseFee}\t{tc.blobHashes}\t{tc.blockNumber}\t{tc.blockHashes}\t{tc.env}\t{tc.expectedHaltKind}\t{tc.expectedPersistentLogLength}\t{tc.expectedTransientLogLength}\t{tc.expectedPostStorage}\t{tc.expectedEventLogCount}\t{tc.expectedEventLogFirst}\t{tc.gasLimit}\t{tc.expectedReturnDataCopied}\t{tc.expectedReturnDataLength}\t{tc.expectedReturnDataHex}\t{tc.expectedSelfdestructBeneficiary}"
          return 0
      | .program => do
          match lookupProgram opts.target with
          | none => do
              IO.eprintln s!"codegen: unknown program: {opts.target}"
              IO.eprintln usage
              return 1
          | some unit => emitAndLink unit opts
      | .testCase => do
          match Tests.lookupTestCase opts.target with
          | none => do
              IO.eprintln s!"codegen: unknown test case: {opts.target}"
              IO.eprintln usage
              return 1
          | some tc => emitAndLink (Tests.buildTestCaseUnit tc) opts

end EvmAsm.Codegen.Cli
