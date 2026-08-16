/-
  EvmAsm.Codegen.Programs.FileSizeGuard

  Elaboration-time guard for the codegen program registry and sibling helper
  modules. This lives outside `Programs.lean` so the registry hub is not forced
  to carry the entire guard implementation and path list.
-/

import Lean

namespace EvmAsm.Codegen.Programs.FileSizeGuard

partial def collectLeanFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let entries ← root.readDir
  entries.foldlM (init := #[]) fun acc entry => do
    if ← entry.path.isDir then
      let nested ← collectLeanFiles entry.path
      pure (acc ++ nested)
    else if entry.path.extension == some "lean" then
      pure (acc.push entry.path)
    else
      pure acc

def registryHub : System.FilePath :=
  System.FilePath.mk "EvmAsm/Codegen/Programs/Imports.lean"

def programsDir : System.FilePath :=
  System.FilePath.mk "EvmAsm/Codegen/Programs"

def hardCap : Nat := 1500

/-! ## File-size guard

    Hard cap of 1500 lines on `Programs.lean` and every sibling under
    `EvmAsm/Codegen/Programs/`, to keep the registry hub and the extracted
    submodules from spiralling. When this guard trips, split a cluster of
    `*Function` / `zisk*` defs into a new or existing submodule and import it
    from `Programs.lean`.

    Runs at elaboration time via `#eval`; adds zero runtime cost.

    Line-count semantics (must match `scripts/check-file-size.sh` / `wc -l`):
    - `wc -l` counts newline characters.
    - `String.splitOn "\n" |>.length` counts segments, which is one larger
      exactly when the file ends with a newline — every well-formed file in
      this tree. Using that here falsely rejected a compliant 1500-line file
      (`RlpWalkNextStrictFuelMachineCont.lean`) while the shell gate passed. -/

/-- Line count matching `wc -l`: number of newline characters in `contents`. -/
def lineCountMatchingWc (contents : String) : Nat :=
  contents.foldl (init := 0) fun n c => if c == '\n' then n + 1 else n

#eval show IO Unit from do
  let programFiles ← collectLeanFiles programsDir
  let paths := #[registryHub] ++ programFiles
  for path in paths do
    let contents ← IO.FS.readFile path
    let lineCount := lineCountMatchingWc contents
    if lineCount > hardCap then
      throw <| IO.userError <|
        s!"{path} has {lineCount} lines; hard cap is {hardCap}. " ++
        "Extract a helper cluster into a new submodule under " ++
        "EvmAsm/Codegen/Programs/ and import it from Programs.lean."

end EvmAsm.Codegen.Programs.FileSizeGuard
