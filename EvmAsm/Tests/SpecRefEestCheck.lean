/-
  EvmAsm.Tests.SpecRefEestCheck

  EEST conformance driver for the SpecRef reference model
  (`EvmAsm.Stateless.SpecRef`). Runs `SpecRef.run_stateless_guest` on the
  *same* ziskemu-framed fixture inputs produced by
  `scripts/eest-stateless-to-input.py` (the fixture set
  `scripts/codegen-eest-stateless-check.sh` exercises) and writes the
  105-byte `StatelessValidationResult` for the harness
  (`scripts/eest-specref-check.sh`) to compare against the fixture's
  `statelessOutputBytes`.

  Why this exists: SpecRef is a pure-Lean functional port of the Amsterdam
  stateless-guest Python spec. This driver ties it to the canonical EEST
  conformance fixtures so regressions in the port's SSZ codec / NPR-root
  hashing / header / chain-config / witness-assembly path surface without
  spinning up ziskemu. The execution seam is the DEFAULT
  (`elExecuteHybrid`, `s1d19.5`): the full ported `elExecute`, falling
  back to the sound-for-accepts static shell only on contact with a
  not-yet-ported precompile — so the `succ` bit is a real verdict and
  is expected to match, alongside the pre-execution regions (NPR root,
  chain-config echo).

  This module lives under `EvmAsm/Tests/` (the unverified escape-hatch
  layer) and is consumed only by the `specref-eest-check` exe; it is never
  imported into any proof. Run via `lake exe specref-eest-check`.
-/

import EvmAsm.Stateless.SpecRef

namespace EvmAsm.Tests.SpecRefEestCheck

open EvmAsm.Stateless.SpecRef

-- ============================================================================
-- Byte list <-> ByteArray (binary file interchange)
-- ============================================================================

/-- `List Byte` (SpecRef `Bytes`) from a `ByteArray` (file content). -/
def bytesOfByteArray (ba : ByteArray) : Bytes :=
  ba.toList.map fun b => BitVec.ofNat 8 b.toNat

/-- `ByteArray` (file content) from a `List Byte`. -/
def byteArrayOfBytes (bs : Bytes) : ByteArray :=
  ⟨bs.map (·.toNat.toUInt8) |>.toArray⟩

-- ============================================================================
-- ziskemu input framing (inverse of `pack_ziskemu_input`)
-- ============================================================================
-- `pack_ziskemu_input` (scripts/eest-stateless-to-input.py:58) emits
-- `<u64 LE length><blob><zero pad to 8>`. We recover the guest-visible
-- `statelessInputBytes` blob by reading the 8-byte little-endian length
-- prefix and taking the next `len` bytes. This is host transport only;
-- execution-specs `run_stateless_guest` consumes just the blob.

/-- Decode an 8-byte little-endian u64 length prefix. -/
def decodeLeU64 (lenPrefix : Bytes) : Option Nat :=
  if lenPrefix.length < 8 then none
  else
    let rev := (lenPrefix.take 8).reverse
    some (rev.foldl (fun acc b => acc * 256 + b.toNat) 0)

/-- Strip the ziskemu framing and return the guest-visible blob, or the
    reason the framing is malformed. -/
def unpackZiskemuInput (packed : Bytes) : Except String Bytes := do
  if packed.length < 8 then
    throw s!"packed input too short: {packed.length}"
  let n ← match decodeLeU64 (packed.take 8) with
    | some n => pure n
    | none => throw "packed input: bad length prefix"
  let endIdx := 8 + n
  if packed.length < endIdx then
    throw s!"packed input truncated: length={n}, bytes={packed.length}"
  pure (packed.drop 8 |>.take n)

-- ============================================================================
-- CLI
-- ============================================================================
-- `specref-eest-check <input_file> <output_file>`
--   exit 0 + writes the 105-byte result to <output_file> on success.
--   exit 2 + stderr message on malformed framing.

def usage : String :=
  "usage: specref-eest-check <input_file> <output_file>"

def main (args : List String) : IO UInt32 := do
  match args with
  | [inputFile, outputFile] =>
    let packedBytes ← IO.FS.readBinFile ⟨inputFile⟩
    let packed := bytesOfByteArray packedBytes
    match unpackZiskemuInput packed with
    | .error msg =>
      IO.eprintln s!"specref-eest-check: framing error ({inputFile}): {msg}"
      return 2
    | .ok blob =>
      let out := run_stateless_guest blob
      IO.FS.writeBinFile ⟨outputFile⟩ (byteArrayOfBytes out)
      return 0
  | _ =>
    IO.eprintln usage
    return 1

end EvmAsm.Tests.SpecRefEestCheck
