/-
  EvmAsm.Tests.Div128V5RandomCheck

  Random + adversarial differential tester for the v5 math model
  `div128Quot_v5` against a Nat-level reference (`q_true = min(2^64 - 1,
  (uHi*2^64 + uLo) / vTop)`). Bead `evm-asm-wbc4i.12` (V5.1.1) — the
  Layer-1 model test from the umbrella's layered testing strategy.

  Run via `lake exe div128-v5-check` (driven by `scripts/div128-v5-model-check.sh`).

  For each sampled `(uHi, uLo, vTop)` with `vTop` normalized (top bit set)
  and `uHi < vTop` (so quotient fits in 64 bits), this checks the v5
  Knuth-A window `q_true ≤ div128Quot_v5 ≤ q_true + 1`.

  Corpus:
  - PR #7080 `cePlus2_*` and `ceUnd_*` regression pins.
  - PR #7077 `ceWideUHi_*` regression pin.
  - Pseudo-random uniform 64-bit triples (deterministic LCG, reproducible).
  - Adversarial wide-uHi (sampled near `vTop * k` for k ∈ {0,1,2,3}).

  If any sample fails the v5 `+1` window, the binary exits with code 1
  and prints the failing inputs — block downstream V5.4 / V5.5 proof work
  until the model is fixed.
-/

module

public import EvmAsm.Evm64.DivMod.LoopDefs.IterV5

@[expose] public section

namespace EvmAsm.Tests.Div128V5RandomCheck

open EvmAsm.Evm64
open EvmAsm.Rv64

/-- Nat-level true quotient, capped at 2^64 - 1 (mirrors EVM's u64
    quotient semantics when uHi < vTop). -/
def trueQuot (uHi uLo vTop : Word) : Nat :=
  let dividend : Nat := uHi.toNat * 2^64 + uLo.toNat
  let divisor : Nat := vTop.toNat
  if divisor = 0 then 0
  else min (2^64 - 1) (dividend / divisor)

/-- A single check: returns `none` if the v5 result is in the Knuth-A
    `+1` window around `q_true`; otherwise `some (q_true, result)` with
    the failing values. -/
def checkOne (uHi uLo vTop : Word) : Option (Nat × Nat) :=
  let qt := trueQuot uHi uLo vTop
  let res := (div128Quot_v5 uHi uLo vTop).toNat
  if qt ≤ res ∧ res ≤ qt + 1 then none else some (qt, res)

/-- Deterministic LCG (Numerical Recipes constants) — generates 64-bit
    pseudo-random numbers without external dependencies. Seed should be
    non-zero. -/
def lcgNext (seed : UInt64) : UInt64 :=
  seed * 1664525 + 1013904223

/-- Sample a normalized vTop (top bit set). -/
def sampleVTop (seed : UInt64) : Word :=
  BitVec.ofNat 64 (seed.toNat ||| (1 <<< 63))

/-- Sample uHi < vTop. Done via masking. -/
def sampleUHiBelow (seed : UInt64) (vTop : Word) : Word :=
  let raw : Word := BitVec.ofNat 64 seed.toNat
  if BitVec.ult raw vTop then raw
  else BitVec.ofNat 64 (seed.toNat % (vTop.toNat + 1))

/-- One pseudo-random sample triple; returns `(uHi, uLo, vTop, nextSeed)`. -/
def randomSample (seed : UInt64) : Word × Word × Word × UInt64 :=
  let s1 := lcgNext seed
  let s2 := lcgNext s1
  let s3 := lcgNext s2
  let vTop := sampleVTop s1
  let uHi := sampleUHiBelow s2 vTop
  let uLo : Word := BitVec.ofNat 64 s3.toNat
  (uHi, uLo, vTop, s3)

/-- Fixed regression corpus from PR #7077 / PR #7080. Inputs are the
    pinned counterexamples that broke `div128Quot_v4`; under v5 they
    MUST satisfy the `+1` window. -/
def fixedCorpus : List (String × Word × Word × Word) := [
  ("ce_plus2",
    BitVec.ofNat 64 0x928ED4518F7DD083,
    BitVec.ofNat 64 0xC3887FC013FF1573,
    BitVec.ofNat 64 0x928ED451C34118C1),
  ("ce_undershoot",
    BitVec.ofNat 64 0x81A6C3EA81786CF7,
    BitVec.ofNat 64 0xAB97850C4B79C4F7,
    BitVec.ofNat 64 0x81A6C3EA83EB4E16),
  ("ce_wide_uHi",
    BitVec.ofNat 64 (2^63 + 2^33 + 2^31),
    BitVec.ofNat 64 0,
    BitVec.ofNat 64 (2^63 + 2^33 + 2^32 - 1))
]

/-- Run `n` random samples starting from `seed`. Returns the list of
    failures (empty if all pass). -/
def runRandom (n : Nat) (seed : UInt64) : List (Nat × Word × Word × Word × Nat × Nat) := Id.run do
  let mut failures := #[]
  let mut s := if seed = 0 then 1 else seed
  for i in [:n] do
    let (uHi, uLo, vTop, s') := randomSample s
    s := s'
    match checkOne uHi uLo vTop with
    | none => pure ()
    | some (qt, res) => failures := failures.push (i, uHi, uLo, vTop, qt, res)
  return failures.toList

/-- Run fixed-corpus checks. -/
def runFixed : List (String × Nat × Nat) := Id.run do
  let mut failures := #[]
  for (label, uHi, uLo, vTop) in fixedCorpus do
    match checkOne uHi uLo vTop with
    | none => pure ()
    | some (qt, res) => failures := failures.push (label, qt, res)
  return failures.toList

/-- Adversarial wide-uHi: for several vTop, sample uHi close to k·vTop_high. -/
def adversarialCorpus (seed : UInt64) (n : Nat) :
    List (Word × Word × Word) := Id.run do
  let mut out := #[]
  let mut s := if seed = 0 then 2 else seed
  for _ in [:n] do
    let s1 := lcgNext s
    let s2 := lcgNext s1
    let vTop := sampleVTop s1
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let kIdx := s2.toNat % 4
    let k : Word := BitVec.ofNat 64 (kIdx + 1)
    let baseUHi := k * dHi
    let delta : Word := BitVec.ofNat 64 ((lcgNext s2).toNat % 4)
    let uHi := baseUHi + delta - BitVec.ofNat 64 2
    let uLo : Word := BitVec.ofNat 64 (lcgNext (lcgNext s2)).toNat
    if BitVec.ult uHi vTop then
      out := out.push (uHi, uLo, vTop)
    s := lcgNext s2
  return out.toList

def runAdversarial (n : Nat) (seed : UInt64) :
    List (Word × Word × Word × Nat × Nat) := Id.run do
  let mut failures := #[]
  for (uHi, uLo, vTop) in adversarialCorpus seed n do
    match checkOne uHi uLo vTop with
    | none => pure ()
    | some (qt, res) => failures := failures.push (uHi, uLo, vTop, qt, res)
  return failures.toList

def runAll (nRandom nAdversarial : Nat) (seed : UInt64) : IO UInt32 := do
  let fixedFailures := runFixed
  let randomFailures := runRandom nRandom seed
  let adversarialFailures := runAdversarial nAdversarial (lcgNext seed)
  let total := fixedFailures.length + randomFailures.length + adversarialFailures.length
  if total = 0 then
    IO.println s!"PASS: {fixedCorpus.length} fixed + {nRandom} random + {nAdversarial} adversarial all in v5 +1 window"
    return 0
  IO.println s!"FAIL: {total} cases violate the v5 +1 window"
  for (label, qt, res) in fixedFailures do
    IO.println s!"  [fixed:{label}] q_true = {qt}, div128Quot_v5 = {res}"
  for (i, uHi, uLo, vTop, qt, res) in randomFailures do
    IO.println s!"  [random#{i}] uHi=0x{uHi.toNat.toDigits 16 |> String.ofList} uLo=0x{uLo.toNat.toDigits 16 |> String.ofList} vTop=0x{vTop.toNat.toDigits 16 |> String.ofList} q_true={qt} v5={res}"
  for (uHi, uLo, vTop, qt, res) in adversarialFailures do
    IO.println s!"  [adversarial] uHi=0x{uHi.toNat.toDigits 16 |> String.ofList} uLo=0x{uLo.toNat.toDigits 16 |> String.ofList} vTop=0x{vTop.toNat.toDigits 16 |> String.ofList} q_true={qt} v5={res}"
  return 1

def parseNat (s : String) (default : Nat) : Nat :=
  s.toNat?.getD default

def parseUInt64 (s : String) (default : UInt64) : UInt64 :=
  match s.toNat? with
  | some n => UInt64.ofNat n
  | none => default

def main (args : List String) : IO UInt32 := do
  let nRandom := match args with
    | a :: _ => parseNat a 10000
    | _ => 10000
  let nAdversarial := match args with
    | _ :: a :: _ => parseNat a 5000
    | _ => 5000
  let seed := match args with
    | _ :: _ :: a :: _ => parseUInt64 a 42
    | _ => 42
  IO.println s!"div128-v5-check: nRandom={nRandom} nAdversarial={nAdversarial} seed={seed}"
  runAll nRandom nAdversarial seed

end EvmAsm.Tests.Div128V5RandomCheck
