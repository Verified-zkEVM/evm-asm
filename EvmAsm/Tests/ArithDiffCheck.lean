/-
  EvmAsm.Tests.ArithDiffCheck

  Boundary-biased differential fuzzer for the six EVM arithmetic opcodes
  whose RISC-V lowering is the historical home of DIV-class bugs:
  `div`, `mod`, `sdiv`, `smod`, `mulmod`, `addmod`. Phase 3 deliverable D1
  (report R-E1) of the agent-progress-steering rollout.

  Driven by `scripts/fuzz-arith-diff.sh`. Two layers, per the report's
  PR-vs-nightly split:

  * PR fast-path (this binary, default mode): compare the executable
    `EvmWord.{div,mod,sdiv,smod,mulmod,addmod}` against an INDEPENDENT
    Nat/Int reference, over operands deliberately biased toward the rare
    paths uniform fuzzing misses — sign boundaries (±2^255), limb
    boundaries (2^64 / 2^128 / 2^192 ± 1), 4-limb divisors with a large
    top word (the `b.getLimbN 3 ≠ 0` case the v4 DIV proof EXCLUDED), and
    the Knuth Algorithm D `qhat`-overestimate + add-back regime. Plus a
    pass over the permanent regression corpus.

  * Nightly (`scripts/fuzz-arith-diff.sh --python`): the execution-specs
    Python EVM is the authoritative oracle; new mismatches are appended to
    `tests/fuzz-corpus/arith/corpus.jsonl` (the `emit` mode below feeds it
    the `EvmWord.*` results). The corpus carries the oracle's verdict in
    its `expected` field, so the PR fast-path re-checks against the frozen
    oracle WITHOUT needing Python at PR time.

  The Nat/Int reference is genuinely independent of the BitVec.sdiv /
  BitVec.srem / toNat-mod implementations the proofs use, so a divergence
  is a real cross-spec signal — never imported into any proof / the
  trusted base (this module lives under EvmAsm/Tests/, consumed only by
  the `arith-diff-check` exe).

  Run via `lake exe arith-diff-check` (see the script for modes).
-/

import EvmAsm.Evm64.EvmWordArith

namespace EvmAsm.Tests.ArithDiffCheck

open EvmAsm.Evm64

/-- `2^256` and `2^255` as `Nat` literals (sign boundary). -/
def two256 : Nat := 2 ^ 256
def two255 : Nat := 2 ^ 255

-- ============================================================================
-- The six fuzzed opcodes
-- ============================================================================

inductive ArithOp
  | div | mod | sdiv | smod | mulmod | addmod
  deriving Repr, DecidableEq, BEq, Inhabited

def ArithOp.name : ArithOp → String
  | .div => "div" | .mod => "mod" | .sdiv => "sdiv"
  | .smod => "smod" | .mulmod => "mulmod" | .addmod => "addmod"

def ArithOp.ofName? (s : String) : Option ArithOp :=
  match s with
  | "div" => some .div | "mod" => some .mod | "sdiv" => some .sdiv
  | "smod" => some .smod | "mulmod" => some .mulmod | "addmod" => some .addmod
  | _ => none

/-- Whether the op consumes the third operand `n` (MULMOD / ADDMOD). -/
def ArithOp.isTernary : ArithOp → Bool
  | .mulmod | .addmod => true
  | _ => false

def allOps : List ArithOp := [.div, .mod, .sdiv, .smod, .mulmod, .addmod]

-- ============================================================================
-- Independent Nat/Int reference (the in-Lean oracle for the PR fast-path)
-- ============================================================================

/-- Signed (two's-complement) interpretation of a 256-bit value `x < 2^256`. -/
def toSigned (x : Nat) : Int :=
  if x < two255 then (x : Int) else (x : Int) - (two256 : Int)

/-- Reduce a signed result back into `[0, 2^256)` (two's-complement wrap).
    `Int.emod` with a positive modulus is always non-negative. -/
def wrap256 (i : Int) : Nat :=
  (i % (two256 : Int)).toNat

/-- The reference result, computed independently of the BitVec ops.
    `a`, `b`, `n` are assumed `< 2^256` (callers reduce). -/
def reference (op : ArithOp) (a b n : Nat) : Nat :=
  match op with
  | .div    => if b = 0 then 0 else a / b
  | .mod    => if b = 0 then 0 else a % b
  | .sdiv   => if b = 0 then 0 else wrap256 (Int.tdiv (toSigned a) (toSigned b))
  | .smod   => if b = 0 then 0 else wrap256 (Int.tmod (toSigned a) (toSigned b))
  | .mulmod => if n = 0 then 0 else (a * b) % n
  | .addmod => if n = 0 then 0 else (a + b) % n

/-- The result produced by the executable `EvmWord.*` spec functions (the
    same definitions the proofs reason about). -/
def evmWordResult (op : ArithOp) (a b n : Nat) : Nat :=
  let aw : EvmWord := BitVec.ofNat 256 a
  let bw : EvmWord := BitVec.ofNat 256 b
  let nw : EvmWord := BitVec.ofNat 256 n
  match op with
  | .div    => (EvmWord.div aw bw).toNat
  | .mod    => (EvmWord.mod aw bw).toNat
  | .sdiv   => (EvmWord.sdiv aw bw).toNat
  | .smod   => (EvmWord.smod aw bw).toNat
  | .mulmod => (EvmWord.mulmod aw bw nw).toNat
  | .addmod => (EvmWord.addmod aw bw nw).toNat

/-- A single differential check against the reference. Returns `none` on
    agreement, else `some (evmWord, reference)`. -/
def checkRef (op : ArithOp) (a b n : Nat) : Option (Nat × Nat) :=
  let got := evmWordResult op a b n
  let want := reference op a b n
  if got = want then none else some (got, want)

-- ============================================================================
-- Hex encode / decode (corpus interchange; no external deps)
-- ============================================================================

def toHex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Parse a hex (optionally `0x`-prefixed) string to `Nat`. Works on
    `List Char` to stay clear of the `String.Slice`-returning String API. -/
def parseHex? (s0 : String) : Option Nat :=
  let cs := match s0.toList with
    | '0' :: 'x' :: r => r
    | '0' :: 'X' :: r => r
    | r => r
  match cs with
  | [] => none
  | _ => cs.foldlM (fun acc c => (hexDigit? c).map (acc * 16 + ·)) 0

/-- The suffix of `l` immediately after the first occurrence of `pat`. -/
def afterSublist (pat l : List Char) : Option (List Char) :=
  if pat.isPrefixOf l then some (l.drop pat.length)
  else match l with
    | [] => none
    | _ :: t => afterSublist pat t

/-- Extract the string value of `"key":"value"` from one JSON object line.
    Deliberately minimal: the corpus schema is fixed and flat, with no
    nested objects or escaped quotes. -/
def jsonField? (line key : String) : Option String :=
  let pat := ('"' :: key.toList) ++ ['"']
  match afterSublist pat line.toList with
  | none => none
  | some rest =>
      match rest.dropWhile (· ≠ '"') with
      | [] => none
      | _ :: valStart => some (String.ofList (valStart.takeWhile (· ≠ '"')))

/-- ASCII trim that returns a `String` (the core `String.trim` now returns
    a `String.Slice`). -/
def trimStr (s : String) : String :=
  let ws (c : Char) : Bool := c == ' ' ∨ c == '\t' ∨ c == '\r' ∨ c == '\n'
  String.ofList (((s.toList.dropWhile ws).reverse.dropWhile ws).reverse)

/-- A double-quote as a one-character string (avoids `\"` inside `s!`). -/
def dq : String := "\""

/-- Render one corpus/results JSON object line by concatenation. -/
def jsonObjLine (fields : List (String × String)) : String :=
  let kv : String × String → String := fun (k, v) => dq ++ k ++ dq ++ ":" ++ dq ++ v ++ dq
  "{" ++ String.intercalate "," (fields.map kv) ++ "}"

-- ============================================================================
-- Deterministic operand generation (boundary-biased)
-- ============================================================================

/-- 64-bit LCG (Knuth MMIX constants); no external randomness. -/
def lcgNext (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- Draw one full 256-bit value from four LCG limbs. Returns the value and
    the advanced seed. -/
def draw256 (s : UInt64) : Nat × UInt64 :=
  let s1 := lcgNext s
  let s2 := lcgNext s1
  let s3 := lcgNext s2
  let s4 := lcgNext s3
  let v := s1.toNat + s2.toNat * 2 ^ 64 + s3.toNat * 2 ^ 128 + s4.toNat * 2 ^ 192
  (v % two256, s4)

/-- "Interesting" boundary values: sign edges, limb boundaries, and small
    magnitudes — the corners uniform sampling almost never hits. -/
def boundaryPool : List Nat :=
  let edges : List Nat := [0, 1, 2, 3]
  let near (p : Nat) : List Nat := [p - 1, p, p + 1]
  edges
    ++ near two255            -- signed min/around it
    ++ near (2 ^ 64) ++ near (2 ^ 128) ++ near (2 ^ 192)  -- limb boundaries
    ++ [two256 - 1, two256 - 2]                            -- unsigned max
    ++ [two256 - two255]                                   -- exactly -2^255 pattern
    -- a normalized 4-limb divisor: top limb just below 2^64, all limbs set
    ++ [(2 ^ 256 - 1)]
    ++ [((2 ^ 64 - 1) * 2 ^ 192) + (2 ^ 128) + (2 ^ 64) + 7]

/-- Knuth add-back / `qhat`-overestimate bias for DIV/MOD: a normalized
    divisor `b` with a large nonzero top limb (the `getLimbN 3 ≠ 0`,
    word-count-4 regime the v4 proof excluded), and a dividend `a ≈ k·b`
    so the long division produces a near-maximal partial remainder. -/
def addbackPair (s : UInt64) : (Nat × Nat × UInt64) :=
  let (bRaw, s1) := draw256 s
  -- force the top bit set (normalized) and a nonzero top limb
  let b := (bRaw ||| two255 ||| (1 * 2 ^ 192)) % two256
  let (kRaw, s2) := draw256 s1
  let k := (kRaw % 3) + 1
  let (dRaw, s3) := draw256 s2
  let delta := dRaw % 5
  let a := (b * k + delta) % two256
  (a, b, s3)

structure Case where
  a : Nat
  b : Nat
  n : Nat
  deriving Inhabited

/-- Cartesian-ish sampling from the boundary pool plus random + add-back
    cases. Caller picks the per-op interpretation of the third slot. -/
def genCases (nRandom nBias : Nat) (seed : UInt64) : Array Case := Id.run do
  let pool := boundaryPool.toArray
  let np := pool.size
  let mut out : Array Case := #[]
  let mut s := if seed = 0 then 1 else seed
  -- boundary × boundary (with a third boundary draw for n)
  for i in [:np] do
    for j in [:np] do
      let ai := pool[i]!
      let bj := pool[j]!
      s := lcgNext s
      let nk := pool[(s.toNat) % np]!
      out := out.push ⟨ai, bj, nk⟩
  -- random full-256 triples
  for _ in [:nRandom] do
    let (a, s1) := draw256 s
    let (b, s2) := draw256 s1
    let (n, s3) := draw256 s2
    s := s3
    out := out.push ⟨a, b, n⟩
  -- add-back biased DIV/MOD pairs (n drawn for ternary reuse)
  for _ in [:nBias] do
    let (a, b, s1) := addbackPair s
    let (n, s2) := draw256 s1
    s := s2
    out := out.push ⟨a, b, n⟩
  return out

-- ============================================================================
-- Runners
-- ============================================================================

structure Failure where
  op : ArithOp
  a : Nat
  b : Nat
  n : Nat
  got : Nat
  want : Nat

def Failure.render (f : Failure) : String :=
  let args :=
    if f.op.isTernary then
      s!"a={toHex f.a} b={toHex f.b} n={toHex f.n}"
    else
      s!"a={toHex f.a} b={toHex f.b}"
  s!"  [{f.op.name}] {args}  EvmWord={toHex f.got}  reference={toHex f.want}"

/-- Fuzz every op over the generated cases against the Nat/Int reference. -/
def runFuzz (nRandom nBias : Nat) (seed : UInt64) : Array Failure := Id.run do
  let cases := genCases nRandom nBias seed
  let mut fails : Array Failure := #[]
  for op in allOps do
    for c in cases do
      match checkRef op c.a c.b c.n with
      | none => pure ()
      | some (got, want) => fails := fails.push ⟨op, c.a, c.b, c.n, got, want⟩
  return fails

structure CorpusEntry where
  op : ArithOp
  a : Nat
  b : Nat
  n : Nat
  expected : Nat

def parseCorpusLine? (line : String) : Option CorpusEntry := do
  let t := trimStr line
  if t.isEmpty ∨ t.startsWith "#" ∨ t.startsWith "//" then none
  else
    let op ← ArithOp.ofName? (← jsonField? t "op")
    let a ← parseHex? (← jsonField? t "a")
    let b ← parseHex? (← jsonField? t "b")
    let n ← parseHex? ((jsonField? t "n").getD "0x0")
    let expected ← parseHex? (← jsonField? t "expected")
    some ⟨op, a, b, n, expected⟩

/-- Re-verify every corpus entry: `EvmWord.*` must still equal the frozen
    `expected` (the execution-specs oracle's recorded verdict). -/
def runCorpus (entries : List CorpusEntry) : Array Failure := Id.run do
  let mut fails : Array Failure := #[]
  for e in entries do
    let got := evmWordResult e.op e.a e.b e.n
    if got ≠ e.expected then
      fails := fails.push ⟨e.op, e.a, e.b, e.n, got, e.expected⟩
  return fails

def readCorpus (path : String) : IO (List CorpusEntry) := do
  if !(← System.FilePath.pathExists path) then
    return []
  let content ← IO.FS.readFile path
  let mut entries : List CorpusEntry := []
  for line in content.splitOn "\n" do
    match parseCorpusLine? line with
    | some e => entries := e :: entries
    | none => pure ()
  return entries.reverse

-- ============================================================================
-- Curated DIV-class seed operands (the permanent edge-case pins)
-- ============================================================================

/-- Hand-picked operands stressing the corners that produce DIV-class bugs:
    zero divisor, 4-limb divisors with a large top word (the
    `b.getLimbN 3 ≠ 0` regime the v4 DIV proof EXCLUDED), Knuth add-back
    (`a ≈ k·b`), the SDIV signed-overflow point (−2^255 / −1), sign edges,
    `N = 0` for MUL/ADDMOD, and >256-bit-precision MULMOD/ADDMOD. The
    third slot `n` is used only by the ternary ops. -/
def seedOperands : List (ArithOp × Nat × Nat × Nat) :=
  let max := two256 - 1
  let bigDivisor := (2 ^ 64 - 1) * 2 ^ 192 + 2 ^ 128 + 2 ^ 64 + 7  -- 4 nonzero limbs, top word ~2^64
  [ -- DIV / MOD
    (.div, 0, 0, 0), (.div, max, 0, 0), (.div, max, 1, 0), (.div, max, max, 0),
    (.div, max, 2 ^ 192, 0), (.div, (2 * bigDivisor - 1) % two256, bigDivisor, 0),
    (.div, (3 * bigDivisor + 4) % two256, bigDivisor, 0),
    (.mod, 0, 0, 0), (.mod, max, 0, 0), (.mod, max, bigDivisor, 0),
    (.mod, (2 * bigDivisor - 1) % two256, bigDivisor, 0),
    -- SDIV / SMOD (signed; max = -1, two255 = -2^255)
    (.sdiv, two255, max, 0),          -- signed-overflow point: (-2^255)/(-1)
    (.sdiv, max, 2, 0),               -- (-1)/2 = 0 (truncate toward zero)
    (.sdiv, two256 - 7, 3, 0),        -- (-7)/3 = -2
    (.sdiv, 7, two256 - 3, 0),        -- 7/(-3) = -2
    (.sdiv, two255, 1, 0), (.sdiv, two255, max, 0),
    (.smod, two256 - 3, 2, 0),        -- (-3) % 2 = -1 (sign of dividend)
    (.smod, 3, two256 - 2, 0),        -- 3 % (-2) = 1
    (.smod, two255, max, 0), (.smod, max, 0, 0),
    -- MULMOD / ADDMOD (n = third slot)
    (.mulmod, max, max, 0),           -- N = 0 ⇒ 0
    (.mulmod, max, max, 2), (.mulmod, max, max, max),
    (.mulmod, two255, two255, 2 ^ 200),  -- needs full 512-bit precision
    (.addmod, max, max, 0), (.addmod, max, max, 2),
    (.addmod, max, max, max), (.addmod, max, 1, two256 - 1) ]

def operandLine (op : ArithOp) (a b n : Nat) : String :=
  jsonObjLine [("op", op.name), ("a", toHex a), ("b", toHex b), ("n", toHex n)]

-- ============================================================================
-- Entry point
-- ============================================================================

def defaultCorpusPath : String := "tests/fuzz-corpus/arith/corpus.jsonl"

def parseNat (s : String) (default : Nat) : Nat := s.toNat?.getD default
def parseSeed (s : String) (default : UInt64) : UInt64 :=
  (s.toNat?.map UInt64.ofNat).getD default

/-- `emit` mode: read an operands JSONL (`{"op","a","b","n"}` per line) and
    print a results JSONL adding `"result"` = the `EvmWord.*` output. Used
    by the nightly execution-specs differential to obtain the evm-asm side
    without per-operand process spawns. -/
def runEmit (path : String) : IO UInt32 := do
  let content ← IO.FS.readFile path
  for line in content.splitOn "\n" do
    let t := trimStr line
    if t.isEmpty then continue
    match (do
        let op ← ArithOp.ofName? (← jsonField? t "op")
        let a ← parseHex? (← jsonField? t "a")
        let b ← parseHex? (← jsonField? t "b")
        let n ← parseHex? ((jsonField? t "n").getD "0x0")
        pure (op, a, b, n)) with
    | some (op, a, b, n) =>
        let r := evmWordResult op a b n
        IO.println (jsonObjLine [("op", op.name), ("a", toHex a), ("b", toHex b), ("n", toHex n), ("result", toHex r)])
    | none =>
        IO.eprintln s!"arith-diff-check emit: skipping unparseable line: {t}"
  return 0

def reportFailures (label : String) (fails : Array Failure) : IO Unit := do
  IO.println s!"FAIL: {fails.size} {label} mismatch(es):"
  for f in fails do
    IO.println f.render

def runPrCheck (nRandom nBias : Nat) (seed : UInt64) (corpusPath : String) :
    IO UInt32 := do
  let entries ← readCorpus corpusPath
  IO.println s!"arith-diff-check: nRandom={nRandom} nBias={nBias} seed={seed} corpus={corpusPath} ({entries.length} entries)"
  let fuzzFails := runFuzz nRandom nBias seed
  let corpusFails := runCorpus entries
  let total := fuzzFails.size + corpusFails.size
  if total = 0 then
    IO.println s!"PASS: all 6 ops agree with the Nat/Int reference over the generated cases, and all {entries.length} corpus entries match the frozen oracle verdict."
    return 0
  if fuzzFails.size > 0 then reportFailures "fuzz" fuzzFails
  if corpusFails.size > 0 then reportFailures "corpus" corpusFails
  return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | "gen-seed" :: _ =>
      -- print the curated DIV-class seed operands as JSONL (no `expected`);
      -- the execution-specs oracle fills `expected` to build the corpus.
      for (op, a, b, n) in seedOperands do
        IO.println (operandLine op a b n)
      return 0
  | "gen" :: rest =>
      -- print fuzz-generated operands as JSONL (no `expected`); for the
      -- nightly execution-specs differential.
      let nRandom := parseNat (rest[0]?.getD "") 20000
      let nBias := parseNat (rest[1]?.getD "") 5000
      let seed := parseSeed (rest[2]?.getD "") 42
      for op in allOps do
        for c in genCases nRandom nBias seed do
          IO.println (operandLine op c.a c.b c.n)
      return 0
  | "emit" :: path :: _ => runEmit path
  | "corpus" :: path :: _ =>
      let entries ← readCorpus path
      let fails := runCorpus entries
      if fails.size = 0 then
        IO.println s!"PASS: all {entries.length} corpus entries match."
        return 0
      reportFailures "corpus" fails
      return 1
  | "fuzz" :: rest =>
      let nRandom := parseNat (rest[0]?.getD "") 20000
      let nBias := parseNat (rest[1]?.getD "") 5000
      let seed := parseSeed (rest[2]?.getD "") 42
      let fails := runFuzz nRandom nBias seed
      if fails.size = 0 then
        IO.println s!"PASS: fuzz, nRandom={nRandom} nBias={nBias} seed={seed}"
        return 0
      reportFailures "fuzz" fails
      return 1
  | _ =>
      -- default PR fast-path: fuzz + corpus
      let nRandom := parseNat (args[0]?.getD "") 20000
      let nBias := parseNat (args[1]?.getD "") 5000
      let seed := parseSeed (args[2]?.getD "") 42
      runPrCheck nRandom nBias seed defaultCorpusPath

end EvmAsm.Tests.ArithDiffCheck
