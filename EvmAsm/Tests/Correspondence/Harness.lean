/-
  EvmAsm.Tests.Correspondence.Harness

  The family-agnostic core of the spec-correspondence differential harness.

  METHOD: docs/agents/spec-correspondence.md. That page defines the verdict
  vocabulary, the `basis` grading, and when a family is or is not a legitimate
  audit target. This module implements only the mechanics; it does not restate
  the method.

  A correspondence check replays a **committed corpus** — generated from a
  pinned external reference by `scripts/spec-oracle.py` — against a Lean
  `Subject`, and classifies every disagreement. The corpus is committed so CI
  needs neither Python nor network; regenerating it is a local step.

  ## Contract every family inherits

  * **Exit codes.** `0` agree · `1` divergence or stale pin · `2` the instrument
    could not run (corpus missing/unparseable). Distinguishing 2 from 1 matters:
    "found nothing" and "could not look" are different results.
  * **Self-test obligation.** Every family must plant one finding of each class
    and assert each is caught. A gate that cannot demonstrate catching a
    violation is itself unaudited (same discipline as
    `scripts/check_spec_refs.py --self-test`).
  * **Capped reporting.** Findings are capped per class. An uncapped dump is one
    bad corpus away from a 200k-line CI log.
  * **Staleness guard runs first.** A green tally must never be printed next to
    a corpus that describes a reference the repo no longer pins.
  * **No Mathlib.** This module and every `Subject` must stay out of the Mathlib
    import closure. That is what makes a correspondence check a per-PR gate
    rather than an hour-long one; a `Subject` rooted in `EvmAsm.Evm64` (closure
    ~1471 modules) forfeits it.

  ## What is deliberately NOT compared

  Rejection *reasons*. A reference's messages describe its own control flow and
  carry no obligation for a different implementation; requiring reason equality
  manufactures failures. Only accept/reject, the rendered value, and the
  family's optional auxiliary axis are compared.
-/

namespace EvmAsm.Tests.Correspondence

/-! ## Hex helpers

Shared because four independent copies of `hexDigit?` had accumulated across
`EvmAsm/Tests/`. -/

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Parse an even-length hex string into bytes. `none` on any bad character or
an odd length. -/
def parseHexBytes (s : String) : Option (List (BitVec 8)) :=
  let rec go : List Char → Option (List (BitVec 8))
    | [] => some []
    | [_] => none
    | hi :: lo :: rest => do
      let h ← hexDigit? hi
      let l ← hexDigit? lo
      let tl ← go rest
      some (BitVec.ofNat 8 (h * 16 + l) :: tl)
  go s.toList

def hexDigitChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + (n - 10))

def hexOfByte (b : BitVec 8) : String :=
  let n := b.toNat
  String.ofList [hexDigitChar (n / 16), hexDigitChar (n % 16)]

def hexOfBytes (bs : List (BitVec 8)) : String :=
  bs.foldl (fun acc b => acc ++ hexOfByte b) ""

/-! ## The subject under test -/

/--
One family's side of a correspondence check.

The interface is narrower than it may look, because the corpus stores
**rendered** values: the harness never needs the family's value type, only a
textual rendering that matches what the Python oracle emits. That keeps a single
harness usable for byte codecs (`input` = hex) and for arithmetic families
(`input` = an operand tuple) alike, with no comparison logic in common to
duplicate.
-/
structure Subject where
  /-- Family name as used on the command line and in the corpus filename. -/
  family : String
  /-- Run the Lean side on one corpus input. `none` means "we reject it".
  The returned string must use the same rendering the oracle emits. -/
  run : String → Option String
  /-- Optional second comparison axis, evaluated only when both sides accept.
  RLP uses it for "does re-encoding reproduce the input byte-for-byte?". -/
  aux : String → Option Bool := fun _ => none
  /-- Human-readable name of the `aux` axis, used in the report. -/
  auxLabel : String := "aux"
  /-- What the Lean side is, for the result line (e.g. `EL.RLP.decodeFully/encode`). -/
  ourName : String := "our model"
  /-- Instance page an operator should read before "fixing" a divergence. -/
  docPage : String := "docs/agents/spec-correspondence.md"

/-! ## Corpus records -/

structure Record where
  input : String
  accepted : Bool
  detail : String
  /-- Reference answer for the family's auxiliary axis; `none` when rejected or
  when the family does not use one. -/
  auxSame : Option Bool := none
deriving Inhabited

private def isBlank (s : String) : Bool :=
  s.all (fun c => c == ' ' || c == '\t' || c == '\r')

/-- Parse one TSV line. Comments and blank lines yield `none`. -/
def parseLine (rawLine : String) : Option Record :=
  -- Drop CRs so a CRLF checkout does not corrupt the last field.
  let line := String.ofList (rawLine.toList.filter (· != '\r'))
  if line.startsWith "#" || line.isEmpty || isBlank line then none
  else
    -- NOTE: an empty input renders as an empty first field, so the split must
    -- keep leading empties (`String.splitOn` does).
    let auxOf (s : String) : Option Bool :=
      if s == "same" then some true else if s == "differs" then some false else none
    match line.splitOn "\t" with
    | [i, v, d, a] =>
        some { input := i, accepted := v == "accept", detail := d, auxSame := auxOf a }
    | [i, v, d] => some { input := i, accepted := v == "accept", detail := d }
    | [i, v] => some { input := i, accepted := v == "accept", detail := "" }
    | _ => none

def loadRecords (path : System.FilePath) : IO (List Record) := do
  let contents ← IO.FS.readFile path
  return contents.splitOn "\n" |>.filterMap parseLine

/-! ## Outcomes

The verdict lattice is **asymmetric on purpose**, and that asymmetry is the
reason this harness is not just an equality checker: `looser` is a soundness
finding (we accept what the reference rejects — a false-accept, the one gate
that never relaxes), while `stricter` is a false-reject risk. See
`docs/agents/spec-alignment-doctrine.md` §2. -/

inductive Outcome where
  /-- Both sides agree (reject, or accept with the same value and aux). -/
  | agree
  /-- We reject what the reference accepts: false-rejects on valid data. -/
  | stricter (input expected : String)
  /-- We accept what the reference rejects: a soundness finding. -/
  | looser (input got why : String)
  /-- Both accept, different rendered values. -/
  | valueMismatch (input expected got : String)
  /-- Both accept and agree on the value; the auxiliary axis disagrees. -/
  | auxMismatch (input : String) (expected got : Bool)
deriving Inhabited

def classify (s : Subject) (r : Record) : Outcome :=
  match s.run r.input, r.accepted with
  | none, false => .agree
  | some got, true =>
    if got != r.detail then .valueMismatch r.input r.detail got
    else
      match r.auxSame with
      | none => .agree
      | some expected =>
        match s.aux r.input with
        | none => .agree
        | some ours => if ours == expected then .agree
                       else .auxMismatch r.input expected ours
  | none, true => .stricter r.input r.detail
  | some got, false => .looser r.input got r.detail

structure Tally where
  total : Nat := 0
  agree : Nat := 0
  stricter : Nat := 0
  looser : Nat := 0
  valueMismatch : Nat := 0
  auxMismatch : Nat := 0
deriving Inhabited

def Tally.clean (t : Tally) : Bool :=
  t.stricter == 0 && t.looser == 0 && t.valueMismatch == 0 && t.auxMismatch == 0

/-! ## Runner -/

def runRecords (s : Subject) (rs : List Record) (maxReport : Nat := 12) :
    Tally × List String := Id.run do
  let mut t : Tally := {}
  let mut msgs : List String := []
  for r in rs do
    t := { t with total := t.total + 1 }
    match classify s r with
    | .agree => t := { t with agree := t.agree + 1 }
    | .stricter inp exp =>
        t := { t with stricter := t.stricter + 1 }
        if t.stricter ≤ maxReport then
          msgs := msgs ++ [s!"  STRICTER  input={inp}  reference accepted {exp}, we rejected"]
    | .looser inp got why =>
        t := { t with looser := t.looser + 1 }
        if t.looser ≤ maxReport then
          msgs := msgs ++ [s!"  LOOSER    input={inp}  reference rejected ({why}), we accepted {got}"]
    | .valueMismatch inp exp got =>
        t := { t with valueMismatch := t.valueMismatch + 1 }
        if t.valueMismatch ≤ maxReport then
          msgs := msgs ++ [s!"  VALUE     input={inp}  reference={exp}  ours={got}"]
    | .auxMismatch inp exp got =>
        t := { t with auxMismatch := t.auxMismatch + 1 }
        if t.auxMismatch ≤ maxReport then
          msgs := msgs ++ [s!"  {s.auxLabel.toUpper}  input={inp}  reference={exp}  ours={got}"]
  return (t, msgs)

/-! ## Staleness guard

A committed corpus can silently keep describing a reference version the repo no
longer uses: every leg of the check would keep passing while measuring the wrong
thing — this harness's own failure mode, one level up.

The generator stamps the reference version and the `execution-specs` gitlink SHA
into the corpus header; here we verify the SHA still matches the superproject.

Why the SHA and not a lockfile: the gitlink is readable from the superproject
tree **without the submodule checked out**, which is the situation in CI. Any
change to a reference pinned inside that submodule necessarily moves this SHA,
so an unchanged SHA is sufficient evidence that the reference has not moved
under the corpus. Families whose reference is *vendored* rather than an external
package get this for free — see the method page's reference taxonomy. -/

private def headerValue (lines : List String) (key : String) : Option String :=
  lines.findSome? fun l =>
    let pfx := "# " ++ key ++ ": "
    if l.startsWith pfx then some ((l.drop pfx.length).trimAscii.toString) else none

/-- The `execution-specs` gitlink SHA recorded in the superproject tree. -/
def recordedSpecsSha : IO (Option String) := do
  let out ← IO.Process.output { cmd := "git", args := #["ls-tree", "HEAD", "execution-specs"] }
  if out.exitCode != 0 then return none
  -- Format: "160000 commit <sha>\texecution-specs"
  match (out.stdout.splitOn " ").getLast? with
  | none => return none
  | some tl => return some ((tl.splitOn "\t").headD "" |>.trimAscii.toString)

/-- Verify the corpus still describes the pinned reference. Returns an error
message, or `none` when the pins agree (or cannot be read in this environment). -/
def checkPins (path : System.FilePath) (quiet : Bool := false) : IO (Option String) := do
  let contents ← IO.FS.readFile path
  let lines := contents.splitOn "\n" |>.take 12
  let some oracleVer := headerValue lines "oracle-version"
    | return some "corpus header has no `# oracle-version:` stamp — regenerate it"
  let some stampedSha := headerValue lines "execution-specs"
    | return some "corpus header has no `# execution-specs:` stamp — regenerate it"
  unless quiet do
    IO.println s!"  pinned reference {oracleVer}, execution-specs {stampedSha.take 12}"
  match ← recordedSpecsSha with
  | none =>
      unless quiet do
        IO.println "  note: could not read the execution-specs gitlink; pin not verified here"
      return none
  | some actual =>
      if actual == stampedSha then return none
      else return some s!"execution-specs moved: corpus was generated at {stampedSha.take 12}, \
repo now pins {actual.take 12}. References pinned inside that submodule may have moved with it, \
so the committed corpus may describe a reference this repo no longer uses. Regenerate it \
(scripts/spec-oracle.py) and re-check."

/-! ## Self-test

The framework owns the pin-guard half of the self-test, since it is identical
for every family; each `Subject` supplies only the planted comparison records
(which need family-specific inputs to be meaningful). -/

/-- Plant a moved gitlink SHA and a missing stamp, and require both to be caught
while a current corpus is not flagged. -/
def selfTestPins : IO Bool := do
  let tmp ← IO.FS.createTempDir
  let sha := (← recordedSpecsSha).getD "unknown"
  let mk (specs : String) (withVersion : Bool) : String :=
    (if withVersion then "# oracle-version: pinned==0.0.0\n" else "")
      ++ "# execution-specs: " ++ specs ++ "\nx\taccept\ty\tsame\n"
  let write (name content : String) : IO System.FilePath := do
    let p := tmp / name; IO.FS.writeFile p content; return p
  let goodOk := (← checkPins (← write "good.tsv" (mk sha true)) (quiet := true)).isNone
  let staleCaught :=
    (← checkPins (← write "stale.tsv"
      (mk "0000000000000000000000000000000000000000" true)) (quiet := true)).isSome
  let noStampCaught :=
    (← checkPins (← write "nostamp.tsv" (mk sha false)) (quiet := true)).isSome
  IO.FS.removeDirAll tmp
  if goodOk && staleCaught && noStampCaught then
    IO.println "  pin guard: OK — catches a moved execution-specs pin and a missing stamp, \
and does not flag a current corpus"
    return true
  else
    IO.println s!"  pin guard: FAILED — {repr (goodOk, staleCaught, noStampCaught)} \
(expected (true, true, true))"
    return false

/-- Run a family's planted records and require exactly one finding of each class
plus one agreement — **exact counts, not non-zero**, so the check demonstrates
that the right thing fires *and* that an agreement is not flagged. -/
def selfTestComparison (s : Subject) (planted : List Record) : IO Bool := do
  let (t, msgs) := runRecords s planted
  for m in msgs do IO.println m
  let ok := t.agree == 1 && t.stricter == 1 && t.looser == 1
            && t.valueMismatch == 1 && t.auxMismatch == 1
  if ok then
    IO.println "  comparison: OK — planted stricter/looser/value/aux findings all detected"
  else
    IO.println s!"  comparison: FAILED — \
{repr (t.agree, t.stricter, t.looser, t.valueMismatch, t.auxMismatch)} \
(expected (1, 1, 1, 1, 1))"
  return ok

def selfTest (s : Subject) (planted : List Record) : IO UInt32 := do
  IO.println s!"self-test [{s.family}]:"
  let a ← selfTestComparison s planted
  let b ← selfTestPins
  if a && b then
    IO.println "self-test: OK"
    return 0
  else
    IO.println "self-test: FAILED"
    return 1

/-! ## Driver -/

/-- Default corpus location for a family. -/
def corpusPath (family : String) : System.FilePath :=
  System.FilePath.mk ("tests/correspondence/" ++ family ++ ".tsv")

/-- Replay a corpus against a subject and report. See the contract in the module
docstring for the exit-code policy. -/
def run (s : Subject) (path : System.FilePath) : IO UInt32 := do
  unless ← path.pathExists do
    IO.eprintln s!"error: corpus not found at {path}"
    IO.eprintln "Generate it with:"
    IO.eprintln s!"  scripts/spec-oracle.py --family {s.family} --out {path}"
    return 2
  let rs ← loadRecords path
  if rs.isEmpty then
    IO.eprintln s!"error: no records parsed from {path}"
    return 2
  IO.println s!"correspondence-check [{s.family}]: {rs.length} records from {path}"
  -- Staleness guard first: a corpus describing the wrong reference makes the
  -- agreement figure meaningless, so a green tally must not be printed with it.
  match ← checkPins path with
  | some err => IO.eprintln s!"error: {err}"; return 1
  | none => pure ()
  let (t, msgs) := runRecords s rs
  IO.println s!"  agree          {t.agree}"
  IO.println s!"  stricter       {t.stricter}   (reference accepts, {s.ourName} rejects)"
  IO.println s!"  looser         {t.looser}   (reference rejects, {s.ourName} accepts)"
  IO.println s!"  value mismatch {t.valueMismatch}"
  IO.println s!"  {s.auxLabel} mismatch  {t.auxMismatch}"
  unless msgs.isEmpty do
    IO.println ""
    IO.println "findings (first few of each class):"
    for m in msgs do IO.println m
  IO.println ""
  if t.clean then
    IO.println s!"RESULT: {s.ourName} agrees with the pinned reference on every record."
    return 0
  else
    if t.looser > 0 then
      IO.println "RESULT: LOOSER findings present — we accept input the reference rejects. \
That is a false-accept: file it before changing either side."
    else
      IO.println "RESULT: divergence."
    IO.println s!"See {s.docPage} and docs/agents/spec-correspondence.md."
    return 1

end EvmAsm.Tests.Correspondence
