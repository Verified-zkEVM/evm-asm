/-
  bench/DivBench.lean — two-axis dynamic cost harness for `evm_div` / `evm_mod`,
  extended for Phase 3 with frequency-weighted cost from real mainnet data.

  Runs the VERIFIED `step` semantics (EvmAsm.Rv64.Execution) on concrete inputs
  and reports, per divisor class:

    * steps   — dynamic instruction (cycle) count   [PRIMARY zkVM cost driver]
    * loads / stores / memOps — memory-traffic count [2nd axis: paging proxy]
    * dwords  — distinct 8-byte cells touched        [working-set size]
    * pages   — distinct 1 KiB data pages touched    [page-in/out proxy]
    * correct — result checked against `a / b`

  Cost-model rationale (Gassmann et al., arXiv:2508.17518v2, RISC0/SP1):
  dynamic instruction count is the primary, near-linear proving-cost driver;
  per-instruction cost is ~uniform ("division is not expensive"); memory is a
  complementary axis — a paged-in access is 1 cycle but a page-in/out ≈ 1130
  cycles. This harness surfaces both axes so the optimization objective can be
  the frequency-weighted (instructions + paging) cost, not instructions alone.

  Phase 3 (this extension): ranks DIV/MOD algorithm candidates under the REAL
  mainnet workload (Phase-2 trace: 138,601 unsigned division ops, 32 blocks)
  rather than a guessed distribution. Metrics, in order of trustworthiness:

    * PRIMARY — operand-sampled mean: the true mean step count over a
      frequency-weighted sample of REAL mainnet (a,b) pairs
      (`bench/div-operands-sample.txt`, from `scripts/sample-div-operands.py`).
      No representative-bias: it captures the within-`n` variation (normalization
      shift, dividend size, a<b/pow2 sub-cases). This is the faithful headline.
    * CROSS-CHECK — representative point estimate: Σ_n (n_k fraction)·steps(rep_n)
      and the partition-weighted variant, using ONE operand per class. NOT exact
      — step count varies within a fixed `n` (e.g. v5 n=2 spans ~528..634, v6 n=1
      ~347..369) and the reps skew expensive (full-width dividend, small
      divisors). Kept to sanity-check the sampled mean and to give the per-class
      breakdown the (not-yet-built) cheap-dispatch candidate will be ranked on.

  Run:  python3 scripts/sample-div-operands.py   # regenerate the sample (once)
        lake env lean bench/DivBench.lean
  (needs `lake build EvmAsm.Evm64.DivMod.FastN1Program EvmAsm.Evm64.DivMod.Program
   EvmAsm.Rv64.Execution EvmAsm.Evm64.Basic`)
-/
import Lean.Data.Json
import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.DivMod.FastN1Program
import EvmAsm.Rv64.Execution
import EvmAsm.Evm64.Basic

open EvmAsm.Rv64
open EvmAsm.Evm64

/-- i-th 64-bit little-endian limb of a 256-bit value. -/
def limbN (v : BitVec 256) (i : Nat) : Word := BitVec.ofNat 64 (v.toNat >>> (64 * i))

/-- Initial data memory: dividend `a` at sp+0..+24, divisor `b` at sp+32..+56,
    everything else (scratch) zero. -/
def mkMem (sp : Word) (a b : BitVec 256) (addr : Word) : Word :=
  let off := (addr - sp).toNat
  if off < 32 ∧ off % 8 = 0 then limbN a (off / 8)
  else if 32 ≤ off ∧ off < 64 ∧ off % 8 = 0 then limbN b ((off - 32) / 8)
  else 0

def spBase : Word := 0xa0001000

def mkState (prog : Program) (a b : BitVec 256) : MachineState :=
  { regs := fun r => if r = Reg.x12 then spBase else 0
  , mem  := mkMem spBase a b
  , code := loadProgram 0 prog
  , pc   := 0 }

/-- If `i` is a memory op, return `(isStore, address)`; else `none`.
    Address computation mirrors `EvmAsm.Rv64.step` (base reg is the first field
    for loads (`rd rs1`) and for stores (`rs1 rs2`)). -/
def classifyMem? (s : MachineState) : Option (Bool × Word) :=
  match s.code s.pc with
  | some (.LD  _ rs1 off) => some (false, s.getReg rs1 + signExtend12 off)
  | some (.LW  _ rs1 off) => some (false, s.getReg rs1 + signExtend12 off)
  | some (.LWU _ rs1 off) => some (false, s.getReg rs1 + signExtend12 off)
  | some (.LB  _ rs1 off) => some (false, s.getReg rs1 + signExtend12 off)
  | some (.LBU _ rs1 off) => some (false, s.getReg rs1 + signExtend12 off)
  | some (.LH  _ rs1 off) => some (false, s.getReg rs1 + signExtend12 off)
  | some (.LHU _ rs1 off) => some (false, s.getReg rs1 + signExtend12 off)
  | some (.SD  rs1 _ off) => some (true,  s.getReg rs1 + signExtend12 off)
  | some (.SW  rs1 _ off) => some (true,  s.getReg rs1 + signExtend12 off)
  | some (.SB  rs1 _ off) => some (true,  s.getReg rs1 + signExtend12 off)
  | some (.SH  rs1 _ off) => some (true,  s.getReg rs1 + signExtend12 off)
  | _ => none

structure Tally where
  steps   : Nat := 0
  loads   : Nat := 0
  stores  : Nat := 0
  dwords  : List Nat := []   -- distinct 8-byte cell indices (addr/8)
  pages   : List Nat := []   -- distinct 1 KiB page indices   (addr/1024)

def Tally.note (acc : Tally) : Option (Bool × Word) → Tally
  | none => acc
  | some (isStore, addr) =>
      let d := addr.toNat / 8
      let p := addr.toNat / 1024
      { acc with
        loads  := acc.loads  + (if isStore then 0 else 1)
      , stores := acc.stores + (if isStore then 1 else 0)
      , dwords := if acc.dwords.contains d then acc.dwords else d :: acc.dwords
      , pages  := if acc.pages.contains p then acc.pages else p :: acc.pages }

/-- Step until PC = `exitPC` (clean return), accumulating cost metrics. -/
def runTally (exitPC : Word) : Nat → MachineState → Tally → (Tally × Option MachineState)
  | 0,        _, acc => (acc, none)
  | fuel + 1, s, acc =>
    if s.pc = exitPC then (acc, some s)
    else
      let acc := acc.note (classifyMem? s)
      match step s with
      | none    => (acc, none)
      | some s' => runTally exitPC fuel s' { acc with steps := acc.steps + 1 }

def readResult (s : MachineState) : Nat :=
  (s.mem (spBase + 32)).toNat
  + (s.mem (spBase + 40)).toNat * 2^64
  + (s.mem (spBase + 48)).toNat * 2^128
  + (s.mem (spBase + 56)).toNat * 2^192

structure Report where
  steps   : Nat
  loads   : Nat
  stores  : Nat
  memOps  : Nat
  dwords  : Nat   -- distinct 8-byte cells touched (working-set size)
  pages   : Nat   -- distinct 1 KiB data pages touched
  ok      : Bool
  correct : Bool
  deriving Repr

/-- Run `prog` on `(a, b)` until `exitPC`, reporting both cost axes and
    correctness against `a / b`. `exitPC` is the byte offset of the program's
    terminal NOP: 1068 for `evm_div`/`evm_div_v5`, 1884 for `evm_div_v6`. -/
def benchDiv (prog : Program) (exitPC : Word) (a b : BitVec 256) : Report :=
  match runTally exitPC 20000 (mkState prog a b) {} with
  | (acc, some s) =>
      let expected := if b == 0 then 0 else a.toNat / b.toNat
      { steps := acc.steps, loads := acc.loads, stores := acc.stores
      , memOps := acc.loads + acc.stores, dwords := acc.dwords.length
      , pages := acc.pages.length, ok := true, correct := readResult s = expected }
  | (acc, none) =>
      { steps := acc.steps, loads := acc.loads, stores := acc.stores
      , memOps := acc.loads + acc.stores, dwords := acc.dwords.length
      , pages := acc.pages.length, ok := false, correct := false }

/-- MOD variant: same harness, but the result at spBase+32 is the remainder, so
    correctness checks against `a % b` (EVM `MOD`: `b=0 → 0`). -/
def benchMod (prog : Program) (exitPC : Word) (a b : BitVec 256) : Report :=
  match runTally exitPC 20000 (mkState prog a b) {} with
  | (acc, some s) =>
      let expected := if b == 0 then 0 else a.toNat % b.toNat
      { steps := acc.steps, loads := acc.loads, stores := acc.stores
      , memOps := acc.loads + acc.stores, dwords := acc.dwords.length
      , pages := acc.pages.length, ok := true, correct := readResult s = expected }
  | (acc, none) =>
      { steps := acc.steps, loads := acc.loads, stores := acc.stores
      , memOps := acc.loads + acc.stores, dwords := acc.dwords.length
      , pages := acc.pages.length, ok := false, correct := false }

-- ============================================================================
-- Candidates and representative operands
-- ============================================================================

/-- Exit PC (byte offset of the terminal NOP) per candidate. `evm_div` and
    `evm_div_v5` share the index-267 NOP (byte 1068); `evm_div_v6` reuses the
    embedded v5 NOP at index 471 (byte 1884). -/
structure Candidate where
  name   : String
  prog   : Program
  exitPC : Word

def candidates : List Candidate :=
  [ { name := "evm_div(v4)",  prog := evm_div,    exitPC := 1068 }
  , { name := "evm_div_v5",   prog := evm_div_v5, exitPC := 1068 }
  , { name := "evm_div_v6",   prog := evm_div_v6, exitPC := 1884 } ]

/-- MOD candidates. `evm_mod`/`evm_mod_v5` exit at the index-267 NOP (byte 1068);
    `evm_mod_v6` (which inserts `divK_fastDenorm`, +7) exits at index 478
    (byte 1912). -/
def modCandidates : List Candidate :=
  [ { name := "evm_mod(v4)",  prog := evm_mod,    exitPC := 1068 }
  , { name := "evm_mod_v6",   prog := evm_mod_v6, exitPC := 1912 } ]

/-- A full-width dividend used for every "a ≥ b" representative. -/
def numA : BitVec 256 := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

/-- Representative operands. One `(a, b)` per dispatch class, chosen to (a) land
    in that class and (b) match the dominant divisor word-count of the class in
    the mainnet data (see `altb_by_n` / `pow2_by_n` in div-weights.json). -/
structure RepInput where
  key : String          -- weights-file key this operand represents
  a   : BitVec 256
  b   : BitVec 256

/-- n-weighting reps: cost of v5/v6 depends only on divisor word-count n. -/
def repsByN : List (Nat × RepInput) :=
  [ (0, { key := "n0", a := numA, b := 0 })
  , (1, { key := "n1", a := numA, b := 1000003 })                                    -- single-word, a≥b
  , (2, { key := "n2", a := numA, b := 0x10000000000000033 })                        -- ~2^64
  , (3, { key := "n3", a := numA, b := 0x100000000000000000000000000000033 })        -- ~2^128
  , (4, { key := "n4", a := numA, b := 0x8000000000000000000000000000000000000000000000000000000000000001 }) ]

/-- partition reps: one per non-overlapping class in `divmod.partition`.
    `b0`/`genuine_n*` reuse the `repsByN` divisors; `a_lt_b` and `pow2_not_altb`
    use the dominant word-count of their class (a<b is ~67% n=3; pow2 is
    dominated by 2^(8k) byte-extraction, esp. 2^224). -/
def repsPartition : List (String × RepInput) :=
  [ ("b0",             { key := "b0",             a := numA, b := 0 })
  , ("a_lt_b",         { key := "a_lt_b",         a := 7, b := 0x100000000000000000000000000000033 })  -- a<b, n=3
  , ("pow2_not_altb",  { key := "pow2_not_altb",  a := numA, b := 0x100000000000000000000000000000000000000000000000000000000 }) -- 2^224, a≥b
  , ("genuine_n1",     { key := "genuine_n1",     a := numA, b := 1000003 })
  , ("genuine_n2",     { key := "genuine_n2",     a := numA, b := 0x10000000000000033 })
  , ("genuine_n3",     { key := "genuine_n3",     a := numA, b := 0x100000000000000000000000000000033 })
  , ("genuine_n4",     { key := "genuine_n4",     a := numA, b := 0x8000000000000000000000000000000000000000000000000000000000000001 }) ]

-- ============================================================================
-- Weights file access (bench/div-weights.json)
-- ============================================================================

open Lean (Json)

/-- Fetch a Float at `<seg0>.<seg1>...` from a parsed JSON object. -/
def jPath (root : Json) (segs : List String) : Except String Float := do
  let mut cur := root
  for s in segs do
    cur ← cur.getObjVal? s
  return (← cur.getNum?).toFloat

def loadWeights : IO Json := do
  let s ← IO.FS.readFile "bench/div-weights.json"
  IO.ofExcept (Json.parse s)

-- ============================================================================
-- Operand sample (bench/div-operands-sample.txt) — real mainnet (a,b) pairs
-- ============================================================================

/-- Parsed `bench/div-operands-sample.txt`: a frequency-weighted sample of real
    mainnet operands (decimal `a b` per line; "# DIV n"/"# MOD n" section heads),
    produced by `scripts/sample-div-operands.py`. Running the harness over these
    gives a TRUE mean step count — no representative-bias. -/
structure Sample where
  divs : Array (BitVec 256 × BitVec 256) := #[]
  mods : Array (BitVec 256 × BitVec 256) := #[]

def parseSample (txt : String) : Sample := Id.run do
  let mut sect := 0    -- 1 = DIV, 2 = MOD
  let mut divs : Array (BitVec 256 × BitVec 256) := #[]
  let mut mods : Array (BitVec 256 × BitVec 256) := #[]
  for raw in txt.splitOn "\n" do
    let line := raw.trim
    if line.isEmpty then continue
    else if line.startsWith "# DIV" then sect := 1
    else if line.startsWith "# MOD" then sect := 2
    else
      match line.splitOn " " with
      | [as, bs] =>
        let a : BitVec 256 := BitVec.ofNat 256 (as.toNat!)
        let b : BitVec 256 := BitVec.ofNat 256 (bs.toNat!)
        if sect == 1 then divs := divs.push (a, b)
        else if sect == 2 then mods := mods.push (a, b)
      | _ => pure ()
  return { divs, mods }

def loadSample : IO Sample := do
  let s ← IO.FS.readFile "bench/div-operands-sample.txt"
  return parseSample s

-- ============================================================================
-- Reporting
-- ============================================================================

/-- Right-pad a string to width `w`. -/
def pad (w : Nat) (s : String) : String :=
  if s.length < w then s ++ String.mk (List.replicate (w - s.length) ' ') else s

/-- 2-decimal float string (avoids scientific notation for small sums).
    Handles negatives: `Float.toUInt64` floors negatives to 0, so format the
    magnitude and prepend a sign (otherwise a regression prints as "0.00"). -/
def f2 (x : Float) : String :=
  let neg := x < 0.0
  let ax := if neg then -x else x
  let scaled := (ax * 100.0 + 0.5).toUInt64.toNat
  let whole := scaled / 100
  let frac  := scaled % 100
  s!"{if neg then "-" else ""}{whole}.{if frac < 10 then "0" else ""}{frac}"

def main : IO Unit := do
  let j ← loadWeights
  let dm ← IO.ofExcept (j.getObjVal? "divmod")

  -- Per-class raw steps for every representative.
  IO.println "=== Per-class dynamic instruction count (steps; ✗ = wrong result) ==="
  IO.println (pad 18 "class"
    ++ candidates.foldl (fun acc c => acc ++ pad 14 c.name) "")
  for (n, r) in repsByN do
    let row := candidates.foldl (fun acc c =>
      let rep := benchDiv c.prog c.exitPC r.a r.b
      acc ++ pad 14 (s!"{rep.steps}{if rep.correct then "" else "✗"}")) ""
    IO.println (pad 18 s!"n={n}" ++ row)
  for (cls, r) in repsPartition do
    if cls == "a_lt_b" || cls == "pow2_not_altb" then
      let row := candidates.foldl (fun acc c =>
        let rep := benchDiv c.prog c.exitPC r.a r.b
        acc ++ pad 14 (s!"{rep.steps}{if rep.correct then "" else "✗"}")) ""
      IO.println (pad 18 s!"{cls}" ++ row)

  -- PRIMARY metric: true mean step count over a frequency-weighted sample of
  -- REAL mainnet operands (bench/div-operands-sample.txt). This has no
  -- representative-bias — it captures the within-n variation (normalization
  -- shift, dividend size, a<b/pow2 sub-cases) that a single rep per class
  -- cannot. This is the faithful before/after headline.
  let smp ← loadSample
  IO.println s!"\n=== PRIMARY: operand-sampled mean steps ({smp.divs.size} real DIV ops) ==="
  let divMeans ← candidates.mapM (fun c => do
    let mut tot := 0
    let mut bad := 0
    for (a, b) in smp.divs do
      let r := benchDiv c.prog c.exitPC a b
      tot := tot + r.steps
      if !(r.ok && r.correct) then bad := bad + 1
    pure (Float.ofNat tot / Float.ofNat smp.divs.size, bad))
  for (c, (m, bad)) in candidates.zip divMeans do
    let note := if bad == 0 then "  (all correct)" else s!"  ({bad} WRONG)"
    IO.println (s!"  {pad 14 c.name}  mean = {pad 8 (f2 m)} steps" ++ note)
  let dBase := (divMeans[0]!).1
  let dV6 := (divMeans[2]!).1
  IO.println s!"  → evm_div_v6 vs deployed evm_div: {f2 ((dBase - dV6) / dBase * 100.0)}% fewer steps"

  -- MOD: measured, not inferred (evm_mod_v6 carries an extra +7 denorm).
  IO.println s!"\n=== Operand-sampled mean steps — MOD ({smp.mods.size} real MOD ops) ==="
  let modMeans ← modCandidates.mapM (fun c => do
    let mut tot := 0
    let mut bad := 0
    for (a, b) in smp.mods do
      let r := benchMod c.prog c.exitPC a b
      tot := tot + r.steps
      if !(r.ok && r.correct) then bad := bad + 1
    pure (Float.ofNat tot / Float.ofNat smp.mods.size, bad))
  for (c, (m, bad)) in modCandidates.zip modMeans do
    let note := if bad == 0 then "  (all correct)" else s!"  ({bad} WRONG)"
    IO.println (s!"  {pad 14 c.name}  mean = {pad 8 (f2 m)} steps" ++ note)
  let mBase := (modMeans[0]!).1
  let mV6 := (modMeans[1]!).1
  IO.println s!"  → evm_mod_v6 vs deployed evm_mod: {f2 ((mBase - mV6) / mBase * 100.0)}% fewer steps"

  -- CROSS-CHECK (NOT the headline): representative point estimate — one operand
  -- per divisor word-count. NOT exact: step count varies within a fixed n with
  -- the normalization shift and dividend (v5 n=2 spans ~528..634; v6 n=1 spans
  -- ~347..369), and these reps (full-width dividend, small divisors) skew to the
  -- expensive end. Kept only to cross-check the sampled mean and to provide the
  -- per-class breakdown the cheap-dispatch candidate will be ranked against.
  IO.println "\n=== Representative-weighted point estimate (cross-check, not headline) ==="
  IO.println (pad 32 "metric" ++ candidates.foldl (fun acc c => acc ++ pad 14 c.name) "")
  let nWeights ← (List.range 5).mapM (fun k => IO.ofExcept (jPath dm [s!"n{k}"]))
  let nRow ← candidates.mapM (fun c => do
    let mut tot := 0.0
    for (n, r) in repsByN do
      let rep := benchDiv c.prog c.exitPC r.a r.b
      tot := tot + nWeights[n]! * Float.ofNat rep.steps
    pure tot)
  IO.println (pad 32 "n-weighted (reps)"
    ++ (nRow.foldl (fun acc x => acc ++ pad 14 (f2 x)) ""))

  -- partition-weighted cost (framework for the cheap-dispatch candidate).
  let partKeys := ["b0","a_lt_b","pow2_not_altb","genuine_n1","genuine_n2","genuine_n3","genuine_n4"]
  let partW ← partKeys.mapM (fun k => IO.ofExcept (jPath dm ["partition", k]))
  let pRow ← candidates.mapM (fun c => do
    let mut tot := 0.0
    let mut i := 0
    for (_, r) in repsPartition do
      let rep := benchDiv c.prog c.exitPC r.a r.b
      tot := tot + partW[i]! * Float.ofNat rep.steps
      i := i + 1
    pure tot)
  IO.println (pad 32 "partition-weighted (reps)"
    ++ (pRow.foldl (fun acc x => acc ++ pad 14 (f2 x)) ""))

  -- Correctness sweep: de-risks recommending v6 for verification by checking
  -- every dispatch corner against `a / b` over a broad operand grid.
  IO.println "\n=== Correctness sweep (vs a/b) ==="
  let aS : List (BitVec 256) :=
    [ 0, 1, numA, 0x10000000000000000, 0xFFFFFFFFFFFFFFFF,
      0x100000000000000000000000000000000,
      0xDEADBEEFCAFEBABE0123456789ABCDEF, 0x8000000000000000000000000000000000000000000000000000000000000000 ]
  let bS : List (BitVec 256) :=
    [ 0, 1, 2, 7, 256, 1000003, 0xFFFFFFFFFFFFFFFF,             -- b0 + n=1 (incl. pow2 1,2,256)
      0x10000000000000000, 0x10000000000000033,                 -- n=2 (pow2 2^64 + genuine)
      0x100000000000000000000000000000000, 0x100000000000000000000000000000033, -- n=3
      0x100000000000000000000000000000000000000000000000000000000,  -- 2^224
      numA, 0x8000000000000000000000000000000000000000000000000000000000000001 ] -- n=4
  for c in candidates do
    let mut fails := 0
    let mut total := 0
    for a in aS do
      for b in bS do
        total := total + 1
        let r := benchDiv c.prog c.exitPC a b
        if !(r.ok && r.correct) then fails := fails + 1
    IO.println (s!"  {pad 14 c.name}  {total - fails}/{total} correct"
                ++ (if fails == 0 then "  ✓" else s!"  ✗ {fails} FAIL"))

#eval main
