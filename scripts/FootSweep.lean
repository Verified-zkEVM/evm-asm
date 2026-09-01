/-
Copyright (c) 2026 EvmAsm Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# Foot sweep: contracts that do not say what the code touches (#12747)

The defect class behind #12715 (`hcore`), #12661 (the knot family) and #12749
(the `hcallee` residual): a pre/post contract and a body of emitted code that
were never checked against each other.  A green build cannot see the gap; the
kernel only adjudicates contracts it is asked to prove.

## The soundness backbone (why this tool scans so little)

`cpsTripleWithin` and its siblings quantify over every pcFree frame `R`
(`CPSSpec.lean`):

```
∀ R, R.pcFree → … (P ** R).holdsFor s → … ∃ s', … (Q ** R).holdsFor s'
```

Instantiate `R = (x ↦ᵣ c)` for a register omitted from both `P` and `Q`: if a
covered execution clobbered it unrestored, `(Q ** R)` fails and the triple is
false, hence unprovable, hence absent from the environment.  So a **proven,
contract-hypothesis-free** cps triple has already had its footprint adjudicated
by the kernel — the 2026-08-22 retraction on #12747 established that scanning
that population is what produced the earlier token detector's ~91% false
positive rate.  This tool therefore **never flags** that safe class; it scans
only where the frame rule never got to run:

* **(a) unanchored contract abbrevs** — `Assertion`-valued definitions that
  occur in no safe-class theorem's type (the `hcore` shape);
* **(b) hypothesis-side contracts** — declarations carrying a hypothesis
  binder whose type is a cps predicate or `ItemsSound` application (the
  #12661 knot family and the #12749 `hcallee` residual: an *assumed* contract
  rather than a discharged one).

## What it checks, mechanically, on the at-risk sites

* **Signature A** (#12715 shape): a `List (BitVec 8)`-typed parameter of the
  host that occurs in the site's post(s) but is tied by no ownership atom —
  no `bytesRegion`/`memIs` argument — in the **alias-expanded** pre.  Alias
  expansion unfolds `Assertion`-valued definition constants transitively
  (that is what defeated the regex census: combinator-built claims have no
  token to grep).
* **Signature B** (#12661 shape): the site's `cr` is resolved to
  `CodeReq.ofProg base <prog>`; the program constant's elaborated value is
  walked as a `List Instr` and the **written-register set** is extracted from
  a destination table over the `Instr` constructors; any register written but
  claimed by neither `regIs` nor `regOwn` in the expanded pre is flagged.
  The table is diff-checked against the `Instr` inductive's constructor list;
  unknown constructors are counted loudly, never silently dropped.
* **Hypothesis-host census**: every declaration with a contract-typed
  hypothesis binder, marked by whether any other declaration's elaborated
  statement or proof references it (undischarged = the class's
  *precondition*, not a defect — a listed row is where a defect *can* live).

## What it CANNOT catch (commissioned list, #12747 scoping)

1. Never-established pins (a path/address property — no pre/post type shape).
2. Station-vs-exit misclassification (needs routine extents; the ELF-side
   prototype owns that side — this tool composes with it, not replaces it).
3. Data-driven footprints (runtime-computed addresses).
4. Decorative ties (an atom that ties the parameter but that the code never
   touches).
5. Unsatisfiable pres (double-own) — deliberately: that is #12825
   `lake exe satsweep`'s axis.  The two tools are complements: **satsweep
   covers satisfiability, footsweep covers footprint**; neither subsumes the
   other.
6. Unimported files and `example`s (bounded by `check-unimported.sh`).
7. Anything the kernel already adjudicated (the safe class — by design).
8. Signature B flags include legitimate save/restore bodies (write-restore
   then omit is *sound*); a flag is a triage row, never a verdict.  The
   2026-08-22 ruling ("no gate; take the fixes and the method") binds: this
   tool is advisory, always exits 0 on a successful walk.

## Modes

```
lake exe footsweep                # partition census + at-risk site report
lake exe footsweep --out r.json   # also write the full per-site report
lake exe footsweep --verbose      # also print every row
lake exe footsweep --self-test    # structural positive/negative controls
```
-/

open Lean

namespace FootSweep

/-- Root modules swept when no `--root` is given. -/
def defaultRoots : Array Name := #[`EvmAsm]

/-! ## Name resolution -/

structure Names where
  assertion : Name
  cpsTripleWithin : Name
  cpsBranchWithin : Name
  cpsHaltTripleWithin : Name
  cpsNBranchWithin : Name
  itemsSound : Name
  bytesRegion : Name
  memIs : Name
  regIs : Name
  regOwn : Name
  sepConj : Name
  ofProg : Name
  instr : Name
  reg : Name

-- Two spellings per role. The RISC-V core and program logic moved to the
-- riscv-zkvm dependency, and evm-asm re-exports them: `EvmAsm.Rv64.Assertion`
-- is now an ALIAS, and `Environment.find?` resolves constants, not aliases.
-- Listing the upstream name keeps this working across that boundary, and
-- keeping the `EvmAsm.` spelling means the sweep still resolves if a
-- declaration ever moves back. An unresolved role is a hard error, never a
-- skip -- the census would silently under-report.
def nameCandidates : List (String × List String) :=
  [ ("assertion", ["EvmAsm.Rv64.Assertion", "RiscvZkvm.Rv64.Assertion"])
  , ("cpsTripleWithin", ["EvmAsm.Rv64.cpsTripleWithin", "RiscvZkvm.Rv64.cpsTripleWithin"])
  , ("cpsBranchWithin", ["EvmAsm.Rv64.cpsBranchWithin", "RiscvZkvm.Rv64.cpsBranchWithin"])
  , ("cpsHaltTripleWithin", ["EvmAsm.Rv64.cpsHaltTripleWithin", "RiscvZkvm.Rv64.cpsHaltTripleWithin"])
  , ("cpsNBranchWithin", ["EvmAsm.Rv64.cpsNBranchWithin", "RiscvZkvm.Rv64.cpsNBranchWithin"])
  , ("itemsSound", ["EvmAsm.Rv64.SAsm.RecDecode.ItemsSound"])
  , ("bytesRegion", ["EvmAsm.Rv64.bytesRegion", "EvmAsm.Rv64.MemRegion.bytesRegion", "RiscvZkvm.Rv64.bytesRegion"])
  , ("memIs", ["EvmAsm.Rv64.memIs", "RiscvZkvm.Rv64.memIs"])
  , ("regIs", ["EvmAsm.Rv64.regIs", "RiscvZkvm.Rv64.regIs"])
  , ("regOwn", ["EvmAsm.Rv64.regOwn", "RiscvZkvm.Rv64.regOwn"])
  , ("sepConj", ["EvmAsm.Rv64.sepConj", "RiscvZkvm.Rv64.sepConj"])
  , ("ofProg", ["EvmAsm.Rv64.CodeReq.ofProg", "RiscvZkvm.Rv64.CodeReq.ofProg"])
  , ("instr", ["EvmAsm.Rv64.Instr", "EvmAsm.Rv64.Basic.Instr", "RiscvZkvm.Rv64.Instr"])
  , ("reg", ["EvmAsm.Rv64.Reg", "EvmAsm.Rv64.Basic.Reg", "RiscvZkvm.Rv64.Reg"]) ]

def resolveNames (env : Environment) : Except (Array String) Names := do
  let mut missing : Array String := #[]
  let mut resolved : Std.HashMap String Name := {}
  for (role, cands) in nameCandidates do
    let mut found := none
    for c in cands do
      if env.find? c.toName |>.isSome then found := some c.toName
    match found with
    | some n => resolved := resolved.insert role n
    | none => missing := missing.push s!"{role} (tried {cands})"
  if !missing.isEmpty then throw missing
  return {
    assertion := resolved["assertion"]!,
    cpsTripleWithin := resolved["cpsTripleWithin"]!,
    cpsBranchWithin := resolved["cpsBranchWithin"]!,
    cpsHaltTripleWithin := resolved["cpsHaltTripleWithin"]!,
    cpsNBranchWithin := resolved["cpsNBranchWithin"]!,
    itemsSound := resolved["itemsSound"]!,
    bytesRegion := resolved["bytesRegion"]!,
    memIs := resolved["memIs"]!,
    regIs := resolved["regIs"]!,
    regOwn := resolved["regOwn"]!,
    sepConj := resolved["sepConj"]!,
    ofProg := resolved["ofProg"]!,
    instr := resolved["instr"]!,
    reg := resolved["reg"]! }

def cpsHeadsOf (n : Names) : Std.HashSet Name :=
  Std.HashSet.ofList [n.cpsTripleWithin, n.cpsBranchWithin, n.cpsHaltTripleWithin,
    n.cpsNBranchWithin]

def contractHeadsOf (n : Names) : Std.HashSet Name :=
  (cpsHeadsOf n).insert n.itemsSound

/-- Bundle passed to the alias-expansion walkers so the head sets are built
once per run, not once per application node. -/
structure Ctx where
  env : Environment
  names : Names
  keep : Std.HashSet Name
  tieHeads : Std.HashSet Name
  claimHeads : Std.HashSet Name

def mkCtx (env : Environment) (n : Names) : Ctx where
  env := env
  names := n
  keep := Std.HashSet.ofList
    [n.bytesRegion, n.memIs, n.regIs, n.regOwn, n.sepConj,
     `EvmAsm.Rv64.empAssertion, `EvmAsm.Rv64.assertPure,
     `EvmAsm.Rv64.SAsm.asrtM, `EvmAsm.Rv64.SAsm.Reach,
     `EvmAsm.Rv64.asrtM, `EvmAsm.Rv64.Reach]
  tieHeads := Std.HashSet.ofList [n.bytesRegion, n.memIs]
  claimHeads := Std.HashSet.ofList [n.regIs, n.regOwn]

/-! ## Expression utilities -/

/-- Strip `∀`/`→` binders (and mdata) to expose a type's result. -/
def peelForall : Expr → Expr
  | .forallE _ _ b _ => peelForall b
  | .mdata _ e => peelForall e
  | e => e

/-- Head constant of an application spine (after mdata peeling). -/
def headConst? : Expr → Option Name
  | .app f _ => headConst? f
  | .mdata _ e => headConst? e
  | .const c _ => some c
  | _ => none

/-- Final string segment of a (reportable) name, e.g. `Foo.x5` → `x5`. -/
def lastComponent : Name → String
  | .str _ s => s
  | _ => ""

/-- Structural occurs-check: does constant `n` occur anywhere in `e`? -/
partial def occurs (n : Name) : Expr → Bool
  | .const c _ => c == n
  | .app f a => occurs n f || occurs n a
  | .lam _ t b _ => occurs n t || occurs n b
  | .forallE _ t b _ => occurs n t || occurs n b
  | .letE _ t v b _ => occurs n t || occurs n v || occurs n b
  | .mdata _ e => occurs n e
  | .proj _ _ e => occurs n e
  | _ => false

def occursAny (n : Names) (e : Expr) : Bool :=
  (cpsHeadsOf n).toList.any (occurs · e)

/-- Occurs-check for a de Bruijn index, depth-adjusted under binders. -/
partial def occursBVarAux (idx : Nat) (depth : Nat) : Expr → Bool
  | .bvar i => i == idx + depth
  | .app f a => occursBVarAux idx depth f || occursBVarAux idx depth a
  | .lam _ t b _ => occursBVarAux idx depth t || occursBVarAux idx (depth + 1) b
  | .forallE _ t b _ => occursBVarAux idx depth t || occursBVarAux idx (depth + 1) b
  | .letE _ t v b _ => occursBVarAux idx depth t || occursBVarAux idx depth v
      || occursBVarAux idx (depth + 1) b
  | .mdata _ e => occursBVarAux idx depth e
  | .proj _ _ e => occursBVarAux idx depth e
  | _ => false

def occursBVar (idx : Nat) (e : Expr) : Bool := occursBVarAux idx 0 e

/-- Whether to report a constant (mirrors axiomsweep / satsweep policy). -/
def isReportable (n : Name) : Bool :=
  !n.hasMacroScopes && !((privateToUserName? n).getD n).isInternalDetail

/-- A `def` whose declared result type is literally the `Assertion` constant. -/
def isAssertionDef (n : Names) (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ => (peelForall ci.type).isConstOf n.assertion
  | _ => false

/-! ## Axiom closure (own, memoized; mirrors axiomsweep) -/

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def axiomCleanStd (axs : Array Name) : Bool :=
  axs.all fun a => standardAxioms.any (a == ·)

/-- Collect all constant names occurring in an expression. -/
partial def occursNames (e : Expr) (acc : Array Name) : Array Name :=
  match e with
  | .const c _ => if acc.contains c then acc else acc.push c
  | .app f a => occursNames a (occursNames f acc)
  | .lam _ t b _ => occursNames b (occursNames t acc)
  | .forallE _ t b _ => occursNames b (occursNames t acc)
  | .letE _ t v b _ => occursNames b (occursNames v (occursNames t acc))
  | .mdata _ b => occursNames b acc
  | .proj _ _ b => occursNames b acc
  | _ => acc

/-- Transitive axiom set of a constant (axioms/quotients are the leaves). -/
partial def axiomClosure (env : Environment)
    (memo : Std.HashMap Name (Array Name)) (n : Name) : Std.HashMap Name (Array Name) :=
  Id.run do
  if memo.contains n then return memo
  match env.find? n with
  | some (.axiomInfo _) | some (.quotInfo _) =>
      return memo.insert n #[n]
  | some ci =>
      let mut seeds := occursNames ci.type #[]
      if let some v := ci.value? then seeds := occursNames v seeds
      let mut memo' := memo.insert n #[]  -- cycle guard
      let mut axs : Array Name := #[]
      for c in seeds do
          let m := axiomClosure env memo' c
          memo' := m
          for x in m[c]?.getD #[] do
            if !axs.contains x then axs := axs.push x
      return memo'.insert n axs
  | none => return memo.insert n #[]

/-! ## Alias-expanding walkers (no term reconstruction) -/

/-- Apply a definition's value to a spine. -/
def unfoldDefnApp (env : Environment) (c : Name) (e : Expr) : Expr :=
  match env.find? c with
  | some (.defnInfo di) => (e.getAppArgs.foldl (fun v a => v.app a) di.value).headBeta
  | _ => e

/-- Tie test over the alias-expanded pre: does some argument of a
`bytesRegion`/`memIs` application mention the parameter (depth-adjusted)?
Definitions whose result type is `Assertion` are unfolded transitively with
bounded fuel; `keep` constants are the atoms and combinators.  A parameter
occurring merely *under* a combinator (e.g. inside `assertPure`) is NOT a
tie: only a `bytesRegion`/`memIs` spine mentioning it ties it. -/
partial def tiedInExpanded (ctx : Ctx) (fuel : Nat) (idx : Nat) (depth : Nat)
    (e : Expr) : Bool :=
  if fuel == 0 then false
  else
    let e := e.headBeta
    match e with
    | .app .. =>
        match headConst? e with
        | some c =>
            if ctx.tieHeads.contains c then
              e.getAppArgs.any (occursBVarAux idx depth)
            else if ctx.keep.contains c then
              -- recurse into the combinator's arguments looking for a tie
              e.getAppArgs.any (tiedInExpanded ctx (fuel - 1) idx depth)
            else
              match ctx.env.find? c with
              | some (.defnInfo di) =>
                  if (peelForall di.type).isConstOf ctx.names.assertion then
                    let body := unfoldDefnApp ctx.env c e
                    tiedInExpanded ctx (fuel - 1) idx depth body
                  else
                    e.getAppArgs.any (tiedInExpanded ctx (fuel - 1) idx depth)
              | _ =>
                  e.getAppArgs.any (tiedInExpanded ctx (fuel - 1) idx depth)
        | none => false
    | .lam _ t b _ =>
        tiedInExpanded ctx fuel idx depth t
          || tiedInExpanded ctx fuel idx (depth + 1) b
    | .forallE _ t b _ =>
        tiedInExpanded ctx fuel idx depth t
          || tiedInExpanded ctx fuel idx (depth + 1) b
    | .letE _ t v b _ =>
        tiedInExpanded ctx fuel idx depth t || tiedInExpanded ctx fuel idx depth v
          || tiedInExpanded ctx fuel idx (depth + 1) b
    | .mdata _ b => tiedInExpanded ctx fuel idx depth b
    | .proj _ _ b => tiedInExpanded ctx fuel idx depth b
    | _ => false

/-- Registers claimed (by `regIs`/`regOwn` atoms) in the alias-expanded pre,
as short register names (`x5`). -/
partial def claimedRegs (ctx : Ctx) (fuel : Nat) (e : Expr)
    (acc : Array String) : Array String :=
  if fuel == 0 then acc
  else
    let e := e.headBeta
    match e with
    | .app .. =>
        match headConst? e with
        | some c =>
            let acc' : Array String :=
              if ctx.claimHeads.contains c then
                match e.getAppArgs[0]? with
                | some (Expr.const r _) =>
                    let nm := lastComponent r
                    if nm != "x0" && !acc.contains nm then acc.push nm else acc
                | _ => acc
              else acc
            if ctx.keep.contains c then
              e.getAppArgs.foldl (init := acc') fun a x => claimedRegs ctx (fuel - 1) x a
            else
              match ctx.env.find? c with
              | some (.defnInfo di) =>
                  if (peelForall di.type).isConstOf ctx.names.assertion then
                    let body := unfoldDefnApp ctx.env c e
                    claimedRegs ctx (fuel - 1) body acc'
                  else
                    e.getAppArgs.foldl (init := acc') fun a x =>
                      claimedRegs ctx (fuel - 1) x a
              | _ =>
                  e.getAppArgs.foldl (init := acc') fun a x =>
                    claimedRegs ctx (fuel - 1) x a
        | none => acc
    | .lam _ t b _ =>
      claimedRegs ctx fuel b (claimedRegs ctx fuel t acc)
    | .forallE _ t b _ =>
      claimedRegs ctx fuel b (claimedRegs ctx fuel t acc)
    | .letE _ _ v b _ =>
      claimedRegs ctx fuel b (claimedRegs ctx fuel v acc)
    | .mdata _ b => claimedRegs ctx fuel b acc
    | .proj _ _ b => claimedRegs ctx fuel b acc
    | _ => acc

/-! ## The `Instr` destination table (signature B) -/

/-- Constructors of `Instr` whose field 0 is the written destination
register.  Every dest-writing constructor in this RV64IM model has `rd`
first (checked against `Basic.lean`); stores, branches, `NOP`, `ECALL`,
`FENCE`, `EBREAK` and `CSRS` write no register.  Startup diff-checks this
table against the environment's constructor list — an unknown constructor is
counted as a table gap, never silently treated as non-writing. -/
def destCtors : List String :=
  ["ADD","SUB","SLL","SRL","SRA","AND","OR","XOR","SLT","SLTU",
   "ADDI","ANDI","ORI","XORI","SLTI","SLTIU","SLLI","SRLI","SRAI","ADDIW",
   "LUI","AUIPC","LD","LW","LWU","LB","LH","LBU","LHU",
   "JAL","JALR","MV","LI",
   "MUL","MULH","MULHSU","MULHU","DIV","DIVU","REM","REMU"]

/-- Constructors known to write no register. -/
def nonWritingCtors : List String :=
  ["SD","SW","SB","SH","BEQ","BNE","BLT","BGE","BLTU","BGEU",
   "NOP","ECALL","FENCE","EBREAK","CSRS"]

structure InstrSite where
  ctor : Name
  args : Array Expr

/-- Walk a `List Instr` value (cons/nil/append/definition-unfolding)
collecting instruction sites.  Returns `none` on an unrecognised spine
(reported as `progUnresolved`, never guessed). -/
partial def collectInstrs (env : Environment)
    (fuel : Nat) (e : Expr) (acc : Array InstrSite) : Option (Array InstrSite) :=
  if fuel == 0 then none
  else
    let e := e.headBeta
    match headConst? e with
    | some c =>
        if c == `List.nil then some acc
        else if c == `List.cons then
          match e.getAppArgs with
          | #[_ty, hd, tl] =>
              collectInstrs env (fuel - 1) tl
                (acc.push { ctor := (headConst? hd).getD Name.anonymous, args := hd.getAppArgs })
          | _ => none
        else if c == `HAppend.hAppend then
          let args := e.getAppArgs
          let n := args.size
          if n ≥ 2 then
            match collectInstrs env (fuel - 1) args[n - 2]! acc with
            | some acc' => collectInstrs env (fuel - 1) args[n - 1]! acc'
            | none => none
          else none
        else
          match env.find? c with
          | some (.defnInfo _) =>
              let body := unfoldDefnApp env c e
              collectInstrs env (fuel - 1) body acc
          | _ => none
    | none => none

/-- Registers written by the collected sites.  Returns (written, tableGaps):
unknown constructors under-approximate the write set and are reported. -/
def writtenRegs (sites : Array InstrSite) : Array String × Array String := Id.run do
  let mut written : Array String := #[]
  let mut gaps : Array String := #[]
  for s in sites do
    let cn := lastComponent s.ctor
    if destCtors.contains cn then
      match s.args[0]? with
      | some (Expr.const r _) =>
        let nm := lastComponent r
        if nm != "x0" && !written.contains nm then written := written.push nm
      | _ => pure ()
    else if !nonWritingCtors.contains cn then
      if !gaps.contains cn then gaps := gaps.push cn
  return (written, gaps)

/-- Resolve a `cr` spine to the `List Instr`-valued program constant behind
`CodeReq.ofProg base prog`, unfolding non-`ofProg` definition heads with
bounded fuel.  Returns `none` when the spine is unrecognised (counted, not
guessed). -/
partial def resolveOfProg (ctx : Ctx) (fuel : Nat) (e : Expr) : Option Name :=
  if fuel == 0 then none
  else
    let e := e.headBeta
    match e with
    | .const p _ => if p == ctx.names.ofProg then none else some p
    | .app .. =>
        match headConst? e with
        | some c =>
            if c == ctx.names.ofProg then
              let args := e.getAppArgs
              if args.size ≥ 2 then
                match args[args.size - 1]! with
                | .const p _ => some p
                | _ => none
              else none
            else
              match ctx.env.find? c with
              | some (.defnInfo _) =>
                  let body := unfoldDefnApp ctx.env c e
                  resolveOfProg ctx (fuel - 1) body
              | _ => none
        | none => none
    | _ => none

/-! ## Site extraction -/

structure CpsSite where
  pred : Name
  cr : Expr
  pre : Expr
  posts : Array Expr
  depth : Nat

structure ByteParam where
  pos : Nat
  name : Name

/-- Argument extraction per cps predicate: (cr, pre, posts) by 0-based
argument position in the elaborated application spine (all binders explicit
in `CPSSpec.lean`). -/
def siteArgs (n : Names) (c : Name) (args : Array Expr) :
    Option (Expr × Expr × Array Expr) :=
  if c == n.cpsTripleWithin then
    -- nSteps entry exit_ cr P Q
    if args.size ≥ 6 then some (args[3]!, args[4]!, #[args[5]!]) else none
  else if c == n.cpsHaltTripleWithin then
    -- nSteps entry cr P Q
    if args.size ≥ 5 then some (args[2]!, args[3]!, #[args[4]!]) else none
  else if c == n.cpsBranchWithin then
    -- nSteps entry cr P exit_t Q_t exit_f Q_f
    if args.size ≥ 8 then some (args[2]!, args[3]!, #[args[5]!, args[7]!]) else none
  else if c == n.cpsNBranchWithin then
    -- nSteps entry cr P exits ; posts = the exits payload (conservative)
    if args.size ≥ 5 then some (args[2]!, args[3]!, #[args[4]!]) else none
  else none

def isByteListType (t : Expr) : Bool :=
  match peelForall t with
  | .app (.const lc _) (.app (.const bv _) (.lit (.natVal 8))) => lc == `List && bv == `BitVec
  | _ => false

/-- Extract byte-list parameters and cps applications from a closed
declaration type.  `depth` counts binders entered; a parameter recorded at
position `p` has de Bruijn index `siteDepth - 1 - p` at a site of depth
`siteDepth`. -/
partial def extractSites (n : Names) (e : Expr) (depth : Nat)
    (params : Array ByteParam) (sites : Array CpsSite) :
    Array ByteParam × Array CpsSite :=
  match e with
  | .forallE bn t b _ =>
      let params := if isByteListType t then params.push { pos := depth, name := bn } else params
      let (params, sites) := extractSites n t depth params sites
      extractSites n b (depth + 1) params sites
  | .mdata _ b => extractSites n b depth params sites
  | .letE _ _ _ b _ => extractSites n b (depth + 1) params sites
  | .app .. =>
      match headConst? e with
      | none => (params, sites)
      | some c =>
          if (cpsHeadsOf n).contains c then
            match siteArgs n c e.getAppArgs with
            | some (cr, pre, posts) =>
                (params, sites.push
                  { pred := c, cr := cr, pre := pre, posts := posts, depth := depth })
            | none => (params, sites)
          else
            e.getAppArgs.foldl (init := (params, sites)) fun (ps, ss) a =>
              extractSites n a depth ps ss
  | _ => (params, sites)

/-- Does the declaration's type contain a contract-typed hypothesis binder
(a cps predicate or `ItemsSound` application)? -/
partial def hasContractHypothesis (heads : Std.HashSet Name) : Expr → Bool
  | .forallE _ t b _ =>
      (match headConst? (peelForall t) with
       | some c => heads.contains c
       | none => false) || hasContractHypothesis heads b
  | .mdata _ b => hasContractHypothesis heads b
  | .letE _ _ _ b _ => hasContractHypothesis heads b
  | .app f a => hasContractHypothesis heads f || hasContractHypothesis heads a
  | _ => false

/-! ## Report rows -/

structure Row where
  host : String
  module : String
  line : Option Nat
  kind : String          -- "hypHost" | "sigA" | "sigB" | "crUnresolved" | "progUnresolved"
  detail : String
  deriving ToJson

/-- Row constructor (kept single-line: Lean's structure-instance parser
enforces column alignment across lines). -/
def mkRow (host module : String) (line : Option Nat) (kind detail : String) : Row :=
  { host := host, module := module, line := line, kind := kind, detail := detail }

/-! ## Self-test -/

def selfTest (ctx : Ctx) : Bool × Array String := Id.run do
  let mut ok := true
  let mut log : Array String := #[]
  let n := ctx.names
  -- (1) a bytesRegion tie mentioning bvar 0 is detected
  let tie := mkApp2 (mkConst n.bytesRegion) (.bvar 0) (.const `List.nil [])
  if !(tiedInExpanded ctx 20 0 0 tie) then
    ok := false; log := log.push "FAIL: bytesRegion tie not detected"
  else log := log.push "pass: bytesRegion tie detected"
  -- (2) occurrence under assertPure (a keep combinator, not an ownership
  -- atom) is NOT a tie
  let notie := mkApp2 (mkConst `EvmAsm.Rv64.assertPure) (.bvar 0)
    (mkConst `EvmAsm.Rv64.empAssertion)
  if tiedInExpanded ctx 20 0 0 notie then
    ok := false; log := log.push "FAIL: tie reported where none exists"
  else log := log.push "pass: no false tie"
  -- (3) bvar occurs check
  if !(occursBVar 0 (.bvar 0)) then
    ok := false; log := log.push "FAIL: occursBVar broken"
  else log := log.push "pass: occursBVar"
  -- (4)+(5) instruction write-set extraction and dest-table completeness
  match ctx.env.find? n.instr with
  | some (.inductInfo ii) =>
      let addCtor := ii.ctors.find? (lastComponent · == "ADD") |>.getD Name.anonymous
      let x5 := mkConst (n.reg.str "x5")
      let x6 := mkConst (n.reg.str "x6")
      let x7 := mkConst (n.reg.str "x7")
      let add := mkApp3 (mkConst addCtor) x5 x6 x7
      let nil := (mkConst `List.nil).app (mkConst n.instr)
      let lst := mkApp3 (mkConst `List.cons) (mkConst n.instr) add nil
      match collectInstrs ctx.env 100 lst #[] with
      | some sites =>
          let (written, gaps) := writtenRegs sites
          if written == #["x5"] && gaps.isEmpty then
            log := log.push "pass: write set of ADD x5,x6,x7 = {x5}"
          else
            ok := false
            log := log.push s!"FAIL: write set {written.toList} gaps {gaps.toList}"
      | none =>
          ok := false; log := log.push "FAIL: collectInstrs returned none on cons literal"
      let gaps := ii.ctors.filter fun c =>
        let cn := lastComponent c
        !destCtors.contains cn && !nonWritingCtors.contains cn
      if gaps.isEmpty then
        log := log.push "pass: dest table covers every Instr constructor"
      else
        ok := false
        log := log.push s!"FAIL: dest table gaps: {gaps.map lastComponent}"
  | _ =>
      ok := false; log := log.push "FAIL: Instr inductive not found"
  -- (6) claimed-reg extraction: regIs x6 v claims x6
  let claim := mkApp2 (mkConst n.regIs) (mkConst (n.reg.str "x6")) (.bvar 0)
  let claimed := claimedRegs ctx 20 claim #[]
  if claimed == #["x6"] then log := log.push "pass: claimedRegs = {x6}"
  else ok := false; log := log.push s!"FAIL: claimedRegs {claimed.toList}"
  -- (7) siteArgs positions on a synthetic cpsTripleWithin spine
  let crArg : Expr := .const `foo []
  let preArg : Expr := .bvar 3
  let postArg : Expr := .bvar 2
  let spine := mkApp6 (mkConst n.cpsTripleWithin) (.lit (.natVal 1)) crArg crArg crArg preArg postArg
  match siteArgs n n.cpsTripleWithin spine.getAppArgs with
  | some (cr, pre, posts) =>
      if cr == crArg && pre == preArg && posts == #[postArg] then
        log := log.push "pass: siteArgs extracts (cr, pre, post) positions"
      else
        ok := false; log := log.push "FAIL: siteArgs wrong positions"
  | none =>
      ok := false; log := log.push "FAIL: siteArgs returned none on full spine"
  return (ok, log)

/-! ## Main walk -/

structure Config where
  roots : Array Name := #[]
  out? : Option String := none
  verbose : Bool := false
  selfTestOnly : Bool := false

def parseArgs : List String → Config → Except String Config
  | [], cfg => .ok cfg
  | "--out" :: path :: rest, cfg => parseArgs rest { cfg with out? := some path }
  | "--verbose" :: rest, cfg => parseArgs rest { cfg with verbose := true }
  | "--self-test" :: rest, cfg => parseArgs rest { cfg with selfTestOnly := true }
  | "--root" :: mod :: rest, cfg =>
      parseArgs rest { cfg with roots := cfg.roots.push mod.toName }
  | arg :: _, _ => .error s!"footsweep: unknown or incomplete argument: {arg}\n\
      usage: lake exe footsweep [--out FILE] [--verbose] [--self-test] [--root MOD]*"

structure SweepResult where
  declCount : Nat
  moduleCount : Nat
  safeCount : Nat
  assertionDefCount : Nat
  anchoredCount : Nat
  hypHostCount : Nat
  sigACount : Nat
  sigBCount : Nat
  crUnresolved : Nat
  progUnresolved : Nat
  instrGaps : Array String
  rows : Array Row

/-- The environment walk: passes 1-3.  Runs in `CoreM` so
`findDeclarationRanges?` can read the imported environment (same shape as
satsweep). -/
def sweep (ctx : Ctx) (roots : Array Name) : CoreM SweepResult := do
  let names := ctx.names
  let env := ctx.env
  let cpsHeads := cpsHeadsOf names
  let contractHeads := contractHeadsOf names
  let mut moduleCount := 0
  let mut decls : Array (Name × Name) := #[]   -- (const, module)
  let mut seen : Std.HashSet Name := {}
  for (mname, mdata) in env.header.moduleNames.zip env.header.moduleData do
    if roots.any (·.isPrefixOf mname) then
      moduleCount := moduleCount + 1
      for c in mdata.constNames do
        if isReportable c && !seen.contains c then
          seen := seen.insert c
          decls := decls.push (c, mname)

  -- Pass 1: classify theorems; safe class = cps-concluded, no contract
  -- hypothesis, axiom-clean.  Safe types anchor the contract abbrevs.
  let mut safeCount := 0
  let mut axiomMemo : Std.HashMap Name (Array Name) := {}
  let mut anchored : Std.HashSet Name := {}
  let mut hypHosts : Array Name := #[]         -- theorems assuming contracts
  let mut assertionDefs : Array Name := #[]
  for (c, _) in decls do
    let some ci := env.find? c | continue
    match ci with
    | .thmInfo _ =>
        let tyHead := headConst? (peelForall ci.type)
        let isCps := tyHead.any (cpsHeads.contains ·)
        let hasHyp := hasContractHypothesis contractHeads ci.type
        if hasHyp then hypHosts := hypHosts.push c
        if isCps && !hasHyp then
          axiomMemo := axiomClosure env axiomMemo c
          if axiomCleanStd (axiomMemo[c]?.getD #[]) then
            safeCount := safeCount + 1
            for k in occursNames ci.type #[] do
              anchored := anchored.insert k
    | .defnInfo _ =>
        if isAssertionDef names ci then assertionDefs := assertionDefs.push c
    | _ => pure ()

  -- Pass 2: referencedness (name occurs in another decl's type or value)
  let mut referenced : Std.HashSet Name := {}
  for (c, _) in decls do
    let some ci := env.find? c | continue
    let base := occursNames ci.type #[]
    let base := match ci.value? with | some v => occursNames v base | none => base
    for k in base do
      if k != c then referenced := referenced.insert k

  -- Pass 3: at-risk rows
  let mut rows : Array Row := #[]
  let mut rowKeys : Std.HashSet String := ∅
  let mut sigACount := 0
  let mut sigBCount := 0
  let mut crUnresolved := 0
  let mut progUnresolved := 0
  let mut instrGaps : Array String := #[]
  for (c, mname) in decls do
    let some ci := env.find? c | continue
    let isSafe := match ci with
      | .thmInfo _ =>
          (headConst? (peelForall ci.type)).any (cpsHeads.contains ·)
            && !(hasContractHypothesis contractHeads ci.type)
            && axiomCleanStd (axiomMemo[c]?.getD #[])
      | _ => false
    if isSafe then continue
    let isThm := match ci with | .thmInfo _ => true | _ => false
    let hasCps := occursAny names ci.type
    let hasHyp := hasContractHypothesis contractHeads ci.type
    if !hasCps && !(hasHyp && isThm) then continue
    let ranges? ← findDeclarationRanges? c
    let line := ranges?.map (·.range.pos.line)
    if hasHyp && isThm then
      let status := if referenced.contains c then "assumed (referenced elsewhere)" else
        "undischarged (never referenced)"
      rows := rows.push (mkRow c.toString mname.toString line "hypHost" status)
    if hasCps then
      let (params, sites) := extractSites names ci.type 0 #[] #[]
      for s in sites do
        -- Signature A: byte-list param free in a post, untied in the
        -- alias-expanded pre.
        for p in params do
          if p.pos < s.depth then
            let idx := s.depth - 1 - p.pos
            let inPost := s.posts.any (occursBVar idx ·)
            let tied := tiedInExpanded ctx 60 idx 0 s.pre
            if inPost && !tied then
              let detail := s!"param {p.name} free in post, untied in expanded pre ({s.pred})"
              let key := c.toString ++ "|sigA|" ++ detail
              if !rowKeys.contains key then
                rowKeys := rowKeys.insert key
                sigACount := sigACount + 1
                rows := rows.push (mkRow c.toString mname.toString line "sigA" detail)
        -- Signature B: written registers unclaimed in the expanded pre.
        match resolveOfProg ctx 30 s.cr with
        | some progName =>
            let some (.defnInfo pdi) := env.find? progName | continue
            match collectInstrs env 200000 pdi.value #[] with
            | some instrs =>
                let (written, gaps) := writtenRegs instrs
                for g in gaps do
                  if !instrGaps.contains g then instrGaps := instrGaps.push g
                if !written.isEmpty then
                  let claimed := claimedRegs ctx 80 s.pre #[]
                  let unclaimed := written.filter (fun r => r.front == 'x' && !claimed.contains r)
                  if !unclaimed.isEmpty then
                    let detail := s!"{progName} writes {unclaimed.toList} unclaimed in pre"
                    let key := c.toString ++ "|sigB|" ++ detail
                    if !rowKeys.contains key then
                      rowKeys := rowKeys.insert key
                      sigBCount := sigBCount + 1
                      rows := rows.push (mkRow c.toString mname.toString line "sigB" detail)
            | none =>
              progUnresolved := progUnresolved + 1
        | none =>
          crUnresolved := crUnresolved + 1

  let anchoredCount := (assertionDefs.filter (anchored.contains ·)).size
  return { declCount := decls.size, moduleCount := moduleCount, safeCount := safeCount, assertionDefCount := assertionDefs.size, anchoredCount := anchoredCount, hypHostCount := hypHosts.size, sigACount := sigACount, sigBCount := sigBCount, crUnresolved := crUnresolved, progUnresolved := progUnresolved, instrGaps := instrGaps, rows := rows }

end FootSweep

open FootSweep in
unsafe def main (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args {} with
    | .ok cfg => pure cfg
    | .error e => IO.eprintln e; return 2
  let roots := if cfg.roots.isEmpty then defaultRoots else cfg.roots
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← try
      importModules (roots.map ({ module := · })) {} (trustLevel := 1024) (loadExts := true)
    catch e =>
      IO.eprintln s!"footsweep: cannot import root modules {roots}: {e.toString}"
      return 2
  let names ← match resolveNames env with
    | .ok n => pure n
    | .error missing =>
        IO.eprintln s!"footsweep: unresolved core names (infra): {missing.toList}"
        return 2
  let ctx := mkCtx env names
  let (stOk, stLog) := selfTest ctx
  for l in stLog do IO.println l
  if cfg.selfTestOnly then
    if stOk then IO.println "footsweep self-test: PASS"; return 0
    else IO.eprintln "footsweep self-test: FAIL"; return 2
  if !stOk then
    IO.eprintln "footsweep: self-test failed; refusing to report (infra)"
    return 2

  let (result, _) ← (sweep ctx roots).toIO { fileName := "<footsweep>", fileMap := default } { env }
  let unanchoredDefs := result.assertionDefCount - result.anchoredCount

  IO.println s!"footsweep: {result.declCount} reportable declarations across {result.moduleCount} modules under {roots}"
  IO.println s!"  safe-class theorems (cps-concluded, contract-hyp-free, axiom-clean): {result.safeCount}"
  IO.println s!"  Assertion-valued defs: {result.assertionDefCount} (anchored {result.anchoredCount}, UNANCHORED {unanchoredDefs})"
  IO.println s!"  contract-hypothesis hosts (theorems): {result.hypHostCount}"
  IO.println s!"  sigA hits (byte-list param free in post, untied in pre): {result.sigACount}"
  IO.println s!"  sigB hits (written register unclaimed in pre): {result.sigBCount}"
  IO.println s!"  cr unresolved (no ofProg spine): {result.crUnresolved}; prog unresolved: {result.progUnresolved}"
  if !result.instrGaps.isEmpty then
    IO.println s!"  INSTR TABLE GAPS (write sets under-approximated): {result.instrGaps.toList}"
  if cfg.verbose then
    for r in result.rows do
      IO.println s!"  [{r.kind}] {r.host} ({r.module}:{r.line.getD 0}): {r.detail}"
  if let some out := cfg.out? then
    let report := Json.mkObj [
      ("roots", toJson (roots.map (·.toString))),
      ("declarationCount", toJson result.declCount),
      ("moduleCount", toJson result.moduleCount),
      ("safeClass", toJson result.safeCount),
      ("assertionDefs", toJson result.assertionDefCount),
      ("anchoredDefs", toJson result.anchoredCount),
      ("unanchoredDefs", toJson unanchoredDefs),
      ("hypHosts", toJson result.hypHostCount),
      ("sigA", toJson result.sigACount),
      ("sigB", toJson result.sigBCount),
      ("crUnresolved", toJson result.crUnresolved),
      ("progUnresolved", toJson result.progUnresolved),
      ("instrTableGaps", toJson result.instrGaps),
      ("rows", toJson result.rows)]
    IO.FS.writeFile out (report.pretty ++ "\n")
    IO.println s!"footsweep: wrote report to {out}"
  IO.println "footsweep: advisory census; exit 0 always"
  return 0
