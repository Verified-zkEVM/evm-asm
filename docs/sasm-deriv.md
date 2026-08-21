# Proof-first SAsm: `DCode` derivations

*Files: `EvmAsm/Rv64/SAsm/Deriv.lean` (the layer), `EvmAsm/Rv64/SAsm/VcExists.lean`
(supporting `sp`/`vcs` lemmas), `EvmAsm/Rv64/SAsm/DerivDemo.lean` (worked examples).*

*Landed real-guest ports (byte-identical to the emitted routines; copy
these as exemplars): `Codegen/Programs/CallFrameForwardGasSAsm.lean`
(register-only ite/when; note the `li`-expansion layout rule),
`ExecLogAddrToBalCanonicalSAsm.lean` (read-region → writable-window
reverse copy via `dwhileHeader`, reusing `revWin`),
`WcidxSwapRecordsSAsm.lean` (in-arena dword swap via `when` + `dwhile`,
unified over the equal-pointer skip).*

## What this is

The classic SAsm workflow is **code-first**: write a `Stmt`, wrap it in an `Fn`,
run `vcgen`, then discover what the code actually does while discharging VCs.
That order is why register clobbering and endianness mistakes historically
surfaced *late* — after the code existed, sometimes after several proof files.

The derivation layer inverts this: you write a **constructive separation-logic
proof first** — a calc-style chain from the precondition to the postcondition —
and the RISC-V code is **generated from the proof**. Each step of the chain
either

- transforms the assertion with **zero instructions** (an entailment/iff of
  assertions, or a ghost fold/unfold of the ambient assertion), or
- attaches a **block of instructions / a call** together with the proof that it
  carries the step's pre to its post.

Because `Prop` has proof irrelevance, nothing can be extracted from a `Prop`
proof — so the derivation lives in `Type`:

```
DStmt reg rw : Stmt → Reach → Reach → Type
DCode reg rw (P Q : Reach) := (S : Stmt) × DStmt reg rw S P Q
```

The erased `Stmt` is a **type index**. That is the load-bearing trick: whenever
two derivations must share machine code (all iterations of a loop body), the
index forces one code skeleton by unification, and an accidental dependence of
*code* on a ghost variable fails **at elaboration, at that step** — not three
proof files later. Assertions may mention ghosts freely; instructions may not.

Soundness is once-and-for-all: `DStmt.vcs_hold` and `DStmt.post_sound` (by
induction on the derivation) produce exactly the VC list of `Stmt.vcs`, so
`DCode.fn_spec` plugs into the existing `Fn.sound` and yields the ordinary
bounded CPS triple `cpsTripleWithin` — the step bound `Stmt.steps` comes with
it. Extraction is `DCode.program` = `Stmt.flatten`, i.e. the same bytes every
other pipeline stage (handles, drift guards, codegen emitters) already consumes.
Nothing downstream changes; a `DCode`-produced `Fn` is an ordinary `Fn`.

## Writing a derivation

Set up a local relation for your region context and write a `calc`:

```lean
local infix:36 " ⤳ " => DCode myRegion myRw

def myRoutine (ghosts…) :
    (fun rf ws A => …pre… ) ⤳ (fun rf ws A => …post… ) :=
  calc (fun rf ws A => …pre… : Reach)
    _ ⤳ (fun rf ws A => …mid… : Reach) :=
      DCode.block "load" [ .LD .x10 .x11 0, … ] (by decide)
        (mem-safety obligation)  (semantic step: execBlock result ⊨ mid)
    _ ⤳ (fun rf ws A => …mid'… : Reach) :=
      DCode.pure "shuffle" (fun rf ws A h => …entailment…)   -- 0 instructions
    _ ⤳ (fun rf ws A => …post… : Reach) :=
      DCode.ite "cmp" (.bltu .x10 .x11) thenDeriv elseDeriv
```

**Always ascribe `: Reach` on calc endpoints written as lambdas** (a `Trans`
instance exists for both the folded and unfolded endpoint type, but the
ascription keeps elaboration predictable and the chain readable).

`Trans` is wired up, so plain `calc` composes steps (`DCode.seq` directly also
works, as does building the value with `refine`/tactics — tactic mode can
define values of any type). Endpoints are `Reach` predicates
(`RegFile → List (BitVec 8) → Assertion → Prop`), the same symbolic-state
vocabulary as all SAsm VCs, so every existing recipe in `docs/sasm-howto.md`
for `.mem`/`.post`-shaped goals applies verbatim to the obligations inside a
step.

### Step vocabulary (v1)

| step | instructions | obligations carried |
|---|---|---|
| `DCode.pure lbl h` | 0 (erases to a `True`-annotated `.assert`) | `P ⊢ Q` pointwise |
| `DCode.ghost lbl Rr h` | 0 | ambient-assertion replacement (fold/unfold), post is the exact `sp` shape |
| `DCode.block lbl is hok hmem hpost` | `is` | `blockOk` (`by decide`), memory VCs (only if the block loads), semantic step via `execBlock` |
| `DCode.blockAt lbl p winR is …` | `is` | focus decomposition + mem VCs + semantic step over the focused window |
| `DCode.readAt lbl p roR is …` | `is` | read-focus analogue |
| `DCode.call lbl f hpre hpost` | 1 (`jal`) | `P ⊢ f.pre`, `f.post ⊢ Q` |
| `DCode.ite lbl c thn els` | arms + 2 | arms start from `P ∧ c` / `P ∧ ¬c`, both reach the same `Q` |
| `DCode.when lbl c body hskip` | body + 1 | body from `P ∧ c` to `Q`; skip path `P ∧ ¬c ⊢ Q` |
| `DCode.dwhile lbl c fuel inv hinit body hexh` | body + 2 | see below |
| `DCode.doWhile lbl c fuel inv bodyEntry bodyIter hexh` | body + 1 | bottom-test variant |
| `DCode.dwhileS lbl c fuel inv hinit body hexh` | body + 2 | snapshot loop — the nested-loop construct, see below |
| `DCode.doWhileS lbl c fuel inv bodyEntry bodyIter hexh` | body + 1 | bottom-test snapshot loop (the converters' idiom) |
| `DCode.dwhileBreak lbl g fuel inv mid br hinit bb ba hexh hguard hbreak` | bb + ba + 3 | scan-until-found, see below |
| `DCode.dwhileHeader lbl c fuel inv mid hE hI body hexh` | header·(1) + body + 2 | reloaded-header loop (`li`-reloaded guard limits): header entry run `P ⤳ inv 0`, per-iteration rerun `i < fuel ∧ mid i ⤳ inv (i+1)` |
| `DCode.callAt lbl roR f …` | 1 (`jal`) | focus decomposition of the ambient into the callee's `bytesRegion` + `rest`; callee pre/post against `empAssertion` ambient |
| `DCode.blockA lbl addr is hok hmem hpost` | `is` | **PC-aware block** (`la`/`AUIPC`): obligations mirror `block` on the PC-threaded engine (`execBlockAt` at the carried placement address); caller-shaped path only — see below |
| `DCode.retJalr lbl` | 1 (`jalr ra`) | return through `ra`; ret-shaped derivations only |
| `DCode.dretIf lbl c thn els` | arms + 1 | branch to two RET-TERMINATED tails (no rejoin); arms from `P ∧ ±c` to one `Q`, at their own `ret`s |
| `DCode.dretCascade lbl stages inv B hinit hchain okD badD` | Σ(stage+1) + ok + bad | guard cascade with a SHARED ret-terminated bad tail — see below |

For a load-free block, discharge `hmem` with `fun h => absurd h (by decide)`.

**Calc endpoints**: always write them as explicit lambdas ascribed `: Reach` —
if you have a named predicate, eta-expand it
(`(fun rf ws A => myInv j rf ws A : Reach)`, not `(myInv j : Reach)`).
Mixing folded and unfolded endpoint types across steps breaks the `Trans`
instance match (`Reach` is a plain def, opaque to instance unification).

**Pure steps are always index-safe**: `DCode.pure` erases to a
`True`-annotated `.assert` — the entailment lives in the derivation, not in
the code — so pure steps inside a loop body may mention the iteration index
freely.  `ghost` relations, by contrast, ARE part of the code skeleton
(they drive the ambient-assertion replacement), so a ghost step inside a
loop body must keep its relation index-free (relate `A` to `A'` through the
current state, the usual SAsm idiom).

### if/fi

Between `ite`'s if and fi, execution splits; **pre- and postconditions match
modulo the condition**: `thn : (P ∧ c) ⤳ Q`, `els : (P ∧ ¬c) ⤳ Q`. An arm that
needs no code is a `DCode.pure` (see `umax` in the demo — the else-arm is
pure). `when` is the elseless form; its skip path is a pure entailment.

### Loops

```lean
DCode.dwhile "loop" (.bne .x5 .x0) fuel inv
  hinit                    -- P ⊢ inv 0
  (fun i => …body…)        -- (i < fuel ∧ inv i ∧ c) ⤳ inv (i+1)
  hexh                     -- inv fuel ⊢ ¬c
```

- The body is a **family over the iteration index** `i : Nat`. Its assertions
  (`inv i`, intermediate endpoints) may mention `i`; its **code may not** — the
  `hcode` autoparam checks `∀ i, (body i).1 = (body 0).1` by `rfl`, and fails
  at the `dwhile` if the instruction skeleton depends on `i`
  ("could not synthesize default value for parameter 'hcode'").
- The loop's post is the exact exit shape
  `(∃ i ≤ fuel, inv i) ∧ ¬c` — follow it with a `DCode.pure` step that
  massages it into your stated post (derive the terminal index from the failed
  guard, as in the demo's `countdown`).
- `fuel` is a static bound (an annotation, part of the code index): it cannot
  depend on loop-local ghosts. Runtime-dependent trip counts use the usual
  static-cap-plus-guard-exit idiom.
- `doWhile` (bottom-test) takes the unconditional first run (`P ⤳ inv 0`) and
  the guarded reruns separately; both must share one skeleton (same autoparam).

### Nested loops: `dwhileS` / `doWhileS`

An **inner** loop's `inv` is an annotation inside the shared code skeleton,
so it must not mention an *outer* iteration index.  Outer facts survive
through the **entry snapshot** instead: `dwhileS` takes
`inv : RegFile → List (BitVec 8) → Assertion → Nat → Reach`, and every
obligation carries both the snapshot `(rf₀, ws₀, A₀)` — the state at loop
entry — and the entry-reach fact `P rf₀ ws₀ A₀`.  The body family is
`(rf₀ ws₀ A₀ i) → (P rf₀ ws₀ A₀ ∧ i < fuel ∧ inv rf₀ ws₀ A₀ i ∧ c)
⤳ inv rf₀ ws₀ A₀ (i+1)`; the exit shape is
`∃ rf₀ ws₀ A₀, P rf₀ ws₀ A₀ ∧ (∃ i ≤ fuel, inv rf₀ ws₀ A₀ i) ∧ ¬c`,
and the following pure step recovers the outer-indexed facts because any
snapshot satisfying the (outer-indexed) entry reach pins them — see the
demo's `nested` (`nestedBody`'s `iexit` step).  `doWhileS` is the
bottom-test sibling (entry run from the exact snapshot state, per
`Reach.exact`).

### Scan-until-found: `dwhileBreak`

`dwhileBreak` is the structured mid-body early exit: per iteration,
`bodyBefore` runs from `i < fuel ∧ inv i ∧ guard` to the mid-states
`mid i`; if `breakCond` holds control exits, otherwise `bodyAfter` runs
from `i < fuel ∧ mid i ∧ ¬breakCond` back to `inv (i+1)`.  Both exits
must entail the same `Q`: `hguard` (guard failed, `inv i` at some
`i ≤ fuel`) and `hbreak` (`mid i` with the break condition, `i < fuel`).
Encode reachability in `inv` (e.g. `i ≤ 1` when the break always fires by
the second iteration) to make impossible exits vacuous — see the demo's
`scanBreak`.  `mid` is derivation-only (not a code annotation), so it may
mention ambient ghosts freely.

### Packaging and extraction

```lean
def myFn : Fn := (myRoutine …).fn "myRoutine"       -- an ordinary SAsm Fn
def myProg : Program := (myRoutine …).program base  -- the generated bytes

theorem myFn_spec (base : Word) : myFn.Spec base :=
  DCode.fn_spec "myRoutine" (myRoutine …) base hRegionWf hRwWf
```

The three layout side conditions of `fn_spec` (`callFree`, `offsetsOk`, size
bound) are autoparams closed by `rfl` — they work under symbolic ghost binders
where `decide` would refuse the free variables. `Fn.toHandle` then packages the
result as a callee handle exactly as for any other verified `Fn`; derivations
containing `.call` steps use `DCode.fn_specR` (the `Fn.SpecR` path, with the
usual `CalleesIn`/`callsOk` side conditions).

### PC-aware blocks (`la`/`AUIPC`): `blockA`

`DCode.blockA` carries its own placement address and runs on the
PC-threaded engine, so a `la` prologue (`auipc`+`addi` with concrete
`AsmReloc.laHi/laLo` immediates) verifies inside the derivation.  Two
constraints follow from the design (`Stmt.blockA`):

- **Caller-shaped path only**: the placement address is pinned by
  `callsOk`, which only `Stmt.soundR` threads — package with
  `DCode.fn_specR`, never `fn_spec` (`callFree` is `false` by design).
- The spec is naturally **single-base** (state it at the routine's own
  guest entry; `hcalls` closes by `rfl`).  Parameterize the derivation
  over `hi`/`lo` and an `hla` resolution hypothesis, discharged per
  placement by `decide` — exemplar:
  `Codegen/Programs/BalSerializerLeSAsm.lean`.
- ⚠️ Two same-named helpers with OPPOSITE argument orders exist:
  `Rv64.LaResolve.laHi (pc target)` vs `Codegen.AsmReloc.laHi (sym pc)`
  (the `_prog`s use AsmReloc's).  The `decide`d `hla` catches a mixup.
- `blockOkAt` with symbolic `hi`/`lo` closes by `rfl`, not `decide`
  (the checks never scrutinize the immediates).

### Ret-terminated derivations: `retJalr` / `dretIf` / `DCode.retSpec`

Routines that exit through `ra` (possibly from several tails) are
derivations ending in `DCode.retJalr`, branching with `DCode.dretIf`
(both arms ret-terminated, no join jump; else-arm is laid out first).

**Shared-tail guard cascades** (`DCode.dretCascade` / `Stmt.retCascade`)
express the "validate; any failure returns the error code" idiom — a
list of stages, each a straight-line block followed by a branch into ONE
shared bad tail, falling through into the ok tail (`is₀; B c₀ → bad; …;
ok; bad`), which a tree of `retIf`s cannot express without duplicating
the tail.  Obligations are a `CascadeChain`: per stage, block support +
memory VCs at a user-chosen invariant `inv k`, a fall-through step
(`step(inv k) ∧ ¬cₖ ⊢ inv (k+1)`) and a fired step (`step(inv k) ∧ cₖ ⊢
B`); then `okD : inv n ⤳ Q` and `badD : B ⤳ Q`, both ret-terminated.
For a concrete stage list the chain is a plain `⟨…⟩` conjunction.
Exemplar: `Codegen/Programs/SgValidateFixedListSAsm.lean`
(`sg_validate_fixed_list`, three guards, byte-identical, on the
top-theorem input-decode path).
The capstone is **`DCode.retSpec`**, the `Stmt.retSound` path: it yields
the `ra`-framed, `FnHandle`-shaped triple ending at the aligned return
address.  `DCode.fn_spec` rejects ret nodes (`offsetsOk` is `false` on
them by design); `retOffsetsOk` is the layout autoparam here.  Structural
limits (from `retOffsetsOk`): ret nodes may appear only at the top of the
statement or under `seq`-suffixes / `retIf` arms — not under
`ite`/`when`/loops.  Demo: `eqFlag` in `DerivDemo.lean`.

## How it composes with the rest of SAsm

- `Stmt.sp` / `Stmt.vcs` are reused unchanged; the two new lemmas
  (`Stmt.sp_exists`, `Stmt.vcs_exists` in `VcExists.lean`) commute them with
  existentials over a nonempty index — that is what lets a per-iteration body
  derivation discharge the body VCs the generator emits at the ∃i-union reach.
- A `DCode`-generated `Fn` is byte-identical in treatment to a hand-written
  one: drift guards (`_eq_prog`), `Fn.toHandle`, `FnFlat`, codegen emission all
  apply as-is.
- Not yet covered: `while2BreakJoin`, `doWhileBreak`, `retWhileBreak`
  (a tail-swapped variant would serve `modexp_iszero`), MID-ROUTINE
  shared-tail joins that resume (as opposed to ret-terminated cascades,
  which `dretCascade` now covers), `callReg`/`callRegS`. Those shapes
  stay on the classic `Stmt`+`vcgen` path; a routine can also be *split*
  so its proof-first prefix feeds a classic tail.

## Why this catches bugs early

Every step names the machine state it starts from and produces. A clobbered
register makes the *next* step's precondition unprovable (or the calc endpoints
fail to line up) at the step that clobbers — while writing the derivation. An
endianness mistake shows up in the very `hpost` of the block that loads or
stores, because the block-engine result must be proven to satisfy the named
mid-assertion before anything downstream is written. And loop-body code that
varies with the iteration index is a type error at the loop constructor.
