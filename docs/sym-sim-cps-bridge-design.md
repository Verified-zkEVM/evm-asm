# Bridging symbolic-simulation results to `cpsTripleWithin`

Slice 4 of GH #302 / parent `evm-asm-rg94` / this slice `evm-asm-hllh`.

This is a *design note*. Slices 1 (`evm-asm-nbx7`, ADD pilot) and 3
(`evm-asm-hy1i`, `sym-step-eq-design.md`) sketch a path where each RV64IM
step is discharged by a pre-generated `@[step_eq]` simp lemma, leaving the
goal in the shape

```
∃ s', stepN k s = some s' ∧ ⌜s' = w_n ⌫ (w_{n-1} ⌫ ... s)⌝ ∧ Q s'
```

That is the *symbolic-simulation* shape: a concrete state-update term
threaded through register and memory writes. Every other proof in evm-asm
speaks in `cpsTripleWithin nSteps entry exit_ cr P Q` (separation logic
over `MachineState`, see `EvmAsm/Rv64/CPSSpec.lean` line 45). Without a
bridge, sym-sim results cannot compose with the existing 50+ opcode
proofs, EVM body, RLP routines, or the LP64 calling-convention specs.

This note designs that bridge: the lemma family that turns a
sym-sim-shaped post-state into a `cpsTripleWithin` consumable by the
existing `cpsTripleWithin_seq` pipeline. It deliberately stops short of
implementation — the goal is to prove that the conversion exists,
characterise its shape and its preconditions, and pick a worked example
(ADD) so slice 1 (the pilot) has a concrete target to compose against.

The conclusion: **a single `cpsTripleWithin_of_stepN` lemma plus a
mechanical "lift register/memory writes into separation-logic
assertions" simp set is enough to make sym-sim results plug straight
into `cpsTripleWithin_seq`.** The harder problem is *not* the bridge
itself — it is keeping the sym-sim post-state in a shape where the
`Q s'` side of the bridge is provable without re-flattening to atoms.

---

## 1. The two shapes

### 1.1 The `cpsTripleWithin` shape

From `Rv64/CPSSpec.lean`:

```lean
def cpsTripleWithin (nSteps : Nat) (entry exit_ : Word) (cr : CodeReq)
    (P Q : Assertion) : Prop :=
  ∀ R s, (P ** R).holdsFor s → s.pc = entry → cr.Holds s →
    ∃ k, k ≤ nSteps ∧ ∃ s', stepN k s = some s' ∧ s'.pc = exit_ ∧
      (Q ** R).holdsFor s'
```

The hypothesis `(P ** R).holdsFor s` is opaque separation-logic:
`Assertion` is `MachineState → Prop`, `**` is `sepConj`, and `R` is the
universally-quantified frame. The user never sees the underlying
record-update structure of `s`.

### 1.2 The sym-sim shape

After `simp only [step_eq]` runs `n` times (slice 3's plan), the goal is
something like:

```lean
⊢ ∃ s', stepN n s = some s' ∧ s' = updates_n (... (updates_1 s) ...) ∧ Q s'
```

where each `updates_k` is a ground term in `MachineState.setReg /
setMem / setPC` — a *record-update tower*. The conclusion `Q s'` is
whatever the user wants to prove (often `(Q ** R).holdsFor s'` for some
`Q`, `R` they picked).

### 1.3 Why we need a bridge

`cpsTripleWithin` is the contract that downstream proofs (every opcode
spec, every full-path divmod theorem, `cpsTripleWithin_seq`, etc.) talk
in. Sym-sim produces an *equation about `s'`*. We need:

* a way to turn a `stepN n s = some s'` result with a known `s'` into
  `cpsTripleWithin n s.pc s'.pc cr P Q`, and
* a way to discharge the `(Q ** R).holdsFor s'` side from the
  record-update tower.

The first half is small (one lemma, sketched in §2). The second half is
the existing `getReg_setReg` / `getMem_setMem` simp infrastructure
applied to assertion-level consequences (`regIs`, `memCellIs`,
`evmStackIs`, ...) — sketched in §3.

---

## 2. The core bridge lemma

Working name: `cpsTripleWithin_of_stepN`. Signature:

```lean
theorem cpsTripleWithin_of_stepN
    {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion}
    (h : ∀ R s, (P ** R).holdsFor s → s.pc = entry → cr.Holds s →
      ∃ k, k ≤ nSteps ∧ ∃ s', stepN k s = some s' ∧
        s'.pc = exit_ ∧ (Q ** R).holdsFor s') :
    cpsTripleWithin nSteps entry exit_ cr P Q := h
```

Yes — it really is `id` after unfolding the definition. The bridge is
not the *theorem*; the bridge is the *proof obligation shape* the user
ends up with after sym-sim runs. The interesting design choice is what
intermediate lemma we expose so that *the user's sym-sim trace fits
this hole without manual surgery*.

A strictly more useful packaging:

```lean
/-- Given a fully evaluated `stepN` trace and a closure that lifts the
    resulting state-update tower into the postcondition, build a
    `cpsTripleWithin`. -/
theorem cpsTripleWithin_of_stepN_const
    {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion}
    (hsteps : ∀ s, s.pc = entry → cr.Holds s →
      ∃ s', stepN nSteps s = some s' ∧ s'.pc = exit_ ∧
        s' = stateUpdate s)
    (hQ : ∀ R s, (P ** R).holdsFor s →
      (Q ** R).holdsFor (stateUpdate s)) :
    cpsTripleWithin nSteps entry exit_ cr P Q := by
  intro R s hPRs hpc hcr
  obtain ⟨s', hstep, hpc', hs'⟩ := hsteps s hpc hcr
  refine ⟨nSteps, le_refl _, s', hstep, hpc', ?_⟩
  rw [hs']
  exact hQ R s hPRs
```

`stateUpdate : MachineState → MachineState` is the closed-form term
sym-sim produces — a chain of `setReg` / `setMem` / `setPC` applied to
`s`. The two obligations that remain are:

* `hsteps`: a fully-evaluated step-count trace. After
  `simp only [stepN_succ, step_eq_pc_<entry+0>, step_eq_pc_<entry+4>, ...]`
  this is `rfl` (slice 3 designs the `step_eq` lemmas to make this hold).
* `hQ`: the *frame-stable* claim that the assertion `Q ** R` is
  preserved by `stateUpdate` whenever the assertion `P ** R` held. This
  is exactly the kind of obligation `xperm_hyp` and the existing
  `regIs_setReg_eq` / `memCellIs_setMem_disjoint` lemmas already solve.

Two design choices to call out:

1. **Exact step count vs. bounded.** The body of `cpsTripleWithin`
   exposes `∃ k, k ≤ nSteps ∧ ...`. Sym-sim always produces an exact
   `k = nSteps`. Picking `k = nSteps` and `le_refl` is fine; it is
   strictly stronger than what the predicate asks for and matches what
   every existing concrete spec already does.
2. **Where does `cr.Holds s` go?** Slice 3 plans `step_eq` lemmas of
   the form `s.code pc_k = some instr_k → step (s with .pc := pc_k) = ...`.
   `cr.Holds s` already entails `s.code pc_k = some instr_k` for every
   PC in the program region (that *is* what `cr.Holds` means); the
   bridge just uses `cr` to discharge the per-PC code-equation
   premises one by one. No new infrastructure required.

## 3. The `Q` side: lifting record updates back into separation logic

This is where the bridge earns its keep. After sym-sim, `s'` looks like
(for a 4-instruction ADD body that the slice 1 pilot might verify):

```lean
s.setPC (s.pc + 16)
 |>.setReg .x5 v_after
 |>.setReg .x10 (a_old + b_old)
```

The `cpsTripleWithin` postcondition `Q ** R` is a separation-logic
formula speaking in `regIs r v` / `memCellIs a v` atoms. We need:

```
(P ** R).holdsFor s →
  (regIs .x10 (a_old + b_old) ** regIs .x5 v_after **
     pcIs (s.pc + 16) ** R').holdsFor s'
```

where `R'` is whatever was framed off in `R` minus the cells the
instruction touched. This is exactly the *frame computation* problem
that `cpsTripleWithin_seq` already solves via `R` quantification, and
the *atom-rewriting* problem that `regIs_setReg_eq`,
`regIs_setReg_disjoint`, `memCellIs_setMem_disjoint` etc. already
solve for hand-written specs.

The key observation: nothing new is needed at the assertion layer.
What we need is a **simp set** that systematically rewrites
`regIs r (s.setReg r v ...)` / `memCellIs a (s.setMem a v ...)` for the
*record-update tower* shape sym-sim produces. Working name:
`@[sym_state_lift]`. Membership:

* `regIs_setReg_eq` / `regIs_setReg_ne` (existing).
* `memCellIs_setMem_disjoint` / `memCellIs_setMem_eq` (existing).
* `pcIs_setPC` (trivial; add if not present).
* `holdsFor_sepConj` decomposition (existing under `xperm` machinery).

The simp call in the user proof becomes:

```lean
simp only [sym_state_lift, getReg_setReg_ne (by decide), ...]
xperm_hyp h
```

i.e. **lift the tower → call existing `xperm_hyp`**. No new tactic,
just curated simp lemmas.

A slightly fancier alternative would be a meta-program that builds the
`stateUpdate → assertion` translation automatically given a list of
`(reg/mem cell, new value)` pairs the sym-sim produced. That is out of
scope here — the simp-set version is enough to demonstrate composition,
and the meta-program is a clean follow-up if the simp set turns out to
be slow on long traces.

## 4. Worked example: ADD on a 4-instruction body

Take the slice-1 pilot ADD body (reg-reg ADD wrapping in a tiny
prologue/epilogue, 4 instructions total). Pseudocode of the existing
spec:

```lean
theorem add_spec_within :
    cpsTripleWithin 4 base (base + 16) (codeReq base addProgram)
      (regIs .x10 a ** regIs .x11 b ** ... ** pcIs base)
      (regIs .x10 (a + b) ** regIs .x11 b ** ... ** pcIs (base + 16))
```

Sym-sim path (slice 3 + slice 1 + this bridge):

1. Generate `step_eq_addProgram_base`,
   `step_eq_addProgram_base_plus_4`, etc. via the slice-3 meta-program.
2. State the goal in `cpsTripleWithin_of_stepN_const` form: peel `R`,
   `s`, `hPRs`, `hpc`, `hcr`. The `hsteps` obligation reduces to
   four `simp only [step_eq_addProgram_*]`-rewrites + `rfl`.
3. The `hQ` obligation is "regIs `.x10` `(a + b)` after the
   four-update tower applied to `s` where `regIs .x10 a ** ...` held".
   Discharge by `simp only [sym_state_lift, ...]; xperm_hyp h`.

Both halves are short and mechanical. The actual measurement
(heartbeats, build time vs. the existing `runBlock`-based proof) is
the slice-1 deliverable; this note's job is to convince ourselves the
shape composes.

## 5. Frame stability: why the bridge survives `cpsTripleWithin_seq`

`cpsTripleWithin_seq` (line 101) glues two triples by matching the
postcondition of the first with the precondition of the second. Once
sym-sim-derived triples are in `cpsTripleWithin` form, this
composition is the same as for any hand-written triple — nothing in
`_seq`'s proof inspects how the triple was *built*.

Concretely: a verified ADD via sym-sim plus a verified MUL via
`runBlock` compose by

```lean
cpsTripleWithin_seq add_spec_via_symsim mul_spec_via_runBlock
```

with no further glue. This is the property the bridge is buying.

## 6. What this slice does *not* design

* **The actual `sym_step` tactic** (slice 2, `evm-asm-avjm`). That's
  the consumer of the `step_eq` simp set; this note assumes it exists.
* **ECALL** — sym-sim's natural shape doesn't generalise to syscalls
  (the post-state depends on register content, not on PC). For ECALL
  blocks, fall back to `runBlock` / hand-written CPS triples. The
  bridge is for the long stretches of register-and-memory-only
  instructions between syscall boundaries.
* **Memory-trap branches** (`isValidXxxAccess`-guarded `none` returns).
  Sym-sim assumes traps don't fire; the obligation is a `cr.Holds`
  consequence the user discharges by `decide` + frame inspection.

## 7. Recommendation for slice 1 (`evm-asm-nbx7`)

Implement, in this order:

1. The single bridge theorem `cpsTripleWithin_of_stepN_const` in a
   small new file `EvmAsm/Rv64/SymExperiment/Bridge.lean`. ~20 lines.
2. The `@[sym_state_lift]` attribute + initial entries (just register
   `regIs_setReg_eq/ne`, `memCellIs_setMem_eq/disjoint`, `pcIs_setPC`).
   ~30 lines.
3. One ADD opcode body, proved twice — once via the existing
   `runBlock` path, once via sym-sim + bridge — in
   `EvmAsm/Evm64/Add/SymExperiment.lean`. Side-by-side comparison of
   build time, heartbeats, and proof-line count goes in slice 1's PR.

If step 3 shows sym-sim wins (or wins for long blocks and loses for
short ones), file follow-up beads tasks under `evm-asm-rg94` for
broader rollout. If it loses, the note in the comparison file
documents the dead-end and `evm-asm-rg94` can be closed.

---

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
