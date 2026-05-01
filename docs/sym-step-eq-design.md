# Pre-generated step-equation theorems for RV64IM (`#genStepEqTheorems` analog)

Slice 3 of GH #302 / parent `evm-asm-rg94` / this slice `evm-asm-hy1i`.

This is a *design note* that asks the question:

> Should evm-asm pre-compute, per program and per PC, simp lemmas of the
> shape
>   `step (s with .pc := pc_k) = w .GPR rd val (w .PC pc_{k+1} ...)`
> tagged `@[step_eq]`, and use those to drive a future `sym_step` tactic
> (slice 2, `evm-asm-avjm`) — analogous to LNSym's `#genStepEqTheorems` —
> instead of recomputing the step relation on the fly?

Conclusion up front: **probably yes for code-region programs, but with a
narrower attribute set than LNSym needs, and with two RV64IM-specific
caveats (decode locality and ECALL).** The pay-off is decode + dispatch
work amortised at *elaboration* time, leaving `sym_step` to do nothing
except `simp only [step_eq]` for the current PC.

The file is structured as: (1) recap of LNSym's machinery; (2) the
RV64IM `step` function and what "an equation per PC" looks like here;
(3) feasibility checklist; (4) a recommended path for the prototype in
slice 2.

---

## 1. What `#genStepEqTheorems` does in LNSym

LNSym (https://github.com/leanprover/LNSym) verifies AArch64 machine code
in Lean 4. Its symbolic-simulation pipeline rests on two ideas:

* `stepi` is the one-step transition: `MachineState -> MachineState`.
* For a *fixed* program (a `Map Nat Instr`-like table), every reachable
  PC has a single statically-known instruction. So the value of
  `stepi (s with .pc := pc_k)` can be partially evaluated at elaboration
  time: decode runs, the relevant `execInstr` case fires, and the
  result reduces to a ground term `w .GPR rd val (w .PC pc_{k+1} s)`.
* `#genStepEqTheorems <programName>` walks the program, builds one
  `theorem stepi_<program>_<pc_k>` per PC, proves each by `decide` /
  `rfl`-shaped reduction, and tags them `@[state_simp_rules]` (that's
  the LNSym attribute name).

Symbolic simulation is then `simp only [state_simp_rules]` on the goal:
the cost per step becomes a single rewrite, not a full WHNF reduction
of `stepi`.

The key invariant is **per-PC determinism of decode**: once the program
is fixed, no run-time dispatch on the instruction word is needed to
prove the step equation.

## 2. RV64IM `step` in evm-asm

`EvmAsm/Rv64/Execution.lean` defines `step : MachineState -> Option MachineState`
as one giant `match s.code s.pc with | some (.LD rd rs1 ofs) => ...`
(see lines 331-405+). Important observations for this design:

1. `s.code : Word -> Option Instr` is the *code memory*. For programs
   loaded via `MachineState.installProgram` (or whatever the canonical
   loader is), `s.code pc_k = some instr_k` is decidable by
   `native_decide` once `pc_k` is concrete.

2. Each branch of the `step` match reduces to
   `some (execInstrBr s instr_k)` (or to `none`, the trap case). For
   "ordinary" register-only instructions the result is a ground term
   in `setReg` / `setPC`. For memory ops the body is wrapped in an
   `if isValidXxxAccess addr then ... else none` guard.

3. ECALL (line 390+) dispatches on `s.getReg .x5`. The branches read
   from registers and the syscall-specific memory regions — the result
   is *not* a fixed term in PC alone; it depends on register content.

4. EBREAK and unknown opcodes return `none`.

So the equation per PC has three flavours:

  (a) **Pure / register-only** (ADD, SUB, ADDI, SLLI, AND, OR, BEQ, ...):
      `step s = some (execInstrBr s instr_k)` reduces further to a
      `MachineState.setReg .. (.. .setPC ..)` ground term, modulo the
      *current* register values inside `s`. The equation is fully
      static once we keep `s` symbolic except for `s.pc`.

  (b) **Memory ops with validity guard** (LD, SD, LW, LB, LBU, SB, ...):
      `step s = if isValidXxxAccess (s.getReg rs1 + signExtend12 ofs)
                then some (execInstrBr s instr_k) else none`.
      The validity predicate depends on a *runtime* register value, so
      the static equation must keep the conditional. A `@[step_eq]`
      lemma can still encode it — just leave the `if` in the RHS — but
      the consumer (`sym_step`) needs a side-tactic to discharge the
      `isValidXxxAccess` precondition from the assertion context.

  (c) **ECALL** (HALT / WRITE / COMMIT / fall-through): branches on
      `s.getReg .x5`. Again, the static equation can keep the `if`
      cascade; `sym_step` will need either a precondition like
      "`s.getReg x5 = 0x10`" supplied by the caller, or it should
      decline to step ECALLs and hand off to the existing
      `cpsTriple`-based syscall specs (`syscall_specs` registry).

## 3. Feasibility checklist

### 3a. Decoding `s.code pc_k` to a concrete `Instr`

Programs in evm-asm are `List Instr`. `MachineState.installProgram`
(and friends) produces a `code` function so that `code (base + 4*k) =
some (program.get? k)`. For a *fixed* program literal this is
`native_decide`-friendly; for parametric programs it is not.

**Verdict**: works for programs that ship as concrete `def`s — which
is the bulk of leaf opcode bodies and the `OPCODE_TEMPLATE`-style
fixed sequences. It does *not* work for `evm_push (n : Nat)` style
parameterised programs; those have to keep using cpsTriple-style
specs.

Practical consequence: a meta `#genStepEqTheorems myProgram` should
*require* the program to be a closed term reducible to a literal
`List Instr`. Sanity-check this in the elaborator and emit a clear
diagnostic when it isn't.

### 3b. Byte-vs-32-bit alignment

RV64IM instructions are 32-bit aligned (4-byte stride). evm-asm's
`code` keys are byte addresses (`Word`). The PC list for the meta
program is therefore `[base, base+4, base+8, ...]`. No half-word
compressed-instruction (RVC) wrinkles to worry about — the project
explicitly does not use RVC.

**Verdict**: trivial. PC enumeration is `base + 4*k` for `k ∈ [0, n)`.

### 3c. ECALL handling

Pre-baking an ECALL step equation as `if t0 == 0 then none else ...`
is correct but useless: the consumer would still need to know which
syscall fires. The clean factoring is to keep the existing
`@[spec_gen_rv64]` syscall registry (`SyscallSpecs.lean`) as the
authority for ECALL, and have `sym_step` *refuse* to step on an ECALL
PC — emit a residual goal "use the syscall spec", or fall back to the
old `cpsTriple` path. This is also how LNSym handles its rare opaque
opcodes (SVC etc.).

**Verdict**: pre-generation should *skip* ECALL PCs. They retain
their existing cpsTriple-based proof.

### 3d. Memory-validity guards

For LD/SD/LW/LB/LBU/SB/.. the step-eq lemma keeps the
`isValidXxxAccess` `if`. Two ways the guard is discharged in practice:

- The caller already proved the address is valid for the cell read
  (e.g. via `↦ₘ` ownership in the assertion). A simp lemma like
  `↦ₘ-implies-isValidDwordAccess` discharges the `if` automatically.
- Or `sym_step` accepts a proof of validity as an explicit argument,
  using it to rewrite the `if` to `some (...)` before applying the
  step equation.

Either way the static lemma stays one per PC; only the side-tactic
needs to know about the guards. This matches how the existing
`spec_gen_rv64` registry already handles memory ops.

### 3e. Build cost

Per-PC equation proofs reduce by `native_decide` (decode the byte
address into the constant `Instr`, then evaluate `execInstrBr` on a
symbolic state). For a 100-instruction body this is 100
`native_decide`s during the meta call. That is *one-time* compilation
cost amortised across every proof that consumes the program.

The expected win shows up at *use* time: a proof that today does
~100 `cpsTriple_seq` compositions × O(n²) `xperm_hyp` per step would
become 100 `simp only [step_eq]` rewrites + one terminal frame
solve.

### 3f. Comparison to LNSym

- LNSym needs `#genStepEqTheorems` because AArch64 has ~1000 opcodes
  and decode is genuinely expensive. RV64IM is much smaller (~50
  opcodes including the M extension), so on-the-fly `sym_step` may
  already be fast enough; pre-generation is more about killing
  per-step elaboration noise (xperm churn) than dodging decode.
- LNSym's `state_simp_rules` attribute does double duty: PC-specific
  step equations *and* generic state-projection lemmas (`get/set`).
  evm-asm should keep these separate — one `@[step_eq]` for PC-specific
  lemmas, the existing `@[reg_ops]` / `@[byte_alg]` grindsets for state
  projection — to avoid recreating the simp-set bloat AGENTS.md warns
  about.
- LNSym proves the equations by a hand-rolled tactic
  (`sym_step_using_decide`); the evm-asm version should just be
  `by simp only [...]; native_decide` on each — RV64IM's `step` is
  small enough that no custom tactic is needed.

## 4. Recommended path for slice 2 (`evm-asm-avjm`, `sym_step` prototype)

In dependency order:

1. **Add `@[step_eq]` attribute** in `EvmAsm/Rv64/Tactics/StepEqAttr.lean`
   (pattern: `register_simp_attr step_eq`, mirroring `RegOpsAttr.lean`).
   Wire it into the `Rv64.lean` umbrella *before* any consumer.

2. **Implement `#genStepEqTheorems <programName>` macro/elab** in
   `EvmAsm/Rv64/Tactics/StepEqGen.lean`:
     - Reduce the named program to a `List Instr` literal (fail loudly
       if it doesn't reduce).
     - Enumerate `pc_k = base + 4*k`.
     - Skip `Instr.ECALL` and `Instr.EBREAK`.
     - For each remaining PC, emit
       ```
       @[step_eq] theorem step_eq_<programName>_<k>
           (s : MachineState) (h_pc : s.pc = base + 4*k)
           (h_code : s.code (base + 4*k) = some instr_k)
           : step s = ... := by
         subst h_pc; rw [step]; rw [h_code]; rfl
       ```
       (Exact shape TBD by the slice-2 author; the `h_code` hypothesis
       lets the lemma be reused under any program-installation
       wrapper that exposes `s.code` for that PC.)
     - Memory ops: keep the `if isValidXxxAccess ..` in the RHS; do
       *not* try to discharge it.

3. **Pilot on ADD** (slice 1, `evm-asm-nbx7`) — generate the table for
   the existing `add` opcode body, prove the existing top-level spec
   via `simp only [step_eq] *; <existing terminal tactic>` and
   compare:
     - elaboration time of the two proofs (`#time` or
       `set_option profiler true`);
     - heartbeats consumed;
     - whether the `step_eq` proof scales linearly in program length.

4. **Decide before broader rollout**: if the pilot doesn't beat the
   current cpsTriple approach by ≥3× on something fast like ADD, the
   payoff for the divmod/shift composition wall (the original target
   of #302/#265) is unlikely. Flag the result on the parent and
   either commit to a `sym_step` rollout or close the investigation.

## 5. Risks and unknowns

* **`native_decide` portability**: existing CI already uses
  `native_decide` widely so the runtime cost is mostly known. But
  generating ~100 `native_decide` proofs per program at elaboration
  may inflate the per-file build time noticeably. Slice-2 needs to
  measure this on a single representative file and weigh it against
  the proof-time saving downstream.

* **Code-region coupling**: the generated lemmas are bound to a
  specific program. Changes to the program (insert/delete an
  instruction) invalidate every lemma. This is fine for stable
  helpers (DivMod loop body, RLP phases) but bad for code under
  active development. Recommendation: add the macro call only to
  files that are mature and bottlenecked by `xperm` cost.

* **Interaction with frame-automation tactics**: `runBlock` /
  `seqFrame` / `liftSpec` already encode "step one instruction at the
  semantic level" with frame baking. `sym_step` needs to coexist with
  these, not replace them — symbolic simulation handles the *intra*
  basic-block stepping; `cpsTriple_seq` still composes whole basic
  blocks and discharges sep-logic frames at boundaries.

## 6. Recommendation

Worth prototyping. The mechanical part (macro that emits one lemma
per PC) is small; the per-PC `native_decide` proof obligation is
already the project's bread-and-butter. The slice-1 ADD pilot
(`evm-asm-nbx7`) should run *first* to validate the cost model
before slice-2 invests in the generator macro. If the pilot
demonstrates a ≥3× speedup on ADD, this design becomes the
preferred path for the divmod/shift composition wall.

The biggest design choice the prototype must lock in:

  Should `step_eq` lemmas embed the program-installation hypothesis
  directly (single-purpose lemmas, easy to use), or be parameterised
  over `s.code (base + 4*k)` and rely on a separate
  `[s.code .. = some instr]` simp set (composable, harder to use)?

The current recommendation (above) is the former for the prototype
and the latter as a refactor target once `sym_step` proves itself.

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
