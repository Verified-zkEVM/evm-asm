# The interpreter-loop verification strategy (bead evm-asm-4ch8f.10)

How the dispatcher core (`EvmAsm/Codegen/Dispatch.lean:2404` —
`.dispatch_loop`: fetch `lbu`, static-gas charge, `jalr` through
`opcode_handlers`, loop) will be proven to simulate the
execution-specs interpreter, and what the pilot
(`EvmAsm/Rv64/SAsm/InterpLoopDemo.lean`, fully proved) establishes.

Companion sections: docs/sasm-design.md §3.6.3 (`callReg`), §3.9 (phase
ownership), §3.10 (loop fuel / `whileS`); the pilot's own header comment.

## 0. The load-bearing risk, and the primitive it forced

A `FnHandle` carries one fixed `pre`/`post` pair of `Reach` predicates.
That contract shape **cannot verify the dispatch loop**, for a reason
worth stating precisely because it looked like a mere inconvenience
until it was chased to the bottom:

- A handler at a looped dispatch site is invoked at a *different* machine
  state every iteration.  Its guarantee must be *relational* — "the exit
  stack is the entry stack with the top two summed" — but `post : Reach`
  sees only the exit state.  Any fixed `post` can either existentially
  forget which entry it came from ("the state encodes *some* spec
  state") or pin constants; neither determines the successor state.
- The forgetting variant is not just weak, it is **fatally weak**: with
  posts of the form "∃ j, the machine encodes trace step j", the loop
  invariant cannot correlate the handler's j with the loop's iteration
  counter, so the per-iteration gas decrease is unprovable and the
  `exhausted` VC (the gas-derived fuel cap) can never close.  A
  trace-indexed ghost family therefore does not rescue monomorphic
  handles (rejected alternative A below).

The fix is the same move `Stmt.whileS` (bead .5) made for loop
invariants: **parameterize the contract by the entry snapshot.**

> **`FnHandleS`** (`SAsm/Handle.lean`): `post : RegFile → List (BitVec 8)
> → Assertion → Reach`, with `sound` quantified over every entry state
> satisfying `pre` — the classic auxiliary-variable (universally
> quantified) triple.  **`Stmt.callRegS`** (`SAsm/Ast.lean` etc.) is
> `callReg` over such handles; its strongest postcondition records the
> call's entry state existentially:
> `∃ rf₀ ws₀ A₀, reach rf₀ ws₀ A₀ ∧ ∃ h ∈ handles, rf₀.get rs = h.entry
> ∧ h.pre rf₀ ws₀ A₀ ∧ h.post rf₀ ws₀ A₀ rf ws A`.
> The `.pre` VC at the dispatch site is unchanged from `callReg` — one
> uniform obligation.  Soundness (`SAsm/StmtSoundCall.lean`) is a ~90-line
> adaptation of the `callReg` case: the per-state split
> (`cpsTripleWithin_exists_pre_M_frame`) already fixes the concrete entry
> state, which is handed to the handle's `sound` as the snapshot.
> `Fn.toHandleS` (`SAsm/Fn.lean`) packages a spec *family*
> (`Fn.SpecS`: for every entry state satisfying the call-site `pre`, the
> body carries `Reach.exact rf₀ ws₀ A₀` to `postS rf₀ ws₀ A₀`) — handler
> proofs stay ordinary `vcgen` proofs, now with the snapshot as the
> master ghost.

This mirrors exactly how the existing machine-level handler specs are
already stated: every theorem in `Codegen/Proofs/HandlerSpecs.lean` is
∀-quantified over the entry values (`sp`, operand limbs, `x10_init`,
`x1_init`).  `FnHandleS` is the packaging that *keeps* those quantifiers
at the call site instead of freezing them.

## 1. The loop invariant shape

**Decision.** The invariant relates the machine state to the *existing*
Lean-side abstract interpreter state (`EvmAsm/Evm64`'s `EvmState`, the one
`InterpreterLoop.loopFuel` / `SupportedLoopBridge` step): a relation

```
encodes : EvmState → RegFile → List (BitVec 8) → Assertion → Prop
```

pinning, per the register audit of Dispatch.lean:

- `x10` = code pointer (`x21 + pc`), `x21` = code base;
- `x12` = value-stack top (grow-down; the pilot uses the same
  convention), with the stack's byte image a contiguous suffix of the
  frame's stack window and the free space existentially quantified
  ("junk ++ stackFlat" in the pilot);
- gas at `env+568`, plus the other env cells (`x20`-relative) as ghost
  fields; `x13` memory base; the exec-log region as a *monotone-append*
  component (§4 below);
- the loop invariant proper is
  `inv rf₀ ws₀ A₀ i rf ws A := encodes (loopFuel handler i σ₀(rf₀,ws₀)) rf ws A ∧ frame-constants pinned to the snapshot`.

**Snapshot usage.** Per-execution constants that are *runtime data* (the
initial gas loaded from env, the code base, the frame base at the current
depth) reach the invariant only through the `whileS` entry snapshot; the
`Fn.pre` correlates them with the theorem-level ghosts at entry and exit.
The pilot exercises precisely this: its trace is
`toyRun prog (ToyState.init (rf₀.get .x29).toNat) i` — the *snapshot's*
gas register defines the spec execution, and `inv_init`/`post` recover
`gas₀` from the pre.  (Statically-known constants like `codeBase` may
stay Lean-level ghosts; the pilot keeps them concrete.)

**Adequacy** (the reviewer's "can the invariant be satisfied by a wrong
EvmState?"): the invariant names the deterministic trace *function* of
the input — `toyRun … i`, not "∃ σ" — so there is nothing to get wrong;
and the post pins the final machine state to `toyRun … cap`, the frozen
halt state.  Pilot theorem: `InterpLoopDemo.interpFn_spec`
(`#print axioms`: `propext, Classical.choice, Quot.sound`).

**Rejected:** a machine-only invariant ("registers well-shaped") with the
spec relation recovered post-hoc — it cannot state the per-opcode
correspondence the handler beads need; and a fresh spec-side interpreter
— `Evm64.EvmState` + the `HandlerLoopSimulationBridge` battery already
connect table dispatch to the abstract loop, so the machine proof should
target that and let the pure-Lean bridge (`SupportedLoopBridge`, bead
.8's SpecRef seam) carry it to `process_message`.

## 2. Fuel

**Decision: gas-derived static cap, gas charge as the variant.**
`fuel := cap` with the ghost precondition `gas₀ < cap` (block gas limit
⇒ `cap = 200M + 1` fits; any larger cap also works — the static-cap
idiom of §3.10, wrong caps are unprovable, never unsound).  The loop
body's static-gas charge (`sub x7,x7,x6; sd` at Dispatch.lean:2427) is
the decrease; the spec-side lemma is "while running, `gas + i = gas₀`"
(pilot: `toyRun_gas`), proven once by induction on the trace and
consumed by the `exhausted` VC:
at `i = cap`, still-running would give `gas + cap = gas₀ < cap` —
absurd.  Notably the invariant itself does *not* carry the variant; the
correlation lives in the spec trace, which the snapshot-parameterized
handler posts keep in lockstep with the machine (this is where rejected
alternative A dies — see §0).

Real-loop wrinkle: EVM ops with static cost 0 exist, but every loop
iteration either charges ≥ 1 gas, exits, or descends/returns a frame;
the frame-aware variant is the lexicographic pair
(gas, current-frame progress) — see §4.  The interpreter-loop cap stays
gas-derived; `charge_gas`-order (charge-then-execute) matches the
emitted code.

**Rejected:** instruction-count cap (no natural ghost precondition — the
input doesn't bound instructions except through gas, so the cap-VC would
need the gas argument anyway, just less directly).

## 3. Dispatch

**Decision: one `FnHandleS` family indexed by opcode, `callRegS` at the
dispatch site.**  `handlers : Fin 256 → FnHandleS` (built from the
lifted `HandlerSpecs` theorems via `Fn.toHandleS`-style packaging), the
table `[handlers 0, …, handlers 255]` at the `callRegS` node.  Handler
contracts are stated uniformly:

- `pre` = the dispatch-site obligation: registers shaped as loop
  invariants guarantee (stack pointer in-window with the op's arity
  room, pc in-code for immediates) — supplied by the loop invariant +
  the per-opcode safety facts;
- `post rf₀ ws₀ A₀` = the exit state as a *function of the entry state*,
  i.e. exactly one spec step at the fetched opcode.

The pilot's `.pre` VC and `inv_step` show the composition at 3 handlers,
including the branch/handle cross-product (selected-address vs
handle-entry mismatches die on address literals).  For 256 entries the
real loop loads the address from the `opcode_handlers` ro table rather
than an `ite` cascade — table load is ordinary ro-region block machinery
(§3.6.3), and the `.pre` VC's "∃ h ∈ handles" witness is `handlers op`
with the table-lookup fact `rf.get rs = (handlers op).entry` coming from
the ro-region load spec.  This is the `.49` skeleton's work, not new
machinery.

**`jalr x0` tail calls: not needed — `.4` closes.**  The emitted
dispatch is `jalr x1, x7, 0` with handlers returning via `ret` to
`j .dispatch_loop` (Dispatch.lean:2429-2432, `HandlerTail.advanceAndRet`)
— exactly the `callReg`/`callRegS` shape.  The handlers with non-`ret`
tails (STOP `j .exit_label`; halts `j .exit_no_epilogue`; CALL-family
and depth-aware halts `j .dispatch_loop` after frame descend/return) are
*not* tail calls either — they are multi-exit control flow.  Decision:
restructure those tails in codegen to the uniform flag+`ret` discipline
(handlers set `halt_kind`/depth state and return; the loop header
branches on it — the loop already has header-exit guards, e.g. the
code-size stop guard), which keeps SAsm single-exit and costs ~1 branch
per iteration.  This is a `.49`-scoped emitted-code change, in exchange
for never adding a multi-exit call primitive to the trusted soundness
proof.  The `.4` remainder ships here as `callRegS` instead;
`jalr x0` support is recorded as not required by any current consumer.

**Rejected alternatives.**
- *(A) Monomorphic handles + trace-indexed ghost posts* ("∃ j, exit
  encodes trace (j+1)"): cannot correlate `j` with the iteration, so
  `inv_step` cannot re-establish `encodes (trace (i+1))` and no variant
  exists — the `exhausted` VC is unprovable.  Not merely inconvenient:
  unsound caps would be the only "fix", and the framework rightly
  refuses.
- *(B) 256 bespoke contracts at the site*: the `.pre` VC becomes a
  256-way disjunction with no uniform witness; handler beads could not
  be delegated independently of the loop proof.
- *(C) Multi-exit `callReg` (callee post at a different exit address)*:
  models the current non-`ret` tails faithfully but adds a second
  continuation to every soundness statement (`cpsTripleWithin` is
  single-exit); the flag+`ret` restructure achieves the same behavior
  inside the existing theory.

**Shipped (`.10.1`, `Codegen/Proofs/HandlerHandles*.lean`).**  The clean-ret
arithmetic/logic family is packaged as snapshot-parameterized `FnHandleS`
handles, each `(base sp : Word) → FnHandleS` (fully base-parameterized — no
`GuestAddrs` pins; `.9.5` layout regen is free to move constants).  Each handle
is verified against a *minimal* value-stack window `rw := ⟨sp, 64⟩` (or
`⟨sp, 32⟩` for unary, `RwRegion.empty` for POP): the operand words at fixed
window offsets, no junk framing.  `.49`/`.56a` embed it into the full arena via
the existing `FnHandle.widenRw`.  The `pre` is the §3 uniform shape
(`x12 = sp`); the `postS rf₀ ws₀ A₀` pins the exit registers/window as functions
of the entry snapshot (no ∃-state escapes).  The adapter reuses the existing
`HandlerSpecs` `cpsTripleWithin` verbatim (arithmetic not re-derived), bridging
raw `↦ₘ` operand cells to the window `bytesRegion` (`bytesRegion_eq_8cells` /
`_4cells`) and peeling the touched registers off `regFileIs`
(`regFileIs_split_bin`); it mirrors the documented template
`Rv64/SAsm/ExamplesVc.handAdd_sound`.  Every `<op>PostS` is `[irreducible]` to
keep the let-bundle folded during `isDefEq` (no `maxHeartbeats` raise);
`#print axioms` on each `<op>Handle`/`<op>Handle_sound` is
`[propext, Classical.choice, Quot.sound]`.

Packaged handles (13): `evmAddHandle`, `evmSubHandle`, `evmLtHandle`,
`evmGtHandle`, `evmSltHandle`, `evmSgtHandle`, `evmEqHandle`, `evmAndHandle`,
`evmOrHandle`, `evmXorHandle`, `evmIsZeroHandle`, `evmNotHandle`, `evmPopHandle`
(entry point for `.49`: these `*Handle` defs).

Skipped here (out of `.10.1` scope), by owning bead:
- **PUSH0, PUSH1, DUP*, SWAP\*** (stack group, PUSH-family `n=2` /
  passthrough-ret tail) → `.50`.
- **MUL, SIGNEXTEND, BYTE** (reload-ret: `x10`-clobbering save/reload tail),
  plus SHR/SHL/SAR/DIV/MOD/SDIV/SMOD/ADDMOD/MULMOD/EXP/CLZ → `.51`.
- **MSTORE, MSTORE8, MLOAD, MSIZE, MCOPY, env loads, CALLDATA\*** (memory/env
  traffic, memory-expansion gas) → `.52`.
- **halts / STOP / RETURN / REVERT / control flow** (non-`ret` tails needing
  the flag+`ret` restructure) → `.10.3` then `.55`.
- **CALL-family / frame machinery** (window-moving posts) → `.56`.

## 4. Frames

**Decision: window movement over the Phase-D arena, one flat loop, depth
as data.**  The dispatcher is one loop; CALL does not recurse (frame
descend rebases `x12`/`x13`/`x20` into `call_frame_arena` slot `d+1` and
jumps to the loop head).  Consequences:

- The interpreter `Fn`'s rw resource is `phaseDView base`
  (`anyBytes base frameArrayBytes`); the proof enters through
  `cpsTripleWithin_anyBytes_pre` (verified for all arena contents — no
  Phase-H assumptions, per §3.9).  Per-depth windows are carved with
  `anyBytes_add`/tiling at `frameArrayBase + d * frameStride`
  (`CallFrameLayout.lean`), the grow-down stack top exactly as the
  pilot's `x12` window.
- The loop invariant generalizes from "machine encodes `EvmState`" to
  "machine encodes the *frame stack*": a depth-indexed
  `encodesFrame : Nat → FrameState → …` for suspended parents (their
  saved pc/codebase/x12 in `frame_call_ctx[d]`/`frame_parent_bases[d]`,
  their stack windows untouched) plus `encodes` for the active frame,
  related to the spec side's `Message`-recursion unrolled to an explicit
  stack (the standard spec-side refactor: `process_message`'s recursion
  ⇒ an iterative frame-stack semantics, proven equivalent in pure Lean).
- CALL/RETURN handlers get `FnHandleS` contracts like every other
  handler — their posts move the window (pointer rebasing is register
  arithmetic; `frame_save/load_regs` are dword stores/loads in the
  frame's meta slots).  The descend/return proofs frame the *other*
  depths' windows untouched — snapshot-parameterized posts state
  "bytes outside [d·stride, (d+1)·stride) equal entry bytes" without
  `widenRw` gymnastics (the pilot's `stopPost`/`pushPost` demonstrate
  byte-range pinning through the snapshot).
- **Exec-log**: the storage exec log (0xa0630000, 128-B entries,
  lengths at env+448/464) enters the invariant as monotone-append
  state: `logBytes σ.execLog <+: logRegion ∧ length cell = |σ.execLog|`.
  Handler posts append (SLOAD/SSTORE) or truncate-to-checkpoint
  (REVERT, which is still monotone w.r.t. the checkpoint discipline the
  spec side mirrors); the composition with `.61` reads the final log
  off the invariant at loop exit.  The pilot omits the log (single rw
  region; adding a second window is the `widenRw` composition already
  proven in HandleWiden) — the invariant *shape* is what §1 fixes.
- Variant across frames: gas is global (charged from the same env cell
  at every depth, 63/64 forwarding only splits it), so the gas variant
  of §2 covers descend/return unchanged; depth ≤ 1024 is a spec-side
  invariant (`StackDepthLimitError`), machine-checked by the depth
  guard.

**Rejected:** verifying the loop per-frame and composing by recursion —
the machine has one loop and no call stack; a recursive proof structure
would have to invent a stack the code doesn't have, and the 1025-slot
arena is exactly the explicit stack already.

## 5. Decomposition (feeds `.49`–`.56`)

Concrete child scopes, in dependency order.  "Opus" = delegable with a
template; "Fable" = novel proof design.

1. **`.49a` — handler-handle packaging** (Opus, per-opcode fan-out):
   wrap each `HandlerSpecs` theorem as an `FnHandleS` via
   `Fn.toHandleS`/direct packaging; uniform pre/post statement per §3.
   Template: the pilot's `pushFnBase/pushPost/pushFn_specS` triple.
   Blocked by nothing; can start now per handler.
2. **`.49b` — opcode-table load spec** (Opus): ro-region load of
   `opcode_handlers[op]`/`opcode_gas_costs[op]` with the witness
   `rf.get rs = (handlers op).entry`; ELF-drift-guarded table contents
   (RegionMap pattern).
3. **`.49c` — flag+`ret` tail restructure** (Fable decision, Opus
   execution): change the emitted non-`ret` handler tails to the flag
   discipline (§3); re-run EEST parity.
4. **`.49d` — loop skeleton theorem** (Fable): `whileS` + `callRegS`
   over `.49a/b`'s handles, gas variant, guards as `when` blocks
   replacing the pilot's `hsafe` (under/overflow → exits 7/8, pc guard
   → implicit STOP), jumpdest bitmap build as a prefix `while` with an
   ro-code invariant.  Pilot is the direct template.
5. **`.56a` — frame-window algebra** (Opus): `anyBytes` carving of
   per-depth windows + the depth-indexed `encodesFrame`; pure
   separation-logic lemmas.
6. **`.56b` — descend/return handles** (Fable): CALL/CREATE/RETURN
   family `FnHandleS` contracts moving the window (§4), incl. the
   spec-side iterative frame-stack semantics and its equivalence to the
   recursive `process_message`.
7. **`.50`–`.55`** (Opus): per-group handler `SpecS` families against
   the `.49a` statement shape — unchanged in scope, now with a concrete
   contract template.
8. **`.59`/`.61` interface**: the loop theorem's exit invariant
   (exec-log + gas settle inputs) is the composition surface; settle
   routines (`dispatcher_tx_gas_settle`) are ordinary post-loop blocks.

## 6. What the pilot proves (for the adversarial reviewer)

`EvmAsm/Rv64/SAsm/InterpLoopDemo.lean`, zero sorries, axioms =
`propext, Classical.choice, Quot.sound`:

- **`interpFn_spec`** — the fetch-charge-select-dispatch loop over
  PUSH-imm8/ADD/STOP (invalid ⇒ STOP), with the value stack a grow-down
  window in the rw region, simulates `toyRun prog (ToyState.init gas₀)`:
  the post pins the exit machine state to `toyRun … cap`, the
  deterministic spec execution frozen at its halt point.  A "wrong
  EvmState" cannot satisfy the invariant: it names the trace function,
  not an existential.
- **Gas actually bounds iterations**: `toyRun_gas` + the `exhausted` VC
  — delete the loop body's `ADDI x29, x29, -1` or weaken `hgas` and the
  proof fails at `exhausted`, not at soundness.
- **Snapshot-carried per-execution constants**: the spec trace is
  defined from the loop-entry snapshot's gas register; nothing else
  carries `gas₀` into the invariant.
- **Handler contract uniformity**: one `.pre` VC; three real
  `Fn.SpecS` handler proofs (`pushFn_specS`, `addFn_specS`,
  `stopFn_specS`) with snapshot-parameterized functional posts; the
  select/handle cross-product (9 cases) closes by address arithmetic.
- **New primitive soundness**: `Stmt.callRegS` + `FnHandleS` +
  `Fn.toHandleS` (`Handle/Ast/Flatten/Vc/StmtSound/StmtSoundCall/Fn`),
  kernel-checked through `Fn.SpecR` like every SAsm construct.

Deliberate pilot simplifications, each mapped to a bead: runtime guards
replaced by the `hsafe` trace-safety hypothesis (`.49d` makes them
`when`-guard exits); handler-address select is an `ite` cascade instead
of the ro-table load (`.49b`); no exec-log window (§4; the invariant
slot is specified); single frame (`.56a/b`).
