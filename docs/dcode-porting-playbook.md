# The DCode porting playbook

How to replace an unverified guest routine with a **proof-first (DCode)**
implementation whose generated code is **byte-identical** to the deployed
bytes.  This is the operational companion to `docs/sasm-deriv.md` (which
explains the paradigm); this file is the recipe an agent follows to land
one more port.  Every step below has shipped at least once — the
references point at merged consumers to copy from.

Reference consumers, roughly in order of difficulty:

| consumer | file (Codegen/Programs/) | shape exercised |
|---|---|---|
| `sg_validate_fixed_list` | `SgValidateFixedListSAsm.lean` | `dretCascade` (guards → shared bad tail) |
| `modexp_iszero` | `ModexpIszeroSAsm.lean` | `dretWhileBreakSwap` (break loop, tails swapped), read-only loads |
| `edd_be32_eq` | `EddBe32EqSAsm.lean` | `dretWhileHeaderBreak` (header-reload loop → cascade), load-heavy stage block |
| `sender_post_nonce_consistent` | `SenderPostNonceConsistentSAsm.lean` | cascade + `dwhile` accumulate loop |
| `edd_memcpy` | `EddMemcpySAsm.lean` | `dwhile` with STORES into the rw window |
| `call_frame_forward_gas` etc. | `CallFrameForwardGasSAsm.lean` | straight-line + `dretIf` |
| `bal_serializer_*_to_le` | `BalSerializerLeSAsm.lean` | `blockA` (`la`/AUIPC), placement-pinned |

## Step 0 — pick a target

`PLAN.md` keeps the ledger.  A good target is a **leaf** routine (no
`jal` to other functions inside it) whose control flow matches an
existing shape (step 2).  Routines needing a NEW `Stmt` shape are
multi-day efforts (see "Adding a shape" below) — do not start one
casually.  Known-blocked: `slot_decode_u256` (multi-tail forward join;
issue #12755).

## Step 1 — recover the machine shape

The deployed code lives either as a `Program` value (a `def *_prog :
Program := [...]` list, e.g. `State.lean`) or as a GNU-as string inside
a `String` def (e.g. `ExtractDepositData.lean`, `ModexpBackend.lean`).
Write out the instruction indices, every branch's absolute target, and
classify each branch: guard into a tail? loop back-edge? loop exit?
break?  Draw the tail region: which tails are shared, which fall
through into which.

## Step 2 — choose the Stmt/DCode shape

Single-exit bodies (consumed via `DCode.fn_spec`): `block`, `blockA`
(needs `la`/AUIPC and a pinned placement), `seq`, `ite`, `when`,
`dwhile`/`doWhile` (+`S` snapshot variants), `dwhileHeader`,
`dwhileBreak`, `readAt`, `callAt`.

Return-terminating bodies (consumed via `DCode.retSpec`; the routine
exits through `ra` at possibly several `ret`s):

| machine idiom | node |
|---|---|
| `ret` | `retJalr` |
| `B c → tail1; tail2` (two ret tails, no rejoin) | `dretIf` |
| `is₀; Bc₀ → bad; is₁; Bc₁ → bad; …; ok; bad` (shared bad) | `dretCascade` |
| top-guarded break loop, exit tail FIRST then break tail | `dretWhileBreak` |
| same but break tail first ("scan until nonzero") | `dretWhileBreakSwap` |
| header-reloaded break loop draining into a cascade, break enters the cascade's shared bad tail | `dretWhileHeaderBreak` |

Check the synthesized offsets against the deployed bytes BEFORE writing
any proof: compute `Stmt.size`s by hand and verify every branch
distance.  If no node matches, stop and read "Adding a shape".

## Step 3 — design ghosts, regions and families

- **Ghosts**: the routine's abstract inputs (pointers, lengths, buffer
  contents `bs : List (BitVec 8)`, initial window `ws0`).  They
  parameterize the derivation; the generated code MUST NOT depend on
  them (enforced by the `hcode … := by intro i; rfl` autoparams and
  re-checked by a `#guard` sampling several instantiations).
- **Regions**: `reg : Region` = the read-only bytes the routine loads
  from (`Region.mk ptr bs`); `rw : RwRegion` = the window it writes
  (`RwRegion.mk dst n`, or `RwRegion.empty` for register-only /
  read-only routines).  Both `wf` obligations become hypotheses of the
  final spec — note `wf` demands an 8-aligned base.
- **Statics**: bundle the never-changing facts (register values of
  untouched argument registers, length bounds, no-wrap bounds,
  src/dst disjointness) into one `def xxStatic … : Prop` carried through
  every invariant — see `mcStatic` in `EddMemcpySAsm.lean`.
- **Families**: loop invariants `inv : Nat → Reach` at the guard
  evaluation; `mid` at a break test; cascade invariants per stage.
  Reach = `RegFile → List (BitVec 8) → Assertion → Prop`; always end
  with `∧ A = empAssertion` for ambient-free leaves.  If the window is
  written, the invariant must pin `ws` exactly (e.g.
  `ws = bs.take i ++ ws0.drop i`).

## Step 4 — write the derivation

Structure: `DCode.seq` of an init block, the main node, and tails; or a
`calc` chain (eta-expand named `Reach`s at calc endpoints:
`(fun rf ws A => myInv j rf ws A : Reach)` — the `Trans` instance will
not fire otherwise).

Proof idioms, in the order you will hit them:

1. **Block obligations** are `(by decide)` for `blockOk`,
   `(fun h => absurd h (by decide))` for the mem-VC of load/store-free
   blocks, and a post-step proof otherwise.
2. **Evaluate `execBlock` with pair-form step lemmas**, never by
   `simp [execInstrRF]` on load-bearing blocks.  Declare local
   `:= rfl` lemmas per ALU opcode
   (`execInstrRF_addi' : execInstrRF ro b rf ws (.ADDI rd rs1 imm) =
   (rf.set rd (rf.get rs1 + signExtend12 imm), ws)`) and an `if_neg`
   lemma per load kind (`execInstrRF_lbu_ro`, hypothesis
   `¬ inRw …`; when the window is empty, specialize to `ws = []` so the
   lemma is unconditional — `execInstrRF_lbu_nil` in
   `EddBe32EqSAsm.lean`).  Then
   `simp only [execBlock_cons, execBlock_nil, <pair lemmas>]` evaluates
   the whole block.  Stores never branch:
   `execInstrRF_sb'` is plain `rfl` (`EddMemcpySAsm.lean`).
3. **Load VCs** are `ite`s over `inRw`.  On Lean ≥ 4.33 do NOT
   `rw [if_neg …]` after any `dsimp`/`simp` has touched the goal — the
   ite's `Decidable` instance argument is left unreduced and the goal
   becomes implicit-transparency-ill-typed (`rw` then fails with a
   spurious "motive is not type correct" / pattern-not-found).  Two safe
   patterns: (a) `exact`/`refine` a helper lemma stating the clean ite
   (`edd_vc_nil`, `mc_vc`) — full-unifier defeq tolerates the instance
   mismatch; (b) re-state the whole ite with `show` before rewriting
   (`SenderPostNonceConsistentSAsm.lean`).
4. **Register bookkeeping** is `rw [RegFile.get_set_self _ _ _ (by
   decide), RegFile.get_set_ne _ _ _ _ (by decide : Reg.a ≠ .b), …]`
   chains — `simp only` will NOT discharge the `≠` side conditions
   (no `reduceCtorEq`).  In `simp only` lists, pass the lemmas
   pre-instantiated: `RegFile.get_set_ne _ _ _ _ (by decide : …)`.
5. **Immediates**: rewrite `signExtend12 (k : BitVec 12) = (k : Word)`
   and `BitVec.toNat (k : BitVec 6) = k` by `show … from by decide`.
   Convert shifted counters with a small `bv_omega` lemma
   (`miz_shift : BitVec.ofNat 64 i <<< 3 = BitVec.ofNat 64 (8*i)`).
6. **`cascadeStep`/loop-step hypotheses** destructure as
   `⟨rf₀, ws₀, hlen, ⟨…inv…⟩, hrf, hws⟩`.  Beware `rintro rfl` on the
   `hws` component: it whnf-collapses and substitutes the wrong binder —
   `obtain` + explicit `subst hrf` and keep `hws` unused if the goal is
   ws-independent.
7. **Window surgery** (stores): `setBytes_singleton`, `setBytes_*` in
   `MultiDword.lean`, and a bespoke `List.ext_getElem` splice lemma
   (`mc_copy_step`).  The `lbu→sb` round-trip is
   `truncate_zeroExtend_byte`.
8. **Fuel**: prefer the exact ghost bound (`fuel := n`,
   `EddMemcpySAsm.lean`) or the deployed cap (256 =
   `modexpBnMaxLimbs`).  `hexh` closes from the invariant's counter
   equation via `bv_omega`/`omega`.
9. **Guard/holds juggling**: `Cond.holds` unfolds by
   `simp only [Cond.holds, RegFile.get_x0, ne_eq]`; convert
   `¬(BitVec.ult a b = true)` with
   `simp only [BitVec.ult, decide_eq_true_eq]` before `omega`.
10. **`decide` refuses free variables** — for autoparam-style side
    conditions use `rfl`, recover Props with `of_decide_eq_true`.

## Step 5 — pin the generated code

```lean
instance : BEq Program := inferInstanceAs (BEq (List Instr))
def xx_prog : Program := (xxDeriv 0 [] 0).stmt.flatten 0
#guard (xx_prog : List Instr) == [ … expected instructions … ]
#guard xx_prog.length = N
#guard (((xxDeriv 8 [0,0] 3).stmt.flatten 0) : List Instr) == (xx_prog : List Instr)
```
Do NOT use `rfl`-equality for long programs (kernel deep recursion);
`#guard` with `==` evaluates in the compiler.  Branch immediates in the
expected list: forward `brOfs n` = `(4*n : BitVec 13)`, backward jumps
`(-4*n : BitVec 21)`.

## Step 6 — the byte gate and the string replacement

If the deployed code is a `Program` value: `#guard`-equate against it —
done.  If it is a GNU-as string with labels:

1. Save the old label-form slice to `old.s` (add the routine label).
2. Predict the emission (`emitProgram` renders `xNN` register names,
   `.+N`/`.-N` branch offsets, `lbu rd, ofs(rs1)` loads — see
   `Codegen/Emit.lean`) and check bytes:
   `scripts/check-byte-identity.sh old.s new.s` (or pipe the new body on
   stdin with `-`).  Must print `BYTE-IDENTICAL`.
3. Replace the slice with
   `"label:\n" ++ emitProgram XxSAsm.xx_prog ++ "\n" ++ …` (import
   `EvmAsm.Codegen.Emit` + the new file; mind that internal `.L` labels
   must not be referenced from OUTSIDE the slice).
4. Pin the exact rendering with a `#guard emitProgram … == "…"` so
   emitter drift re-triggers the external check (see the drift guards in
   `ModexpBackend.lean` / `ExtractDepositData.lean`).

## Step 7 — spec, wiring, checks, PR

- Capstone: `DCode.retSpec` (multi-exit) or `DCode.fn_spec`/`fn_specR`
  (single-exit); the `hleaf/hofs/hsz` autoparams close by `rfl` for
  concrete layouts.
- Add the module to `EvmAsm.lean`; move the routine in `PLAN.md`'s
  ledger; update `docs/sasm-deriv.md` only if a new shape landed.
- `lake build` (zero warnings — fix `unusedVariables`/`unusedSimpArgs`),
  `scripts/check-forbidden-tactics.sh`, `scripts/check-layering.sh`.
- One PR per port (or shape+port), stacked on the current DCode branch;
  PR body: shape, spec statement, byte-identity evidence, checks.

## Adding a shape (new Stmt node)

Only when no composition of existing nodes matches the bytes.  Budget a
full day+.  The recipe that worked four times
(`blockA`, `retCascade`, `retWhileBreakSwap`, `retWhileHeaderBreak`):

1. Verify the intended layout offsets against the target routine BY
   HAND before writing Lean.
2. Mirror an existing sibling node through the whole match surface —
   every file with a total match over `Stmt` needs a case:
   `Ast.lean` (ctor, `size`, `callFree`), `Flatten.lean` (`flatten`,
   `flatten_length`, `offsetsOk := false`, `retOffsetsOk`, `callsOk`),
   `Vc.lean` (`sp`, `vcs`, `steps`, `sp_mono`, `sp_of_endsWith`
   (`nomatch`), `vcs_antitone`, `CalleesIn`), `VcExists.lean` (2 cases),
   `StmtSound.lean` (`sound` reject + the real `retSound` case),
   `StmtSoundCall.lean` (reject), `Deriv.lean` (DStmt ctor,
   `post_sound`, `vcs_hold`, DCode smart ctor).  Missing-alternative
   errors from the compiler enumerate what is left.
3. Soundness cases are compositions of existing engines — reuse, do not
   reinvent: `Stmt.sound` on `.block`-wrapped raw lists +
   `cpsTripleWithin_frameL (ra ↦ᵣ ret)`; `branch_spec_asrt` +
   `signExtend13_brOfs` + frame/extend/weaken for guards;
   `WP.loopNatCert` / `WP.loopBreakNatCert` for loops (fold reloaded
   headers into the body leg, whileHeader-style);
   `retCascade_sound_aux` for cascade tails (its bad-triple FAMILY
   argument is what lets several edges share one tail).
4. Address arithmetic: `show A = B from by bv_omega` between
   `base + BitVec.ofNat 64 (4 * …)` forms; or `addr_shift` + a Nat
   `omega` show.  Keep `sel`-style case splits out of dependent types by
   packaging (target, triple) pairs in an `∃` before `cases`.
5. Then a DCode constructor bridging user families to the definitional
   `sp`/`vcs` (mirror `cascadeChain_bridge`), and at least one consumer
   or a `DerivDemo` exercising every exit.

## Operational notes for agents on this machine

- `lake env lean` is broken here (issue #10537) — iterate with
  `lake build <OneModule>`; never chmod `.lake/build`.
- The Bash tool caps foreground commands at 600 s and background tasks
  are killed after ~10 min: run long builds with `nohup lake build … >
  log 2>&1 &` and watch the log with a Monitor until-loop.
- A killed `lake` leaves its `lean` child running AND a blocked lock:
  before re-running, `pgrep -x lean` and inspect `/proc/<pid>/cmdline`
  (a `pgrep -f` pattern will match your own watchdog's command line).
- Other sessions build in `/tmp/evm-asm*` worktrees — check `uptime`
  before trusting wall-clock timings; distinguish a runaway from a slow
  build by the lean process's RSS trend, not by timeouts.
- If elaboration consumes unbounded memory with NO heartbeat error, you
  have hit a heartbeat-exempt sink (see issue #12755) — stash, record,
  and move to a different target rather than fighting it blind.

## The remaining ledger (2026-08-23)

- `slot_decode_u256` — BLOCKED on issue #12755 (`retSelCascadeLoop`
  draft is on `wip/retselcascadeloop`, 1886 lines, complete but
  explodes; resume by minimizing the repro or restructuring
  `retSelCascade_sound_aux`).
- `modexp_cmpge`, `modexp_sub`, `modexp_mul`, `modexp_binmod`,
  `modexp_be_to_le`, `modexp_le_to_be` — loops with loads/stores;
  `be_to_le`/`le_to_be` are memcpy-like (existing shapes), `cmpge` needs
  a two-break scan (check `while2BreakJoin` or the ret-tail variants).
- `receipt_records_*`, `edd_*` bundles — multi-entry ABI (several entry
  points into one blob).  ✅ PATTERN ESTABLISHED (#12991,
  `ReceiptRecordsSAsm.lean`): per-entry DCode derivations, then state each
  entry's triple over the SHARED bundle image by instantiating
  `DCode.retSpec`'s `hcode` inclusion with `CodeReq.ofProg_mono_sub`
  (bundle program = concatenation, entry k at instruction index
  `idx k`; the slice/range/bound side conditions close by `decide` after
  an `rfl` equation collapsing `flatten base` to the pinned program —
  works with `base` FREE since plain blocks flatten base-independently).
  No new Stmt node and no new soundness machinery.  Remaining for the
  receipt bundle: `append`/`nth`/`append_runtime_result` read the control
  block AND write the separately-pointed record arena — blocked on a
  dual-writable-region story (single `RwRegion` today); and
  `append_runtime_result` tail-jumps INTO `append`, the composition that
  will consume the shared bundle CodeReq non-trivially.
- CSRS accelerator splices — survey first.
- `extract_deposit_data` main body — sp-frame + calls
  (`call`/`callAt`); the leaf callees (`edd_be32_eq`, `edd_memcpy`) are
  done.
