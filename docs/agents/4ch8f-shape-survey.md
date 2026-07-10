# 4ch8f shape survey — control-flow census of the unverified guest corpus and its combinator-mappability

**Bead**: `evm-asm-4ch8f.70` (planning; no code changes).
**Deliverable**: this doc + a recipe-table addendum to `docs/agents/roadmap-4ch8f.md`
+ the child beads listed in §6.
**Author's stance**: front-load the "which loop idiom does this routine use, and does a
combinator byte-match it?" discovery into one systematic pass, so no future
verification session stalls on an unmatched shape (as happened reactively for
`whileBreak` #9804, `doWhile` #9818, `doWhileS` `.69`).

---

## 0. TL;DR (the reviewer's four answers)

1. **The corpus is already combinator-aligned by construction.** Every one of the
   **628 loop back-edges** in the guest falls into one of the four shapes that
   already have SAsm combinators (`while`/`whileS`, `doWhile`/`doWhileS`,
   `whileBreak`), and **zero** use the "rotated while" lowering that would *not*
   byte-match. There is **no missing loop combinator** for the emitted shapes.
   The reactive discovery pain was not a combinator shortage — it was the absence
   of *this census*.
2. **72 % of routines (612 / 848) have no loop at all** — straight-line blocks
   and branch cascades — and map to `block`/`ite`/`when` with no loop reasoning.
3. **The re-emission lever is a convention, not a codegen knob.** The asm strings
   are *hand-authored* (there is no DSL/compiler pass emitting the bodies), so
   there is nothing to "reshape uniformly." But the reason we byte-match is a
   *disciplined authoring house-style* (canonical loop lowering). The
   highest-value action is to **codify that house-style as a lint** so future
   hand-written routines stay portable-by-construction, rather than to build a
   reshape pass. (§5)
4. **Only two genuine shape gaps remain**, both narrow: `mpt_insert` / `mpt_set`
   contain an **early `ret` from inside a loop** (function-return-from-loop),
   which no single-exit combinator models directly (§4.2); and a handful of
   **high-fan-out verdict/gate monoliths** carry loops whose multi-way exits need
   per-loop analysis before their (already-planned) monolithic beads (§4.3).

---

## 1. Method & honesty ledger

**What was counted vs sampled.** The census below is **exhaustive, not sampled**:
a CFG parser (`scratchpad/shape.py`, reproduced in `scripts/` per §6 bead .70.1)
read **all 848** `*Function : String` definitions under
`EvmAsm/Codegen/Programs/*.lean`, split each into instructions (honoring `;`
instruction packing and `--`/`#` comments), resolved every branch/jump target
against the label table, and classified each **local (`.L`) back-edge** by shape.
Cross-routine `j <named_routine>` jumps (many `Function` strings bundle several
named sub-routines) are tail-calls, **not** loops, and are excluded from the
back-edge counts — this correction matters (it removed ~7 spurious `whileBreak`
and all but 2 spurious `ret`-in-loop hits).

**Coverage gap, stated plainly.** `grep` finds ~851 `…Function` identifiers; the
parser analyzed the **848** that are `: String :=`. The 3 remainder are
non-string helpers, excluded. The classifier is a static CFG heuristic: it is
authoritative for back-edge *existence* and *top-vs-bottom test* (those are pure
structure), and for the **0 rotated-while / 0 indirect** results (strong
negatives). Its `whileBreak`-vs-multi-exit boundary is an over-approximation
(§4.1) — the 157 "multi-exit" functions were **triaged by sampling**, not each
read by hand; representative samples are cited.

**What "byte-match" means here.** SAsm's `flatten` (`EvmAsm/Rv64/SAsm/Flatten.lean`)
emits, for each loop combinator, an exact instruction sequence:

| combinator | flattened shape (Flatten.lean) |
|---|---|
| `while` / `whileS` | `Lhdr: B¬c → Lend · body · J → Lhdr` (top guard, **unconditional** back-jump) |
| `doWhile` | `body · [guard → Lbody]` (no header, the **conditional** branch *is* the back-edge) |
| `whileBreak` | `Lhdr: B¬guard → Lend · before · B break → Lend · after · J → Lhdr` |

A routine is "portable as-is" when its emitted loop already has this byte shape.
The census key insight is that **it always does** — see §2.

---

## 2. Shape census (all 848 routines)

### 2a. Top-level control-flow class

| class | count | % | maps to | portability |
|---|---:|---:|---|---|
| **straight-line, no branches** (flat block) | 424 | 50.0 | `block` / `blockAt` | port as-is |
| **straight-line, branch cascade** (forward branches only) | 188 | 22.2 | `ite` / `when` (+`block`) | port as-is |
| **has ≥1 loop back-edge** | 236 | 27.8 | loop combinators (below) | per §2b |
| **indirect jump (`jr`/`jalr`)** | 0 | 0.0 | — (`callReg`/`callRegS` reserved for dispatch) | n/a |
| **total** | **848** | 100 | | |

Of the 236 looping routines, **159 have a single loop** and **77 are nested
(≥2 back-edges)**. The heaviest are `balCodePreimagesValid` (43),
`blockVerdictFunction` (38), `txEip7702ExistingAuthorityRefund` (26).

### 2b. Loop back-edge census (628 back-edges across the 236 looping routines)

| emitted shape | back-edges | byte-matching combinator | gap? |
|---|---:|---|---|
| top-test `while` (header guard + unconditional back-jump) | **493** | `Stmt.while` / `Stmt.whileS` | none |
| bottom-test `do-while` (body + conditional back-branch) | **100** | `Stmt.doWhile` (#9818) / `Stmt.doWhileS` (`.69`) | none |
| mid-break `whileBreak` (header guard + mid-loop break) | **34** | `Stmt.whileBreak` (#9804) | none |
| **"rotated while"** (`j .Ltest; body; .Ltest: Bcc body`) | **0** | — (would need a new combinator) | **absent — good** |
| unresolved (1 back-edge inside the `blockVerdictFunction` monolith) | 1 | — | analyze in .61 |

**This is the headline.** The GCC-style *rotated* while (entry jumps forward to a
bottom test, body may run 0 times, conditional back-branch) is the one common
lowering that matches *no* current combinator. The guest uses it **zero** times:
top-test loops are *always* emitted as `header-guard + unconditional J-back`
(= `while`), and bottom-test loops as `body + conditional-branch-back`
(= `doWhile`). This is not luck; it is the authoring convention (§5).

Every loop combinator already has a proved exemplar: `while`/`whileS`
(`SAsm/*Demo.lean`, `KeccakReverseSAsm`, `BalValueReverseSAsm`), `whileBreak`
(#9804 + `SwdMinimalCopySAsm`), `doWhile` (#9818). `doWhileS` (`.69`) is the
last one in flight.

### 2c. `while` vs `whileS`, `doWhile` vs `doWhileS` is a *proof-side* choice, not an asm shape

The snapshot (`S`) variants emit **identical bytes** to their plain siblings
(`Flatten.lean` lines 66–71, 78–79: `whileS` = `while`, and `doWhileS` will = `doWhile`).
They differ only in the *invariant signature* — the `S` variants thread an
entry-snapshot so an **inner** loop can see an **outer** loop's counter register
(`sp` forgets the entry reach). Therefore: **you cannot read "needs whileS" off
the asm.** The rule is structural-context, not shape:

> A loop that is the *inner* loop of a nest, and whose invariant must reference a
> register set by the enclosing loop, uses the `S` variant. All 77 nested
> routines are the population that may need `whileS`/`doWhileS` on their inner
> loops; the 159 single-loop routines never need `S`.

This is exactly why `.69 doWhileS` was needed for *outer counting loops* whose
body is itself a bottom-test loop — and why the survey files a **doWhileS/whileS
consumer inventory** (bead .70.3) so `.69` lands with its consumers known.

---

## 3. SpecRef alignment

**Current SpecRef surface** (`EvmAsm/Stateless/SpecRef/`): 9 modules — `Guest`,
`Stateless`, `Runtime`, `Ssz`, `SszCodec`, `Secp256k1Recover`, `WitnessState`,
`Crypto`, `Types`. This mirrors `execution-specs@tests-zkevm@v0.4.0` and covers
the **top-level shell + SSZ codec + secp recover + witness-state + runtime seam**.
The **majority of the 848 leaf/composite routines do not (yet) have a SpecRef
counterpart** — per the roadmap, their functional post is stated against a
leaf-level byte equation that a later SpecRef bridge consumes. So "SpecRef
alignment" today is a question for the routines that *do* have a mirror, plus a
forward-looking rule for the rest.

**Where SpecRef exists, it is functional/monadic** (`Except`, `List.range`,
`.foldl`, structural recursion) — the Python `for`/`while` becomes a fold or a
`List.range` map. The emitted guest loop aligns to it the standard way:

> **loop ⇄ fold.** A `while`/`doWhile` whose invariant `inv i` states
> "registers/memory = the partial fold after `i` steps" discharges directly
> against a spec `List.foldl`/`List.range` — the emitted top-test/bottom-test
> shape *is* the fold's iteration. No re-emit is needed: the shape already
> matches the spec's natural structure. The proof novelty is the **invariant
> (the partial-fold statement)**, not the control flow.

**Divergence assessment — concrete calls:**

- **RLP read primitives** (`rlp_item_size`, `rlp_field_to_u256_be`): emitted as a
  top-test `while` accumulating a big-endian length; the spec is a
  `List.foldl (·*256 + ·)`. **Aligned** — invariant = partial BE-accumulate. No
  re-emit. (Sampled `rlpItemSizeFunction`: `.Lris2_be` is a clean top-test while.)
- **byte/copy leaves** (`*_rev_le_be`, `sg_memcpy`, reverse-copy): fixed-trip
  `while`; spec is `List.reverse`/`List.take`. **Aligned** (already proved:
  `KeccakReverseSAsm`, `BalValueReverseSAsm`, `SwrRevLeBeSAsm`). No re-emit.
- **crypto field-arith limb loops** (`bls12_fq12_mul`, `bn254_fq12_mul`: 6
  `doWhile` each; `secp256k1`/`modexp` ladders): emitted as bottom-test `doWhile`
  over a fixed limb count; spec is a fixed fold / `Nat.pow` ladder
  (`Crypto/PowLadder.lean`). **Aligned** — `doWhile` invariant = partial limb
  product. No re-emit. (These are `.38`/`.57`/`.58`.)
- **BAL-consistency scanners** (`bal_storage_matches_exec_log`,
  `bal_all_accounts_*_consistent`): emitted as nested top-test `while` with a
  mid-break search; spec is `List.all`/`List.foldl` over tuples. **Aligned in
  shape**; the proof cost is the *nesting* (inner loop needs `whileS` to see the
  outer index), not a shape mismatch. (`.41`–`.43`.)
- **`txEip7702ExistingAuthorityRefund`** (26 `doWhile`): emitted as many
  sequential fixed-trip bottom-test loops; spec is a sequence of folds over the
  authorization list. **Aligned**; high count = many independent limbs, each a
  clean `doWhile`. (`.40`.)

**Verdict:** no routine's emitted shape *diverges* from its spec's natural
structure in a way a drop-in would fix — because the emission is already
fold-shaped. The lever for shrinking proof novelty is **choosing the right
invariant / `S`-variant**, not re-emitting bytes. The one exception class is
early-return-from-loop (§4.2), where the *spec* is a short-circuiting `find`/`any`
and the emission's mid-loop `ret` is the honest match — but that shape has no
single-exit combinator.

---

## 4. Risk features & the two genuine gaps

### 4.1 Multi-way-exit loops (157 routines) — mostly `whileBreak`, not a gap

157 routines contain a loop with **≥2 distinct `.L` exit targets** (a loop whose
completion and whose mid-break jump to *different* labels). Triage by sampling:

- **The common case is *search-until-found*** (guard-completion → "not found"
  label, match → "found" label). Sampled `accountExistsAtBlockNumberAddress`:
  a header scan with `beq s8,s7,.Laebn_finish` (done) + a match break. This is
  `whileBreak` with the found/not-found distinction carried in the predicate-out
  register the body sets before breaking — **`post` is single, byte shape matches
  `whileBreak`.** The `maxexits=2` majority (≈130 of 157) are this idiom.
- **The hard subset is the high-`maxexits` verdict/gate monoliths**:
  `eip8037TxGasGate` (maxexits 5), `balCodePreimagesValid` (maxexits 4, 43 loops),
  `blockVerdictFunction` (38 loops). These have loops with genuinely divergent
  continuations and are **already** planned as monolithic composition beads
  (`.36`, `.43`, `.61`). They need per-loop shape maps *inside* those beads, not
  new combinators — filed as .70.4 (pre-analysis annotation).

### 4.2 Early-return-from-loop (2 routines) — **the one real combinator question**

`mpt_insert` (`MptInsert.lean`) and `mpt_set` (`MptSet.lean`) each contain a `ret`
**inside** a `.L` loop body — the walk returns from the *whole function* mid-scan
(short-circuit on a found/leaf node). None of `while`/`doWhile`/`whileBreak`
model an early function-return: they all exit to a single in-`Fn` `post` and fall
through. Two resolutions, to be decided in bead **.70.2** (callee-blocker for the
MPT beads `.29`/`.31`):

1. **`whileBreak`-to-epilogue** — if the `ret` is preceded only by
   epilogue-equivalent setup, model the break target as the function post and let
   the shared epilogue `ret` serve both exits. Likely works if the mid-`ret` and
   the fall-through `ret` restore the same frame; needs a byte check.
2. **Drop-in re-emit** — rewrite the walk so the early return becomes a
   `whileBreak` break to a single tail `ret` (guest-byte change → EEST A/B under
   the drop-in policy). Small, local, one routine each.

This is the *only* place the survey finds a shape that no current combinator
byte-matches. It is narrow (2 routines, same family) and both options are
one-session.

> **RESOLVED (bead .70.2): option 1 — whileBreak-to-epilogue, byte-transparent.**
> Byte-level inspection of the emitted programs (`mptSetAcc_prog` /
> `mptInsertAcc_prog`, the linked-image variants beads .29/.31 target) shows the
> "mid-loop `ret`" is not a second `ret` at all: each routine has exactly ONE
> `ret` and one frame restore, and the loop break targets a 2-instruction fail
> stub `li a0, 2 ; j <epilogue>` that jumps *backward* into the shared epilogue
> — so "both paths restore the same frame" holds by construction.
> `EvmAsm/Rv64/SAsm/RetFromLoop.lean` adds the missing piece at
> `cpsTripleWithin` level (additive): `liJumpTailProg`/`multiRegJumpTail_spec`
> (the `li* ; j join` tail — `multiRegRetTail_spec` with the terminal `ret`
> replaced by the jump) and `jumpJoinTail_spec` (tail ∘ shared-epilogue
> continuation), plus an end-to-end demo (`EarlyRetLoop.earlyRetLoop_spec`).
> The loop itself is the existing `breakStation_spec`/`twoBreakRetLoop_spec`.
> `EvmAsm/Codegen/Programs/MptEarlyRetShape.lean` is the kernel-checked byte
> check on the real programs: `prog.drop failIdx = liJumpTailProg [(a0, 2)]
> (-56)`, single-`ret` count, all break/back-edge/epilogue offsets (relative,
> symbolic base, no address pins), and the reusable
> `mptSetAcc_failTail_spec`/`mptInsertAcc_failTail_spec` break-arm triples.

### 4.3 The unresolved back-edge

1 of 628 back-edges (inside `blockVerdictFunction`, the 38-loop verdict monolith)
did not resolve to a clean shape under the static heuristic — an artifact of the
monolith's size, not a new idiom. Resolve during `.61` (it already carries its
own plan note).

---

## 5. The re-emission lever — verdict

**Is the asm generated by a codegen pass we can reshape uniformly? No — and that
reframes the answer.** The `*Function : String` defs are **hand-authored RISC-V
assembly** (the guest image's source of truth; `asm_to_program.py` converts them
to `_prog`, `emitProgram` splices verified triples back). The only *rendered* asm
is the **dispatcher scaffold** (`Dispatch.lean`, from an `OpcodeHandlerSpec`
registry) — and per its own header comment the handler *bodies* are still raw
asm. So there is **no single knob** that emits the 848 loop bodies; a
"codegen-level reshape" has nothing to hook.

**But the census proves the bodies are *already* uniformly shaped** (0 rotated,
0 indirect, every back-edge in a combinator family). That uniformity is a
**disciplined authoring convention** — top-test⇒`header-guard+J-back`,
bottom-test⇒`body+cond-branch`, mid-break⇒`whileBreak`. The correct lever is
therefore **not to build a reshape pass but to protect the convention**:

> **Recommendation: add a loop-shape lint** (bead .70.1) to
> `scripts/check-asm-to-program.sh` (or a sibling) that fails CI if any
> `*Function` asm contains (a) a rotated-while (`j` to a bottom test), (b) an
> indirect `jr`/`jalr` outside the sanctioned dispatch sites, or (c) an early
> `ret` inside a `.L` loop (the §4.2 shape) that isn't on an allow-list. This
> makes portability-by-construction a *checked invariant* instead of a lucky
> convention, and turns the "reactive mid-port discovery" failure mode into a
> pre-merge signal. It reuses the CFG parser written for this survey.

Per-routine drop-in re-emit remains the tool for the rare genuine mismatch
(§4.2), governed by the existing drop-in policy (guest-byte change accounted for
+ EEST A/B parity). No wholesale re-emission is warranted or possible.

---

## 6. Prioritized plan & child beads

**(a) Shape-class table** → §2 (and the roadmap recipe-table addendum).
**(b) Combinator-gap list** → essentially empty: **no new loop combinator is
needed for the emitted shapes.** The only shape without a byte-match is
early-return-from-loop (2 routines, §4.2), routed to a *decision* bead (drop-in
vs `whileBreak`-to-epilogue), not a new-combinator bead.
**(c) Per-family recommendation:**

| family (bead) | dominant shape | recommendation |
|---|---|---|
| leaves .12/.13/.16, RLP .14/.15 | flat block / fixed-trip `while` | **port as-is** (exemplars proved) |
| decode/extract/gas .25/.26/.33/.35/.36/.37 | branch cascade + single `while` | **port as-is** (`ite`/`when`+`while`) |
| MPT .28/.29/.31 | `while`+`whileBreak`, **early-ret** in insert/set | **.70.2 first** (early-ret decision), then port |
| trie roots / BAL .32/.41/.42/.43 | nested `while`, inner needs `whileS` | **port as-is**, tag inner loops `whileS` |
| crypto .38/.57/.58 | fixed-trip `doWhile` limb loops | **port as-is** (`doWhile` + PowLadder fold) |
| gas .40 (`txEip7702…Refund`) | 26× sequential `doWhile` | **port as-is** (independent limbs) |
| verdict monoliths .36/.43/.61 | high-fan-out multi-exit | **.70.4 pre-analysis** inside the monolith beads |
| outer counting loops (various nested) | `doWhile` outer + `whileS`/`doWhileS` inner | **depends `.69`**; inventory in **.70.3** |

**(d) Child beads to file** (callee-first; see §6 tail for the actual `bd create`):
- **.70.1** (P2, tooling) — loop-shape lint enforcing the authoring convention
  (rotated-while / stray-indirect / early-ret-in-loop guard). Ships the CFG
  parser to `scripts/`.
- **.70.2** (P1, shape decision, **blocks .29/.31**) — resolve early-return-from-loop
  in `mpt_insert`/`mpt_set`: `whileBreak`-to-epilogue vs drop-in re-emit; produce
  the byte check either way.
- **.70.3** (P1, inventory, **depends .69**) — `doWhileS`/`whileS` consumer list:
  enumerate the nested routines whose inner loop needs an `S` variant, so `.69`
  lands with known consumers and the nested beads pick the right combinator up
  front.
- **.70.4** (P2, pre-analysis) — per-loop shape maps for the three loop-heavy
  monoliths (`blockVerdictFunction` 38, `balCodePreimagesValid` 43,
  `txEip7702ExistingAuthorityRefund` 26) recorded into their composition beads
  (.61/.43/.40) before those beads start.

**(e) Codegen-reshape verdict** → §5: **not feasible and not needed as a pass**;
replaced by the convention-lint (.70.1). This is the outcome that changes how the
epic proceeds: byte-matchability is a *solved, checkable* property, so the
remaining epic cost is invariant/proof work per routine, **not** shape wrangling.

**(f) Open questions** (recorded, not forced): the §4.3 unresolved back-edge
(→ .61); whether any `maxexits≥3` verdict loop needs a genuinely new construct
(→ .70.4 will confirm; current read is "no, they decompose into `whileBreak`+`ite`").
