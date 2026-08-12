# Demand-first String→Program transcription queue (GH #12035)

Which unconverted guest routine to transcribe **next**, ranked by what its
transcription would *unblock* — not by how big it is.

The repo already has two conversion censuses, and neither ranks anything:
`docs/4ch8f-asm-to-program-coverage.md` classifies every `*Function : String`
by shape (ALREADY-STRUCTURED / READY-WAVE3 / BLOCKED_ON_.6 / …), and
`docs/4ch8f-guest-image-coverage.md` measures which `.text` bytes a converted
`_prog` covers. Both answer *how big* and *how hard*. Neither answers *who is
waiting*, so transcription picked from either is transcription ordered by
**cost** — which is how routines that four proof lanes are stalled behind stay
`String`-only because they are large, while leaves nobody is blocked on keep
landing. This document is the missing third axis.

**GENERATED FILE — do not hand-edit.** Rendered from
`scripts/asm-fixtures/transcription-queue-template.md` (prose and placeholder
slots only — no figures) plus live numbers from the generator:

```
python3 scripts/transcription_queue.py --write-doc      # regenerate THIS FILE
python3 scripts/transcription_queue.py --check-doc      # drift check
python3 scripts/transcription_queue.py                  # human summary
python3 scripts/transcription_queue.py --all            # every named row
python3 scripts/transcription_queue.py --self-test      # scorer/matcher self-test
python3 scripts/transcription_queue.py --refresh-issues # the ONE network mode
```

`scripts/check-transcription-queue.sh` wraps `--check-doc` for CI. Every mode
except `--refresh-issues` reads the tree and a committed issue snapshot only,
so the same tree renders the same bytes.

## 1. Method

**Universe and cost.** The rows are the unconverted half of the guest-image
census, taken from `guest_image_coverage.load_converted()` — a `.text` symbol
is *converted* iff a `scripts/asm-fixtures/MANIFEST.tsv` row binds it to a
`"<entry>:\n" ++ emitProgram…` Function whose `_prog` carries a kernel-checked
`#guard <prog>.length = N` pin. Extent (symbol start → next symbol) is the
**cost** column. Cost is printed and never scored.

> `EvmAsm/Codegen/GuestAddrs.lean` is **not** consulted, and must not be: it
> lists `String`-only routines that are called by address and omits probe-only
> routines that exist, so presence there proves nothing in either direction.
> The representation-independent check this file uses instead is the emitted
> label literal (§4).

**Demand.** Five evidence sources, weighted so that *being named as a blocker*
always beats *being popular*:

| signal | weight | source |
|---|---:|---|
| obligation blocker | @@W_OBLIGATION@@ per distinct obligation | `EvmAsm/Progress/Obligations.lean` `blockedBy` (the `note`/`auditedAt` fields are excluded — a note saying "X is now `.proven`" is the *opposite* of a blocking claim) |
| named residual | @@W_RESIDUAL@@ per declaration | a declaration whose NAME carries `Residual` (the `…ResidualNote` discharge-owner convention) and whose text names the routine |
| open `proof` issue | @@W_ISSUE@@ per issue | `scripts/proof-issues.json`, a committed snapshot of `gh issue list --label proof --state open` (@@N_ISSUES@@ issues) |
| registry gate | @@W_GATE@@ per row | a `.conditional`/`.execSpec` row in `EvmAsm/Progress/Routines.lean` whose `gate`/`notes` prose names the routine |
| call site | @@W_CALLSITE@@ each, capped at @@CALLSITE_CAP@@ (≤ @@CALLSITE_MAX@@) | emitted-instruction references only, using `scripts/check_routine_liveness.py`'s pattern set — a name is not a contract, so docstrings and `#guard`s count for nothing |

`@@CALLSITE_MAX@@ < @@W_OBLIGATION@@` by construction, and `--self-test`
asserts it: no amount of call-site popularity can outrank a single obligation
row. The weights are *ratios*, not calibrated constants — the only property
that matters is the order they impose.

Issue **#@@SELF_ISSUE@@ is excluded from the issue signal.** It is this
queue's own issue, and it names the routines it expects to see ranked highly;
counting it would make the ranking circular — the queue would "discover"
exactly what its specification told it to find. Everything in §2 stands on
evidence that predates it.

**A signal scoring zero is not a broken signal.** The residual scanner reads
@@N_RESIDUAL_DECLS@@ `Residual`-named declarations today and @@N_RESIDUAL_HITS@@
of them name an unconverted routine. When that second figure is 0 it is a
result, not a bug: every named discharge owner in the tree
(`witnessLookupResidualNote`, `zkvmSha256ResidualNote`, `hpDecodeResidualNote`,
the `*_wl_call_residual` family) points at a routine that has already been
transcribed. Read a zero there as "the residual wall those notes described has
been cleared", and re-check the scanner only if it also disagrees with a `grep`
for `ResidualNote`.

**The queue proper is the *named* set** — routines some human-written artifact
says are blocking. Routines whose only signal is call-site popularity are the
tail (§5), reported as a count and a top-N rather than dressed up as ranked
work.

## 2. The queue (top @@TOP_N@@ of @@N_NAMED@@)

@@QUEUE_TABLE@@

Reading the columns: **demand** is the score; **evidence** is what produced it
(`obl N` = obligation N's blocker list, `#N` = open issue, `gate N` = N gated
registry rows, `resid N` = N residual declarations); **shape** is §4; **cost**
is extent bytes, or `interior` for a label that shares an address with the next
symbol (`.dispatch_loop` sits at the same address as
`.runtime_tx_message_entry`, so the next-symbol extent model gives it 0 — its
real transcription cost is the enclosing dispatcher body's).

A `derived` row can never rank above the base it is `.replace`-generated from,
however its own signals score: the base is a hard prerequisite, so derived rows
sort on the base's score and lose every tie.

## 3. Declared judgement calls

Everything below is a **hand-written claim** that a piece of evidence is about
a symbol it does not spell. It is listed here, in full, so it can be audited or
challenged — this is the only hand-ranking anywhere in the generator.

**Spec-side identifiers.** Names from the Lean spec side that denote a guest
routine:

| identifier | guest symbol | why |
|---|---|---|
@@ALIAS_TABLE@@

**Prose anchors.** Regexes matched against obligation blocker text and issue
bodies, for evidence that describes a routine without naming it:

| pattern | guest symbol | why |
|---|---|---|
@@ANCHOR_TABLE@@

**Opcode mnemonics are handled mechanically, not by hand.** Obligation 5's
blockers are `.opcode "RETURN"`-shaped plus a counted set ("14 `.execSpec`
entries have no RV64 subroutine"); neither spells `h_RETURN`. The mnemonic list
comes from `EvmAsm/Progress.lean`'s registry (so a renamed or promoted opcode
drops out on its own), the range form `LOG0..4` expands to `h_LOG0 … h_LOG4`,
and a mnemonic only counts where it is used **as** an opcode — backticked,
`.opcode "…"`, or `h_…`. A bare word-boundary sweep is a homonym generator: the
prose is full of `does NOT yet discharge`, `the CALL family`, `AND`, `GAS`, and
an earlier revision of this script ranked `h_NOT` eighth on exactly that. For
the same reason a tier is expanded only where it is *counted* (`14
\`.execSpec\` entries`) — obligation 3's "`rlp_item_span` is `.conditional`
short-list only" is a claim about one routine, not about the opcode set.

Every application of a declared alias, anchor, tier set or derivation roll-up
in the current tree:

| symbol | via | why |
|---|---|---|
@@VIA_TABLE@@

## 4. Authoring shape (what transcription actually costs)

How the routine's text reaches the image — the transcribability question that
`GuestAddrs.lean` cannot answer:

| shape | count |
|---|---:|
@@SHAPE_TABLE@@

* `label-string` — an emitted label literal `"<sym>:\n"` (or `"<sym>:"`) exists
  in an `EvmAsm/**` Lean file; the enclosing `def` is recorded in the
  generator's detail column. Directly transcribable.
* `handler-spec` — an `OpcodeHandlerSpec` row (`label := "<sym>"`) whose body is
  raw `preBody`/`tail` strings; the entry label is emitted by the table
  renderer, so no label literal exists. `h_KECCAK256`
  (`EvmAsm/Codegen/Programs/EvmHashHandlers.lean`) is the shape's type
  specimen: `preBody` and `tail` are `String`, `body` is `[]`.

  ⛔ **DESIGN-BLOCKED, NOT MERELY UNCONVERTED. Do not pick a `handler-spec` row
  off this queue as an ordinary transcription — it is not one.** Measured on
  `h_KECCAK256` (#12128): **no `h_*` handler has ever been converted** —
  `MANIFEST.tsv` has 0 of 426 such rows — and three structural blockers explain
  why, each surfaced by `asm_to_program.py` itself:

  1. handlers use the GNU-as **numeric local label** form (`137f` / `137:`,
     `Dispatch.lean:176-182`), which the converter does not support;
  2. they branch to the dispatcher-owned `.exit_outofgas`, ~65 KB away and far
     outside B-type ±4 KiB reach, so the assembler **relaxes every such branch**
     into `beqz .+8 ; j …` — meaning the instruction count is a function of the
     **link layout, not the source text**, and `emitProgramR` has no
     symbolic-branch reloc kind able to express that;
  3. `dispatchContinueRet` (`Dispatch.lean:251-252`) does
     `la x1, .Ldispatch_resume`, and **`.L*` symbols are discarded by the
     assembler** (`riscv64-elf-nm` finds zero in the guest ELF), so no
     `GuestAddrs` anchor can exist and the verification view has nothing to bind
     to.

  Blocker 3's fix changes emission for **all ~120 handlers**, so unblocking this
  class is a dispatcher/emitter design change, not a per-routine conversion. The
  ranks below are therefore **demand estimates for work that cannot start yet**;
  they say what the class is worth, not that it is available. This affects every
  `.execSpec` opcode row (obligation 5), including `h_SLOAD`/#11654.
* `derived` — the Function is built by `.replace` from another symbol's
  Function. The whole `witness_codes_*` family is generated this way from the
  `witness_*` state-index family, so it is **not** independently
  transcribable — converting the base is the prerequisite.
* `not-authored` — none of the above; the symbol reaches the image through a
  composite emitter, a layout template, or a data section.

The label test demands the colon be followed by `\n` or the closing quote.
The loose form matches the roundtrip stub
`"witness_codes_lookup_by_hash: ret"` in
`EvmAsm/Codegen/Programs/CallFrameRoundtrip.lean`, which would report a 620-byte
routine as authored-and-ready when what exists is a two-token placeholder.

## 5. The popularity tail

@@N_TAIL@@ unconverted routines have call sites but are named by no obligation,
residual, issue or gate; @@N_SILENT@@ have no signal at all. These are **not**
ranked work: a heavily-called routine that nothing is waiting on is still
nothing anyone is waiting on. Top @@TAIL_TOP_N@@ by call count, as a watchlist:

@@TAIL_TABLE@@

## 6. What this queue CANNOT see

A queue that overstates its coverage is worse than one that admits its blind
spots. In rough order of how much they matter:

1. **Unwritten demand.** A proof lane blocked on a routine that nobody recorded
   in an obligation, a residual, an issue or a gate scores zero here. The
   queue measures *written-down* demand, and its accuracy is bounded by the
   freshness of `Obligations.lean` and the issue tracker.
2. **Stale demand.** The converse: a blocker whose transcription already landed
   still scores until someone edits the row. Obligations 7 and 10 currently
   describe `witness_lookup_by_hash` as "`String`-only … 620 B UNCONVERTED"
   although it is converted and in `guestImageEntries`; the routine correctly
   does **not** appear in §2 (the universe is computed, not read from the
   prose), but the prose that named it is now wrong. The universe is always
   fresher than the evidence.
3. **Suffix-only mentions.** Symbol matching is strict on both sides
   (`witness_lookup_by_hash` does not match `witness_lookup_by_hash_indexed` —
   a different 200-byte symbol). The price is that a routine mentioned *only*
   as a suffixed theorem name (`<sym>_spec_within`) and never bare is invisible.
4. **Structural blocking that no prose states.** `.dispatch_loop` contains the
   per-opcode gas debit (`EvmAsm/Codegen/Dispatch.lean`, the
   `opcode_gas_costs` → `env+568` charge before the table jump). Because that
   code is inside a `String`, no triple can observe the debit at all, which
   silently weakens every handler-level gas claim downstream. Nothing in the
   tree says so in a form this script can read; the anchors in §3 catch
   `.dispatch_loop` for other reasons, and its rank should be read as a floor.
5. **Cost is a proxy.** Extent bytes measure the routine's size, not the
   difficulty of its proof obligations, its register discipline, or whether it
   is a multi-entry bundle or caller-local fragment (the classes
   `docs/4ch8f-asm-to-program-coverage.md` tracks and this file does not).
6. **Closed issues.** Only *open* `proof`-label issues count. A closed issue
   whose residual survived it contributes nothing.
7. **Non-`proof` labels.** Issues without the `proof` label are outside the
   snapshot entirely.

## 7. Cross-check against the other censuses

| figure | here | `docs/4ch8f-guest-image-coverage.md` |
|---|---:|---:|
| `.text` symbols | @@N_SYMS@@ | @@N_SYMS@@ |
| converted **and linked** | @@N_CONVERTED@@ | @@N_CONVERTED@@ |
| unconverted | @@N_UNCONVERTED@@ | @@N_UNCONVERTED@@ |
| unconverted bytes | @@TOTAL_UNCONVERTED_BYTES@@ | see below |

Both sides come from the same loader, so they agree by construction. Two
figures need care. First, **converted-and-linked is not the manifest total**:
`scripts/asm-fixtures/MANIFEST.tsv` has @@N_MANIFEST@@ conversion rows, of
which @@N_UNLINKED@@ have no entry symbol in the linker-facts table
(converted but not linked — gas helpers etc. awaiting wiring). Those are not
`.text` symbols, are not in `guestImageEntries`, and are **not** queue rows.
Quoting @@N_MANIFEST@@ as "converted symbols" is the easy error here.

Second, the guest-image doc reports **gap ranges**, of
which there is one more than there are unconverted symbols — the extra is the
`TAIL` gap on `requests_hash_verify` (12 B), a *converted* symbol whose `_prog`
is shorter than its linker extent. Gap bytes therefore exceed unconverted bytes
by exactly those 12 B. That range is real transcription-adjacent work, but it is
not a routine, so it has no queue row.

The `docs/4ch8f-asm-to-program-coverage.md` totals are **not** comparable: that
census counts `*Function : String` **defs** (including composites, probe
prologues and unlinked helpers), while this one counts **linked `.text`
symbols**. A single symbol can have several Function defs and a Function def
need not be linked, so neither total bounds the other.

Named-set cost: @@NAMED_BYTES@@ B of @@TOTAL_UNCONVERTED_BYTES@@ B unconverted
— i.e. the routines anything is demonstrably waiting on are a small fraction of
the unconverted mass, which is the point of ranking by demand rather than by
bytes.

## 8. Full named table (@@N_NAMED@@ rows)

@@FULL_TABLE@@
