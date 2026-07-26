# The six untracked SAsm files in working checkouts

**Load when:** a `git status` in this repo shows untracked `*SAsm.lean` files
under `EvmAsm/Codegen/Programs/`, or `scripts/check-unimported.sh` fails locally
while CI is green.

**Do not delete them, and do not `git add -A`.** They are not abandoned as far as
anyone has established, and they are not ours to remove. See "What is still
open" at the bottom before acting on them.

This page exists so the next session does not re-run the investigation. It was
written after auditing them once; the evidence for every claim is stated so you
can disagree with any of it cheaply.

## The set

Six files, all untracked, all under `EvmAsm/Codegen/Programs/`:

| file | size | state |
|---|---|---|
| `HeaderExtractLogsBloomSAsm.lean` | 1450 lines, 34 theorems | substantial, 0 `sorry` |
| `ReceiptExtractLogsBloomSAsm.lean` | 1497 lines, 37 theorems | substantial, 0 `sorry` |
| `HeaderValidateExtraDataLengthSAsm.lean` | 550 lines, 13 theorems | substantial, 0 `sorry` |
| `ReceiptExtractLogsBloomComposeSAsm.lean` | 24 lines, 1 theorem | imports the Receipt one |
| `HeaderExtractWithdrawalsRootSAsm.lean` | 59 lines, 0 theorems | **untouched generator stub** — `scripts/gen-port-kit.py` output, still carrying 2 `TODO(port)` blocks |
| `ReceiptExtractLogsBloomSAsm.olean` | 4.6 MB | compiled artifact **beside its source** |

They were once swept into #10544 by a `git add -A EvmAsm/` and had to be
reverted before review. That is why the standing rule is **explicit paths in
every commit**.

## Three facts worth not re-deriving

**1. They have never been tracked, on any branch.**
`git log --all --diff-filter=A` over all six returns empty. Not a merged branch,
not an abandoned one — they have never been in the history.

**2. Committing any of them turns CI red immediately, so the #10544 accident
cannot recur silently.** `scripts/check-unimported.sh` names exactly these five
modules as orphans. Its historical allow-list (`scripts/unimported-allow.txt`)
was drained to zero and removed in #1440, and the script refuses to
re-introduce an escape hatch. That is a second independent reason #10544 had to
be reverted, separate from the 4.6 MB binary — and it means leaving these files
in place costs nothing.

Note the precise consequence of orphan status, because it is easy to get
backwards: `check-unimported.sh`'s own header states that **lake will happily
compile every reachable `.lean` under the library directory**. So orphan files
*are* compiled; what orphan status prevents is anything `import`ing their
declarations. That is why they cannot enter the emitted guest — not because the
build skips them.

**3. Their targets are already landed on main, but these files are not copies of
what landed.** `headerExtractLogsBloom_spec_within` is at
`HeaderExtractLogsBloomSpec.lean:1350`, `receiptExtractLogsBloom_spec_within` at
`ReceiptExtractLogsBloomSpec.lean:1290`, and the history closes all three
contracts at #10358, #10360 and `3f0dac58b`.

But the declaration-name overlap with the landed modules is **4 of 65** for the
header pair and **0 of 31** for the extra-data-length pair, and the four shared
names (`K20B`, `program_length`, `wrapperCode`, `wrapper_list_disjoint`) are
shared scaffolding rather than shared proofs. So these are a **different
decomposition of the same target**, not a stale duplicate of it.

## On the `.olean` — do not read its timestamp

The obvious test is whether the `.olean` is newer or older than its source: a
stale one is build residue, a fresh one suggests someone mid-iteration. **That
signal does not exist in this tree.** All six files carry mtimes identical to
within 20 ms (`2026-07-26 03:10:11`), which is a bulk restore — the #10544
revert putting them back to untracked — not six authoring times.

What *is* informative is a location fact rather than a timestamp one: lake
writes `.olean` files to `.lake/build/lib/lean/…`, both tracked siblings' oleans
are there, and this is the **only `.olean` anywhere under `EvmAsm/`**. It is not
a path lake ever writes to, so it was produced by a direct `lean` invocation or
hand-copied. That points at manual iteration by a person, but it is a single
anomaly and should be treated as a pointer, not a conclusion.

## What is still open

Two things, deliberately not settled:

- **Live work in progress versus abandoned output is NOT established.** The
  targets landing is consistent with either a superseded draft *or* someone
  holding a better decomposition back. Distinguishing them is a reading question
  over roughly 3500 lines of proof, which nobody has done.
- **They have not been verified to still compile against current main.** That is
  the real rot test, and it costs a build.

Ownership is a question for the maintainer, not something either fact above can
settle.

**If they do turn out to be genuinely abandoned, propose removal as its own PR** —
never folded into unrelated work. The two hypotheses that cannot currently be
distinguished have very different costs if you guess wrong, and since CI already
guards against accidental landing, leaving them in place costs nothing.
