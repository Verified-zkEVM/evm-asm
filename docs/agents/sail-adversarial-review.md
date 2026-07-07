# Sail-zkVM integration — adversarial review of the P2 hand-off (2026-06-25)

**What this is.** An independent verification of the P2 "core migration done" hand-off
(`sail-phase3-bootstrap.md`), run against the actual repo rather than the bootstrap's
prose. Every claim below is backed by a command run this session. TL;DR: **the migration
is real and green**, but three trust claims are overstated and two doc surfaces are stale.
The corrected priorities are folded into `sail-phase3-bootstrap.md`.

## Verified TRUE (hand-off holds)

| Claim | Evidence |
|---|---|
| Full build `lake build EvmAsm` = 2984/2984, exit 0 | ran clean this session |
| 51 `*_sail_equiv` lemmas | `grep` over `EvmAsm/Rv64/SailEquiv/` = 51 |
| 0 `sorry`/`admit` in `SailEquiv/` | grep = 0 |
| 0 `native_decide`/`bv_decide` in `SailEquiv/` proof sources | grep = 0 |
| `dhsorens` gone from the **build** (lakefile + manifest) | only a lakefile *comment* remains |
| Vendored model = 113 `.lean` files (excl. `.lake`) | matches PROVENANCE `[target]` |
| **ALU** lemmas genuinely 3-axiom clean | `#print axioms add_sail_equiv` = {propext, Classical.choice, Quot.sound} |

## Findings (overstated / stale — ordered by severity)

### F1 (HIGH) — "3 classical axioms only" is FALSE for memory ops
PROVENANCE `[target].notes` and the P4 exit criterion both claim the lemmas reduce to the
three classical axioms. Reality, verified by `#print axioms`:

- `add_sail_equiv` → `{propext, Classical.choice, Quot.sound}` ✅ (clean)
- `ld_sail_equiv` → classical **+ `load_reservation, plat_term_write, sys_enable_experimental_extensions`**
- `sd_sail_equiv` → classical **+ `match_reservation, plat_term_write, sys_enable_experimental_extensions`**

These are Sail-model *platform* axioms (terminal I/O, LR/SC reservation bookkeeping,
experimental-extension gate) declared in the vendored model — they are the model's trust
boundary, not a soundness hole. But the consequence is concrete: **P4's
`step_execute_sail_sim` cases over memory ops and WILL inherit them, so its stated exit
criterion ("`#print axioms` = 3 classical only") is unachievable as written.**

→ Fix: rewrite the P4 exit criterion and the PROVENANCE note to "3 classical + an
enumerated, justified Sail-platform allowlist": `{plat_term_write, load_reservation,
match_reservation, sys_enable_experimental_extensions}`. Document *why* each is an
acceptable boundary (they abstract host/platform effects outside the pure ISA step).

### F2 (RESOLVED 2026-06-25) — `model_sha256` recipe was underspecified (hash is correct)
PROVENANCE `[target].model_sha256 = 3a49ffa5…` documented recipe
`find -name '*.lean' | sort | xargs sha256sum | sha256sum`. As written it does **not**
reproduce the hash — the variations I tried landed on `1c6b5294…`, `4f3a5582…`,
`757cee10…`, `5eb37571…`. Root cause was the recipe, not the content: it failed to pin
**(1)** CWD (vendor dir, so paths are `./…`), **(2)** `LC_ALL=C sort` (locale-stable
ordering), **(3)** `./.lake/*` exclusion. The exact invocation

```
cd vendor/sail-riscv-zkvm-lean && \
  find . -name '*.lean' -not -path './.lake/*' | LC_ALL=C sort | xargs sha256sum | sha256sum
```

reproduces `3a49ffa5…` bit-identically across runs (coreutils 9.4). **The committed model
content is intact.** Fixed: the reproducible recipe is now pinned at the hash line in
PROVENANCE; `check-sail-pin.sh` (P6) must use this exact invocation.

### F3 (MEDIUM) — no axiom / forbidden-tactic CI gate actually exists
`model-review.md §5.6` references `check-axioms.sh` / `check-forbidden-tactics.sh` as live
gates. They are **not in `scripts/`**. `build.yml` runs only `check-file-size`,
`check-unimported`, `check-no-warnings`, `check-progress`. So the project's headline proof
conventions — *no `native_decide`/`bv_decide`* (CLAUDE.md) and the completed bv_decide
purge (290→0) — are **not machine-enforced**; a regression would pass CI. This raises P6's
gate work from "ledger hygiene" to "protect the invariants already won."
→ Fix: add `scripts/check-forbidden-tactics.sh` (grep gate) and `scripts/check-axioms.sh`
(asserts the F1 allowlist), wire both into `build.yml`.

### F4 (MEDIUM) — stale user-facing docs contradict the migration
The migration repointed the build but left the *legible* surface describing dhsorens:
- `PROGRESS.md:119` and `scripts/progress-template.md:110` — "references … via the `dhsorens` fork (`lakefile.toml`)"
- `README.md:404-415` — describes `Lean_RV64D` / dhsorens fork as the dependency
- `AGENTS.md:12` — "Toolchain: Lean 4.28.0-nightly-2026-01-22" (actual: `v4.30.0-rc1`)

For a project whose thesis is auditable legibility, the onboarding docs pointing at the
removed fork is a real defect. → Fix: update all four to the vendored model + correct
toolchain.

### F5 (LOW) — "scoped" model still ships full softfloat axiom set
The vendored model declares **75 axioms**; ~60 are `riscv_fXX` softfloat primitives
(F16/F32/F64 add/mul/div/convert) unused by RV64IM. Not a soundness issue (unreachable
from I/M lemmas, confirmed by the clean ALU footprint), but it undercuts the "smaller
trust/attack surface" justification recorded for the scoping decision. → Note in the
coverage gate (P6): these should be provably unreachable from the shipped `cases`, or
scoped out at generation.

### F6 (LOW) — config still unvalidated + Zicclsm decision not recorded
`riscv64im_zicclsm.json` was produced against sail-riscv `1760ee2` and **never run through
`validate_config`** (carried as P2 residual #5). Separately, `model-review.md §4` flips the
design-doc's Zicclsm recommendation to "(a) model misaligned semantics — essentially free
via config," but the design doc's §9 still lists it as an open question. → Record the
decision; validate the config when the toolchain is available.

## Assessment of the proposed plan

The bootstrap says "start with P4." **P4 is still the right next proof step**, but as
written it would fail its own exit gate (F1). Net re-prioritization, cheapest-and-highest-
leverage first:

1. **Trust hygiene (pure-repo, <1 session):** fix F4 (stale docs), F1 (PROVENANCE prose +
   P4 exit criterion), F2 (nail the `model_sha256` recipe + re-pin). Protects the audit
   thesis and unblocks the gate.
2. **P4 — consolidated sim theorem, corrected spec.** Pure Lean, ~1 session. Exit = builds
   + axioms ⊆ {classical} ∪ {platform allowlist}, allowlist enumerated and justified.
3. **P6 gates, promoted ahead of P3.** `check-forbidden-tactics.sh` + `check-axioms.sh`
   (enforce F1 allowlist) + `check-sail-pin.sh` (after F2). Pure-repo, closes F3 — the
   gap that currently lets any of the above silently regress.
4. **P3 — differential testing.** Genuinely the essential mitigation, but infra-heavy and
   blocked on the Sail toolchain (opam `sail5`, Sail 0.20.2, z3 4.15.3). Do when the
   environment is available; until then it is the one track that cannot start cold.

The key correction to the hand-off's framing: **the cheapest, highest-leverage next work
is trust-hygiene + gates (items 1 & 3), not P4.** They are pure-repo, they protect
everything already proven, and item 1 is a prerequisite for P4 even being able to claim
success.
