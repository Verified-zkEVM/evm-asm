# Spec-aligned rewrite workflow

**Unproven guest code is disposable.** If a RISC-V routine carries no proof, it
may be discarded and replaced outright — there is no obligation to preserve its
structure, its instruction sequence, or its byte image. The goal is **code that
is structure-aligned to `execution-specs` and proven**, not code that is
preserved.

This page is the workflow for getting there. It applies whenever a guest routine
is being reemitted, restructured, or newly written against a reference function.

---

## 1. Start from the reference function, not from the guest

Pick the `SpecRef` function you intend to implement (`EvmAsm/Stateless/SpecRef/`,
a port of the pinned `execution-specs` at `e5a8caf1b`). Read it and enumerate
**its conjuncts, in its order**.

Then look at what the guest does today. The interesting question is not "is the
guest correct" but:

> **Does any single guest routine correspond to this reference function?**

If the reference's checks are spread across several guest routines, **no single
triple can discharge the reference function**, and a correspondence proof has to
compose across separately-rooted routines with different entry contracts. That
is the signal to restructure.

**Worked example.** `SpecRef.validate_header` (`SeamShell.lean:232`) is one
function with eleven conjuncts. The guest split them across `validate_header_full`
(field checks), `chain_validate_increasing_timestamps` /
`chain_validate_consecutive_numbers` (parent-relative), and `headers_parent_hash`
(hash link) — so the proof could not be stated at all. See #12345 / #12346.

## 2. Measure what actually runs before changing anything

⛔ **A routine having a proof does not mean the routine runs.** Before
restructuring, take a **fresh link** and count call sites in the disassembly:

```
riscv64-unknown-elf-objdump -d <fresh>/stateless_guest.elf > dis.txt
grep -cE "j(al)?[[:space:]].*<SYMBOL>" dis.txt
```

Read the result carefully:

- **Zero direct call sites is not proof of dead code** — an indirect call through
  a register does not appear as `jal <sym>`.
- **Dead code is harmless if the check happens elsewhere, and a false ACCEPT if
  it happens nowhere.** Search for the *comparison shape* in the reachable
  routines (two values loaded and a branch to a failure exit), **not** for the
  routine name. **Absence proved by a grep is not absence.**

This step exists because it has already found something: three routines carrying
registry rows — `chain_validate_increasing_timestamps`,
`chain_validate_consecutive_numbers`, `chain_validate_post_merge_full` — had
**zero call sites** on a fresh 2026-08-14 link.

## 3. Rewrite structure-aligned; retire rather than hybridise

- **Mirror the reference's decomposition**: one guest routine per reference
  function, its conjuncts in the reference's order, each with its own failure
  exit.
- **Retire the code being replaced.** Do not leave both paths alive. A
  hybrid is worse than either side: it doubles the surface and nothing states
  which path runs.
- **No byte-equivalence expectation.** The bar is that the structure matches the
  spec and that `r200` does not get much worse.
- **Use `SAsm`.** Structural alignment is a reemission, and `SAsm` both prevents
  hand-picked landing points and eases the proof that follows. See
  `docs/sasm-howto.md`.
- **File-size cap:** 1500 lines under `EvmAsm/Codegen/Programs`, no opt-out. If
  the routine plus its spec exceeds it, split on a **semantic seam** (model vs
  machine contracts, say), never on a line count.

### Allowed exception: where Python and RISC-V genuinely differ

Mirroring is a requirement on the *logic*, not on features the target machine
does not have. Where the reference relies on a Python construct with no RISC-V
counterpart, **a structural difference is expected and allowed** — say so in the
correspondence proof rather than contorting the guest to imitate it.

**The canonical case is exceptions.** `SpecRef.validate_header` returns
`Except SpecError Unit` and every failed check is a `throw (.invalidBlock …)` —
in `execution-specs` this is a raised `InvalidBlock` that unwinds the stack. The
guest cannot raise. It sets a failure status and branches to an exit, so one
Python construct (`throw` from anywhere in the body) becomes many machine
constructs (a comparison, a branch, a status write, a jump to a shared exit).

⇒ **That divergence is allowed.** What is *not* allowed is losing a conjunct in
the translation: the guest must still reject on exactly the inputs the reference
throws on, and the correspondence proof states that. **Structure-aligned means
the same checks in the same order with the same rejection behaviour — not the
same control-flow primitive.**

The same latitude covers other Python-only mechanisms — dynamic allocation
(lists and dicts become fixed arenas with capacity bounds, and an overflow
becomes an explicit reject), unbounded integers, and garbage collection. In each
case, **document the divergence at the routine's spec and prove the behaviour it
is standing in for**; do not treat the absence of the Python construct as a
licence to drop the check it guarded.

## 4. Wire it into the path that runs — and prove that you did

⚠️ **A new routine that is correct and uncalled reproduces the original defect in
a new place.** After emission, disassemble and confirm the new routine has a call
site on the reachable path from the entry point, and **state the count** in the
PR.

## 5. Prove the correspondence

The deliverable is a whole-routine `cpsTripleWithin` at the routine's
`GuestAddrs` entry whose post is stated **against the `SpecRef` function** —
every conjunct discharged, or explicitly gated.

- ⛔ **Direction matters.** The soundness-critical direction is that the guest
  **rejects everything the reference rejects**; a missing check is a false
  ACCEPT. If only one direction is proved, say which, in the row's gate.
- **Separate input-domain gates from caller-ABI obligations.** A gate that
  excludes real inputs is a restriction; an alignment or buffer-length premise
  discharged at the call site is not. Listing them together makes a row read as
  more restricted than it is.
- **Name the residual.** A `.conditional` row whose gate states exactly what is
  excluded is useful immediately; a row withheld until `.proven` says nothing in
  the meantime.

## 6. Land it with both ledgers

A new spec-bearing routine needs **two** entries, in the same PR:

1. a row in `EvmAsm/Progress/Routines.lean`, and
2. an entry in `scripts/axiom-witness-registry-allow.txt`.

And if the routine was previously allowlisted in
`scripts/registry-coverage-allow.txt`, **delete that line in the same PR** —
`check-registry-coverage` fails on a *stale* entry (allowlisted but no longer a
gap), so rowing without deleting, or deleting without rowing, breaks CI.

**Verify counts by membership, both directions** (`main − PR` and `PR − main`),
not by the totals. A matching total hides a swap.

## 7. The review screen

> **Could this change cause an invalid block to be accepted?**

Every conjunct that rejects today must still reject. **A check that silently
stops running is the failure mode** — and it is not hypothetical: §2 exists
because that is what was found.

---

## Why "unproven code is disposable" is the right default

Preserving unproven behaviour costs alignment and buys nothing verifiable. The
guest's value is what has been proved about it; code with no proof carries no
guarantee to protect, and its structure is the main obstacle to acquiring one.
Rewriting it to mirror the reference converts an unverifiable artifact into a
provable one — which is the only durable direction.
