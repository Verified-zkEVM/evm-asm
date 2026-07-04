# Review playbook — how to review a 4ch8f PR

**Audience**: the agent reviewing any PR in this repo. The review's job is NOT
to re-run CI (it runs build, tactic/TCB scans, axiom audit of registered
witnesses, layering, region-map, etc. — full list in
`docs/agents/roadmap-4ch8f.md` §3). The review's job is (a) the gates CI does
not run, and (b) **adversarial reading of statements** — every hole listed in
§3 below was found in review, in this repo, after the author believed the work
was done.

## 1. Per-PR-type checklist (gates CI does not run)

**Lean-proof PR** (new specs/theorems):
1. `#print axioms <FULLY.QUALIFIED.name>` yourself on the headline theorems —
   expect exactly `[propext, Classical.choice, Quot.sound]` (or fewer). Do not
   trust the PR body; namespaces have tripped this before.
2. Read every `def …Pre`/`…Post`/spec statement with §2's checklist.
3. `scripts/port-check.sh <module>` where the module is a port.

**Conversion PR** (emitted strings / `_prog`s):
1. `bash scripts/check-asm-to-program.sh` → CLEAN over the full manifest.
2. Whole-guest LINKED `.text` byte-identity vs merge-base — build both sides
   (`lake exe codegen --program stateless_guest --halt linux93 -o …`;
   `objcopy -O binary -j .text`; `cmp`). Comparing unlinked `.s` is INVALID
   (symbolic `la` assembles to zeroed relocations).
3. Run ≥1 probe the author did NOT run, from a family the PR touches.
4. `GuestAddrs.lean` diff purely additive (0 deletions) or absent — unless the
   PR is itself a regen.
5. Grep added def strings for baked immediates (`auipc`, `%pcrel`,
   `la x, 0x…`) — link-dependent operands must stay symbolic in emission
   views (the #9720 multi-image lesson).

**Guest-byte-changing PR** (fixes/restructures):
1. The PR must carry its own layout regen (region-map GREEN in CI now, but
   verify `check-asm-to-program` CLEAN too — GuestAddrs/TSV can desync, §3.6).
2. EEST parity: `scripts/codegen-eest-stateless-check.sh` A/B vs base —
   identical pass/fail sets, or strictly-better with flipped cases named.
3. The `.s` diff vs base contains ONLY the advertised change.
4. Probes covering the changed paths — including one that FAILS on base if the
   PR fixes a behavior bug (a fix without a base-failing test is unverified).

**Layout-metadata regen PR**:
1. `check-region-map.sh` GREEN, `check-asm-to-program.sh` CLEAN, guest bytes
   UNCHANGED (byte-identity vs base must hold — metadata never moves bytes).
2. Merge-order awareness: such PRs race every byte-changing merge. Merge
   promptly; conflicts are resolved by RE-RUNNING the regen on the merged tree
   (take either side textually first), never by textual merge.

**Docs/bead-only PR**: spot-check citations (file:line drift is common —
measurements taken pre-merge of a rewriting wave go stale); reproduce at least
one load-bearing measurement independently.

## 2. Adversarial statement-reading checklist

For every spec/postcondition/Prop in the PR, ask:

1. **∃-escape**: does the post existentially quantify something the routine
   determines (a state, an output buffer, a length)? If the prover picks the
   witness, can it pick a degenerate one (`[]`, over-long, wrong-but-undecodable)?
   Fixed lengths and function-of-snapshot posts are the antidotes.
2. **Vacuity, pre side**: can the precondition be unsatisfiable (a wrong
   framing, contradictory pins)? For framing bundles demand a satisfiability
   witness (`scratch_sat` pattern).
3. **Vacuity, provability side**: can the triple be discharged without the
   intended work (does the exhausted/cap VC actually depend on the loop
   body's charge? would the proof fail if the body's key instruction were
   deleted)?
4. **Resource accounting**: does the postcondition give every entry-owned
   resource a home (residue slot)? A post owning less than the pre is
   unprovable; a post letting residue absorb the OBSERVED region is vacuous.
5. **Spec-shaped restatement**: is the post the actual mathematical claim
   (`Nat.pow`, `List.reverse`, the SpecRef function) or a ladder/loop-shaped
   restatement a wrong implementation could satisfy? Guard bridges with
   kernel KATs where cheap.
6. **Weakening under pressure**: `take`-truncations, `getD` defaults, dropped
   bound checks — each is a place a wrong input pins WRONG values instead of
   being unsatisfiable. Demand the length/bounds invariant.
7. **Convention over-constraint**: does a precondition assert something the
   real host/machine does not guarantee (meta bytes zero, unaliased operands
   the hardware allows aliased)? Over-constrained pres silently narrow the
   theorem's applicability.

## 3. The known-hole catalog (all real, all caught in review here)

1. **∃-out decode vacuity** — post `∃ out, bytesRegion … out ∧ (decode out
   claims valid → …)` with no length pin: prover picks `out = []` (resource
   slides into residue) or an over-long undecodable `out`; claim vacuous even
   on accept runs. Fix: pin `out.length`, state claims on fixed offsets.
2. **Missing residue slot** — halt-triple post owning only the observation
   window while the pre owned all scratch: unprovable. Fix: `GuestFraming`
   with a residue conjunct.
3. **Multi-image baked immediates** — a def emitted into N linked images had
   guest-layout `la`/`jal` immediates baked in; every other image broke.
   Emission views keep link-dependent operands symbolic; only `_prog`
   verification views pin.
4. **Verbatim-block split** — a generated conversion block split across two
   files defeated the source-drift gate. A block moves as a unit; the
   MANIFEST points at the file that holds ALL of it.
5. **Differential-testing gap** — the MODEXP `exp==0 ∧ modulus==1 → 1` bug
   survived months of probes: differential testing is not a terminal
   verification tier for math kernels.
6. **GuestAddrs/TSV desync** — the two regen outputs committed from different
   builds (mid-work main merge between them): `check-region-map` green while
   `check-asm-to-program` red. Always regen BOTH after the LAST merge.
7. **Layout-snapshot race** — a regen measured on a stale base fails CI once
   main moves (CI tests the MERGE). Re-regen after merging main; merge such
   PRs promptly.
8. **Stale citations** — inventory measured pre-wave; line refs and status
   columns drifted after the wave rewrote the cited files. Pin a provenance
   commit in measurement docs.
9. **`take`-truncating encodings** — a stack serialization that truncates
   over-deep stacks pins wrong bytes instead of being unsatisfiable (a
   soundness trap if it graduates from placeholder to real relation). Carry
   the capacity invariant.
10. **Over-constrained host pre** — asserting the ZisK meta dwords are zero
    would make the top theorem inapplicable to real hosts. Leave unread host
    bytes in the frame.

## 4. Review output conventions

- Verify claims INDEPENDENTLY (re-derive the spec corner from
  `tests-zkevm@v0.4.0`, re-run the probe, re-compute the constant) — author
  assertions are hypotheses. Refuting a claimed bug is a successful review.
- Post one comment: what you verified (with the exact commands/theorem names),
  defects found (severity-ordered), non-blocking notes routed to the consumer
  bead (`bd update <bead> --append-notes …`) so the knowledge lands where the
  next session will look.
- Small mechanical defects in an idle author's PR (a missed regen, a stale
  sync): fix and push to the PR branch yourself, and say so in the comment —
  unless the PR is near-merge (then a fresh stacked branch; automerge can
  orphan late pushes).
- If two open PRs rewrite the same generated files, post the merge-order plan
  explicitly on both.
