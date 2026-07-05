# Replacing an unverified program with a verified one — strategy

The high-level decision guide for any bead of the shape "verify `<routine>`"
or "swap `<routine>` for a verified implementation". The *mechanics* (class
table, scaffold, VC closers, deploy gates) live in
[`port-playbook.md`](port-playbook.md) — read that when you start typing.
Read THIS page when you are deciding **what to prove, against what interface,
and what to do when the pieces don't fit**.

## 1. The drop-in principle

**Byte-sequence equality with the old unverified routine is NOT required.**
What must be preserved is the routine's *observable contract at its call
boundary* — the replacement must be a **functional drop-in**:

| Must be preserved | Why |
|---|---|
| ABI: argument/return registers, status-code conventions | callers are unverified asm that reads exactly these |
| Clobber set ⊆ the documented convention for its class (leaf vs non-leaf; caller-saved x5–x7/x28–x31, dispatcher x14–x19 conventions, callee-saved discipline) | a wider clobber silently corrupts an unverified caller |
| Memory footprint: which regions/cells it reads and writes — including its **static `.data` scratch cells** | anything it touches that the old one didn't can break a phase/aliasing assumption |
| Termination/halt behavior and any exit ECALLs | the guest's control structure is straight-line composition |
| Link-layout constraints *only where callers bake them in*: entry symbol name; nothing else. Function length and internal layout are free to change — `GuestAddrs.lean` and `symbol-addresses.tsv` are **regenerated**, not preserved (the `.9.5` regen pattern) | |

What is explicitly FREE to change: instruction sequence, register allocation
inside the clobber budget, loop shape (a `whileBreak` scan may become a
canonical `while`, cf. bead `.70.2`), internal scratch layout, code length.
Exemplars of landed drop-ins: the bn254 compare-leaves replacement
(PR #9843, `port/bn254-cmp-leaves-dropin`) and the `.12.10` re-emit leaves.

**The two byte-tie strategies** (pick one per PR, consciously):

1. **Byte-identity** (`<name>Function_eq_prog` `rfl` drift guards): you did NOT
   change the emitted routine; you verified a `Program` conversion of the
   exact existing bytes. Cheap gate, no A/B needed. This is the default for
   pure verification beads.
2. **Re-emit** (true drop-in): the emitted bytes change. Then the gate is the
   full emit pipeline: guest re-emit, `scripts/check-region-map.sh`,
   link-layout regen (`gen-symbol-addresses.py`, `GuestAddrs`), and an
   **EEST A/B** (sasm-howto §7.6) — failures acceptable only if identical on
   both legs. #9852 (the frame-arena resize) is the maximal example of this
   path. Never mix strategies silently: a "verification" PR that quietly
   re-emits has skipped the A/B gate.

## 2. How to formulate the specification

The binding rule is already in AGENTS.md ("Spec design — keep preconditions
static; put outcomes in the postcondition"). Strategy on top of it:

- **State the footprint in the assertion vocabulary, not raw cells.** Frame
  against `evmStackIs`, `evmMemoryIs`, `storageLogIs`, `accountRlpIs`,
  `mptNodeIs`/`nodeDbIs`, `witnessSectionIs`/`codeDbIs`, `bytesRegion` — not
  ad-hoc `↦ₘ` chains. A spec stated in raw dwords is *consumable only by the
  session that wrote it*; a spec stated in the vocabulary is consumable by
  every later composition (and by the refinement map,
  `docs/4ch8f-slstate-specref-correspondence.md`). If the vocabulary lacks
  your structure, adding the assertion (with a faithfulness tie) is part of
  the job — copy the pattern of `EvmAsm/Evm64/StateAssertions.lean`.
  Historical warning: the MLOAD/MSTORE stack specs were first stated against
  raw dword windows and had to be *reframed afterwards*
  (`Evm64/MLoad/MemoryRegionStackSpec.lean`) — state new specs at the right
  altitude the first time.
- **Value-carrying assertions + pure WF.** Assertions carry their contents as
  parameters (`SepLogic.assertPure` shape: `fun ps => WF ∧ region ps`), so
  the postcondition is a *pure function of the input parameters* — e.g.
  "pushes `evmMemoryReadWord contents offset`", not "pushes whatever was in
  memory". That pure function should be an **executable spec-level mirror**
  (decode/lookup/replay), ideally tied to `SpecRef` (`decode_account_from_leaf`,
  `build_node_db`, …) — then the routine spec and the refinement compose for
  free. `#guard` the mirror on concrete vectors.
- **All outcomes, one theorem.** Parse-fail / miss / conservative-failure
  paths are part of the contract: model them as postcondition disjuncts with
  static guards (the `ContentToU256Be` shape), never as preconditions that
  assume success. A routine's *conservative-failure path is load-bearing*
  (e.g. the witness-index builder failing over capacity is what makes the
  uncapped linear fallback reachable).
- **Own what you clobber.** Scratch registers and static `.data` scratch
  cells (`mnk_dummy_offset`-style) appear in the pre as owned resources and
  in the post either restored or existentially havoc'd (`memOwn`/`aExists`) —
  fabricating concrete final values for scratch makes the spec unprovable or,
  worse, over-specified so that a future re-emit breaks it.
- **State the honest domain.** If the routine is only *instantiable* on a
  sub-domain, gate the theorem on it and say so — do not force a general
  statement whose extra cases have unsatisfiable preconditions. (Lesson: the
  unaligned MLOAD/MSTORE window specs force adjacent limbs to share a dword,
  so the separated precondition is satisfiable only for the aligned case;
  the honest spec is the aligned one, recorded as such.) The `conditional`
  tier of `Progress.lean` exists for exactly this — with a
  `…_precondition_reachable` cover lemma to prove the gate is non-vacuous.
- **Non-vacuity is a deliverable.** Provide the satisfiability witness for
  your pre (the vacuity-guard section of `top-theorem-ledger.md`). Reviewers
  reject triples whose pre can't be inhabited.

## 3. When the callee doesn't expose enough

You are composing routine B, and verified callee A's spec doesn't give you
what B's proof needs. The escalation ladder, cheapest first — **do not skip
to the bottom**:

1. **A bridging lemma next to A.** Often A's spec is fine and you need a pure
   consequence of its postcondition (a fold of its output bytes, an algebraic
   restatement). Add the lemma in A's module; don't touch the triple.
2. **A variant theorem for A** (additive). A's proof usually supports a
   differently-shaped conclusion — a folded post, a mid-chain `_right`
   rewrite form, an instantiated corollary. Add `A_spec_within_<shape>`
   alongside; never *weaken or reshape the existing theorem* (other callers
   and the witness registry depend on it).
3. **Reframe A against the assertion vocabulary.** If A predates the
   vocabulary and frames raw cells, write the reframed theorem by *consuming*
   the proven one (peel the assertion into A's raw footprint, run A's spec,
   fold back). This is the `evm_mload_stack_spec_within_evmMemoryIs` pattern
   — the reframe is itself the assertion's honesty gate.
4. **Strengthen A's spec** (re-prove with a stronger post). Needed when A's
   post genuinely forgets information B needs (e.g. A returns a pointer but
   its spec doesn't relate it to the region — the `(offset,len)`-view shape
   should use a `matchesSection`-style relation, not a bare word). This costs
   re-proving A; budget it as its own bead if nontrivial.
5. **Change A's code** (true drop-in replacement, §1 path 2). Justified when
   A's *interface* is the problem: it doesn't return a fact it inescapably
   computed (a length, a status), or its contract is unspecifiable as-is
   (multi-exit tails — cf. the `.10.3` set-flag+ret restructure that made all
   256 handlers satisfy one return contract). Full emit gates apply.
6. **STOP and file a bug.** If B's correctness *requires* something A cannot
   provide because the guest is wrong — A reads garbage, relies on
   zero-init that aliasing violates, its output is clobbered before B reads
   it — that is not a proof obstacle. Do not prove around it, do not weaken
   B's statement to avoid it. File the bead with the concrete failure
   scenario (the `.72`/`.73` audit findings are the template) and wire it as
   a blocker of the affected beads.

Two special cases that look like "not enough" but aren't:

- **Global aliasing/phase facts** (call-frame arena unions): never assert
  disjointness that the physical layout doesn't provide. Consume the phase
  views (`Codegen/CallFramePhase.lean`, `CallFrameWindows.lean`); the havoc
  on view switches is the guarantee. If your proof wants to carry a value
  across a phase switch, that is finding a bug, not missing a lemma.
- **Link-layout facts** (absolute addresses, section extents): these come
  from `RegionMap.lean` + the ELF drift guard, never from hardcoding. If A's
  spec pins an address B needs symbolic, parametrize (the assertions are
  base-parametrized for exactly this reason).

## 4. Review expectations for a replacement PR

What a reviewer will check (be ahead of it):

- Which byte-tie strategy (§1) the PR uses, stated explicitly; A/B evidence
  present iff re-emit.
- The spec's pre is static + satisfiable; outcomes are disjunctive; the
  domain restriction (if any) is honest and registered at the right
  `Progress.lean` tier with witnesses.
- The footprint is complete (including static scratch) and stated in the
  vocabulary; nothing in the pre pre-decides a branch.
- No existing theorem was weakened or reshaped (statement-tamper check);
  strengthenings are additive.
- Blockers honored: if the routine sits behind an open bug bead (`.72`,
  `.73` class), the PR either fixes it first or is re-scoped.
