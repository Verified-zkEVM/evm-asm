# Opcode-Subroutine Template

Conventions for implementing a new EVM opcode as a RISC-V subroutine, distilled
from the DivMod build-out (issue #313).

The goal is that each new opcode (SDIV, SMOD, ADDMOD, MULMOD, EXP, …) lands on
this substrate from day one instead of retrofitting after the DivMod-style
file explosion (~39k LOC, >50% of the repo). Every convention below encodes a
lesson that cost a retrofit PR in DivMod — skipping it recreates the tax.

---

## 1. Directory layout

```
EvmAsm/Evm64/<Opcode>/
  Program.lean          -- bytecode + executable tests
  LimbSpec/             -- per-limb + phase specs, split by phase
    PerLimb.lean        -- raw per-limb helpers
    <Phase>.lean        -- phase composites + cascade dispatch (one per phase)
    Branch.lean         -- BEQ/BLTU merge specs shared by multiple phases
  LoopDefs/             -- iteration/postcondition defs (only if looped)
    Iter.lean           -- pure Word/Prop-level iter computations
    Post.lean           -- Assertion-valued postconditions
    Bundle.lean         -- @[irreducible] def-bundled sub-assertions (frames)
  Compose/
    Base.lean           -- shared CodeReq, skipBlock, length lemmas
    Offsets.lean        -- named constants for block-boundary byte offsets
    <Phase>.lean        -- one per phase, parallels LimbSpec/<Phase>
    FullPath.lean       -- Bool-unified, Fin-parametric end-to-end spec
  AddrNorm.lean         -- opcode-specific address grindset
  AddrNormAttr.lean     -- registers the attribute (required in its own file)
  Semantic.lean         -- stack-level spec via evmWordIs
```

Rationale for the splits:
- `LimbSpec/` / `LoopDefs/` / `Compose/` parallel directories keep each layer's
  sub-files aligned — reviewers can locate the phase-A work in all three at a
  glance. (DivMod retrofitted this under issues #261, #312, this file.)
- `AddrNormAttr.lean` must be separate from `AddrNorm.lean`: Lean 4 forbids
  using a `register_simp_attr` in the same file that declares it.

## 2. Required-from-day-one conventions

All of these exist in DivMod today, but as retrofits. Starting them at day one
avoids the cascading rewrite tax.

### 2.1 Unified dispatch first

If the opcode has skip/addback, max/call, taken/not-taken, or any other binary
branch that merges on the same exit PC, ship the Bool-parameterized
postcondition and the dispatching theorem **from day one**.

Do **not** create `<Opcode>Skip.lean` + `<Opcode>Addback.lean` as intermediate
files and then unify later (issues #262, #283 were cleanup passes for this).
The rule:

> One `Bool`/`Fin n` parameter for every binary/finite branch axis. One
> `@[irreducible] def ... Post` per axis combination. One dispatching
> `_spec` theorem with `cases` on the parameter.

### 2.2 MOD-style sibling opcodes

If the opcode has a sibling (SDIV ↔ SMOD like DIV ↔ MOD, MULMOD ↔ ADDMOD in
some splits, …), the two usually differ only in the epilogue. File layout
must make the shared/variable boundary explicit **from the start**:

```
Compose/
  SharedBody.lean       -- specs that work for both siblings
  <Sibling1>Epilogue.lean
  <Sibling2>Epilogue.lean
  <Sibling1>FullPath.lean
  <Sibling2>FullPath.lean
```

DivMod retrofitted this under issue #266; MOD initially had a parallel clone
of every DIV file, which doubled the LOC.

### 2.3 `@[irreducible] def` + `_consequence` for large postconditions

Any postcondition with ≥3 `let` bindings — or any frame with ≥20 atoms —
**must** be wrapped in `@[irreducible] def` with an accompanying `_unfold`
(or `_consequence`) lemma. This is non-negotiable for scaling.

Reasons, both hit during the DivMod build-out:
- Lean's WHNF elaboration at 25+ instruction atoms in a single theorem type
  times out (nested `let` binding substitution is exponential — see
  `AGENTS.md` "Scaling" paragraph).
- `xperm_hyp` is O(n²) in atom count with deep WHNF per pair; >36 atoms
  exceeds 200k heartbeats (issue #265 documents the 51.2M-heartbeat hotspot
  in `Compose/PhaseAB.lean`).

`@[irreducible]` bundling collapses a sub-assertion to a single atom for both
WHNF elaboration and `xperm` purposes. Unfolding happens locally via the
`_unfold` lemma only where needed.

### 2.4 Named block-boundary offsets from day one

Create `Compose/Offsets.lean` with `abbrev` constants for every block's byte
offset **on the first commit that adds a second block**. Do **not** use raw
numeric literals (`base + 448`, `base + 908`) in downstream proofs; always
write `base + <blockName>Off`.

Add `drift_check_*` `example`s to `Compose/Offsets.lean` that tie each offset
to `<prev>Off + 4 * <prev>.length`. When a block grows or shrinks, the
check fails at kernel-check time with a pointer to the stale constant.

Retrofit cost: PR #300 (a one-instruction addition) cascaded into a 43-file,
500+ line diff because the offsets were raw literals (issue #301). Starting
with named constants keeps that change localized to `Offsets.lean`.

### 2.5 Opcode-specific address grindset

Ship `AddrNorm.lean` + `AddrNormAttr.lean` on the **first commit that
introduces a non-trivial address computation**. Register all atomic
`signExtend12` / `<<<` / `BitVec.toNat` evaluations as `@[<opcode>_addr, grind =]`
so new concrete offsets are one line and every downstream proof picks them up.

DivMod had 112 one-off address-equality lemmas before `divmod_addr` was
introduced (issue #263).

### 2.6 Validity bundle

If the opcode has any `isValidDwordAccess` side-conditions, bundle them into
a `structure <Opcode>Valid` from day one. Threading 20+ individual validity
hypotheses through every composition level is a retrofit tax (issue #264).

---

## 3. Pre-SDIV / pre-ADDMOD / pre-EXP audit

Before starting the next opcode, checkpoint:

1. `GRIND.md` Phase 3 (`rv64_addr` common base) landed, or explicitly
   descoped, so the opcode's `AddrNorm` extends a shared base rather than
   re-deriving it.
2. Issue #266 (MOD factoring) landed so the "sign-sibling factors as a
   post-rewrite" pattern is demonstrated end-to-end.
3. Issues #262 / #283 (Bool / Fin unification) landed so unified dispatch
   is the known default.
4. Issue #312 (monolithic-file splits) continued so the new opcode's file
   sizes match the `LoopDefs/{Iter,Post,Bundle}` target shape, not DivMod's
   legacy 3k-line files.

Starting a new opcode before those land replicates the DivMod retrofit tax.

---

## 4. Review checklist

For PRs that introduce a new opcode subtree:

- [ ] `Compose/Offsets.lean` present with `drift_check_*` examples.
- [ ] `AddrNormAttr.lean` and `AddrNorm.lean` present, with the
  `<opcode>_addr` attribute registered and at least one `@[grind =]` lemma.
- [ ] No `<Opcode>Skip.lean` / `<Opcode>Addback.lean` split — branches are
  Bool-dispatched.
- [ ] Every postcondition with ≥3 `let` bindings is `@[irreducible] def`.
- [ ] Every frame with >20 atoms is bundled through an `@[irreducible] def`.
- [ ] If the opcode has a sibling (SMOD, ADDMOD, …), shared body / per-sibling
  epilogue layout is present from the first PR.
- [ ] Validity hypotheses are bundled into a `structure <Opcode>Valid`.

Refs: #313, #261, #262, #263, #264, #265, #266, #283, #301, #312.
