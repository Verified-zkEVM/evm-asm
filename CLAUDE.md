# CLAUDE.md

See AGENTS.md for full project context, build instructions, and coding patterns.

## PLAN.md Maintenance

Read PLAN.md at the start of each session. Keep it updated as you work:

- **Completed a task/opcode**: Move it to Done, update the status table and counts
- **Discovered new sub-tasks or blockers**: Add them to the relevant phase
- **Added new infrastructure**: Update the Infrastructure section
- **Before committing**: Check if PLAN.md needs updates for the work in this session

## Proof Conventions

- **No `native_decide` or `bv_decide`**: All proofs must be kernel-checkable. Use `decide` for concrete decidable propositions, or `omega`/`simp`/`ext` for bitvector reasoning. `native_decide` bypasses the kernel via code generation, introducing a soundness gap.

## Building a strong grindset

Prefer `grind` over hand-assembled `simp only [...]; bv_omega` chains when performance is comparable. Grind picks up newly-registered facts automatically, so proofs built on top of `@[grind =]` sets survive code churn without per-proof edits. `grind` is kernel-checkable — it is compatible with the `native_decide`/`bv_decide` ban.

### Canonical example: `EvmAsm/Evm64/DivMod/AddrNorm.lean` (issue #263)

Address-arithmetic equalities in DivMod are closed by a `divmod_addr` tactic that wraps grind + a simp fallback. The file is the reference implementation for this pattern.

### Pattern: registering a new grind/simp set

A grindset has three moving parts. Use one of these layouts:

**Grind-only (simplest)** — if you only need `grind` to close goals, skip the simp-attr file:

```lean
namespace MyDomain

@[grind =] theorem foo_eval_0 : foo 0 = bar := by decide
@[grind =] theorem foo_eval_1 : foo 1 = baz := by decide
-- ...

/-- Close a MyDomain equality. -/
macro "my_domain" : tactic => `(tactic| grind)

end MyDomain
```

**Grind + simp set (preferred when you also want `simp only [my_attr]`)** — Lean forbids using an attribute in the file where it is declared, so split into two files:

- `MyDomainAttr.lean`:
    ```lean
    import Mathlib.Tactic.Attr.Register
    register_simp_attr my_domain
    ```
- `MyDomain.lean`:
    ```lean
    import MyDomainAttr

    namespace MyDomain

    @[my_domain, grind =] theorem foo_eval_0 : foo 0 = bar := by decide
    -- ...

    /-- Close a MyDomain equality. Grind first (fastest, most resilient);
        simp+bv_omega as fallback for shapes grind can't close. -/
    macro "my_domain" : tactic =>
      `(tactic| first
        | grind
        | (simp only [my_domain]; bv_omega))

    end MyDomain
    ```

### Rules of thumb

- **Dual-register atomic facts** as `@[my_attr, grind =]` so both `simp only [my_attr]` users and `grind` users see the same vocabulary.
- **Put atomic facts in a sub-namespace** (e.g., `EvmAsm.Evm64.DivMod.AddrNorm`) to avoid colliding with file-private shadows that may already exist in consumer files. `@[grind =]` and `@[my_attr]` work across namespaces, so the tactic macro keeps working without an `open`.
- **Tactic macros are syntactically global** — a `macro "my_domain" : tactic => ...` declaration is usable from any file that imports yours, no `open` needed.
- **Keep the set complete on first landing.** If a new concrete literal turns up later, add it as a one-line `@[my_attr, grind =]` fact — don't scatter inline `show … from by decide` lemmas in proof bodies.
- **Prefer `grind` over `simp+omega` when the timing is within ~1.5×** of each other. Verify with a throwaway benchmark before committing to a large rollout.
- **Don't use `grind` for separation-logic permutation** — that is `xperm`'s job, and grind's congruence reasoning interacts badly with the 30+ atom assertions common in this repo.
- **Don't register broad `@[simp]` on signExtend/shift evaluations.** They are too aggressive for global simp and can derail unrelated proofs. Keep them scoped to a named attribute.

### When opening follow-up issues

New `@[grind =]` sets worth tracking (at minimum): `Rv64` address arithmetic generalizing `bv_addr`, `ByteOps` algebra (`extractByte`/`replaceByte`), register operations (`getReg`/`setReg`/`getPC`/`setPC`), and program composition lemmas (`ofProg_append` and friends). Each one gets its own issue so impact can be measured independently.
