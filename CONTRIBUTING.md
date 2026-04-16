# Contributing to EvmAsm

Thanks for contributing.

Start with:

- [`README.md`](README.md) for the project overview
- [`AGENTS.md`](AGENTS.md) for build instructions, project structure, and proof guidance
- [`PLAN.md`](PLAN.md) for the current roadmap and task status

Before sending work for review:

- Run `lake build` and confirm it succeeds with no errors and no `sorry`.
- Run `scripts/check-file-size.sh` (or rely on CI) — Lean files under `EvmAsm/Evm64/` have line caps documented in `AGENTS.md` ("File-size guardrail"). Split rather than raise the cap; if a split is genuinely impractical, add a `-- file-size-exception: <reason>` line near the top of the file so reviewers see the exception.
- Avoid leaving `sorry` in finished work unless the change is explicitly meant to preserve partial progress.
- When adding a new `.lean` file, make sure it is imported so that it is included in the default build target.
- Do not add `set_option maxHeartbeats` or `set_option maxRecDepth` to files. These are configured globally in `lakefile.toml`. If a proof times out, restructure it (split into smaller lemmas, add intermediate `have` bindings) instead of raising limits. Timeouts are usually caused by unification issues, not insufficient heartbeats.
- Do not use `native_decide` or `bv_decide`. All proofs must be kernel-checkable. `native_decide` reflects through compiled code, and `bv_decide` dispatches to an external SAT solver and reflects the UNSAT certificate — neither is verified by the kernel. `decide`, `omega`, `bv_omega`, `simp`, and `ext` are all fine (`bv_omega` is `omega` extended with BitVec normalization and is kernel-checkable). Prefer `decide` for concrete decidable propositions.

## Spec and Proof Guidelines

- **No duplicate memory locations in separation-logic assertions.** A `↦ₘ` assertion that mentions the same address twice in the same `**`-chain becomes unusable because separation logic requires disjointness. This rule applies only to `↦ₘ` (and `↦ᵣ`) atoms inside `Assertion` values, not to standalone `isValidDwordAccess` hypotheses (which are pure alignment checks and may legitimately share addresses).
- **Do not existentially quantify results of computation.** Keep computed results concrete in postconditions — existentials hide information that downstream specs need.
- **Avoid excessive `let` bindings before Hoare triples.** Many `let`s followed by a `cpsTriple` or `cpsBranch` conclusion is an anti-pattern that slows elaboration. When unavoidable, bundle the postcondition into an `@[irreducible] def` returning `Assertion` (see the Bundling Postconditions section of [`AGENTS.md`](AGENTS.md)). Pure math theorems (e.g., `fromLimbs`-based conclusions) may use `let` bindings freely for readability.
- **No underscore-prefixed parameters.** If a function parameter is unused, remove it from the signature instead of prefixing with `_`.

## Style Notes

- Keep imports at the top of the file.
- Follow the naming conventions and proof patterns documented in [`AGENTS.md`](AGENTS.md).

## Git Workflow

- Main branch: `main`
- Create feature branches for new work.
- Use meaningful commit messages.

## Licensing

This project is licensed under the terms described in the [`LICENSE`](LICENSE) file. By contributing, you agree that your contributions are licensed under the same terms.
