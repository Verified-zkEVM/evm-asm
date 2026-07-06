# Contributing to EvmAsm

Thanks for contributing.

Start with:

- [`README.md`](README.md) for the project overview
- [`AGENTS.md`](AGENTS.md) for build instructions, project structure, and proof guidance
- [`PLAN.md`](PLAN.md) for the current roadmap and task status
- [`docs/notable-specs.md`](docs/notable-specs.md) for an index of notable proven
  specifications (per-opcode stack specs, EvmWord correctness theorems,
  RLP/ByteOps/calling-convention helpers) with permalinks to the exact theorem
  statements at a pinned commit. Use it to find a spec without grepping. The
  index is refreshed whenever a `#61`-class umbrella issue closes or quarterly,
  whichever comes first; the bottom of that page documents the refresh
  procedure.

Before sending work for review:

- Run `lake build` and confirm it succeeds with no errors and no `sorry`.
- Run `scripts/check-file-size.sh` (or rely on CI) — Lean files under `EvmAsm/Evm64/` have line caps documented in `AGENTS.md` ("File-size guardrail"). Split rather than raise the cap; if a split is genuinely impractical, add a `-- file-size-exception: <reason>` line near the top of the file so reviewers see the exception.
- Avoid leaving `sorry` in finished work unless the change is explicitly meant to preserve partial progress.
- When adding a new `.lean` file, make sure it is imported so that it is included in the default build target.
- Do not add `set_option maxHeartbeats` or `set_option maxRecDepth` to files. These are configured globally in `lakefile.toml`. If a proof times out, restructure it (split into smaller lemmas, add intermediate `have` bindings) instead of raising limits. Timeouts are usually caused by unification issues, not insufficient heartbeats.
- Do not use `native_decide` or `bv_decide` (or any other TCB-expanding tactic). All proofs must be kernel-checkable. `native_decide` reflects through compiled code, and `bv_decide` dispatches to an external SAT solver and reflects the certificate through a native-evaluated checker — both seal their result behind a native-compiler trust axiom (`Lean.ofReduceBool` / `Lean.trustCompiler`) rather than a kernel-checked proof term. Both are fully eliminated (`native_decide` 206→0, `bv_decide` 290→0) and the trusted base is now only the three classical axioms. `decide`, `omega`, `bv_omega`, `simp`, `ext`, and `BitVec.eq_of_getLsbD_eq` are all fine (`bv_omega` is `omega` extended with BitVec normalization and is kernel-checkable; `decide` is fast even on concrete 256-bit `BitVec` goals because the kernel's `Nat` is GMP-backed). Prefer `decide` for concrete decidable propositions.
  - **CI enforces this two ways** (both run on every PR): `scripts/check-forbidden-tactics.sh` fails on any `bv_decide`/`native_decide` *tactic invocation* in `EvmAsm/**.lean` (mention them only inside `` `backticks` ``); `scripts/check-axioms.sh` is the kernel-truth backstop, rejecting any non-classical *axiom* (`sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, `bv_decide`/`native_decide` trust axioms). Run `scripts/check-forbidden-tactics.sh` locally before pushing.

## Spec and Proof Guidelines

- **No duplicate memory locations in separation-logic assertions.** A `↦ₘ` assertion that mentions the same address twice in the same `**`-chain becomes unusable because separation logic requires disjointness. This rule applies only to `↦ₘ` (and `↦ᵣ`) atoms inside `Assertion` values, not to standalone `isValidDwordAccess` hypotheses (which are pure alignment checks and may legitimately share addresses).
- **Do not existentially quantify results of computation.** Keep computed results concrete in postconditions — existentials hide information that downstream specs need.
- **Avoid excessive `let` bindings before Hoare triples.** Many `let`s followed by a `cpsTriple` or `cpsBranch` conclusion is an anti-pattern that slows elaboration. When unavoidable, bundle the postcondition into an `@[irreducible] def` returning `Assertion` (see the Bundling Postconditions section of [`AGENTS.md`](AGENTS.md)). Pure math theorems (e.g., `fromLimbs`-based conclusions) may use `let` bindings freely for readability.
- **No underscore-prefixed parameters.** If a function parameter is unused, remove it from the signature instead of prefixing with `_`.

## Style Notes

- Keep imports at the top of the file.
- Follow the naming conventions and proof patterns documented in [`AGENTS.md`](AGENTS.md).

### Naming conventions (Mathlib-aligned)

We follow the [Mathlib4 naming guide](https://leanprover-community.github.io/contribute/naming.html#capitalization). Summary:

1. **Terms of `Prop`s** (proofs, theorem names) — `snake_case`. e.g. `add_comm`, `evm_div_spec`.
2. **`Prop`s and `Type`s** (inductive types, structures, classes) — `UpperCamelCase`. e.g. `CodeReq`, `PartialState`.
3. **Functions** — named like their return value (so `Prop`-returning functions are `snake_case`, `Type`-returning functions are `UpperCamelCase`).
4. **All other terms of `Type`s** — `lowerCamelCase`. e.g. `clzResult`, `loopBodyOff`.
5. Inside a `snake_case` name, an `UpperCamelCase` segment appears in `lowerCamelCase`. e.g. `List.bitVec_cons`, not `List.BitVec_cons`.
6. Acronyms are lowercased/uppercased as a group (`LE`, `le`, not `lE`).

**Local variables inside proofs** (bound by `have`, `intro`, `let`) follow the same rules by extension:

- Proof/hypothesis names (most `have`/`intro`) — `snake_case` (rule 1). Short forms like `h`, `hx`, `h1`, `hab` are standard. Descriptive forms like `h_carry_pos`, `add_lt_aux` are fine.
- `let`-bound values of `Type`s — `lowerCamelCase` (rule 4). e.g. `let midPoint := ...`, `let carryIn := ...`. A Word-valued local called `carryIn` is a Type term (rule 4), not a Prop term (rule 1) — even though the underlying computation is carry arithmetic.

## Git Workflow

- Main branch: `main`
- Create feature branches for new work.
- Use meaningful commit messages.

## Licensing

This project is licensed under the terms described in the [`LICENSE`](LICENSE) file. By contributing, you agree that your contributions are licensed under the same terms.
