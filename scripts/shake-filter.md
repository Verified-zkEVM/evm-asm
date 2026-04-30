# shake-filter — known false-positive filter for `lake exe shake`

`lake exe shake EvmAsm` produces a long list of "remove this import"
suggestions. Past slices of #1045 repeatedly hit the same problem: many
of those suggestions are wrong because shake does not see lemmas /
notations / spec-database entries that are referenced indirectly via
attributes or tactic macros.

`scripts/shake-filter.py` post-processes shake's output and drops every
file block whose source contains a documented false-positive marker
(custom simp attributes, `runBlock` / `xperm` / `xsimp` / `seqFrame`
tactic invocations, `@[spec_gen_*]` attribute use, `Word` notation, etc.).

## Usage

```bash
lake build
lake exe shake EvmAsm 2>/dev/null | scripts/shake-filter.py
```

To inspect what the filter dropped:

```bash
lake exe shake EvmAsm 2>/dev/null | scripts/shake-filter.py --show-dropped | less
```

Filter stats are printed to stderr (`N kept, M dropped`).

## What gets dropped, and why

See the `MARKERS` list at the top of `shake-filter.py` — each marker is
paired with a one-line reason. The categories are:

1. **Spec-database tactics** — `runBlock`, `xperm` / `xperm_hyp`,
   `xcancel`, `xsimp`, `seqFrame`, `liftSpec`. These tactics elaborate
   to `simp` / `grind` calls over an attribute-driven set of lemmas
   (`@[spec_gen]`, `@[spec_gen_*]`). The imports that *register* those
   lemmas have no direct reference inside the consumer file, so shake
   flags them as unused.

2. **`@[spec_gen_*]` declarations** — files that declare specs locally
   are themselves consumed by attribute, not by direct reference. Shake
   does not see the downstream attribute lookup.

3. **`*_spec_gen_within` / `*_spec_within` lookup names** — common spec
   identifiers used in `CallingConvention.lean` and similar files; the
   backing lemma is loaded via a `simp` / `grind` set.

4. **Custom simp attributes** — `rv64_addr`, `divmod_addr`, `reg_ops`,
   `byte_alg`. Each is registered in a `*Attr.lean` file and consumed by
   `simp [attr_name]` elsewhere; shake doesn't track this.

5. **`Word` notation** — `notation "Word" => BitVec 64` lives in
   `EvmAsm.Rv64.Basic`. Files that only mention `Word` look unrelated
   to that import.

## Verifying false-positive drops

Past investigations (see `evm-asm-o6y`, `evm-asm-pic`) confirmed that
the following files produced ZERO genuine shake suggestions despite
appearing prominently in raw output:

- `EvmAsm/Evm64/CallingConvention.lean`
- `EvmAsm/Evm64/DivMod/Spec.lean`
- `EvmAsm/Evm64/DivMod/SpecCall.lean`
- `EvmAsm/Rv64/SyscallSpecs.lean`
- `EvmAsm/Rv64/InstructionSpecs.lean`

The filter drops all five. (One survivor — `Evm64/CallingConvention.lean` —
landed under PR #1481 which removes its single genuinely-unused import.)

## Caveats

The filter is **conservative on the drop side**: it discards any file
matching a marker, even when shake's suggestion happens to be correct.
That is the right tradeoff while we still have hundreds of false
positives — pruning the noise gives slicers a high-signal worklist.
Expand the audit later by removing markers as we gain confidence that
shake is correct in their presence.

The filter does **not** modify shake itself; it operates on stdout. To
re-run shake from scratch:

```bash
lake clean && lake build && lake exe shake EvmAsm 2>/dev/null \
    | scripts/shake-filter.py | tee shake-real.txt
```
