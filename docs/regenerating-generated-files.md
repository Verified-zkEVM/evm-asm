# Regenerating the generated layout files

Several checked-in files are **generated from the linked guest ELF** and must be regenerated
after any change that alters the guest's emitted bytes or layout (a re-emit, a new/removed
routine, a `.text`/`.data` size change). Editing them by hand is wrong — each carries a
`GENERATED — do not edit` header.

The generated files, what regenerates each, and what it depends on:

| File | Regenerate with | Derived from |
|---|---|---|
| `scripts/asm-fixtures/symbol-addresses.tsv` | `scripts/gen-symbol-addresses.py --build` | the linked ELF (`lake exe codegen`) |
| `EvmAsm/Codegen/GuestAddrs.lean` | `python3 scripts/asm_to_program.py guest-addrs` | the TSV above |
| `EvmAsm/Codegen/RegionMapLinkPins.lean` | `python3 scripts/gen-region-map-link-pins.py` | the linked ELF (class-A sizes + three BSS bases; #11230) |
| `EvmAsm/Codegen/Proofs/GuestImageEntries.lean` | `python3 scripts/guest_image_coverage.py --emit-lean` | `GuestAddrs` + the linked function set |

`RegionMap.lean` re-exports class-A pins from `RegionMapLinkPins` as
`abbrev name := RegionMapLinkPins.name` — do **not** hand-edit sizes or the
three BSS bases there, and do **not** turn those `abbrev`s back into
`def … := 0x…` during a layout repin. Class A hex lives **only** in
`RegionMapLinkPins.lean` (generator output). A merge that drops the re-export
while leaving LinkPins current is a silent two-modules-one-fact regression
(`check-region-map.sh` greps the `abbrev` form; #11282). Class B stable bases
(INPUT/OUTPUT/zisk/stack/section starts/schemeA) stay typed in RegionMap with
a per-def why. `GuestImage.lean` unfolds LinkPins via `simp`/`decide` — no
hand `.bss` end hex.

## Prerequisites

The RISC-V toolchain (`riscv64-unknown-elf-*`) and `readelf` must be installed — the first step
shells out to `lake exe codegen` to (re)link the ELF. Without the toolchain the regen cannot run
(and the guard scripts skip with exit 0 rather than verifying).

## Procedure (run in this order — later steps consume earlier outputs)

```bash
# 1. Relink the ELF and regenerate the linker-facts snapshot (TSV).
#    Builds stateless_guest + runtime_dispatcher via `lake exe codegen ... --halt linux93`.
scripts/gen-symbol-addresses.py --build

# 2. Regenerate GuestAddrs.lean from the fresh TSV (one Nat per referenced symbol).
python3 scripts/asm_to_program.py guest-addrs

# 3. Regenerate the guest-image entry list.
python3 scripts/guest_image_coverage.py --emit-lean

# 4. Derive class-A RegionMap pins from the linked ELF (#11230).
python3 scripts/gen-region-map-link-pins.py

# 5. Repeat steps 1-4 until a complete pass makes no changes. Updating
#    RegionMapLinkPins.textSizeBytes (re-exported as RegionMap.textSizeBytes)
#    can itself change the emitted image, so a one-pass relink is not a
#    convergence check. The *second* gen-region-map-link-pins pass must be a
#    NO-OP (diff empty) or stop and investigate.
```

## Layout invariants during a regen

- **Reach a fixed point.** `textSizeBytes` is an input to emission as well as a
  record of it. After regenerating LinkPins, relink and repeat the complete
  procedure until a further pass changes neither the generated files nor the
  reported section sizes. Do not trust a one-pass repin.
- **Keep `.data` fixed.** Its base is `0xa3000000`; growth shifts downstream
  data symbols and breaks the hard `rfl` address proofs. In particular,
  `GuestAddrs.bnf_le_a` must remain `2734690016` (`0xa3000ee0`). A changed
  value is a layout regression to investigate, not an address to accept.
- **Do not hand-edit GuestImage `.bss` end hex.** `guestScratch_sat` unfolds
  `RegionMap.dataSizeBytes` / `bssSizeBytes` from LinkPins (#11230). A stale
  LinkPins file fails `check-region-map.sh` (pins vs check-time ELF) and/or
  `gen-region-map-link-pins.py --check`.
- **Guard contract.** `check-region-map.sh` compares LinkPins (regen-time ELF
  reading) to readelf/nm of the ELF built at *check* time — two independent
  readings of two artefacts. Never compare a generated file only to itself.

## Verify

```bash
scripts/check-asm-to-program.sh   # byte-tie: emitted _prog bytes vs GuestAddrs/TSV (also runs check-guest-addrs)
scripts/check-region-map.sh       # Lean RegionMap vs ELF section sizes / bases
lake build                        # the Lean side (GuestImage etc.) must still compile
```

`check-asm-to-program.sh` and `check-region-map.sh` are the drift guards; if either fails after a
guest change, a regen step above was missed or RegionMap's sizes are stale.

## Notes

- **`scripts/regen-cycle.sh` was removed** (#10746). It hardcoded a dead scratch path and
  invoked an uncommitted helper (`remap_sasm.py`, which exists in no tree) — and with a
  missing scratch directory its clean-test `[ ! -s "$S/failpass.txt" ]` was satisfied by the
  *absence* of the file it had failed to write, so it printed `REGEN_CLEAN pass=1` and exited
  0 regardless of actual drift. Use the commands above.
- Step 2 (`GuestAddrs.lean`) is the file that churns on essentially every layout change: the
  per-function `_prog` defs reference its constants by name (`AsmReloc.{laHi,laLo,jalOff}`), so a
  size change only requires regenerating the TSV + `GuestAddrs.lean`, never the hundreds of
  `_prog`s.
- See also `docs/4ch8f-region-map.md` §5 ("Drift handling") for the RegionMap/TSV rationale and
  the STABLE-vs-LINK_DEPENDENT symbol classification.

## Troubleshooting: bootstrapping past a stale-layout build failure

Merging two address-shifting branches (or resolving a merge conflict on the generated files
above with a placeholder) can leave the tree in a state where `lake build` fails at
`EvmAsm/Codegen/Proofs/GuestImage.lean`'s `guestImageEntries_extentsOk : ... := by decide`, because
`guestImageEntries` (built from the stale/placeholder `GuestAddrs.lean`) has entries that overlap
or are out of order. This is a genuine chicken-and-egg: step 1 of the procedure above
(`gen-symbol-addresses.py --build`) needs to build and relink `lake exe codegen`, but `Main.lean`
(the codegen executable's root file) imports the 20 `EvmAsm.Codegen.Proofs.*` modules — including
`GuestImage` — purely to force them to be *checked* as part of the exe build. With a false
`extentsOk`, that import chain fails to typecheck, so the exe cannot build, so step 1 cannot run,
so the addresses that would fix `extentsOk` can never be produced. Loosening
`RegionMap.textSizeBytes` does **not** help: `CodeReq.extentsOkFrom` (`EvmAsm/Rv64/CodeReqExtents.lean`)
folds over the entry list checking each entry's address against the *end of the previous entry*,
only checking the final `hi` bound once at the very end — so the failure is almost always an
internal ordering/overlap violation between two entries, not an upper-bound issue.

The escape hatch: the codegen exe's actual emitter logic (`Cli`/`Driver`/`Emit`/`Layout`/
`Programs.Registry`/`RegionMap`) does not need any of the `Proofs.*` modules to run — they are
imported into `Main.lean` only so `lake build`/`lake exe codegen` also checks them as a side
effect. Temporarily breaking that forced-check import chain lets the exe build and relink even
while `GuestImage`'s `decide` is still false:

```bash
# 1. Comment out the twenty `import EvmAsm.Codegen.Proofs.*` lines in Main.lean
#    (repo root) — everything else in Main.lean is untouched.

# 2. Run the full 4-step regen from the "Procedure" section above against this
#    tree (steps 1-4: relink, GuestAddrs.lean, GuestImageEntries.lean, RegionMap sizes).

# 3. Restore Main.lean (git checkout -- Main.lean) — the imports must come back
#    before committing; the exe does not need them, but everything else that
#    imports Main's proof surface does.

# 4. Full `lake build`. `extentsOkFrom` now decides true because the addresses are
#    correct — this is real progress, not a bypass.
```

This is fully revertible and touches no proof: `Main.lean` ends up byte-identical to its
pre-bootstrap state, and only address literals / generated doc counts (`GuestAddrs.lean`,
`RegionMap.lean`, the TSV) change. `scripts/check-forbidden-tactics.sh` and
`scripts/check-axioms.sh` stay clean throughout — no `sorry`, no `native_decide`/`bv_decide`, no
weakened statement. If conflict markers from a merge are also present in the four generated files,
seed them from the side with the superset of symbols (normally `origin/main`), rather than
reflexively taking `--ours`, so the tree can build far enough to run step 1. In one incident an
`--ours` placeholder lacked `block_access_list_hash_core` and prevented codegen from building.
The subsequent regen remains authoritative, but it can only run from a buildable placeholder.

### `Main.lean` is not the only chain that needs breaking

The hatch above breaks the *forced-check* import chain — `Main.lean` imports the
`EvmAsm.Codegen.Proofs.*` modules only so they get checked, so commenting them is free. But the
deadlock can also sit in a module the emitter **genuinely needs**, and then that hatch does not
help.

Observed while batching three branches where one *deleted* code (shrinking `.text`) and another
*added* it. `lake exe codegen` would not link:

```
error: EvmAsm/Codegen/Programs/RlpSpliceHelperSpec.lean:697:73: Tactic `decide` proved that the
  proposition rlpItemSizeBase = 2147503412 is false
```

Same chicken-and-egg as above — a `decide`-pinned guest PC checked against a stale
`GuestAddrs.lean` — but `RlpSpliceHelperSpec` reaches the exe via
`Programs/Imports.lean` → `Programs/Registry.lean`, which `Cli`/`Driver` really do need. Commenting
`Main.lean`'s `Proofs.*` imports leaves that path intact, so the exe still fails.

The lower cut is the two `*Spec` imports in `EvmAsm/Codegen/Programs/Imports.lean`. The Spec
modules contribute theorems, not emitted programs, so the emitter does not need them:

```bash
# 1. Comment ONLY the failing `*Spec` imports in EvmAsm/Codegen/Programs/Imports.lean
#    (plus Main.lean's Proofs.* imports if GuestImage is also implicated).
# 2. scripts/gen-symbol-addresses.py --build     # now links; TSV is authoritative
# 3. Read the true addresses for the pinned symbols out of the fresh TSV:
#      grep -E '\brlp_item_span\b|\brlp_item_size\b' scripts/asm-fixtures/symbol-addresses.tsv
# 4. Restore BOTH files, then run the full 4-step procedure and repin.
```

**The linked image is the arbiter for a pinned address, not either branch.** In that incident the
pins the merge already carried (`0x80004dc0` / `0x80004d34`, from the deleting branch) turned out to
be *correct* for the combined layout, and the older values on the sibling branches were the stale
ones — so no pin needed editing at all, and "fixing" the mismatch by reverting to a sibling's
literal would have broken the build. Read the relinked ELF before changing any pin.

Verify the bootstrap was free the same way as above: `git diff --quiet` on **both**
`EvmAsm/Codegen/Programs/Imports.lean` and `Main.lean` before committing.

### Iterate to a fixpoint, and check exit codes rather than file stability

When one branch shrinks `.text` and another grows it, a single regen pass is not enough — the size
change moves addresses, which changes the emitted `la`/`jal` encodings, which changes the size
again. Iterate steps 1–3 until the TSV stops changing.

Do **not** decide convergence by comparing the TSV before and after a pass. A failed
`gen-symbol-addresses.py` leaves the file untouched, and "unchanged" then looks exactly like
"converged" — a loop written that way reports a fixpoint over a failed regen. Check every step's
exit status first, and only then treat a stable TSV as convergence:

```bash
scripts/gen-symbol-addresses.py --build          || { echo "step 1 FAILED"; exit 1; }
python3 scripts/asm_to_program.py guest-addrs    || { echo "step 2 FAILED"; exit 1; }
python3 scripts/guest_image_coverage.py --emit-lean || { echo "step 3 FAILED"; exit 1; }
```

A stale pin fails late and behind a cached `.olean`, so the first symptom is often an unrelated
module rather than the pin itself.
