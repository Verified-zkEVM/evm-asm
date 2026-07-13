# Regenerating the generated layout files

Several checked-in files are **generated from the linked guest ELF** and must be regenerated
after any change that alters the guest's emitted bytes or layout (a re-emit, a new/removed
routine, a `.text`/`.data` size change). Editing them by hand is wrong — each carries a
`GENERATED — do not edit` header.

The four files, what regenerates each, and what it depends on:

| File | Regenerate with | Derived from |
|---|---|---|
| `scripts/asm-fixtures/symbol-addresses.tsv` | `scripts/gen-symbol-addresses.py --build` | the linked ELF (`lake exe codegen`) |
| `EvmAsm/Codegen/GuestAddrs.lean` | `python3 scripts/asm_to_program.py guest-addrs` | the TSV above |
| `EvmAsm/Codegen/RegionMap.lean` (the `textSizeBytes` / `dataSizeBytes` fields) | manual edit to the ELF section sizes | the linked ELF |
| `EvmAsm/Codegen/Proofs/GuestImageEntries.lean` | `python3 scripts/guest_image_coverage.py --emit-lean` | `GuestAddrs` + the linked function set |

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

# 4. RegionMap.lean is NOT fully auto-generated: if the ELF section sizes changed,
#    update RegionMap.textSizeBytes / dataSizeBytes to the sizes reported by
#    `readelf -S` on the relinked ELF. Everything else in RegionMap is a fixed,
#    kernel-checked layout statement and should not change on a routine re-emit.
```

## Verify

```bash
scripts/check-asm-to-program.sh   # byte-tie: emitted _prog bytes vs GuestAddrs/TSV (also runs check-guest-addrs)
scripts/check-region-map.sh       # Lean RegionMap vs ELF section sizes / bases
lake build                        # the Lean side (GuestImage etc.) must still compile
```

`check-asm-to-program.sh` and `check-region-map.sh` are the drift guards; if either fails after a
guest change, a regen step above was missed or RegionMap's sizes are stale.

## Notes

- **Do not use `scripts/regen-cycle.sh`** — it is broken (hardcoded dead scratch path + an
  uncommitted helper). Use the commands above.
- Step 2 (`GuestAddrs.lean`) is the file that churns on essentially every layout change: the
  per-function `_prog` defs reference its constants by name (`AsmReloc.{laHi,laLo,jalOff}`), so a
  size change only requires regenerating the TSV + `GuestAddrs.lean`, never the hundreds of
  `_prog`s.
- See also `docs/4ch8f-region-map.md` §5 ("Drift handling") for the RegionMap/TSV rationale and
  the STABLE-vs-LINK_DEPENDENT symbol classification.
