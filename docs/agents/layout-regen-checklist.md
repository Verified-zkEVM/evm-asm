# Layout regen checklist

For any change that moves the guest memory layout (arena capacities,
section bases, row strides). Written after GH #10836 / PR #10878, whose
CI caught a pin casualty the local build never saw.

## The four steps

1. `python3 scripts/gen-symbol-addresses.py --build` — rebuild + re-emit
   the guest ELF with the new layout; writes the checked-in snapshot
   `scripts/asm-fixtures/symbol-addresses.tsv`.
2. `python3 scripts/asm_to_program.py guest-addrs` — regenerates
   `EvmAsm/Codegen/GuestAddrs.lean` from the fixture scan (drift-guarded
   by `check-guest-addrs`).
3. `python3 scripts/guest_image_coverage.py --emit-lean` — regenerates
   `EvmAsm/Codegen/Proofs/GuestImageEntries.lean`.
4. Full build + repair every address-pinned proof (see below).

`RegionMap.lean` is hand-maintained: update its sizes/bases by hand and
confirm with `scripts/check-region-map.sh` (PASS required, with the
symbol-addresses TSV matching the relinked ELF).

## Full build, not `lake build codegen`

**`lake build codegen` is NOT `lake build` for casualty enumeration.**
The codegen target builds only the codegen executable's import closure;
proof modules outside it (e.g. `EvmAsm/Codegen/Proofs/GuestImage.lean`)
are never type-checked. A layout-moving change must run a **full**
`lake build` before anyone claims zero casualties, and the casualty
report should name modules that demonstrably appear in the build log.

## Pin values come from regenerated artifacts, not arithmetic

When a `by decide`/`rfl` pin breaks, take the new value from the
**regenerated** `GuestAddrs.lean` / ELF, never from hand arithmetic on
the old value (arena re-packing makes offsets unpredictable, and a
wrong literal gets reflected back by the build error, looking measured).

Known manual-repin files (the four-step regen does NOT touch them):
- `EvmAsm/Codegen/Proofs/GuestImage.lean` — `SatWithin` literals for
  `.bss` base/size/end (see the warning comment at the top of that
  section). Update with ELF-measured values.
- `U256MulU64Be/OuterLoop.lean` — `accBase_toNat` + sibling literals
  (consumed by `rw`; take values from regenerated `GuestAddrs`).

## Fixed-point standard

After the regen, emit `stateless_guest` again and state byte-identity of
the emitted `.s` and stripped ELF (raw ELF sha differs only by the
embedded object filename — compare stripped). Two consecutive identical
emissions do NOT prove freshness (two cache hits satisfy trivially); the
strong checks are artifact-vs-independent-expectation:
`check-region-map.sh` against the relinked ELF and `check-guest-addrs`
regenerate-and-diff, plus a positive content check that every `.bss`
symbol in the TSV lies inside the intended window.
