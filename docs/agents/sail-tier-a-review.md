# Adversarial review — Tier A LD discharge (commit `e34e4b918`)

**Date:** 2026-06-29. **Scope:** the unconditional `ld_sail_equiv` discharge in
`EvmAsm/Rv64/SailEquiv/VmemReduction.lean` (+ `SailStepAttr.lean`; `MemProofs.lean`
placeholder removal). Independent read-only adversarial pass. Build green (2987/2987).

## Verdict: 🔴 sound, non-vacuous, faithful — no soundness defects.

### Vacuity (the headline risk) — CLEARED
The deleted `h_exec` version was vacuous: its hypothesis literally assumed the
`StateRel (execInstrBr …) sSail'` conclusion. The new `ld_sail_equiv`:
- **Every hypothesis is input-side** (`sSail`/`sRv`/the access address
  `sRv.getReg rs1 + signExtend12 offset`). **None mention the output `sSail'` or assume the
  conclusion.**
- **Hypotheses are mutually satisfiable** — they constrain *independent* subsystems
  (PMP entries vs. the PMA-region table vs. CLINT/SIG/HTIF ranges vs. hashmap contents). A
  normal bare-mode RAM doubleword (e.g. `0x8000_0000`, in the default `sail_model_init`
  RAM region, disjoint from MMIO) satisfies all of them at once. The alignment predicate
  is genuine and discriminating, verified by `decide`:
  `is_aligned_vaddr (Virtaddr 0x8000_0000) 8 = true`, `… 0x8000_0003 … = false`.

### Faithfulness — OK
Conclusion relates the real `runSail (execute_LOAD … false 8)` to the toy
`execInstrBr sRv (.LD rd rs1 offset)` via the **same `StateRel`** (`reg_agree`+`mem_agree`)
the genuine `add_sail_equiv` etc. use. Address bridge `sign_extend (m:=64) offset =
signExtend12 offset` is a kernel-checked `rfl`; value bridge is `reconstructDword = getMem`
via `mem_agree`. The leaves (`read_ram_plain_load`, `checked_mem_read_load`,
`mem_read_load_bare`, `vmem_read_addr_load_bare`, `vmem_read_load_bare`) each conclude the
**actual** SAIL function `= .ok (… reconstructDword …) s` (state unchanged) — genuine
definitional reductions, no smuggled conclusion.

### Hygiene — OK
`#print axioms ld_sail_equiv` = `{propext, Classical.choice, Quot.sound} ∪
{load_reservation, plat_term_write, sys_enable_experimental_extensions}` — within the
allowlist; the 3 platform axioms are declared in the **vendored** `RiscvExtras.lean`, not
introduced by us (`mem_read_load_bare` itself is clean `{3 classical}`; the platform axioms
enter only via the wider `execute_LOAD` path). No `sorry`/`admit`/`native_decide`/
`bv_decide` in `SailEquiv/`. `sail_step`/`sail_reduce` populate only the custom set (no
global `@[simp]` perturbation); `+decide` is kernel-checked.

## 🟡 Scope-honesty notes (not defects — capture in docs / caller-facing story)

1. **Byte-presence is an assumption strictly beyond `StateRel`.** `StateRel.mem_agree`
   uses `reconstructDword`, which `getD`-defaults missing bytes to `0`, so it does **not**
   imply the `hm0..hm7` "byte present in `sSail.mem`" facts. Toy `getMem` is total; SAIL
   `readByte` throws on a missing key. So `ld_sail_equiv` is genuinely *conditional on the
   8 accessed bytes being materialized in `sSail.mem`* — the LD correspondence is partial
   (holds only where SAIL memory is populated). Correct and honest; a caller with
   `StateRel` alone cannot derive `hm0..hm7`.
2. **The MMIO/PMA preconditions are caller obligations with no construction lemma yet.**
   `hclint/hsig/hhtif/h_match` are supplied abstractly; nothing yet discharges them against
   the concrete `sail_model_init` region table + platform constants. End-to-end use needs a
   `BareModeInv`-construction / "RAM-address ⇒ MMIO-disjoint + readable-region" glue lemma.
   This is exactly what Tier C and the consolidated `step_execute_sail_sim` will need.

## 🟢 Cosmetic
- `bits_of_virtaddr_mk` was a global `@[simp]`; **demoted to `@[sail_step]`-only** this pass
  (niche helper, zero global footprint) — done, build still green.
- `is_unsigned = false` is irrelevant at width 8 (extend is identity); `region`/`b0..b7`
  are explicit binders the caller must name — over-explicit, not unsound.

## Bottom line
The vacuity that made the `h_exec` version worthless is genuinely gone. The two 🟡 items
are *scope-honesty* facts about what the theorem does and doesn't promise — recorded here
and in `sail-tier-c-bootstrap.md`, not bugs.
