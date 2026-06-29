# Sail-zkVM — Tier C (sub-doubleword loads) bootstrap

**For:** the next session. **Status going in:** Tier A (LD, doubleword) is **DONE** —
`ld_sail_equiv` is now an unconditional theorem (no `h_exec`), committed `e34e4b918`
on `feat/sail-zkvm-integration`. Build `lake build EvmAsm` = **2987/2987, exit 0**,
sorry-free, no `native_decide`/`bv_decide`.

> ## ⇒ START HERE
> 1. Read this file + `EvmAsm/Rv64/SailEquiv/VmemReduction.lean` (all the Tier A infra)
>    + the memory note `[[sail-zkvm-integration]]` (full recipe + gotchas).
> 2. Tier C = the **6 sub-doubleword loads** `LW LWU LH LHU LB LBU` (`execute_LOAD`
>    widths 4/2/1). They reuse ~everything from Tier A; the one genuinely new piece is a
>    **width-N read bridge** relating the Sail `readBytes w addr` to the toy
>    `extract*(getMem (alignToDword addr))`.
> 3. There is **one OPEN decision that gates Tier B (stores), NOT Tier C**: the
>    `StateRel.mem_agree` align-restrict question (see "Tier B blocker" below). Tier C is
>    unblocked — do it first.

## Reusable infrastructure now available (all in `VmemReduction.lean`)

- **`structure BareModeInv s`** — the register-level bare bundle (priv=Machine, MPRV=0,
  mseccfg.PMM=0, pmpcfg all-OFF, pmpaddr, pma_regions). Reuse verbatim.
- **`sail_reduce [facts…]`** tactic + `sail_step` simp set (`SailStepAttr.lean`) — bundles
  the `SailME.run`/`ExceptT`/`EStateM`/`monadLift`/`readReg` plumbing every reduction
  unfolds. Use it for the new width-N reductions.
- **Width-GENERIC leaves** (take a `width : Nat` arg — reuse directly):
  `pmaCheck_load_ok`, `pmpCheck_machine_off`, `within_mmio_readable_ram`,
  `phys_access_check_load_ok` (the last is currently stated generic too).
- **Width-8-SPECIFIC** (need width-N analogues): `readBytes8_eq_reconstruct`/`readBytes8_raw`,
  `read_ram_plain_load`, `checked_mem_read_load`, `mem_read_load_bare`,
  `vmem_read_addr_load_bare`, `vmem_read_load_bare`. These hardcode `readBytes 8` /
  `reconstructDword`. Generalize to `w ∈ {1,2,4}` (parametrize or one-per-width).
- **Address/value plumbing:** `pm_transform_PA_zero`, `transform_effective_address_bare`,
  `translateAddr_bare`, `runSail_eq_ok`, `bits_of_virtaddr_mk`, `zero_extend64_id`,
  `updateSubrange_full` (width-8; needs width-N), `split_misaligned_aligned`,
  `misaligned_order_one`, the generalized `untilFuelM_one`/`_pure` (`[Monad m]`).

## Tier C plan (per the grounded scope `sail-memory-discharge-scope.md` §"Tier C-load")

Toy semantics (verified, `Basic.lean`): for width `w`,
`LW → setReg rd ((getWord32 addr).signExtend 64)`, `LWU → zeroExtend`, similarly
`LH/LHU` (`getHalfword`), `LB/LBU` (`getByte`). And
`getWord32 s addr = extractWord32 (s.getMem (alignToDword addr)) (byteOffset addr / 4)`
(`extractWord32 w pos = (w >>> (pos*32)).truncate 32`); `getHalfword`/`getByte` analogous.

Sail side (`execute_LOAD imm rs1 rd is_unsigned w`): identical to LD except `w ∈ {1,2,4}`
and `extend_value is_unsigned data` is a REAL sign/zero extend (for LD width 8 it was the
identity). `vmem_read`→`vmem_read_addr`: `split_misaligned` aligned ⇒ `(1, w)`, so the
loop is still single-iteration; `updateSubrange data (8w-1) 0 v = v` (width-N analogue of
`updateSubrange_full`); `mem_read … w …` reads `w` bytes via `read_ram`→`readBytes w`.

**The one new semantic obligation — the width-N read bridge.** Relate the Sail
`readBytes w addr` (the low-`w`-byte little-endian value at `addr`) to the toy
`extract*(getMem (alignToDword addr))`. `mem_agree` only relates full dwords
(`reconstructDword sSail.mem a.toNat = sRv.getMem a` for 8-aligned-or-any `a`), so:
`readBytes w addr = extractLsb' 0 (8w) (reconstructDword sSail.mem (alignToDword addr).toNat
shifted by byteOffset)`. Concretely the value the Sail reads at a `w`-aligned `addr`
equals `getWord32/Halfword/Byte` of the toy dword at `alignToDword addr`. Prove this once
(parametric in `w`, keyed on the alignment precondition `addr % w = 0` and the dword base),
then the 6 lemmas are near-copies differing only in `w` and `extend_value` sign/zero.

**Suggested order:** (1) `readBytesN`/`reconstruct`-slice bridge lemma; (2) width-N
`read_ram`/`checked_mem_read`/`mem_read`/`vmem_read_addr`/`vmem_read` (mirror Tier A, use
`sail_reduce`); (3) `lw_sail_equiv` (signed, w=4) end-to-end; (4) `lwu/lh/lhu/lb/lbu`
as copies (flip `is_unsigned`, swap `w` and the extract). Then delete the corresponding
`h_exec` placeholders in `MemProofs.lean` (as we did for LD).

## Scope-honesty carried from the Tier A review (`sail-tier-a-review.md`)

Two facts about what `ld_sail_equiv` promises — inherit them for the Tier C lemmas and
flag them for the eventual consolidated `step_execute_sail_sim`:

1. **Byte-presence is an assumption beyond `StateRel`.** `mem_agree` (via `reconstructDword`'s
   `getD`-default-0) does NOT imply the `hm0..hm7` "byte materialized in `sSail.mem`" facts;
   toy `getMem` is total, SAIL `readByte` throws on a missing key. So the load correspondence
   is *partial* (holds where SAIL memory is populated). Tier C lemmas inherit this (width-N
   byte-presence). Keep it explicit in statements.
2. **Missing precondition-construction glue (the real end-to-end gap).** `hclint/hsig/hhtif/
   h_match` are abstract caller obligations; nothing yet discharges them from the concrete
   `sail_model_init` region table + platform constants. The end-to-end usable form needs a
   **`BareModeInv`-construction lemma** + a **"RAM address ⇒ MMIO-disjoint ∧ in a readable
   PMA region"** lemma (instantiating `within_clint/sig/htif = false` and `matching_pma_region
   … = some readable` for addresses in the default RAM region). Build this once; both Tier C
   and the consolidated step theorem consume it. (It's also what would let a non-vacuity
   *witness* `example` be written cheaply — currently argued, not mechanized.)

## `bv_eval` grind set — seed it here (per GRIND.md §8.2 Phase 6)

Tier C multiplies the recurring concrete-arithmetic facts (per-width `.toNat`/index/
`setWidth`/sign-zero-extend evaluations: `(8*(0+1)*w-1).toNat`, `extend_value` cases,
`extractLsb'`/`truncate` identities). That is exactly the planned `bv_eval` grind set's
scope. Once 5–10 such facts recur across the 6 lemmas, register the stable ones as
`@[bv_eval, grind =]` following the §8.1 recipe (cap ~30, survey demand first). Do NOT
grind the monad plumbing — that stays `sail_reduce` (simp).

## Tier B (stores) — STILL BLOCKED on the `mem_agree` decision

Unchanged from `sail-memory-discharge-scope.md` §"decisive blocker": a store mutates one
toy dword cell but the byte-quantified `StateRel.mem_agree` breaks at the 7 overlapping
unaligned offsets ⇒ the store `*_sail_equiv` conclusion is FALSE for general inputs.
**Decision required before any store work** (Option A align-restrict `mem_agree` to
8-aligned `a` — recommended, needs re-audit of consumers, which after Tier A/C are exactly
the load lemmas reading at the access address; Option B byte-granular toy mem; Option C
keep `h_exec`). This is the maintainer's call; surface it before Tier B.

## Carried-forward gotchas (full list in `[[sail-zkvm-integration]]`)

- `erw` (not `rw`) for the `8*w` vs reduced-Nat type-annotation defeq on `readBytes`.
- StateRel reg_agree: `rw [hdata]` (= `hrel.mem_agree addr`) BEFORE any `simp`/`simpa`,
  because `simpa`'s `BitVec.toNat_add` normalizes `(x+y).toNat` and then `hdata` no longer
  matches.
- `assert (w ≤b xlen_bytes)`: `simp +decide only [PreSail.assert, if_true]`; reduce it
  before the `vmem_read` rewrite so the read runs on `sSail`, not the post-assert `s'`.
- doc-comment (`/-- -/`) on an `attribute` command is a parse error — use `/- -/`.
- the `unusedSimpArgs` linter false-flags args when the overall simp leaves a goal — ignore
  until the proof closes.
