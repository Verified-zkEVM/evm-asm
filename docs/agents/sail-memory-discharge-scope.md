# Sail memory `h_exec` discharge — grounded scope (2026-06-26)

> **UPDATE 2026-07-09 — ALL TIERS DONE; `h_exec` is fully eliminated.**
> Tier A (`ld_sail_equiv`, `VmemReduction.lean`) and Tier C (the six sub-dword loads,
> `VmemReductionLoads.lean`) landed with PR #9535. Tier B (the four stores) is now
> discharged too: the `mem_agree` align-restrict decision (Option A below) was adopted
> on main, and `sd/sw/sh/sb_sail_equiv` are unconditional theorems in
> `EvmAsm/Rv64/SailEquiv/VmemReductionStores.lean`, built on the store-side write chain
> in `VmemWriteReduction.lean` (`writeBytes → write_ram → checked_mem_write →
> mem_write_value → vmem_write_addr → vmem_write`, plus `Store Data` twins of the
> bare-mode leaves). The `mem_agree` rebuild uses `reconstructDword_of_bytes` /
> `reconstructDword_congr` (`MemReduce.lean`) + per-width read-modify-write bridges
> (`replaceWord32/Halfword/Byte`). Stores need **no byte-presence hypotheses**
> (`writeByte` is `mem.insert`). `MemProofs.lean` retains no conditional lemmas.
> The analysis below is kept as the historical reference. Remaining follow-ups:
> the consolidated-theorem fold (§Final fold) and the `BareModeInv`
> precondition-construction glue.

> **UPDATE 2026-06-29 — Tier A (LD) is DONE.** `ld_sail_equiv` is now an unconditional
> theorem (no `h_exec`) in `EvmAsm/Rv64/SailEquiv/VmemReduction.lean`, committed
> `e34e4b918` (build 2987/2987). The full `execute_LOAD`→`vmem_read`→`mem_read` chain is
> proven against a `BareModeInv` bundle + per-access facts; the vacuous `h_exec`
> `ld_sail_equiv` was removed from `MemProofs.lean`.

Fresh adversarial review + full call-chain trace of the Sail RV64 model
(`vendor/sail-riscv-zkvm-lean/Out/`) and the toy model (`EvmAsm/Rv64/`).
Purpose: scope the work to turn the 11 conditional `MemProofs.*_sail_equiv`
lemmas (each assumes `h_exec`) into real, unconditional lemmas — *before*
committing to execution.

**Baseline:** `lake build EvmAsm` = 2986/2986, exit 0. 8 leaf lemmas in
`VmemReduction.lean` confirmed present and well-formed. The 11 `MemProofs`
lemmas are trivial `h_exec` wrappers (they assume the very `StateRel`
conclusion to be proven — sound but vacuous when `h_exec` is unsatisfiable).

---

## TL;DR — three findings, one of them decisive

1. **The LD path is real and clean.** The 8 leaves cover its hard semantic
   content; a genuine unconditional `ld_sail_equiv` is achievable. (Tier A)

2. **Sub-doubleword *loads* (LW/LWU/LH/LHU/LB/LBU) are a separate, real tier**
   — not "assembly." Each needs its own width-N read bridge + sign/zero
   extension, keyed on an alignment precondition. Doable, shareable infra. (Tier C-load)

3. **🛑 Stores (SD/SW/SH/SB) are likely *not provable* against the current
   `StateRel`.** `StateRel.mem_agree` quantifies over **every** byte address
   `a' : BitVec 64`, but the toy memory is a dword-cell function that a store
   mutates at a single index. A store breaks `mem_agree` at the 7 overlapping
   unaligned offsets. This is a **memory-model decision**, not a proof-effort
   question — and almost certainly why the original author deferred with
   `h_exec`. **Must be resolved before any store work.** (Tier B — blocked)

---

## Confirmed ground truth (file:line)

### Load path (all reductions exist or are mechanical)
- `execute_LOAD` `InstsEnd.lean:4207` — `vmem_read … (Load Data) false false false`,
  then `wX_bits rd (extend_value is_unsigned data)`.
- `extend_value` `BaseInsts.lean:469` — unsigned ⇒ `zero_extend 64`, signed ⇒
  `sign_extend 64`. **For LD (width 8) this is identity** (64→64).
- `vmem_read` `VmemUtils.lean:391` → `get_transformed_data_addr` (= `rX_bits + offset`,
  bare-mode `transform_effective_address` is identity) → `vmem_read_addr`.
- `vmem_read_addr` `VmemUtils.lean:249` — alignment branch (skipped when aligned),
  `split_misaligned`, `misaligned_order`, `untilFuelM`, `translateAddr`, `mem_read`.
- `split_misaligned` `VmemUtils.lean:206` — `sys_misaligned_byte_by_byte = false`
  (`:201`), `sys_misaligned_allowed_within_exp = 0` (`:203`); aligned ⇒ `(1, width)`.
- `misaligned_order` `VmemUtils.lean:223` — `sys_misaligned_order_decreasing = false`
  (`:199`) ⇒ `(0, n-1, 1)`; for `n=1` ⇒ `(0,0,1)` (one iteration).
- `mem_read` `Mem.lean:441` → `mem_read_priv` `:435` → `mem_read_priv_meta` `:408`.
  Plain LD `(aq,rl,res)=(false,false,false)`: align-throw guard `(aq||res)&&¬aligned`
  is false; match arm `(_,_,_)` ⇒ `checked_mem_read`.
- `checked_mem_read` `Mem.lean:394` — `phys_access_check` then `within_mmio_readable`
  (false ⇒ `read_ram`).
- `phys_access_check` `Mem.lean:382` — `pmpCheck` (leaf #8) + `pmaCheck` (leaf #7),
  both `none` ⇒ `none`.
- `read_kind_of_flags (false,false,false) = Read_plain` `Mem.lean:214`.
- `read_ram` `PhysMemInterface.lean:319` → `sail_mem_read` `Sail.lean:626` →
  `readBytes` `Sail.lean:587` → `readByte` `Sail.lean:581` (state `mem.get?`).
  **No axioms on this path** beyond the 4 known platform axioms (and those enter
  only via the wider `execute`, not the pure read).
- Callbacks `mem_read_callback`/`mem_exception_callback` are no-op `Unit` stubs.

### The MMIO leaf gap (no existing lemma)
- `within_mmio_readable` `Platform.lean:686` — `get_config_rvfi () = false`
  (`Prelude.lean:222`), so it does **not** short-circuit. Reduces to
  `within_clint || within_sig || (within_htif_readable && 1≤width)`.
- `plat_have_clint = true` (`PlatformConfig.lean:2159`), `plat_have_sig = true`
  (`:2165`) ⇒ `within_clint`/`within_sig` do real range checks (`Platform.lean:203/214`).
- `within_htif_readable` = `within_htif_writable` `Platform.lean:225` — reads
  register `htif_tohost_base`; `none` ⇒ false, else range check.
- **⇒ a new leaf #9 `within_mmio_readable_ram`** is required: from address
  disjointness vs CLINT/SIG ranges + (`htif_tohost_base = none` or HTIF
  disjoint), conclude `within_mmio_readable paddr width s = .ok false s`.
  Mechanical but not yet done; the bootstrap's "assembly" framing omits it.

### Store path (structurally parallel; needs new write-side leaves)
- `execute_STORE` `InstsEnd.lean:3955` — `data = extractLsb (rX rs2) (width*8-1) 0`,
  `vmem_write … (Store Data) false false false`.
- `vmem_write` `VmemUtils.lean:402` / `vmem_write_addr` `:308` — same loop shape;
  `res=false` ⇒ skips the reservation branch; calls `mem_write_ea` then
  `mem_write_value`.
- `mem_write_ea` `Mem.lean:448` — `(rl||con)&&¬aligned` false ⇒ `Ok (write_ram_ea …)`;
  `write_ram_ea` `PhysMemInterface.lean:313` is a pure `Unit` no-op.
- `mem_write_value` `Mem.lean:496` → `_meta` → `_priv_meta` `:469` →
  `checked_mem_write` `:455` → `phys_access_check` + `within_mmio_writable` →
  `write_ram` `PhysMemInterface.lean:276` → `sail_mem_write`/`writeBytes`.
- `writeBytes` `Sail.lean:563` — `List.forM` of `writeByte` `:559` =
  `modify mem.insert addr v_i`. An 8-byte store ⇒ `mem` with `addr+i ↦ vᵢ`.
- **`pmaCheck` leaf #7 is stated for `Load Data`** (`VmemReduction.lean:240`); a
  **`Store Data` variant (checks `attributes.writable`) is needed**. `pmpCheck`
  leaf #8 generalizes trivially (all-OFF + Machine ⇒ `none`, access-agnostic).
- **A new leaf #10 `within_mmio_writable_ram`** (mirror of #9).

---

## The decisive blocker: `StateRel.mem_agree` vs stores

`StateRel` (`StateRel.lean:231`):
```lean
mem_agree : ∀ (a : BitVec 64), reconstructDword sSail.mem a.toNat = sRv.getMem a
```
Toy memory (`Basic.lean:436`): `getMem a = s.mem a`, a total `BitVec 64 → BitVec 64`
function; `setMem a v` (`:440`) changes it at **index `a` only**. Toy SD
(`Execution.lean:92`): `setMem addr (getReg rs2)` — one cell.

`reconstructDword mem a.toNat` reads the **8 bytes** `[a.toNat, a.toNat+8)`. So
`mem_agree` ties every byte-offset's dword-view of the Sail byte map to the toy
cell at that index — a strong total invariant.

**A store does not preserve it.** SD writes Sail bytes `[addr, addr+8)` and toy
cell `addr`. Consider `a' = addr+1` (toy cell unchanged, since `addr+1 ≠ addr`):
- toy side after: `getMem (addr+1)` = old value.
- Sail side after: `reconstructDword mem' (addr+1)` reads bytes `addr+1 … addr+8`
  — 7 of which were just overwritten by `v`, 1 (`addr+8`) old. Generally a
  different value than old `getMem (addr+1)`.

So the conclusion `StateRel (execInstrBr sRv (.SD …)) sSail'` is **false for
general inputs**. The store `*_sail_equiv` lemmas are therefore not merely hard —
they are unprovable against the current relation. (They "compile" today only
because `h_exec` *assumes* that conclusion.)

This is independent of the Sail reduction work; it is a model-definition choice.

### Options (pick before any store work)
| Option | Change | Cost | Risk |
|---|---|---|---|
| **A. Align-restrict `mem_agree`** | `∀ a, a aligned-8 → reconstructDword … = getMem a` | small edit to `StateRel`; re-audit all proofs that *consume* `mem_agree` (loads) | LD/sub-word loads must read via the aligned base — already how the toy does it (`getWord32` uses `alignToDword`); LD assumes addr 8-aligned. Cleanest. |
| **B. Byte-granular toy memory** | redefine toy `mem : Addr → BitVec 8`; `getMem`/`setMem` become 8-byte read/write | large; touches every memory-touching toy proof + EVM layer | high blast radius |
| **C. Keep `h_exec` for stores** | ship loads unconditionally, leave stores deferred | zero | honest but leaves 4 lemmas conditional indefinitely |

**Recommendation: Option A**, but it requires a **fresh audit** — `mem_agree` is
consumed by every lemma that reads memory and is a field of the `StateRel` used
by *all* 49 instruction proofs. Restricting it weakens a hypothesis the loads
rely on; need to confirm no current proof depends on the unaligned cases.
(Likely none do — only LD/LW/etc. read memory, and they read at the access
address; but this must be verified, not assumed.)

---

## Tiered work breakdown

### Tier A — `ld_sail_equiv` unconditional ✅ achievable now
New artifacts in `VmemReduction.lean`:
- `structure BareModeInv` (priv=Machine, mstatus+MPRV=0, pmpcfg all-OFF,
  pmpaddr present, pma_regions has a readable region covering the access,
  htif/MMIO disjointness). Bundles leaves #2/#7/#8 + #9 preconditions.
- **leaf #9** `within_mmio_readable_ram` (new; mechanical).
- plumbing lemmas: `misaligned_order 1 = (0,0,1)`; `untilFuelM` already #5;
  `updateSubrange data 63 0 v = v` (n=1 full-range write); `drop_meta`/`add_meta`
  no-ops; `extend_value false (8-byte) = id`.
- `mem_read_load_bare` (compose effectivePrivilege→…→read_ram→#1).
- `vmem_read_addr` / `vmem_read` / `execute_LOAD` reductions.
- rewrite `ld_sail_equiv` (drop `h_exec`, take `BareModeInv` + per-access facts);
  rebuild `StateRel` (reg via `reg_agree_after_insert`; mem unchanged ⇒ trivial).
- Est: the bulk of one focused session; de-risks the whole approach.

### Tier C-load — LW/LWU/LH/LHU/LB/LBU 🟡 real, shareable
- width-N read bridge: `readBytesN a` = the N-byte slice; relate to
  `extractWord32 / extractHalfword / extractByte` of `reconstructDword` at the
  **aligned base** (uses `mem_agree` at `alignToDword addr`; needs `byteOffset`
  reasoning, clean because the access is N-aligned).
- `extend_value` sign/zero cases (LW signed, LWU/LBU/LHU unsigned, etc.).
- 6 lemmas; once one width is done the others are near-copies. No store blocker
  (loads don't mutate memory).
- Est: one session after Tier A infra lands.

### Tier B — SD/SW/SH/SB 🛑 blocked on `mem_agree` decision
- Prereq: resolve the relation (Option A) + audit.
- Then write-side leaves: `pmaCheck` Store-Data variant; `within_mmio_writable_ram`;
  `writeBytes`→`reconstructDword` **write bridge** (post-`insert×N` mem reconstructs
  to `v` at the written dword, unchanged on disjoint dwords); the hardest new
  semantic content. Sub-word stores add read-modify-write (`replaceWord32` etc.).
- `vmem_write_addr` reduction (mirror of read, plus `mem_write_ea`).
- StateRel rebuild now has the **mem-changed** obligation (the crux above).
- Est: largest tier; do not start before the model decision.

### Final fold (after tiers)
- `StateRelFull` + side-condition predicate; generalize `Instr.simulableUncond`
  → `Instr.simulable`; extend `step_execute_sail_sim_uncond` (`StepSim.lean`) to
  dispatch the memory tier. (Already sketched in the StepSim header / bootstrap.)

---

## Recommended sequencing
1. **Tier A** (LD) — proves the machinery end-to-end, ships a real lemma, no
   model changes needed.
2. **Decide the `mem_agree` question** (Option A recommended) + audit consumers.
3. **Tier C-load** (6 loads) — parallel-friendly once the width-N bridge exists.
4. **Tier B** (4 stores) — only after step 2.
5. **Fold** into the consolidated theorem.

## Axiom budget
Pure reads/writes stay within `{3 classical} ∪ {4 platform}`; the 4 platform
axioms enter only through the wider `execute` reference, not the leaf reductions.
Keep the `lake env lean AxCheck.lean` guard (no `2>/dev/null`) after each tier.
