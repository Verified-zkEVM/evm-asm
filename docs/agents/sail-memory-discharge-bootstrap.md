# Sail-zkVM — memory `h_exec` discharge bootstrap

> **⚠ SUPERSEDED (2026-06-29).** Tier A (LD) is complete: the composition described below
> (`BareModeInv` → `mem_read_load_bare` → `vmem_read_addr` → `vmem_read` → `execute_LOAD`)
> is all PROVEN, and `ld_sail_equiv` is now unconditional (commit `e34e4b918`). For the
> next tier use **`docs/agents/sail-tier-c-bootstrap.md`** (sub-doubleword loads). This
> file is kept for historical context only.

---


**For:** the next session. Goal: turn the 11 conditional `MemProofs` `*_sail_equiv`
lemmas (each assumes `h_exec`) into lemmas proven from a concrete **bare-mode
precondition bundle**, by writing the layered `vmem_read/write` reduction the original
authors deferred. This is the largest remaining tier of the P4 consolidated theorem.

> ## ⇒ START HERE (Phase 2 — composition). All 8 leaf lemmas are DONE & committed.
> The hard proofs are over; what's left is **assembly**. Cold-start steps:
> 1. Read this file + `EvmAsm/Rv64/SailEquiv/VmemReduction.lean` (the 8 proven leaves) +
>    `EvmAsm/Rv64/SailEquiv/MemProofs.lean` (the 11 `h_exec` lemmas to rewrite).
> 2. Add a `BareModeInv` bundle to `VmemReduction.lean` (sketch below), then prove
>    `mem_read_load_bare` (the first composition lemma — combines #1/#7/#8 through the
>    `mem_read` wrapper chain). Then `vmem_read_addr` → `vmem_read` → `execute_LOAD`.
> 3. Verify each builds (`lake build EvmAsm`, 2986/2986 baseline) and stays axiom-clean
>    (`{3 classical} ∪ {4 platform}` — the 4 platform axioms enter only via the wider
>    `execute` reference, not the pure reads).
>
> **`BareModeInv` sketch** (the bundle to define; addresses the long per-lemma hyp list):
> ```lean
> structure BareModeInv (s : SailState) : Prop where
>   priv   : s.regs.get? Register.cur_privilege = some Privilege.Machine
>   mstatus : ∃ mst, s.regs.get? Register.mstatus = some mst ∧ _get_Mstatus_MPRV mst = 0#1
>   pmpcfg  : ∃ cfgs, s.regs.get? Register.pmpcfg_n = some cfgs ∧
>               ∀ i, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A cfgs[i]!) = .OFF
>   pmpaddr : ∃ pas, s.regs.get? Register.pmpaddr_n = some pas
>   -- per-access (keep separate; depend on paddr): a readable PMA region covers
>   -- [paddr, paddr+width); paddr aligned; paddr outside CLINT/SIG/HTIF MMIO; bytes present.
> ```
> First composition lemma target:
> ```lean
> theorem mem_read_load_bare (s : SailState) (paddr : physaddr) (b0..b7 : BitVec 8)
>     (hbare : BareModeInv s) (region …) (h_match …) (h_read …) (h_align …)
>     (h_mmio : within_mmio_readable paddr 8 = …false…) (h_bytes : 8 bytes at (bits_of_physaddr paddr).toNat) :
>     mem_read (.Load .Data) PBMT_PMA paddr 8 false false false s
>       = .ok (.Ok (reconstructDword s.mem (bits_of_physaddr paddr).toNat)) s
> ```
> Reduce via: `mem_read`→`effectivePrivilege` (Machine, from hbare) →`mem_read_priv`→
> `mem_read_priv_meta` (aq=res=false ⇒ skip the align-throw; `(_,_,_)` arm) →
> `checked_mem_read` → `phys_access_check` (combine `pmaCheck_load_ok` #7 +
> `pmpCheck_machine_off` #8 — note phys_access_check Mem.lean:382 calls both) →
> `within_mmio_readable` false → `read_ram`→`sail_mem_read`→`readBytes` (`readBytes8_eq_reconstruct` #1).
> The callbacks (`mem_read_callback`) and `MemoryOpResult_drop_meta` are pure no-ops.
> Watch: the address into `readBytes` is `(bits_of_physaddr paddr).toNat`; thread #1's `a`
> to that. Use the proven recipe `unfold <fn>; simp +decide [<plumbing> + leaf lemmas]`.

## Verified ground truth (re-checked 2026-06-26)

- `lake build EvmAsm` = **2986/2986, exit 0** (includes `VmemReduction.lean` + `StepSim.lean`).
- `EvmAsm/Rv64/SailEquiv/StepSim.lean` ships `step_execute_sail_sim_uncond` over the
  **29 unconditional** instrs. Axioms = `{propext, Classical.choice, Quot.sound}` ∪
  `{load_reservation, match_reservation, plat_term_write, sys_enable_experimental_extensions}`.
- The `toSailInstr?` LOAD/STORE **width bug is fixed** (bytes now: LD/SD=8, LW/LWU/SW=4,
  LH/LHU/SH=2, LB/LBU/SB=1) — commit `699e9f038`.

## Why this is feasible (the decisive facts)

- `sail_mem_read`/`sail_mem_write` (`.lake/packages/Sail/Sail/Sail.lean:618,626`) are
  concrete `@[simp_sail]` **defs** over `SailState.mem : Std.ExtHashMap Nat (BitVec 8)`
  — NOT axioms. `read_ram`→`readBytes`→`readByte` (throws `OutOfMemoryRange` if a byte
  is absent). `write_ram`→`writeBytes`.
- Plain LD/SD pass `res=false`, so `load_reservation`/`match_reservation` are NEVER hit
  on the data path (they're behind `if res`/`if res && …`).
- So nothing on the path is axiomatic. It is fully reducible — under preconditions.

## Why it canNOT be unconditional (so: derive from a bundle, don't assume `h_exec`)

`pmaCheck` requires the address inside a RAM PMA region; `readByte` throws on missing
bytes; bare-mode needs Machine privilege. An arbitrary address genuinely faults. So the
deliverable is `ld_sail_equiv` (etc.) re-stated WITHOUT `h_exec`, taking instead:

### Minimal bare-mode bundle (verified for `execute_LOAD … 8`, access `Load Data`, aq=rl=res=false)

1. `cur_privilege = Machine` — read in `effectivePrivilege` (`SysControl.lean:205`).
2. `mstatus` bit 17 (MPRV) = 0 — so eff-priv = cur_privilege.
3. `mseccfg` bits 33:32 = `0b00` (PMM disabled) — so `get_pmlen = 0`, address unchanged
   by `pm_transform_PA` (`PmUtils.lean:237`).
4. all 16 `pmpcfg_n[i]` A-field (bits 4:3) = OFF — `pmpCheck` loop all `PMP_NoMatch`,
   then `priv=Machine` ⇒ `none` (`PmpControl.lean:286,314`). (NB `sys_pmp_count = 16`,
   not 0 — `PmpRegs.lean:193`.)
5. address `a = (rX[rs1] + sign_extend imm).toNat`, `a % 8 = 0` (`is_aligned_vaddr`,
   `Mem.lean:209`) — so `split_misaligned` returns `(1, 8)` (`VmemUtils.lean:206`), loop
   runs once.
6. `[a, a+8) ⊆` a readable PMA region & `a` outside CLINT `[0x0200_0000,0x020C_0000)` /
   SIG `[0x0C00_0000,0x0C00_0020)` / HTIF (HTIF off when `htif_tohost_base = none`).
   Default `sail_model_init` (`Out.lean:203`, writes `pma_regions` at `:244`) gives 3
   regions; region 3 `[2^34, 2^35)` is MainMemory `readable=true`. (`pma_regions :
   List PMA_Region`, `matching_pma_region` at `Pma.lean:334`, `range_subset` at
   `RangeUtil.lean:189`.)
7. all 8 bytes `a .. a+7` present in `sSail.mem` (else `readByte` throws).

**Result state** = input `sSail` with exactly `x_rd ↦ extend_value false data`, `mem`
and all other regs unchanged (only state mutation is the final `wX_bits`; all callbacks
— `mem_read_callback`, `xreg_full_write_callback` — are pure `Unit` no-ops). For the
post-`StateRel` to hold, need `data = sRv.getMem a`, i.e. **`readBytes 8 a` (little-endian
append) = `reconstructDword sSail.mem a`** — a bitvector bridge lemma. StateRel.reg_agree
ties `rX[rs1] = sRv.getReg rs1` so the Sail address = the toy address.

## STATUS (8 leaf lemmas proven & committed in `VmemReduction.lean`)

All axiom-clean, build 2986/2986. The hard leaves are DONE; what remains is composition.
1. ✅ `readBytes8_eq_reconstruct` (`78ac911c6`) — leaf read = `reconstructDword`.
2. ✅ `translateAddr_bare` (`274dfa8e4`) — bare-mode translation = identity.
3. ✅ `forIn'_noop` (`41bf9ae0b`) — SailM WF-loop no-op invariant.
4. ✅ `forIn'_noop_except` (`3eec407c0`) — SailME/ExceptT WF-loop no-op invariant.
5/6. ✅ `untilFuelM_one` / `_pure` (`478c2a262`) — unwrap the `fuel=1` access loop.
7. ✅ `pmaCheck_load_ok` (`2999f2047`) — PMA permits aligned readable load.
8. ✅ `pmpCheck_machine_off` + helpers `pmpReadAddrReg_noop`/`pmpMatchAddr_off` (`60bfbfe7d`) — PMP permits Machine+all-OFF.

**Remaining = composition (assembly, no open questions):** thread a `BareModeInv` bundle
through `mem_read` (effectivePrivilege Machine → mem_read_priv_meta aq=res=false skip-align
→ checked_mem_read → phys_access_check[#7+#8=none] → within_mmio_readable false → read_ram
→ readBytes[#1]); then `vmem_read_addr` (alignment + `split_misaligned`=(1,w) + untilFuelM[#5]
+ translateAddr[#2] + the above); then `vmem_read` (get_transformed_data_addr) → `execute_LOAD`
(rX read, wX write, RETIRE_SUCCESS) → rebuild `StateRel` (reg via `reg_agree_after_insert`,
mem unchanged). Then the STORE mirror (write_ram/writeBytes, mem_write_value/ea), apply to all
11 MemProofs lemmas (replacing `h_exec` with the bundle), and finally strengthen `StateRel`
to fold all tiers into one `step_execute_sail_sim`.

**Recommended next:** define `BareModeInv (s) : Prop` (cur_privilege=Machine; ∃mst, mstatus
+ MPRV=0; pmpcfg all-OFF + pmpaddr present; pma_regions has a readable region covering the
access; htif none) to bundle the per-lemma hypotheses, then the composition lemmas read cleanly.

## Proof plan (layered reduction lemmas — `simp [simp_sail]` alone does NOT work)

A diagnostic `simp only [runSail, execute_LOAD, vmem_read, vmem_read_addr, simp_sail, …]`
unfolds the structure but reduces **no branch** (all gated on symbolic register reads).
So build, bottom-up, reduction lemmas each consuming part of the bundle:

1. ✅ **DONE (commit `78ac911c6`)** — `readByte`/`readBytes` reduction + the `reconstructDword` bridge, in `EvmAsm/Rv64/SailEquiv/VmemReduction.lean`: `readBytes8_eq_reconstruct` (+ pure helper `append8_eq_or_shifts`). Axiom-clean ({3 classical}; helper {propext,Quot.sound}). Gotchas captured for the rest: `readBytes`/`readByte` ∈ namespace `PreSail`; getD↔get? = `Std.ExtHashMap.getD_eq_getD_getElem?` + `get?_eq_getElem?`; `getLsbD_append` only fires after `show (… ++ …) = _` (the `.append`/`++` head mismatch), then an 8-way getLsbD bit-range split + `BitVec.getLsbD_of_ge`.
2. **`read_ram` / `sail_mem_read`** ⇒ wrap (1) (both `@[simp_sail]`, near-definitional).
3. **`pmpCheck_machine_off`**: 16 pmpcfg OFF + Machine ⇒ `none`. The 16-iteration loop needs an invariant or `decide`-style unfold over the concrete range `[0:15]`.
4. **`pmaCheck_region`**: region membership + readable + aligned ⇒ `none`.
5. **`phys_access_check`** ⇒ combine 3+4 ⇒ `none`; then `checked_mem_read` not-MMIO ⇒ `read_ram`.
6. ✅ **DONE (commit `274dfa8e4`)** — `translateAddr_bare` in `VmemReduction.lean`: Machine + MPRV=0 ⇒ `.ok (Ok (Physaddr (zero_extend 64 vaddr), PBMT_PMA, ())) s`, no state change. EStateM `.ok` form. Recipe: `unfold translateAddr; simp +decide [SailME.run, PreSail.PreSailME.run, effectivePrivilege, translationMode, is_shadow_stack_access, PreSail.readReg, <reg hyps>, <EStateM/ExceptT/liftM plumbing — see runSail_jump_to set>]`. `+decide` is essential (derived-BEq `==` won't fire via `beq_self_eq_true`); `open Out` for the `physaddr.Physaddr`/`page_based_mem_type.PBMT_PMA` constructors.
   - ✅ **DONE (commit `41bf9ae0b`)** — generic `forIn'_noop` invariant in `VmemReduction.lean` (read-only no-op body ⇒ `IntRange.forIn'` returns init, state unchanged), proven via `IntRange.forIn'.loop.induct`. Axioms `{propext, Quot.sound}`. **Stated for the SailM monad.**
   - ⚠ **pmpCheck BLOCKER:** its loop is `forIn … inside ExceptT.run` = the **SailME** monad (`ExceptT _ SailM`), so `forIn'_noop` does not apply as-is. NEXT: a SailME/ExceptT variant of `forIn'_noop` (or reduce through `ExceptT.run`/`SailME.run` to expose the SailM loop first). pmpCheck body is a no-op when every cfg A-field is OFF (`pmpMatchAddr` → `PMP_NoMatch`; `pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = .OFF`).
7. **`untilFuelM` single-iteration**: `split_misaligned` = `(1,8)` ⇒ loop body runs once, `finished := true`.
8. **`vmem_read_addr` / `vmem_read` / `execute_LOAD` top**: chain 1–7, plus the top `assert (8 ≤ xlen_bytes)` (xlen_bytes=8) and `get_transformed_data_addr` (default `ext_data_get_addr` = `Ext_DataAddr_OK (Virtaddr (rX[rs1]+offset))`, cannot error).

Then `ld_sail_equiv` (no `h_exec`) = chain + `wX_bits` + rebuild `StateRel` (reuse
`reg_agree_after_insert` from ALUProofs; mem unchanged). STORE is the mirror via
`write_ram`/`writeBytes` + `mem_write_value`/`checked_mem_write` (note STORE also calls
`mem_write_ea` first — `Mem.lean:448`).

**Suggested home:** a new `EvmAsm/Rv64/SailEquiv/VmemReduction.lean` for lemmas 1–8, then
rewrite `MemProofs.lean` to consume them. Consider a `BareModeInv (sSail)` structure
bundling preconditions 1–4 (+6's region facts), reused across all 11 mem lemmas.

## After memory: fold all tiers into one theorem

Define a strengthened invariant `StateRelFull` (= `StateRel` + PC agreement + misa
present + …) and a per-instruction side-condition predicate (branch alignment, mem
bundle). Then `step_execute_sail_sim` over all 49 `simulable` instrs, dispatching to:
the 29 unconditional lemmas, the 9 control-flow lemmas (BranchProofs/ALUProofs, under
`StateRelFull` + alignment), and the 11 new unconditional-modulo-bundle mem lemmas.
`Instr.simulableUncond` in `StepSim.lean` generalizes to `Instr.simulable` (drop only
the 6 system/pseudo).

## Proven commands

```bash
lake build EvmAsm
# axiom check (scratch imports StepSim + #print axioms; NO 2>/dev/null — guardrail hook)
lake env lean /path/to/AxCheck.lean
# diagnostic: see the un-reduced vmem residual
#   simp only [runSail, execute_LOAD, vmem_read, vmem_read_addr, simp_sail, bind, EStateM.bind, pure]
```

## Bead tree

```
sail-zkvm-integration (parent)
├─ p2-foundation-migration       ✅ DONE
├─ p2.5-trust-hygiene            ✅ DONE
├─ p4-consolidated-sim-theorem   🟡 PARTIAL — 29 unconditional DONE (StepSim.lean); control-flow + memory tiers remain
│  ├─ width-bug-fix              ✅ DONE (699e9f038)
│  ├─ mem-h_exec-discharge       ← NEXT (this doc; ~6–8 reduction lemmas + bundle)
│  └─ strengthened-invariant     (after mem: StateRelFull + all-49 step_execute_sail_sim)
├─ p6-gates-and-ledger           (check-forbidden-tactics/-axioms/-sail-pin; closes F3)
├─ p3-differential-testing       (blocked on Sail toolchain)
└─ p5-full-rv64im-coverage       (12 word-ops; lemmas-only)
```
