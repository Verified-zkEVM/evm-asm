/-
  EvmAsm.Rv64.SailEquiv.RunInv

  The **run-level** (fetch-boundary) simulation invariant and the side-condition
  ingredients that discharge the per-instruction Sail obligations from it.

  The step capstones in `StepProofs`/`StepSim` all take a `nextPC = pc + 4`
  hypothesis and produce a post-state in which `nextPC` still holds the *branch
  target*, so `StateRelPC` alone is not a loop invariant.  In real Sail the
  `nextPC := PC + 4` default is re-installed by **fetch**, once per step.  The
  invariant below therefore deliberately carries **no** `nextPC` fact; the
  fetch-side default is modelled explicitly by `SailEquiv.sailStep` (see
  `StepRun.lean`).

  What `RunInv` does carry, beyond `StateRelPC`, is exactly the set of
  access-independent platform facts that the memory/control-flow reductions
  consume: `misa` readability, a bare-mode machine with the initializer PMA
  table, HTIF disabled, and byte-presence of the guest's memory window.
-/

import EvmAsm.Rv64.SailEquiv.VmemConstruction
import EvmAsm.Rv64.Execution

open Out.Functions
open Sail

namespace EvmAsm.Rv64.SailEquiv

-- ============================================================================
-- The run-level invariant
-- ============================================================================

/-- **Run-level (fetch-boundary) simulation invariant.**

    `StateRelPC` (registers, memory, committed `PC`) plus the access-independent
    platform facts an instruction step needs:

    * `misa_present` — `jump_to` reads `misa` to decide whether `Zca` allows a
      2-byte-aligned target;
    * `bare` — a `BareModeInv` (Machine privilege, `MPRV = 0`, pointer masking
      off, all PMP entries `OFF`) whose PMA table is the one installed by
      `sail_model_init`, with `mseccfg.MLPE = 0`;
    * `htif_off` — the HTIF `tohost` window is unmapped, so no access is ever
      diverted to the host interface;
    * `mem_present` — every byte of the guest window `[lo, hi)` is backed in the
      Sail byte memory (Sail loads `.error` on absent bytes).

    Deliberately does **not** carry a `nextPC` fact: Sail's fetch re-defaults
    `nextPC := PC + 4` every step, which `SailEquiv.sailStep` models. -/
structure RunInv (lo hi : Nat) (sRv : MachineState) (sSail : SailState) : Prop
    extends StateRelPC sRv sSail where
  /-- `misa` is readable, as `jump_to`/`currentlyEnabled Ext_C` require. -/
  misa_present : ∃ v, sSail.regs.get? Register.misa = some v
  /-- The machine is in bare mode with the initializer's PMA region table and
      pointer-masking-on-landing-pads disabled. -/
  bare : ∃ bm : BareModeInv sSail,
    bm.regions = sailInitPmaRegions ∧ _get_Seccfg_MLPE bm.msec = 0#1
  /-- The HTIF `tohost` base is unmapped. -/
  htif_off : sSail.regs.get? Register.htif_tohost_base = some none
  /-- Every byte of the guest window `[lo, hi)` is present in Sail memory. -/
  mem_present : MemPresent lo hi sSail.mem

/-- Writing `nextPC` preserves the run-level invariant: `nextPC` is not one of
    the registers `RunInv` constrains.  This is the step taken by the modelled
    fetch (`nextPC := PC + 4`). -/
theorem RunInv.insert_nextPC {lo hi : Nat} {sRv : MachineState} {sSail : SailState}
    (h : RunInv lo hi sRv sSail) (v : BitVec 64) :
    RunInv lo hi sRv { sSail with regs := sSail.regs.insert Register.nextPC v } := by
  obtain ⟨bm, hregions, hmlpe⟩ := h.bare
  obtain ⟨mv, hmv⟩ := h.misa_present
  have fr : PlatformFrame sSail { sSail with regs := sSail.regs.insert Register.nextPC v } :=
    platformFrame_insert_nextPC _ _
  refine
    { toStateRel := ⟨fun r => ?_, fun a ha => h.mem_agree a ha⟩
      pc_agree := ?_
      misa_present := ⟨mv, fr.misa_eq.trans hmv⟩
      bare := ⟨bm.transport fr, by simpa using hregions, by simpa using hmlpe⟩
      htif_off := fr.htif_eq.trans h.htif_off
      mem_present := MemPresent.of_frame fr h.mem_present }
  · have ha := h.reg_agree r
    cases r <;> simpa [sailRegVal, Std.ExtDHashMap.get?_insert] using ha
  · simpa [Std.ExtDHashMap.get?_insert] using h.pc_agree

/-- **Re-establish the run-level invariant after a step.** Everything `RunInv`
    adds on top of `StateRelPC` is pinned (or made monotone) by a
    `PlatformFrame`, so given the frame across the step and the fresh
    `StateRelPC` at the post-state, the whole invariant transports. -/
theorem RunInv.reestablish {lo hi : Nat} {sRv sRv' : MachineState} {sSail sSail' : SailState}
    (h : RunInv lo hi sRv sSail) (fr : PlatformFrame sSail sSail')
    (hrel : StateRelPC sRv' sSail') : RunInv lo hi sRv' sSail' := by
  obtain ⟨bm, hregions, hmlpe⟩ := h.bare
  obtain ⟨mv, hmv⟩ := h.misa_present
  exact
    { toStateRelPC := hrel
      misa_present := ⟨mv, fr.misa_eq.trans hmv⟩
      bare := ⟨bm.transport fr, by simpa using hregions, by simpa using hmlpe⟩
      htif_off := fr.htif_eq.trans h.htif_off
      mem_present := MemPresent.of_frame fr h.mem_present }

/-- Pull a concrete byte out of the presence invariant. -/
theorem RunInv.byte_present {lo hi : Nat} {sRv : MachineState} {sSail : SailState}
    (h : RunInv lo hi sRv sSail) {a : Nat} (h1 : lo ≤ a) (h2 : a < hi) :
    ∃ b, sSail.mem.get? a = some b :=
  Option.isSome_iff_exists.mp (h.mem_present a h1 h2)

-- ============================================================================
-- Alignment: Rv64 `% w = 0` → Sail `is_aligned_*`
-- ============================================================================

/-- A Sail virtual-address alignment fact from an ordinary `Nat` divisibility
    fact. Inverts the `halign8` derivation inlined in `ld_sail_equiv`. -/
theorem is_aligned_vaddr_of_toNat_mod {a : BitVec 64} {w : Nat} (h : a.toNat % w = 0) :
    is_aligned_vaddr (virtaddr.Virtaddr a) w = true := by
  unfold is_aligned_vaddr Sail.BitVec.toNatInt
  rw [beq_iff_eq]
  exact Int.ofNat_inj.mpr h

/-- A Sail physical-address alignment fact from an ordinary `Nat` divisibility
    fact. -/
theorem is_aligned_paddr_of_toNat_mod {a : physaddrbits} {w : Nat} (h : a.toNat % w = 0) :
    is_aligned_paddr (physaddr.Physaddr a) w = true := by
  unfold is_aligned_paddr Sail.BitVec.toNatInt
  rw [beq_iff_eq]
  exact Int.ofNat_inj.mpr h

-- ============================================================================
-- MMIO windows: RAM-zone addresses miss CLINT, the signature window and HTIF
-- ============================================================================

/-- An address at or above `RAM_MEM_START` is outside the CLINT window
    (`[0x02000000, 0x020C0000)`), for any access width. -/
theorem within_clint_ram {a : physaddrbits} {w : Nat} (s : SailState)
    (hlo : RAM_MEM_START ≤ a.toNat) :
    (within_clint (physaddr.Physaddr a) w) s = .ok false s := by
  have h1 : BitVec.toNat plat_clint_base = 33554432 := by decide
  have h2 : BitVec.toNat plat_clint_size = 786432 := by decide
  simp only [RAM_MEM_START] at hlo
  simp only [within_clint, plat_have_clint, Out.Functions.not, Bool.not_true,
    Bool.false_eq_true, if_false, Sail.BitVec.toNatInt]
  show EStateM.Result.ok _ s = _
  congr 1
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, h1, h2,
    Int.ofNat_eq_natCast]
  right
  omega

/-- An address at or above `RAM_MEM_START` is outside the signature window
    (`[0x0C000000, 0x0C000020)`), for any access width. -/
theorem within_sig_ram {a : physaddrbits} {w : Nat} (s : SailState)
    (hlo : RAM_MEM_START ≤ a.toNat) :
    (within_sig (physaddr.Physaddr a) w) s = .ok false s := by
  have h1 : BitVec.toNat plat_sig_base = 201326592 := by decide
  have h2 : BitVec.toNat plat_sig_size = 32 := by decide
  simp only [RAM_MEM_START] at hlo
  simp only [within_sig, plat_have_sig, Out.Functions.not, Bool.not_true,
    Bool.false_eq_true, if_false, Sail.BitVec.toNatInt]
  show EStateM.Result.ok _ s = _
  congr 1
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, h1, h2,
    Int.ofNat_eq_natCast]
  right
  omega

/-- With the HTIF `tohost` base unmapped, no address is HTIF-writable. -/
theorem within_htif_writable_none {a : physaddrbits} {w : Nat} {s : SailState}
    (h : s.regs.get? Register.htif_tohost_base = some none) :
    (within_htif_writable (physaddr.Physaddr a) w) s = .ok false s := by
  simp only [within_htif_writable, PreSail.readReg, h, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]
  rfl

/-- With the HTIF `tohost` base unmapped, no address is HTIF-readable. -/
theorem within_htif_readable_none {a : physaddrbits} {w : Nat} {s : SailState}
    (h : s.regs.get? Register.htif_tohost_base = some none) :
    (within_htif_readable (physaddr.Physaddr a) w) s = .ok false s :=
  within_htif_writable_none h

-- ============================================================================
-- PMA lookup: symbolic RAM addresses land in the main-memory region
-- ============================================================================

/-- `to_bits` of a `Nat` is its 64-bit truncation. -/
theorem to_bits_64_toNat (w : Nat) :
    (to_bits (l := 64) w : BitVec 64).toNat = w % 2 ^ 64 := by
  simp [to_bits, get_slice_int]

/-- `range_subset` in `Nat` terms.  The Sail definition rebases both ranges at
    `b_begin` and compares unsigned; `(b_begin + b_size) - b_begin` is just
    `b_size`. -/
theorem range_subset_toNat {n : Nat} (ab as bb bs : BitVec n) :
    range_subset ab as bb bs
      = (decide ((ab - bb).toNat ≤ bs.toNat)
          && (decide ((ab + as - bb).toNat ≤ bs.toNat)
              && decide ((ab - bb).toNat ≤ (ab + as - bb).toNat))) := by
  have hbb : bb + bs - bb = bs := by rw [BitVec.add_comm, BitVec.add_sub_cancel]
  simp only [range_subset, zopz0zIzJ_u, Sail.BitVec.toNatInt, hbb,
    Int.ofNat_eq_natCast, Nat.cast_le]

/-- **Symbolic PMA lookup.** Any access wholly inside `[0x80000000, 0x100000000)`
    matches the initializer's main-memory region: it is not a subrange of either
    I/O region (both live below `0x12000000`), and it *is* a subrange of main
    memory.  Generalises the concrete-address `sailRamWitness_matching_pma`. -/
theorem matching_pma_region_mainMemory {a : BitVec 64} {w : Nat}
    (hlo : 2147483648 ≤ a.toNat) (hhi : a.toNat + w ≤ 4294967296) :
    matching_pma_region sailInitPmaRegions (physaddr.Physaddr a) w
      = some sailInitMainMemoryRegion := by
  have hbase :
      (zero_extend (m := 64) (bits_of_physaddr (physaddr.Physaddr a)) : BitVec 64) = a := by
    simp [zero_extend, Sail.BitVec.zeroExtend, bits_of_physaddr]
  have hlt : a.toNat < 2 ^ 64 := a.isLt
  have hwlt : (to_bits (l := 64) w : BitVec 64).toNat = w := by
    rw [to_bits_64_toNat]; omega
  unfold matching_pma_region
  rw [hbase]
  simp only [sailInitPmaRegions, matching_pma_region_bits_range, range_subset_toNat,
    sailInitReadOnlyIoRegion, sailInitIoRegion, sailInitMainMemoryRegion,
    BitVec.toNat_sub, BitVec.toNat_add, hwlt, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod]
  split_ifs with h1 h2 h3
  · exfalso; simp only [Bool.and_eq_true, decide_eq_true_eq] at h1; omega
  · exfalso; simp only [Bool.and_eq_true, decide_eq_true_eq] at h2; omega
  · rfl
  · exact absurd (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega) h3

/-- **Every access-local Sail obligation for one in-window memory access.**
    Bundles the alignment, PMA-membership and MMIO-exclusion facts that the
    `vmem_read`/`vmem_write` reductions consume, discharged from the run-level
    invariant plus the caller's window bounds. -/
theorem RunInv.access_ok {lo hi : Nat} {sRv : MachineState} {sSail : SailState}
    (h : RunInv lo hi sRv sSail) (hlo : RAM_MEM_START ≤ lo) (hhi : hi ≤ RAM_MEM_END)
    {a : Word} {w : Nat} (ha1 : lo ≤ a.toNat) (ha2 : a.toNat + w ≤ hi)
    (halign : a.toNat % w = 0)
    (bm : BareModeInv sSail) (hreg : bm.regions = sailInitPmaRegions) :
    is_aligned_vaddr (virtaddr.Virtaddr a) w = true ∧
    matching_pma_region bm.regions (physaddr.Physaddr a) w = some sailInitMainMemoryRegion ∧
    is_aligned_paddr (physaddr.Physaddr a) w = true ∧
    (within_clint (physaddr.Physaddr a) w) sSail = .ok false sSail ∧
    (within_sig (physaddr.Physaddr a) w) sSail = .ok false sSail ∧
    (within_htif_writable (physaddr.Physaddr a) w) sSail = .ok false sSail ∧
    (within_htif_readable (physaddr.Physaddr a) w) sSail = .ok false sSail := by
  have hram : RAM_MEM_START ≤ a.toNat := le_trans hlo ha1
  refine ⟨is_aligned_vaddr_of_toNat_mod halign, ?_, is_aligned_paddr_of_toNat_mod halign,
    within_clint_ram _ hram, within_sig_ram _ hram,
    within_htif_writable_none h.htif_off, within_htif_readable_none h.htif_off⟩
  rw [hreg]
  refine matching_pma_region_mainMemory ?_ ?_
  · simp only [RAM_MEM_START] at hram; omega
  · simp only [RAM_MEM_END] at hhi; omega

-- ============================================================================
-- Why `JALR` is out of scope: the vendored `update_elp_state` always faults
-- ============================================================================

/-- The vendored `currentlyEnabled` has **no arm for `Ext_Zicsr`**: the query
    falls through to the generated catch-all, which asserts `false` and throws.
    (This is a gap in the vendored Sail→Lean extraction, not a modelling choice
    of ours.) -/
theorem currentlyEnabled_Ext_Zicsr_error (s : SailState) :
    ∃ e, currentlyEnabled extension.Ext_Zicsr s = .error e s := by
  rw [currentlyEnabled.eq_def]
  simp only []
  exact ⟨_, rfl⟩

/-- `Ext_Zicfilp`'s enable test begins by querying `Ext_Zicsr`, so it inherits
    the fault. -/
theorem currentlyEnabled_Ext_Zicfilp_error (s : SailState) :
    ∃ e, currentlyEnabled extension.Ext_Zicfilp s = .error e s := by
  obtain ⟨e, he⟩ := currentlyEnabled_Ext_Zicsr_error s
  rw [currentlyEnabled.eq_def]
  simp only []
  simp only [bind, EStateM.bind, he]
  exact ⟨e, rfl⟩

/-- Consequently `update_elp_state` — the first action of the vendored
    `execute_JALR` — **never** returns normally, in any state.  This is why
    `JALR` is excluded from the run-level simulation theorem
    (`Instr.runSimulable` in `StepRun.lean`): the `h_elp` premise of
    `jalr_sail_equiv` / `instrSideCond (.JALR ..)` is unsatisfiable, so no
    caller can supply it.  Fixing this needs a vendored-model update, not a
    proof. -/
theorem update_elp_state_error (rs1 : regidx) (s : SailState) :
    ∃ e, update_elp_state rs1 s = .error e s := by
  obtain ⟨e, he⟩ := currentlyEnabled_Ext_Zicfilp_error s
  rw [update_elp_state.eq_def]
  simp only [bind, EStateM.bind, he]
  exact ⟨e, rfl⟩

-- ============================================================================
-- Toy-side per-step side conditions
-- ============================================================================

/-- **Toy-state-only obligations for one step**, i.e. the facts about the *Rv64*
    state at `s` that `step s` does not itself guarantee but that the Sail model
    needs:

    * control transfers must land 4-byte aligned (Sail `jump_to` faults
      otherwise; the toy `execInstrBr` happily writes an unaligned `pc`);
    * every memory access must sit wholly inside the caller's window
      `[lo, hi)`.

    The `addr.toNat + w ≤ hi` form is deliberate.  The toy `isValid*Access`
    predicates check only the access's **start** address (a known extent hazard,
    GH #10560), so carrying the end bound here keeps the run theorem immune to
    that gap. -/
def stepSideCond (lo hi : Nat) (s : MachineState) : Prop :=
  match s.code s.pc with
  | some (.BEQ _ _ off) => (s.pc + signExtend13 off) &&& 3 = 0
  | some (.BNE _ _ off) => (s.pc + signExtend13 off) &&& 3 = 0
  | some (.BLT _ _ off) => (s.pc + signExtend13 off) &&& 3 = 0
  | some (.BGE _ _ off) => (s.pc + signExtend13 off) &&& 3 = 0
  | some (.BLTU _ _ off) => (s.pc + signExtend13 off) &&& 3 = 0
  | some (.BGEU _ _ off) => (s.pc + signExtend13 off) &&& 3 = 0
  | some (.JAL _ off) => (s.pc + signExtend21 off) &&& 3 = 0
  | some (.JALR _ rs1 off) => ((s.getReg rs1 + signExtend12 off) &&& ~~~1#64) &&& 3 = 0
  | some (.LD _ rs1 off) =>
      lo ≤ (s.getReg rs1 + signExtend12 off).toNat ∧
      (s.getReg rs1 + signExtend12 off).toNat + 8 ≤ hi
  | some (.SD rs1 _ off) =>
      lo ≤ (s.getReg rs1 + signExtend12 off).toNat ∧
      (s.getReg rs1 + signExtend12 off).toNat + 8 ≤ hi
  | some (.LW _ rs1 off) =>
      lo ≤ (s.getReg rs1 + signExtend12 off).toNat ∧
      (s.getReg rs1 + signExtend12 off).toNat + 4 ≤ hi
  | some (.LWU _ rs1 off) =>
      lo ≤ (s.getReg rs1 + signExtend12 off).toNat ∧
      (s.getReg rs1 + signExtend12 off).toNat + 4 ≤ hi
  | some (.SW rs1 _ off) =>
      lo ≤ (s.getReg rs1 + signExtend12 off).toNat ∧
      (s.getReg rs1 + signExtend12 off).toNat + 4 ≤ hi
  | some (.LH _ rs1 off) =>
      lo ≤ (s.getReg rs1 + signExtend12 off).toNat ∧
      (s.getReg rs1 + signExtend12 off).toNat + 2 ≤ hi
  | some (.LHU _ rs1 off) =>
      lo ≤ (s.getReg rs1 + signExtend12 off).toNat ∧
      (s.getReg rs1 + signExtend12 off).toNat + 2 ≤ hi
  | some (.SH rs1 _ off) =>
      lo ≤ (s.getReg rs1 + signExtend12 off).toNat ∧
      (s.getReg rs1 + signExtend12 off).toNat + 2 ≤ hi
  | some (.LB _ rs1 off) =>
      lo ≤ (s.getReg rs1 + signExtend12 off).toNat ∧
      (s.getReg rs1 + signExtend12 off).toNat + 1 ≤ hi
  | some (.LBU _ rs1 off) =>
      lo ≤ (s.getReg rs1 + signExtend12 off).toNat ∧
      (s.getReg rs1 + signExtend12 off).toNat + 1 ≤ hi
  | some (.SB rs1 _ off) =>
      lo ≤ (s.getReg rs1 + signExtend12 off).toNat ∧
      (s.getReg rs1 + signExtend12 off).toNat + 1 ≤ hi
  | _ => True

end EvmAsm.Rv64.SailEquiv
