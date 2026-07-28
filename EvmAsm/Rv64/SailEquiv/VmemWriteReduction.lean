/-
  EvmAsm.Rv64.SailEquiv.VmemWriteReduction

  Store-side (Tier B) mirror of the bare-mode load reduction chain in
  `VmemReduction.lean` / `VmemReductionN.lean`: the building blocks behind the four
  unconditional store capstones (`SD / SW / SH / SB`, `execute_STORE` widths 8/4/2/1)
  in `VmemReductionStores.lean`.  (These originally discharged the deferred
  `MemProofs` store stubs; no stubs remain.)

  Three ingredient groups:

  * **Access-type twins** of the Tier-A leaves. `translateAddr` / `get_pmlen` /
    `transform_effective_address` / `pmpCheck` / `pmaCheck` / `within_mmio_*` were stated
    for `Load Data`; a `Store Data` access takes the same bare-mode path (the access type
    only selects the PMA permission bit — `writable` instead of `readable` — and the
    faulting arms, which bare mode never reaches). Same proof recipes, verbatim.
  * **The physical write chain** (`writeBytes → write_ram → checked_mem_write →
    mem_write_value`). Unlike a read, the write *changes* the Sail state: `writeByte` is
    `mem.insert`, so a width-`w` store at `a` ends in the canonical insert chain
    `((mem.insert a v₀).insert (a+1) v₁)…` with `vᵢ = data.extractLsb' (8*i) 8`.
    `writeByte` never fails, so — unlike loads — stores need **no byte-presence
    hypotheses**.
  * **The `vmem_write_addr` / `vmem_write` loop reductions** (fuel-1 aligned loop,
    mirroring `vmem_read_addr_load_core` / `vmem_read_load_N`).

  The `StateRel` rebuild bridges (`reconstructDword` over the insert chain) and the four
  capstone `s{d,w,h,b}_sail_equiv` theorems live in `VmemReductionStores.lean`.
-/

import EvmAsm.Rv64.SailEquiv.VmemReductionN

open Out
open Out.Functions
open Sail
open PreSail

namespace EvmAsm.Rv64.SailEquiv

-- ============================================================================
-- Access-type twins of the Tier-A bare-mode leaves (Store Data)
-- ============================================================================

/-- **`translateAddr` bare-mode no-op, `Store Data` twin.** Same identity reduction as
    `translateAddr_bare`: a store is not a shadow-stack access, so bare mode returns the
    virtual address as physical unchanged. -/
theorem translateAddr_bare_store (s : SailState) (vAddr : virtaddr) (mst : BitVec 64)
    (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (h_mst : s.regs.get? Register.mstatus = some mst)
    (h_mprv : _get_Mstatus_MPRV mst = 0#1) :
    translateAddr vAddr (MemoryAccessType.Store mem_payload.Data) s
      = .ok (Ok ((physaddr.Physaddr (zero_extend (m := 64) (bits_of_virtaddr vAddr))),
                 page_based_mem_type.PBMT_PMA, init_ext_ptw)) s := by
  unfold translateAddr
  simp +decide [SailME.run, PreSail.PreSailME.run, effectivePrivilege, translationMode,
    is_shadow_stack_access, PreSail.readReg, h_priv, h_mst, h_mprv,
    pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get,
    MonadLift.monadLift, monadLift, liftM, Functor.map,
    ExceptT.run, ExceptT.mk, ExceptT.pure, ExceptT.bind, ExceptT.bindCont, ExceptT.lift,
    EStateM.map]

/-- **`get_pmlen` zero in Machine mode, `Store Data` twin.** A data store is
    PMM-applicable exactly like a data load; with `mseccfg.PMM = 0` the masking length
    is `0`. -/
theorem get_pmlen_machine_zero_store (s : SailState) (mst msec : BitVec 64)
    (h_mst : s.regs.get? Register.mstatus = some mst)
    (h_sec : s.regs.get? Register.mseccfg = some msec)
    (h_pmm : _get_Seccfg_PMM msec = 0#2) :
    (get_pmlen (MemoryAccessType.Store mem_payload.Data) Privilege.Machine) s = .ok 0 s := by
  unfold get_pmlen is_pmm_applicable get_pmm
  simp +decide [PreSail.readReg, h_mst, h_sec, h_pmm, pmm_mode_backwards,
    pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get, bne]

/-- **`transform_effective_address` bare-mode identity, `Store Data` twin.** -/
theorem transform_effective_address_bare_store (s : SailState) (vaddr : virtaddr)
    (mst msec : BitVec 64)
    (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (h_mst : s.regs.get? Register.mstatus = some mst)
    (h_mprv : _get_Mstatus_MPRV mst = 0#1)
    (h_sec : s.regs.get? Register.mseccfg = some msec)
    (h_pmm : _get_Seccfg_PMM msec = 0#2) :
    (transform_effective_address vaddr (MemoryAccessType.Store mem_payload.Data)) s
      = .ok (pm_transform_PA vaddr 0) s := by
  unfold transform_effective_address
  sail_reduce [h_priv, h_mst, effectivePrivilege_machine s _ mst _ h_mprv,
    get_pmlen_machine_zero_store s mst msec h_mst h_sec h_pmm,
    translationMode_machine s, if_true, Int.toNat_zero]

/-- **`pmpCheck` permits a store in Machine mode with all PMP entries OFF.** Twin of
    `pmpCheck_machine_off`: the 16-entry scan is the same read-only no-op (the access
    type appears only in the unreachable fault arms), and the trailing
    `priv == Machine` guard yields `none`. -/
theorem pmpCheck_machine_off_store (addr : physaddr) (width : Nat) (s : SailState)
    (cfgs : Vector (BitVec 8) 64) (pmpaddrs : Vector (BitVec 64) 64)
    (h_cfg : s.regs.get? Register.pmpcfg_n = some cfgs)
    (h_addr : s.regs.get? Register.pmpaddr_n = some pmpaddrs)
    (h_off : ∀ i : Nat,
      pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (cfgs[i]!)) = PmpAddrMatchType.OFF) :
    pmpCheck addr width (MemoryAccessType.Store mem_payload.Data) Privilege.Machine s
      = .ok none s := by
  unfold pmpCheck
  simp +decide only [SailME.run, PreSail.PreSailME.run, sys_pmp_count,
    bind, EStateM.bind,
    ExceptT.run, ExceptT.mk, ExceptT.bind]
  simp only [if_false, if_true]
  rw [forIn]
  simp only [instForInOfForIn', EStateM.bind]
  rw [forIn'_noop_except _ () s _ ?hf]
  case hf =>
    intro i hi b
    have hmatch : ∀ (pa prev : BitVec 64),
        (pmpMatchAddr addr (to_bits width) cfgs[i]! pa prev) s
          = .ok pmpAddrMatch.PMP_NoMatch s := by
      intro pa prev
      exact pmpMatchAddr_off s addr (to_bits width) pa prev cfgs[i]! (h_off i.toNat)
    split
    all_goals
      simp +decide only [PreSail.readReg, h_cfg,
        pmpReadAddrReg_noop s _ cfgs pmpaddrs h_cfg h_addr,
        hmatch,
        pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
        get, MonadState.get, getThe, MonadStateOf.get,
        MonadLift.monadLift, monadLift, liftM, Functor.map,
        ExceptT.mk, ExceptT.pure, ExceptT.bindCont, ExceptT.lift,
        EStateM.map]
  rfl

/-- **`pmaCheck` permits an aligned writable store.** Twin of `pmaCheck_load_ok` with the
    `Store Data` arm selecting the region's `writable` attribute; returns
    `Ok alignedAccessInfo` (permitted, unsplittable), state untouched. -/
theorem pmaCheck_store_ok (paddr : physaddr) (width : Nat) (s : SailState)
    (regions : List PMA_Region) (region : PMA_Region)
    (h_reg : s.regs.get? Register.pma_regions = some regions)
    (h_match : matching_pma_region regions paddr width = some region)
    (h_write : region.attributes.writable = true)
    (h_align : is_aligned_paddr paddr width = true) :
    pmaCheck paddr width (MemoryAccessType.Store mem_payload.Data) page_based_mem_type.PBMT_PMA false s
      = .ok (Ok alignedAccessInfo) s := by
  unfold pmaCheck mag_pma_check is_mag_applicable_access
  simp +decide [alignedAccessInfo, SailME.run, PreSail.PreSailME.run,
    PreSail.readReg, h_reg, h_match, override_PMA, h_align, h_write,
    pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get,
    ExceptT.run, ExceptT.mk, ExceptT.pure, ExceptT.bind, ExceptT.bindCont, ExceptT.lift,
    MonadLift.monadLift, monadLift, liftM, Functor.map, EStateM.map,
    Sail.assert, PreSail.assert]

/-- **`check_pma_with_pmp_priority` permits an aligned writable store.** The PMA check
    succeeds first, so the PMP fallback is never consulted (any privilege). Twin of
    `check_pma_with_pmp_priority_load_ok`. -/
theorem check_pma_with_pmp_priority_store_ok (paddr : physaddr) (width : Nat) (s : SailState)
    (priv : Privilege) (regions : List PMA_Region) (region : PMA_Region)
    (h_reg : s.regs.get? Register.pma_regions = some regions)
    (h_match : matching_pma_region regions paddr width = some region)
    (h_write : region.attributes.writable = true)
    (h_align : is_aligned_paddr paddr width = true) :
    check_pma_with_pmp_priority (MemoryAccessType.Store mem_payload.Data)
      page_based_mem_type.PBMT_PMA priv paddr width false s
      = .ok (Ok alignedAccessInfo) s := by
  unfold check_pma_with_pmp_priority
  simp only [bind, EStateM.bind,
    pmaCheck_store_ok paddr width s regions region h_reg h_match h_write h_align,
    pure, EStateM.pure]

/-- **Leaf #10 — `within_mmio_writable` is `false` off the MMIO ranges.** Mirror of
    `within_mmio_readable_ram`: with RVFI off the check is
    `within_clint || within_sig || (within_htif_writable && width ≤ 8)`; all three
    sub-checks `false` at this address gives `false`, state untouched — so
    `checked_mem_write` takes the `write_ram` branch. -/
theorem within_mmio_writable_ram (addr : physaddr) (width : Nat) (s : SailState)
    (hclint : (within_clint addr width) s = .ok false s)
    (hsig : (within_sig addr width) s = .ok false s)
    (hhtif : (within_htif_writable addr width) s = .ok false s) :
    (within_mmio_writable addr width) s = .ok false s := by
  unfold within_mmio_writable
  simp only [get_config_rvfi, Bool.false_eq_true, if_false,
    bind, EStateM.bind, hclint, hsig, hhtif,
    pure, EStateM.pure, Bool.false_or, Bool.false_and]

/-- **`phys_access_check` permits a bare-mode aligned writable store.** Composes the
    store-side `pmpCheck` `none` result with the `pmaCheck` `Ok alignedAccessInfo`. -/
theorem phys_access_check_store_ok (addr : BitVec 64) (width : Nat) (s : SailState)
    (cfgs : Vector (BitVec 8) 64) (pmpaddrs : Vector (BitVec 64) 64)
    (regions : List PMA_Region) (region : PMA_Region)
    (h_cfg : s.regs.get? Register.pmpcfg_n = some cfgs)
    (h_addr : s.regs.get? Register.pmpaddr_n = some pmpaddrs)
    (h_off : ∀ i : Nat,
      pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (cfgs[i]!)) = PmpAddrMatchType.OFF)
    (h_reg : s.regs.get? Register.pma_regions = some regions)
    (h_match : matching_pma_region regions (physaddr.Physaddr addr) width = some region)
    (h_write : region.attributes.writable = true)
    (h_align : is_aligned_paddr (physaddr.Physaddr addr) width = true) :
    phys_access_check (MemoryAccessType.Store mem_payload.Data) page_based_mem_type.PBMT_PMA
      Privilege.Machine (physaddr.Physaddr addr) width false s
      = .ok (Ok alignedAccessInfo) s := by
  unfold phys_access_check
  simp only [bind, EStateM.bind,
    pmpCheck_machine_off_store (physaddr.Physaddr addr) width s cfgs pmpaddrs h_cfg h_addr h_off,
    pmaCheck_store_ok (physaddr.Physaddr addr) width s regions region h_reg h_match h_write h_align,
    pure, EStateM.pure]

-- ============================================================================
-- The physical write: writeBytes → canonical insert chain
-- ============================================================================

/-- `writeBytes 8` never fails: it inserts the eight little-endian byte slices of `v`
    at `a … a+7` and returns `true`. The insert chain is the canonical (low-to-high)
    order the `List.forM` produces. -/
theorem writeBytes8_raw (s : SailState) (a : Nat) (v : BitVec (8*8)) :
    (writeBytes a v : SailM Bool) s
      = .ok true { s with mem :=
          ((((((((s.mem.insert a (v.extractLsb' 0 8)).insert (a+1) (v.extractLsb' 8 8)).insert
            (a+2) (v.extractLsb' 16 8)).insert (a+3) (v.extractLsb' 24 8)).insert
            (a+4) (v.extractLsb' 32 8)).insert (a+5) (v.extractLsb' 40 8)).insert
            (a+6) (v.extractLsb' 48 8)).insert (a+7) (v.extractLsb' 56 8)) } := rfl

/-- `writeBytes 4`: the four byte slices of `v` at `a … a+3`, returns `true`. -/
theorem writeBytes4_raw (s : SailState) (a : Nat) (v : BitVec (8*4)) :
    (writeBytes a v : SailM Bool) s
      = .ok true { s with mem :=
          ((((s.mem.insert a (v.extractLsb' 0 8)).insert (a+1) (v.extractLsb' 8 8)).insert
            (a+2) (v.extractLsb' 16 8)).insert (a+3) (v.extractLsb' 24 8)) } := rfl

/-- `writeBytes 2`: the two byte slices of `v` at `a`, `a+1`, returns `true`. -/
theorem writeBytes2_raw (s : SailState) (a : Nat) (v : BitVec (8*2)) :
    (writeBytes a v : SailM Bool) s
      = .ok true { s with mem :=
          ((s.mem.insert a (v.extractLsb' 0 8)).insert (a+1) (v.extractLsb' 8 8)) } := rfl

/-- `writeBytes 1`: the single byte `v` at `a`, returns `true`. -/
theorem writeBytes1_raw (s : SailState) (a : Nat) (v : BitVec (8*1)) :
    (writeBytes a v : SailM Bool) s
      = .ok true { s with mem := s.mem.insert a (v.extractLsb' 0 8) } := rfl

-- ============================================================================
-- Full-range `extractLsb` identities (per width; the store's data slice)
-- ============================================================================

/-- `extractLsb 63 0` of a 64-bit value is the value (full-range slice). -/
theorem extractLsb_full64 (x : BitVec 64) : Sail.BitVec.extractLsb x 63 0 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb,
    show i < 64 from by omega]

/-- `extractLsb 31 0` of a 32-bit value is the value. -/
theorem extractLsb_full32 (x : BitVec 32) : Sail.BitVec.extractLsb x 31 0 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb,
    show i < 32 from by omega]

/-- `extractLsb 15 0` of a 16-bit value is the value. -/
theorem extractLsb_full16 (x : BitVec 16) : Sail.BitVec.extractLsb x 15 0 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb,
    show i < 16 from by omega]

/-- `extractLsb 7 0` of an 8-bit value is the value. -/
theorem extractLsb_full8 (x : BitVec 8) : Sail.BitVec.extractLsb x 7 0 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb,
    show i < 8 from by omega]

/-- Loop-shape variants: the `checked_mem_write` loop slices the data as
    `extractLsb data (8*w - 1) 0` with the width expression **inside the type index**,
    so the literal-index lemmas above cannot fire (rewriting `8*w-1` would change the
    type). Stated verbatim per width instead. -/
theorem extractLsb_full_w1 (x : BitVec (8*1)) : Sail.BitVec.extractLsb x (8*1 - 1) 0 = x :=
  extractLsb_full8 x

theorem extractLsb_full_w2 (x : BitVec (8*2)) : Sail.BitVec.extractLsb x (8*2 - 1) 0 = x :=
  extractLsb_full16 x

theorem extractLsb_full_w4 (x : BitVec (8*4)) : Sail.BitVec.extractLsb x (8*4 - 1) 0 = x :=
  extractLsb_full32 x

theorem extractLsb_full_w8 (x : BitVec (8*8)) : Sail.BitVec.extractLsb x (8*8 - 1) 0 = x :=
  extractLsb_full64 x

-- ============================================================================
-- Width-generic write chain (post-write state abstracted)
-- ============================================================================

/-- `write_ram` for a plain width-`w` store with the `writeBytes` result supplied: builds
    the write request, `sail_mem_write` runs `writeBytes` (which succeeds with the given
    post-state), the metadata write is a pure no-op, and `true` is returned. -/
theorem write_ram_plain_store_N (w : Nat) (addr : BitVec 64) (s s' : SailState)
    (data : BitVec (8*w))
    (hwrite : (writeBytes addr.toNat data : SailM Bool) s = .ok true s') :
    (Functions.write_ram write_kind.Write_plain (physaddr.Physaddr addr) w data ()) s
      = .ok true s' := by
  unfold Functions.write_ram Sail.ConcurrencyInterfaceV1.sail_mem_write
    PreSail.ConcurrencyInterfaceV1.sail_mem_write
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  erw [hwrite]
  simp only [EStateM.pure]

/-- `mem_write_ea` for a bare-mode plain (non-release, non-conditional) aligned writable
    store: the effective privilege is Machine, the PMA-with-PMP-priority check passes
    (`Ok alignedAccessInfo`), the single-access loop's `pmpCheck` permits, and
    `write_ram_ea` is a pure no-op. State untouched. (The new model runs the full
    PMA/PMP checks here, so this needs the same bare-mode hypotheses as the write
    itself.) -/
theorem mem_write_ea_plain (addr : BitVec 64) (width : Nat) (s : SailState) (mst : BitVec 64)
    (cfgs : Vector (BitVec 8) 64) (pmpaddrs : Vector (BitVec 64) 64)
    (regions : List PMA_Region) (region : PMA_Region)
    (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (h_mst : s.regs.get? Register.mstatus = some mst)
    (h_mprv : _get_Mstatus_MPRV mst = 0#1)
    (h_cfg : s.regs.get? Register.pmpcfg_n = some cfgs)
    (h_addr : s.regs.get? Register.pmpaddr_n = some pmpaddrs)
    (h_off : ∀ i : Nat,
      pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (cfgs[i]!)) = PmpAddrMatchType.OFF)
    (h_reg : s.regs.get? Register.pma_regions = some regions)
    (h_match : matching_pma_region regions (physaddr.Physaddr addr) width = some region)
    (h_write : region.attributes.writable = true)
    (h_align : is_aligned_paddr (physaddr.Physaddr addr) width = true) :
    (mem_write_ea (physaddr.Physaddr addr) width (MemoryAccessType.Store mem_payload.Data)
      page_based_mem_type.PBMT_PMA false false false) s
      = .ok (Result.Ok ()) s := by
  have hcheck := check_pma_with_pmp_priority_store_ok (physaddr.Physaddr addr) width s
    Privilege.Machine regions region h_reg h_match h_write h_align
  have hsplit := split_misaligned_cannotsplit (physaddr.Physaddr addr) width 0 s
  have hpmp := pmpCheck_machine_off_store (physaddr.Physaddr addr) width s cfgs pmpaddrs
    h_cfg h_addr h_off
  unfold mem_write_ea
  simp +decide only [SailME.run, PreSail.PreSailME.run,
    PreSail.readReg, h_priv, h_mst,
    effectivePrivilege_machine s _ mst _ h_mprv,
    hcheck, alignedAccessInfo, hsplit, misaligned_order_one,
    Int.toNat_one, Int.toNat_zero, untilFuelM_one,
    Sail.assert, PreSail.assert, if_true,
    BitVec.addInt, Int.natCast_zero, Int.zero_mul, Int.mul_zero, Int.zero_add,
    Int.mul_one, ofInt_zero_bv, BitVec.add_zero, add_zero_physaddrbits,
    Int.toNat_natCast, bits_of_physaddr_mk,
    hpmp, write_kind_of_flags, write_ram_ea,
    EStateM.map, bind, EStateM.bind, pure, EStateM.pure, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.lift, ExceptT.pure,
    MonadLift.monadLift, monadLift, liftM, Functor.map]

/-- `checked_mem_write` for a bare-mode aligned writable width-`w` store: the
    PMA-with-PMP-priority check passes (`Ok alignedAccessInfo`), so the access loop runs
    once (`untilFuelM` fuel 1); the per-access `pmpCheck` permits, the address is off the
    writable MMIO ranges (so `write_ram`, not `mmio_write`), the write kind is
    `Write_plain`, the full-width data slice is the data, and `write_ram` lands in the
    post-write state returning `true`. -/
theorem checked_mem_write_store_N (w : Nat) (addr : BitVec 64) (s s' : SailState)
    (data : BitVec (8*w))
    (cfgs : Vector (BitVec 8) 64) (pmpaddrs : Vector (BitVec 64) 64)
    (regions : List PMA_Region) (region : PMA_Region)
    (hwlit : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8)
    (h_cfg : s.regs.get? Register.pmpcfg_n = some cfgs)
    (h_addr : s.regs.get? Register.pmpaddr_n = some pmpaddrs)
    (h_off : ∀ i : Nat,
      pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (cfgs[i]!)) = PmpAddrMatchType.OFF)
    (h_reg : s.regs.get? Register.pma_regions = some regions)
    (h_match : matching_pma_region regions (physaddr.Physaddr addr) w = some region)
    (h_write : region.attributes.writable = true)
    (h_align : is_aligned_paddr (physaddr.Physaddr addr) w = true)
    (hclint : (within_clint (physaddr.Physaddr addr) w) s = .ok false s)
    (hsig : (within_sig (physaddr.Physaddr addr) w) s = .ok false s)
    (hhtif : (within_htif_writable (physaddr.Physaddr addr) w) s = .ok false s)
    (hwrite : (writeBytes addr.toNat data : SailM Bool) s = .ok true s') :
    checked_mem_write (physaddr.Physaddr addr) w data
      (MemoryAccessType.Store mem_payload.Data) page_based_mem_type.PBMT_PMA
      Privilege.Machine () false false false s
      = .ok (Result.Ok true) s' := by
  have hcheck := check_pma_with_pmp_priority_store_ok (physaddr.Physaddr addr) w s
    Privilege.Machine regions region h_reg h_match h_write h_align
  have hsplit := split_misaligned_cannotsplit (physaddr.Physaddr addr) w 0 s
  have hpmp := pmpCheck_machine_off_store (physaddr.Physaddr addr) w s cfgs pmpaddrs
    h_cfg h_addr h_off
  have hmmio := within_mmio_writable_ram (physaddr.Physaddr addr) w s hclint hsig hhtif
  have hwr := write_ram_plain_store_N w addr s s' data hwrite
  unfold checked_mem_write
  simp +decide only [SailME.run, PreSail.PreSailME.run,
    hcheck, alignedAccessInfo, hsplit, misaligned_order_one,
    Int.toNat_one, Int.toNat_zero, untilFuelM_one,
    Sail.assert, PreSail.assert, if_true,
    BitVec.addInt, Int.natCast_zero, Int.zero_mul, Int.mul_zero, Int.zero_add,
    Int.mul_one, ofInt_zero_bv, BitVec.add_zero, add_zero_physaddrbits,
    Int.toNat_natCast, bits_of_physaddr_mk,
    hpmp, hmmio, Bool.false_eq_true, if_false, write_kind_of_flags,
    EStateM.map, bind, EStateM.bind, pure, EStateM.pure,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.lift, ExceptT.pure,
    MonadLift.monadLift, monadLift, liftM, Functor.map]
  rw [show ((8 : Int) * ((0 : Int) + 1) * ((w : Nat) : Int) - 1).toNat = 8 * w - 1
        from by omega,
      show ((8 : Int) * (0 : Int) * ((w : Nat) : Int)).toNat = 0 from by omega]
  rcases hwlit with rfl | rfl | rfl | rfl <;>
    simp only [extractLsb_full_w1, extractLsb_full_w2, extractLsb_full_w4,
      extractLsb_full_w8, BitVec.setWidth_eq, hwr, Bool.true_and, Bool.and_self,
      ExceptT.bindCont, EStateM.bind, EStateM.pure, EStateM.map]

/-- `mem_write_value` for a bare-mode aligned writable width-`w` store (capstone of the
    `mem_write` chain): effective privilege is Machine (`MPRV = 0`), the alignment guard
    is bypassed (`rl = con = false`), `checked_mem_write` performs the write, and the
    callback is a no-op. Returns `Ok true` in the post-write state. -/
theorem mem_write_value_store_N (w : Nat) (addr : BitVec 64) (s s' : SailState)
    (mst : BitVec 64) (data : BitVec (8*w))
    (cfgs : Vector (BitVec 8) 64) (pmpaddrs : Vector (BitVec 64) 64)
    (regions : List PMA_Region) (region : PMA_Region)
    (hwlit : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8)
    (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (h_mst : s.regs.get? Register.mstatus = some mst)
    (h_mprv : _get_Mstatus_MPRV mst = 0#1)
    (h_cfg : s.regs.get? Register.pmpcfg_n = some cfgs)
    (h_addr : s.regs.get? Register.pmpaddr_n = some pmpaddrs)
    (h_off : ∀ i : Nat,
      pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (cfgs[i]!)) = PmpAddrMatchType.OFF)
    (h_reg : s.regs.get? Register.pma_regions = some regions)
    (h_match : matching_pma_region regions (physaddr.Physaddr addr) w = some region)
    (h_write : region.attributes.writable = true)
    (h_align : is_aligned_paddr (physaddr.Physaddr addr) w = true)
    (hclint : (within_clint (physaddr.Physaddr addr) w) s = .ok false s)
    (hsig : (within_sig (physaddr.Physaddr addr) w) s = .ok false s)
    (hhtif : (within_htif_writable (physaddr.Physaddr addr) w) s = .ok false s)
    (hwrite : (writeBytes addr.toNat data : SailM Bool) s = .ok true s') :
    (mem_write_value (physaddr.Physaddr addr) w data
      (MemoryAccessType.Store mem_payload.Data) page_based_mem_type.PBMT_PMA
      false false false) s
      = .ok (Result.Ok true) s' := by
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
  simp only [PreSail.readReg, h_priv, h_mst, pure, EStateM.pure, bind, EStateM.bind,
    get, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    effectivePrivilege_machine s _ mst _ h_mprv,
    checked_mem_write_store_N w addr s s' data cfgs pmpaddrs regions region hwlit
      h_cfg h_addr h_off h_reg h_match h_write h_align hclint hsig hhtif hwrite]

-- ============================================================================
-- `vmem_write_addr` and `vmem_write`
-- ============================================================================

/-- **`vmem_write_addr` for a bare-mode aligned width-`w` store.** The aligned access
    stays inside its page (`split_on_page_boundary` → `(w, 0)`) and translation is
    `Bare`, so no page-split happens and the access width is the full width:
    `translateAddr` is the bare-mode identity, the reservation branch is skipped
    (`res = false`), `mem_write_ea` passes its checks as a state-no-op, the full-range
    data slice is the data, and `mem_write_value` performs the physical write (the
    split-misaligned loop now lives inside `checked_mem_write`). Returns `Ok true` in
    the post-write state `s'`. -/
theorem vmem_write_addr_store_core (w : Nat) (vaddr : virtaddr) (s s' : SailState)
    (mst : BitVec 64) (data : BitVec (8*w))
    (cfgs : Vector (BitVec 8) 64) (pmpaddrs : Vector (BitVec 64) 64)
    (regions : List PMA_Region) (region : PMA_Region)
    (hwlit : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8)
    (h_valign : is_aligned_vaddr vaddr w = true)
    (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (h_mst : s.regs.get? Register.mstatus = some mst)
    (h_mprv : _get_Mstatus_MPRV mst = 0#1)
    (h_cfg : s.regs.get? Register.pmpcfg_n = some cfgs)
    (h_pmpaddr : s.regs.get? Register.pmpaddr_n = some pmpaddrs)
    (h_off : ∀ i : Nat,
      pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (cfgs[i]!)) = PmpAddrMatchType.OFF)
    (h_reg : s.regs.get? Register.pma_regions = some regions)
    (h_match : matching_pma_region regions
      (physaddr.Physaddr (bits_of_virtaddr vaddr)) w = some region)
    (h_write : region.attributes.writable = true)
    (h_palign : is_aligned_paddr (physaddr.Physaddr (bits_of_virtaddr vaddr)) w = true)
    (hclint : (within_clint (physaddr.Physaddr (bits_of_virtaddr vaddr)) w) s = .ok false s)
    (hsig : (within_sig (physaddr.Physaddr (bits_of_virtaddr vaddr)) w) s = .ok false s)
    (hhtif : (within_htif_writable (physaddr.Physaddr (bits_of_virtaddr vaddr)) w) s
      = .ok false s)
    (hwrite : (writeBytes (bits_of_virtaddr vaddr).toNat data : SailM Bool) s = .ok true s') :
    (vmem_write_addr vaddr w data (MemoryAccessType.Store mem_payload.Data) false false false) s
      = .ok (Result.Ok true) s' := by
  have halignN : (bits_of_virtaddr vaddr).toNat % w = 0 :=
    toNat_mod_of_is_aligned_vaddr vaddr w hwlit h_valign
  have hpage := split_on_page_boundary_aligned (bits_of_virtaddr vaddr) w s hwlit halignN
  have htrans := translateAddr_bare_store s vaddr mst h_priv h_mst h_mprv
  have hea := mem_write_ea_plain (bits_of_virtaddr vaddr) w s mst cfgs pmpaddrs
    regions region h_priv h_mst h_mprv h_cfg h_pmpaddr h_off h_reg h_match h_write h_palign
  have hmwv := mem_write_value_store_N w (bits_of_virtaddr vaddr) s s' mst data
    cfgs pmpaddrs regions region hwlit h_priv h_mst h_mprv h_cfg h_pmpaddr h_off h_reg
    h_match h_write h_palign hclint hsig hhtif hwrite
  unfold vmem_write_addr
  simp +decide only [h_valign, Functions.not, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, if_false,
    SailME.run, PreSail.PreSailME.run,
    hpage, PreSail.readReg, h_priv, h_mst,
    effectivePrivilege_machine s _ mst _ h_mprv, translationMode_machine,
    sys_misaligned_order_decreasing, bne, is_store_conditional,
    show (SATPMode.Bare == SATPMode.Bare) = true from rfl,
    Bool.false_and, Bool.true_and, ite_self,
    Int.toNat_natCast,
    htrans, zero_extend64_id, bits_of_virtaddr_mk,
    Sail.assert, PreSail.assert, if_true,
    EStateM.map, bind, EStateM.bind, pure, EStateM.pure, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.lift, ExceptT.pure,
    MonadLift.monadLift, monadLift, liftM, Functor.map]
  -- collapse the (degenerate) `access_width` selector sitting in type positions, land
  -- the effective-address check up to defeq, then reduce the remaining plumbing
  rw [show (if (false = true) then ((w : Nat) : Int) else ((w : Nat) : Int))
        = ((w : Nat) : Int) from rfl]
  erw [hea]
  simp only [EStateM.map, bind, EStateM.bind, pure, EStateM.pure,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.lift, ExceptT.pure,
    MonadLift.monadLift, monadLift, liftM, Functor.map]
  rw [show ((8 : Int) * ((w : Nat) : Int) - 1).toNat = 8 * w - 1 from by omega]
  rcases hwlit with rfl | rfl | rfl | rfl <;>
  · simp only [extractLsb_full_w1, extractLsb_full_w2, extractLsb_full_w4,
      extractLsb_full_w8, BitVec.setWidth_eq]
    erw [hmwv]
    simp only [Bool.true_and, Bool.and_self, ExceptT.bindCont, EStateM.bind, EStateM.pure,
      EStateM.map]

/-- **`vmem_write` for a bare-mode aligned width-`w` store.** The effective-address
    pipeline (`ext_data_get_addr` reads `rs_addr`; `transform_effective_address` is the
    bare-mode identity) yields `rsval + offset`, then `vmem_write_addr` performs the
    write. Consumes the `vmem_write_addr` result abstractly (mirror of
    `vmem_read_load_N`). -/
theorem vmem_write_store_N (w : Nat) (rs_addr : regidx) (offset rsval : BitVec 64)
    (s s' : SailState) (data : BitVec (8*w)) (bm : BareModeInv s)
    (h_rs : (rX_bits rs_addr) s = .ok rsval s)
    (hvwa : (vmem_write_addr (virtaddr.Virtaddr (rsval + offset)) w data
      (MemoryAccessType.Store mem_payload.Data) false false false) s
      = .ok (Result.Ok true) s') :
    (vmem_write rs_addr offset w data (MemoryAccessType.Store mem_payload.Data)
      false false false) s = .ok (Result.Ok true) s' := by
  obtain ⟨mst, msec, cfgs, pmpaddrs, regions, h_priv, h_mst, h_mprv, h_sec, h_pmm,
    h_cfg, h_pmpaddr, h_off, h_reg⟩ := bm
  have htransform := transform_effective_address_bare_store s
    (virtaddr.Virtaddr (rsval + offset)) mst msec h_priv h_mst h_mprv h_sec h_pmm
  unfold vmem_write get_transformed_data_addr ext_data_get_addr
  sail_reduce [h_rs, htransform, pm_transform_PA_zero, bits_of_virtaddr_mk, hvwa]

end EvmAsm.Rv64.SailEquiv
