/-
  EvmAsm.Rv64.SailEquiv.VmemReduction

  Full bare-mode reduction of the SAIL `execute_LOAD` doubleword path, ending in the
  unconditional Tier-A capstone `ld_sail_equiv` (bottom of this file): given
  `StateRel`, a `BareModeInv`, and per-access facts (alignment, a readable PMA
  region, MMIO disjointness, byte-presence witnesses), the SAIL load retires with
  `RETIRE_SUCCESS` into a state `StateRel`-related to the toy model's `LD`. The
  vacuous `h_exec` hypothesis the original deferred lemma carried is gone.

  Contents, bottom-up:

  * the `sail_step` simp set + `sail_reduce` tactic — the Sail monad-transformer
    plumbing every bare-mode reduction has to unfold;
  * the leaf data-correctness bridge: the little-endian `readBytes` append equals
    the abstraction relation's `reconstructDword` (`append8_eq_or_shifts`,
    `readBytes8_eq_reconstruct`);
  * the bare-mode leaves: `translateAddr_bare`, the `pmpCheck` PMP-scan collapse
    (`forIn'_noop*`, `pmpCheck_machine_off`), `pmaCheck_load_ok` region membership,
    and the `untilFuelM` single-iteration (fuel-1) loop reduction (`untilFuelM_one`);
  * the physical read chain (`mem_read_load_bare`, `checked_mem_read_load`, …),
    the `vmem_read` loop reductions (`vmem_read_addr_load_bare`,
    `vmem_read_load_bare`), and `ld_sail_equiv` on top.

  Sub-doubleword loads reuse this chain via `VmemReductionN.lean` /
  `VmemReductionLoads.lean`; stores mirror it in `VmemWriteReduction.lean` /
  `VmemReductionStores.lean`. The byte-presence hypotheses are supplied per
  access; deriving them from a run-level invariant is tracked as #10529.
-/

import EvmAsm.Rv64.SailEquiv.MemProofs
import EvmAsm.Rv64.SailEquiv.SailStepAttr

open Out
open Out.Functions
open Sail
open PreSail

namespace EvmAsm.Rv64.SailEquiv

/- **`sail_step` simp set** — the Sail monad-transformer plumbing that every bare-mode
   `execute_*`/`vmem_*` reduction has to unfold: `SailME.run`/`PreSailME.run`, the
   `ExceptT` and `EStateM` bind/pure/map/get machinery, `monadLift`/`liftM`/`Functor.map`,
   and `readReg`. Invoke through `sail_reduce` (below). Per-lemma facts (register-value
   hypotheses, leaf lemmas like `translateAddr_bare`/`mem_read_load_bare`) are passed as
   extra args, not registered here. -/
attribute [sail_step]
  SailME.run PreSail.PreSailME.run PreSail.readReg
  EStateM.map EStateM.bind EStateM.pure EStateM.get
  bind pure get MonadState.get getThe MonadStateOf.get
  ExceptT.run ExceptT.mk ExceptT.bind ExceptT.bindCont ExceptT.lift ExceptT.pure
  MonadLift.monadLift monadLift liftM Functor.map

/-- Discharge the Sail monad plumbing of a bare-mode reduction goal: `simp +decide only`
    over the `sail_step` set plus any extra facts/leaf lemmas you supply. -/
syntax "sail_reduce" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| sail_reduce) => `(tactic| simp +decide only [sail_step])
  | `(tactic| sail_reduce [$args,*]) => `(tactic| simp +decide only [sail_step, $args,*])

/-- Pure `BitVec` identity: the little-endian nested `append` that `readBytes 8`
    produces equals the or-of-shifts that `reconstructDword` uses (`b0` = lowest byte). -/
theorem append8_eq_or_shifts (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0
      : BitVec 64)
    = b0.zeroExtend 64 ||| (b1.zeroExtend 64 <<< 8) ||| (b2.zeroExtend 64 <<< 16) |||
      (b3.zeroExtend 64 <<< 24) ||| (b4.zeroExtend 64 <<< 32) ||| (b5.zeroExtend 64 <<< 40) |||
      (b6.zeroExtend 64 <<< 48) ||| (b7.zeroExtend 64 <<< 56) := by
  show (((((((b7 ++ b6) ++ b5) ++ b4) ++ b3) ++ b2) ++ b1) ++ b0 : BitVec 64) = _
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
             BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth, ← Bool.if_false_right]
  have h64 : i < 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 := hi
  simp only [if_pos h64, if_pos (show i - 8  < 8+8+8+8+8+8+8+8 by omega),
                         if_pos (show i - 16 < 8+8+8+8+8+8+8+8 by omega),
                         if_pos (show i - 24 < 8+8+8+8+8+8+8+8 by omega),
                         if_pos (show i - 32 < 8+8+8+8+8+8+8+8 by omega),
                         if_pos (show i - 40 < 8+8+8+8+8+8+8+8 by omega),
                         if_pos (show i - 48 < 8+8+8+8+8+8+8+8 by omega)]
  rcases Nat.lt_or_ge i 8 with h0 | h0
  · -- [0, 8): b0 is active
    simp [h0, show i < 16 by omega, show i < 24 by omega, show i < 32 by omega,
          show i < 40 by omega, show i < 48 by omega, show i < 56 by omega]
  rcases Nat.lt_or_ge i 16 with h1 | h1
  · -- [8, 16): b1 is active
    simp [BitVec.getLsbD_of_ge b0 i (by omega),
          show ¬ i < 8 by omega, show i < 16 by omega, show i < 24 by omega,
          show i < 32 by omega, show i < 40 by omega, show i < 48 by omega, show i < 56 by omega,
          show i - 8 < 8 by omega]
  rcases Nat.lt_or_ge i 24 with h2 | h2
  · -- [16, 24): b2 is active
    simp [BitVec.getLsbD_of_ge b0 i (by omega), BitVec.getLsbD_of_ge b1 (i-8) (by omega),
          show ¬ i < 8 by omega, show ¬ i < 16 by omega, show i < 24 by omega,
          show i < 32 by omega, show i < 40 by omega, show i < 48 by omega, show i < 56 by omega,
          show ¬ i - 8 < 8 by omega, show i - 8 - 8 < 8 by omega]
    rfl
  rcases Nat.lt_or_ge i 32 with h3 | h3
  · -- [24, 32): b3 is active
    simp [BitVec.getLsbD_of_ge b0 i (by omega), BitVec.getLsbD_of_ge b1 (i-8) (by omega),
          BitVec.getLsbD_of_ge b2 (i-16) (by omega),
          show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, show i < 32 by omega,
          show i < 40 by omega, show i < 48 by omega, show i < 56 by omega,
          show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega, show i - 8 - 8 - 8 < 8 by omega]
    rfl
  rcases Nat.lt_or_ge i 40 with h4 | h4
  · -- [32, 40): b4 is active
    simp [BitVec.getLsbD_of_ge b0 i (by omega), BitVec.getLsbD_of_ge b1 (i-8) (by omega),
          BitVec.getLsbD_of_ge b2 (i-16) (by omega), BitVec.getLsbD_of_ge b3 (i-24) (by omega),
          show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, show ¬ i < 32 by omega,
          show i < 40 by omega, show i < 48 by omega, show i < 56 by omega,
          show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega, show ¬ i - 8 - 8 - 8 < 8 by omega,
          show i - 8 - 8 - 8 - 8 < 8 by omega]
    rfl
  rcases Nat.lt_or_ge i 48 with h5 | h5
  · -- [40, 48): b5 is active
    simp [BitVec.getLsbD_of_ge b0 i (by omega), BitVec.getLsbD_of_ge b1 (i-8) (by omega),
          BitVec.getLsbD_of_ge b2 (i-16) (by omega), BitVec.getLsbD_of_ge b3 (i-24) (by omega),
          BitVec.getLsbD_of_ge b4 (i-32) (by omega),
          show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, show ¬ i < 32 by omega,
          show ¬ i < 40 by omega, show i < 48 by omega, show i < 56 by omega,
          show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega, show ¬ i - 8 - 8 - 8 < 8 by omega,
          show ¬ i - 8 - 8 - 8 - 8 < 8 by omega, show i - 8 - 8 - 8 - 8 - 8 < 8 by omega]
    rfl
  rcases Nat.lt_or_ge i 56 with h6 | h6
  · -- [48, 56): b6 is active
    simp [BitVec.getLsbD_of_ge b0 i (by omega), BitVec.getLsbD_of_ge b1 (i-8) (by omega),
          BitVec.getLsbD_of_ge b2 (i-16) (by omega), BitVec.getLsbD_of_ge b3 (i-24) (by omega),
          BitVec.getLsbD_of_ge b4 (i-32) (by omega), BitVec.getLsbD_of_ge b5 (i-40) (by omega),
          show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, show ¬ i < 32 by omega,
          show ¬ i < 40 by omega, show ¬ i < 48 by omega, show i < 56 by omega,
          show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega, show ¬ i - 8 - 8 - 8 < 8 by omega,
          show ¬ i - 8 - 8 - 8 - 8 < 8 by omega, show ¬ i - 8 - 8 - 8 - 8 - 8 < 8 by omega,
          show i - 8 - 8 - 8 - 8 - 8 - 8 < 8 by omega]
    rfl
  · -- [56, 64): b7 is active
    simp [BitVec.getLsbD_of_ge b0 i (by omega), BitVec.getLsbD_of_ge b1 (i-8) (by omega),
          BitVec.getLsbD_of_ge b2 (i-16) (by omega), BitVec.getLsbD_of_ge b3 (i-24) (by omega),
          BitVec.getLsbD_of_ge b4 (i-32) (by omega), BitVec.getLsbD_of_ge b5 (i-40) (by omega),
          BitVec.getLsbD_of_ge b6 (i-48) (by omega),
          show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, show ¬ i < 32 by omega,
          show ¬ i < 40 by omega, show ¬ i < 48 by omega, show ¬ i < 56 by omega,
          show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega, show ¬ i - 8 - 8 - 8 < 8 by omega,
          show ¬ i - 8 - 8 - 8 - 8 < 8 by omega, show ¬ i - 8 - 8 - 8 - 8 - 8 < 8 by omega,
          show ¬ i - 8 - 8 - 8 - 8 - 8 - 8 < 8 by omega, show i - 56 < 64 by omega]
    rfl

/-- **Leaf data bridge.** If the 8 bytes at `a … a+7` are present in SAIL memory, the
    physical doubleword read `readBytes 8 a` succeeds, leaves the state untouched, and
    returns exactly `reconstructDword sSail.mem a` — the value the abstraction relation
    (`StateRel.mem_agree`) ties to the toy model's `getMem`. -/
theorem readBytes8_eq_reconstruct (sSail : SailState) (a : Nat)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h0 : sSail.mem.get? a = some b0) (h1 : sSail.mem.get? (a+1) = some b1)
    (h2 : sSail.mem.get? (a+2) = some b2) (h3 : sSail.mem.get? (a+3) = some b3)
    (h4 : sSail.mem.get? (a+4) = some b4) (h5 : sSail.mem.get? (a+5) = some b5)
    (h6 : sSail.mem.get? (a+6) = some b6) (h7 : sSail.mem.get? (a+7) = some b7) :
    runSail (readBytes 8 a) sSail = some ((reconstructDword sSail.mem a, none), sSail) := by
  simp only [runSail, readBytes, readByte, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, h0, h1, h2, h3, h4, h5, h6, h7]
  simp only [Std.ExtHashMap.get?_eq_getElem?] at h0 h1 h2 h3 h4 h5 h6 h7
  simp only [reconstructDword, Std.ExtHashMap.getD_eq_getD_getElem?,
    h0, h1, h2, h3, h4, h5, h6, h7, Option.getD_some, append8_eq_or_shifts]

/-- **Lemma #2 — `translateAddr` bare-mode no-op.** In bare mode (`cur_privilege =
    Machine`, `mstatus.MPRV = 0`) a `Load Data` translation is the identity: it reads
    only `mstatus`/`cur_privilege`, leaves the state untouched, and returns the virtual
    address as physical (`PBMT_PMA`). Stated in `EStateM` `.ok` form so it rewrites
    directly inside the `vmem_read_addr` translation `bind`/`match`. -/
theorem translateAddr_bare (s : SailState) (vAddr : virtaddr) (mst : BitVec 64)
    (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (h_mst : s.regs.get? Register.mstatus = some mst)
    (h_mprv : _get_Mstatus_MPRV mst = 0#1) :
    translateAddr vAddr (MemoryAccessType.Load mem_payload.Data) s
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

/-- **Lemma #3 — `IntRange.forIn'` no-op invariant.** If the loop body, run on a fixed
    state `s`, always leaves `s` unchanged and `.yield`s the accumulator unchanged (i.e.
    only reads state, never errors or `.done`s), the whole loop returns `init` with `s`
    untouched. Proven by the generated well-founded induction principle
    `IntRange.forIn'.loop.induct`. This collapses `pmpCheck`'s 16-entry PMP scan — whose
    body, with every cfg A-field OFF, is exactly such a read-only no-op — and any similar
    Sail `for i in [..]i` loop. -/
theorem forIn'_noop {β : Type} (range : IntRange) (init : β) (s : SailState)
    (f : (i : Int) → i ∈ range → β → SailM (ForInStep β))
    (hf : ∀ (i : Int) (hi : i ∈ range) (b : β), f i hi b s = .ok (.yield b) s) :
    (forIn' range init f) s = .ok init s := by
  have aux : ∀ (b : β) (i : Int) (hs : (i - range.start) % range.step = 0),
      IntRange.forIn'.loop range f b i hs s = .ok b s := by
    intro b i hs
    induction b, i, hs using IntRange.forIn'.loop.induct (range := range) with
    | case1 b i hs hin ih =>
      rw [IntRange.forIn'.loop.eq_def]
      simp only [hin, dif_pos]
      show (EStateM.bind (f i hin b) _) s = _
      simp only [EStateM.bind, hf i hin b]
      exact ih b
    | case2 b i hs hnin =>
      rw [IntRange.forIn'.loop.eq_def]
      simp only [hnin, dif_neg, not_false_iff]
      rfl
  show IntRange.forIn'.loop range f init range.start _ s = _
  exact aux init range.start _

/-- **Lemma #4 — `IntRange.forIn'` no-op invariant in the `SailME`/`ExceptT` monad.**
    The `forIn'_noop` analogue for loops that run inside `SailME.run` (i.e. in
    `ExceptT ε SailM`), such as `pmpCheck`'s PMP scan. If the body, run on a fixed state
    `s`, returns `.ok (Except.ok (.yield b)) s` — read-only, no early `throw`, yields the
    accumulator unchanged — the whole loop returns `init` with `s` untouched. Same
    `IntRange.forIn'.loop.induct` proof as `forIn'_noop`, with the `ExceptT` bind. -/
theorem forIn'_noop_except {β : Type} {ε : Type} (range : IntRange) (init : β) (s : SailState)
    (f : (i : Int) → i ∈ range → β → ExceptT ε SailM (ForInStep β))
    (hf : ∀ (i : Int) (hi : i ∈ range) (b : β), (f i hi b) s = .ok (Except.ok (.yield b)) s) :
    (forIn' range init f) s = .ok (Except.ok init) s := by
  have aux : ∀ (b : β) (i : Int) (hs : (i - range.start) % range.step = 0),
      IntRange.forIn'.loop range f b i hs s = .ok (Except.ok b) s := by
    intro b i hs
    induction b, i, hs using IntRange.forIn'.loop.induct (range := range) with
    | case1 b i hs hin ih =>
      rw [IntRange.forIn'.loop.eq_def]
      simp only [hin, dif_pos]
      show (ExceptT.bind (f i hin b) _) s = _
      simp only [ExceptT.bind, ExceptT.mk, ExceptT.bindCont, bind, EStateM.bind, hf i hin b]
      exact ih b
    | case2 b i hs hnin =>
      rw [IntRange.forIn'.loop.eq_def]
      simp only [hnin, dif_neg, not_false_iff]
      rfl
  show IntRange.forIn'.loop range f init range.start _ s = _
  exact aux init range.start _

/-- **Lemma #5 — `untilFuelM` single iteration.** With `fuel = 1` the Sail bounded loop
    runs its body once and evaluates the condition (whose result is discarded — both `if`
    branches return the same `x`). Used to unwrap `vmem_read_addr`'s outer access loop,
    which has `fuel = 1` for an aligned access (`split_misaligned` returns `(1, width)`). -/
theorem untilFuelM_one {m : Type → Type} [Monad m] [LawfulMonad m] {α}
    (cond : α → m Bool) (init : α) (f : α → m α) :
    untilFuelM 1 cond init f = (f init >>= fun x => cond x >>= fun _ => pure x) := by
  show untilFuelM.go cond f init 1 = _
  rw [untilFuelM.go.eq_def]
  simp only [untilFuelM.go]
  apply bind_congr
  intro x
  simp only [ite_self]

/-- `untilFuelM` fuel-1 with a pure condition (the `vmem_read_addr` shape, where the
    condition is `fun (data, finished, i) => pure finished`) collapses to just the body. -/
theorem untilFuelM_one_pure {m : Type → Type} [Monad m] [LawfulMonad m] {α}
    (g : α → Bool) (init : α) (f : α → m α) :
    untilFuelM 1 (fun x => pure (g x)) init f = f init := by
  rw [untilFuelM_one]
  simp only [pure_bind, bind_pure]

/-- The `Phys_Mem_Access_Info` witness every **aligned** access produces: the PMA
    misaligned-atomicity-granule check (`mag_pma_check`) short-circuits on
    `is_aligned_paddr`, returning `CannotSplit` with granule exponent `0`. -/
def alignedAccessInfo : Phys_Mem_Access_Info :=
  { splittable := Splittability.CannotSplit, granule_size_exp := 0 }

/-- **Lemma #7 — `pmaCheck` permits an aligned readable Load.** If `paddr` lies in a PMA
    region (`matching_pma_region` finds it) that is `readable` and the access is aligned,
    a `Load Data` PMA check (with `PBMT_PMA`, non-reservation) returns
    `Ok alignedAccessInfo` (permitted, unsplittable), leaving the state untouched. Region
    membership/readability are taken abstractly so this is independent of the concrete
    `sail_model_init` region list. -/
theorem pmaCheck_load_ok (paddr : physaddr) (width : Nat) (s : SailState)
    (regions : List PMA_Region) (region : PMA_Region)
    (h_reg : s.regs.get? Register.pma_regions = some regions)
    (h_match : matching_pma_region regions paddr width = some region)
    (h_read : region.attributes.readable = true)
    (h_align : is_aligned_paddr paddr width = true) :
    pmaCheck paddr width (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA false s
      = .ok (Ok alignedAccessInfo) s := by
  unfold pmaCheck mag_pma_check is_mag_applicable_access
  simp +decide [alignedAccessInfo, SailME.run, PreSail.PreSailME.run,
    PreSail.readReg, h_reg, h_match, override_PMA, h_align, h_read,
    pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get,
    ExceptT.run, ExceptT.mk, ExceptT.pure, ExceptT.bind, ExceptT.bindCont, ExceptT.lift,
    MonadLift.monadLift, monadLift, liftM, Functor.map, EStateM.map,
    Sail.assert, PreSail.assert]

/-- **`check_pma_with_pmp_priority` permits an aligned readable Load.** The PMA check
    succeeds first, so the (fault-attribution) PMP fallback is never consulted — the
    privilege argument is arbitrary. This is the access check `checked_mem_read` /
    `checked_mem_write` now run up front. -/
theorem check_pma_with_pmp_priority_load_ok (paddr : physaddr) (width : Nat) (s : SailState)
    (priv : Privilege) (regions : List PMA_Region) (region : PMA_Region)
    (h_reg : s.regs.get? Register.pma_regions = some regions)
    (h_match : matching_pma_region regions paddr width = some region)
    (h_read : region.attributes.readable = true)
    (h_align : is_aligned_paddr paddr width = true) :
    check_pma_with_pmp_priority (MemoryAccessType.Load mem_payload.Data)
      page_based_mem_type.PBMT_PMA priv paddr width false s
      = .ok (Ok alignedAccessInfo) s := by
  unfold check_pma_with_pmp_priority
  simp only [bind, EStateM.bind,
    pmaCheck_load_ok paddr width s regions region h_reg h_match h_read h_align,
    pure, EStateM.pure]

/-- `pmpReadAddrReg` is read-only: it reads `pmpcfg_n`/`pmpaddr_n` and returns the stored
    address (the grain-`0` mask branches are trivial), leaving the state untouched. -/
theorem pmpReadAddrReg_noop (s : SailState) (n : Nat)
    (cfgs : Vector (BitVec 8) 64) (pmpaddrs : Vector (BitVec 64) 64)
    (h_cfg : s.regs.get? Register.pmpcfg_n = some cfgs)
    (h_addr : s.regs.get? Register.pmpaddr_n = some pmpaddrs) :
    (pmpReadAddrReg n) s = .ok (pmpaddrs[n]!) s := by
  unfold pmpReadAddrReg
  simp +decide only [sys_pmp_grain, PreSail.readReg, h_cfg, h_addr,
    pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get, if_false]
  generalize BitVec.access (_get_Pmpcfg_ent_A cfgs[n]!) 1 = b
  match b with
  | 0#1 => rfl
  | 1#1 => rfl

/-- When a PMP entry's A-field decodes to `OFF`, `pmpMatchAddr` returns `PMP_NoMatch`
    immediately without touching the address/state. -/
theorem pmpMatchAddr_off (s : SailState) (addr : physaddr) (width pmpaddr prev : BitVec 64)
    (ent : BitVec 8)
    (h_off : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = PmpAddrMatchType.OFF) :
    (pmpMatchAddr addr width ent pmpaddr prev) s = .ok pmpAddrMatch.PMP_NoMatch s := by
  unfold pmpMatchAddr
  simp +decide only [h_off, pure, EStateM.pure]

/-- **Lemma #8 — `pmpCheck` permits access in Machine mode with all PMP entries OFF.**
    Returns `none` (access permitted), state untouched. The 16-entry PMP scan is a
    read-only no-op (every entry OFF ⇒ `pmpMatchAddr` = `PMP_NoMatch`), collapsed via
    `forIn'_noop_except` (#4); the trailing `priv == Machine` guard yields `none`. -/
theorem pmpCheck_machine_off (addr : physaddr) (width : Nat) (s : SailState)
    (cfgs : Vector (BitVec 8) 64) (pmpaddrs : Vector (BitVec 64) 64)
    (h_cfg : s.regs.get? Register.pmpcfg_n = some cfgs)
    (h_addr : s.regs.get? Register.pmpaddr_n = some pmpaddrs)
    (h_off : ∀ i : Nat,
      pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (cfgs[i]!)) = PmpAddrMatchType.OFF) :
    pmpCheck addr width (MemoryAccessType.Load mem_payload.Data) Privilege.Machine s
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

/-- **Lemma #9 — `within_mmio_readable` is `false` off the MMIO ranges.** With RVFI off
    (`get_config_rvfi () = false`, definitional) the check reduces to
    `within_clint || within_sig || (within_htif_readable && 1≤width)`. If all three
    sub-checks return `false` at this address (the access is in ordinary RAM, disjoint
    from CLINT/SIG/HTIF), the whole check returns `false`, state untouched — so
    `checked_mem_read` takes the `read_ram` branch. Sub-checks taken abstractly so this is
    independent of the concrete platform range constants. -/
theorem within_mmio_readable_ram (addr : physaddr) (width : Nat) (s : SailState)
    (hclint : (within_clint addr width) s = .ok false s)
    (hsig : (within_sig addr width) s = .ok false s)
    (hhtif : (within_htif_readable addr width) s = .ok false s) :
    (within_mmio_readable addr width) s = .ok false s := by
  unfold within_mmio_readable
  simp only [get_config_rvfi, Bool.false_eq_true, if_false,
    bind, EStateM.bind, hclint, hsig, hhtif,
    pure, EStateM.pure, Bool.false_or, Bool.false_and]

/-- **Lemma #2b — `effectivePrivilege` is the identity in Machine mode with `MPRV = 0`.**
    A data access (not an `InstructionFetch`) only switches privilege when `MPRV = 1`; with
    `MPRV = 0` the guard is false and the passed-in privilege is returned unchanged. -/
theorem effectivePrivilege_machine (s : SailState) (access : MemoryAccessType mem_payload)
    (mst : BitVec 64) (priv : Privilege)
    (h_mprv : _get_Mstatus_MPRV mst = 0#1) :
    (effectivePrivilege access mst priv) s = .ok priv s := by
  unfold effectivePrivilege
  simp only [h_mprv, show ((0#1 : BitVec 1) == 1#1) = false by decide, Bool.and_false]
  rfl

/-- **Lemma #2c — `get_pmlen` is `0` in Machine mode with pointer masking disabled.**
    A `Load Data` access is PMM-applicable, so `get_pmlen` consults `get_pmm Machine`,
    which reads `mseccfg`; with its PMM field (`bits 33:32`) zero, the mode is
    `PMM_Disabled` and the masking length is `0`. Reads `mstatus` (forced by the
    short-circuited applicability test) and `mseccfg`, leaving the state untouched. -/
theorem get_pmlen_machine_zero (s : SailState) (mst msec : BitVec 64)
    (h_mst : s.regs.get? Register.mstatus = some mst)
    (h_sec : s.regs.get? Register.mseccfg = some msec)
    (h_pmm : _get_Seccfg_PMM msec = 0#2) :
    (get_pmlen (MemoryAccessType.Load mem_payload.Data) Privilege.Machine) s = .ok 0 s := by
  unfold get_pmlen is_pmm_applicable get_pmm
  simp +decide [PreSail.readReg, h_mst, h_sec, h_pmm, pmm_mode_backwards,
    pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get, bne]

/-- `translationMode` in Machine mode is `Bare` (no address translation), state untouched. -/
theorem translationMode_machine (s : SailState) :
    (translationMode Privilege.Machine) s = .ok SATPMode.Bare s := by
  unfold translationMode
  simp +decide only [if_true, pure, EStateM.pure, bind]

/-- **Lemma #2d — `transform_effective_address` is the identity in bare mode.** With
    `cur_privilege = Machine`, `MPRV = 0`, and pointer masking disabled, the effective
    privilege is Machine, translation mode is `Bare`, and `pmlen = 0`, so
    `pm_transform_PA vaddr 0` returns `vaddr` unchanged (a zero-extend of the full 64-bit
    address). State untouched. -/
theorem transform_effective_address_bare (s : SailState) (vaddr : virtaddr)
    (mst msec : BitVec 64)
    (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (h_mst : s.regs.get? Register.mstatus = some mst)
    (h_mprv : _get_Mstatus_MPRV mst = 0#1)
    (h_sec : s.regs.get? Register.mseccfg = some msec)
    (h_pmm : _get_Seccfg_PMM msec = 0#2) :
    (transform_effective_address vaddr (MemoryAccessType.Load mem_payload.Data)) s
      = .ok (pm_transform_PA vaddr 0) s := by
  unfold transform_effective_address
  sail_reduce [h_priv, h_mst, effectivePrivilege_machine s _ mst _ h_mprv,
    get_pmlen_machine_zero s mst msec h_mst h_sec h_pmm,
    translationMode_machine s, if_true, Int.toNat_zero]

/-- Generic `runSail` inversion: a successful `runSail` gives the underlying `EStateM`
    `.ok`. Lets us reuse `runSail`-stated leaves (#1) in raw `EStateM` reductions. -/
theorem runSail_eq_ok {α} {m : SailM α} {s : SailState} {v : α} {s' : SailState}
    (h : runSail m s = some (v, s')) : m s = .ok v s' := by
  unfold runSail at h
  cases hm : m s with
  | ok a t =>
    rw [hm] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | error e t => rw [hm] at h; exact absurd h (by simp)

/-- Raw `.ok` form of the leaf data bridge (#1): the doubleword physical read returns
    `reconstructDword` directly in `EStateM` form, for composing inside `read_ram`. -/
theorem readBytes8_raw (sSail : SailState) (a : Nat)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h0 : sSail.mem.get? a = some b0) (h1 : sSail.mem.get? (a+1) = some b1)
    (h2 : sSail.mem.get? (a+2) = some b2) (h3 : sSail.mem.get? (a+3) = some b3)
    (h4 : sSail.mem.get? (a+4) = some b4) (h5 : sSail.mem.get? (a+5) = some b5)
    (h6 : sSail.mem.get? (a+6) = some b6) (h7 : sSail.mem.get? (a+7) = some b7) :
    (readBytes 8 a : SailM ((BitVec (8*8)) × Option Bool)) sSail
      = .ok (reconstructDword sSail.mem a, none) sSail := by
  simp only [readBytes, readByte, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, h0, h1, h2, h3, h4, h5, h6, h7]
  simp only [Std.ExtHashMap.get?_eq_getElem?] at h0 h1 h2 h3 h4 h5 h6 h7
  simp only [reconstructDword, Std.ExtHashMap.getD_eq_getD_getElem?,
    h0, h1, h2, h3, h4, h5, h6, h7, Option.getD_some, append8_eq_or_shifts]

/-- **`read_ram` for a plain doubleword load.** With the 8 bytes present, `read_ram`
    builds its read request, calls `sail_mem_read` (→ `readBytes`), and returns
    `reconstructDword` with default (unit) metadata, state untouched. -/
theorem read_ram_plain_load (sSail : SailState) (addr : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h0 : sSail.mem.get? addr.toNat = some b0) (h1 : sSail.mem.get? (addr.toNat+1) = some b1)
    (h2 : sSail.mem.get? (addr.toNat+2) = some b2) (h3 : sSail.mem.get? (addr.toNat+3) = some b3)
    (h4 : sSail.mem.get? (addr.toNat+4) = some b4) (h5 : sSail.mem.get? (addr.toNat+5) = some b5)
    (h6 : sSail.mem.get? (addr.toNat+6) = some b6) (h7 : sSail.mem.get? (addr.toNat+7) = some b7) :
    (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr addr) 8 false) sSail
      = .ok (reconstructDword sSail.mem addr.toNat, ()) sSail := by
  have hbytes := readBytes8_raw sSail addr.toNat b0 b1 b2 b3 b4 b5 b6 b7
    h0 h1 h2 h3 h4 h5 h6 h7
  unfold Functions.read_ram Sail.ConcurrencyInterfaceV1.sail_mem_read
    PreSail.ConcurrencyInterfaceV1.sail_mem_read
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  erw [hbytes]
  simp only [EStateM.pure]

/-- **`phys_access_check` permits a bare-mode aligned readable load.** Composes the
    `pmpCheck` (#8) `none` result with the `pmaCheck` (#7) `Ok alignedAccessInfo`. -/
theorem phys_access_check_load_ok (addr : BitVec 64) (width : Nat) (s : SailState)
    (cfgs : Vector (BitVec 8) 64) (pmpaddrs : Vector (BitVec 64) 64)
    (regions : List PMA_Region) (region : PMA_Region)
    (h_cfg : s.regs.get? Register.pmpcfg_n = some cfgs)
    (h_addr : s.regs.get? Register.pmpaddr_n = some pmpaddrs)
    (h_off : ∀ i : Nat,
      pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (cfgs[i]!)) = PmpAddrMatchType.OFF)
    (h_reg : s.regs.get? Register.pma_regions = some regions)
    (h_match : matching_pma_region regions (physaddr.Physaddr addr) width = some region)
    (h_read : region.attributes.readable = true)
    (h_align : is_aligned_paddr (physaddr.Physaddr addr) width = true) :
    phys_access_check (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      Privilege.Machine (physaddr.Physaddr addr) width false s
      = .ok (Ok alignedAccessInfo) s := by
  unfold phys_access_check
  simp only [bind, EStateM.bind,
    pmpCheck_machine_off (physaddr.Physaddr addr) width s cfgs pmpaddrs h_cfg h_addr h_off,
    pmaCheck_load_ok (physaddr.Physaddr addr) width s regions region h_reg h_match h_read h_align]

/-- A full-width `updateSubrange` (bits 63..0 of a 64-bit word) is just the written value:
    the mask `~~~(allOnes <<< 0)` is `0`, so `(0 &&& x) ||| y = y`. Used to collapse the
    single-access doubleword writeback in `checked_mem_read` / `vmem_read_addr`. -/
theorem updateSubrange_full (x y : BitVec 64) :
    Sail.BitVec.updateSubrange x 63 0 y = y := by
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    Nat.sub_zero]
  simp [hi, Bool.and_comm]

/-- A full-width `updateSubrange'` (start 0, length = width) is just the written value:
    the mask `~~~(allOnes <<< 0)` is `0`, so `(0 &&& x) ||| y = y`.  Width-generic — the
    width-8 `updateSubrange_full` above is the `w = 64` instance. -/
theorem updateSubrange'_full {w : Nat} (x y : BitVec w) :
    Sail.BitVec.updateSubrange' x 0 w y = y := by
  simp only [Sail.BitVec.updateSubrange']
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    Nat.sub_zero]
  simp [hi, Bool.and_comm]

/-- `split_misaligned` never splits an unsplittable access: with
    `splittable = CannotSplit` (the `alignedAccessInfo` witness) it returns `(1, width)`
    (one access of full width), state untouched, for any granule exponent. -/
theorem split_misaligned_cannotsplit (paddr : physaddr) (width : Nat) (exp : Nat)
    (s : SailState) :
    (split_misaligned paddr width exp Splittability.CannotSplit) s
      = .ok (1, (width : Int)) s := by
  obtain ⟨addr⟩ := paddr
  unfold split_misaligned
  simp only [show (Splittability.CannotSplit == Splittability.CannotSplit) = true from rfl,
    Bool.true_or, if_true]
  rfl

/-- `misaligned_order 1 = (0, 0, 1)` (a single forward iteration). -/
theorem misaligned_order_one : misaligned_order 1 = (0, 0, 1) := by
  unfold misaligned_order
  simp only [sys_misaligned_order_decreasing, Bool.false_eq_true, if_false]
  rfl

/-- `bits_of_virtaddr` is the projection out of `Virtaddr`. Tagged `sail_step`-only (not a
    global `@[simp]`) — it is a niche helper for the bare-mode reductions. -/
@[sail_step] theorem bits_of_virtaddr_mk (x : BitVec 64) :
    bits_of_virtaddr (virtaddr.Virtaddr x) = x := rfl

/-- `bits_of_physaddr` is the projection out of `Physaddr`. -/
@[sail_step] theorem bits_of_physaddr_mk (x : physaddrbits) :
    bits_of_physaddr (physaddr.Physaddr x) = x := rfl

/-- A 64→64 `zero_extend` is the identity. -/
theorem zero_extend64_id (x : BitVec 64) : (zero_extend (m := 64) x) = x := by
  simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.setWidth_eq]

/-- `BitVec.ofInt` of `0` is `0#n` — width-generic, so it also fires at the
    `physaddrbits` width `(if 64 = 32 then 34 else 64)`, which is not syntactically
    `64` (lemmas stated at literal width 64 silently fail to rewrite there). -/
theorem ofInt_zero_bv (n : Nat) : BitVec.ofInt n 0 = 0#n := rfl

/-- Adding the zero of the `physaddrbits` width (an `if`-expression that is only
    *definitionally* `64`) is the identity. Stated verbatim at that width so it fires
    where `BitVec.add_zero` (whose addition lives at syntactic width `64`) fails to
    match. -/
theorem add_zero_physaddrbits (x : BitVec (if decide ((64 : Nat) = 32) = true then 34 else 64)) :
    x + 0#(if decide ((64 : Nat) = 32) = true then 34 else 64) = x :=
  BitVec.add_zero x

/-- `read_ram` for a plain width-`w` load with the read value supplied. -/
theorem read_ram_load_N (w : Nat) (addr : BitVec 64) (s : SailState) (v : BitVec (8*w))
    (hread : (readBytes w addr.toNat : SailM ((BitVec (8*w)) × Option Bool)) s
      = .ok (v, none) s) :
    (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr addr) w false) s
      = .ok (v, ()) s := by
  unfold Functions.read_ram Sail.ConcurrencyInterfaceV1.sail_mem_read
    PreSail.ConcurrencyInterfaceV1.sail_mem_read
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  erw [hread]
  simp only [EStateM.pure]

/-- **`checked_mem_read` for a bare-mode aligned readable width-`w` load.** The
    PMA-with-PMP-priority check passes (`Ok alignedAccessInfo`), so `split_misaligned`
    yields a single access of full width and the access loop runs once (`untilFuelM`
    fuel 1): the per-access `pmpCheck` permits (Machine, all entries OFF), the address is
    off the MMIO ranges (so `read_ram`, not `mmio_read`), the read kind is `Read_plain`,
    and the full-width writeback keeps the read value. Returns `Ok (v, ())`, state
    untouched. -/
theorem checked_mem_read_load_w (w : Nat) (addr : BitVec 64) (s : SailState) (v : BitVec (8*w))
    (cfgs : Vector (BitVec 8) 64) (pmpaddrs : Vector (BitVec 64) 64)
    (regions : List PMA_Region) (region : PMA_Region)
    (hwlit : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8)
    (h_cfg : s.regs.get? Register.pmpcfg_n = some cfgs)
    (h_addr : s.regs.get? Register.pmpaddr_n = some pmpaddrs)
    (h_off : ∀ i : Nat,
      pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (cfgs[i]!)) = PmpAddrMatchType.OFF)
    (h_reg : s.regs.get? Register.pma_regions = some regions)
    (h_match : matching_pma_region regions (physaddr.Physaddr addr) w = some region)
    (h_read : region.attributes.readable = true)
    (h_align : is_aligned_paddr (physaddr.Physaddr addr) w = true)
    (hclint : (within_clint (physaddr.Physaddr addr) w) s = .ok false s)
    (hsig : (within_sig (physaddr.Physaddr addr) w) s = .ok false s)
    (hhtif : (within_htif_readable (physaddr.Physaddr addr) w) s = .ok false s)
    (hread : (readBytes w addr.toNat : SailM ((BitVec (8*w)) × Option Bool)) s
      = .ok (v, none) s) :
    checked_mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      Privilege.Machine (physaddr.Physaddr addr) w false false false false s
      = .ok (Result.Ok (v, ())) s := by
  have hcheck := check_pma_with_pmp_priority_load_ok (physaddr.Physaddr addr) w s
    Privilege.Machine regions region h_reg h_match h_read h_align
  have hsplit := split_misaligned_cannotsplit (physaddr.Physaddr addr) w 0 s
  have hpmp := pmpCheck_machine_off (physaddr.Physaddr addr) w s cfgs pmpaddrs
    h_cfg h_addr h_off
  have hmmio := within_mmio_readable_ram (physaddr.Physaddr addr) w s hclint hsig hhtif
  have hram := read_ram_load_N w addr s v hread
  unfold checked_mem_read
  simp +decide only [SailME.run, PreSail.PreSailME.run,
    hcheck, alignedAccessInfo, hsplit, misaligned_order_one,
    Int.toNat_one, Int.toNat_zero, untilFuelM_one,
    Sail.assert, PreSail.assert, if_true,
    BitVec.addInt, Int.natCast_zero, Int.zero_mul, Int.zero_add,
    ofInt_zero_bv, add_zero_physaddrbits,
    Int.toNat_natCast, bits_of_physaddr_mk,
    hpmp, hmmio, if_false, read_kind_of_flags, hram, default_meta,
    EStateM.map, bind, EStateM.bind, pure, EStateM.pure,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.lift, ExceptT.pure,
    MonadLift.monadLift, monadLift, liftM, Functor.map]
  rw [show ((8 : Int) * ((0 : Int) + 1) * ((w : Nat) : Int) - 1).toNat = 8 * w - 1
        from by omega,
      show ((8 : Int) * (0 : Int) * ((w : Nat) : Int)).toNat = 0 from by omega,
      show ((8 : Int) * 1 * ((w : Nat) : Int)).toNat = 8 * w from by omega]
  rcases hwlit with rfl | rfl | rfl | rfl <;>
    simp only [Sail.BitVec.updateSubrange, updateSubrange'_full, BitVec.setWidth_eq]

/-- **`checked_mem_read` for a bare-mode aligned readable doubleword load.** Width-8
    instance of `checked_mem_read_load_w` with the eight present bytes reassembled:
    returns `Ok (reconstructDword, ())`, state untouched. -/
theorem checked_mem_read_load (addr : BitVec 64) (s : SailState)
    (cfgs : Vector (BitVec 8) 64) (pmpaddrs : Vector (BitVec 64) 64)
    (regions : List PMA_Region) (region : PMA_Region)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h_cfg : s.regs.get? Register.pmpcfg_n = some cfgs)
    (h_addr : s.regs.get? Register.pmpaddr_n = some pmpaddrs)
    (h_off : ∀ i : Nat,
      pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (cfgs[i]!)) = PmpAddrMatchType.OFF)
    (h_reg : s.regs.get? Register.pma_regions = some regions)
    (h_match : matching_pma_region regions (physaddr.Physaddr addr) 8 = some region)
    (h_read : region.attributes.readable = true)
    (h_align : is_aligned_paddr (physaddr.Physaddr addr) 8 = true)
    (hclint : (within_clint (physaddr.Physaddr addr) 8) s = .ok false s)
    (hsig : (within_sig (physaddr.Physaddr addr) 8) s = .ok false s)
    (hhtif : (within_htif_readable (physaddr.Physaddr addr) 8) s = .ok false s)
    (hm0 : s.mem.get? addr.toNat = some b0) (hm1 : s.mem.get? (addr.toNat+1) = some b1)
    (hm2 : s.mem.get? (addr.toNat+2) = some b2) (hm3 : s.mem.get? (addr.toNat+3) = some b3)
    (hm4 : s.mem.get? (addr.toNat+4) = some b4) (hm5 : s.mem.get? (addr.toNat+5) = some b5)
    (hm6 : s.mem.get? (addr.toNat+6) = some b6) (hm7 : s.mem.get? (addr.toNat+7) = some b7) :
    checked_mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      Privilege.Machine (physaddr.Physaddr addr) 8 false false false false s
      = .ok (Result.Ok (reconstructDword s.mem addr.toNat, ())) s :=
  checked_mem_read_load_w 8 addr s _ cfgs pmpaddrs regions region
    (by right; right; right; rfl) h_cfg h_addr h_off h_reg h_match h_read h_align
    hclint hsig hhtif
    (readBytes8_raw s addr.toNat b0 b1 b2 b3 b4 b5 b6 b7 hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7)

/-- **`mem_read` for a bare-mode aligned readable width-`w` load (capstone of the
    `mem_read` chain).** Effective privilege is Machine (`MPRV=0`), the
    `(false,false,false)` flag arm dispatches to `checked_mem_read`, the callback is a
    no-op, and `drop_meta` strips the unit metadata. Returns `Ok v`, state untouched. -/
theorem mem_read_load_w (w : Nat) (addr : BitVec 64) (s : SailState) (mst : BitVec 64)
    (v : BitVec (8*w))
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
    (h_read : region.attributes.readable = true)
    (h_align : is_aligned_paddr (physaddr.Physaddr addr) w = true)
    (hclint : (within_clint (physaddr.Physaddr addr) w) s = .ok false s)
    (hsig : (within_sig (physaddr.Physaddr addr) w) s = .ok false s)
    (hhtif : (within_htif_readable (physaddr.Physaddr addr) w) s = .ok false s)
    (hread : (readBytes w addr.toNat : SailM ((BitVec (8*w)) × Option Bool)) s
      = .ok (v, none) s) :
    (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr addr) w false false false) s
      = .ok (Result.Ok v) s := by
  unfold mem_read mem_read_priv mem_read_priv_meta
  simp only [PreSail.readReg, h_priv, h_mst, pure, EStateM.pure, bind, EStateM.bind,
    get, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    effectivePrivilege_machine s _ mst _ h_mprv,
    checked_mem_read_load_w w addr s v cfgs pmpaddrs regions region hwlit
      h_cfg h_addr h_off h_reg h_match h_read h_align hclint hsig hhtif hread,
    MemoryOpResult_drop_meta]

/-- **`mem_read` for a bare-mode aligned readable doubleword load.** Width-8 instance of
    `mem_read_load_w`: returns `Ok (reconstructDword)`, state untouched. -/
theorem mem_read_load_bare (addr : BitVec 64) (s : SailState) (mst : BitVec 64)
    (cfgs : Vector (BitVec 8) 64) (pmpaddrs : Vector (BitVec 64) 64)
    (regions : List PMA_Region) (region : PMA_Region)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (h_mst : s.regs.get? Register.mstatus = some mst)
    (h_mprv : _get_Mstatus_MPRV mst = 0#1)
    (h_cfg : s.regs.get? Register.pmpcfg_n = some cfgs)
    (h_addr : s.regs.get? Register.pmpaddr_n = some pmpaddrs)
    (h_off : ∀ i : Nat,
      pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (cfgs[i]!)) = PmpAddrMatchType.OFF)
    (h_reg : s.regs.get? Register.pma_regions = some regions)
    (h_match : matching_pma_region regions (physaddr.Physaddr addr) 8 = some region)
    (h_read : region.attributes.readable = true)
    (h_align : is_aligned_paddr (physaddr.Physaddr addr) 8 = true)
    (hclint : (within_clint (physaddr.Physaddr addr) 8) s = .ok false s)
    (hsig : (within_sig (physaddr.Physaddr addr) 8) s = .ok false s)
    (hhtif : (within_htif_readable (physaddr.Physaddr addr) 8) s = .ok false s)
    (hm0 : s.mem.get? addr.toNat = some b0) (hm1 : s.mem.get? (addr.toNat+1) = some b1)
    (hm2 : s.mem.get? (addr.toNat+2) = some b2) (hm3 : s.mem.get? (addr.toNat+3) = some b3)
    (hm4 : s.mem.get? (addr.toNat+4) = some b4) (hm5 : s.mem.get? (addr.toNat+5) = some b5)
    (hm6 : s.mem.get? (addr.toNat+6) = some b6) (hm7 : s.mem.get? (addr.toNat+7) = some b7) :
    (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr addr) 8 false false false) s
      = .ok (Result.Ok (reconstructDword s.mem addr.toNat)) s :=
  mem_read_load_w 8 addr s mst _ cfgs pmpaddrs regions region
    (by right; right; right; rfl) h_priv h_mst h_mprv h_cfg h_addr h_off h_reg h_match
    h_read h_align hclint hsig hhtif
    (readBytes8_raw s addr.toNat b0 b1 b2 b3 b4 b5 b6 b7 hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7)

-- ============================================================================
-- Page-boundary split: an aligned power-of-two access never crosses a page
-- ============================================================================

/-- Adding `r < 2 ^ k` to a `2 ^ k`-aligned `Nat` does not change the quotient by any
    `2 ^ n` with `k ≤ n` (the addition cannot carry past bit `k`). -/
theorem add_small_div_pow_eq (a r k n : Nat) (hk : k ≤ n) (hr : r < 2 ^ k)
    (ha : a % 2 ^ k = 0) : (a + r) / 2 ^ n = a / 2 ^ n := by
  have hpow : (2:Nat) ^ k ∣ 2 ^ n := Nat.pow_dvd_pow 2 hk
  have hnpos : 0 < (2:Nat) ^ n := Nat.two_pow_pos n
  have hmdvd : (2:Nat) ^ k ∣ a % 2 ^ n := by
    refine Nat.dvd_of_mod_eq_zero ?_
    rw [Nat.mod_mod_of_dvd a hpow]
    exact ha
  have hmlt : a % 2 ^ n < 2 ^ n := Nat.mod_lt _ hnpos
  have hsum : a % 2 ^ n + r < 2 ^ n := by
    have hdvd : (2:Nat) ^ k ∣ (2 ^ n - a % 2 ^ n) := Nat.dvd_sub hpow hmdvd
    have hpos : 0 < 2 ^ n - a % 2 ^ n := by omega
    have := Nat.le_of_dvd hpos hdvd
    omega
  have hdecomp : a + r = 2 ^ n * (a / 2 ^ n) + (a % 2 ^ n + r) := by
    have := Nat.div_add_mod a (2 ^ n)
    omega
  rw [hdecomp, Nat.mul_add_div hnpos, Nat.div_eq_of_lt hsum, Nat.add_zero]

/-- Bit-level form of `add_small_div_pow_eq`: adding `r < 2 ^ k` to a `2 ^ k`-aligned
    `Nat` leaves every bit at position `≥ k` unchanged. -/
theorem testBit_add_small (a r k n : Nat) (hk : k ≤ n) (hr : r < 2 ^ k)
    (ha : a % 2 ^ k = 0) : (a + r).testBit n = a.testBit n := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow,
    add_small_div_pow_eq a r k n hk hr ha]

/-- **`split_on_page_boundary` on an aligned power-of-two access.** A `w`-aligned access
    of width `w ∈ {1,2,4,8}` stays inside its 4 KiB page (`addr` and `addr + w - 1` agree
    on all bits ≥ 12), so the split is `(w, 0)` — no next-page tail — and the state is
    untouched. In bare mode the tail is dead anyway (`do_split_access` is `false`), but
    the reduction still has to run this computation to completion. -/
theorem split_on_page_boundary_aligned (addr : BitVec 64) (w : Nat) (s : SailState)
    (hwlit : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8)
    (h_align : addr.toNat % w = 0) :
    (split_on_page_boundary addr w) s = .ok ((w : Int), (0 : Int)) s := by
  have hlt : addr.toNat < 2 ^ 64 := addr.isLt
  -- the incremented end address, in `Nat` form (no wraparound: `addr` is `w`-aligned)
  have hqval : (BitVec.subInt (BitVec.addInt addr (w : Int)) 1).toNat
      = addr.toNat + (w - 1) := by
    rcases hwlit with rfl | rfl | rfl | rfl <;>
    · simp only [BitVec.addInt, BitVec.subInt, BitVec.toNat_sub, BitVec.toNat_add,
        BitVec.toNat_ofInt]
      omega
  -- bits ≥ 12 agree between `addr` and `addr + (w-1)`
  have hbits : addr &&& (BitVec.allOnes 64 <<< 12)
      = (BitVec.subInt (BitVec.addInt addr (w : Int)) 1) &&& (BitVec.allOnes 64 <<< 12) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes]
    rcases Nat.lt_or_ge i 12 with h12 | h12
    · simp [h12]
    · have hk : ∃ k, k ≤ 3 ∧ w = 2 ^ k := by
        rcases hwlit with rfl | rfl | rfl | rfl
        · exact ⟨0, by decide, rfl⟩
        · exact ⟨1, by decide, rfl⟩
        · exact ⟨2, by decide, rfl⟩
        · exact ⟨3, by decide, rfl⟩
      obtain ⟨k, hk3, rfl⟩ := hk
      have htb : (addr.toNat + (2 ^ k - 1)).testBit i = addr.toNat.testBit i :=
        testBit_add_small addr.toNat (2 ^ k - 1) k i (by omega)
          (by have := Nat.two_pow_pos k; omega) h_align
      rw [← BitVec.testBit_toNat, ← BitVec.testBit_toNat, hqval, htb]
  unfold split_on_page_boundary
  split
  · rfl
  · -- the intra-page test cannot fail on an aligned power-of-two access: the page mask
    -- (a closed term, definitionally `0xFFFFFFFFFFFFF000#64 = allOnes <<< 12`) sees the
    -- same bits on both endpoints (`hbits`)
    rename_i hcond
    exfalso
    apply hcond
    rw [beq_iff_eq]
    -- unify the goal's (closed) page-mask term with `M`, then evaluate it by kernel
    -- computation — the mask's elaborated form need never be spelled out
    have hM : ∀ M : BitVec 64, M = BitVec.allOnes 64 <<< 12 →
        addr &&& M = BitVec.subInt (BitVec.addInt addr (w : Int)) 1 &&& M := by
      rintro M rfl
      exact hbits
    apply hM
    simp only [Sail.BitVec.length]
    decide

/-- The `Nat`-divisibility form of a Sail virtual-address alignment fact (the inverse
    of `RunInv.is_aligned_vaddr_of_toNat_mod`), for the power-of-two widths the
    reductions use. -/
theorem toNat_mod_of_is_aligned_vaddr (vaddr : virtaddr) (w : Nat)
    (hwlit : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8)
    (h : is_aligned_vaddr vaddr w = true) :
    (bits_of_virtaddr vaddr).toNat % w = 0 := by
  obtain ⟨a⟩ := vaddr
  unfold is_aligned_vaddr Sail.BitVec.toNatInt at h
  rw [beq_iff_eq] at h
  show a.toNat % w = 0
  rcases hwlit with rfl | rfl | rfl | rfl <;> exact Int.ofNat_inj.mp h

/-- **`translateAddr` + `mem_read`, fused.** In bare mode `translate_and_read_value`
    returns the (untranslated) physical address paired with the value the supplied
    `mem_read` reduction produces, state untouched. -/
theorem translate_and_read_value_load_bare (vaddr : virtaddr) (w : Nat) (s : SailState)
    (mst : BitVec 64) (v : BitVec (8*w))
    (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (h_mst : s.regs.get? Register.mstatus = some mst)
    (h_mprv : _get_Mstatus_MPRV mst = 0#1)
    (hmem : (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
        (physaddr.Physaddr (bits_of_virtaddr vaddr)) w false false false) s
      = .ok (Result.Ok v) s) :
    (translate_and_read_value vaddr w (MemoryAccessType.Load mem_payload.Data)
        false false false) s
      = .ok (Result.Ok (physaddr.Physaddr (bits_of_virtaddr vaddr), v)) s := by
  have htrans := translateAddr_bare s vaddr mst h_priv h_mst h_mprv
  unfold translate_and_read_value
  simp only [bind, EStateM.bind, htrans, zero_extend64_id, hmem, pure, EStateM.pure]

/-- **`vmem_read_addr` for a bare-mode aligned doubleword load.** The aligned access
    stays inside its page (`split_on_page_boundary` → `(8, 0)`) and translation is
    `Bare`, so no page-split happens and the access width is the full width;
    `translate_and_read_value` returns `reconstructDword` at the untranslated address
    (the split loop now lives inside `checked_mem_read`), and the full-width writeback
    keeps it. State untouched. -/
theorem vmem_read_addr_load_bare (vaddr : virtaddr) (s : SailState) (mst : BitVec 64)
    (cfgs : Vector (BitVec 8) 64) (pmpaddrs : Vector (BitVec 64) 64)
    (regions : List PMA_Region) (region : PMA_Region)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h_valign : is_aligned_vaddr vaddr 8 = true)
    (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (h_mst : s.regs.get? Register.mstatus = some mst)
    (h_mprv : _get_Mstatus_MPRV mst = 0#1)
    (h_cfg : s.regs.get? Register.pmpcfg_n = some cfgs)
    (h_pmpaddr : s.regs.get? Register.pmpaddr_n = some pmpaddrs)
    (h_off : ∀ i : Nat,
      pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (cfgs[i]!)) = PmpAddrMatchType.OFF)
    (h_reg : s.regs.get? Register.pma_regions = some regions)
    (h_match : matching_pma_region regions
      (physaddr.Physaddr (bits_of_virtaddr vaddr)) 8 = some region)
    (h_read : region.attributes.readable = true)
    (h_palign : is_aligned_paddr (physaddr.Physaddr (bits_of_virtaddr vaddr)) 8 = true)
    (hclint : (within_clint (physaddr.Physaddr (bits_of_virtaddr vaddr)) 8) s = .ok false s)
    (hsig : (within_sig (physaddr.Physaddr (bits_of_virtaddr vaddr)) 8) s = .ok false s)
    (hhtif : (within_htif_readable (physaddr.Physaddr (bits_of_virtaddr vaddr)) 8) s = .ok false s)
    (hm0 : s.mem.get? (bits_of_virtaddr vaddr).toNat = some b0)
    (hm1 : s.mem.get? ((bits_of_virtaddr vaddr).toNat+1) = some b1)
    (hm2 : s.mem.get? ((bits_of_virtaddr vaddr).toNat+2) = some b2)
    (hm3 : s.mem.get? ((bits_of_virtaddr vaddr).toNat+3) = some b3)
    (hm4 : s.mem.get? ((bits_of_virtaddr vaddr).toNat+4) = some b4)
    (hm5 : s.mem.get? ((bits_of_virtaddr vaddr).toNat+5) = some b5)
    (hm6 : s.mem.get? ((bits_of_virtaddr vaddr).toNat+6) = some b6)
    (hm7 : s.mem.get? ((bits_of_virtaddr vaddr).toNat+7) = some b7) :
    (vmem_read_addr vaddr 8 (MemoryAccessType.Load mem_payload.Data) false false false) s
      = .ok (Result.Ok (reconstructDword s.mem (bits_of_virtaddr vaddr).toNat)) s := by
  have halignN : (bits_of_virtaddr vaddr).toNat % 8 = 0 :=
    toNat_mod_of_is_aligned_vaddr vaddr 8 (by right; right; right; rfl) h_valign
  have hpage := split_on_page_boundary_aligned (bits_of_virtaddr vaddr) 8 s
    (by right; right; right; rfl) halignN
  have hmem := mem_read_load_bare (bits_of_virtaddr vaddr) s mst cfgs pmpaddrs regions region
    b0 b1 b2 b3 b4 b5 b6 b7 h_priv h_mst h_mprv h_cfg h_pmpaddr h_off h_reg h_match h_read
    h_palign hclint hsig hhtif hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7
  have htrv := translate_and_read_value_load_bare vaddr 8 s mst _ h_priv h_mst h_mprv hmem
  unfold vmem_read_addr
  simp +decide only [h_valign, Functions.not, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, if_false,
    SailME.run, PreSail.PreSailME.run,
    hpage, PreSail.readReg, h_priv, h_mst,
    effectivePrivilege_machine s _ mst _ h_mprv, translationMode_machine,
    sys_misaligned_order_decreasing, bne,
    show (SATPMode.Bare == SATPMode.Bare) = true from rfl,
    Bool.false_and, Bool.true_and,
    EStateM.map, bind, EStateM.bind, pure, EStateM.pure, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.lift, ExceptT.pure,
    MonadLift.monadLift, monadLift, liftM, Functor.map]
  -- collapse the (degenerate, both-branches-equal) `access_width` selector, which sits
  -- in type-determining positions simp's congruence cannot rewrite; `rw` can. Then land
  -- the fused translate+read leaf up to defeq (its width is `(↑8).toNat`, only
  -- definitionally `8`), and reduce the remaining plumbing.
  rw [show (if (false = true) then ((8 : Nat) : Int) else ((8 : Nat) : Int))
        = ((8 : Nat) : Int) from rfl]
  erw [htrv]
  simp only [EStateM.bind, EStateM.pure, ExceptT.bindCont]
  rw [show ((8 : Int) * ((8 : Nat) : Int) - 1).toNat = 63 from by omega]
  simp only [updateSubrange_full]
  erw [BitVec.setWidth_eq]

/-- `pm_transform_PA` with `pmlen = 0` is the identity: it extracts bits `63..0` of the
    64-bit address and zero-extends back to 64, both no-ops. -/
theorem pm_transform_PA_zero (x : BitVec 64) :
    pm_transform_PA (virtaddr.Virtaddr x) 0 = virtaddr.Virtaddr x := by
  unfold pm_transform_PA
  simp only [Functions.xlen]
  rw [show ((↑(64 : Nat) - ↑(0 : Nat) - 1 : Int)).toNat = 63 from by omega]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb, Nat.sub_zero, Nat.zero_add,
    hi, decide_true, Bool.true_and]

/-- **Bare-mode machine invariant.** Bundles the (access-independent) register-level
    facts that make a `Load Data` in M-mode reduce to a plain physical RAM read: Machine
    privilege, `MPRV = 0`, pointer-masking off (`mseccfg.PMM = 0`), and all 16 PMP entries
    `OFF`. The PMA region table is carried too (membership is an access-level fact). -/
structure BareModeInv (s : SailState) where
  mst : BitVec 64
  msec : BitVec 64
  cfgs : Vector (BitVec 8) 64
  pmpaddrs : Vector (BitVec 64) 64
  regions : List PMA_Region
  h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine
  h_mst : s.regs.get? Register.mstatus = some mst
  h_mprv : _get_Mstatus_MPRV mst = 0#1
  h_sec : s.regs.get? Register.mseccfg = some msec
  h_pmm : _get_Seccfg_PMM msec = 0#2
  h_cfg : s.regs.get? Register.pmpcfg_n = some cfgs
  h_pmpaddr : s.regs.get? Register.pmpaddr_n = some pmpaddrs
  h_off : ∀ i : Nat,
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (cfgs[i]!)) = PmpAddrMatchType.OFF
  h_reg : s.regs.get? Register.pma_regions = some regions

/-- **Transport a bare-mode invariant along a platform frame.** Every hypothesis
    field of `BareModeInv` is a read of a platform register that `PlatformFrame`
    pins, so the whole bundle moves to the post-state with its five data fields
    (`mst`, `msec`, `cfgs`, `pmpaddrs`, `regions`) unchanged.  This is how a
    downstream client re-establishes bare mode after an instruction step. -/
def BareModeInv.transport {s s' : SailState} (bm : BareModeInv s) (fr : PlatformFrame s s') :
    BareModeInv s' where
  mst := bm.mst
  msec := bm.msec
  cfgs := bm.cfgs
  pmpaddrs := bm.pmpaddrs
  regions := bm.regions
  h_priv := fr.priv_eq.trans bm.h_priv
  h_mst := fr.mstatus_eq.trans bm.h_mst
  h_mprv := bm.h_mprv
  h_sec := fr.mseccfg_eq.trans bm.h_sec
  h_pmm := bm.h_pmm
  h_cfg := fr.pmpcfg_eq.trans bm.h_cfg
  h_pmpaddr := fr.pmpaddr_eq.trans bm.h_pmpaddr
  h_off := bm.h_off
  h_reg := fr.pma_eq.trans bm.h_reg

/-- Transporting a bare-mode invariant keeps the PMA region table, so region-match
    side conditions stated against `bm.regions` survive verbatim. -/
@[simp] theorem BareModeInv.transport_regions {s s' : SailState} (bm : BareModeInv s)
    (fr : PlatformFrame s s') : (bm.transport fr).regions = bm.regions := rfl

/-- Transporting a bare-mode invariant keeps the `mseccfg` value. -/
@[simp] theorem BareModeInv.transport_msec {s s' : SailState} (bm : BareModeInv s)
    (fr : PlatformFrame s s') : (bm.transport fr).msec = bm.msec := rfl

/-- **`vmem_read` for a bare-mode aligned doubleword load.** The effective-address pipeline
    (`ext_data_get_addr` reads `rs`; `transform_effective_address` is the bare-mode identity)
    yields `rsval + offset`, then `vmem_read_addr` reads the doubleword. Returns
    `Ok (reconstructDword)` at `rsval + offset`, state untouched. -/
theorem vmem_read_load_bare (rs : regidx) (offset rsval : BitVec 64) (s : SailState)
    (bm : BareModeInv s) (region : PMA_Region)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h_rs : (rX_bits rs) s = .ok rsval s)
    (h_valign : is_aligned_vaddr (virtaddr.Virtaddr (rsval + offset)) 8 = true)
    (h_match : matching_pma_region bm.regions (physaddr.Physaddr (rsval + offset)) 8 = some region)
    (h_read : region.attributes.readable = true)
    (h_palign : is_aligned_paddr (physaddr.Physaddr (rsval + offset)) 8 = true)
    (hclint : (within_clint (physaddr.Physaddr (rsval + offset)) 8) s = .ok false s)
    (hsig : (within_sig (physaddr.Physaddr (rsval + offset)) 8) s = .ok false s)
    (hhtif : (within_htif_readable (physaddr.Physaddr (rsval + offset)) 8) s = .ok false s)
    (hm0 : s.mem.get? (rsval + offset).toNat = some b0)
    (hm1 : s.mem.get? ((rsval + offset).toNat+1) = some b1)
    (hm2 : s.mem.get? ((rsval + offset).toNat+2) = some b2)
    (hm3 : s.mem.get? ((rsval + offset).toNat+3) = some b3)
    (hm4 : s.mem.get? ((rsval + offset).toNat+4) = some b4)
    (hm5 : s.mem.get? ((rsval + offset).toNat+5) = some b5)
    (hm6 : s.mem.get? ((rsval + offset).toNat+6) = some b6)
    (hm7 : s.mem.get? ((rsval + offset).toNat+7) = some b7) :
    (vmem_read rs offset 8 (MemoryAccessType.Load mem_payload.Data) false false false) s
      = .ok (Result.Ok (reconstructDword s.mem (rsval + offset).toNat)) s := by
  obtain ⟨mst, msec, cfgs, pmpaddrs, regions, h_priv, h_mst, h_mprv, h_sec, h_pmm,
    h_cfg, h_pmpaddr, h_off, h_reg⟩ := bm
  have htransform := transform_effective_address_bare s
    (virtaddr.Virtaddr (rsval + offset)) mst msec h_priv h_mst h_mprv h_sec h_pmm
  have hvra := vmem_read_addr_load_bare (virtaddr.Virtaddr (rsval + offset)) s mst
    cfgs pmpaddrs regions region b0 b1 b2 b3 b4 b5 b6 b7
    h_valign h_priv h_mst h_mprv h_cfg h_pmpaddr h_off h_reg
    (by simpa using h_match) h_read (by simpa using h_palign)
    (by simpa using hclint) (by simpa using hsig) (by simpa using hhtif)
    (by simpa using hm0) (by simpa using hm1) (by simpa using hm2) (by simpa using hm3)
    (by simpa using hm4) (by simpa using hm5) (by simpa using hm6) (by simpa using hm7)
  unfold vmem_read get_transformed_data_addr ext_data_get_addr
  sail_reduce [h_rs, htransform, pm_transform_PA_zero, bits_of_virtaddr_mk, hvra]

/-- **`ld_sail_equiv` discharged — unconditional doubleword-load equivalence.** Given the
    abstraction relation, a bare-mode machine, and that the access is aligned, in a
    readable PMA region, off the MMIO ranges, and backed by present memory, the SAIL
    `execute_LOAD` (width 8) succeeds with `RETIRE_SUCCESS` and the resulting state is
    `StateRel`-related to the toy model's `LD`. No `h_exec` assumption. -/
theorem ld_sail_equiv (sRv : MachineState) (sSail : SailState)
    (rd rs1 : Reg) (offset : BitVec 12)
    (hrel : StateRel sRv sSail) (bm : BareModeInv sSail) (region : PMA_Region)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h_valign : is_aligned_vaddr
      (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 8 = true)
    (h_match : matching_pma_region bm.regions
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8 = some region)
    (h_read : region.attributes.readable = true)
    (h_palign : is_aligned_paddr
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8 = true)
    (hclint : (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8) sSail
      = .ok false sSail)
    (hsig : (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8) sSail
      = .ok false sSail)
    (hhtif : (within_htif_readable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8) sSail
      = .ok false sSail)
    (hm0 : sSail.mem.get? (sRv.getReg rs1 + signExtend12 offset).toNat = some b0)
    (hm1 : sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+1) = some b1)
    (hm2 : sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+2) = some b2)
    (hm3 : sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+3) = some b3)
    (hm4 : sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+4) = some b4)
    (hm5 : sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+5) = some b5)
    (hm6 : sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+6) = some b6)
    (hm7 : sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+7) = some b7) :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 8) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LD rd rs1 offset)) sSail' ∧
      sSail'.regs.get? Register.nextPC = sSail.regs.get? Register.nextPC ∧
      PlatformFrame sSail sSail' := by
  have soff : sign_extend (m := 64) offset = signExtend12 offset := by
    unfold sign_extend signExtend12 Sail.BitVec.signExtend; rfl
  have h_rs : (rX_bits (regToRegidx rs1)) sSail = .ok (sRv.getReg rs1) sSail :=
    runSail_eq_ok (runSail_rX_bits_of_stateRel hrel rs1)
  have hvr := vmem_read_load_bare (regToRegidx rs1) (signExtend12 offset) (sRv.getReg rs1) sSail
    bm region b0 b1 b2 b3 b4 b5 b6 b7 h_rs h_valign h_match h_read h_palign hclint hsig hhtif
    hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7
  have halign8 : (sRv.getReg rs1 + signExtend12 offset).toNat % 8 = 0 := by
    have h := h_valign
    unfold is_aligned_vaddr Sail.BitVec.toNatInt at h
    rw [beq_iff_eq] at h
    exact Int.ofNat_inj.mp h
  have hdata := hrel.mem_agree (sRv.getReg rs1 + signExtend12 offset) halign8
  refine ⟨sailStateWithReg sSail rd
      (reconstructDword sSail.mem (sRv.getReg rs1 + signExtend12 offset).toNat),
      ?_, ?_, ?_, ?_⟩
  · -- SAIL execution succeeds with RETIRE_SUCCESS
    unfold execute_LOAD
    simp +decide only [soff, runSail_bind, runSail_pure, PreSail.assert, if_true]
    rw [show runSail (vmem_read (regToRegidx rs1) (signExtend12 offset) 8
          (MemoryAccessType.Load mem_payload.Data) false false false) sSail
        = some (Result.Ok (reconstructDword sSail.mem
            (sRv.getReg rs1 + signExtend12 offset).toNat), sSail) from by
      simp only [runSail, hvr]]
    simp only [extend_value, Bool.false_eq_true, if_false, sign_extend,
      Sail.BitVec.signExtend, BitVec.signExtend_eq, runSail_bind, runSail_wX_bits_of_reg,
      runSail_pure]
  · -- abstraction relation holds for the post-state
    refine ⟨fun r => ?_, fun a ha => ?_⟩
    · rw [hdata]
      simpa [execInstrBr, MachineState.setPC]
        using reg_agree_after_insert sSail sRv hrel rd _ r
    · simpa [execInstrBr, MachineState.setPC, MachineState.getMem, sailStateWithReg_mem]
        using hrel.mem_agree a ha
  · simp
  · exact platformFrame_sailStateWithReg _ _ _

end EvmAsm.Rv64.SailEquiv
