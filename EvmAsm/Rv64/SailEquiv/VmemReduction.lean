/-
  EvmAsm.Rv64.SailEquiv.VmemReduction

  Building blocks for discharging the `h_exec` hypothesis carried by the `MemProofs`
  `*_sail_equiv` lemmas — i.e. for proving the SAIL `execute_LOAD`/`execute_STORE`
  bare-mode `vmem_read`/`vmem_write` reduction the original lemmas defer.

  This file currently establishes **lemma #1**: the leaf data-correctness bridge tying
  the SAIL physical read (`readBytes`, which appends bytes little-endian) to the
  abstraction relation's `reconstructDword`. With all `width` bytes present in `mem`,
  `readBytes 8 a` succeeds and yields exactly `reconstructDword sSail.mem a` — so the
  value a doubleword `LOAD` writes back is provably the toy model's `getMem` value.

  Remaining building blocks (for the full discharge, see
  `docs/agents/sail-memory-discharge-bootstrap.md`): the `pmpCheck` 16-entry loop, the
  `untilFuelM` single-iteration reduction, `translateAddr` bare-mode, and `pmaCheck`
  region membership — each consuming part of the bare-mode precondition bundle.
-/

import EvmAsm.Rv64.SailEquiv.MemProofs

open Out
open Out.Functions
open Sail
open PreSail

namespace EvmAsm.Rv64.SailEquiv

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

end EvmAsm.Rv64.SailEquiv
