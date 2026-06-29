/-
  EvmAsm.Rv64.SailEquiv.MemMonad

  The Sail monadic reduction (Phase 2, step #2): symbolically executing the Sail
  golden model's `execute_STORE`/`execute_LOAD` to a closed-form state update, for
  an aligned access in bare Machine mode.  Built bottom-up as per-layer `runSail_*`
  lemmas (the `runSail_jump_to` pattern in `MonadLemmas.lean`).

  This file starts with the generic loop lemma `untilFuelM_one` that the
  single-chunk (aligned) `vmem_*_addr` loop needs.
-/

import EvmAsm.Rv64.SailEquiv.MonadLemmas
import EvmAsm.Rv64.SailEquiv.MemReduce

open Sail
open LeanRV64D.Functions

namespace EvmAsm.Rv64.SailEquiv

/-- `untilFuelM` with fuel 1 and a **pure** loop condition runs the body exactly
    once and returns its result (the condition is evaluated but has no effect).
    For an aligned access `split_misaligned` gives `n = 1`, so the `vmem_*_addr`
    loop is this single iteration. -/
theorem untilFuelM_one_pure {α : Type} (g : α → Bool) (init : α) (f : α → SailM α) :
    untilFuelM 1 (fun x => (Pure.pure (g x) : SailM Bool)) init f = f init := by
  unfold untilFuelM
  simp [untilFuelM.go]

/-- Sail's `writeBytes` stores byte `i` as `v.extractLsb' (8*i) 8`; our reassembly
    lemmas (`MemReduce`) are stated with `extractByte`. They coincide. -/
theorem extractByte_eq_extractLsb' (v : Word) (i : Nat) :
    extractByte v i = v.extractLsb' (8 * i) 8 := by
  simp only [extractByte, BitVec.extractLsb', Nat.mul_comm i 8]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]

/-- State effect of an 8-byte `writeBytes`: registers unchanged; the doubleword's
    eight little-endian byte slices are written at `addr … addr+7`, everything else
    left alone. -/
theorem writeBytes_effect (addr : Nat) (v : BitVec 64) (s : SailState) :
    runSail (PreSail.writeBytes (n := 8) addr v) s = some (true,
      { s with mem :=
        (((((((s.mem.insert addr (v.extractLsb' 0 8)).insert (addr + 1) (v.extractLsb' 8 8)).insert
          (addr + 2) (v.extractLsb' 16 8)).insert (addr + 3) (v.extractLsb' 24 8)).insert
          (addr + 4) (v.extractLsb' 32 8)).insert (addr + 5) (v.extractLsb' 40 8)).insert
          (addr + 6) (v.extractLsb' 48 8)).insert (addr + 7) (v.extractLsb' 56 8) }) := by
  simp [runSail, PreSail.writeBytes, List.ofFn_succ, List.ofFn_zero, List.forM_cons, List.forM_nil,
    PreSail.writeByte, modify, modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet,
    EStateM.modifyGet, Bind.bind, bind, EStateM.bind, Pure.pure, EStateM.pure, Fin.succ]

/-- **Bare-mode address translation.** In Machine privilege with `MPRV = 0` and a
    non-shadow-stack access, `translateAddr` is the identity: it returns
    `Ok (Physaddr vaddr, PBMT_PMA, ())` and leaves the state unchanged. -/
theorem runSail_translateAddr_bare (vAddr : virtaddr) (access : MemoryAccessType mem_payload)
    (s : SailState) (mstatusVal : BitVec 64)
    (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (h_mstatus : s.regs.get? Register.mstatus = some mstatusVal)
    (h_mprv : _get_Mstatus_MPRV mstatusVal = 0#1)
    (h_ss : is_shadow_stack_access access = Pure.pure false) :
    runSail (translateAddr vAddr access) s =
      some (Ok (physaddr.Physaddr (zero_extend (m := 64) (bits_of_virtaddr vAddr)),
        page_based_mem_type.PBMT_PMA, init_ext_ptw), s) := by
  unfold translateAddr
  simp (config := { decide := true }) [runSail, SailME.run, PreSail.PreSailME.run,
    effectivePrivilege, translationMode, h_ss, h_mprv,
    PreSail.readReg, h_priv, h_mstatus,
    ExceptT.run, ExceptT.mk, ExceptT.pure, ExceptT.bind, ExceptT.bindCont, ExceptT.lift,
    MonadLift.monadLift, monadLift, liftM, Functor.map,
    Pure.pure, EStateM.pure, Bind.bind, bind, EStateM.bind, EStateM.map, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get, bne]

/-- `write_ram` (plain write of a doubleword) reduces to its underlying
    `writeBytes`: the physical-memory interface decomposes the value into
    little-endian bytes and returns success. -/
theorem runSail_write_ram (addr : physaddrbits) (data : BitVec 64) (s : SailState) :
    runSail (write_ram write_kind.Write_plain (physaddr.Physaddr addr) 8 data ()) s =
      runSail (PreSail.writeBytes (n := 8) addr.toNat data) s := by
  rw [writeBytes_effect]
  unfold write_ram
  simp [runSail, PreSail.ConcurrencyInterfaceV1.sail_mem_write, PreSail.writeBytes,
    List.ofFn_succ, List.ofFn_zero,
    List.forM_cons, List.forM_nil, PreSail.writeByte, modify, modifyGet,
    MonadStateOf.modifyGet, MonadState.modifyGet, EStateM.modifyGet,
    Bind.bind, bind, EStateM.bind, Pure.pure, EStateM.pure, Fin.succ]

end EvmAsm.Rv64.SailEquiv
