/-
  EvmAsm.Codegen.Programs.SystemCallStagingResiduals

  The three named callee residuals of `stage_system_call` (#12206 item 1), one
  per `jal ra, …` site:

    index  7  (0x8005374c)  `account_read_record`         → `ArdCallShape`
    index 25  (0x80053794)  `stage_system_call_payload`    → `SscpCallShape`
    index 31  (0x800537ac)  `runtime_dispatcher_call`      → `RdcCallShape`

  WHY ALL THREE ARE RESIDUALS AND NOT COMPOSITIONS.

  * `account_read_record` IS rowed, but the triple
    (`accountReadRecordSuppressedFlat_spec`) is gated to the SUPPRESSED arm
    only — it assumes `runtime_tx_account_read_suppress ≠ 0`, which takes the
    `bnez` at its index 11 straight to the restore block.  `stage_system_call`
    establishes nothing about that global, so the three arms the gate excludes
    are exactly the ones the fall-through reaches.  There is no contract to
    compose at this call site.
  * `stage_system_call_payload` has a `_prog` (141 instructions) but **no
    triple and no registry row**.  It calls `stage_runtime_payload_code` and
    `stage_runtime_payload_witness_context` and carries three backward loops.
  * `runtime_dispatcher_call` has no triple — it is the whole EVM interpreter,
    and is the standing #12204 blocker.

  Per the issue's own licence ("state these triples under that named residual
  rather than waiting for it, per the walk precedent") each site therefore gets
  ONE named residual.  These are UNPROVEN-CALLEE **DEPENDENCIES**, not
  input-domain gates.

  WHAT THE RESIDUALS DELIBERATELY DO NOT SAY.  Nothing about what any callee
  *computes*.  `account_read_record` records "some" read; the payload stager
  returns "some" status word `stP`; the dispatcher leaves "some" return-data
  length `retLen` and "some" halt kind `hk`.  Every one of those is universally
  quantified by the shape's user.  That is what makes the `stage_system_call`
  contract both provable and honest: the status word `a2` it returns is set
  entirely by its OWN straight-line code (`li a2, 2` at index 52, `li a2, 0` at
  54, `li a2, 1` at 63), so `a2 ∈ {0,1,2}` — and the distinction between the
  staging-failure class `1` and the execution-failure class `2` that #11810 is
  emphatic about — holds no matter what any callee did.

  WHAT THE RESIDUALS DO SAY, AND WHY EACH CLAUSE IS THERE.  Each shape pins a
  small set of registers/cells as PRESERVED across the call, because the
  emitted code reads them afterwards.  Every one of those was measured against
  the callee's own emitted text rather than assumed:

  * `ArdCallShape` pins `t1` (`x6`), `a1` (`x11`), `a2` (`x12`), `a3` (`x13`)
    and `a4` (`x14`).  `accountReadRecord_prog` (AccountReadLog.lean:97) opens
    `addi sp,-64` + `sd t0..t6` at 0/8/16/24/32/40/48 and closes with the
    matching seven `ld` + `addi sp,64`; it writes only `t0`–`t6` and reads
    `a0`; it has no result register.  Its own docstring states this
    ("Clobbers nothing the caller can see").  `stage_system_call` depends on
    exactly that: it reads `t1` at index 8, `a2` at index 9 (the empty-code
    gate) and `a4` at index 10, and forwards `a1`/`a3` to the payload stager.
  * `SscpCallShape` pins `s0` (`x8`), read at index 27 (`addi t1, s0, 8`).
    `stageSystemCallPayload_prog` (SystemCallStaging.lean:...) opens
    `addi sp,-48` + `sd ra/s0/s1/s2/s3/s4` at 0/8/16/24/32/40 and closes with
    the matching six `ld` + `addi sp,48`, so `s0` is genuinely callee-saved.
  * All three pin `ssc_saved_ra ↦ ret` and `ssc_saved_s0 ↦ v8`, and
    `SscpCallShape` additionally pins `system_call_mode ↦ 1`.  Basis: a
    whole-image grep of the emitted `la` reloc tables for the symbols
    `ssc_saved_ra`, `ssc_saved_s0`, `system_call_mode`,
    `system_call_returndata_len`, `runtime_tx_auth_exec_fn` and
    `rdg_halt_kind` finds them referenced from exactly three routines —
    `stage_system_call` itself, `dispatcher_tx_gas_settle` (`rdg_halt_kind`)
    and `storage_read_log` (`system_call_mode`), both of which sit under
    `runtime_dispatcher_call`, not under `account_read_record` or
    `stage_system_call_payload`.  The guest addresses every global through a
    named `la`, so that grep is the write set.

  ⚠️ THE STRONGEST ASSUMPTION IN THIS FILE, stated plainly: `RdcCallShape`
  claims the whole EVM interpreter leaves `ssc_saved_ra` and `ssc_saved_s0`
  untouched.  That is precisely why those two cells are DEDICATED spill slots
  rather than shared scratch, and it is the reason `stage_system_call` is not
  re-entrant — a dispatcher path that re-entered `stage_system_call` would
  overwrite both and falsify this residual.  Discharge owner: #12204.

  ON FRAMES.  `cpsTripleWithin` quantifies over all frames `R`, so a register
  the footprint omits ENTIRELY can be instantiated by a caller as `r ↦ᵣ v`; a
  callee that writes it then falsifies the triple, and the residual becomes
  unsatisfiable — the exact vacuity trap of #10688.  Every register any of the
  three callees may clobber is therefore named, either concretely or through
  `sscScratchOwn`.  Carrying a clobbered register as `regOwn` is sound
  (`regOwn r` is `∃ v, regIs r v h`, so the pre and post witnesses may differ);
  what is NOT sound is carrying a CONCRETE `r ↦ᵣ v` for an `r` the callee
  writes, which is why each concrete preservation above is justified against a
  measured save/restore set rather than by convenience.
-/

import EvmAsm.Codegen.Programs.SystemCallStagingBase
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.SystemCallStagingResiduals

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.SystemCallStagingBase

/-! ## The clobber set

    Every general-purpose register that `stage_system_call` itself never names,
    held as OWNED so that no caller can frame it concretely and no callee's
    write can falsify a residual.  `x0`–`x2`, `x5`, `x6`, `x8`, `x10`–`x14`
    are the eleven the routine tracks by value and are therefore absent. -/
def sscScratchOwn : Assertion :=
  regOwn .x3 ** regOwn .x4 ** regOwn .x7 ** regOwn .x9 **
  regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x18 ** regOwn .x19 ** regOwn .x20 ** regOwn .x21 **
  regOwn .x22 ** regOwn .x23 ** regOwn .x24 ** regOwn .x25 **
  regOwn .x26 ** regOwn .x27 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

theorem sscScratchOwn_pcFree : sscScratchOwn.pcFree := by
  unfold sscScratchOwn
  repeat first | apply pcFree_sepConj | exact pcFree_regOwn

/-- The two dedicated spill cells, pinned across every call.  Split out so the
    one assumption every residual shares is visible in one place. -/
def sscSpillSaved (ret v8 : Word) : Assertion :=
  (SscRa ↦ₘ ret) ** (SscS0 ↦ₘ v8)

theorem sscSpillSaved_pcFree (ret v8 : Word) : (sscSpillSaved ret v8).pcFree := by
  unfold sscSpillSaved
  exact pcFree_sepConj pcFree_memIs pcFree_memIs

/-! ## Residual 1 — `account_read_record` at index 7 -/

/-- Call-site entry ambient for `account_read_record`: `a0` = the 20-byte
    big-endian target address pointer (its only input). -/
def ardCallEntry (sp0 tgt codePtr codeLen blockPayload payloadOut
    v5 v6 v8 ret : Word) (m : Nat) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m **
  (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x8 ↦ᵣ v8) **
  (.x10 ↦ᵣ tgt) ** (.x11 ↦ᵣ codePtr) ** (.x12 ↦ᵣ codeLen) **
  (.x13 ↦ᵣ blockPayload) ** (.x14 ↦ᵣ payloadOut) **
  sscScratchOwn ** sscSpillSaved ret v8

/-- Call-site return.  `t1` is pinned because index 8 reads it; `a1`/`a2`/`a3`/
    `a4` because indices 9/10 and the payload ABI read them.  `t0`, `s0` and
    `a0` are left ABSTRACT (`w5`/`w8`/`w10`) — the routine restores `a0` from
    `t1` at index 8 and does not depend on either. -/
def ardCallReturn (sp0 codePtr codeLen blockPayload payloadOut
    tgtSaved w5 w8 w10 ret v8 : Word) (m : Nat) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m **
  (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ tgtSaved) ** (.x8 ↦ᵣ w8) **
  (.x10 ↦ᵣ w10) ** (.x11 ↦ᵣ codePtr) ** (.x12 ↦ᵣ codeLen) **
  (.x13 ↦ᵣ blockPayload) ** (.x14 ↦ᵣ payloadOut) **
  sscScratchOwn ** sscSpillSaved ret v8

/-- The NON-TRIPLE side conditions of a call residual, split out so they can be
    discharged concretely against the emitted image — this is where a vacuity
    hole would hide.  `…CallSite_ok` in `SystemCallStagingTop` closes all four
    at the real call site.

    `callerPC` and `calleeEntry` are parameters precisely so a negative control
    can exhibit a site where the reloc conjunct is provably FALSE. -/
def CallSiteOk (cr : CodeReq) (callerPC calleeEntry : Word)
    (offset : BitVec 21) (F : Assertion) : Prop :=
  F.pcFree ∧
  ((callerPC + 4) &&& ~~~(1 : Word)) = callerPC + 4 ∧
  callerPC + signExtend21 offset = calleeEntry ∧
  (∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i →
    cr a = some i)

/-- Shape the residual `h_ard` must satisfy at index 7. -/
def ArdCallShape (cr : CodeReq)
    (callerPC vOld sp0 tgt codePtr codeLen blockPayload payloadOut
     v5 v6 v8 w5 w8 w10 ret : Word)
    (m : Nat) (offset : BitVec 21) (fuel : Nat) (F : Assertion) : Prop :=
  CallSiteOk cr callerPC ArdB offset F ∧
  cpsTripleWithin (1 + fuel) callerPC (callerPC + 4) cr
    (((.x1 ↦ᵣ vOld) **
      ardCallEntry sp0 tgt codePtr codeLen blockPayload payloadOut
        v5 v6 v8 ret m) ** F)
    (((.x1 ↦ᵣ (callerPC + 4)) **
      ardCallReturn sp0 codePtr codeLen blockPayload payloadOut
        tgt w5 w8 w10 ret v8 m) ** F)

/-! ## Residual 2 — `stage_system_call_payload` at index 25 -/

/-- Call-site entry ambient for `stage_system_call_payload`: `a0`–`a4` are the
    five staging arguments the routine forwarded, `s0` already holds the output
    payload buffer, and `system_call_mode` is 1 (the NoopHalt capture flag set
    at index 18). -/
def sscpCallEntry (sp0 tgt codePtr codeLen blockPayload payloadOut
    v5 v6 ret v8 : Word) (m : Nat) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m **
  (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x8 ↦ᵣ payloadOut) **
  (.x10 ↦ᵣ tgt) ** (.x11 ↦ᵣ codePtr) ** (.x12 ↦ᵣ codeLen) **
  (.x13 ↦ᵣ blockPayload) ** (.x14 ↦ᵣ payloadOut) **
  sscScratchOwn ** sscSpillSaved ret v8 ** (SccMode ↦ₘ (1 : Word))

/-- Call-site return: `a0` holds SOME status word `stP` (nothing is claimed
    about its value), `s0` is preserved because it is callee-saved and index 27
    reads it, and everything else is abstract. -/
def sscpCallReturn (sp0 payloadOut stP u5 u6 u11 u12 u13 u14 ret v8 : Word)
    (m : Nat) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m **
  (.x5 ↦ᵣ u5) ** (.x6 ↦ᵣ u6) ** (.x8 ↦ᵣ payloadOut) **
  (.x10 ↦ᵣ stP) ** (.x11 ↦ᵣ u11) ** (.x12 ↦ᵣ u12) **
  (.x13 ↦ᵣ u13) ** (.x14 ↦ᵣ u14) **
  sscScratchOwn ** sscSpillSaved ret v8 ** (SccMode ↦ₘ (1 : Word))

/-- Shape the residual `h_sscp` must satisfy at index 25. -/
def SscpCallShape (cr : CodeReq)
    (callerPC vOld sp0 tgt codePtr codeLen blockPayload payloadOut
     v5 v6 stP u5 u6 u11 u12 u13 u14 ret v8 : Word)
    (m : Nat) (offset : BitVec 21) (fuel : Nat) (F : Assertion) : Prop :=
  CallSiteOk cr callerPC SscpB offset F ∧
  cpsTripleWithin (1 + fuel) callerPC (callerPC + 4) cr
    (((.x1 ↦ᵣ vOld) **
      sscpCallEntry sp0 tgt codePtr codeLen blockPayload payloadOut
        v5 v6 ret v8 m) ** F)
    (((.x1 ↦ᵣ (callerPC + 4)) **
      sscpCallReturn sp0 payloadOut stP u5 u6 u11 u12 u13 u14 ret v8 m) ** F)

/-! ## Residual 3 — `runtime_dispatcher_call` at index 31 -/

/-- Call-site entry ambient for the dispatcher: `runtime_dispatcher_input_ptr`
    points at `s0 + 8` and `system_call_mode` is 1, so a depth-0 `RETURN` from
    the predeploy is captured into `system_call_returndata` (NoopHalt, #8681)
    rather than halting the guest. -/
def rdcCallEntry (sp0 payloadOut r5 r6 r10 r11 r12 r13 r14 ret v8 : Word)
    (m : Nat) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m **
  (.x5 ↦ᵣ r5) ** (.x6 ↦ᵣ r6) ** (.x8 ↦ᵣ payloadOut) **
  (.x10 ↦ᵣ r10) ** (.x11 ↦ᵣ r11) ** (.x12 ↦ᵣ r12) **
  (.x13 ↦ᵣ r13) ** (.x14 ↦ᵣ r14) **
  sscScratchOwn ** sscSpillSaved ret v8 **
  (SccMode ↦ₘ (1 : Word)) ** (RdInPtr ↦ₘ (payloadOut + BitVec.ofNat 64 8)) **
  (SccLen ↦ₘ (0 : Word)) ** (RdgHalt ↦ₘ (0 : Word)) ** (RtAuthFn ↦ₘ (0 : Word))

/-- Call-site return.  EVERY register is abstract — the routine reloads `s0`
    and `ra` from the two spill cells and recomputes `a0`/`a1`/`a2` from
    scratch, so it depends on no register the interpreter leaves behind.
    `system_call_returndata_len` holds SOME `retLen` and `rdg_halt_kind` SOME
    `hk`; those are the two cells indices 43 and 46 read, and they are
    universally quantified by the shape's user.  `system_call_mode`,
    `runtime_dispatcher_input_ptr` and `runtime_tx_auth_exec_fn` come back
    merely OWNED: the dispatcher may write all three (it does — see
    `Codegen/Dispatch.lean`), and the routine overwrites the first two and
    never reads the third. -/
def rdcCallReturn (sp0 retLen hk q5 q6 q8 q10 q11 q12 q13 q14 ret v8 : Word)
    (m : Nat) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m **
  (.x5 ↦ᵣ q5) ** (.x6 ↦ᵣ q6) ** (.x8 ↦ᵣ q8) **
  (.x10 ↦ᵣ q10) ** (.x11 ↦ᵣ q11) ** (.x12 ↦ᵣ q12) **
  (.x13 ↦ᵣ q13) ** (.x14 ↦ᵣ q14) **
  sscScratchOwn ** sscSpillSaved ret v8 **
  memOwn SccMode ** memOwn RdInPtr **
  (SccLen ↦ₘ retLen) ** (RdgHalt ↦ₘ hk) ** memOwn RtAuthFn

/-- Shape the residual `h_rdc` must satisfy at index 31. -/
def RdcCallShape (cr : CodeReq)
    (callerPC vOld sp0 payloadOut r5 r6 r10 r11 r12 r13 r14
     retLen hk q5 q6 q8 q10 q11 q12 q13 q14 ret v8 : Word)
    (m : Nat) (offset : BitVec 21) (fuel : Nat) (F : Assertion) : Prop :=
  CallSiteOk cr callerPC RdcB offset F ∧
  cpsTripleWithin (1 + fuel) callerPC (callerPC + 4) cr
    (((.x1 ↦ᵣ vOld) **
      rdcCallEntry sp0 payloadOut r5 r6 r10 r11 r12 r13 r14 ret v8 m) ** F)
    (((.x1 ↦ᵣ (callerPC + 4)) **
      rdcCallReturn sp0 retLen hk q5 q6 q8 q10 q11 q12 q13 q14 ret v8 m) ** F)

/-! ## Obligation-retirement notes -/

/-- Rendered into `Progress.Obligations`. -/
def sscResidualNote : String :=
  "stage_system_call's three `jal ra` sites each stand under ONE named \
residual: `ArdCallShape` (index 7, account_read_record), `SscpCallShape` \
(index 25, stage_system_call_payload) and `RdcCallShape` (index 31, \
runtime_dispatcher_call). All three are UNPROVEN-CALLEE residual \
DEPENDENCIES, not input-domain gates. account_read_record IS rowed but only \
on the SUPPRESSED arm (`runtime_tx_account_read_suppress ≠ 0`), which \
stage_system_call does not establish, so that row is not composable here; \
stage_system_call_payload has a `_prog` but no triple and no row; \
runtime_dispatcher_call is the whole interpreter and is the standing #12204 \
blocker. Each shape leaves what the callee COMPUTES abstract — the payload \
status `stP`, the return-data length `retLen` and the halt kind `hk` are all \
universally quantified — so the `stage_system_call` post is proved against \
ANY callee behaviour. The strongest thing assumed is that the interpreter \
leaves `ssc_saved_ra`/`ssc_saved_s0` untouched, which is why those are \
dedicated spill cells and why the routine is not re-entrant. Discharge \
owners, in order: stage_system_call_payload's own triple, then #12204."

end EvmAsm.Codegen.SystemCallStagingResiduals
