/-
  EvmAsm.Codegen.Programs.SystemCallStagingTop

  The whole-routine triple for `stage_system_call` (#12206 item 1).

  The routine has no ABI stack frame — it spills `ra`/`s0` to the dedicated BSS
  cells `ssc_saved_ra`/`ssc_saved_s0` — so `abiFrame_spec` does not apply and
  all 71 instructions are chained by hand.  The per-segment triples live in
  `SystemCallStagingSegments`; this module adds the three call sites, the
  whole-routine triple that stitches the segments together, and the
  non-vacuity evidence.

  Body chain (each address re-derived from the linked guest ELF):
    pc 0  → pc 6    spill `ra` and `s0` to their two BSS cells
    pc 6  → pc 7    `mv t1, a0`
    pc 7  → pc 8    `jal account_read_record`         — NAMED RESIDUAL
    pc 8  → pc 9    `mv a0, t1`
    pc 9            `beqz a2` — the EMPTY-CODE gate, to pc 56
    pc 10 → pc 25   park `a4` in `s0`; zero len / auth-fn / halt-kind;
                    `system_call_mode := 1`
    pc 25 → pc 26   `jal stage_system_call_payload`   — NAMED RESIDUAL
    pc 26           `bnez a0` — the PAYLOAD-REJECT gate, to pc 56
    pc 27 → pc 31   `runtime_dispatcher_input_ptr := s0 + 8`
    pc 31 → pc 32   `jal runtime_dispatcher_call`     — NAMED RESIDUAL
    pc 32 → pc 47   clear input ptr and `system_call_mode`; load
                    `a0 := &system_call_returndata`, `a1 := [len]`,
                    `t1 := [rdg_halt_kind]`
    pc 47 → pc 64   the three-way halt-kind cascade (`sscExecStatus`)
    pc 56 → pc 64   the shared staging-failure epilogue (`a2 := 1`)
    pc 64 → ret     restore `s0` and `ra` from their cells and `ret`

  THE THREE EXIT CODES all appear in the post, through `sscStatus`:
    `a2 = 1` staging failure  — empty code (pc 9) or payload reject (pc 26)
    `a2 = 2` execution failure — dispatch ran, `rdg_halt_kind ∉ {0,1,5}`
    `a2 = 0` success           — dispatch ran, `rdg_halt_kind ∈ {0,1,5}`

  **Why this contract is worth having even with three uncontracted callees.**
  `a2` is written ONLY by this routine's own straight-line code, at indices 52,
  54 and 63.  So `a2 ∈ {0,1,2}`, and `a2 = 1 ↔ the staging-failure path was
  taken`, are callee-INDEPENDENT: they hold for every instantiation of the
  three residuals.  That is exactly the property the routine's docstring
  (SystemCallStaging.lean:236-255, #11810) is emphatic about — the unchecked
  4788/2935 callers reject only `a2 = 1` and must ignore `a2 = 2`, so
  collapsing the two classes is a soundness bug.  Also callee-independent on
  the failure path: `a1 = 0`, `a0 = &system_call_returndata`, and
  `system_call_mode = 0`.
-/

import EvmAsm.Codegen.Programs.SystemCallStagingSegments
import EvmAsm.Rv64.SAsm.Fn
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.SystemCallStagingTop

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.SystemCallStagingBase
open EvmAsm.Codegen.SystemCallStagingResiduals
open EvmAsm.Codegen.SystemCallStagingSegments

set_option maxRecDepth 20000

local macro "pcfR" : tactic =>
  `(tactic| repeat' first
      | exact pcFree_stackFree _ _
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact sscScratchOwn_pcFree
      | exact sscSpillSaved_pcFree _ _
      | apply pcFree_sepConj)

/-! ## The three call sites

    Each steps over one `jal ra, callee` from its named residual.  Nothing
    about any callee is assumed here beyond what the shape states. -/

theorem ssc_ard_call (sp0 tgt codePtr codeLen blockPayload payloadOut
    v5 v6 v8 w5 w8 w10 ret vOld : Word) (m fuel : Nat) (F : Assertion)
    (h_ard : ArdCallShape sscCode (pc 7) vOld sp0 tgt codePtr codeLen blockPayload
      payloadOut v5 v6 v8 w5 w8 w10 ret m
      (jalOff GuestAddrs.account_read_record (GuestAddrs.stage_system_call + 28))
      fuel F) :
    cpsTripleWithin (1 + fuel) (pc 7) (pc 8) sscCode
      (((.x1 ↦ᵣ vOld) **
        ardCallEntry sp0 tgt codePtr codeLen blockPayload payloadOut
          v5 v6 v8 ret m) ** F)
      (((.x1 ↦ᵣ (pc 8)) **
        ardCallReturn sp0 codePtr codeLen blockPayload payloadOut
          tgt w5 w8 w10 ret v8 m) ** F) := by
  obtain ⟨_, hcall⟩ := h_ard
  rwa [pc_next 7 8 rfl] at hcall

theorem ssc_sscp_call (sp0 tgt codePtr codeLen blockPayload payloadOut
    v5 v6 stP u5 u6 u11 u12 u13 u14 ret v8 vOld : Word) (m fuel : Nat) (F : Assertion)
    (h_sscp : SscpCallShape sscCode (pc 25) vOld sp0 tgt codePtr codeLen blockPayload
      payloadOut v5 v6 stP u5 u6 u11 u12 u13 u14 ret v8 m
      (jalOff GuestAddrs.stage_system_call_payload (GuestAddrs.stage_system_call + 100))
      fuel F) :
    cpsTripleWithin (1 + fuel) (pc 25) (pc 26) sscCode
      (((.x1 ↦ᵣ vOld) **
        sscpCallEntry sp0 tgt codePtr codeLen blockPayload payloadOut
          v5 v6 ret v8 m) ** F)
      (((.x1 ↦ᵣ (pc 26)) **
        sscpCallReturn sp0 payloadOut stP u5 u6 u11 u12 u13 u14 ret v8 m) ** F) := by
  obtain ⟨_, hcall⟩ := h_sscp
  rwa [pc_next 25 26 rfl] at hcall

theorem ssc_rdc_call (sp0 payloadOut r5 r6 r10 r11 r12 r13 r14
    retLen hk q5 q6 q8 q10 q11 q12 q13 q14 ret v8 vOld : Word)
    (m fuel : Nat) (F : Assertion)
    (h_rdc : RdcCallShape sscCode (pc 31) vOld sp0 payloadOut r5 r6 r10 r11 r12 r13 r14
      retLen hk q5 q6 q8 q10 q11 q12 q13 q14 ret v8 m
      (jalOff GuestAddrs.runtime_dispatcher_call (GuestAddrs.stage_system_call + 124))
      fuel F) :
    cpsTripleWithin (1 + fuel) (pc 31) (pc 32) sscCode
      (((.x1 ↦ᵣ vOld) **
        rdcCallEntry sp0 payloadOut r5 r6 r10 r11 r12 r13 r14 ret v8 m) ** F)
      (((.x1 ↦ᵣ (pc 32)) **
        rdcCallReturn sp0 retLen hk q5 q6 q8 q10 q11 q12 q13 q14 ret v8 m) ** F) := by
  obtain ⟨_, hcall⟩ := h_rdc
  rwa [pc_next 31 32 rfl] at hcall

/-! ### The residuals' computable side conditions, discharged at the REAL sites

    Without these, each `…CallShape` could be unsatisfiable and the whole
    triple vacuous.  Each closes all four conjuncts of `CallSiteOk` against the
    emitted image: the `jal` reloc really resolves to the callee's entry, the
    return address really is even, and the `jal` really is the instruction at
    that index. -/

theorem ardCallSite_ok (F : Assertion) (hF : F.pcFree) :
    CallSiteOk sscCode (pc 7) ArdB
      (jalOff GuestAddrs.account_read_record (GuestAddrs.stage_system_call + 28)) F :=
  ⟨hF, ra_ard_aligned, pc_jal_ard,
    mem_at 7 _ (pc 7) rfl (by rw [sscProgL_len]; norm_num) (by decide)⟩

theorem sscpCallSite_ok (F : Assertion) (hF : F.pcFree) :
    CallSiteOk sscCode (pc 25) SscpB
      (jalOff GuestAddrs.stage_system_call_payload
        (GuestAddrs.stage_system_call + 100)) F :=
  ⟨hF, ra_sscp_aligned, pc_jal_sscp,
    mem_at 25 _ (pc 25) rfl (by rw [sscProgL_len]; norm_num) (by decide)⟩

theorem rdcCallSite_ok (F : Assertion) (hF : F.pcFree) :
    CallSiteOk sscCode (pc 31) RdcB
      (jalOff GuestAddrs.runtime_dispatcher_call
        (GuestAddrs.stage_system_call + 124)) F :=
  ⟨hF, ra_rdc_aligned, pc_jal_rdc,
    mem_at 31 _ (pc 31) rfl (by rw [sscProgL_len]; norm_num) (by decide)⟩

/-- `ssc_tail` entered with `t0` merely OWNED — the shape it comes back in from
    the verdict cascade, which leaves `t0` holding `1` or `5` depending on the
    halt kind. -/
theorem ssc_tail_own (ret v8 b1 b8 : Word) (halign : (ret &&& ~~~(1 : Word)) = ret)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 7 (pc 64) ret sscCode
      (regOwn .x5 ** (.x8 ↦ᵣ b8) ** (.x1 ↦ᵣ b1) **
        (SscS0 ↦ₘ v8) ** (SscRa ↦ₘ ret) ** F)
      ((.x5 ↦ᵣ SscRa) ** (.x8 ↦ᵣ v8) ** (.x1 ↦ᵣ ret) **
        (SscS0 ↦ₘ v8) ** (SscRa ↦ₘ ret) ** F) := by
  have h : ∀ b5, cpsTripleWithin 7 (pc 64) ret sscCode
      (((.x8 ↦ᵣ b8) ** (.x1 ↦ᵣ b1) ** (SscS0 ↦ₘ v8) ** (SscRa ↦ₘ ret) ** F) **
        (.x5 ↦ᵣ b5))
      ((.x5 ↦ᵣ SscRa) ** (.x8 ↦ᵣ v8) ** (.x1 ↦ᵣ ret) **
        (SscS0 ↦ₘ v8) ** (SscRa ↦ₘ ret) ** F) := fun b5 =>
    cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
      (ssc_tail ret v8 b1 b5 b8 halign F hF)
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5) h)

/-! ## The whole-routine footprint -/

/-- `stage_system_call`'s precondition.  `a0`–`a4` are the five staging
    arguments (`tgt`, `codePtr`, `codeLen`, `blockPayload`, `payloadOut`),
    `ra` the return address, `sp` a stack with `m` free dwords below it for the
    callees' frames.  The seven BSS cells the routine touches are owned; every
    register the routine does not name rides in `sscScratchOwn` so that no
    caller can pin one a callee clobbers. -/
def sscPre (sp0 tgt codePtr codeLen blockPayload payloadOut v5 v6 v8 ret : Word)
    (m : Nat) (A : Assertion) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m **
  (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x8 ↦ᵣ v8) **
  (.x10 ↦ᵣ tgt) ** (.x11 ↦ᵣ codePtr) ** (.x12 ↦ᵣ codeLen) **
  (.x13 ↦ᵣ blockPayload) ** (.x14 ↦ᵣ payloadOut) ** sscScratchOwn **
  memOwn SscRa ** memOwn SscS0 ** memOwn SccMode ** memOwn SccLen **
  memOwn RtAuthFn ** memOwn RdgHalt ** memOwn RdInPtr ** A

/-- `stage_system_call`'s postcondition.

    The three caller-visible results are `a0 = &system_call_returndata`,
    `a1 = sscRetLen codeLen stP retLen` and `a2 = sscStatus codeLen stP hk`;
    `system_call_mode` is cleared on every path, and `ra`/`s0` come back from
    the two spill cells.  `t1`, `a3`, `a4` and four of the cells are left OWNED
    because their final values genuinely differ between the three exits. -/
def sscPost (sp0 ret v8 codeLen stP hk retLen : Word) (m : Nat) (A : Assertion) :
    Assertion :=
  regOwn .x6 ** regOwn .x13 ** regOwn .x14 **
  memOwn SccLen ** memOwn RdgHalt ** memOwn RdInPtr ** memOwn RtAuthFn **
  (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m **
  (.x5 ↦ᵣ SscRa) ** (.x8 ↦ᵣ v8) ** (.x10 ↦ᵣ SccData) **
  (.x11 ↦ᵣ sscRetLen codeLen stP retLen) **
  (.x12 ↦ᵣ sscStatus codeLen stP hk) ** sscScratchOwn **
  (SscRa ↦ₘ ret) ** (SscS0 ↦ₘ v8) ** (SccMode ↦ₘ (0 : Word)) ** A

/-- Whole-routine step budget: 61 of the routine's own steps on its longest
    path (the dispatch path, indices 0–46 plus the seven-step halt-kind cascade
    and the seven-step restore block), plus the three residual fuels. -/
def sscFuel (fArd fSscp fRdc : Nat) : Nat := 61 + fArd + fSscp + fRdc

/-! ### Exit weakenings, one per path -/

private theorem exit_weaken_A (a6 a13 a14 : Word) (Rest : Assertion) :
    ∀ h, ((.x6 ↦ᵣ a6) ** (.x13 ↦ᵣ a13) ** (.x14 ↦ᵣ a14) ** Rest) h →
      (regOwn .x6 ** regOwn .x13 ** regOwn .x14 ** Rest) h :=
  sepConj_mono (fun _ hv => ⟨a6, hv⟩)
    (sepConj_mono (fun _ hv => ⟨a13, hv⟩)
      (sepConj_mono_left (fun _ hv => ⟨a14, hv⟩)))

private theorem exit_weaken_B (a6 a13 a14 cl ch af : Word) (Rest : Assertion) :
    ∀ h, ((.x6 ↦ᵣ a6) ** (.x13 ↦ᵣ a13) ** (.x14 ↦ᵣ a14) **
        (SccLen ↦ₘ cl) ** (RdgHalt ↦ₘ ch) ** memOwn RdInPtr **
        (RtAuthFn ↦ₘ af) ** Rest) h →
      (regOwn .x6 ** regOwn .x13 ** regOwn .x14 **
        memOwn SccLen ** memOwn RdgHalt ** memOwn RdInPtr **
        memOwn RtAuthFn ** Rest) h :=
  sepConj_mono (fun _ hv => ⟨a6, hv⟩)
    (sepConj_mono (fun _ hv => ⟨a13, hv⟩)
      (sepConj_mono (fun _ hv => ⟨a14, hv⟩)
        (sepConj_mono (fun _ hv => ⟨cl, hv⟩)
          (sepConj_mono (fun _ hv => ⟨ch, hv⟩)
            (sepConj_mono_right
              (sepConj_mono_left (fun _ hv => ⟨af, hv⟩)))))))

private theorem exit_weaken_C (a6 a13 a14 cl ch ci : Word) (Rest : Assertion) :
    ∀ h, ((.x6 ↦ᵣ a6) ** (.x13 ↦ᵣ a13) ** (.x14 ↦ᵣ a14) **
        (SccLen ↦ₘ cl) ** (RdgHalt ↦ₘ ch) ** (RdInPtr ↦ₘ ci) **
        memOwn RtAuthFn ** Rest) h →
      (regOwn .x6 ** regOwn .x13 ** regOwn .x14 **
        memOwn SccLen ** memOwn RdgHalt ** memOwn RdInPtr **
        memOwn RtAuthFn ** Rest) h :=
  sepConj_mono (fun _ hv => ⟨a6, hv⟩)
    (sepConj_mono (fun _ hv => ⟨a13, hv⟩)
      (sepConj_mono (fun _ hv => ⟨a14, hv⟩)
        (sepConj_mono (fun _ hv => ⟨cl, hv⟩)
          (sepConj_mono (fun _ hv => ⟨ch, hv⟩)
            (sepConj_mono_left (fun _ hv => ⟨ci, hv⟩))))))

/-- `ssc_fail_block` entered with `system_call_mode` holding a KNOWN value —
    the shape the payload-reject path arrives in, since index 18 set it to 1
    and neither the payload stager nor the gate touches it. -/
theorem ssc_fail_block_of_mode (cm a5 a6 a10 a11 a12 : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 8 (pc 56) (pc 64) sscCode
      ((.x5 ↦ᵣ a5) ** (.x6 ↦ᵣ a6) ** (.x10 ↦ᵣ a10) ** (.x11 ↦ᵣ a11) **
        (.x12 ↦ᵣ a12) ** (SccMode ↦ₘ cm) ** F)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ SccMode) ** (.x10 ↦ᵣ SccData) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (1 : Word)) **
        (SccMode ↦ₘ (0 : Word)) ** F) :=
  cpsTripleWithin_weaken
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (fun _ hv => ⟨cm, hv⟩)))))))
    (fun _ hq => hq) (ssc_fail_block a5 a6 a10 a11 a12 F hF)

/-- **`stage_system_call`, whole routine** (`GuestAddrs.stage_system_call =
    through its `jalr x0, 0(ra)`, 71 instructions, 284 bytes).

    The routine records the predeploy address as an account read, rejects empty
    predeploy code, stages the SYSTEM payload, runs the callable runtime
    dispatcher with `system_call_mode = 1` so the predeploy's depth-0 `RETURN`
    is captured (NoopHalt, #8681), clears the flag, and reports the outcome.

    **Post — the three exit codes**, via `sscStatus`:
    * `a2 = 1` STAGING failure: `beqz a2` at `0x80053754` taken (empty code) or
      `bnez a0` at `0x80053798` taken (payload stager rejected).  `li a2, 1` at
      `0x8005382c`.
    * `a2 = 2` EXECUTION failure: the dispatcher ran and left
      `rdg_halt_kind ∉ {0, 1, 5}`.  `li a2, 2` at `0x80053800`.
    * `a2 = 0` SUCCESS: the dispatcher ran and left `rdg_halt_kind ∈ {0, 1, 5}`
      (STOP / RETURN / SELFDESTRUCT).  `li a2, 0` at `0x80053808`.

    All three are written by `li` instructions of THIS routine, so
    `sscStatus_mem_three` (`a2 ∈ {0,1,2}`) and `sscStatus_eq_one_iff`
    (`a2 = 1 ↔ staging failed`) hold for EVERY instantiation of the three
    residuals — which is exactly the callee-independent guarantee the unchecked
    4788/2935 callers depend on (#11810: they reject only `a2 = 1` and must
    ignore `a2 = 2`).

    Also callee-independent, and in the post: on the staging-failure path
    `a1 = 0` and `a0 = &system_call_returndata`; on every path
    `system_call_mode = 0`, `ra` is restored from `ssc_saved_ra` and `s0` from
    `ssc_saved_s0`.

    Hypotheses, classified:
    * `halign` — the ordinary ABI obligation that the return address is even.
    * `h_ard` / `h_sscp` / `h_rdc` — the three NAMED RESIDUALS, all
      UNPROVEN-CALLEE **DEPENDENCIES**, not input-domain restrictions.
      `h_rdc`'s `a0` slot is `0` rather than `stP`: the dispatcher is only ever
      reached when the payload stager returned zero (the `bnez a0` at index 26
      fell through) and nothing at indices 27-30 writes `a0`, so `0` is what
      the machine actually holds there.  Spelling it `stP` would demand the
      shape for statuses the call site cannot present.  See
      `SystemCallStagingResiduals` for what each does and does not say, and
      `…CallSite_ok` below for the discharge of every computable conjunct at
      the real call site.

    There is NO input-domain gate: the routine reads no caller memory, so the
    only thing a caller must supply is the footprint itself. -/
theorem stage_system_call_spec_within
    (sp0 tgt codePtr codeLen blockPayload payloadOut v5 v6 v8 ret : Word)
    (w5 w8 w10 : Word)
    (stP u5 u6 u11 u12 u13 u14 : Word)
    (retLen hk q5 q6 q8 q10 q11 q12 q13 q14 : Word)
    (m fArd fSscp fRdc : Nat)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (A : Assertion) (hA : A.pcFree)
    (h_ard : ArdCallShape sscCode (pc 7) ret sp0 tgt codePtr codeLen blockPayload
      payloadOut SscS0 tgt v8 w5 w8 w10 ret m
      (jalOff GuestAddrs.account_read_record (GuestAddrs.stage_system_call + 28))
      fArd (memOwn SccMode ** memOwn SccLen ** memOwn RtAuthFn **
        memOwn RdgHalt ** memOwn RdInPtr ** A))
    (h_sscp : SscpCallShape sscCode (pc 25) (pc 8) sp0 tgt codePtr codeLen
      blockPayload payloadOut RdgHalt RtAuthFn stP u5 u6 u11 u12 u13 u14 ret v8 m
      (jalOff GuestAddrs.stage_system_call_payload
        (GuestAddrs.stage_system_call + 100))
      fSscp ((SccLen ↦ₘ (0 : Word)) ** (RtAuthFn ↦ₘ (0 : Word)) **
        (RdgHalt ↦ₘ (0 : Word)) ** memOwn RdInPtr ** A))
    (h_rdc : RdcCallShape sscCode (pc 31) (pc 26) sp0 payloadOut RdInPtr
      (payloadOut + BitVec.ofNat 64 8) (0 : Word) u11 u12 u13 u14
      retLen hk q5 q6 q8 q10 q11 q12 q13 q14 ret v8 m
      (jalOff GuestAddrs.runtime_dispatcher_call
        (GuestAddrs.stage_system_call + 124))
      fRdc A) :
    cpsTripleWithin (sscFuel fArd fSscp fRdc) B ret sscCode
      (sscPre sp0 tgt codePtr codeLen blockPayload payloadOut v5 v6 v8 ret m A)
      (sscPost sp0 ret v8 codeLen stP hk retLen m A) := by
  have hB : B = pc 0 := by unfold pc; simp
  rw [hB]
  -- ## Prologue: indices 0–8, shared by all three paths
  have s0 := ssc_spill ret v5 v8
    ((.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m ** (.x6 ↦ᵣ v6) **
      (.x10 ↦ᵣ tgt) ** (.x11 ↦ᵣ codePtr) ** (.x12 ↦ᵣ codeLen) **
      (.x13 ↦ᵣ blockPayload) ** (.x14 ↦ᵣ payloadOut) ** sscScratchOwn **
      memOwn SccMode ** memOwn SccLen ** memOwn RtAuthFn ** memOwn RdgHalt **
      memOwn RdInPtr ** A) (by pcfR; exact hA)
  have s6 := ssc_park_target tgt v6
    ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m **
      (.x5 ↦ᵣ SscS0) ** (.x8 ↦ᵣ v8) ** (.x11 ↦ᵣ codePtr) ** (.x12 ↦ᵣ codeLen) **
      (.x13 ↦ᵣ blockPayload) ** (.x14 ↦ᵣ payloadOut) ** sscScratchOwn **
      (SscRa ↦ₘ ret) ** (SscS0 ↦ₘ v8) **
      memOwn SccMode ** memOwn SccLen ** memOwn RtAuthFn ** memOwn RdgHalt **
      memOwn RdInPtr ** A) (by pcfR; exact hA)
  have s7 := ssc_ard_call sp0 tgt codePtr codeLen blockPayload payloadOut
    SscS0 tgt v8 w5 w8 w10 ret ret m fArd
    (memOwn SccMode ** memOwn SccLen ** memOwn RtAuthFn ** memOwn RdgHalt **
      memOwn RdInPtr ** A) h_ard
  have s8 := ssc_restore_target tgt w10
    ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (pc 8)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m **
      (.x5 ↦ᵣ w5) ** (.x8 ↦ᵣ w8) ** (.x11 ↦ᵣ codePtr) ** (.x12 ↦ᵣ codeLen) **
      (.x13 ↦ᵣ blockPayload) ** (.x14 ↦ᵣ payloadOut) ** sscScratchOwn **
      (SscRa ↦ₘ ret) ** (SscS0 ↦ₘ v8) **
      memOwn SccMode ** memOwn SccLen ** memOwn RtAuthFn ** memOwn RdgHalt **
      memOwn RdInPtr ** A) (by pcfR; exact hA)
  have p0 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) s0 s6
  have p1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [ardCallEntry, sscSpillSaved] at hp ⊢; xperm_chunked hp) p0 s7
  have p2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [ardCallReturn, sscSpillSaved] at hp ⊢; xperm_chunked hp) p1 s8
  by_cases hcl : codeLen = 0
  · -- ## Path A: empty predeploy code — staging failure, no dispatch
    subst hcl
    have b9 := ssc_empty_gate_taken
      ((.x1 ↦ᵣ (pc 8)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m ** (.x5 ↦ᵣ w5) **
        (.x6 ↦ᵣ tgt) ** (.x8 ↦ᵣ w8) ** (.x10 ↦ᵣ tgt) ** (.x11 ↦ᵣ codePtr) **
        (.x13 ↦ᵣ blockPayload) ** (.x14 ↦ᵣ payloadOut) ** sscScratchOwn **
        (SscRa ↦ₘ ret) ** (SscS0 ↦ₘ v8) **
        memOwn SccMode ** memOwn SccLen ** memOwn RtAuthFn ** memOwn RdgHalt **
        memOwn RdInPtr ** A) (by pcfR; exact hA)
    have fb := ssc_fail_block w5 tgt tgt codePtr (0 : Word)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (pc 8)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m **
        (.x8 ↦ᵣ w8) ** (.x13 ↦ᵣ blockPayload) ** (.x14 ↦ᵣ payloadOut) **
        sscScratchOwn ** (SscRa ↦ₘ ret) ** (SscS0 ↦ₘ v8) **
        memOwn SccLen ** memOwn RtAuthFn ** memOwn RdgHalt **
        memOwn RdInPtr ** A) (by pcfR; exact hA)
    have tl := ssc_tail ret v8 (pc 8) (0 : Word) w8 halign
      ((.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m **
        (.x6 ↦ᵣ SccMode) ** (.x10 ↦ᵣ SccData) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (1 : Word)) ** (.x13 ↦ᵣ blockPayload) **
        (.x14 ↦ᵣ payloadOut) ** sscScratchOwn ** (SccMode ↦ₘ (0 : Word)) **
        memOwn SccLen ** memOwn RtAuthFn ** memOwn RdgHalt **
        memOwn RdInPtr ** A) (by pcfR; exact hA)
    have c0 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) p2 b9
    have c1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) c0 fb
    have c2 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) c1 tl
    refine cpsTripleWithin_weaken
      (fun _ hp => by simp only [sscPre] at hp; xperm_chunked hp)
      (fun h hq => ?_)
      (cpsTripleWithin_mono_nSteps (by unfold sscFuel; omega) c2)
    simp only [sscPost, sscStatus_fail_empty, sscRetLen_fail_empty]
    exact exit_weaken_A SccMode blockPayload payloadOut _ h (by xperm_chunked hq)
  · -- Non-empty code: stage the payload
    have st := ssc_stage_setup payloadOut w5 tgt w8
      ((.x1 ↦ᵣ (pc 8)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m ** (.x10 ↦ᵣ tgt) **
        (.x11 ↦ᵣ codePtr) ** (.x12 ↦ᵣ codeLen) ** (.x13 ↦ᵣ blockPayload) **
        sscScratchOwn ** (SscRa ↦ₘ ret) ** (SscS0 ↦ₘ v8) **
        memOwn RdInPtr ** A) (by pcfR; exact hA)
    have b9 := ssc_empty_gate_ntaken codeLen hcl
      ((.x1 ↦ᵣ (pc 8)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m ** (.x5 ↦ᵣ w5) **
        (.x6 ↦ᵣ tgt) ** (.x8 ↦ᵣ w8) ** (.x10 ↦ᵣ tgt) ** (.x11 ↦ᵣ codePtr) **
        (.x13 ↦ᵣ blockPayload) ** (.x14 ↦ᵣ payloadOut) ** sscScratchOwn **
        (SscRa ↦ₘ ret) ** (SscS0 ↦ₘ v8) **
        memOwn SccMode ** memOwn SccLen ** memOwn RtAuthFn ** memOwn RdgHalt **
        memOwn RdInPtr ** A) (by pcfR; exact hA)
    have sc := ssc_sscp_call sp0 tgt codePtr codeLen blockPayload payloadOut
      RdgHalt RtAuthFn stP u5 u6 u11 u12 u13 u14 ret v8 (pc 8) m fSscp
      ((SccLen ↦ₘ (0 : Word)) ** (RtAuthFn ↦ₘ (0 : Word)) **
        (RdgHalt ↦ₘ (0 : Word)) ** memOwn RdInPtr ** A) h_sscp
    have q0 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) p2 b9
    have q1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) q0 st
    have q2 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        simp only [sscpCallEntry, sscSpillSaved] at hp ⊢; xperm_chunked hp) q1 sc
    by_cases hst : stP = 0
    · -- ## Path C: staged, dispatcher runs
      subst hst
      have b26 := ssc_payload_gate_ntaken
        ((.x1 ↦ᵣ (pc 26)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m ** (.x5 ↦ᵣ u5) **
          (.x6 ↦ᵣ u6) ** (.x8 ↦ᵣ payloadOut) ** (.x11 ↦ᵣ u11) **
          (.x12 ↦ᵣ u12) ** (.x13 ↦ᵣ u13) ** (.x14 ↦ᵣ u14) ** sscScratchOwn **
          (SscRa ↦ₘ ret) ** (SscS0 ↦ₘ v8) ** (SccMode ↦ₘ (1 : Word)) **
          (SccLen ↦ₘ (0 : Word)) ** (RtAuthFn ↦ₘ (0 : Word)) **
          (RdgHalt ↦ₘ (0 : Word)) ** memOwn RdInPtr ** A) (by pcfR; exact hA)
      have ds := ssc_dispatch_setup payloadOut u5 u6
        ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (pc 26)) ** (.x2 ↦ᵣ sp0) **
          stackFree sp0 m ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ u11) **
          (.x12 ↦ᵣ u12) ** (.x13 ↦ᵣ u13) ** (.x14 ↦ᵣ u14) ** sscScratchOwn **
          (SscRa ↦ₘ ret) ** (SscS0 ↦ₘ v8) ** (SccMode ↦ₘ (1 : Word)) **
          (SccLen ↦ₘ (0 : Word)) ** (RtAuthFn ↦ₘ (0 : Word)) **
          (RdgHalt ↦ₘ (0 : Word)) ** A) (by pcfR; exact hA)
      have rc := ssc_rdc_call sp0 payloadOut RdInPtr
        (payloadOut + BitVec.ofNat 64 8) (0 : Word) u11 u12 u13 u14
        retLen hk q5 q6 q8 q10 q11 q12 q13 q14 ret v8 (pc 26) m fRdc A h_rdc
      have ad := ssc_after_dispatch retLen hk q5 q6 q10 q11
        ((.x1 ↦ᵣ (pc 32)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m ** (.x8 ↦ᵣ q8) **
          (.x12 ↦ᵣ q12) ** (.x13 ↦ᵣ q13) ** (.x14 ↦ᵣ q14) ** sscScratchOwn **
          (SscRa ↦ₘ ret) ** (SscS0 ↦ₘ v8) ** memOwn RtAuthFn ** A)
        (by pcfR; exact hA)
      have vd := ssc_verdict hk RdgHalt q12
        ((.x1 ↦ᵣ (pc 32)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m ** (.x8 ↦ᵣ q8) **
          (.x10 ↦ᵣ SccData) ** (.x11 ↦ᵣ retLen) ** (.x13 ↦ᵣ q13) **
          (.x14 ↦ᵣ q14) ** sscScratchOwn ** (SscRa ↦ₘ ret) ** (SscS0 ↦ₘ v8) **
          (SccMode ↦ₘ (0 : Word)) ** (RdInPtr ↦ₘ (0 : Word)) **
          (SccLen ↦ₘ retLen) ** (RdgHalt ↦ₘ hk) ** memOwn RtAuthFn ** A)
        (by pcfR; exact hA)
      have tl := ssc_tail_own ret v8 (pc 32) q8 halign
        ((.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m **
          (.x6 ↦ᵣ hk) ** (.x10 ↦ᵣ SccData) ** (.x11 ↦ᵣ retLen) **
          (.x12 ↦ᵣ sscExecStatus hk) ** (.x13 ↦ᵣ q13) ** (.x14 ↦ᵣ q14) **
          sscScratchOwn ** (SccMode ↦ₘ (0 : Word)) ** (RdInPtr ↦ₘ (0 : Word)) **
          (SccLen ↦ₘ retLen) ** (RdgHalt ↦ₘ hk) ** memOwn RtAuthFn ** A)
        (by pcfR; exact hA)
      have r0 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by
          simp only [sscpCallReturn, sscSpillSaved] at hp ⊢; xperm_chunked hp) q2 b26
      have r1 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_chunked hp) r0 ds
      have r2 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by
          simp only [rdcCallEntry, sscSpillSaved] at hp ⊢; xperm_chunked hp) r1 rc
      have r3 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by
          simp only [rdcCallReturn, sscSpillSaved] at hp ⊢; xperm_chunked hp) r2 ad
      have r4 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_chunked hp) r3 vd
      have r5 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_chunked hp) r4 tl
      refine cpsTripleWithin_weaken
        (fun _ hp => by simp only [sscPre] at hp; xperm_chunked hp)
        (fun h hq => ?_)
        (cpsTripleWithin_mono_nSteps (by unfold sscFuel; omega) r5)
      simp only [sscPost, sscStatus_dispatched codeLen hk hcl,
        sscRetLen_dispatched codeLen retLen hcl]
      exact exit_weaken_C hk q13 q14 retLen hk (0 : Word) _ h (by xperm_chunked hq)
    · -- ## Path B: payload stager rejected — staging failure, no dispatch
      have b26 := ssc_payload_gate_taken stP hst
        ((.x1 ↦ᵣ (pc 26)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m ** (.x5 ↦ᵣ u5) **
          (.x6 ↦ᵣ u6) ** (.x8 ↦ᵣ payloadOut) ** (.x11 ↦ᵣ u11) **
          (.x12 ↦ᵣ u12) ** (.x13 ↦ᵣ u13) ** (.x14 ↦ᵣ u14) ** sscScratchOwn **
          (SscRa ↦ₘ ret) ** (SscS0 ↦ₘ v8) ** (SccMode ↦ₘ (1 : Word)) **
          (SccLen ↦ₘ (0 : Word)) ** (RtAuthFn ↦ₘ (0 : Word)) **
          (RdgHalt ↦ₘ (0 : Word)) ** memOwn RdInPtr ** A) (by pcfR; exact hA)
      have fb := ssc_fail_block_of_mode (1 : Word) u5 u6 stP u11 u12
        ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (pc 26)) ** (.x2 ↦ᵣ sp0) **
          stackFree sp0 m ** (.x8 ↦ᵣ payloadOut) ** (.x13 ↦ᵣ u13) **
          (.x14 ↦ᵣ u14) ** sscScratchOwn ** (SscRa ↦ₘ ret) ** (SscS0 ↦ₘ v8) **
          (SccLen ↦ₘ (0 : Word)) ** (RtAuthFn ↦ₘ (0 : Word)) **
          (RdgHalt ↦ₘ (0 : Word)) ** memOwn RdInPtr ** A) (by pcfR; exact hA)
      have tl := ssc_tail ret v8 (pc 26) (0 : Word) payloadOut halign
        ((.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 m **
          (.x6 ↦ᵣ SccMode) ** (.x10 ↦ᵣ SccData) ** (.x11 ↦ᵣ (0 : Word)) **
          (.x12 ↦ᵣ (1 : Word)) ** (.x13 ↦ᵣ u13) ** (.x14 ↦ᵣ u14) **
          sscScratchOwn ** (SccMode ↦ₘ (0 : Word)) ** (SccLen ↦ₘ (0 : Word)) **
          (RtAuthFn ↦ₘ (0 : Word)) ** (RdgHalt ↦ₘ (0 : Word)) **
          memOwn RdInPtr ** A) (by pcfR; exact hA)
      have r0 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by
          simp only [sscpCallReturn, sscSpillSaved] at hp ⊢; xperm_chunked hp) q2 b26
      have r1 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_chunked hp) r0 fb
      have r2 := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_chunked hp) r1 tl
      refine cpsTripleWithin_weaken
        (fun _ hp => by simp only [sscPre] at hp; xperm_chunked hp)
        (fun h hq => ?_)
        (cpsTripleWithin_mono_nSteps (by unfold sscFuel; omega) r2)
      simp only [sscPost, sscStatus_fail_payload codeLen stP hk hst,
        sscRetLen_fail_payload codeLen stP retLen hst]
      exact exit_weaken_B SccMode u13 u14 (0 : Word) (0 : Word) (0 : Word) _ h
        (by xperm_chunked hq)

/-! ## Non-vacuity

    Three named residuals could each make the whole triple vacuous.  There is
    no input-domain gate to check — the routine reads no caller memory — so all
    the evidence below is about the residuals and about the post.

    Each residual gets (a) a POSITIVE instance: its computable conjuncts
    discharged against the emitted image at the real call site, and (b) a
    NEGATIVE CONTROL: the same bundle at a different `jal` site of this same
    routine, where it is provably FALSE.  The negative controls are what show
    the reloc conjunct is load-bearing — it ties each shape to ITS site rather
    than to any `jal` at all, which is the property `jalr_sail_equiv` (#10688)
    turned out to lack.

    A fourth exhibit shows the shapes' resource accounting is self-consistent
    (the post demands nothing the pre does not supply), and a fifth shows the
    post is not constant: all three status codes are taken.

    The permanent witness `sscSamplePre_inhabited` is a JOINT, non-empty
    inhabitant of the whole wrapper precondition, rather than a collection of
    per-atom checks.  The three `…_sscCode_not_inhabited` theorems then refute
    the corresponding full residual shapes at that same concrete state: the
    wrapper JAL is fetched, but its target is absent from the wrapper-only
    `sscCode`, so the next machine step is `none` and cannot satisfy the
    residual's return-PC postcondition.  Thus the residuals are genuinely
    blocked on callee code, not merely on an impossible resource footprint.

    ⚠️ WHAT THIS DOES NOT ESTABLISH, stated rather than hidden: that a real
    `account_read_record` / `stage_system_call_payload` /
    `runtime_dispatcher_call` execution satisfies the TRIPLE half of each
    shape.  That is the discharge, and it is the open work (owner #12204 for
    the third). -/

/-! ### A concrete whole-routine precondition witness

    The residual refutations below must not be explained by an impossible
    resource footprint.  This witness uses `m = 0` and `A = empAssertion`, but
    it still supplies every register and every BSS cell in `sscPre` exactly
    once.  The register-owned scratch is given concrete zero values in the
    witness heap; `memOwn` cells are given the values the call sites expect.
    The code and PC fields are deliberately left unowned by the partial state,
    since `sscPre` owns neither. -/

def sscSampleSp : Word := (0x1000 : Word)
def sscSampleTgt : Word := (0x2000 : Word)
def sscSampleCodePtr : Word := (0x3000 : Word)
def sscSampleCodeLen : Word := (0 : Word)
def sscSampleBlockPayload : Word := (0x4000 : Word)
def sscSamplePayloadOut : Word := (0x5000 : Word)
def sscSampleV5 : Word := (5 : Word)
def sscSampleV6 : Word := (6 : Word)
def sscSampleV8 : Word := sscSamplePayloadOut
def sscSampleRet : Word := (0 : Word)

private inductive SscSampleAtom where
  | reg (r : Reg) (v : Word)
  | own (a v : Word) (valid : isValidDwordAccess a = true)
  deriving DecidableEq

private inductive SscSampleResource where
  | reg (r : Reg)
  | mem (a : Word)
  deriving DecidableEq

private def sscSampleResource : SscSampleAtom → SscSampleResource
  | .reg r _ => .reg r
  | .own a _ _ => .mem a

private def sscScratchReg (r : Reg) : Prop :=
  r = .x3 ∨ r = .x4 ∨ r = .x7 ∨ r = .x9 ∨
    r = .x15 ∨ r = .x16 ∨ r = .x17 ∨ r = .x18 ∨
    r = .x19 ∨ r = .x20 ∨ r = .x21 ∨ r = .x22 ∨
    r = .x23 ∨ r = .x24 ∨ r = .x25 ∨ r = .x26 ∨
    r = .x27 ∨ r = .x28 ∨ r = .x29 ∨ r = .x30 ∨ r = .x31

private instance sscScratchRegDecidable (r : Reg) : Decidable (sscScratchReg r) := by
  unfold sscScratchReg
  infer_instance

private def sscSampleAtom : SscSampleAtom → Assertion
  | .reg r v => if sscScratchReg r then regOwn r else r ↦ᵣ v
  | .own a _ _ => memOwn a

private def sscSampleHeap : SscSampleAtom → PartialState
  | .reg r v => PartialState.singletonReg r v
  | .own a v _ => PartialState.singletonMem a v

private theorem sscSampleRegReg {r1 r2 : Reg} {v1 v2 : Word}
    (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint
      (PartialState.singletonReg r2 v2) := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r
  by_cases h : r = r1
  · subst r
    right
    simp [PartialState.singletonReg, hne]
  · left
    simp [PartialState.singletonReg, h]

private theorem sscSampleMemMem {a1 a2 : Word} {v1 v2 : Word}
    (hne : a1 ≠ a2) :
    (PartialState.singletonMem a1 v1).Disjoint
      (PartialState.singletonMem a2 v2) := by
  refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro a
  by_cases h : a = a1
  · subst a
    right
    simp [PartialState.singletonMem, hne]
  · left
    simp [PartialState.singletonMem, h]

private theorem sscSampleRegMem {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem sscSampleMemReg {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonMem a v).Disjoint
      (PartialState.singletonReg r w) :=
  sscSampleRegMem.symm

private theorem sscSampleHeapDisjoint {x y : SscSampleAtom}
    (h : sscSampleResource x ≠ sscSampleResource y) :
    (sscSampleHeap x).Disjoint (sscSampleHeap y) := by
  cases x <;> cases y
  · apply sscSampleRegReg
    simpa [sscSampleResource] using h
  · exact sscSampleRegMem
  · exact sscSampleMemReg
  · apply sscSampleMemMem
    simpa [sscSampleResource] using h

private def sscSampleAtoms : List SscSampleAtom :=
  [ .reg .x0 0, .reg .x1 sscSampleRet, .reg .x2 sscSampleSp,
    .reg .x5 sscSampleV5, .reg .x6 sscSampleV6, .reg .x8 sscSampleV8,
    .reg .x10 sscSampleTgt, .reg .x11 sscSampleCodePtr,
    .reg .x12 sscSampleCodeLen, .reg .x13 sscSampleBlockPayload,
    .reg .x14 sscSamplePayloadOut,
    .reg .x3 0, .reg .x4 0, .reg .x7 0, .reg .x9 0,
    .reg .x15 0, .reg .x16 0, .reg .x17 0, .reg .x18 0,
    .reg .x19 0, .reg .x20 0, .reg .x21 0, .reg .x22 0,
    .reg .x23 0, .reg .x24 0, .reg .x25 0, .reg .x26 0,
    .reg .x27 0, .reg .x28 0, .reg .x29 0, .reg .x30 0,
    .reg .x31 0,
    .own SscRa 0 (by decide), .own SscS0 sscSampleV8 (by decide),
    .own SccMode 1 (by decide), .own SccLen 0 (by decide),
    .own RtAuthFn 0 (by decide), .own RdgHalt 0 (by decide),
    .own RdInPtr (sscSamplePayloadOut + BitVec.ofNat 64 8) (by decide) ]

private theorem sscSampleAtoms_pairwise :
    sscSampleAtoms.Pairwise
      (fun x y => sscSampleResource x ≠ sscSampleResource y) := by
  unfold sscSampleAtoms sscSampleResource
  decide

private theorem sscSampleAtoms_hsat :
    (sscSampleAtoms.foldr (fun x acc => sscSampleAtom x ** acc) empAssertion)
      (sscSampleAtoms.foldr
        (fun x acc => (sscSampleHeap x).union acc) PartialState.empty) := by
  apply sepConj_foldr_satisfiable sscSampleAtom sscSampleHeap sscSampleAtoms
  · intro x hx
    cases x with
    | reg r v =>
      by_cases hs : sscScratchReg r
      · simp only [sscSampleAtom, hs, ↓reduceIte]
        exact ⟨v, rfl⟩
      · simp only [sscSampleAtom, hs, ↓reduceIte, sscSampleHeap, regIs]
    | own a v hv => exact ⟨v, rfl, hv⟩
  · exact List.Pairwise.imp
      (fun {_ _} h => sscSampleHeapDisjoint h)
      sscSampleAtoms_pairwise

private def sscSampleAtomConcrete : SscSampleAtom → Assertion
  | .reg r v => if sscScratchReg r then regOwn r else r ↦ᵣ v
  | .own a v _ => a ↦ₘ v

private def sscSampleAtomsConcreteAssert : Assertion :=
  sscSampleAtoms.foldr
    (fun x acc => sscSampleAtomConcrete x ** acc) empAssertion

private theorem sscSampleAtoms_hsat_concrete :
    (sscSampleAtomsConcreteAssert)
      (sscSampleAtoms.foldr
        (fun x acc => (sscSampleHeap x).union acc) PartialState.empty) := by
  apply sepConj_foldr_satisfiable sscSampleAtomConcrete sscSampleHeap
    sscSampleAtoms
  · intro x hx
    cases x with
    | reg r v =>
      by_cases hs : sscScratchReg r
      · simp only [sscSampleAtomConcrete, hs, ↓reduceIte]
        exact ⟨v, rfl⟩
      · simp only [sscSampleAtomConcrete, hs, ↓reduceIte, sscSampleHeap,
          regIs]
    | own a v hv => exact ⟨rfl, hv⟩
  · exact List.Pairwise.imp
      (fun {_ _} h => sscSampleHeapDisjoint h)
      sscSampleAtoms_pairwise

private def sscSampleHeapFold : PartialState :=
  sscSampleAtoms.foldr
    (fun x acc => (sscSampleHeap x).union acc) PartialState.empty

private def sscSampleAtomsAssert : Assertion :=
  sscSampleAtoms.foldr (fun x acc => sscSampleAtom x ** acc) empAssertion

def sscSamplePre : Assertion :=
  sscPre sscSampleSp sscSampleTgt sscSampleCodePtr sscSampleCodeLen
    sscSampleBlockPayload sscSamplePayloadOut sscSampleV5 sscSampleV6
    sscSampleV8 sscSampleRet 0 empAssertion

private theorem sscSamplePre_eq_atoms :
    sscSamplePre = sscSampleAtomsAssert := by
  simp [sscSamplePre, sscPre, sscScratchOwn, sscSampleAtomsAssert,
    sscSampleAtoms, sscSampleAtom, sscSampleSp, sscSampleTgt,
    sscSampleCodePtr, sscSampleCodeLen, sscSampleBlockPayload,
    sscSamplePayloadOut, sscSampleV5, sscSampleV6, sscSampleV8,
    sscSampleRet, sscScratchReg, stackFree, sepConj_emp_left',
    sepConj_emp_right']
  funext h
  exact propext ⟨fun hp => by xperm_hyp hp, fun hp => by xperm_hyp hp⟩

def sscSampleStateAt (entry : Word) : MachineState where
  regs := fun r => (sscSampleHeapFold.regs r).getD 0
  mem := fun a => (sscSampleHeapFold.mem a).getD 0
  code := sscCode
  pc := entry
  publicValues := (sscSampleHeapFold.publicValues).getD []
  privateInput := (sscSampleHeapFold.privateInput).getD []
  inputBufBase := defaultInputBufBase

private theorem sscSampleHeap_x0 :
    sscSampleHeapFold.regs .x0 = some 0 := by
  unfold sscSampleHeapFold sscSampleAtoms sscSampleHeap
  decide

private theorem sscSampleState_getReg (entry : Word) (r : Reg) (hr : r ≠ .x0) :
    (sscSampleStateAt entry).getReg r =
      (sscSampleHeapFold.regs r).getD 0 := by
  cases r <;> simp_all [sscSampleStateAt, MachineState.getReg]

private theorem sscSampleState_getMem (entry : Word) (a : Word) :
    (sscSampleStateAt entry).getMem a =
      (sscSampleHeapFold.mem a).getD 0 := by
  rfl

private theorem sscSampleHeap_code_none_atom (x : SscSampleAtom) (a : Word) :
    (sscSampleHeap x).code a = none := by
  cases x <;> rfl

private theorem sscSampleHeap_code_none (a : Word) :
    sscSampleHeapFold.code a = none := by
  unfold sscSampleHeapFold
  induction sscSampleAtoms with
  | nil => rfl
  | cons x xs ih =>
    have hx : (sscSampleHeap x).code a = none :=
      sscSampleHeap_code_none_atom x a
    change (match (sscSampleHeap x).code a with
      | some v => some v | none =>
        (xs.foldr (fun y acc => (sscSampleHeap y).union acc)
          PartialState.empty).code a) = none
    rw [hx, ih]

private theorem sscSampleHeap_pc_none :
    sscSampleHeapFold.pc = none := by
  unfold sscSampleHeapFold
  induction sscSampleAtoms with
  | nil => rfl
  | cons x xs ih =>
    have hx : (sscSampleHeap x).pc = none := by cases x <;> rfl
    change (match (sscSampleHeap x).pc with
      | some v => some v | none =>
        (xs.foldr (fun y acc => (sscSampleHeap y).union acc)
          PartialState.empty).pc) = none
    rw [hx, ih]

private theorem sscSampleState_compat (entry : Word) :
    sscSampleHeapFold.CompatibleWith (sscSampleStateAt entry) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r v hv
    by_cases hr : r = .x0
    · subst r
      have hv0 : v = 0 := by
        rw [sscSampleHeap_x0] at hv
        injection hv with hv
        exact hv.symm
      subst hv0
      rfl
    · rw [sscSampleState_getReg entry r hr, hv]
      rfl
  · intro a v hv
    show (sscSampleStateAt entry).getMem a = v
    rw [sscSampleState_getMem entry a, hv]
    rfl
  · intro a i hi
    rw [sscSampleHeap_code_none a] at hi
    cases hi
  · intro v hv
    rw [sscSampleHeap_pc_none] at hv
    cases hv
  · intro v hv; cases hv
  · intro v hv; cases hv
  · intro v hv; cases hv

theorem sscSamplePre_inhabited :
    sscSamplePre.holdsFor (sscSampleStateAt B) := by
  refine ⟨sscSampleHeapFold, sscSampleState_compat B, ?_⟩
  rw [sscSamplePre_eq_atoms]
  exact sscSampleAtoms_hsat

private def sscSampleArdFrame : Assertion :=
  (SccMode ↦ₘ (1 : Word)) ** (SccLen ↦ₘ (0 : Word)) **
  (RtAuthFn ↦ₘ (0 : Word)) ** (RdgHalt ↦ₘ (0 : Word)) **
  (RdInPtr ↦ₘ (sscSamplePayloadOut + BitVec.ofNat 64 8))

private def sscSampleSscpFrame : Assertion :=
  (SccLen ↦ₘ (0 : Word)) ** (RtAuthFn ↦ₘ (0 : Word)) **
  (RdgHalt ↦ₘ (0 : Word)) **
  (RdInPtr ↦ₘ (sscSamplePayloadOut + BitVec.ofNat 64 8))

private theorem sscSampleArdPre_eq_concrete :
    (((.x1 ↦ᵣ sscSampleRet) **
      ardCallEntry sscSampleSp sscSampleTgt sscSampleCodePtr
        sscSampleCodeLen sscSampleBlockPayload sscSamplePayloadOut
        sscSampleV5 sscSampleV6 sscSampleV8 sscSampleRet 0) **
      sscSampleArdFrame) = sscSampleAtomsConcreteAssert := by
  simp [ardCallEntry, sscSampleArdFrame, sscSpillSaved, sscScratchOwn,
    sscSampleAtomsConcreteAssert, sscSampleAtoms, sscSampleAtomConcrete,
    sscScratchReg,
    sscSampleSp, sscSampleTgt, sscSampleCodePtr, sscSampleCodeLen,
    sscSampleBlockPayload, sscSamplePayloadOut, sscSampleV5, sscSampleV6,
    sscSampleV8, sscSampleRet, stackFree, sepConj_emp_left',
    sepConj_emp_right']
  funext h
  exact propext ⟨fun hp => by xperm_hyp hp, fun hp => by xperm_hyp hp⟩

private theorem sscSampleSscpPre_eq_concrete :
    (((.x1 ↦ᵣ sscSampleRet) **
      sscpCallEntry sscSampleSp sscSampleTgt sscSampleCodePtr
        sscSampleCodeLen sscSampleBlockPayload sscSamplePayloadOut
        sscSampleV5 sscSampleV6 sscSampleRet sscSampleV8 0) **
      sscSampleSscpFrame) = sscSampleAtomsConcreteAssert := by
  simp [sscpCallEntry, sscSampleSscpFrame, sscSpillSaved, sscScratchOwn,
    sscSampleAtomsConcreteAssert, sscSampleAtoms, sscSampleAtomConcrete,
    sscScratchReg,
    sscSampleSp, sscSampleTgt, sscSampleCodePtr, sscSampleCodeLen,
    sscSampleBlockPayload, sscSamplePayloadOut, sscSampleV5, sscSampleV6,
    sscSampleV8, sscSampleRet, stackFree, sepConj_emp_left',
    sepConj_emp_right']
  funext h
  exact propext ⟨fun hp => by xperm_hyp hp, fun hp => by xperm_hyp hp⟩

private theorem sscSampleRdcPre_eq_concrete :
    (((.x1 ↦ᵣ sscSampleRet) **
      rdcCallEntry sscSampleSp sscSamplePayloadOut
        sscSampleV5 sscSampleV6 sscSampleTgt sscSampleCodePtr
        sscSampleCodeLen sscSampleBlockPayload sscSamplePayloadOut
        sscSampleRet sscSampleV8 0)) = sscSampleAtomsConcreteAssert := by
  simp [rdcCallEntry, sscSpillSaved, sscScratchOwn,
    sscSampleAtomsConcreteAssert, sscSampleAtoms, sscSampleAtomConcrete,
    sscScratchReg,
    sscSampleSp, sscSampleTgt, sscSampleCodePtr, sscSampleCodeLen,
    sscSampleBlockPayload, sscSamplePayloadOut, sscSampleV5, sscSampleV6,
    sscSampleV8, sscSampleRet, stackFree, sepConj_emp_left',
    sepConj_emp_right']
  funext h
  exact propext ⟨fun hp => by xperm_hyp hp, fun hp => by xperm_hyp hp⟩

/-! ### The deployed wrapper does not contain its three callees

    The `CodeReq` above is intentionally only the 71-instruction wrapper.  The
    following kernel checks make the resulting boundary explicit: each
    local JAL is present in that wrapper, while each deployed callee entry is
    outside its instruction range.  The offsets and entries below are derived
    from `GuestAddrs`; older `SystemCallStagingBase` and
    `SystemCallStagingResiduals` docstrings still contain stale literal
    addresses and are not the formal source of these checks. -/

private theorem sscCode_ard_jal :
    sscCode (pc 7) =
      some (.JAL .x1
        (jalOff GuestAddrs.account_read_record
          (GuestAddrs.stage_system_call + 28))) := by
  apply (mem_at 7 (.JAL .x1
      (jalOff GuestAddrs.account_read_record
        (GuestAddrs.stage_system_call + 28))) (pc 7) rfl
    (by rw [sscProgL_len]; norm_num) (by decide))
  simp [CodeReq.singleton]

private theorem sscCode_ard_missing : sscCode ArdB = none := by
  unfold sscCode ArdB B sscProgL
  decide

private theorem sscCode_sscp_jal :
    sscCode (pc 25) =
      some (.JAL .x1
        (jalOff GuestAddrs.stage_system_call_payload
          (GuestAddrs.stage_system_call + 100))) := by
  apply (mem_at 25 (.JAL .x1
      (jalOff GuestAddrs.stage_system_call_payload
        (GuestAddrs.stage_system_call + 100))) (pc 25) rfl
    (by rw [sscProgL_len]; norm_num) (by decide))
  simp [CodeReq.singleton]

private theorem sscCode_sscp_missing : sscCode SscpB = none := by
  unfold sscCode SscpB B sscProgL
  decide

private theorem sscCode_rdc_jal :
    sscCode (pc 31) =
      some (.JAL .x1
        (jalOff GuestAddrs.runtime_dispatcher_call
          (GuestAddrs.stage_system_call + 124))) := by
  apply (mem_at 31 (.JAL .x1
      (jalOff GuestAddrs.runtime_dispatcher_call
        (GuestAddrs.stage_system_call + 124))) (pc 31) rfl
    (by rw [sscProgL_len]; norm_num) (by decide))
  simp [CodeReq.singleton]

private theorem sscCode_rdc_missing : sscCode RdcB = none := by
  unfold sscCode RdcB B sscProgL
  decide

private theorem sscArdStep_one :
    step (sscSampleStateAt (pc 7)) =
      some (execInstrBr (sscSampleStateAt (pc 7))
        (.JAL .x1
          (jalOff GuestAddrs.account_read_record
            (GuestAddrs.stage_system_call + 28)))) := by
  apply step_non_ecall_non_mem
  · change sscCode (pc 7) = some (.JAL .x1
      (jalOff GuestAddrs.account_read_record
        (GuestAddrs.stage_system_call + 28)))
    exact sscCode_ard_jal
  · decide
  · decide
  · decide

private theorem sscArdStep_target_pc :
    (execInstrBr (sscSampleStateAt (pc 7))
      (.JAL .x1
        (jalOff GuestAddrs.account_read_record
          (GuestAddrs.stage_system_call + 28)))).pc = ArdB := by
  change (sscSampleStateAt (pc 7)).pc + signExtend21
      (jalOff GuestAddrs.account_read_record
        (GuestAddrs.stage_system_call + 28)) = ArdB
  change pc 7 + signExtend21
      (jalOff GuestAddrs.account_read_record
        (GuestAddrs.stage_system_call + 28)) = ArdB
  exact pc_jal_ard

private theorem sscArdStep_after_none :
    step (execInstrBr (sscSampleStateAt (pc 7))
      (.JAL .x1
        (jalOff GuestAddrs.account_read_record
          (GuestAddrs.stage_system_call + 28)))) = none := by
  have hcode := step_code_preserved sscArdStep_one
  have hfetch :
      (execInstrBr (sscSampleStateAt (pc 7))
        (.JAL .x1
          (jalOff GuestAddrs.account_read_record
            (GuestAddrs.stage_system_call + 28)))).code
        (execInstrBr (sscSampleStateAt (pc 7))
          (.JAL .x1
            (jalOff GuestAddrs.account_read_record
              (GuestAddrs.stage_system_call + 28)))).pc = none := by
    rw [hcode, sscArdStep_target_pc]
    exact sscCode_ard_missing
  simp [step, hfetch]

private theorem sscSscpStep_one :
    step (sscSampleStateAt (pc 25)) =
      some (execInstrBr (sscSampleStateAt (pc 25))
        (.JAL .x1
          (jalOff GuestAddrs.stage_system_call_payload
            (GuestAddrs.stage_system_call + 100)))) := by
  apply step_non_ecall_non_mem
  · change sscCode (pc 25) = some (.JAL .x1
      (jalOff GuestAddrs.stage_system_call_payload
        (GuestAddrs.stage_system_call + 100)))
    exact sscCode_sscp_jal
  · decide
  · decide
  · decide

private theorem sscSscpStep_target_pc :
    (execInstrBr (sscSampleStateAt (pc 25))
      (.JAL .x1
        (jalOff GuestAddrs.stage_system_call_payload
          (GuestAddrs.stage_system_call + 100)))).pc = SscpB := by
  change (sscSampleStateAt (pc 25)).pc + signExtend21
      (jalOff GuestAddrs.stage_system_call_payload
        (GuestAddrs.stage_system_call + 100)) = SscpB
  change pc 25 + signExtend21
      (jalOff GuestAddrs.stage_system_call_payload
        (GuestAddrs.stage_system_call + 100)) = SscpB
  exact pc_jal_sscp

private theorem sscSscpStep_after_none :
    step (execInstrBr (sscSampleStateAt (pc 25))
      (.JAL .x1
        (jalOff GuestAddrs.stage_system_call_payload
          (GuestAddrs.stage_system_call + 100)))) = none := by
  have hcode := step_code_preserved sscSscpStep_one
  have hfetch :
      (execInstrBr (sscSampleStateAt (pc 25))
        (.JAL .x1
          (jalOff GuestAddrs.stage_system_call_payload
            (GuestAddrs.stage_system_call + 100)))).code
        (execInstrBr (sscSampleStateAt (pc 25))
          (.JAL .x1
            (jalOff GuestAddrs.stage_system_call_payload
              (GuestAddrs.stage_system_call + 100)))).pc = none := by
    rw [hcode, sscSscpStep_target_pc]
    exact sscCode_sscp_missing
  simp [step, hfetch]

private theorem sscRdcStep_one :
    step (sscSampleStateAt (pc 31)) =
      some (execInstrBr (sscSampleStateAt (pc 31))
        (.JAL .x1
          (jalOff GuestAddrs.runtime_dispatcher_call
            (GuestAddrs.stage_system_call + 124)))) := by
  apply step_non_ecall_non_mem
  · change sscCode (pc 31) = some (.JAL .x1
      (jalOff GuestAddrs.runtime_dispatcher_call
        (GuestAddrs.stage_system_call + 124)))
    exact sscCode_rdc_jal
  · decide
  · decide
  · decide

private theorem sscRdcStep_target_pc :
    (execInstrBr (sscSampleStateAt (pc 31))
      (.JAL .x1
        (jalOff GuestAddrs.runtime_dispatcher_call
          (GuestAddrs.stage_system_call + 124)))).pc = RdcB := by
  change (sscSampleStateAt (pc 31)).pc + signExtend21
      (jalOff GuestAddrs.runtime_dispatcher_call
        (GuestAddrs.stage_system_call + 124)) = RdcB
  change pc 31 + signExtend21
      (jalOff GuestAddrs.runtime_dispatcher_call
        (GuestAddrs.stage_system_call + 124)) = RdcB
  exact pc_jal_rdc

private theorem sscRdcStep_after_none :
    step (execInstrBr (sscSampleStateAt (pc 31))
      (.JAL .x1
        (jalOff GuestAddrs.runtime_dispatcher_call
          (GuestAddrs.stage_system_call + 124)))) = none := by
  have hcode := step_code_preserved sscRdcStep_one
  have hfetch :
      (execInstrBr (sscSampleStateAt (pc 31))
        (.JAL .x1
          (jalOff GuestAddrs.runtime_dispatcher_call
            (GuestAddrs.stage_system_call + 124)))).code
        (execInstrBr (sscSampleStateAt (pc 31))
          (.JAL .x1
            (jalOff GuestAddrs.runtime_dispatcher_call
              (GuestAddrs.stage_system_call + 124)))).pc = none := by
    rw [hcode, sscRdcStep_target_pc]
    exact sscCode_rdc_missing
  simp [step, hfetch]

private theorem sscStepN_after_none {next : MachineState}
    (hafter : step next = none) (n : Nat) :
    stepN (n + 1) next = none := by
  rw [stepN_succ]
  simp [hafter]

private theorem sscStepN_two_plus {state next : MachineState}
    (hstep : step state = some next) (hafter : step next = none) (n : Nat) :
    stepN (n + 2) state = none := by
  rw [show n + 2 = (n + 1) + 1 by omega, stepN_succ, hstep]
  exact sscStepN_after_none hafter n

private theorem sscNoReturn (state next : MachineState) (caller : Word)
    (hstep : step state = some next) (hafter : step next = none)
    (hcaller : state.pc ≠ caller + 4)
    (hnext : next.pc ≠ caller + 4)
    (k : Nat) (s' : MachineState)
    (hsteps : stepN k state = some s') :
    s'.pc ≠ caller + 4 := by
  cases k with
  | zero =>
    have heq : state = s' := by
      simpa [stepN] using hsteps
    intro hpceq
    rw [← heq] at hpceq
    exact hcaller hpceq
  | succ k =>
    cases k with
    | zero =>
      have heq : next = s' := by
        rw [stepN_one, hstep] at hsteps
        exact Option.some.inj hsteps
      intro hpceq
      rw [← heq] at hpceq
      exact hnext hpceq
    | succ n =>
      rw [sscStepN_two_plus hstep hafter n] at hsteps
      cases hsteps

theorem ard_residual_sscCode_not_inhabited (fuel : Nat) :
    ¬ ArdCallShape sscCode (pc 7) sscSampleRet
      sscSampleSp sscSampleTgt sscSampleCodePtr sscSampleCodeLen
      sscSampleBlockPayload sscSamplePayloadOut
      sscSampleV5 sscSampleV6 sscSampleV8
      (0 : Word) (0 : Word) (0 : Word) sscSampleRet
      0 (jalOff GuestAddrs.account_read_record
        (GuestAddrs.stage_system_call + 28)) fuel sscSampleArdFrame := by
  intro hcontract
  have htrip := hcontract.2
  have hpre :
      ((((.x1 ↦ᵣ sscSampleRet) **
        ardCallEntry sscSampleSp sscSampleTgt sscSampleCodePtr
          sscSampleCodeLen sscSampleBlockPayload sscSamplePayloadOut
          sscSampleV5 sscSampleV6 sscSampleV8 sscSampleRet 0) **
        sscSampleArdFrame) ** empAssertion).holdsFor
        (sscSampleStateAt (pc 7)) := by
    refine ⟨sscSampleHeapFold, sscSampleState_compat (pc 7), ?_⟩
    rw [sscSampleArdPre_eq_concrete]
    exact ⟨sscSampleHeapFold, PartialState.empty,
      PartialState.Disjoint_empty_right, PartialState.union_empty_right,
      sscSampleAtoms_hsat_concrete, rfl⟩
  have hcr : sscCode.SatisfiedBy (sscSampleStateAt (pc 7)) := by
    intro a i hi
    change sscCode a = some i
    exact hi
  obtain ⟨k, _, s', hstep, hpc', _⟩ :=
    htrip empAssertion pcFree_emp (sscSampleStateAt (pc 7)) hcr hpre rfl
  have hcaller : (sscSampleStateAt (pc 7)).pc ≠ pc 7 + 4 := by
    change pc 7 ≠ pc 7 + 4
    unfold pc B
    decide
  have hnext :
      (execInstrBr (sscSampleStateAt (pc 7))
        (.JAL .x1
          (jalOff GuestAddrs.account_read_record
            (GuestAddrs.stage_system_call + 28)))).pc ≠ pc 7 + 4 := by
    rw [sscArdStep_target_pc]
    unfold ArdB pc B
    decide
  exact (sscNoReturn (state := sscSampleStateAt (pc 7))
    (next := execInstrBr (sscSampleStateAt (pc 7))
      (.JAL .x1
        (jalOff GuestAddrs.account_read_record
          (GuestAddrs.stage_system_call + 28)))) (caller := pc 7)
    sscArdStep_one sscArdStep_after_none hcaller hnext k s' hstep) hpc'

theorem sscp_residual_sscCode_not_inhabited (fuel : Nat) :
    ¬ SscpCallShape sscCode (pc 25) sscSampleRet
      sscSampleSp sscSampleTgt sscSampleCodePtr sscSampleCodeLen
      sscSampleBlockPayload sscSamplePayloadOut
      sscSampleV5 sscSampleV6 (0 : Word)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      sscSampleRet sscSampleV8
      0 (jalOff GuestAddrs.stage_system_call_payload
        (GuestAddrs.stage_system_call + 100)) fuel sscSampleSscpFrame := by
  intro hcontract
  have htrip := hcontract.2
  have hpre :
      ((((.x1 ↦ᵣ sscSampleRet) **
        sscpCallEntry sscSampleSp sscSampleTgt sscSampleCodePtr
          sscSampleCodeLen sscSampleBlockPayload sscSamplePayloadOut
          sscSampleV5 sscSampleV6 sscSampleRet sscSampleV8 0) **
        sscSampleSscpFrame) ** empAssertion).holdsFor
        (sscSampleStateAt (pc 25)) := by
    refine ⟨sscSampleHeapFold, sscSampleState_compat (pc 25), ?_⟩
    rw [sscSampleSscpPre_eq_concrete]
    exact ⟨sscSampleHeapFold, PartialState.empty,
      PartialState.Disjoint_empty_right, PartialState.union_empty_right,
      sscSampleAtoms_hsat_concrete, rfl⟩
  have hcr : sscCode.SatisfiedBy (sscSampleStateAt (pc 25)) := by
    intro a i hi
    change sscCode a = some i
    exact hi
  obtain ⟨k, _, s', hstep, hpc', _⟩ :=
    htrip empAssertion pcFree_emp (sscSampleStateAt (pc 25)) hcr hpre rfl
  have hcaller : (sscSampleStateAt (pc 25)).pc ≠ pc 25 + 4 := by
    change pc 25 ≠ pc 25 + 4
    unfold pc B
    decide
  have hnext :
      (execInstrBr (sscSampleStateAt (pc 25))
        (.JAL .x1
          (jalOff GuestAddrs.stage_system_call_payload
            (GuestAddrs.stage_system_call + 100)))).pc ≠ pc 25 + 4 := by
    rw [sscSscpStep_target_pc]
    unfold SscpB pc B
    decide
  exact (sscNoReturn (state := sscSampleStateAt (pc 25))
    (next := execInstrBr (sscSampleStateAt (pc 25))
      (.JAL .x1
        (jalOff GuestAddrs.stage_system_call_payload
          (GuestAddrs.stage_system_call + 100)))) (caller := pc 25)
    sscSscpStep_one sscSscpStep_after_none hcaller hnext k s' hstep) hpc'

theorem rdc_residual_sscCode_not_inhabited (fuel : Nat) :
    ¬ RdcCallShape sscCode (pc 31) sscSampleRet
      sscSampleSp sscSamplePayloadOut
      sscSampleV5 sscSampleV6 sscSampleTgt sscSampleCodePtr
      sscSampleCodeLen sscSampleBlockPayload sscSamplePayloadOut
      (0 : Word) (0 : Word)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      (0 : Word) (0 : Word) sscSampleRet sscSampleV8
      0 (jalOff GuestAddrs.runtime_dispatcher_call
        (GuestAddrs.stage_system_call + 124)) fuel empAssertion := by
  intro hcontract
  have htrip := hcontract.2
  have hpre :
      ((((.x1 ↦ᵣ sscSampleRet) **
        rdcCallEntry sscSampleSp sscSamplePayloadOut
          sscSampleV5 sscSampleV6 sscSampleTgt sscSampleCodePtr
          sscSampleCodeLen sscSampleBlockPayload sscSamplePayloadOut
          sscSampleRet sscSampleV8 0) ** empAssertion) ** empAssertion).holdsFor
        (sscSampleStateAt (pc 31)) := by
    refine ⟨sscSampleHeapFold, sscSampleState_compat (pc 31), ?_⟩
    rw [sscSampleRdcPre_eq_concrete]
    refine ⟨sscSampleHeapFold, PartialState.empty,
      PartialState.Disjoint_empty_right, PartialState.union_empty_right,
      ?_, rfl⟩
    exact ⟨sscSampleHeapFold, PartialState.empty,
      PartialState.Disjoint_empty_right, PartialState.union_empty_right,
      sscSampleAtoms_hsat_concrete, rfl⟩
  have hcr : sscCode.SatisfiedBy (sscSampleStateAt (pc 31)) := by
    intro a i hi
    change sscCode a = some i
    exact hi
  obtain ⟨k, _, s', hstep, hpc', _⟩ :=
    htrip empAssertion pcFree_emp (sscSampleStateAt (pc 31)) hcr hpre rfl
  have hcaller : (sscSampleStateAt (pc 31)).pc ≠ pc 31 + 4 := by
    change pc 31 ≠ pc 31 + 4
    unfold pc B
    decide
  have hnext :
      (execInstrBr (sscSampleStateAt (pc 31))
        (.JAL .x1
          (jalOff GuestAddrs.runtime_dispatcher_call
            (GuestAddrs.stage_system_call + 124)))).pc ≠ pc 31 + 4 := by
    rw [sscRdcStep_target_pc]
    unfold RdcB pc B
    decide
  exact (sscNoReturn (state := sscSampleStateAt (pc 31))
    (next := execInstrBr (sscSampleStateAt (pc 31))
      (.JAL .x1
        (jalOff GuestAddrs.runtime_dispatcher_call
          (GuestAddrs.stage_system_call + 124)))) (caller := pc 31)
    sscRdcStep_one sscRdcStep_after_none hcaller hnext k s' hstep) hpc'

/-- **Residual 1 is reachable**: every computable conjunct of `ArdCallShape`
    holds at the real `jal ra, account_read_record` (index 7, `0x8005374c`). -/
theorem ard_residual_reachable :
    CallSiteOk sscCode (pc 7) ArdB
      (jalOff GuestAddrs.account_read_record
        (GuestAddrs.stage_system_call + 28)) empAssertion :=
  ardCallSite_ok empAssertion pcFree_emp

/-- **Negative control 1**: the same bundle at index 25 is provably FALSE — the
    `jal` there targets `stage_system_call_payload`, so
    `pc 25 + signExtend21 offset` does not resolve to `account_read_record`. -/
theorem ard_residual_wrong_site :
    ¬ CallSiteOk sscCode (pc 25) ArdB
        (jalOff GuestAddrs.account_read_record
          (GuestAddrs.stage_system_call + 28)) empAssertion := by
  intro h
  exact absurd h.2.2.1 (by decide)

/-- **Residual 2 is reachable** at the real `jal ra, stage_system_call_payload`
    (index 25, `0x80053794`). -/
theorem sscp_residual_reachable :
    CallSiteOk sscCode (pc 25) SscpB
      (jalOff GuestAddrs.stage_system_call_payload
        (GuestAddrs.stage_system_call + 100)) empAssertion :=
  sscpCallSite_ok empAssertion pcFree_emp

/-- **Negative control 2**: the same bundle at index 7 is provably FALSE. -/
theorem sscp_residual_wrong_site :
    ¬ CallSiteOk sscCode (pc 7) SscpB
        (jalOff GuestAddrs.stage_system_call_payload
          (GuestAddrs.stage_system_call + 100)) empAssertion := by
  intro h
  exact absurd h.2.2.1 (by decide)

/-- **Residual 3 is reachable** at the real `jal ra, runtime_dispatcher_call`
    (index 31, `0x800537ac`). -/
theorem rdc_residual_reachable :
    CallSiteOk sscCode (pc 31) RdcB
      (jalOff GuestAddrs.runtime_dispatcher_call
        (GuestAddrs.stage_system_call + 124)) empAssertion :=
  rdcCallSite_ok empAssertion pcFree_emp

/-- **Negative control 3**: the same bundle at index 25 is provably FALSE. -/
theorem rdc_residual_wrong_site :
    ¬ CallSiteOk sscCode (pc 25) RdcB
        (jalOff GuestAddrs.runtime_dispatcher_call
          (GuestAddrs.stage_system_call + 124)) empAssertion := by
  intro h
  exact absurd h.2.2.1 (by decide)

/-! ### The shapes' resource accounting is self-consistent

    A residual whose POST demanded a resource its PRE did not supply would be
    unsatisfiable for a reason no site-level check catches.  Each identity
    below picks the parameters of a "callee that returns leaving everything as
    it found it" and shows the pre and post are then the SAME assertion — so
    the footprints balance atom for atom, and every atom the shape names is
    named exactly once. -/

theorem ardCall_balanced (sp0 tgt codePtr codeLen blockPayload payloadOut
    v5 v8 ret : Word) (m : Nat) :
    ardCallEntry sp0 tgt codePtr codeLen blockPayload payloadOut v5 tgt v8 ret m
      = ardCallReturn sp0 codePtr codeLen blockPayload payloadOut
          tgt v5 v8 tgt ret v8 m := rfl

theorem sscpCall_balanced (sp0 tgt codePtr codeLen blockPayload payloadOut
    v5 v6 ret v8 : Word) (m : Nat) :
    sscpCallEntry sp0 tgt codePtr codeLen blockPayload payloadOut v5 v6 ret v8 m
      = sscpCallReturn sp0 payloadOut tgt v5 v6 codePtr codeLen blockPayload
          payloadOut ret v8 m := rfl

/-! ### The post is not constant

    All three status codes are produced, and `1` is never produced by the
    dispatch path — which is the #11810 property in its sharpest form. -/

theorem ssc_status_success_reachable : sscStatus 1 0 1 = 0 := by decide

theorem ssc_status_staging_fail_reachable : sscStatus 0 0 0 = 1 := by decide

theorem ssc_status_exec_fail_reachable : sscStatus 1 0 7 = 2 := by decide

/-- **Negative control on the status function**: the execution-failure code is
    provably NOT the staging-failure code, so a caller that tests `a2 = 1`
    genuinely distinguishes the two classes. -/
theorem ssc_status_exec_fail_ne_staging_fail : sscStatus 1 0 7 ≠ sscStatus 0 0 0 := by
  decide

/-- The routine's returned length is `0` on both staging-failure paths and the
    dispatcher's captured length otherwise — also not constant. -/
theorem ssc_retlen_staging_fail_reachable : sscRetLen 0 0 9 = 0 := by decide

theorem ssc_retlen_dispatch_reachable : sscRetLen 1 0 9 = 9 := by decide

#print axioms sscSamplePre_inhabited
#print axioms ard_residual_sscCode_not_inhabited
#print axioms sscp_residual_sscCode_not_inhabited
#print axioms rdc_residual_sscCode_not_inhabited

end EvmAsm.Codegen.SystemCallStagingTop
