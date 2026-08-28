/-
  EvmAsm.Codegen.Programs.SystemCallStagingSegments

  The machine-step layer of the `stage_system_call` proof (#12206 item 1): the
  per-instruction helpers, the two verdict functions, and one triple per
  straight-line run, branch and join of the routine's control-flow DAG.

  Nothing here mentions a callee.  The three `jal ra` sites, the residual
  hypotheses they stand under, and the whole-routine triple that stitches these
  segments together live in `SystemCallStagingTop`.

  Segment map (indices are into `stageSystemCall_prog`; see
  `SystemCallStagingBase` for the full index table):
    `ssc_spill`             0 → 6    spill `ra`/`s0` to their BSS cells
    `ssc_park_target`       6 → 7    `mv t1, a0`
    `ssc_restore_target`    8 → 9    `mv a0, t1`
    `ssc_empty_gate_*`      9        the empty-predeploy-code gate
    `ssc_stage_setup`      10 → 25   zero the three cells, `system_call_mode := 1`
    `ssc_payload_gate_*`   26        the payload-reject gate
    `ssc_dispatch_setup`   27 → 31   `runtime_dispatcher_input_ptr := s0 + 8`
    `ssc_after_dispatch`   32 → 47   clear the flag, load `a0`/`a1`/`t1`
    `ssc_verdict`          47 → 64   the three-way halt-kind cascade
    `ssc_fail_block`       56 → 64   the shared staging-failure epilogue
    `ssc_tail`             64 → ret  restore `s0`/`ra` and return
-/

import EvmAsm.Codegen.Programs.SystemCallStagingResiduals
import EvmAsm.Rv64.SAsm.Fn
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.SystemCallStagingSegments

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.SystemCallStagingBase
open EvmAsm.Codegen.SystemCallStagingResiduals

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

/-! ## Small arithmetic bridges -/

private theorem se12_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

private theorem se12_8 : signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 := by decide

private theorem addr_ofs0 (w : Word) : w + signExtend12 (0 : BitVec 12) = w := by
  rw [se12_0]; bv_omega

/-- Two consecutive instructions of the routine form the `la` pair that
    materializes `target` in `rd`.  The `hins` equations are `decide`d against
    the emitted Program, so the CODEGEN-side immediates
    (`Codegen.laHi sym (stage_system_call + 4k)`) and the RV64-side ones
    (`Rv64.laHi (pc k) target`) are checked equal by the kernel rather than
    assumed. -/
theorem pc_next (k k' : Nat) (h : k' = k + 1) : (pc k : Word) + 4 = pc k' := by
  subst h; exact pc_succ k

private theorem la_step (k kexit : Nat) (rd : Reg) (vOld target : Word)
    (hexit : kexit = k + 2)
    (hrd : rd ≠ .x0)
    (hrange : laInRange (pc k) target)
    (hk1 : k < sscProgL.length) (hk2 : k + 1 < sscProgL.length)
    (hins1 : sscProgL[k]'hk1 = .AUIPC rd (Rv64.laHi (pc k) target))
    (hins2 : sscProgL[k + 1]'hk2 = .ADDI rd rd (Rv64.laLo (pc k) target)) :
    cpsTripleWithin 2 (pc k) (pc kexit) sscCode (rd ↦ᵣ vOld) (rd ↦ᵣ target) := by
  subst hexit
  have h := la_materialize_within (cr := sscCode) rd vOld (pc k) target hrd hrange
    (mem_at k _ (pc k) rfl hk1 hins1)
    (by rw [pc_succ k]; exact mem_at (k + 1) _ (pc (k + 1)) rfl hk2 hins2)
  rwa [pc_add8] at h

/-! ## Per-instruction step helpers

    Each takes the instruction's index and reads the opcode straight out of
    `sscProgL` by `decide`, so no instruction is transcribed twice. -/

private theorem li_step (k k' : Nat) (rd : Reg) (vOld imm : Word)
    (hk' : k' = k + 1) (hrd : rd ≠ .x0)
    (hk : k < sscProgL.length) (hins : sscProgL[k]'hk = .LI rd imm) :
    cpsTripleWithin 1 (pc k) (pc k') sscCode (rd ↦ᵣ vOld) (rd ↦ᵣ imm) := by
  subst hk'
  have h := cpsTripleWithin_extend_code (mem_at k _ (pc k) rfl hk hins)
    (li_spec_gen_within rd vOld imm (pc k) hrd)
  rwa [pc_succ k] at h

private theorem mv_step (k k' : Nat) (rd rs : Reg) (v vOld : Word)
    (hk' : k' = k + 1) (hrd : rd ≠ .x0)
    (hk : k < sscProgL.length) (hins : sscProgL[k]'hk = .MV rd rs) :
    cpsTripleWithin 1 (pc k) (pc k') sscCode
      ((rs ↦ᵣ v) ** (rd ↦ᵣ vOld)) ((rs ↦ᵣ v) ** (rd ↦ᵣ v)) := by
  subst hk'
  have h := cpsTripleWithin_extend_code (mem_at k _ (pc k) rfl hk hins)
    (mv_spec_gen_within rd rs v vOld (pc k) hrd)
  rwa [pc_succ k] at h

private theorem sd_step (k k' : Nat) (rs1 rs2 : Reg) (v_addr v_data : Word)
    (hk' : k' = k + 1)
    (hk : k < sscProgL.length) (hins : sscProgL[k]'hk = .SD rs1 rs2 (0 : BitVec 12)) :
    cpsTripleWithin 1 (pc k) (pc k') sscCode
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memOwn v_addr)
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (v_addr ↦ₘ v_data)) := by
  subst hk'
  have h := sd_spec_gen_own_within rs1 rs2 v_addr v_data (0 : BitVec 12) (pc k)
  rw [addr_ofs0, pc_succ k] at h
  exact cpsTripleWithin_extend_code (mem_at k _ (pc k) rfl hk hins) h

private theorem ld_step (k k' : Nat) (rd rs1 : Reg) (v_addr vOld memVal : Word)
    (hk' : k' = k + 1) (hrd : rd ≠ .x0)
    (hk : k < sscProgL.length) (hins : sscProgL[k]'hk = .LD rd rs1 (0 : BitVec 12)) :
    cpsTripleWithin 1 (pc k) (pc k') sscCode
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** (v_addr ↦ₘ memVal))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ memVal) ** (v_addr ↦ₘ memVal)) := by
  subst hk'
  have h := ld_spec_gen_within rd rs1 v_addr vOld memVal (0 : BitVec 12) (pc k) hrd
  rw [addr_ofs0, pc_succ k] at h
  exact cpsTripleWithin_extend_code (mem_at k _ (pc k) rfl hk hins) h

/-- `addi rd, rs1, 8` — the one non-zero immediate in the routine (index 27,
    `addi t1, s0, 8`), normalized to `+ BitVec.ofNat 64 8` so it matches the
    `runtime_dispatcher_input_ptr` value the dispatcher residual expects. -/
private theorem addi8_step (k k' : Nat) (rd rs1 : Reg) (v1 vOld : Word)
    (hk' : k' = k + 1) (hrd : rd ≠ .x0)
    (hk : k < sscProgL.length) (hins : sscProgL[k]'hk = .ADDI rd rs1 (8 : BitVec 12)) :
    cpsTripleWithin 1 (pc k) (pc k') sscCode
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + BitVec.ofNat 64 8))) := by
  subst hk'
  have h := addi_spec_gen_within rd rs1 vOld v1 (8 : BitVec 12) (pc k) hrd
  rw [se12_8, pc_succ k] at h
  exact cpsTripleWithin_extend_code (mem_at k _ (pc k) rfl hk hins) h

/-! ## The verdict functions

    Both are total functions of the residuals' abstract outputs, so the whole
    post is deterministic once those are fixed — the same shape `rhvVerdict`
    has in `requests_hash_verify`. -/

/-- The execution-status half: the dispatcher ran, and `rdg_halt_kind`
    discriminates success from failure.  `0 = STOP`, `1 = RETURN`,
    `5 = SELFDESTRUCT` are the success set (#11798 / #11815); anything else is
    `MessageCallOutput.error` and reports `2`. -/
def sscExecStatus (hk : Word) : Word :=
  if hk = 0 ∨ hk = 1 ∨ hk = 5 then 0 else 2

/-- The routine's status word `a2`.  `1` is the STAGING-failure class (empty
    predeploy code, or the payload stager rejecting); it must stay
    distinguishable from the EXECUTION-failure class `2` — see #11810. -/
def sscStatus (codeLen stP hk : Word) : Word :=
  if codeLen = 0 ∨ stP ≠ 0 then 1 else sscExecStatus hk

/-- The routine's returned length `a1`: zero on either staging-failure path
    (`li a1, 0` at index 62), the dispatcher's captured length otherwise. -/
def sscRetLen (codeLen stP retLen : Word) : Word :=
  if codeLen = 0 ∨ stP ≠ 0 then 0 else retLen

theorem sscStatus_fail_empty (stP hk : Word) : sscStatus 0 stP hk = 1 := by
  unfold sscStatus; rw [if_pos (Or.inl rfl)]

theorem sscStatus_fail_payload (codeLen stP hk : Word) (h : stP ≠ 0) :
    sscStatus codeLen stP hk = 1 := by
  unfold sscStatus; rw [if_pos (Or.inr h)]

theorem sscStatus_dispatched (codeLen hk : Word) (h : codeLen ≠ 0) :
    sscStatus codeLen 0 hk = sscExecStatus hk := by
  unfold sscStatus
  rw [if_neg (by rintro (hc | hc); exacts [h hc, hc rfl])]

theorem sscRetLen_fail_empty (stP retLen : Word) : sscRetLen 0 stP retLen = 0 := by
  unfold sscRetLen; rw [if_pos (Or.inl rfl)]

theorem sscRetLen_fail_payload (codeLen stP retLen : Word) (h : stP ≠ 0) :
    sscRetLen codeLen stP retLen = 0 := by
  unfold sscRetLen; rw [if_pos (Or.inr h)]

theorem sscRetLen_dispatched (codeLen retLen : Word) (h : codeLen ≠ 0) :
    sscRetLen codeLen 0 retLen = retLen := by
  unfold sscRetLen
  rw [if_neg (by rintro (hc | hc); exacts [h hc, hc rfl])]

/-! ### The two callee-independent facts the callers depend on -/

/-- **`a2 ∈ {0, 1, 2}`, for every instantiation of the three residuals.** -/
theorem sscStatus_mem_three (codeLen stP hk : Word) :
    sscStatus codeLen stP hk = 0 ∨ sscStatus codeLen stP hk = 1 ∨
      sscStatus codeLen stP hk = 2 := by
  unfold sscStatus sscExecStatus
  split
  · exact Or.inr (Or.inl rfl)
  · split
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)

/-- **The two failure classes stay distinguishable (#11810).**  `a2 = 1` holds
    exactly on the staging-failure paths — empty predeploy code, or the payload
    stager reporting a non-zero status — and never when the dispatcher ran.
    An implementation that collapsed `2` into `1` would break the unchecked
    4788/2935 callers, which reject only `a2 = 1`. -/
theorem sscStatus_eq_one_iff (codeLen stP hk : Word) :
    sscStatus codeLen stP hk = 1 ↔ (codeLen = 0 ∨ stP ≠ 0) := by
  unfold sscStatus sscExecStatus
  constructor
  · intro h
    by_contra hc
    rw [if_neg hc] at h
    split at h <;> exact absurd h (by decide)
  · intro h; rw [if_pos h]

/-- The execution-failure class is never `1`: `2` and `0` are the only values
    the cascade at indices 47–55 can produce. -/
theorem sscExecStatus_ne_one (hk : Word) : sscExecStatus hk ≠ 1 := by
  unfold sscExecStatus; split <;> decide

/-! ## Straight-line segments -/

/-- **Indices 0–5**: spill `ra` into `ssc_saved_ra` and `s0` into
    `ssc_saved_s0` (two `la` pairs and two `sd`s).  This is the routine's
    prologue; there is no stack frame. -/
theorem ssc_spill (ret v5 v8 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 6 (pc 0) (pc 6) sscCode
      ((.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ ret) ** (.x8 ↦ᵣ v8) **
        memOwn SscRa ** memOwn SscS0 ** F)
      ((.x5 ↦ᵣ SscS0) ** (.x1 ↦ᵣ ret) ** (.x8 ↦ᵣ v8) **
        (SscRa ↦ₘ ret) ** (SscS0 ↦ₘ v8) ** F) := by
  have h0 := la_step 0 2 .x5 v5 SscRa rfl (by decide) laRange_0
    (by rw [sscProgL_len]; norm_num) (by rw [sscProgL_len]; norm_num)
    (by decide) (by decide)
  have h0F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (.x8 ↦ᵣ v8) ** memOwn SscRa ** memOwn SscS0 ** F)
    (by pcfR; exact hF) h0
  have h2 := sd_spec_gen_own_within .x5 .x1 SscRa ret (0 : BitVec 12) (pc 2)
  rw [addr_ofs0, pc_next 2 3 rfl] at h2
  have h2' := cpsTripleWithin_extend_code
    (mem_at 2 (.SD .x5 .x1 (0 : BitVec 12)) (pc 2) rfl
      (by rw [sscProgL_len]; norm_num) (by decide)) h2
  have h2F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ v8) ** memOwn SscS0 ** F) (by pcfR; exact hF) h2'
  have h3 := la_step 3 5 .x5 SscRa SscS0 rfl (by decide) laRange_3
    (by rw [sscProgL_len]; norm_num) (by rw [sscProgL_len]; norm_num)
    (by decide) (by decide)
  have h3F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (.x8 ↦ᵣ v8) ** (SscRa ↦ₘ ret) ** memOwn SscS0 ** F)
    (by pcfR; exact hF) h3
  have h5 := sd_spec_gen_own_within .x5 .x8 SscS0 v8 (0 : BitVec 12) (pc 5)
  rw [addr_ofs0, pc_next 5 6 rfl] at h5
  have h5' := cpsTripleWithin_extend_code
    (mem_at 5 (.SD .x5 .x8 (0 : BitVec 12)) (pc 5) rfl
      (by rw [sscProgL_len]; norm_num) (by decide)) h5
  have h5F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (SscRa ↦ₘ ret) ** F) (by pcfR; exact hF) h5'
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) h0F h2F
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c0 h3F
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c1 h5F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c2

/-- `jal x0, off` carrying the surviving state (the library triple has
    `empAssertion` pre/post). -/
private theorem jal_x0_frame_within (P : Assertion) (hP : P.pcFree)
    (offset : BitVec 21) (addr : Word) :
    cpsTripleWithin 1 addr (addr + signExtend21 offset)
      (CodeReq.singleton addr (.JAL .x0 offset)) P P := by
  have h := cpsTripleWithin_frameL P hP (jal_x0_spec_gen_within offset addr)
  exact (sepConj_emp_right' P) ▸ h

/-- **Index 6** (`0x80053748`): `mv t1, a0` — park the target-address pointer
    in `t1` across the `account_read_record` call. -/
theorem ssc_park_target (tgt v6 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 6) (pc 7) sscCode
      ((.x10 ↦ᵣ tgt) ** (.x6 ↦ᵣ v6) ** F)
      ((.x10 ↦ᵣ tgt) ** (.x6 ↦ᵣ tgt) ** F) := by
  have h := cpsTripleWithin_extend_code
    (mem_at 6 (.MV .x6 .x10) (pc 6) rfl (by rw [sscProgL_len]; norm_num) (by decide))
    (mv_spec_gen_within .x6 .x10 tgt v6 (pc 6) (by decide))
  rw [pc_next 6 7 rfl] at h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) (cpsTripleWithin_frameR F hF h)

/-- **Index 8** (`0x80053750`): `mv a0, t1` — restore the target pointer that
    was parked at index 6.  Nothing about `account_read_record`'s treatment of
    `a0` is assumed; the routine recomputes it. -/
theorem ssc_restore_target (tgt w10 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 8) (pc 9) sscCode
      ((.x6 ↦ᵣ tgt) ** (.x10 ↦ᵣ w10) ** F)
      ((.x6 ↦ᵣ tgt) ** (.x10 ↦ᵣ tgt) ** F) := by
  have h := cpsTripleWithin_extend_code
    (mem_at 8 (.MV .x10 .x6) (pc 8) rfl (by rw [sscProgL_len]; norm_num) (by decide))
    (mv_spec_gen_within .x10 .x6 tgt w10 (pc 8) (by decide))
  rw [pc_next 8 9 rfl] at h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) (cpsTripleWithin_frameR F hF h)

/-! ### The empty-code gate (index 9) -/

/-- `beqz a2, +0xe0` at `0x80053754` with `a2 = 0`: empty predeploy code, so the
    routine jumps straight to the staging-failure epilogue at index 56 without
    ever setting `system_call_mode` or running the dispatcher.  Spec pin
    `process_checked_system_transaction` (fork.py:761-765). -/
theorem ssc_empty_gate_taken (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 9) (pc 56) sscCode
      ((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  have hbr0 := beq_spec_gen_within .x12 .x0
    (brOff (GuestAddrs.stage_system_call + 224) (GuestAddrs.stage_system_call + 36))
    (0 : Word) (0 : Word) (pc 9)
  rw [pc_beq_emptycode, pc_next 9 10 rfl] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (mem_at 9 (.BEQ .x12 .x0
      (brOff (GuestAddrs.stage_system_call + 224) (GuestAddrs.stage_system_call + 36)))
      (pc 9) rfl (by rw [sscProgL_len]; norm_num) (by decide)) hbr0
  have ht := cpsBranchWithin_takenStripPure2 hbr
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ((sepConj_pure_right _).1 hQ).2 rfl)
  have htF := cpsTripleWithin_frameR F hF ht
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) htF

/-- `beqz a2` with `a2 ≠ 0`: non-empty code, so staging proceeds at index 10. -/
theorem ssc_empty_gate_ntaken (codeLen : Word) (hcl : codeLen ≠ 0)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 9) (pc 10) sscCode
      ((.x12 ↦ᵣ codeLen) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x12 ↦ᵣ codeLen) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  have hbr0 := beq_spec_gen_within .x12 .x0
    (brOff (GuestAddrs.stage_system_call + 224) (GuestAddrs.stage_system_call + 36))
    codeLen (0 : Word) (pc 9)
  rw [pc_beq_emptycode, pc_next 9 10 rfl] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (mem_at 9 (.BEQ .x12 .x0
      (brOff (GuestAddrs.stage_system_call + 224) (GuestAddrs.stage_system_call + 36)))
      (pc 9) rfl (by rw [sscProgL_len]; norm_num) (by decide)) hbr0
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact hcl ((sepConj_pure_right _).1 hQ).2)
  have hntF := cpsTripleWithin_frameR F hF hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hntF

/-! ### The payload-reject gate (index 26) -/

/-- `bnez a0, +0xa0` at `0x80053798` with a non-zero payload-stager status:
    staging failed, jump to index 56.  Nothing about WHY it failed is claimed —
    `stP` is the residual's abstract output. -/
theorem ssc_payload_gate_taken (stP : Word) (hst : stP ≠ 0)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 26) (pc 56) sscCode
      ((.x10 ↦ᵣ stP) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ stP) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  have hbr0 := bne_spec_gen_within .x10 .x0
    (brOff (GuestAddrs.stage_system_call + 224) (GuestAddrs.stage_system_call + 104))
    stP (0 : Word) (pc 26)
  rw [pc_bne_payloadfail, pc_next 26 27 rfl] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (mem_at 26 (.BNE .x10 .x0
      (brOff (GuestAddrs.stage_system_call + 224) (GuestAddrs.stage_system_call + 104)))
      (pc 26) rfl (by rw [sscProgL_len]; norm_num) (by decide)) hbr0
  have ht := cpsBranchWithin_takenStripPure2 hbr
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact hst ((sepConj_pure_right _).1 hQ).2)
  have htF := cpsTripleWithin_frameR F hF ht
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) htF

/-- `bnez a0` with a zero payload-stager status: proceed to the dispatcher
    setup at index 27. -/
theorem ssc_payload_gate_ntaken (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 26) (pc 27) sscCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  have hbr0 := bne_spec_gen_within .x10 .x0
    (brOff (GuestAddrs.stage_system_call + 224) (GuestAddrs.stage_system_call + 104))
    (0 : Word) (0 : Word) (pc 26)
  rw [pc_bne_payloadfail, pc_next 26 27 rfl] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (mem_at 26 (.BNE .x10 .x0
      (brOff (GuestAddrs.stage_system_call + 224) (GuestAddrs.stage_system_call + 104)))
      (pc 26) rfl (by rw [sscProgL_len]; norm_num) (by decide)) hbr0
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 rfl)
  have hntF := cpsTripleWithin_frameR F hF hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hntF

/-- **Indices 10–24** (`0x80053758`–`0x80053790`): park the output payload
    buffer in `s0`, zero `system_call_returndata_len`, set `system_call_mode`
    to 1 (the NoopHalt capture flag, #8681), and zero
    `runtime_tx_auth_exec_fn` and `rdg_halt_kind`. -/
theorem ssc_stage_setup (payloadOut w5 w6 w8 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 15 (pc 10) (pc 25) sscCode
      ((.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ w5) **
        (.x6 ↦ᵣ w6) **
        (.x8 ↦ᵣ w8) **
        (.x14 ↦ᵣ payloadOut) **
        memOwn SccLen **
        memOwn SccMode **
        memOwn RtAuthFn **
        memOwn RdgHalt **
        F)
      ((.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ RdgHalt) **
        (.x6 ↦ᵣ RtAuthFn) **
        (.x8 ↦ᵣ payloadOut) **
        (.x14 ↦ᵣ payloadOut) **
        (SccLen ↦ₘ (0 : Word)) **
        (SccMode ↦ₘ (1 : Word)) **
        (RtAuthFn ↦ₘ (0 : Word)) **
        (RdgHalt ↦ₘ (0 : Word)) **
        F) := by
  have h10 := mv_step 10 11 .x8 .x14 payloadOut w8 rfl (by decide) (by rw [sscProgL_len]; norm_num) (by decide)
  have h10F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** memOwn SccLen ** memOwn SccMode ** memOwn RtAuthFn ** memOwn RdgHalt ** F)
    (by pcfR; exact hF) h10
  have h11 := li_step 11 12 .x5 w5 (0 : Word) rfl (by decide) (by rw [sscProgL_len]; norm_num) (by decide)
  have h11F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ w6) ** (.x8 ↦ᵣ payloadOut) ** (.x14 ↦ᵣ payloadOut) ** memOwn SccLen ** memOwn SccMode ** memOwn RtAuthFn ** memOwn RdgHalt ** F)
    (by pcfR; exact hF) h11
  have h12 := la_step 12 14 .x6 w6 SccLen rfl (by decide) laRange_12 (by rw [sscProgL_len]; norm_num) (by rw [sscProgL_len]; norm_num) (by decide) (by decide)
  have h12F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ payloadOut) ** (.x14 ↦ᵣ payloadOut) ** memOwn SccLen ** memOwn SccMode ** memOwn RtAuthFn ** memOwn RdgHalt ** F)
    (by pcfR; exact hF) h12
  have h14 := sd_step 14 15 .x6 .x5 SccLen (0 : Word) rfl (by rw [sscProgL_len]; norm_num) (by decide)
  have h14F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ payloadOut) ** (.x14 ↦ᵣ payloadOut) ** memOwn SccMode ** memOwn RtAuthFn ** memOwn RdgHalt ** F)
    (by pcfR; exact hF) h14
  have h15 := li_step 15 16 .x5 (0 : Word) (1 : Word) rfl (by decide) (by rw [sscProgL_len]; norm_num) (by decide)
  have h15F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ SccLen) ** (.x8 ↦ᵣ payloadOut) ** (.x14 ↦ᵣ payloadOut) ** (SccLen ↦ₘ (0 : Word)) ** memOwn SccMode ** memOwn RtAuthFn ** memOwn RdgHalt ** F)
    (by pcfR; exact hF) h15
  have h16 := la_step 16 18 .x6 SccLen SccMode rfl (by decide) laRange_16 (by rw [sscProgL_len]; norm_num) (by rw [sscProgL_len]; norm_num) (by decide) (by decide)
  have h16F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x8 ↦ᵣ payloadOut) ** (.x14 ↦ᵣ payloadOut) ** (SccLen ↦ₘ (0 : Word)) ** memOwn SccMode ** memOwn RtAuthFn ** memOwn RdgHalt ** F)
    (by pcfR; exact hF) h16
  have h18 := sd_step 18 19 .x6 .x5 SccMode (1 : Word) rfl (by rw [sscProgL_len]; norm_num) (by decide)
  have h18F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ payloadOut) ** (.x14 ↦ᵣ payloadOut) ** (SccLen ↦ₘ (0 : Word)) ** memOwn RtAuthFn ** memOwn RdgHalt ** F)
    (by pcfR; exact hF) h18
  have h19 := la_step 19 21 .x6 SccMode RtAuthFn rfl (by decide) laRange_19 (by rw [sscProgL_len]; norm_num) (by rw [sscProgL_len]; norm_num) (by decide) (by decide)
  have h19F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x8 ↦ᵣ payloadOut) ** (.x14 ↦ᵣ payloadOut) ** (SccLen ↦ₘ (0 : Word)) ** (SccMode ↦ₘ (1 : Word)) ** memOwn RtAuthFn ** memOwn RdgHalt ** F)
    (by pcfR; exact hF) h19
  have h21 := sd_step 21 22 .x6 .x0 RtAuthFn (0 : Word) rfl (by rw [sscProgL_len]; norm_num) (by decide)
  have h21F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (1 : Word)) ** (.x8 ↦ᵣ payloadOut) ** (.x14 ↦ᵣ payloadOut) ** (SccLen ↦ₘ (0 : Word)) ** (SccMode ↦ₘ (1 : Word)) ** memOwn RdgHalt ** F)
    (by pcfR; exact hF) h21
  have h22 := la_step 22 24 .x5 (1 : Word) RdgHalt rfl (by decide) laRange_22 (by rw [sscProgL_len]; norm_num) (by rw [sscProgL_len]; norm_num) (by decide) (by decide)
  have h22F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ RtAuthFn) ** (.x8 ↦ᵣ payloadOut) ** (.x14 ↦ᵣ payloadOut) ** (SccLen ↦ₘ (0 : Word)) ** (SccMode ↦ₘ (1 : Word)) ** (RtAuthFn ↦ₘ (0 : Word)) ** memOwn RdgHalt ** F)
    (by pcfR; exact hF) h22
  have h24 := sd_step 24 25 .x5 .x0 RdgHalt (0 : Word) rfl (by rw [sscProgL_len]; norm_num) (by decide)
  have h24F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ RtAuthFn) ** (.x8 ↦ᵣ payloadOut) ** (.x14 ↦ᵣ payloadOut) ** (SccLen ↦ₘ (0 : Word)) ** (SccMode ↦ₘ (1 : Word)) ** (RtAuthFn ↦ₘ (0 : Word)) ** F)
    (by pcfR; exact hF) h24
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) h10F h11F
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c0 h12F
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c1 h14F
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c2 h15F
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c3 h16F
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c4 h18F
  have c6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c5 h19F
  have c7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c6 h21F
  have c8 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c7 h22F
  have c9 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c8 h24F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c9

/-- **Indices 27–30** (`0x8005379c`–`0x800537a8`):
    `runtime_dispatcher_input_ptr := s0 + 8`, the dispatcher's input record. -/
theorem ssc_dispatch_setup (payloadOut u5 u6 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (pc 27) (pc 31) sscCode
      ((.x5 ↦ᵣ u5) **
        (.x6 ↦ᵣ u6) **
        (.x8 ↦ᵣ payloadOut) **
        memOwn RdInPtr **
        F)
      ((.x5 ↦ᵣ RdInPtr) **
        (.x6 ↦ᵣ (payloadOut + BitVec.ofNat 64 8)) **
        (.x8 ↦ᵣ payloadOut) **
        (RdInPtr ↦ₘ (payloadOut + BitVec.ofNat 64 8)) **
        F) := by
  have h27 := addi8_step 27 28 .x6 .x8 payloadOut u6 rfl (by decide) (by rw [sscProgL_len]; norm_num) (by decide)
  have h27F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ u5) ** memOwn RdInPtr ** F)
    (by pcfR; exact hF) h27
  have h28 := la_step 28 30 .x5 u5 RdInPtr rfl (by decide) laRange_28 (by rw [sscProgL_len]; norm_num) (by rw [sscProgL_len]; norm_num) (by decide) (by decide)
  have h28F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (payloadOut + BitVec.ofNat 64 8)) ** (.x8 ↦ᵣ payloadOut) ** memOwn RdInPtr ** F)
    (by pcfR; exact hF) h28
  have h30 := sd_step 30 31 .x5 .x6 RdInPtr (payloadOut + BitVec.ofNat 64 8) rfl (by rw [sscProgL_len]; norm_num) (by decide)
  have h30F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ payloadOut) ** F)
    (by pcfR; exact hF) h30
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) h27F h28F
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c0 h30F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c1

/-- **Indices 32–46** (`0x800537b0`–`0x800537e8`): clear the dispatcher input
    pointer and `system_call_mode`, then load the three caller-visible results —
    `a0 := &system_call_returndata`, `a1 := [system_call_returndata_len]`,
    `t1 := [rdg_halt_kind]`.  `retLen` and `hk` are the dispatcher residual's
    abstract outputs; nothing is claimed about their values. -/
theorem ssc_after_dispatch (retLen hk q5 q6 q10 q11 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 15 (pc 32) (pc 47) sscCode
      ((.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ q5) **
        (.x6 ↦ᵣ q6) **
        (.x10 ↦ᵣ q10) **
        (.x11 ↦ᵣ q11) **
        memOwn SccMode **
        memOwn RdInPtr **
        (SccLen ↦ₘ retLen) **
        (RdgHalt ↦ₘ hk) **
        F)
      ((.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ RdgHalt) **
        (.x6 ↦ᵣ hk) **
        (.x10 ↦ᵣ SccData) **
        (.x11 ↦ᵣ retLen) **
        (SccMode ↦ₘ (0 : Word)) **
        (RdInPtr ↦ₘ (0 : Word)) **
        (SccLen ↦ₘ retLen) **
        (RdgHalt ↦ₘ hk) **
        F) := by
  have h32 := la_step 32 34 .x5 q5 RdInPtr rfl (by decide) laRange_32 (by rw [sscProgL_len]; norm_num) (by rw [sscProgL_len]; norm_num) (by decide) (by decide)
  have h32F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ q6) ** (.x10 ↦ᵣ q10) ** (.x11 ↦ᵣ q11) ** memOwn SccMode ** memOwn RdInPtr ** (SccLen ↦ₘ retLen) ** (RdgHalt ↦ₘ hk) ** F)
    (by pcfR; exact hF) h32
  have h34 := sd_step 34 35 .x5 .x0 RdInPtr (0 : Word) rfl (by rw [sscProgL_len]; norm_num) (by decide)
  have h34F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ q6) ** (.x10 ↦ᵣ q10) ** (.x11 ↦ᵣ q11) ** memOwn SccMode ** (SccLen ↦ₘ retLen) ** (RdgHalt ↦ₘ hk) ** F)
    (by pcfR; exact hF) h34
  have h35 := li_step 35 36 .x5 RdInPtr (0 : Word) rfl (by decide) (by rw [sscProgL_len]; norm_num) (by decide)
  have h35F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ q6) ** (.x10 ↦ᵣ q10) ** (.x11 ↦ᵣ q11) ** memOwn SccMode ** (RdInPtr ↦ₘ (0 : Word)) ** (SccLen ↦ₘ retLen) ** (RdgHalt ↦ₘ hk) ** F)
    (by pcfR; exact hF) h35
  have h36 := la_step 36 38 .x6 q6 SccMode rfl (by decide) laRange_36 (by rw [sscProgL_len]; norm_num) (by rw [sscProgL_len]; norm_num) (by decide) (by decide)
  have h36F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ q10) ** (.x11 ↦ᵣ q11) ** memOwn SccMode ** (RdInPtr ↦ₘ (0 : Word)) ** (SccLen ↦ₘ retLen) ** (RdgHalt ↦ₘ hk) ** F)
    (by pcfR; exact hF) h36
  have h38 := sd_step 38 39 .x6 .x5 SccMode (0 : Word) rfl (by rw [sscProgL_len]; norm_num) (by decide)
  have h38F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ q10) ** (.x11 ↦ᵣ q11) ** (RdInPtr ↦ₘ (0 : Word)) ** (SccLen ↦ₘ retLen) ** (RdgHalt ↦ₘ hk) ** F)
    (by pcfR; exact hF) h38
  have h39 := la_step 39 41 .x10 q10 SccData rfl (by decide) laRange_39 (by rw [sscProgL_len]; norm_num) (by rw [sscProgL_len]; norm_num) (by decide) (by decide)
  have h39F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ SccMode) ** (.x11 ↦ᵣ q11) ** (SccMode ↦ₘ (0 : Word)) ** (RdInPtr ↦ₘ (0 : Word)) ** (SccLen ↦ₘ retLen) ** (RdgHalt ↦ₘ hk) ** F)
    (by pcfR; exact hF) h39
  have h41 := la_step 41 43 .x5 (0 : Word) SccLen rfl (by decide) laRange_41 (by rw [sscProgL_len]; norm_num) (by rw [sscProgL_len]; norm_num) (by decide) (by decide)
  have h41F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ SccMode) ** (.x10 ↦ᵣ SccData) ** (.x11 ↦ᵣ q11) ** (SccMode ↦ₘ (0 : Word)) ** (RdInPtr ↦ₘ (0 : Word)) ** (SccLen ↦ₘ retLen) ** (RdgHalt ↦ₘ hk) ** F)
    (by pcfR; exact hF) h41
  have h43 := ld_step 43 44 .x11 .x5 SccLen q11 retLen rfl (by decide) (by rw [sscProgL_len]; norm_num) (by decide)
  have h43F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ SccMode) ** (.x10 ↦ᵣ SccData) ** (SccMode ↦ₘ (0 : Word)) ** (RdInPtr ↦ₘ (0 : Word)) ** (RdgHalt ↦ₘ hk) ** F)
    (by pcfR; exact hF) h43
  have h44 := la_step 44 46 .x5 SccLen RdgHalt rfl (by decide) laRange_44 (by rw [sscProgL_len]; norm_num) (by rw [sscProgL_len]; norm_num) (by decide) (by decide)
  have h44F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ SccMode) ** (.x10 ↦ᵣ SccData) ** (.x11 ↦ᵣ retLen) ** (SccMode ↦ₘ (0 : Word)) ** (RdInPtr ↦ₘ (0 : Word)) ** (SccLen ↦ₘ retLen) ** (RdgHalt ↦ₘ hk) ** F)
    (by pcfR; exact hF) h44
  have h46 := ld_step 46 47 .x6 .x5 RdgHalt SccMode hk rfl (by decide) (by rw [sscProgL_len]; norm_num) (by decide)
  have h46F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ SccData) ** (.x11 ↦ᵣ retLen) ** (SccMode ↦ₘ (0 : Word)) ** (RdInPtr ↦ₘ (0 : Word)) ** (SccLen ↦ₘ retLen) ** F)
    (by pcfR; exact hF) h46
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) h32F h34F
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c0 h35F
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c1 h36F
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c2 h38F
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c3 h39F
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c4 h41F
  have c6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c5 h43F
  have c7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c6 h44F
  have c8 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c7 h46F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c8

/-- **Indices 56–63** (`0x80053810`–`0x8005382c`): the shared staging-failure
    epilogue, reached from the empty-code gate at index 9 and the
    payload-reject gate at index 26.  It clears `system_call_mode` and sets
    the three caller-visible results `a0 = &system_call_returndata`, `a1 = 0`,
    `a2 = 1`.  `a2 = 1` is written HERE, by this routine, which is why the
    staging-failure class is callee-independent. -/
theorem ssc_fail_block (a5 a6 a10 a11 a12 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 8 (pc 56) (pc 64) sscCode
      ((.x5 ↦ᵣ a5) **
        (.x6 ↦ᵣ a6) **
        (.x10 ↦ᵣ a10) **
        (.x11 ↦ᵣ a11) **
        (.x12 ↦ᵣ a12) **
        memOwn SccMode **
        F)
      ((.x5 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ SccMode) **
        (.x10 ↦ᵣ SccData) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (1 : Word)) **
        (SccMode ↦ₘ (0 : Word)) **
        F) := by
  have h56 := li_step 56 57 .x5 a5 (0 : Word) rfl (by decide) (by rw [sscProgL_len]; norm_num) (by decide)
  have h56F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ a6) ** (.x10 ↦ᵣ a10) ** (.x11 ↦ᵣ a11) ** (.x12 ↦ᵣ a12) ** memOwn SccMode ** F)
    (by pcfR; exact hF) h56
  have h57 := la_step 57 59 .x6 a6 SccMode rfl (by decide) laRange_57 (by rw [sscProgL_len]; norm_num) (by rw [sscProgL_len]; norm_num) (by decide) (by decide)
  have h57F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ a10) ** (.x11 ↦ᵣ a11) ** (.x12 ↦ᵣ a12) ** memOwn SccMode ** F)
    (by pcfR; exact hF) h57
  have h59 := sd_step 59 60 .x6 .x5 SccMode (0 : Word) rfl (by rw [sscProgL_len]; norm_num) (by decide)
  have h59F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a10) ** (.x11 ↦ᵣ a11) ** (.x12 ↦ᵣ a12) ** F)
    (by pcfR; exact hF) h59
  have h60 := la_step 60 62 .x10 a10 SccData rfl (by decide) laRange_60 (by rw [sscProgL_len]; norm_num) (by rw [sscProgL_len]; norm_num) (by decide) (by decide)
  have h60F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ SccMode) ** (.x11 ↦ᵣ a11) ** (.x12 ↦ᵣ a12) ** (SccMode ↦ₘ (0 : Word)) ** F)
    (by pcfR; exact hF) h60
  have h62 := li_step 62 63 .x11 a11 (0 : Word) rfl (by decide) (by rw [sscProgL_len]; norm_num) (by decide)
  have h62F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ SccMode) ** (.x10 ↦ᵣ SccData) ** (.x12 ↦ᵣ a12) ** (SccMode ↦ₘ (0 : Word)) ** F)
    (by pcfR; exact hF) h62
  have h63 := li_step 63 64 .x12 a12 (1 : Word) rfl (by decide) (by rw [sscProgL_len]; norm_num) (by decide)
  have h63F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ SccMode) ** (.x10 ↦ᵣ SccData) ** (.x11 ↦ᵣ (0 : Word)) ** (SccMode ↦ₘ (0 : Word)) ** F)
    (by pcfR; exact hF) h63
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) h56F h57F
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c0 h59F
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c1 h60F
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c2 h62F
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c3 h63F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c4

/-! ### Branch and join helpers -/

private theorem beq_taken_step (k kt : Nat) (rs1 rs2 : Reg) (offset : BitVec 13) (v : Word)
    (htgt : (pc k : Word) + signExtend13 offset = pc kt)
    (hk : k < sscProgL.length) (hins : sscProgL[k]'hk = .BEQ rs1 rs2 offset)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc k) (pc kt) sscCode
      ((rs1 ↦ᵣ v) ** (rs2 ↦ᵣ v) ** F) ((rs1 ↦ᵣ v) ** (rs2 ↦ᵣ v) ** F) := by
  have hbr0 := beq_spec_gen_within rs1 rs2 offset v v (pc k)
  rw [htgt] at hbr0
  have hbr := cpsBranchWithin_extend_code (mem_at k _ (pc k) rfl hk hins) hbr0
  have ht := cpsBranchWithin_takenStripPure2 hbr
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ((sepConj_pure_right _).1 hQ).2 rfl)
  have htF := cpsTripleWithin_frameR F hF ht
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) htF

private theorem beq_ntaken_step (k kn : Nat) (rs1 rs2 : Reg) (offset : BitVec 13)
    (v1 v2 : Word) (hne : v1 ≠ v2) (hkn : kn = k + 1)
    (hk : k < sscProgL.length) (hins : sscProgL[k]'hk = .BEQ rs1 rs2 offset)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc k) (pc kn) sscCode
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** F) ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** F) := by
  subst hkn
  have hbr0 := beq_spec_gen_within rs1 rs2 offset v1 v2 (pc k)
  rw [pc_succ k] at hbr0
  have hbr := cpsBranchWithin_extend_code (mem_at k _ (pc k) rfl hk hins) hbr0
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact hne ((sepConj_pure_right _).1 hQ).2)
  have hntF := cpsTripleWithin_frameR F hF hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hntF

private theorem jal_join_step (k kt : Nat) (offset : BitVec 21)
    (htgt : (pc k : Word) + signExtend21 offset = pc kt)
    (hk : k < sscProgL.length) (hins : sscProgL[k]'hk = .JAL .x0 offset)
    (P : Assertion) (hP : P.pcFree) :
    cpsTripleWithin 1 (pc k) (pc kt) sscCode P P := by
  have h := jal_x0_frame_within P hP offset (pc k)
  rw [htgt] at h
  exact cpsTripleWithin_extend_code (mem_at k _ (pc k) rfl hk hins) h

/-- Weakening a concrete `t0` to owned — `t0` is dead from index 52 onward
    (the restore block reloads it at index 64), so its value is not part of the
    caller-visible post. -/
private theorem own_x5_weaken (v5 : Word) (Rest : Assertion) :
    ∀ h, ((.x5 ↦ᵣ v5) ** Rest) h → (regOwn .x5 ** Rest) h :=
  sepConj_mono_left (fun _ hv => ⟨v5, hv⟩)

/-! ### The two verdict exits -/

/-- **Indices 54–55**: `li a2, 0` (success) then `j +36` to the restore
    block. -/
private theorem ssc_exit_ok (v12 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 54) (pc 64) sscCode
      ((.x12 ↦ᵣ v12) ** F) ((.x12 ↦ᵣ (0 : Word)) ** F) := by
  have h54 := li_step 54 55 .x12 v12 (0 : Word) rfl (by decide)
    (by rw [sscProgL_len]; norm_num) (by decide)
  have h54F := cpsTripleWithin_frameR F hF h54
  have h55 := jal_join_step 55 64 (36 : BitVec 21) pc_jal_ok_join
    (by rw [sscProgL_len]; norm_num) (by decide)
    ((.x12 ↦ᵣ (0 : Word)) ** F) (by pcfR; exact hF)
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) h54F h55

/-- **Indices 52–53**: `li a2, 2` (execution failure) then `j +44` to the
    restore block. -/
private theorem ssc_exit_execfail (v12 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 52) (pc 64) sscCode
      ((.x12 ↦ᵣ v12) ** F) ((.x12 ↦ᵣ (2 : Word)) ** F) := by
  have h52 := li_step 52 53 .x12 v12 (2 : Word) rfl (by decide)
    (by rw [sscProgL_len]; norm_num) (by decide)
  have h52F := cpsTripleWithin_frameR F hF h52
  have h53 := jal_join_step 53 64 (44 : BitVec 21) pc_jal_execfail_join
    (by rw [sscProgL_len]; norm_num) (by decide)
    ((.x12 ↦ᵣ (2 : Word)) ** F) (by pcfR; exact hF)
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) h52F h53

/-! ### The halt-kind cascade (indices 47–55) -/

/-- **Indices 47–55**: the three-way `rdg_halt_kind` test.  `a2` is set to `0`
    when the halt kind is `STOP` (0), `RETURN` (1) or `SELFDESTRUCT` (5), and
    to `2` otherwise — `sscExecStatus`.  Both values are written by `li`
    instructions of THIS routine, so neither depends on the dispatcher beyond
    the abstract `hkv` it left in the cell. -/
theorem ssc_verdict (hkv v5 v12 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 7 (pc 47) (pc 64) sscCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ hkv) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12) ** F)
      (regOwn .x5 ** (.x6 ↦ᵣ hkv) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ sscExecStatus hkv) ** F) := by
  by_cases h0 : hkv = 0
  · subst h0
    rw [show sscExecStatus (0 : Word) = 0 from by
      unfold sscExecStatus; rw [if_pos (Or.inl rfl)]]
    have b47 := beq_taken_step 47 54 .x6 .x0 (28 : BitVec 13) (0 : Word)
      pc_beq_halt_stop (by rw [sscProgL_len]; norm_num) (by decide)
      ((.x5 ↦ᵣ v5) ** (.x12 ↦ᵣ v12) ** F) (by pcfR; exact hF)
    have e54 := ssc_exit_ok v12
      ((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** F)
      (by pcfR; exact hF)
    have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) b47 e54
    refine cpsTripleWithin_mono_nSteps (by norm_num)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun h hq => ?_) c)
    exact own_x5_weaken v5 _ h (by xperm_chunked hq)
  · by_cases h1 : hkv = 1
    · subst h1
      rw [show sscExecStatus (1 : Word) = 0 from by
        unfold sscExecStatus; rw [if_pos (Or.inr (Or.inl rfl))]]
      have b47 := beq_ntaken_step 47 48 .x6 .x0 (28 : BitVec 13) (1 : Word) (0 : Word)
        (by decide) rfl (by rw [sscProgL_len]; norm_num) (by decide)
        ((.x5 ↦ᵣ v5) ** (.x12 ↦ᵣ v12) ** F) (by pcfR; exact hF)
      have s48 := li_step 48 49 .x5 v5 (1 : Word) rfl (by decide)
        (by rw [sscProgL_len]; norm_num) (by decide)
      have s48F := cpsTripleWithin_frameR
        ((.x6 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12) ** F)
        (by pcfR; exact hF) s48
      have b49 := beq_taken_step 49 54 .x6 .x5 (20 : BitVec 13) (1 : Word)
        pc_beq_halt_return (by rw [sscProgL_len]; norm_num) (by decide)
        ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12) ** F) (by pcfR; exact hF)
      have e54 := ssc_exit_ok v12
        ((.x6 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (1 : Word)) ** F)
        (by pcfR; exact hF)
      have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) b47 s48F
      have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c0 b49
      have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c1 e54
      refine cpsTripleWithin_mono_nSteps (by norm_num)
        (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun h hq => ?_) c2)
      exact own_x5_weaken (1 : Word) _ h (by xperm_chunked hq)
    · by_cases h5 : hkv = 5
      · subst h5
        rw [show sscExecStatus (5 : Word) = 0 from by
          unfold sscExecStatus; rw [if_pos (Or.inr (Or.inr rfl))]]
        have b47 := beq_ntaken_step 47 48 .x6 .x0 (28 : BitVec 13) (5 : Word) (0 : Word)
          (by decide) rfl (by rw [sscProgL_len]; norm_num) (by decide)
          ((.x5 ↦ᵣ v5) ** (.x12 ↦ᵣ v12) ** F) (by pcfR; exact hF)
        have s48 := li_step 48 49 .x5 v5 (1 : Word) rfl (by decide)
          (by rw [sscProgL_len]; norm_num) (by decide)
        have s48F := cpsTripleWithin_frameR
          ((.x6 ↦ᵣ (5 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12) ** F)
          (by pcfR; exact hF) s48
        have b49 := beq_ntaken_step 49 50 .x6 .x5 (20 : BitVec 13) (5 : Word) (1 : Word)
          (by decide) rfl (by rw [sscProgL_len]; norm_num) (by decide)
          ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12) ** F) (by pcfR; exact hF)
        have s50 := li_step 50 51 .x5 (1 : Word) (5 : Word) rfl (by decide)
          (by rw [sscProgL_len]; norm_num) (by decide)
        have s50F := cpsTripleWithin_frameR
          ((.x6 ↦ᵣ (5 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12) ** F)
          (by pcfR; exact hF) s50
        have b51 := beq_taken_step 51 54 .x6 .x5 (12 : BitVec 13) (5 : Word)
          pc_beq_halt_selfdestruct (by rw [sscProgL_len]; norm_num) (by decide)
          ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12) ** F) (by pcfR; exact hF)
        have e54 := ssc_exit_ok v12
          ((.x6 ↦ᵣ (5 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (5 : Word)) ** F)
          (by pcfR; exact hF)
        have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) b47 s48F
        have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c0 b49
        have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c1 s50F
        have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c2 b51
        have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c3 e54
        refine cpsTripleWithin_mono_nSteps (by norm_num)
          (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun h hq => ?_) c4)
        exact own_x5_weaken (5 : Word) _ h (by xperm_chunked hq)
      · rw [show sscExecStatus hkv = 2 from by
          unfold sscExecStatus
          rw [if_neg (by rintro (hc | hc | hc); exacts [h0 hc, h1 hc, h5 hc])]]
        have b47 := beq_ntaken_step 47 48 .x6 .x0 (28 : BitVec 13) hkv (0 : Word)
          h0 rfl (by rw [sscProgL_len]; norm_num) (by decide)
          ((.x5 ↦ᵣ v5) ** (.x12 ↦ᵣ v12) ** F) (by pcfR; exact hF)
        have s48 := li_step 48 49 .x5 v5 (1 : Word) rfl (by decide)
          (by rw [sscProgL_len]; norm_num) (by decide)
        have s48F := cpsTripleWithin_frameR
          ((.x6 ↦ᵣ hkv) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12) ** F)
          (by pcfR; exact hF) s48
        have b49 := beq_ntaken_step 49 50 .x6 .x5 (20 : BitVec 13) hkv (1 : Word)
          h1 rfl (by rw [sscProgL_len]; norm_num) (by decide)
          ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12) ** F) (by pcfR; exact hF)
        have s50 := li_step 50 51 .x5 (1 : Word) (5 : Word) rfl (by decide)
          (by rw [sscProgL_len]; norm_num) (by decide)
        have s50F := cpsTripleWithin_frameR
          ((.x6 ↦ᵣ hkv) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12) ** F)
          (by pcfR; exact hF) s50
        have b51 := beq_ntaken_step 51 52 .x6 .x5 (12 : BitVec 13) hkv (5 : Word)
          h5 rfl (by rw [sscProgL_len]; norm_num) (by decide)
          ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12) ** F) (by pcfR; exact hF)
        have e52 := ssc_exit_execfail v12
          ((.x6 ↦ᵣ hkv) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (5 : Word)) ** F)
          (by pcfR; exact hF)
        have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) b47 s48F
        have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c0 b49
        have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c1 s50F
        have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c2 b51
        have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c3 e52
        refine cpsTripleWithin_mono_nSteps (by norm_num)
          (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun h hq => ?_) c4)
        exact own_x5_weaken (5 : Word) _ h (by xperm_chunked hq)

/-! ### The restore block (indices 64–70) -/

/-- **Indices 64–70** (`0x80053830`–`0x80053848`): reload `s0` from
    `ssc_saved_s0` and `ra` from `ssc_saved_ra`, then `ret`.  This is where the
    routine's whole register discipline is discharged: whatever the three
    callees did to `s0` and `ra`, both come back from the two dedicated
    cells. -/
theorem ssc_tail (ret v8 b1 b5 b8 : Word) (halign : (ret &&& ~~~(1 : Word)) = ret)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 7 (pc 64) ret sscCode
      ((.x5 ↦ᵣ b5) ** (.x8 ↦ᵣ b8) ** (.x1 ↦ᵣ b1) **
        (SscS0 ↦ₘ v8) ** (SscRa ↦ₘ ret) ** F)
      ((.x5 ↦ᵣ SscRa) ** (.x8 ↦ᵣ v8) ** (.x1 ↦ᵣ ret) **
        (SscS0 ↦ₘ v8) ** (SscRa ↦ₘ ret) ** F) := by
  have h64 := la_step 64 66 .x5 b5 SscS0 rfl (by decide) laRange_64
    (by rw [sscProgL_len]; norm_num) (by rw [sscProgL_len]; norm_num)
    (by decide) (by decide)
  have h64F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ b8) ** (.x1 ↦ᵣ b1) ** (SscS0 ↦ₘ v8) ** (SscRa ↦ₘ ret) ** F)
    (by pcfR; exact hF) h64
  have h66 := ld_step 66 67 .x8 .x5 SscS0 b8 v8 rfl (by decide)
    (by rw [sscProgL_len]; norm_num) (by decide)
  have h66F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ b1) ** (SscRa ↦ₘ ret) ** F) (by pcfR; exact hF) h66
  have h67 := la_step 67 69 .x5 SscS0 SscRa rfl (by decide) laRange_67
    (by rw [sscProgL_len]; norm_num) (by rw [sscProgL_len]; norm_num)
    (by decide) (by decide)
  have h67F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ v8) ** (.x1 ↦ᵣ b1) ** (SscS0 ↦ₘ v8) ** (SscRa ↦ₘ ret) ** F)
    (by pcfR; exact hF) h67
  have h69 := ld_step 69 70 .x1 .x5 SscRa b1 ret rfl (by decide)
    (by rw [sscProgL_len]; norm_num) (by decide)
  have h69F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ v8) ** (SscS0 ↦ₘ v8) ** F) (by pcfR; exact hF) h69
  have h70 := cpsTripleWithin_extend_code
    (mem_at 70 (.JALR .x0 .x1 (0 : BitVec 12)) (pc 70) rfl
      (by rw [sscProgL_len]; norm_num) (by decide))
    (EvmAsm.Rv64.SAsm.Fn.jalr_ret_spec (pc 70) ret halign
      (P := (.x5 ↦ᵣ SscRa) ** (.x8 ↦ᵣ v8) ** (SscS0 ↦ₘ v8) ** (SscRa ↦ₘ ret) ** F)
      (by pcfR; exact hF))
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) h64F h66F
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c0 h67F
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c1 h69F
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c2 h70
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c3


end EvmAsm.Codegen.SystemCallStagingSegments
