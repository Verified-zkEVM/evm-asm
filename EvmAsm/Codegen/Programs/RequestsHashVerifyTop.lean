/-
  EvmAsm.Codegen.Programs.RequestsHashVerifyTop

  The whole-routine triple for `requests_hash_verify` (#12206 item 2).

  The routine is an ordinary leaf ABI frame — `addi sp,-32` + three `sd`,
  a 27-instruction body, three `ld` + `addi sp,32` + `ret` — so the prologue
  and epilogue are discharged by `abiFrame_spec` and this module only has to
  prove the BODY, indices 4 → 31.

  Body chain (each address re-derived from the linked guest ELF):
    pc 4 → pc 7    three `mv`s: s0 := a6, s1 := a7, a6 := a7
    pc 7 → pc 8    `jal assemble_execution_requests`  — GENUINELY COMPOSED
                   against `assemble_execution_requests_spec_within` (#12813)
    pc 8 → pc 12   a1 := a0, a0 := s1, a2 := &rhv_hash
    pc 12 → pc 13  `jal execution_requests_hash`      — NAMED RESIDUAL
                   (`ErhCallShape`; see RequestsHashVerifyResidual)
    pc 13          `bnez a0` — the hash-failure split
    pc 14 → pc 18  t0 := &rhv_hash, t1 := s0, t2 := 32
    pc 18 → pc 31  the 32-byte comparison tail (RequestsHashVerifyCmp)
    pc 30 → pc 31  `li a0, 2`, the hash-failure verdict

  THE THREE EXIT CODES all appear in the post, through `rhvVerdict`:
    `a0 = 2` when the callee reported failure  (proved at pc 13/30 here)
    `a0 = 1` on a byte mismatch                (proved in `rhv_cmp_tail`)
    `a0 = 0` on a full 32-byte match           (proved in `rhv_cmp_tail`)
-/

import EvmAsm.Codegen.Programs.RequestsHashVerifyCmp
import EvmAsm.Codegen.Programs.RequestsHashVerifyResidual
import EvmAsm.Codegen.Programs.AssembleExecutionRequestsTop
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.RequestsHashVerifyTop

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.RequestsHashVerifyBase
open EvmAsm.Codegen.RequestsHashVerifyCmp
open EvmAsm.Codegen.RequestsHashVerifyResidual
-- NOT `open …AssembleExecutionRequestsBase`: it also defines `pc`/`B`, and an
-- ambiguous `pc` here would silently index the WRONG routine.
open EvmAsm.Codegen.AssembleExecutionRequestsHeader
  (BdPtrA BdLenA BePtrA BeLenA aerOff4)
open EvmAsm.Codegen.AssembleExecutionRequestsTail (aerTotal)
open EvmAsm.Codegen.AssembleExecutionRequestsTop
  (aerGateOk aerFuel aerSection assemble_execution_requests_spec_within)

set_option maxRecDepth 12000

local macro "pcfR" : tactic =>
  `(tactic| repeat' first
      | exact bytesRegion_pcFree _ _
      | exact pcFree_stackFree _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | apply pcFree_sepConj)

/-! ## The ABI frame decomposition -/

/-- The three callee-saved slots, read off 0x80054350/54/58 (`sd ra,0(sp)`,
    `sd s0,8(sp)`, `sd s1,16(sp)`) and 0x800543c8/cc/d0. -/
def rhvFrame : FrameDesc :=
  [(.x1, (0 : BitVec 12)), (.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12))]

/-- Indices 4–30: everything between the prologue and the epilogue. -/
def rhvBody : List Instr :=
  [ .MV .x8 .x16,
    .MV .x9 .x17,
    .MV .x16 .x17,
    .JAL .x1 (jalOff GuestAddrs.assemble_execution_requests
      (GuestAddrs.requests_hash_verify + 28)),
    .MV .x11 .x10,
    .MV .x10 .x9,
    .AUIPC .x12 (laHi GuestAddrs.rhv_hash (GuestAddrs.requests_hash_verify + 40)),
    .ADDI .x12 .x12 (laLo GuestAddrs.rhv_hash (GuestAddrs.requests_hash_verify + 40)),
    .JAL .x1 (jalOff GuestAddrs.execution_requests_hash
      (GuestAddrs.requests_hash_verify + 48)),
    .BNE .x10 .x0 (68 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.rhv_hash (GuestAddrs.requests_hash_verify + 56)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rhv_hash (GuestAddrs.requests_hash_verify + 56)),
    .MV .x6 .x8,
    .LI .x7 (32 : Word),
    .BEQ .x7 .x0 (32 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .LBU .x29 .x6 (0 : BitVec 12),
    .BNE .x28 .x29 (28 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word) ]

/-- Kernel-checked: the emitted routine IS the ABI-frame flatten of `rhvBody`
    over `rhvFrame` with `sp -= 32` / `sp += 32`. This is what lets
    `abiFrame_spec` discharge the prologue and epilogue. -/
theorem rhvProg_eq_abiFrame :
    rhvProgL = abiFrameProg (-32 : BitVec 12) (32 : BitVec 12) rhvFrame rhvBody := by
  simp only [rhvProgL, requestsHashVerify_prog, abiFrameProg, framePrologue,
    frameEpilogue, storeProg, loadProg, rhvFrame, rhvBody]
  rfl

/-! ## Address bridges (all `decide`d against the concrete linked layout) -/

private theorem la_rhv_hash_a2_hi :
    laHi GuestAddrs.rhv_hash (GuestAddrs.requests_hash_verify + 40) =
      Rv64.laHi (pc 10) RhvHash := by decide

private theorem la_rhv_hash_a2_lo :
    laLo GuestAddrs.rhv_hash (GuestAddrs.requests_hash_verify + 40) =
      Rv64.laLo (pc 10) RhvHash := by decide

private theorem la_rhv_hash_a2_range : laInRange (pc 10) RhvHash := by decide

private theorem la_rhv_hash_t0_hi :
    laHi GuestAddrs.rhv_hash (GuestAddrs.requests_hash_verify + 56) =
      Rv64.laHi (pc 14) RhvHash := by decide

private theorem la_rhv_hash_t0_lo :
    laLo GuestAddrs.rhv_hash (GuestAddrs.requests_hash_verify + 56) =
      Rv64.laLo (pc 14) RhvHash := by decide

private theorem la_rhv_hash_t0_range : laInRange (pc 14) RhvHash := by decide

private theorem pc_10_12 : (pc 10 : Word) + 8 = pc 12 := by
  have := pc_add 10 2; simpa using this

private theorem pc_14_16 : (pc 14 : Word) + 8 = pc 16 := by
  have := pc_add 14 2; simpa using this

/-! ## The three exit codes -/

/-- The routine's return value, as a function of the callee's status word and
    of whether the derived digest matched the expected hash.

    `2` hash call failed · `1` byte mismatch · `0` match — exactly the three
    `li a0, _` at 0x800543c4 / 0x800543bc / 0x800543b4. -/
def rhvVerdict (st : Word) (dig exp : List (BitVec 8)) : Word :=
  if st = 0 then (if dig = exp then (0 : Word) else (1 : Word)) else (2 : Word)

@[simp] theorem rhvVerdict_fail (st : Word) (h : st ≠ 0)
    (dig exp : List (BitVec 8)) : rhvVerdict st dig exp = 2 := by
  simp only [rhvVerdict, if_neg h]

@[simp] theorem rhvVerdict_ok (dig exp : List (BitVec 8)) :
    rhvVerdict 0 dig exp = (if dig = exp then (0 : Word) else (1 : Word)) := by
  simp only [rhvVerdict]; simp

/-! ## The two call sites -/

/-- **Index 7 (0x80054368): `jal ra, assemble_execution_requests`.**

    Generic in the callee's footprint so the concrete instantiation against
    `assemble_execution_requests_spec_within` happens exactly once, in
    `rhv_aer_call_composed`. -/
theorem rhv_aer_call {P Q : Assertion} (vOld : Word) (n : Nat) (hP : P.pcFree)
    (hcallee : cpsTripleWithin n AerB ((pc 7 : Word) + 4) rhvCode
        (((.x1 : Reg) ↦ᵣ ((pc 7 : Word) + 4)) ** P)
        (((.x1 : Reg) ↦ᵣ ((pc 7 : Word) + 4)) ** Q)) :
    cpsTripleWithin (1 + n) (pc 7) (pc 8) rhvCode
      (((.x1 : Reg) ↦ᵣ vOld) ** P)
      (((.x1 : Reg) ↦ᵣ (pc 8)) ** Q) := by
  have hc := callWithin_spec (cr := rhvCode) (P := P) (Q := Q)
    (pc 7) AerB vOld
    (jalOff GuestAddrs.assemble_execution_requests
      (GuestAddrs.requests_hash_verify + 28)) n
    pc_jal_aer
    (mem_at 7 _ (pc 7) rfl (by rw [rhvProgL_len]; norm_num) (by decide))
    hP hcallee
  rwa [pc_succ 7] at hc

/-- **Index 12 (0x8005437c): `jal ra, execution_requests_hash`.**

    Steps over the call from the named residual. Nothing about the callee is
    assumed here beyond what `ErhCallShape` states — and that shape leaves the
    digest and the status word abstract. -/
theorem rhv_erh_call
    (vOld sp0 secPtr secLenW outPtr st : Word)
    (sec outOld dig : List (BitVec 8))
    (fuel : Nat) (F : Assertion)
    (h_erh : ErhCallShape rhvCode (pc 12) vOld sp0 secPtr secLenW outPtr st
      sec outOld dig
      (jalOff GuestAddrs.execution_requests_hash
        (GuestAddrs.requests_hash_verify + 48)) fuel F) :
    cpsTripleWithin (1 + fuel) (pc 12) (pc 13) rhvCode
      (((.x1 ↦ᵣ vOld) **
        erhCallEntry sp0 secPtr secLenW outPtr sec outOld) ** F)
      (((.x1 ↦ᵣ (pc 13)) **
        erhCallReturn sp0 secPtr outPtr st sec dig) ** F) := by
  obtain ⟨_, hcall⟩ := h_erh
  rwa [pc_succ 12] at hcall

/-- Every computable side condition of the `execution_requests_hash` residual
    holds at the real call site: the `jal` reloc resolves to the callee's
    entry, the return address is even, and the `jal` really is in the emitted
    image. Only `F.pcFree` and the two length facts come from the caller.

    This is the non-vacuity guard on the residual — without it `ErhCallShape`
    could be unsatisfiable and the whole triple vacuous. -/
theorem erhCallSite_ok (outOld dig : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree) (hoo : outOld.length = 32) (hd : dig.length = 32) :
    ErhCallSiteOk rhvCode (pc 12) outOld dig
      (jalOff GuestAddrs.execution_requests_hash
        (GuestAddrs.requests_hash_verify + 48)) F :=
  ⟨hF, ra_erh_aligned, pc_jal_erh,
    mem_at 12 _ (pc 12) rfl (by rw [rhvProgL_len]; norm_num) (by decide),
    hoo, hd⟩

/-! ## The straight-line marshalling segments -/

/-- Indices 4–6 (0x8005435c/60/64): `s0 := a6`, `s1 := a7`, `a6 := a7`.

    This is where the caller's expected-hash pointer (`a6`) is parked in the
    callee-saved `s0` and the scratch section buffer (`a7`) becomes
    `assemble_execution_requests`'s `out` in `a6`. -/
theorem rhv_marshal_entry (v8 v9 expPtr secBuf : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 3 (pc 4) (pc 7) rhvCode
      ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x16 ↦ᵣ expPtr) ** (.x17 ↦ᵣ secBuf) ** F)
      ((.x8 ↦ᵣ expPtr) ** (.x9 ↦ᵣ secBuf) ** (.x16 ↦ᵣ secBuf) **
       (.x17 ↦ᵣ secBuf) ** F) := by
  have s4 := cpsTripleWithin_extend_code
    (mem_at 4 (.MV .x8 .x16) (pc 4) rfl (by rw [rhvProgL_len]; norm_num) (by decide))
    (mv_spec_gen_within .x8 .x16 expPtr v8 (pc 4) (by decide))
  rw [pc_succ 4] at s4
  have s4F := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ v9) ** (.x17 ↦ᵣ secBuf) ** F) (by pcfR; exact hF) s4
  have s5 := cpsTripleWithin_extend_code
    (mem_at 5 (.MV .x9 .x17) (pc 5) rfl (by rw [rhvProgL_len]; norm_num) (by decide))
    (mv_spec_gen_within .x9 .x17 secBuf v9 (pc 5) (by decide))
  rw [pc_succ 5] at s5
  have s5F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ expPtr) ** (.x16 ↦ᵣ expPtr) ** F) (by pcfR; exact hF) s5
  have s6 := cpsTripleWithin_extend_code
    (mem_at 6 (.MV .x16 .x17) (pc 6) rfl (by rw [rhvProgL_len]; norm_num) (by decide))
    (mv_spec_gen_within .x16 .x17 secBuf expPtr (pc 6) (by decide))
  rw [pc_succ 6] at s6
  have s6F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ expPtr) ** (.x9 ↦ᵣ secBuf) ** F) (by pcfR; exact hF) s6
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s4F s5F
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c0 s6F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-- Indices 8–11 (0x8005436c/70/74/78): `a1 := a0` (the section length that
    `assemble_execution_requests` returned), `a0 := s1` (the section buffer),
    `a2 := &rhv_hash` — the ABI for `execution_requests_hash`. -/
theorem rhv_marshal_erh (v10 v11 v12 secBuf : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (pc 8) (pc 12) rhvCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x9 ↦ᵣ secBuf) ** F)
      ((.x10 ↦ᵣ secBuf) ** (.x11 ↦ᵣ v10) ** (.x12 ↦ᵣ RhvHash) **
       (.x9 ↦ᵣ secBuf) ** F) := by
  have s8 := cpsTripleWithin_extend_code
    (mem_at 8 (.MV .x11 .x10) (pc 8) rfl (by rw [rhvProgL_len]; norm_num) (by decide))
    (mv_spec_gen_within .x11 .x10 v10 v11 (pc 8) (by decide))
  rw [pc_succ 8] at s8
  have s8F := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ v12) ** (.x9 ↦ᵣ secBuf) ** F) (by pcfR; exact hF) s8
  have s9 := cpsTripleWithin_extend_code
    (mem_at 9 (.MV .x10 .x9) (pc 9) rfl (by rw [rhvProgL_len]; norm_num) (by decide))
    (mv_spec_gen_within .x10 .x9 secBuf v10 (pc 9) (by decide))
  rw [pc_succ 9] at s9
  have s9F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v10) ** (.x12 ↦ᵣ v12) ** F) (by pcfR; exact hF) s9
  have sla := la_materialize_within (cr := rhvCode) .x12 v12 (pc 10) RhvHash
    (by decide) la_rhv_hash_a2_range
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 10)
          (.AUIPC .x12 (laHi GuestAddrs.rhv_hash
            (GuestAddrs.requests_hash_verify + 40))) a = some i := by
        rw [la_rhv_hash_a2_hi]; exact hs
      exact mem_at 10 _ (pc 10) rfl (by rw [rhvProgL_len]; norm_num) (by decide) a i hs')
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 11)
          (.ADDI .x12 .x12 (laLo GuestAddrs.rhv_hash
            (GuestAddrs.requests_hash_verify + 40))) a = some i := by
        rw [la_rhv_hash_a2_lo, ← pc_succ 10]; exact hs
      exact mem_at 11 _ (pc 11) rfl (by rw [rhvProgL_len]; norm_num) (by decide) a i hs')
  rw [pc_10_12] at sla
  have slaF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ secBuf) ** (.x11 ↦ᵣ v10) ** (.x9 ↦ᵣ secBuf) ** F)
    (by pcfR; exact hF) sla
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s8F s9F
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c0 slaF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-- Indices 14–17 (0x80054384/88/8c/90): `t0 := &rhv_hash`, `t1 := s0`,
    `t2 := 32` — the two cursors and the byte counter of the compare loop.

    `t2 := 32` is `li t2, 32` at 0x80054390, which is why the top-tested
    `beqz t2` at 0x80054394 never fires on the first iteration. -/
theorem rhv_cmp_setup (v5 v6 v7 expPtr : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (pc 14) (pc 18) rhvCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x8 ↦ᵣ expPtr) ** F)
      ((.x5 ↦ᵣ RhvHash) ** (.x6 ↦ᵣ expPtr) ** (.x7 ↦ᵣ (32 : Word)) **
       (.x8 ↦ᵣ expPtr) ** F) := by
  have sla := la_materialize_within (cr := rhvCode) .x5 v5 (pc 14) RhvHash
    (by decide) la_rhv_hash_t0_range
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 14)
          (.AUIPC .x5 (laHi GuestAddrs.rhv_hash
            (GuestAddrs.requests_hash_verify + 56))) a = some i := by
        rw [la_rhv_hash_t0_hi]; exact hs
      exact mem_at 14 _ (pc 14) rfl (by rw [rhvProgL_len]; norm_num) (by decide) a i hs')
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 15)
          (.ADDI .x5 .x5 (laLo GuestAddrs.rhv_hash
            (GuestAddrs.requests_hash_verify + 56))) a = some i := by
        rw [la_rhv_hash_t0_lo, ← pc_succ 14]; exact hs
      exact mem_at 15 _ (pc 15) rfl (by rw [rhvProgL_len]; norm_num) (by decide) a i hs')
  rw [pc_14_16] at sla
  have slaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x8 ↦ᵣ expPtr) ** F)
    (by pcfR; exact hF) sla
  have s16 := cpsTripleWithin_extend_code
    (mem_at 16 (.MV .x6 .x8) (pc 16) rfl (by rw [rhvProgL_len]; norm_num) (by decide))
    (mv_spec_gen_within .x6 .x8 expPtr v6 (pc 16) (by decide))
  rw [pc_succ 16] at s16
  have s16F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ RhvHash) ** (.x7 ↦ᵣ v7) ** F) (by pcfR; exact hF) s16
  have s17 := cpsTripleWithin_extend_code
    (mem_at 17 (.LI .x7 (32 : Word)) (pc 17) rfl
      (by rw [rhvProgL_len]; norm_num) (by decide))
    (li_spec_gen_within .x7 v7 (32 : Word) (pc 17) (by decide))
  rw [pc_succ 17] at s17
  have s17F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ RhvHash) ** (.x6 ↦ᵣ expPtr) ** (.x8 ↦ᵣ expPtr) ** F)
    (by pcfR; exact hF) s17
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) slaF s16F
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c0 s17F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-! ## The hash-failure split (index 13) and its verdict (index 30) -/

/-- `bnez a0, +68` at 0x80054380, status word zero: falls through to the
    comparison setup at index 14. -/
theorem rhv_status_branch_ok (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 13) (pc 14) rhvCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  have hbr0 := bne_spec_gen_within .x10 .x0 (68 : BitVec 13)
    (0 : Word) (0 : Word) (pc 13)
  rw [pc_bne_hashfail, show (pc 13 : Word) + 4 = pc 14 from pc_succ 13] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (mem_at 13 (.BNE .x10 .x0 (68 : BitVec 13)) (pc 13) rfl
      (by rw [rhvProgL_len]; norm_num) (by decide)) hbr0
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 rfl)
  have hntF := cpsTripleWithin_frameR F hF hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hntF

/-- `bnez a0, +68` at 0x80054380, non-zero status word: jumps to the
    `li a0, 2` hash-failure verdict at index 30 (0x800543c4). -/
theorem rhv_status_branch_fail (st : Word) (hst : st ≠ 0)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 13) (pc 30) rhvCode
      ((.x10 ↦ᵣ st) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ st) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  have hbr0 := bne_spec_gen_within .x10 .x0 (68 : BitVec 13)
    st (0 : Word) (pc 13)
  rw [pc_bne_hashfail, show (pc 13 : Word) + 4 = pc 14 from pc_succ 13] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (mem_at 13 (.BNE .x10 .x0 (68 : BitVec 13)) (pc 13) rfl
      (by rw [rhvProgL_len]; norm_num) (by decide)) hbr0
  have ht := cpsBranchWithin_takenStripPure2 hbr
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact hst ((sepConj_pure_right _).1 hQ).2)
  have htF := cpsTripleWithin_frameR F hF ht
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) htF

/-- Index 30 (0x800543c4): `li a0, 2`, then FALL THROUGH into the epilogue at
    index 31 — there is no jump here, the hash-failure arm is the last thing
    before the restore sequence. -/
theorem rhv_hashfail_verdict (v10 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 30) (pc 31) rhvCode
      ((.x10 ↦ᵣ v10) ** F)
      ((.x10 ↦ᵣ (2 : Word)) ** F) := by
  have s30 := cpsTripleWithin_extend_code
    (mem_at 30 (.LI .x10 (2 : Word)) (pc 30) rfl
      (by rw [rhvProgL_len]; norm_num) (by decide))
    (li_spec_gen_within .x10 v10 (2 : Word) (pc 30) (by decide))
  rw [pc_succ 30] at s30
  exact cpsTripleWithin_frameR F hF s30

/-- `rhv_cmp_setup` with `t0`/`t1`/`t2` merely OWNED on entry — which is how
    they come back from `execution_requests_hash` (they are in `erhScratchOwn`,
    not pinned). -/
theorem rhv_cmp_setup_own (expPtr : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (pc 14) (pc 18) rhvCode
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x8 ↦ᵣ expPtr) ** F)
      ((.x5 ↦ᵣ RhvHash) ** (.x6 ↦ᵣ expPtr) ** (.x7 ↦ᵣ (32 : Word)) **
       (.x8 ↦ᵣ expPtr) ** F) := by
  have h5 : ∀ v5, cpsTripleWithin 4 (pc 14) (pc 18) rhvCode
      ((regOwn .x6 ** regOwn .x7 ** (.x8 ↦ᵣ expPtr) ** F) ** (.x5 ↦ᵣ v5))
      ((.x5 ↦ᵣ RhvHash) ** (.x6 ↦ᵣ expPtr) ** (.x7 ↦ᵣ (32 : Word)) **
       (.x8 ↦ᵣ expPtr) ** F) := by
    intro v5
    have h6 : ∀ v6, cpsTripleWithin 4 (pc 14) (pc 18) rhvCode
        ((regOwn .x7 ** (.x8 ↦ᵣ expPtr) ** F ** (.x5 ↦ᵣ v5)) ** (.x6 ↦ᵣ v6))
        ((.x5 ↦ᵣ RhvHash) ** (.x6 ↦ᵣ expPtr) ** (.x7 ↦ᵣ (32 : Word)) **
         (.x8 ↦ᵣ expPtr) ** F) := by
      intro v6
      have h7 : ∀ v7, cpsTripleWithin 4 (pc 14) (pc 18) rhvCode
          (((.x8 ↦ᵣ expPtr) ** F ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6)) ** (.x7 ↦ᵣ v7))
          ((.x5 ↦ᵣ RhvHash) ** (.x6 ↦ᵣ expPtr) ** (.x7 ↦ᵣ (32 : Word)) **
           (.x8 ↦ᵣ expPtr) ** F) := by
        intro v7
        exact cpsTripleWithin_weaken
          (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
          (rhv_cmp_setup v5 v6 v7 expPtr F hF)
      exact cpsTripleWithin_weaken
        (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
        (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7) h7)
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6) h6)
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5) h5)

/-! ## Composing the `assemble_execution_requests` contract

    Everything below transcribes `assemble_execution_requests_spec_within`
    (#12813, `AssembleExecutionRequestsTop`) with the `x1` atom factored out,
    which is the shape `callWithin_spec` consumes. The callee's own ambient
    parameter `A` is where `requests_hash_verify`'s private resources ride
    across the call, so no separate frame is needed. -/

private theorem aerPc0 : AssembleExecutionRequestsBase.pc 0 = AerB := by
  unfold AssembleExecutionRequestsBase.pc AerB
  decide

/-- `assemble_execution_requests`'s precondition, minus `ra`. -/
def aerFoot (secBuf dp dl wp wl cp cl bdp bdl bep bel v5 v6 v7 v28 : Word)
    (dep wdb cns bdb beb ob : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
  (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) ** (.x16 ↦ᵣ secBuf) **
  bytesRegion secBuf ob ** (BdLenA ↦ₘ bdl) **
  (.x0 ↦ᵣ (0 : Word)) ** regOwn .x29 **
  bytesRegion dp dep ** bytesRegion wp wdb ** bytesRegion cp cns **
  bytesRegion bdp bdb ** bytesRegion bep beb **
  (.x10 ↦ᵣ dp) ** (.x12 ↦ᵣ wp) ** (.x14 ↦ᵣ cp) **
  (BdPtrA ↦ₘ bdp) ** (BePtrA ↦ₘ bep) ** (BeLenA ↦ₘ bel) ** A

/-- `assemble_execution_requests`'s postcondition, minus `ra`. -/
def aerFootPost (secBuf dp dl wp wl cp cl bdp bdl bep bel : Word) (ntot : Nat)
    (dep wdb cns bdb beb ob : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x10 ↦ᵣ (aerTotal dl wl cl bdl bel)) **
  (.x7 ↦ᵣ BeLenA) ** (.x28 ↦ᵣ bel) **
  (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) **
  (BdLenA ↦ₘ bdl) ** (BeLenA ↦ₘ bel) **
  (.x6 ↦ᵣ (secBuf + BitVec.ofNat 64 ntot)) ** (.x0 ↦ᵣ (0 : Word)) **
  regOwn .x29 **
  bytesRegion secBuf (aerSection ob dl wl cl bdl dep wdb cns bdb beb) **
  bytesRegion dp dep ** bytesRegion wp wdb ** bytesRegion cp cns **
  bytesRegion bdp bdb ** bytesRegion bep beb **
  (.x5 ↦ᵣ (aerOff4 dl wl cl bdl)) ** (.x12 ↦ᵣ wp) ** (.x14 ↦ᵣ cp) **
  (.x16 ↦ᵣ secBuf) ** (BdPtrA ↦ₘ bdp) ** (BePtrA ↦ₘ bep) ** A

theorem aerFoot_pcFree (secBuf dp dl wp wl cp cl bdp bdl bep bel v5 v6 v7 v28 : Word)
    (dep wdb cns bdb beb ob : List (BitVec 8)) (A : Assertion) (hA : A.pcFree) :
    (aerFoot secBuf dp dl wp wl cp cl bdp bdl bep bel v5 v6 v7 v28
      dep wdb cns bdb beb ob A).pcFree := by
  unfold aerFoot; pcfR; exact hA

theorem aerFootPost_pcFree (secBuf dp dl wp wl cp cl bdp bdl bep bel : Word)
    (ntot : Nat) (dep wdb cns bdb beb ob : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree) :
    (aerFootPost secBuf dp dl wp wl cp cl bdp bdl bep bel ntot
      dep wdb cns bdb beb ob A).pcFree := by
  unfold aerFootPost; pcfR; exact hA

/-- **Index 7 composed against the real callee contract.**

    This is a genuine composition, not an assumption: the only inputs are
    `assemble_execution_requests_spec_within` and this routine's own code
    membership. -/
theorem rhv_aer_call_composed
    (secBuf dp dl wp wl cp cl bdp bdl bep bel v5 v6 v7 v28 vOld : Word)
    (dep wdb cns bdb beb ob : List (BitVec 8)) (ntot : Nat)
    (hntot : ntot = 20 + dep.length + wdb.length + cns.length + bdb.length + beb.length)
    (hdl : dl = BitVec.ofNat 64 dep.length)
    (hwl : wl = BitVec.ofNat 64 wdb.length)
    (hcl : cl = BitVec.ofNat 64 cns.length)
    (hbdl : bdl = BitVec.ofNat 64 bdb.length)
    (hbel : bel = BitVec.ofNat 64 beb.length)
    (hGate : aerGateOk secBuf dp wp cp bdp bep dep wdb cns bdb beb ob)
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin (1 + aerFuel (ntot - 20)) (pc 7) (pc 8) rhvCode
      ((.x1 ↦ᵣ vOld) **
        aerFoot secBuf dp dl wp wl cp cl bdp bdl bep bel v5 v6 v7 v28
          dep wdb cns bdb beb ob A)
      ((.x1 ↦ᵣ (pc 8)) **
        aerFootPost secBuf dp dl wp wl cp cl bdp bdl bep bel ntot
          dep wdb cns bdb beb ob A) := by
  have h0 := assemble_execution_requests_spec_within secBuf ((pc 7 : Word) + 4)
    dp dl wp wl cp cl bdp bdl bep bel v5 v6 v7 v28 dep wdb cns bdb beb ob ntot
    hntot hdl hwl hcl hbdl hbel hGate A hA
  rw [ra_aer_aligned, aerPc0] at h0
  have h1 := cpsTripleWithin_extend_code aer_sub_rhvCode h0
  have h2 : cpsTripleWithin (aerFuel (ntot - 20)) AerB ((pc 7 : Word) + 4) rhvCode
      (((.x1 : Reg) ↦ᵣ ((pc 7 : Word) + 4)) **
        aerFoot secBuf dp dl wp wl cp cl bdp bdl bep bel v5 v6 v7 v28
          dep wdb cns bdb beb ob A)
      (((.x1 : Reg) ↦ᵣ ((pc 7 : Word) + 4)) **
        aerFootPost secBuf dp dl wp wl cp cl bdp bdl bep bel ntot
          dep wdb cns bdb beb ob A) :=
    cpsTripleWithin_weaken
      (fun _ hp => by simp only [aerFoot] at hp; xperm_chunked hp)
      (fun _ hq => by simp only [aerFootPost]; xperm_chunked hq) h1
  exact rhv_aer_call vOld (aerFuel (ntot - 20))
    (aerFoot_pcFree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A hA) h2

/-! ## The body, indices 4 → 31 -/

/-- Everything live across index 4–7 that the three `mv`s do not touch. -/
def rhvF1 (newSp ret v5 v6 v7 v28 expPtr secBuf
    dp dl wp wl cp cl bdp bdl bep bel : Word)
    (dep wdb cns bdb beb ob rhvOld exp : List (BitVec 8))
    (vals : Reg → Word) (A : Assertion) : Assertion :=
  (.x1 ↦ᵣ ret) **
  (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
  (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) **
  bytesRegion secBuf ob ** (BdLenA ↦ₘ bdl) **
  (.x0 ↦ᵣ (0 : Word)) ** regOwn .x29 **
  bytesRegion dp dep ** bytesRegion wp wdb ** bytesRegion cp cns **
  bytesRegion bdp bdb ** bytesRegion bep beb **
  (.x10 ↦ᵣ dp) ** (.x12 ↦ᵣ wp) ** (.x14 ↦ᵣ cp) **
  (BdPtrA ↦ₘ bdp) ** (BePtrA ↦ₘ bep) ** (BeLenA ↦ₘ bel) **
  (.x2 ↦ᵣ newSp) ** frameSlotsSaved rhvFrame newSp vals **
  stackFree newSp erhStackDwords **
  bytesRegion RhvHash rhvOld ** bytesRegion expPtr exp **
  regOwn .x30 ** regOwn .x31 ** A

/-- `requests_hash_verify`'s private resources, threaded as
    `assemble_execution_requests`'s ambient across its call. Every atom is one
    the callee's contract does not mention: the stack pointer and the three
    frame slots it saved (0x80054350/54/58), the free stack the SECOND callee
    frames from, both 32-byte hash regions, the callee-saved `s0`/`s1` holding
    the caller's two pointers, the dead `a7`, and `x30`/`x31`. -/
def rhvAerAmb (newSp expPtr secBuf : Word) (rhvOld exp : List (BitVec 8))
    (vals : Reg → Word) (A : Assertion) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ expPtr) ** (.x9 ↦ᵣ secBuf) ** (.x17 ↦ᵣ secBuf) **
  frameSlotsSaved rhvFrame newSp vals **
  stackFree newSp erhStackDwords **
  bytesRegion RhvHash rhvOld ** bytesRegion expPtr exp **
  regOwn .x30 ** regOwn .x31 ** A

/-- Resources `execution_requests_hash` neither reads nor writes. `s0`/`s1`
    are NOT here: they are named explicitly at the call site, because
    `requests_hash_verify` still needs them afterwards. -/
def rhvErhFrame (newSp expPtr dp wp cp bdp bdl bep bel : Word)
    (dep wdb cns bdb beb exp : List (BitVec 8))
    (vals : Reg → Word) (A : Assertion) : Assertion :=
  frameSlotsSaved rhvFrame newSp vals **
  bytesRegion expPtr exp **
  bytesRegion dp dep ** bytesRegion wp wdb ** bytesRegion cp cns **
  bytesRegion bdp bdb ** bytesRegion bep beb **
  (BdPtrA ↦ₘ bdp) ** (BdLenA ↦ₘ bdl) ** (BePtrA ↦ₘ bep) **
  (BeLenA ↦ₘ bel) ** A

/-- Body entry state at index 4: the callee's ABI inputs are already in
    `a0`–`a5`, but `a6` still holds the caller's expected-hash pointer and
    `s0`/`s1` still hold whatever the caller left there. -/
def rhvBodyPre (newSp ret v8 v9 v5 v6 v7 v28 expPtr secBuf
    dp dl wp wl cp cl bdp bdl bep bel : Word)
    (dep wdb cns bdb beb ob rhvOld exp : List (BitVec 8))
    (vals : Reg → Word) (A : Assertion) : Assertion :=
  (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x16 ↦ᵣ expPtr) ** (.x17 ↦ᵣ secBuf) **
  rhvF1 newSp ret v5 v6 v7 v28 expPtr secBuf
    dp dl wp wl cp cl bdp bdl bep bel dep wdb cns bdb beb ob rhvOld exp vals A

/-- Body exit state at index 31: `a0` carries the verdict, `s0`/`s1` carry the
    two pointers, and every caller-saved register is merely owned. -/
def rhvBodyPost (newSp secBuf expPtr st dl wl cl bdl bel
    dp wp cp bdp bep : Word)
    (dep wdb cns bdb beb ob dig exp : List (BitVec 8))
    (vals : Reg → Word) (A : Assertion) : Assertion :=
  (.x10 ↦ᵣ rhvVerdict st dig exp) **
  (.x1 ↦ᵣ (pc 13)) ** (.x8 ↦ᵣ expPtr) ** (.x9 ↦ᵣ secBuf) **
  (.x2 ↦ᵣ newSp) ** (.x0 ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
  regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  stackFree newSp erhStackDwords **
  frameSlotsSaved rhvFrame newSp vals **
  bytesRegion secBuf (aerSection ob dl wl cl bdl dep wdb cns bdb beb) **
  bytesRegion RhvHash dig ** bytesRegion expPtr exp **
  bytesRegion dp dep ** bytesRegion wp wdb ** bytesRegion cp cns **
  bytesRegion bdp bdb ** bytesRegion bep beb **
  (BdPtrA ↦ₘ bdp) ** (BdLenA ↦ₘ bdl) ** (BePtrA ↦ₘ bep) **
  (BeLenA ↦ₘ bel) ** A

/-- Body step budget: three `mv`s, the composed call, four marshalling steps,
    the residual call, the status branch, then the longer of the two arms
    (setup + the 32-byte compare, `4 + 260`). -/
def rhvBodyFuel (bodyBytes erhFuel : Nat) : Nat :=
  274 + aerFuel bodyBytes + erhFuel

/-! ## The routine's resource gate -/

/-- The `rhv_hash` BSS region's half of the comparison gate is a FACT, not a
    hypothesis: 0xb9e02d08 is dword-aligned and 0xb9e02d08 + 32 sits below the
    guest's byte-access validity bound. Kernel-checked here so the routine's
    stated gate only ever constrains the CALLER's buffer. -/
theorem rhvHash_gate :
    RhvHash.toNat % 8 = 0 ∧ RhvHash.toNat + 32 < 2 ^ 64 ∧
    (∀ i, i < 32 → isValidByteAccess (RhvHash + BitVec.ofNat 64 i) = true) := by
  refine ⟨by decide, by decide, ?_⟩
  decide

/-- **The routine's resource gate.** Only the caller's expected-hash buffer:
    32 bytes, dword aligned, not wrapping, every byte a valid access — plus
    the digest length the residual already guarantees.

    `rhv_gate_reachable` exhibits a satisfying instance;
    `rhv_gate_unaligned` and `rhv_gate_short_expected` are negative controls
    where the bundle is provably FALSE. -/
def rhvGateOk (expPtr : Word) (dig exp : List (BitVec 8)) : Prop :=
  dig.length = 32 ∧ exp.length = 32 ∧
  expPtr.toNat % 8 = 0 ∧ expPtr.toNat + 32 < 2 ^ 64 ∧
  (∀ i, i < 32 → isValidByteAccess (expPtr + BitVec.ofNat 64 i) = true)

theorem cmpGate_of_rhvGate (expPtr : Word) (dig exp : List (BitVec 8))
    (h : rhvGateOk expPtr dig exp) : cmpGateOk RhvHash expPtr dig exp := by
  obtain ⟨hd, he, ha, ho, hv⟩ := h
  obtain ⟨ra, ro, rv⟩ := rhvHash_gate
  exact ⟨hd, he, ra, ha, ro, ho, rv, hv⟩

/-! ## The body chain -/

/-- Every caller-saved register `execution_requests_hash` may clobber, weakened
    from the concrete values `assemble_execution_requests` left in them. -/
private theorem erhScratch_of_regIs (a b c d e f g i j : Word) :
    ∀ h, ((((.x5 : Reg) ↦ᵣ a) ** ((.x6 : Reg) ↦ᵣ b) ** ((.x7 : Reg) ↦ᵣ c) **
          ((.x13 : Reg) ↦ᵣ d) ** ((.x14 : Reg) ↦ᵣ e) ** ((.x15 : Reg) ↦ᵣ f) **
          ((.x16 : Reg) ↦ᵣ g) ** ((.x17 : Reg) ↦ᵣ i) ** ((.x28 : Reg) ↦ᵣ j) **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31) h) →
        erhScratchOwn h := by
  intro h hp
  unfold erhScratchOwn
  exact sepConj_mono (regIs_implies_regOwn .x5)
    (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7)
        (sepConj_mono (regIs_implies_regOwn .x13)
          (sepConj_mono (regIs_implies_regOwn .x14)
            (sepConj_mono (regIs_implies_regOwn .x15)
              (sepConj_mono (regIs_implies_regOwn .x16)
                (sepConj_mono (regIs_implies_regOwn .x17)
                  (sepConj_mono (regIs_implies_regOwn .x28)
                    (fun _ hx => hx))))))))) h hp

private theorem addr_zero (w : Word) : w + BitVec.ofNat 64 0 = w := by bv_omega

/-- Everything live across indices 8–11 that the marshalling does not touch. -/
def rhvF3 (newSp secBuf expPtr dl wl cl bdl bel dp wp cp bdp bep : Word)
    (ntot : Nat)
    (dep wdb cns bdb beb ob rhvOld exp : List (BitVec 8))
    (vals : Reg → Word) (A : Assertion) : Assertion :=
  (.x1 ↦ᵣ (pc 8)) **
  (.x7 ↦ᵣ BeLenA) ** (.x28 ↦ᵣ bel) **
  (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) **
  (BdLenA ↦ₘ bdl) ** (BeLenA ↦ₘ bel) **
  (.x6 ↦ᵣ (secBuf + BitVec.ofNat 64 ntot)) ** (.x0 ↦ᵣ (0 : Word)) **
  regOwn .x29 **
  bytesRegion secBuf (aerSection ob dl wl cl bdl dep wdb cns bdb beb) **
  bytesRegion dp dep ** bytesRegion wp wdb ** bytesRegion cp cns **
  bytesRegion bdp bdb ** bytesRegion bep beb **
  (.x5 ↦ᵣ (aerOff4 dl wl cl bdl)) ** (.x14 ↦ᵣ cp) **
  (.x16 ↦ᵣ secBuf) ** (BdPtrA ↦ₘ bdp) ** (BePtrA ↦ₘ bep) **
  (.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ expPtr) ** (.x17 ↦ᵣ secBuf) **
  frameSlotsSaved rhvFrame newSp vals **
  stackFree newSp erhStackDwords **
  bytesRegion RhvHash rhvOld ** bytesRegion expPtr exp **
  regOwn .x30 ** regOwn .x31 ** A

/-- `rhv_marshal_erh`, additionally weakening the nine caller-saved registers
    that `assemble_execution_requests` left pinned into the owned form
    `execution_requests_hash`'s footprint asks for. Doing the weakening inside
    a segment keeps it away from the 35-atom junction assertions. -/
theorem rhv_marshal_erh_own (v10 v11 v12 secBuf a b c d e f g i j : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (pc 8) (pc 12) rhvCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x9 ↦ᵣ secBuf) **
       (((.x5 ↦ᵣ a) ** (.x6 ↦ᵣ b) ** (.x7 ↦ᵣ c) **
         (.x13 ↦ᵣ d) ** (.x14 ↦ᵣ e) ** (.x15 ↦ᵣ f) **
         (.x16 ↦ᵣ g) ** (.x17 ↦ᵣ i) ** (.x28 ↦ᵣ j) **
         regOwn .x29 ** regOwn .x30 ** regOwn .x31) ** F))
      ((.x10 ↦ᵣ secBuf) ** (.x11 ↦ᵣ v10) ** (.x12 ↦ᵣ RhvHash) **
       (.x9 ↦ᵣ secBuf) ** (erhScratchOwn ** F)) := by
  have base := rhv_marshal_erh v10 v11 v12 secBuf
    (((.x5 ↦ᵣ a) ** (.x6 ↦ᵣ b) ** (.x7 ↦ᵣ c) **
      (.x13 ↦ᵣ d) ** (.x14 ↦ᵣ e) ** (.x15 ↦ᵣ f) **
      (.x16 ↦ᵣ g) ** (.x17 ↦ᵣ i) ** (.x28 ↦ᵣ j) **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31) ** F)
    (by pcfR; exact hF)
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) base
  exact sepConj_mono (fun _ hx => hx)
    (sepConj_mono (fun _ hx => hx)
      (sepConj_mono (fun _ hx => hx)
        (sepConj_mono (fun _ hx => hx)
          (sepConj_mono (erhScratch_of_regIs a b c d e f g i j)
            (fun _ hx => hx))))) h hq

/-- Frame across the comparison arm: everything the compare loop does not own.
    `s0` is deliberately NOT here — `rhv_cmp_setup_own` names it explicitly,
    because index 16 (0x8005438c `mv t1, s0`) reads it. -/
def rhvCmpFrame (newSp secBuf dl wl cl bdl bel dp wp cp bdp bep : Word)
    (dep wdb cns bdb beb ob : List (BitVec 8))
    (vals : Reg → Word) (A : Assertion) : Assertion :=
  (.x1 ↦ᵣ (pc 13)) ** (.x2 ↦ᵣ newSp) ** stackFree newSp erhStackDwords **
  regOwn .x11 ** regOwn .x12 **
  regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x30 ** regOwn .x31 **
  bytesRegion secBuf (aerSection ob dl wl cl bdl dep wdb cns bdb beb) **
  (.x9 ↦ᵣ secBuf) ** frameSlotsSaved rhvFrame newSp vals **
  bytesRegion dp dep ** bytesRegion wp wdb ** bytesRegion cp cns **
  bytesRegion bdp bdb ** bytesRegion bep beb **
  (BdPtrA ↦ₘ bdp) ** (BdLenA ↦ₘ bdl) ** (BePtrA ↦ₘ bep) **
  (BeLenA ↦ₘ bel) ** A

theorem rhvCmpFrame_pcFree (newSp secBuf dl wl cl bdl bel dp wp cp bdp bep : Word)
    (dep wdb cns bdb beb ob : List (BitVec 8))
    (vals : Reg → Word) (A : Assertion) (hA : A.pcFree) :
    (rhvCmpFrame newSp secBuf dl wl cl bdl bel dp wp cp bdp bep
      dep wdb cns bdb beb ob vals A).pcFree := by
  unfold rhvCmpFrame; pcfR; exact hA

/-- `rhv_status_branch_ok` with `a0` already weakened to owned — the shape the
    comparison tail wants, and weakening it here keeps the junction between the
    branch and the setup a pure permutation. -/
theorem rhv_status_branch_ok_own (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 13) (pc 14) rhvCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      (regOwn .x10 ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_)
    (rhv_status_branch_ok F hF)
  exact sepConj_mono (regIs_implies_regOwn (v := (0 : Word)) .x10)
    (fun _ hx => hx) h hq

/-- Frame at the status branch (index 13): everything except `a0` and `x0`. -/
def rhvBranchF (newSp secBuf expPtr dl wl cl bdl bel dp wp cp bdp bep : Word)
    (dep wdb cns bdb beb ob dig exp : List (BitVec 8))
    (vals : Reg → Word) (A : Assertion) : Assertion :=
  (.x1 ↦ᵣ (pc 13)) ** (.x2 ↦ᵣ newSp) ** stackFree newSp erhStackDwords **
  regOwn .x11 ** regOwn .x12 ** erhScratchOwn **
  bytesRegion secBuf (aerSection ob dl wl cl bdl dep wdb cns bdb beb) **
  bytesRegion RhvHash dig ** bytesRegion expPtr exp **
  (.x8 ↦ᵣ expPtr) ** (.x9 ↦ᵣ secBuf) **
  frameSlotsSaved rhvFrame newSp vals **
  bytesRegion dp dep ** bytesRegion wp wdb ** bytesRegion cp cns **
  bytesRegion bdp bdb ** bytesRegion bep beb **
  (BdPtrA ↦ₘ bdp) ** (BdLenA ↦ₘ bdl) ** (BePtrA ↦ₘ bep) **
  (BeLenA ↦ₘ bel) ** A

theorem rhvBranchF_pcFree (newSp secBuf expPtr dl wl cl bdl bel dp wp cp bdp bep : Word)
    (dep wdb cns bdb beb ob dig exp : List (BitVec 8))
    (vals : Reg → Word) (A : Assertion) (hA : A.pcFree) :
    (rhvBranchF newSp secBuf expPtr dl wl cl bdl bel dp wp cp bdp bep
      dep wdb cns bdb beb ob dig exp vals A).pcFree := by
  unfold rhvBranchF; pcfR; exact hA

/-- **The body of `requests_hash_verify`, indices 4 → 31.**

    One callee is COMPOSED (`assemble_execution_requests`, via
    `rhv_aer_call_composed`); the other is a NAMED RESIDUAL (`h_erh`). All three
    exit codes are produced here: `2` on the `bnez` at index 13, `1` and `0`
    from the comparison tail. -/
theorem rhv_body
    (newSp ret v8 v9 v5 v6 v7 v28 expPtr secBuf
     dp dl wp wl cp cl bdp bdl bep bel st : Word)
    (dep wdb cns bdb beb ob rhvOld exp dig : List (BitVec 8))
    (ntot erhFuel : Nat)
    (hntot : ntot = 20 + dep.length + wdb.length + cns.length + bdb.length + beb.length)
    (hdl : dl = BitVec.ofNat 64 dep.length)
    (hwl : wl = BitVec.ofNat 64 wdb.length)
    (hcl : cl = BitVec.ofNat 64 cns.length)
    (hbdl : bdl = BitVec.ofNat 64 bdb.length)
    (hbel : bel = BitVec.ofNat 64 beb.length)
    (hAer : aerGateOk secBuf dp wp cp bdp bep dep wdb cns bdb beb ob)
    (hGate : rhvGateOk expPtr dig exp)
    (vals : Reg → Word) (A : Assertion) (hA : A.pcFree)
    (h_erh : ErhCallShape rhvCode (pc 12) (pc 8) newSp secBuf
      (aerTotal dl wl cl bdl bel) RhvHash st
      (aerSection ob dl wl cl bdl dep wdb cns bdb beb) rhvOld dig
      (jalOff GuestAddrs.execution_requests_hash
        (GuestAddrs.requests_hash_verify + 48)) erhFuel
      ((.x8 ↦ᵣ expPtr) ** (.x9 ↦ᵣ secBuf) **
        rhvErhFrame newSp expPtr dp wp cp bdp bdl bep bel
          dep wdb cns bdb beb exp vals A)) :
    cpsTripleWithin (rhvBodyFuel (ntot - 20) erhFuel) (pc 4) (pc 31) rhvCode
      (rhvBodyPre newSp ret v8 v9 v5 v6 v7 v28 expPtr secBuf
        dp dl wp wl cp cl bdp bdl bep bel
        dep wdb cns bdb beb ob rhvOld exp vals A)
      (rhvBodyPost newSp secBuf expPtr st dl wl cl bdl bel dp wp cp bdp bep
        dep wdb cns bdb beb ob dig exp vals A) := by
  have hF1 : (rhvF1 newSp ret v5 v6 v7 v28 expPtr secBuf
      dp dl wp wl cp cl bdp bdl bep bel
      dep wdb cns bdb beb ob rhvOld exp vals A).pcFree := by
    unfold rhvF1; pcfR; exact hA
  have hAmb : (rhvAerAmb newSp expPtr secBuf rhvOld exp vals A).pcFree := by
    unfold rhvAerAmb; pcfR; exact hA
  have hF3 : (rhvF3 newSp secBuf expPtr dl wl cl bdl bel dp wp cp bdp bep ntot
      dep wdb cns bdb beb ob rhvOld exp vals A).pcFree := by
    unfold rhvF3; pcfR; exact hA
  have hEF : (rhvErhFrame newSp expPtr dp wp cp bdp bdl bep bel
      dep wdb cns bdb beb exp vals A).pcFree := by
    unfold rhvErhFrame; pcfR; exact hA
  have hBF := rhvBranchF_pcFree newSp secBuf expPtr dl wl cl bdl bel
    dp wp cp bdp bep dep wdb cns bdb beb ob dig exp vals A hA
  have hCF := rhvCmpFrame_pcFree newSp secBuf dl wl cl bdl bel dp wp cp bdp bep
    dep wdb cns bdb beb ob vals A hA
  -- indices 4-6, then the composed call at index 7
  have s1 := rhv_marshal_entry v8 v9 expPtr secBuf _ hF1
  have s2 := rhv_aer_call_composed secBuf dp dl wp wl cp cl bdp bdl bep bel
    v5 v6 v7 v28 ret dep wdb cns bdb beb ob ntot hntot hdl hwl hcl hbdl hbel hAer
    _ hAmb
  have c1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [rhvF1, rhvAerAmb, aerFoot] at hp ⊢; xperm_chunked hp) s1 s2
  -- indices 8-11
  have s3 := rhv_marshal_erh_own (aerTotal dl wl cl bdl bel) dl wp secBuf
    (aerOff4 dl wl cl bdl) (secBuf + BitVec.ofNat 64 ntot) BeLenA wl cp cl
    secBuf secBuf bel
    ((.x1 ↦ᵣ (pc 8)) ** (.x2 ↦ᵣ newSp) ** stackFree newSp erhStackDwords **
     (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion secBuf (aerSection ob dl wl cl bdl dep wdb cns bdb beb) **
     bytesRegion RhvHash rhvOld ** (.x8 ↦ᵣ expPtr) **
     rhvErhFrame newSp expPtr dp wp cp bdp bdl bep bel
       dep wdb cns bdb beb exp vals A)
    (by pcfR; exact hA)
  have c2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [aerFootPost, rhvAerAmb, rhvErhFrame] at hp ⊢
      xperm_chunked hp) c1 s3
  -- index 12: the named residual
  have s4 := rhv_erh_call (pc 8) newSp secBuf (aerTotal dl wl cl bdl bel) RhvHash st
    (aerSection ob dl wl cl bdl dep wdb cns bdb beb) rhvOld dig erhFuel _ h_erh
  have c3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [erhCallEntry] at hp ⊢; xperm_chunked hp) c2 s4
  -- index 13: the status split
  by_cases hst : st = 0
  · subst hst
    have s5 := rhv_status_branch_ok_own _ hBF
    have c4 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        simp only [erhCallReturn, rhvErhFrame, rhvBranchF, erhStackDwords] at hp ⊢
        xperm_chunked hp) c3 s5
    have s6 := rhv_cmp_setup_own expPtr
      (regOwn .x10 ** (.x0 ↦ᵣ (0 : Word)) **
       regOwn .x28 ** regOwn .x29 **
       bytesRegion RhvHash dig ** bytesRegion expPtr exp **
       rhvCmpFrame newSp secBuf dl wl cl bdl bel dp wp cp bdp bep
         dep wdb cns bdb beb ob vals A)
      (by pcfR; exact hA)
    have c5 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        simp only [rhvBranchF, erhScratchOwn, rhvCmpFrame] at hp ⊢
        xperm_chunked hp) c4 s6
    have s7 := rhv_cmp_tail RhvHash expPtr dig exp
      (cmpGate_of_rhvGate expPtr dig exp hGate)
      ((.x8 ↦ᵣ expPtr) ** rhvCmpFrame newSp secBuf dl wl cl bdl bel
        dp wp cp bdp bep dep wdb cns bdb beb ob vals A)
      (by pcfR; exact hA)
    have c6 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        have h32 : BitVec.ofNat 64 32 = (32 : Word) := by decide
        simp only [cmpInv, addr_zero, h32] at hp ⊢
        xperm_chunked hp) c5 s7
    have hle : 3 + (1 + aerFuel (ntot - 20)) + 4 + (1 + erhFuel) + 1 + 4 + 260
        ≤ rhvBodyFuel (ntot - 20) erhFuel := by
      unfold rhvBodyFuel; omega
    refine cpsTripleWithin_mono_nSteps hle ?_
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) c6
    simp only [rhvBodyPost, rhvVerdict_ok, cmpJoin, rhvCmpFrame] at hq ⊢
    xperm_chunked hq
  · have s5 := rhv_status_branch_fail st hst _ hBF
    have c4 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        simp only [erhCallReturn, rhvErhFrame, rhvBranchF, erhStackDwords] at hp ⊢
        xperm_chunked hp) c3 s5
    have s8 := rhv_hashfail_verdict st
      ((.x0 ↦ᵣ (0 : Word)) ** rhvBranchF newSp secBuf expPtr dl wl cl bdl bel
        dp wp cp bdp bep dep wdb cns bdb beb ob dig exp vals A)
      (by pcfR; exact hA)
    have c5 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_chunked hp) c4 s8
    have hle : 3 + (1 + aerFuel (ntot - 20)) + 4 + (1 + erhFuel) + 1 + 1
        ≤ rhvBodyFuel (ntot - 20) erhFuel := by
      unfold rhvBodyFuel; omega
    refine cpsTripleWithin_mono_nSteps hle ?_
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) c5
    simp only [rhvBodyPost, rhvVerdict_fail st hst dig exp, rhvBranchF,
      erhScratchOwn] at hq ⊢
    xperm_chunked hq

/-! ## The whole routine -/

/-- Entry values of the three callee-saved registers the prologue spills. -/
def rhvVals (ret v8 v9 : Word) : Reg → Word
  | .x1 => ret
  | .x8 => v8
  | .x9 => v9
  | _ => 0

/-- Their values at the end of the body: `ra` holds the second call's link,
    `s0`/`s1` the caller's two pointers. All three are then restored by the
    epilogue (0x800543c8/cc/d0), which is why the routine's post shows
    `rhvVals` again. -/
def rhvVals' (raLast expPtr secBuf : Word) : Reg → Word
  | .x1 => raLast
  | .x8 => expPtr
  | .x9 => secBuf
  | _ => 0

/-- Caller-visible footprint at entry: the five request bodies and their
    lengths in the ABI registers, the scratch section buffer, the header's
    expected 32-byte hash, the `rhv_hash` BSS scratch, the free stack
    `execution_requests_hash` frames from, and the caller-saved registers
    the two callees clobber. -/
def rhvCallerPre (newSp v5 v6 v7 v28 expPtr secBuf
    dp dl wp wl cp cl bdp bdl bep bel : Word)
    (dep wdb cns bdb beb ob rhvOld exp : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x16 ↦ᵣ expPtr) ** (.x17 ↦ᵣ secBuf) **
  (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
  (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) **
  bytesRegion secBuf ob ** (BdLenA ↦ₘ bdl) **
  (.x0 ↦ᵣ (0 : Word)) ** regOwn .x29 **
  bytesRegion dp dep ** bytesRegion wp wdb ** bytesRegion cp cns **
  bytesRegion bdp bdb ** bytesRegion bep beb **
  (.x10 ↦ᵣ dp) ** (.x12 ↦ᵣ wp) ** (.x14 ↦ᵣ cp) **
  (BdPtrA ↦ₘ bdp) ** (BePtrA ↦ₘ bep) ** (BeLenA ↦ₘ bel) **
  stackFree newSp erhStackDwords **
  bytesRegion RhvHash rhvOld ** bytesRegion expPtr exp **
  regOwn .x30 ** regOwn .x31 ** A

/-- Caller-visible footprint at return: `a0` holds the verdict, the scratch
    buffer holds the assembled SSZ section, `rhv_hash` holds the digest the
    second callee derived, and every caller-saved register is merely owned. -/
def rhvCallerPost (newSp secBuf expPtr st dl wl cl bdl bel
    dp wp cp bdp bep : Word)
    (dep wdb cns bdb beb ob dig exp : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x10 ↦ᵣ rhvVerdict st dig exp) ** (.x0 ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
  regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  stackFree newSp erhStackDwords **
  bytesRegion secBuf (aerSection ob dl wl cl bdl dep wdb cns bdb beb) **
  bytesRegion RhvHash dig ** bytesRegion expPtr exp **
  bytesRegion dp dep ** bytesRegion wp wdb ** bytesRegion cp cns **
  bytesRegion bdp bdb ** bytesRegion bep beb **
  (BdPtrA ↦ₘ bdp) ** (BdLenA ↦ₘ bdl) ** (BePtrA ↦ₘ bep) **
  (BeLenA ↦ₘ bel) ** A

/-- Whole-routine step budget: prologue (`addi` + three `sd`), the body, the
    epilogue (three `ld` + `addi`), and `ret`. -/
def rhvFuel (bodyBytes erhFuel : Nat) : Nat := rhvBodyFuel bodyBytes erhFuel + 9

private theorem regsAt_rhvFrame (ret v8 v9 : Word) :
    regsAt rhvFrame (rhvVals ret v8 v9)
      = ((.x1 ↦ᵣ ret) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** empAssertion) := rfl

private theorem regsAt_rhvFrame' (raLast expPtr secBuf : Word) :
    regsAt rhvFrame (rhvVals' raLast expPtr secBuf)
      = ((.x1 ↦ᵣ raLast) ** (.x8 ↦ᵣ expPtr) ** (.x9 ↦ᵣ secBuf) ** empAssertion) := rfl

private theorem rhvFrame_len : rhvFrame.length = 3 := by decide
private theorem se12_m32 : signExtend12 (-32 : BitVec 12) = (-32 : Word) := by decide
private theorem se12_p32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide

/-- **`requests_hash_verify`, whole routine** (0x8005434c → `ret` at
    0x800543d8, 36 instructions).

    The routine assembles the five execution-produced request bodies into an
    SSZ section, has `execution_requests_hash` derive a `requests_hash` from it
    into the `rhv_hash` BSS scratch, and compares that digest byte-for-byte
    against the 32-byte hash the block header claims.

    **Post — the three exit codes**, via `rhvVerdict`:
    * `a0 = 2` when the callee reported failure (`bnez a0` at 0x80054380 taken,
      `li a0, 2` at 0x800543c4);
    * `a0 = 1` when some byte differs (`bne t3, t4` at 0x800543a0 taken,
      `li a0, 1` at 0x800543bc);
    * `a0 = 0` when all 32 bytes match (`beqz t2` at 0x80054394 taken,
      `li a0, 0` at 0x800543b4).

    The scratch buffer is left holding the assembled section and `rhv_hash` the
    derived digest; the five body regions and the caller's expected hash are
    unchanged; `ra`/`s0`/`s1` are restored by the epilogue.

    Hypotheses, classified:
    * `hntot`/`hdl`…`hbel` — the callee's length bookkeeping, forwarded.
    * `hAer` — `assemble_execution_requests`'s own input-domain gate (#12813).
    * `hGate` — this routine's input-domain gate, about the CALLER's
      expected-hash buffer only; the `rhv_hash` side is proved, not assumed
      (`rhvHash_gate`).
    * `halign` — the ordinary ABI obligation that the return address is even.
    * `h_erh` — the NAMED RESIDUAL `ErhCallShape`: an UNPROVEN-CALLEE
      DEPENDENCY on `execution_requests_hash`, **not** an input-domain
      restriction. `execution_requests_hash`'s registry row covers only a
      non-returning validation prefix, so there is no contract to compose;
      `erhCallSite_ok` discharges every computable conjunct of the shape at the
      real call site, and `rhv_residual_reachable` exhibits an instance.

    `assemble_execution_requests` is NOT assumed: its call is composed from
    `assemble_execution_requests_spec_within` in `rhv_aer_call_composed`. -/
theorem requests_hash_verify_spec_within
    (sp0 ret v8 v9 v5 v6 v7 v28 expPtr secBuf
     dp dl wp wl cp cl bdp bdl bep bel st : Word)
    (dep wdb cns bdb beb ob rhvOld exp dig : List (BitVec 8))
    (ntot erhFuel : Nat)
    (hntot : ntot = 20 + dep.length + wdb.length + cns.length + bdb.length + beb.length)
    (hdl : dl = BitVec.ofNat 64 dep.length)
    (hwl : wl = BitVec.ofNat 64 wdb.length)
    (hcl : cl = BitVec.ofNat 64 cns.length)
    (hbdl : bdl = BitVec.ofNat 64 bdb.length)
    (hbel : bel = BitVec.ofNat 64 beb.length)
    (hAer : aerGateOk secBuf dp wp cp bdp bep dep wdb cns bdb beb ob)
    (hGate : rhvGateOk expPtr dig exp)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (A : Assertion) (hA : A.pcFree)
    (h_erh : ErhCallShape rhvCode (pc 12) (pc 8)
      (sp0 + signExtend12 (-32 : BitVec 12)) secBuf
      (aerTotal dl wl cl bdl bel) RhvHash st
      (aerSection ob dl wl cl bdl dep wdb cns bdb beb) rhvOld dig
      (jalOff GuestAddrs.execution_requests_hash
        (GuestAddrs.requests_hash_verify + 48)) erhFuel
      ((.x8 ↦ᵣ expPtr) ** (.x9 ↦ᵣ secBuf) **
        rhvErhFrame (sp0 + signExtend12 (-32 : BitVec 12)) expPtr
          dp wp cp bdp bdl bep bel dep wdb cns bdb beb exp
          (rhvVals ret v8 v9) A)) :
    cpsTripleWithin (rhvFuel (ntot - 20) erhFuel) B ret rhvCode
      ((.x2 ↦ᵣ sp0) ** regsAt rhvFrame (rhvVals ret v8 v9) **
        frameSlotsOwn rhvFrame (sp0 + signExtend12 (-32 : BitVec 12)) **
        rhvCallerPre (sp0 + signExtend12 (-32 : BitVec 12)) v5 v6 v7 v28
          expPtr secBuf dp dl wp wl cp cl bdp bdl bep bel
          dep wdb cns bdb beb ob rhvOld exp A)
      ((.x2 ↦ᵣ sp0) ** regsAt rhvFrame (rhvVals ret v8 v9) **
        frameSlotsSaved rhvFrame (sp0 + signExtend12 (-32 : BitVec 12))
          (rhvVals ret v8 v9) **
        rhvCallerPost (sp0 + signExtend12 (-32 : BitVec 12)) secBuf expPtr st
          dl wl cl bdl bel dp wp cp bdp bep
          dep wdb cns bdb beb ob dig exp A) := by
  have hbody := rhv_body (sp0 + signExtend12 (-32 : BitVec 12)) ret v8 v9
    v5 v6 v7 v28 expPtr secBuf dp dl wp wl cp cl bdp bdl bep bel st
    dep wdb cns bdb beb ob rhvOld exp dig ntot erhFuel
    hntot hdl hwl hcl hbdl hbel hAer hGate (rhvVals ret v8 v9) A hA h_erh
  have hb1 : B + BitVec.ofNat 64 (4 * (1 + rhvFrame.length)) = pc 4 := by
    unfold pc; rw [rhvFrame_len]
  have hb2 : B + BitVec.ofNat 64 (4 * (1 + rhvFrame.length + rhvBody.length)) = pc 31 := by
    unfold pc; rw [rhvFrame_len, show rhvBody.length = 27 from by decide]
  rw [← hb1, ← hb2] at hbody
  have hcpF : (rhvCallerPre (sp0 + signExtend12 (-32 : BitVec 12)) v5 v6 v7 v28
      expPtr secBuf dp dl wp wl cp cl bdp bdl bep bel
      dep wdb cns bdb beb ob rhvOld exp A).pcFree := by
    unfold rhvCallerPre; pcfR; exact hA
  have hcpF' : (rhvCallerPost (sp0 + signExtend12 (-32 : BitVec 12)) secBuf expPtr st
      dl wl cl bdl bel dp wp cp bdp bep dep wdb cns bdb beb ob dig exp A).pcFree := by
    unfold rhvCallerPost; pcfR; exact hA
  have hle : 1 + rhvFrame.length + rhvBodyFuel (ntot - 20) erhFuel
      + rhvFrame.length + 1 + 1 ≤ rhvFuel (ntot - 20) erhFuel := by
    rw [rhvFrame_len]; unfold rhvFuel; omega
  refine cpsTripleWithin_mono_nSteps hle ?_
  refine abiFrame_spec B sp0 ret (-32 : BitVec 12) (32 : BitVec 12)
    rhvFrame (0 : BitVec 12) [(.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12))]
    (rhvVals ret v8 v9) (rhvVals' (pc 13) expPtr secBuf)
    rhvBody (rhvBodyFuel (ntot - 20) erhFuel) _ _ rhvCode
    rfl (by decide) (by decide)
    (by rw [← rhvProg_eq_abiFrame, rhvProgL_len]; norm_num)
    rfl halign
    (by rw [se12_m32, se12_p32]; bv_omega)
    hcpF hcpF'
    (by
      intro a i h
      rw [← rhvProg_eq_abiFrame] at h
      exact CodeReq.union_mono_left a i h)
    ?_
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hbody
  · simp only [rhvBodyPre, rhvF1, rhvCallerPre, regsAt_rhvFrame,
      sepConj_emp_right'] at hp ⊢
    xperm_chunked hp
  · simp only [rhvBodyPost, rhvCallerPost, regsAt_rhvFrame',
      sepConj_emp_right'] at hq ⊢
    xperm_chunked hq

end EvmAsm.Codegen.RequestsHashVerifyTop
