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
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_bytesRegion
      | exact pcFree_stackFree)

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

end EvmAsm.Codegen.RequestsHashVerifyTop
