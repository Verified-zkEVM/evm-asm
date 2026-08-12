/-
  EvmAsm.Codegen.Programs.WitnessCodesLookupSpec

  **Machine facts for the guest routine `witness_codes_lookup_by_hash`** (GH #12036).

  `witnessCodesLookupByHash_prog` (`WitnessCodeLookup.lean`, 155 instructions) was
  transcribed in #12111 specifically so a `cpsTripleWithin` over the real
  linked program could be STATED. This module is the first tranche of that
  triple. The proved domain is an intentionally narrow empty-section,
  index-disabled checkpoint; it is not a claim about the scan, hash, or
  index-hit arms.

  ## §A  What is established here

  * `wclh_abiFrame_byte_tie` — the routine IS a standard 8-slot ABI frame
    around a 136-instruction body, so `abiFrame_spec_own` applies and the
    prologue/epilogue (`ra`, `s0`, `s1`, `s2`…`s6` save/restore, `sp`
    round-trip) are DERIVED, not assumed.
  * `wclhCounterBump_spec` — the five-instruction telemetry idiom
    (`la t0,C ; ld t1,0(t0) ; addi t1,t1,1 ; sd t1,0(t0)`) that occurs at
    EIGHT sites in this routine (instruction indices 14, 36, 43, 49, 55,
    96, 130, 139), proved once at a free `(A, C)`.
  * `witness_codes_lookup_by_hash_spec_within_empty_section` — the **whole-routine
    triple**, entry `GuestAddrs.witness_codes_lookup_by_hash` to the caller's
    return address, over `CodeReq.ofProg` of the real program, for the
    documented `section_len = 0 ⇒ guaranteed miss` domain with the witness
    index disabled. It pins `a0 = 1`, the callee-saved registers restored,
    the caller's out cells UNTOUCHED, and all six telemetry cells to their
    exact updated values.

  ## §B  What is NOT established (read before citing this module)

  The scan loop (`+308 … +552`), the SSZ offset-table guards (`+272 … +304`)
  and BOTH cross-`jal` arms are outside the claim:

  * `witness_codes_lookup_by_hash_indexed` (idx 41) and `zkvm_keccak256` (idx 101)
    have no machine triple. On the domain proved here neither is REACHED
    (the `wcidx_enabled = 0` test at idx 22 jumps over the first, and the
    `section_len = 0` test at idx 68 jumps over the loop that contains the
    second), so this theorem carries no unproven-callee dependency — but the
    general routine does, and any extension of this proof past those two
    branches must carry the callee contracts as explicit hypotheses.
  * The size subtlety in `WitnessCodeLookup.lean`'s docstring is respected:
    NOTHING here bounds `section_len` from above. The gate is
    `section_len = 0`, an input-domain restriction, not a size cap.

  * A concrete `MachineState` witness for the full nested precondition was
    attempted but did not discharge. The obstruction is the explicit
    `sepConj` disjointness construction for `regsAt`, `frameSlotsOwn`, and the
    telemetry-bearing `wclhArgs`; the attempted scratch proof remains
    commented below deliberately, with no `sorry` or `admit`. The two
    structural anti-vacuity checks that do hold are that `wclhCr` is
    `CodeReq.ofProg` at the real linked entry, and that the postcondition pins
    `a0`, caller cells, and every telemetry result.

  ## §C  The `wlCallWithinShape` residual (why it is still open)

  `MptWalkResiduals.wlCallWithinShape` is the named residual at the three
  MPT-walk call sites. `wclh_entry_not_in_walk_fullCode` and
  `wclh_cells_outside_residual_footprint` record, kernel-checked, the two
  independent reasons it cannot be discharged against ANY whole-routine
  triple for this routine as currently stated — see their docstrings.
  `wclhCallWithin_empty_section` is the discharge that IS available: the same
  `callWithin_spec` composition, at a `CodeReq` that contains the callee and
  with the telemetry cells in the call-site ambient.
-/

import EvmAsm.Codegen.Programs.WitnessCodeLookup
import EvmAsm.Codegen.Programs.MptWalkResiduals
import EvmAsm.Evm64.WitnessAssertions
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.WitnessCodesLookupSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Evm64
open EvmAsm.Codegen

set_option maxRecDepth 8000

/-! ## §1  The linked routine -/

/-- The routine's linked entry (`GuestAddrs.witness_codes_lookup_by_hash`). -/
def wclhB : Word := (GuestAddrs.witness_codes_lookup_by_hash : Word)

/-- The routine's own code requirement: the 155-instruction emitted program
    at its linked address. Every triple below is stated over this, so the
    machine is named in each of them. -/
def wclhCr : CodeReq := CodeReq.ofProg wclhB witnessCodesLookupByHash_prog

/-- The 8-slot callee-save frame: `ra` plus `s0,s1,s2,s3,s4,s5,s6`
    (`x8,x9,x18,x19,x20,x21,x22`), 64 bytes. -/
def wclhFrame : FrameDesc :=
  [(.x1, (0 : BitVec 12)), (.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12)),
   (.x18, (24 : BitVec 12)), (.x19, (32 : BitVec 12)), (.x20, (40 : BitVec 12)),
   (.x21, (48 : BitVec 12)), (.x22, (56 : BitVec 12))]

/-- The framed body: instructions 9 … 144, i.e. everything between the
    prologue's last `sd` and the epilogue's first `ld`. -/
def wclhBody : List Instr := (witnessCodesLookupByHash_prog.drop 9).take 136

/-- **The routine is an ABI frame around `wclhBody`.** Kernel-checked against
    the emitted program, so callee-saved preservation and the `sp`
    round-trip come from `abiFrame_spec_own` rather than being assumed. -/
theorem wclh_abiFrame_byte_tie :
    abiFrameProg (-64 : BitVec 12) (64 : BitVec 12) wclhFrame wclhBody =
      witnessCodesLookupByHash_prog := by
  decide

theorem wclhBody_length : wclhBody.length = 136 := by decide

theorem wclhFrame_length : wclhFrame.length = 8 := by decide

/-! ## §2  The `.data` cells the routine reads and writes

    Six telemetry/dispatch cells lie on the `section_len = 0` path. They are
    part of the routine's FOOTPRINT: the pre must own them, or the frame rule
    is violated. -/

/-- `wclh_lookup_calls` — bumped on every call. -/
def CallsLoc : Word := (GuestAddrs.wclh_lookup_calls : Word)
/-- `wcidx_enabled` — the index-dispatch flag (read only). -/
def WcidxEnLoc : Word := (GuestAddrs.wcidx_enabled : Word)
/-- `wclh_linear_calls` — bumped on every linear-path call. -/
def LinCallsLoc : Word := (GuestAddrs.wclh_linear_calls : Word)
/-- `wclh_linear_last_section_len` — overwritten with this call's length. -/
def LinLastLoc : Word := (GuestAddrs.wclh_linear_last_section_len : Word)
/-- `wclh_linear_max_section_len` — kept at the running maximum. -/
def LinMaxLoc : Word := (GuestAddrs.wclh_linear_max_section_len : Word)
/-- `wclh_linear_misses` — bumped when the linear path reports a miss. -/
def LinMissLoc : Word := (GuestAddrs.wclh_linear_misses : Word)

/-! ## §3  The telemetry-counter idiom

    `la t0, C ; ld t1, 0(t0) ; addi t1, t1, 1 ; sd t1, 0(t0)` — five
    instructions; three of the eight occurrences in this routine are on the
    `section_len = 0` path. Proved once, at a free `(A, C)`. -/

private theorem sext12_zero : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem sext12_one : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide

/-- **One telemetry bump**, at a free bump address `A` and free cell `C`.
    Code membership is hypothesis-shaped so each call site discharges it by
    evaluation against `wclhCr`. -/
theorem wclhCounterBump_spec (A C : Word) (v5 v6 n : Word)
    (hrange : laInRange A C)
    (hau : ∀ a i, CodeReq.singleton A (.AUIPC .x5 (Rv64.laHi A C)) a = some i →
      wclhCr a = some i)
    (had : ∀ a i, CodeReq.singleton (A + 4) (.ADDI .x5 .x5 (Rv64.laLo A C)) a = some i →
      wclhCr a = some i)
    (hld : ∀ a i, CodeReq.singleton (A + 8) (.LD .x6 .x5 (0 : BitVec 12)) a = some i →
      wclhCr a = some i)
    (hai : ∀ a i, CodeReq.singleton (A + 12) (.ADDI .x6 .x6 (1 : BitVec 12)) a = some i →
      wclhCr a = some i)
    (hsd : ∀ a i, CodeReq.singleton (A + 16) (.SD .x5 .x6 (0 : BitVec 12)) a = some i →
      wclhCr a = some i) :
    cpsTripleWithin 5 A (A + 20) wclhCr
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** (C ↦ₘ n))
      (((.x5 : Reg) ↦ᵣ C) ** ((.x6 : Reg) ↦ᵣ (n + 1)) ** (C ↦ₘ (n + 1))) := by
  have hla := la_materialize_within .x5 v5 A C (by decide) hrange hau had
  have h2 := liftCode (cr' := wclhCr)
    (ld_spec_gen_within .x6 .x5 C v6 n (0 : BitVec 12) (A + 8) (by decide)) hld
  rw [sext12_zero, show C + (0 : Word) = C from by bv_omega,
    show (A + 8 : Word) + 4 = A + 12 from by bv_omega] at h2
  have h3 := liftCode (cr' := wclhCr)
    (addi_spec_gen_same_within .x6 n (1 : BitVec 12) (A + 12) (by decide)) hai
  rw [sext12_one, show (A + 12 : Word) + 4 = A + 16 from by bv_omega] at h3
  have h4 := liftCode (cr' := wclhCr)
    (sd_spec_gen_within .x5 .x6 C (n + 1) n (0 : BitVec 12) (A + 16)) hsd
  rw [sext12_zero, show C + (0 : Word) = C from by bv_omega,
    show (A + 16 : Word) + 4 = A + 20 from by bv_omega] at h4
  have f1 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6) ** (C ↦ₘ n)) (by pcf) hla
  have f3 := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ C) ** (C ↦ₘ n)) (by pcf) h3
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f1 h2
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 f3
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 h4
  exact cpsTripleWithin_mono_nSteps (show 2 + 1 + 1 + 1 ≤ 5 by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c3)


/-! ## §4  The `section_len = 0` body, segment by segment

    Body entry is `wclhB + 36` (instruction 9, the first `mv`); body exit is
    `wclhB + 580` (instruction 145, the epilogue's first `ld`) — the address
    the routine's own `j` instructions target. Each segment below is stated
    with a TIGHT footprint (only what it touches); the composition frames the
    rest. -/

/-- **S1 — the argument moves** (idx 9…13): the five caller arguments are
    parked in the callee-saved registers the whole routine uses. Asymmetric
    by construction: `a0→s0`, `a1→s1`, `a2→s2`, `a3→s3`, `a4→s4` are five
    different pairs, so a swapped pair would not typecheck against the post. -/
private theorem wclhArgMoves_spec (secPtr len hashPtr outOffP outLenP
    a8 a9 a18 a19 a20 : Word) :
    cpsTripleWithin 5 (wclhB + 36) (wclhB + 56) wclhCr
      (((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
        ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
        ((.x8 : Reg) ↦ᵣ a8) ** ((.x9 : Reg) ↦ᵣ a9) ** ((.x18 : Reg) ↦ᵣ a18) **
        ((.x19 : Reg) ↦ᵣ a19) ** ((.x20 : Reg) ↦ᵣ a20))
      (((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
        ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
        ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ hashPtr) **
        ((.x19 : Reg) ↦ᵣ outOffP) ** ((.x20 : Reg) ↦ᵣ outLenP)) := by
  have h9 := liftCode (cr' := wclhCr)
    (mv_spec_gen_within .x8 .x10 secPtr a8 (wclhB + 36) (by decide))
    (by unfold wclhCr; code_mem)
  rw [show (wclhB + 36 : Word) + 4 = wclhB + 40 from by bv_omega] at h9
  have h10 := liftCode (cr' := wclhCr)
    (mv_spec_gen_within .x9 .x11 len a9 (wclhB + 40) (by decide))
    (by unfold wclhCr; code_mem)
  rw [show (wclhB + 40 : Word) + 4 = wclhB + 44 from by bv_omega] at h10
  have h11 := liftCode (cr' := wclhCr)
    (mv_spec_gen_within .x18 .x12 hashPtr a18 (wclhB + 44) (by decide))
    (by unfold wclhCr; code_mem)
  rw [show (wclhB + 44 : Word) + 4 = wclhB + 48 from by bv_omega] at h11
  have h12 := liftCode (cr' := wclhCr)
    (mv_spec_gen_within .x19 .x13 outOffP a19 (wclhB + 48) (by decide))
    (by unfold wclhCr; code_mem)
  rw [show (wclhB + 48 : Word) + 4 = wclhB + 52 from by bv_omega] at h12
  have h13 := liftCode (cr' := wclhCr)
    (mv_spec_gen_within .x20 .x14 outLenP a20 (wclhB + 52) (by decide))
    (by unfold wclhCr; code_mem)
  rw [show (wclhB + 52 : Word) + 4 = wclhB + 56 from by bv_omega] at h13
  have f9 := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
      ((.x14 : Reg) ↦ᵣ outLenP) ** ((.x9 : Reg) ↦ᵣ a9) ** ((.x18 : Reg) ↦ᵣ a18) **
      ((.x19 : Reg) ↦ᵣ a19) ** ((.x20 : Reg) ↦ᵣ a20)) (by pcf) h9
  have f10 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ secPtr) ** ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
      ((.x14 : Reg) ↦ᵣ outLenP) ** ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x18 : Reg) ↦ᵣ a18) **
      ((.x19 : Reg) ↦ᵣ a19) ** ((.x20 : Reg) ↦ᵣ a20)) (by pcf) h10
  have f11 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x13 : Reg) ↦ᵣ outOffP) **
      ((.x14 : Reg) ↦ᵣ outLenP) ** ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x9 : Reg) ↦ᵣ len) **
      ((.x19 : Reg) ↦ᵣ a19) ** ((.x20 : Reg) ↦ᵣ a20)) (by pcf) h11
  have f12 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
      ((.x14 : Reg) ↦ᵣ outLenP) ** ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x9 : Reg) ↦ᵣ len) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x20 : Reg) ↦ᵣ a20)) (by pcf) h12
  have f13 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
      ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x9 : Reg) ↦ᵣ len) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP)) (by pcf) h13
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f9 f10
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 f11
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 f12
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c3 f13
  exact cpsTripleWithin_mono_nSteps (show 1 + 1 + 1 + 1 + 1 ≤ 5 by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c4)

/-- The false arm of a `beq` whose two operands are the same value is
    unsatisfiable — it carries `⌜v ≠ v⌝`. -/
private theorem beq_same_absurd {r1 r2 : Reg} {v : Word} :
    ∀ hp, (((r1 : Reg) ↦ᵣ v) ** ((r2 : Reg) ↦ᵣ v) ** ⌜v ≠ v⌝) hp → False := by
  intro hp hq
  obtain ⟨_, _, _, _, _, hB⟩ := hq
  obtain ⟨_, _, _, _, _, hP⟩ := hB
  exact hP.2 rfl

/-- The false arm of `bgeu rs1, x9` with `x9 = 0` is unsatisfiable — nothing
    is unsigned-less-than zero. -/
private theorem bgeu_zero_absurd {r1 r2 : Reg} {v : Word} :
    ∀ hp, (((r1 : Reg) ↦ᵣ v) ** ((r2 : Reg) ↦ᵣ (0 : Word)) **
      ⌜BitVec.ult v (0 : Word)⌝) hp → False := by
  intro hp hq
  obtain ⟨_, _, _, _, _, hB⟩ := hq
  obtain ⟨_, _, _, _, _, hP⟩ := hB
  have h := hP.2
  simp only [BitVec.ult, decide_eq_true_eq,
    show (0 : Word).toNat = 0 from by decide] at h
  omega

/-- **S3 — the index dispatch** (idx 19…22): `wcidx_enabled` is read and, when
    it is zero, control jumps to the linear scan at `+220`. This is the
    branch that makes the `witness_codes_lookup_by_hash_indexed` cross-`jal` (idx
    41) UNREACHED on this domain. -/
private theorem wclhWcidxDispatch_spec (v5 : Word) :
    cpsTripleWithin 4 (wclhB + 76) (wclhB + 220) wclhCr
      (((.x5 : Reg) ↦ᵣ v5) ** (WcidxEnLoc ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (((.x5 : Reg) ↦ᵣ (0 : Word)) ** (WcidxEnLoc ↦ₘ (0 : Word)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word))) := by
  have hla := la_materialize_within .x5 v5 (wclhB + 76) WcidxEnLoc (cr := wclhCr)
    (by decide) (by decide) (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem)
  rw [show (wclhB + 76 : Word) + 8 = wclhB + 84 from by bv_omega] at hla
  have hld := liftCode (cr' := wclhCr)
    (ld_spec_gen_same_within .x5 WcidxEnLoc (0 : Word) (0 : BitVec 12) (wclhB + 84)
      (by decide))
    (by unfold wclhCr; code_mem)
  rw [sext12_zero, show WcidxEnLoc + (0 : Word) = WcidxEnLoc from by bv_omega,
    show (wclhB + 84 : Word) + 4 = wclhB + 88 from by bv_omega] at hld
  have hbr := cpsBranchWithin_extend_code (cr' := wclhCr)
    (by unfold wclhCr; code_mem)
    (beq_spec_gen_within .x5 .x0
      (brOff (GuestAddrs.witness_codes_lookup_by_hash + 220)
        (GuestAddrs.witness_codes_lookup_by_hash + 88)) (0 : Word) (0 : Word) (wclhB + 88))
  have hbt := cpsBranchWithin_takenStripPure2 hbr beq_same_absurd
  rw [show (wclhB + 88 : Word) + signExtend13
      (brOff (GuestAddrs.witness_codes_lookup_by_hash + 220)
        (GuestAddrs.witness_codes_lookup_by_hash + 88)) = wclhB + 220 from by decide] at hbt
  have f1 := cpsTripleWithin_frameR
    ((WcidxEnLoc ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) (by pcf) hla
  have f2 := cpsTripleWithin_frameR (((.x0 : Reg) ↦ᵣ (0 : Word))) (by pcf) hld
  have f3 := cpsTripleWithin_frameR ((WcidxEnLoc ↦ₘ (0 : Word))) (by pcf) hbt
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f1 f2
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 f3
  exact cpsTripleWithin_mono_nSteps (show 2 + 1 + 1 ≤ 4 by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c2)

/-- **S5 — the last-length telemetry store** (idx 60…62): this call's
    `section_len` (in `s1`) is written to `wclh_linear_last_section_len`. -/
private theorem wclhLastLen_spec (v5 len nLast : Word) :
    cpsTripleWithin 3 (wclhB + 240) (wclhB + 252) wclhCr
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x9 : Reg) ↦ᵣ len) ** (LinLastLoc ↦ₘ nLast))
      (((.x5 : Reg) ↦ᵣ LinLastLoc) ** ((.x9 : Reg) ↦ᵣ len) ** (LinLastLoc ↦ₘ len)) := by
  have hla := la_materialize_within .x5 v5 (wclhB + 240) LinLastLoc (cr := wclhCr)
    (by decide) (by decide) (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem)
  rw [show (wclhB + 240 : Word) + 8 = wclhB + 248 from by bv_omega] at hla
  have hsd := liftCode (cr' := wclhCr)
    (sd_spec_gen_within .x5 .x9 LinLastLoc len nLast (0 : BitVec 12) (wclhB + 248))
    (by unfold wclhCr; code_mem)
  rw [sext12_zero, show LinLastLoc + (0 : Word) = LinLastLoc from by bv_omega,
    show (wclhB + 248 : Word) + 4 = wclhB + 252 from by bv_omega] at hsd
  have f1 := cpsTripleWithin_frameR
    (((.x9 : Reg) ↦ᵣ len) ** (LinLastLoc ↦ₘ nLast)) (by pcf) hla
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f1 hsd
  exact cpsTripleWithin_mono_nSteps (show 2 + 1 ≤ 3 by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c1)

/-- **S6 — the max-length telemetry guard** (idx 63…66): the running maximum
    is read and the `bgeu` skips the update. With `section_len = 0` the guard
    ALWAYS skips, so `wclh_linear_max_section_len` is left unchanged — the
    routine never lowers its own high-water mark. -/
private theorem wclhMaxLen_spec (v5 v6 nMax : Word) :
    cpsTripleWithin 4 (wclhB + 252) (wclhB + 272) wclhCr
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
        (LinMaxLoc ↦ₘ nMax))
      (((.x5 : Reg) ↦ᵣ LinMaxLoc) ** ((.x6 : Reg) ↦ᵣ nMax) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** (LinMaxLoc ↦ₘ nMax)) := by
  have hla := la_materialize_within .x5 v5 (wclhB + 252) LinMaxLoc (cr := wclhCr)
    (by decide) (by decide) (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem)
  rw [show (wclhB + 252 : Word) + 8 = wclhB + 260 from by bv_omega] at hla
  have hld := liftCode (cr' := wclhCr)
    (ld_spec_gen_within .x6 .x5 LinMaxLoc v6 nMax (0 : BitVec 12) (wclhB + 260)
      (by decide))
    (by unfold wclhCr; code_mem)
  rw [sext12_zero, show LinMaxLoc + (0 : Word) = LinMaxLoc from by bv_omega,
    show (wclhB + 260 : Word) + 4 = wclhB + 264 from by bv_omega] at hld
  have hbr := cpsBranchWithin_extend_code (cr' := wclhCr)
    (by unfold wclhCr; code_mem)
    (bgeu_spec_gen_within .x6 .x9 (8 : BitVec 13) nMax (0 : Word) (wclhB + 264))
  have hbt := cpsBranchWithin_takenStripPure2 hbr bgeu_zero_absurd
  rw [show (wclhB + 264 : Word) + signExtend13 (8 : BitVec 13) = wclhB + 272
    from by decide] at hbt
  have f1 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) ** (LinMaxLoc ↦ₘ nMax))
    (by pcf) hla
  have f2 := cpsTripleWithin_frameR (((.x9 : Reg) ↦ᵣ (0 : Word))) (by pcf) hld
  have f3 := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ LinMaxLoc) ** (LinMaxLoc ↦ₘ nMax)) (by pcf) hbt
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f1 f2
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 f3
  exact cpsTripleWithin_mono_nSteps (show 2 + 1 + 1 ≤ 4 by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c2)

/-- **S7 — the zero-length exit** (idx 68): `section_len = 0` jumps straight
    to the miss tail at `+556`, over the SSZ header guards AND the whole scan
    loop — which is why the `zkvm_keccak256` cross-`jal` (idx 101) is
    UNREACHED on this domain. -/
private theorem wclhZeroLenExit_spec :
    cpsTripleWithin 1 (wclhB + 272) (wclhB + 556) wclhCr
      (((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) := by
  have hbr := cpsBranchWithin_extend_code (cr' := wclhCr)
    (by unfold wclhCr; code_mem)
    (beq_spec_gen_within .x9 .x0
      (brOff (GuestAddrs.witness_codes_lookup_by_hash + 556)
        (GuestAddrs.witness_codes_lookup_by_hash + 272)) (0 : Word) (0 : Word) (wclhB + 272))
  have hbt := cpsBranchWithin_takenStripPure2 hbr beq_same_absurd
  rw [show (wclhB + 272 : Word) + signExtend13
      (brOff (GuestAddrs.witness_codes_lookup_by_hash + 556)
        (GuestAddrs.witness_codes_lookup_by_hash + 272)) = wclhB + 556 from by decide] at hbt
  exact hbt

/-- **S9 — the miss status** (idx 144): `a0 := 1`. -/
private theorem wclhMissStatus_spec (v10 : Word) :
    cpsTripleWithin 1 (wclhB + 576) (wclhB + 580) wclhCr
      (((.x10 : Reg) ↦ᵣ v10)) (((.x10 : Reg) ↦ᵣ (1 : Word))) := by
  have h := liftCode (cr' := wclhCr)
    (li_spec_gen_within .x10 v10 (1 : Word) (wclhB + 576) (by decide))
    (by unfold wclhCr; code_mem)
  rw [show (wclhB + 576 : Word) + 4 = wclhB + 580 from by bv_omega] at h
  exact h

/-! ## §5  The body, composed

    Nine segments, 33 machine steps, `wclhB + 36` → `wclhB + 580`. The exit is
    the epilogue's first instruction — the address the routine's own `j`
    instructions target — so this is the body `abiFrame_spec_own` expects. -/

/-- **The `section_len = 0` body**, with the tight footprint: the thirteen
    registers and six `.data` cells the path touches, and nothing else. -/
private theorem wclhEmptySectionBody_core (secPtr hashPtr outOffP outLenP
    v5 v6 a8 a9 a18 a19 a20 nCalls nLin nLast nMax nMiss : Word) :
    cpsTripleWithin 33 (wclhB + 36) (wclhB + 580) wclhCr
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x8 : Reg) ↦ᵣ a8) ** ((.x9 : Reg) ↦ᵣ a9) **
        ((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
        ((.x14 : Reg) ↦ᵣ outLenP) ** ((.x18 : Reg) ↦ᵣ a18) **
        ((.x19 : Reg) ↦ᵣ a19) ** ((.x20 : Reg) ↦ᵣ a20) ** (CallsLoc ↦ₘ nCalls) **
        (WcidxEnLoc ↦ₘ (0 : Word)) ** (LinCallsLoc ↦ₘ nLin) **
        (LinLastLoc ↦ₘ nLast) ** (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nMiss))
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ LinMissLoc) **
        ((.x6 : Reg) ↦ᵣ (nMiss + 1)) ** ((.x8 : Reg) ↦ᵣ secPtr) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
        ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
        ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
        ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
        ((.x20 : Reg) ↦ᵣ outLenP) ** (CallsLoc ↦ₘ (nCalls + 1)) **
        (WcidxEnLoc ↦ₘ (0 : Word)) ** (LinCallsLoc ↦ₘ (nLin + 1)) **
        (LinLastLoc ↦ₘ (0 : Word)) ** (LinMaxLoc ↦ₘ nMax) **
        (LinMissLoc ↦ₘ (nMiss + 1))) := by
  have h_s1 := wclhArgMoves_spec secPtr (0 : Word) hashPtr outOffP outLenP a8 a9 a18 a19 a20
  have h_b1 := wclhCounterBump_spec (wclhB + 56) CallsLoc v5 v6 nCalls (by decide)
    (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem)
  rw [show (wclhB + 56 : Word) + 20 = wclhB + 76 from by bv_omega] at h_b1
  have h_s3 := wclhWcidxDispatch_spec CallsLoc
  have h_b2 := wclhCounterBump_spec (wclhB + 220) LinCallsLoc (0 : Word) (nCalls + 1) nLin
    (by decide) (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem)
  rw [show (wclhB + 220 : Word) + 20 = wclhB + 240 from by bv_omega] at h_b2
  have h_s5 := wclhLastLen_spec LinCallsLoc (0 : Word) nLast
  have h_s6 := wclhMaxLen_spec LinLastLoc (nLin + 1) nMax
  have h_s7 := wclhZeroLenExit_spec
  have h_b3 := wclhCounterBump_spec (wclhB + 556) LinMissLoc LinMaxLoc nMax nMiss
    (by decide) (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem)
  rw [show (wclhB + 556 : Word) + 20 = wclhB + 576 from by bv_omega] at h_b3
  have h_s9 := wclhMissStatus_spec secPtr
  have f_s1 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) **
      ((.x6 : Reg) ↦ᵣ v6) ** (CallsLoc ↦ₘ nCalls) **
      (WcidxEnLoc ↦ₘ (0 : Word)) ** (LinCallsLoc ↦ₘ nLin) **
      (LinLastLoc ↦ₘ nLast) ** (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nMiss)) (by pcf) h_s1
  have f_b1 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x8 : Reg) ↦ᵣ secPtr) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ secPtr) **
      ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
      ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
      ((.x20 : Reg) ↦ᵣ outLenP) ** (WcidxEnLoc ↦ₘ (0 : Word)) **
      (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) ** (LinMaxLoc ↦ₘ nMax) **
      (LinMissLoc ↦ₘ nMiss)) (by pcf) h_b1
  have f_s3 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ (nCalls + 1)) ** ((.x8 : Reg) ↦ᵣ secPtr) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ secPtr) **
      ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
      ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
      ((.x20 : Reg) ↦ᵣ outLenP) ** (CallsLoc ↦ₘ (nCalls + 1)) **
      (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) ** (LinMaxLoc ↦ₘ nMax) **
      (LinMissLoc ↦ₘ nMiss)) (by pcf) h_s3
  have f_b2 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x8 : Reg) ↦ᵣ secPtr) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ secPtr) **
      ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
      ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
      ((.x20 : Reg) ↦ᵣ outLenP) ** (CallsLoc ↦ₘ (nCalls + 1)) **
      (WcidxEnLoc ↦ₘ (0 : Word)) ** (LinLastLoc ↦ₘ nLast) **
      (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nMiss)) (by pcf) h_b2
  have f_s5 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ (nLin + 1)) **
      ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x10 : Reg) ↦ᵣ secPtr) **
      ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
      ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
      ((.x20 : Reg) ↦ᵣ outLenP) ** (CallsLoc ↦ₘ (nCalls + 1)) **
      (WcidxEnLoc ↦ₘ (0 : Word)) ** (LinCallsLoc ↦ₘ (nLin + 1)) **
      (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nMiss)) (by pcf) h_s5
  have f_s6 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x8 : Reg) ↦ᵣ secPtr) **
      ((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
      ((.x14 : Reg) ↦ᵣ outLenP) ** ((.x18 : Reg) ↦ᵣ hashPtr) **
      ((.x19 : Reg) ↦ᵣ outOffP) ** ((.x20 : Reg) ↦ᵣ outLenP) **
      (CallsLoc ↦ₘ (nCalls + 1)) ** (WcidxEnLoc ↦ₘ (0 : Word)) **
      (LinCallsLoc ↦ₘ (nLin + 1)) ** (LinLastLoc ↦ₘ (0 : Word)) **
      (LinMissLoc ↦ₘ nMiss)) (by pcf) h_s6
  have f_s7 := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ LinMaxLoc) ** ((.x6 : Reg) ↦ᵣ nMax) **
      ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x10 : Reg) ↦ᵣ secPtr) **
      ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
      ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
      ((.x20 : Reg) ↦ᵣ outLenP) ** (CallsLoc ↦ₘ (nCalls + 1)) **
      (WcidxEnLoc ↦ₘ (0 : Word)) ** (LinCallsLoc ↦ₘ (nLin + 1)) **
      (LinLastLoc ↦ₘ (0 : Word)) ** (LinMaxLoc ↦ₘ nMax) **
      (LinMissLoc ↦ₘ nMiss)) (by pcf) h_s7
  have f_b3 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x8 : Reg) ↦ᵣ secPtr) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ secPtr) **
      ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
      ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
      ((.x20 : Reg) ↦ᵣ outLenP) ** (CallsLoc ↦ₘ (nCalls + 1)) **
      (WcidxEnLoc ↦ₘ (0 : Word)) ** (LinCallsLoc ↦ₘ (nLin + 1)) **
      (LinLastLoc ↦ₘ (0 : Word)) ** (LinMaxLoc ↦ₘ nMax)) (by pcf) h_b3
  have f_s9 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ LinMissLoc) **
      ((.x6 : Reg) ↦ᵣ (nMiss + 1)) ** ((.x8 : Reg) ↦ᵣ secPtr) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
      ((.x14 : Reg) ↦ᵣ outLenP) ** ((.x18 : Reg) ↦ᵣ hashPtr) **
      ((.x19 : Reg) ↦ᵣ outOffP) ** ((.x20 : Reg) ↦ᵣ outLenP) **
      (CallsLoc ↦ₘ (nCalls + 1)) ** (WcidxEnLoc ↦ₘ (0 : Word)) **
      (LinCallsLoc ↦ₘ (nLin + 1)) ** (LinLastLoc ↦ₘ (0 : Word)) **
      (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ (nMiss + 1))) (by pcf) h_s9
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f_s1 f_b1
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 f_s3
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 f_b2
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c3 f_s5
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c4 f_s6
  have c6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c5 f_s7
  have c7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c6 f_b3
  have c8 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c7 f_s9
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c8)

/-! ## §6  The whole-routine triple

    `abiFrame_spec_own` turns the body into the routine: the prologue's nine
    stores, the epilogue's nine loads and the `ret` are DERIVED, and with them
    callee-saved preservation and the `sp` round-trip. -/

/-- The caller-visible ambient at entry: the ABI arguments with
    `section_len = 0`, the two temporaries the routine clobbers, and the six
    `.data` cells it touches — `wcidx_enabled` READ as zero (index disabled),
    the other five owned because the routine writes them. -/
def wclhArgs (v5 v6 secPtr hashPtr outOffP outLenP
    nCalls nLin nLast nMax nMiss : Word) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
  ((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
  ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
  ((.x14 : Reg) ↦ᵣ outLenP) **
  (CallsLoc ↦ₘ nCalls) ** (WcidxEnLoc ↦ₘ (0 : Word)) ** (LinCallsLoc ↦ₘ nLin) **
  (LinLastLoc ↦ₘ nLast) ** (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nMiss)

/-- The caller-visible ambient at return: **`a0 = 1`, the miss status**, the
    argument registers `a1…a4` intact, and each telemetry cell at its exact
    new value. Asymmetric by construction — `wclh_lookup_calls` and
    `wclh_linear_calls` are bumped, `wclh_linear_last_section_len` is
    OVERWRITTEN with this call's length (zero) while
    `wclh_linear_max_section_len` is LEFT ALONE, and `wclh_linear_misses` is
    bumped. Swapping any two of the five would not typecheck. -/
def wclhMissOut (hashPtr outOffP outLenP
    nCalls nLin nMax nMiss : Word) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ LinMissLoc) **
  ((.x6 : Reg) ↦ᵣ (nMiss + 1)) **
  ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
  ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
  ((.x14 : Reg) ↦ᵣ outLenP) **
  (CallsLoc ↦ₘ (nCalls + 1)) ** (WcidxEnLoc ↦ₘ (0 : Word)) **
  (LinCallsLoc ↦ₘ (nLin + 1)) ** (LinLastLoc ↦ₘ (0 : Word)) **
  (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ (nMiss + 1))

theorem wclhArgs_pcFree (v5 v6 secPtr hashPtr outOffP outLenP
    nCalls nLin nLast nMax nMiss : Word) :
    (wclhArgs v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax nMiss).pcFree := by
  unfold wclhArgs; pcf

theorem wclhMissOut_pcFree (hashPtr outOffP outLenP nCalls nLin nMax nMiss : Word) :
    (wclhMissOut hashPtr outOffP outLenP nCalls nLin nMax nMiss).pcFree := by
  unfold wclhMissOut; pcf

private theorem regsAt_wclhFrame (vals : Reg → Word) :
    regsAt wclhFrame vals =
      (((.x1 : Reg) ↦ᵣ vals .x1) ** ((.x8 : Reg) ↦ᵣ vals .x8) **
        ((.x9 : Reg) ↦ᵣ vals .x9) ** ((.x18 : Reg) ↦ᵣ vals .x18) **
        ((.x19 : Reg) ↦ᵣ vals .x19) ** ((.x20 : Reg) ↦ᵣ vals .x20) **
        ((.x21 : Reg) ↦ᵣ vals .x21) ** ((.x22 : Reg) ↦ᵣ vals .x22)) := by
  simp [wclhFrame, regsAt, sepConj_emp_right']

private theorem regsOwnAt_wclhFrame :
    regsOwnAt wclhFrame =
      (regOwn .x1 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
        regOwn .x20 ** regOwn .x21 ** regOwn .x22) := by
  simp [wclhFrame, regsOwnAt, sepConj_emp_right']

private theorem ent_own8 (r1 r2 r3 r4 r5 r6 r7 r8 : Reg)
    (w1 w2 w3 w4 w5 w6 w7 w8 : Word) (P : Assertion) (h : PartialState)
    (hp : ((r1 ↦ᵣ w1) ** (r2 ↦ᵣ w2) ** (r3 ↦ᵣ w3) ** (r4 ↦ᵣ w4) ** (r5 ↦ᵣ w5) **
      (r6 ↦ᵣ w6) ** (r7 ↦ᵣ w7) ** (r8 ↦ᵣ w8) ** P) h) :
    (regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 ** regOwn r5 ** regOwn r6 **
      regOwn r7 ** regOwn r8 ** P) h :=
  sepConj_mono (regIs_to_regOwn r1 w1)
    (sepConj_mono (regIs_to_regOwn r2 w2)
      (sepConj_mono (regIs_to_regOwn r3 w3)
        (sepConj_mono (regIs_to_regOwn r4 w4)
          (sepConj_mono (regIs_to_regOwn r5 w5)
            (sepConj_mono (regIs_to_regOwn r6 w6)
              (sepConj_mono (regIs_to_regOwn r7 w7)
                (sepConj_mono (regIs_to_regOwn r8 w8) (fun _ hx => hx)))))))) h hp

/-- **The body in `abiFrame_spec_own` shape.** -/
private theorem wclhEmptySectionBody (newSp : Word) (vals : Reg → Word)
    (v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax nMiss : Word) :
    cpsTripleWithin 33
      (wclhB + BitVec.ofNat 64 (4 * (1 + wclhFrame.length)))
      (wclhB + BitVec.ofNat 64 (4 * (1 + wclhFrame.length + wclhBody.length))) wclhCr
      ((((.x2 : Reg) ↦ᵣ newSp) ** regsAt wclhFrame vals **
        frameSlotsSaved wclhFrame newSp vals **
        wclhArgs v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax nMiss))
      ((((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt wclhFrame **
        frameSlotsSaved wclhFrame newSp vals **
        wclhMissOut hashPtr outOffP outLenP nCalls nLin nMax nMiss)) := by
  rw [wclhFrame_length, wclhBody_length]
  simp only [show 4 * (1 + 8) = 36 from rfl, show 4 * (1 + 8 + 136) = 580 from rfl]
  have core := wclhEmptySectionBody_core secPtr hashPtr outOffP outLenP v5 v6
    (vals .x8) (vals .x9) (vals .x18) (vals .x19) (vals .x20) nCalls nLin nLast nMax nMiss
  have framed := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) ** ((.x1 : Reg) ↦ᵣ vals .x1) **
      ((.x21 : Reg) ↦ᵣ vals .x21) ** ((.x22 : Reg) ↦ᵣ vals .x22) **
      frameSlotsSaved wclhFrame newSp vals) (by pcf) core
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) framed
  · rw [regsAt_wclhFrame] at hp
    unfold wclhArgs at hp
    xperm_hyp hp
  · show ((((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt wclhFrame **
      frameSlotsSaved wclhFrame newSp vals **
      wclhMissOut hashPtr outOffP outLenP nCalls nLin nMax nMiss)) h
    rw [regsOwnAt_wclhFrame]
    unfold wclhMissOut
    have hq2 : (((.x1 : Reg) ↦ᵣ vals .x1) ** ((.x8 : Reg) ↦ᵣ secPtr) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ hashPtr) **
        ((.x19 : Reg) ↦ᵣ outOffP) ** ((.x20 : Reg) ↦ᵣ outLenP) **
        ((.x21 : Reg) ↦ᵣ vals .x21) ** ((.x22 : Reg) ↦ᵣ vals .x22) **
        (((.x2 : Reg) ↦ᵣ newSp) ** frameSlotsSaved wclhFrame newSp vals **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ LinMissLoc) **
          ((.x6 : Reg) ↦ᵣ (nMiss + 1)) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
          ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
          ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
          (CallsLoc ↦ₘ (nCalls + 1)) ** (WcidxEnLoc ↦ₘ (0 : Word)) **
          (LinCallsLoc ↦ₘ (nLin + 1)) ** (LinLastLoc ↦ₘ (0 : Word)) **
          (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ (nMiss + 1)))) h := by
      xperm_hyp hq
    have hq3 := ent_own8 .x1 .x8 .x9 .x18 .x19 .x20 .x21 .x22
      (vals .x1) secPtr (0 : Word) hashPtr outOffP outLenP (vals .x21) (vals .x22) _ h hq2
    xperm_hyp hq3

/-- **`witness_codes_lookup_by_hash`, whole routine, at its linked guest address —
    on the `section_len = 0` domain.**

    From the routine's entry `GuestAddrs.witness_codes_lookup_by_hash`, over the
    emitted program itself (`wclhCr = CodeReq.ofProg wclhB
    witnessCodesLookupByHash_prog`), execution returns to the caller in at most 52
    steps with:

    * `a0 = 1` — the documented "`section_len = 0` ⇒ guaranteed miss";
    * every callee-saved register (`ra`, `s0`…`s6`) back at its ENTRY value
      and `sp` back at `sp0` — derived from `abiFrame_spec_own`, not assumed;
    * the caller's two out cells NEVER MENTIONED, hence untouched by the
      frame rule: a miss must not publish an offset or a length;
    * the six `.data` cells at their exact new values.

    Hypotheses are ABI/resource facts only: a two-byte-aligned return address
    held in `ra` at entry, and the 64-byte frame slots owned. The domain
    restriction is `a1 = 0` together with `wcidx_enabled = 0` — an
    INPUT-DOMAIN gate. There is deliberately no upper bound on `section_len`
    anywhere in this file (`WitnessCodeLookup.lean`'s docstring records what a
    size cap here once broke). -/
theorem witness_codes_lookup_by_hash_spec_within_empty_section
    (sp0 ret : Word) (vals : Reg → Word)
    (v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax nMiss : Word)
    (hret : vals .x1 = ret)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 52 wclhB ret wclhCr
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt wclhFrame vals **
        frameSlotsOwn wclhFrame (sp0 + signExtend12 (-64 : BitVec 12)) **
        wclhArgs v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax nMiss)
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt wclhFrame vals **
        frameSlotsSaved wclhFrame (sp0 + signExtend12 (-64 : BitVec 12)) vals **
        wclhMissOut hashPtr outOffP outLenP nCalls nLin nMax nMiss) := by
  have h := abiFrame_spec_own wclhB sp0 ret (-64 : BitVec 12) (64 : BitVec 12)
    wclhFrame (0 : BitVec 12)
    [(.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12)), (.x18, (24 : BitVec 12)),
     (.x19, (32 : BitVec 12)), (.x20, (40 : BitVec 12)), (.x21, (48 : BitVec 12)),
     (.x22, (56 : BitVec 12))]
    vals wclhBody 33
    (wclhArgs v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax nMiss)
    (wclhMissOut hashPtr outOffP outLenP nCalls nLin nMax nMiss)
    wclhCr rfl (by decide) (by decide)
    (by rw [wclh_abiFrame_byte_tie]; decide)
    hret halign (sext_frameRestore _ _ _ (by decide))
    (wclhArgs_pcFree _ _ _ _ _ _ _ _ _ _ _) (wclhMissOut_pcFree _ _ _ _ _ _ _)
    (by rw [wclh_abiFrame_byte_tie]; unfold wclhCr; code_mem)
    (wclhEmptySectionBody _ vals v5 v6 secPtr hashPtr outOffP outLenP
      nCalls nLin nLast nMax nMiss)
  rw [wclhFrame_length] at h
  exact h

/-! ## §7  Non-vacuity -/

/-- Sample entry values for the eight callee-saved registers — pairwise
    distinct, so the post's "restored to its ENTRY value" claim is
    discriminating rather than satisfied by a constant. -/
def wclhSampleVals : Reg → Word
  | .x1 => (0x80006300 : Word)
  | .x8 => (0x101 : Word)
  | .x9 => (0x202 : Word)
  | .x18 => (0x303 : Word)
  | .x19 => (0x404 : Word)
  | .x20 => (0x505 : Word)
  | .x21 => (0x606 : Word)
  | .x22 => (0x707 : Word)
  | _ => (0 : Word)

/-- The six `.data` cells the routine's footprint names are pairwise
    distinct addresses, so the precondition's `**` chain is satisfiable —
    `wclhArgs` is not the empty assertion in disguise. -/
theorem wclhCells_distinct :
    CallsLoc ≠ WcidxEnLoc ∧ CallsLoc ≠ LinCallsLoc ∧ CallsLoc ≠ LinLastLoc ∧
    CallsLoc ≠ LinMaxLoc ∧ CallsLoc ≠ LinMissLoc ∧
    WcidxEnLoc ≠ LinCallsLoc ∧ WcidxEnLoc ≠ LinLastLoc ∧ WcidxEnLoc ≠ LinMaxLoc ∧
    WcidxEnLoc ≠ LinMissLoc ∧ LinCallsLoc ≠ LinLastLoc ∧ LinCallsLoc ≠ LinMaxLoc ∧
    LinCallsLoc ≠ LinMissLoc ∧ LinLastLoc ≠ LinMaxLoc ∧ LinLastLoc ≠ LinMissLoc ∧
    LinMaxLoc ≠ LinMissLoc := by
  unfold CallsLoc WcidxEnLoc LinCallsLoc LinLastLoc LinMaxLoc LinMissLoc
  decide

/-- ⭐ **A concrete satisfying instance of the whole-routine triple.**

    A closed instantiation: entry `sp = 0xa0050000`, return address
    `0x80006300`, the eight callee-saved registers holding eight DIFFERENT
    entry values, a zero-length section at `0x40000030`, a target hash at
    `0x40000010`, out cells at `0xa0010008`/`0xa0010010`, and telemetry
    counters starting at `(7, 3, 99, 4096, 5)`. Every hypothesis of
    `witness_codes_lookup_by_hash_spec_within_empty_section` is discharged here and
    the post is fully concrete — in particular `a0 = 1`,
    `wclh_linear_last_section_len` becomes `0` while
    `wclh_linear_max_section_len` stays `4096`. -/
theorem wclh_empty_section_sample_witness :
    cpsTripleWithin 52 wclhB (0x80006300 : Word) wclhCr
      (((.x2 : Reg) ↦ᵣ (0xa0050000 : Word)) ** regsAt wclhFrame wclhSampleVals **
        frameSlotsOwn wclhFrame ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12)) **
        wclhArgs (0 : Word) (0 : Word) (0x40000030 : Word) (0x40000010 : Word)
          (0xa0010008 : Word) (0xa0010010 : Word) (7 : Word) (3 : Word) (99 : Word)
          (4096 : Word) (5 : Word))
      (((.x2 : Reg) ↦ᵣ (0xa0050000 : Word)) ** regsAt wclhFrame wclhSampleVals **
        frameSlotsSaved wclhFrame
          ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12)) wclhSampleVals **
        wclhMissOut (0x40000010 : Word) (0xa0010008 : Word) (0xa0010010 : Word)
          (7 : Word) (3 : Word) (4096 : Word) (5 : Word)) :=
  witness_codes_lookup_by_hash_spec_within_empty_section (0xa0050000 : Word)
    (0x80006300 : Word) wclhSampleVals (0 : Word) (0 : Word) (0x40000030 : Word)
    (0x40000010 : Word) (0xa0010008 : Word) (0xa0010010 : Word) (7 : Word) (3 : Word)
    (99 : Word) (4096 : Word) (5 : Word) rfl (by decide)

/-! A concrete state witness was attempted alongside the closed triple. The
    scratch is intentionally retained as a starting point for the follow-up
    issue: its remaining obligation is the explicit nested `sepConj`
    disjointness proof for `regsAt`, `frameSlotsOwn`, and `wclhArgs`. It is
    now active and discharges that obligation with the inter-fold combinator;
    there is no `sorry` or `admit`. -/

def wclhSampleState : MachineState where
  regs := fun r =>
    match r with
    | .x1 => (0x80006300 : Word)
    | .x2 => (0xa0050000 : Word)
    | .x5 => 0
    | .x6 => 0
    | .x8 => (0x101 : Word)
    | .x9 => (0x202 : Word)
    | .x10 => (0x40000030 : Word)
    | .x11 => 0
    | .x12 => (0x40000010 : Word)
    | .x13 => (0xa0010008 : Word)
    | .x14 => (0xa0010010 : Word)
    | .x18 => (0x303 : Word)
    | .x19 => (0x404 : Word)
    | .x20 => (0x505 : Word)
    | .x21 => (0x606 : Word)
    | .x22 => (0x707 : Word)
    | _ => 0
  mem := fun a =>
    if a = ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (0 : BitVec 12)) then 0 else
    if a = ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (8 : BitVec 12)) then 0 else
    if a = ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (16 : BitVec 12)) then 0 else
    if a = ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (24 : BitVec 12)) then 0 else
    if a = ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (32 : BitVec 12)) then 0 else
    if a = ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (40 : BitVec 12)) then 0 else
    if a = ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (48 : BitVec 12)) then 0 else
    if a = ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (56 : BitVec 12)) then 0 else
    if a = CallsLoc then 7 else if a = WcidxEnLoc then 0 else
    if a = LinCallsLoc then 3 else if a = LinLastLoc then 99 else
    if a = LinMaxLoc then 4096 else if a = LinMissLoc then 5 else 0
  code := wclhCr
  pc := wclhB

private def wclhRegsPartial : PartialState :=
  PartialState.union (PartialState.singletonReg .x1 (0x80006300 : Word))
    (PartialState.union (PartialState.singletonReg .x8 (0x101 : Word))
      (PartialState.union (PartialState.singletonReg .x9 (0x202 : Word))
        (PartialState.union (PartialState.singletonReg .x18 (0x303 : Word))
          (PartialState.union (PartialState.singletonReg .x19 (0x404 : Word))
            (PartialState.union (PartialState.singletonReg .x20 (0x505 : Word))
              (PartialState.union (PartialState.singletonReg .x21 (0x606 : Word))
                (PartialState.union (PartialState.singletonReg .x22 (0x707 : Word))
                  PartialState.empty)))))))

private def wclhFramePartial : PartialState :=
  PartialState.union (PartialState.singletonMem
      ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (0 : BitVec 12)) 0)
    (PartialState.union (PartialState.singletonMem
      ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (8 : BitVec 12)) 0)
      (PartialState.union (PartialState.singletonMem
        ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (16 : BitVec 12)) 0)
        (PartialState.union (PartialState.singletonMem
          ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (24 : BitVec 12)) 0)
          (PartialState.union (PartialState.singletonMem
            ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (32 : BitVec 12)) 0)
            (PartialState.union (PartialState.singletonMem
              ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (40 : BitVec 12)) 0)
              (PartialState.union (PartialState.singletonMem
                ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (48 : BitVec 12)) 0)
                (PartialState.union (PartialState.singletonMem
                  ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (56 : BitVec 12)) 0)
                  PartialState.empty)))))))

private def wclhArgsPartial : PartialState :=
  PartialState.union (PartialState.singletonReg .x0 0)
    (PartialState.union (PartialState.singletonReg .x5 0)
      (PartialState.union (PartialState.singletonReg .x6 0)
        (PartialState.union (PartialState.singletonReg .x10 (0x40000030 : Word))
          (PartialState.union (PartialState.singletonReg .x11 0)
            (PartialState.union (PartialState.singletonReg .x12 (0x40000010 : Word))
              (PartialState.union (PartialState.singletonReg .x13 (0xa0010008 : Word))
                (PartialState.union (PartialState.singletonReg .x14 (0xa0010010 : Word))
                  (PartialState.union (PartialState.singletonMem CallsLoc 7)
                    (PartialState.union (PartialState.singletonMem WcidxEnLoc 0)
                      (PartialState.union (PartialState.singletonMem LinCallsLoc 3)
                        (PartialState.union (PartialState.singletonMem LinLastLoc 99)
                          (PartialState.union (PartialState.singletonMem LinMaxLoc 4096)
                            (PartialState.union (PartialState.singletonMem LinMissLoc 5)
                              PartialState.empty)))))))))))))

def wclhSamplePrePartial : PartialState :=
  PartialState.union (PartialState.singletonReg .x2 (0xa0050000 : Word))
    (PartialState.union wclhRegsPartial
      (PartialState.union wclhFramePartial wclhArgsPartial))

def wclhSampleState' : MachineState where
  regs := fun r => match wclhSamplePrePartial.regs r with | some v => v | none => 0
  mem := fun a => match wclhSamplePrePartial.mem a with | some v => v | none => 0
  code := wclhCr
  pc := wclhB

private theorem wclhSamplePrePartial_x0 :
    wclhSamplePrePartial.regs .x0 = some 0 := by
  decide

private theorem wclhSampleState'_getReg (r : Reg) (hr : r ≠ .x0) :
    wclhSampleState'.getReg r =
      (match wclhSamplePrePartial.regs r with | some v => v | none => 0) := by
  cases r <;> simp_all [wclhSampleState', MachineState.getReg]

private theorem wclhSampleState'_getMem (a : Word) :
    wclhSampleState'.getMem a =
      (match wclhSamplePrePartial.mem a with | some v => v | none => 0) := by
  rfl

private theorem wclhSamplePrePartial_code_none (a : Word) :
    wclhSamplePrePartial.code a = none := by
  rfl

private theorem wclhSamplePrePartial_pc_none : wclhSamplePrePartial.pc = none := by
  rfl

private theorem wclh_reg_disjoint_union
    {r : Reg} {v : Word} {h1 h2 : PartialState}
    (h1r : h1.regs r = none) (h2r : h2.regs r = none) :
    (PartialState.singletonReg r v).Disjoint (h1.union h2) := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r'
  by_cases heq : r' = r
  · subst r'
    right
    simp only [PartialState.union, h1r, h2r]
  · left
    simp only [PartialState.singletonReg]
    by_cases hbeq : (r' == r) = true
    · rw [beq_iff_eq] at hbeq
      exact (heq hbeq).elim
    · simp [hbeq]

private theorem wclh_mem_disjoint_union
    {a v : Word} {h1 h2 : PartialState}
    (h1a : h1.mem a = none) (h2a : h2.mem a = none) :
    (PartialState.singletonMem a v).Disjoint (h1.union h2) := by
  refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro a'
  by_cases heq : a' = a
  · subst a'
    right
    simp only [PartialState.union, h1a, h2a]
  · left
    simp only [PartialState.singletonMem]
    by_cases hbeq : (a' == a) = true
    · rw [beq_iff_eq] at hbeq
      exact (heq hbeq).elim
    · simp [hbeq]

private theorem wclh_reg_reg_disjoint {r1 r2 : Reg} {v1 v2 : Word}
    (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint
      (PartialState.singletonReg r2 v2) := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r
  by_cases h : r = r1
  · subst r; right; simp [PartialState.singletonReg, hne]
  · left; simp [PartialState.singletonReg, h]

private theorem wclh_mem_mem_disjoint {a1 a2 : Word} {v1 v2 : Word}
    (hne : a1 ≠ a2) :
    (PartialState.singletonMem a1 v1).Disjoint
      (PartialState.singletonMem a2 v2) := by
  refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro a
  by_cases h : a = a1
  · subst a; right; simp [PartialState.singletonMem, hne]
  · left; simp [PartialState.singletonMem, h]

private theorem wclh_reg_mem_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem wclh_mem_reg_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonMem a v).Disjoint
      (PartialState.singletonReg r w) := by
  exact wclh_reg_mem_disjoint.symm

private structure WclhMem where
  a : Word
  v : Word
  valid : isValidDwordAccess a = true

private inductive WclhAtom where
  | reg (r : Reg) (v : Word)
  | mem (m : WclhMem)
  | own (m : WclhMem)

private def wclhAtomAssertion : WclhAtom → Assertion
  | .reg r v => regIs r v
  | .mem m => memIs m.a m.v
  | .own m => memOwn m.a

private def wclhAtomHeap : WclhAtom → PartialState
  | .reg r v => PartialState.singletonReg r v
  | .mem m => PartialState.singletonMem m.a m.v
  | .own m => PartialState.singletonMem m.a 0

private inductive WclhResource where
  | reg (r : Reg)
  | mem (a : Word)
  deriving DecidableEq

private def wclhAtomResource : WclhAtom → WclhResource
  | .reg r _ => .reg r
  | .mem m => .mem m.a
  | .own m => .mem m.a

private theorem wclhAtomHeap_disjoint_of_resource_ne {x y : WclhAtom}
    (h : wclhAtomResource x ≠ wclhAtomResource y) :
    (wclhAtomHeap x).Disjoint (wclhAtomHeap y) := by
  cases x <;> cases y
  · apply wclh_reg_reg_disjoint
    simpa [wclhAtomResource] using h
  · exact wclh_reg_mem_disjoint
  · exact wclh_reg_mem_disjoint
  · exact wclh_mem_reg_disjoint
  · apply wclh_mem_mem_disjoint
    simpa [wclhAtomResource] using h
  · apply wclh_mem_mem_disjoint
    simpa [wclhAtomResource] using h
  · exact wclh_mem_reg_disjoint
  · apply wclh_mem_mem_disjoint
    simpa [wclhAtomResource] using h
  · apply wclh_mem_mem_disjoint
    simpa [wclhAtomResource] using h

private def wclhLeftAtoms : List WclhAtom :=
  [.reg .x2 (0xa0050000 : Word)]

private def wclhRightAtoms : List WclhAtom :=
  [.reg .x1 (0x80006300 : Word), .reg .x8 (0x101 : Word),
   .reg .x9 (0x202 : Word), .reg .x18 (0x303 : Word),
   .reg .x19 (0x404 : Word), .reg .x20 (0x505 : Word),
   .reg .x21 (0x606 : Word), .reg .x22 (0x707 : Word),
   .own ⟨(0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (0 : BitVec 12), 0, by decide⟩,
   .own ⟨(0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (8 : BitVec 12), 0, by decide⟩,
   .own ⟨(0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (16 : BitVec 12), 0, by decide⟩,
   .own ⟨(0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (24 : BitVec 12), 0, by decide⟩,
   .own ⟨(0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (32 : BitVec 12), 0, by decide⟩,
   .own ⟨(0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (40 : BitVec 12), 0, by decide⟩,
   .own ⟨(0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (48 : BitVec 12), 0, by decide⟩,
   .own ⟨(0xa0050000 : Word) + signExtend12 (-64 : BitVec 12) + signExtend12 (56 : BitVec 12), 0, by decide⟩,
   .reg .x0 0, .reg .x5 0, .reg .x6 0,
   .reg .x10 (0x40000030 : Word), .reg .x11 0,
   .reg .x12 (0x40000010 : Word), .reg .x13 (0xa0010008 : Word),
   .reg .x14 (0xa0010010 : Word),
   .mem ⟨CallsLoc, 7, by decide⟩, .mem ⟨WcidxEnLoc, 0, by decide⟩,
   .mem ⟨LinCallsLoc, 3, by decide⟩, .mem ⟨LinLastLoc, 99, by decide⟩,
   .mem ⟨LinMaxLoc, 4096, by decide⟩, .mem ⟨LinMissLoc, 5, by decide⟩]

private theorem wclh_left_hsat :
    (wclhLeftAtoms.foldr (fun x acc => wclhAtomAssertion x ** acc) empAssertion)
      (wclhLeftAtoms.foldr (fun x acc => (wclhAtomHeap x).union acc)
        PartialState.empty) := by
  apply sepConj_foldr_satisfiable wclhAtomAssertion wclhAtomHeap
    wclhLeftAtoms
  · intro x hx
    cases x with
    | reg r v => exact rfl
    | mem m => exact ⟨rfl, m.valid⟩
    | own m => exact ⟨0, rfl, m.valid⟩
  · apply List.Pairwise.imp (fun {x y} h =>
      wclhAtomHeap_disjoint_of_resource_ne h)
    decide

private theorem wclh_right_hsat :
    (wclhRightAtoms.foldr (fun x acc => wclhAtomAssertion x ** acc) empAssertion)
      (wclhRightAtoms.foldr (fun x acc => (wclhAtomHeap x).union acc)
        PartialState.empty) := by
  apply sepConj_foldr_satisfiable wclhAtomAssertion wclhAtomHeap
    wclhRightAtoms
  · intro x hx
    cases x with
    | reg r v => exact rfl
    | mem m => exact ⟨rfl, m.valid⟩
    | own m => exact ⟨0, rfl, m.valid⟩
  · apply List.Pairwise.imp (fun {x y} h =>
      wclhAtomHeap_disjoint_of_resource_ne h)
    decide

private theorem wclh_cross_hdisjoint :
    ∀ x ∈ wclhLeftAtoms, ∀ y ∈ wclhRightAtoms,
      (wclhAtomHeap x).Disjoint (wclhAtomHeap y) := by
  have hpair : (wclhLeftAtoms ++ wclhRightAtoms).Pairwise
      (fun x y => wclhAtomResource x ≠ wclhAtomResource y) := by decide
  intro x hx y hy
  apply wclhAtomHeap_disjoint_of_resource_ne
  exact (List.pairwise_append.mp hpair).2.2 x hx y hy

private theorem wclh_union_assoc (h1 h2 h3 : PartialState) :
    (h1.union h2).union h3 = h1.union (h2.union h3) := by
  rcases h1 with ⟨regs1, mem1, code1, pc1, publicValues1, privateInput1, inputBufBase1⟩
  rcases h2 with ⟨regs2, mem2, code2, pc2, publicValues2, privateInput2, inputBufBase2⟩
  rcases h3 with ⟨regs3, mem3, code3, pc3, publicValues3, privateInput3, inputBufBase3⟩
  simp only [PartialState.union]
  rw [PartialState.mk.injEq]
  constructor
  · funext r
    cases h1r : regs1 r <;> cases h2r : regs2 r <;> rfl
  constructor
  · funext a
    cases h1a : mem1 a <;> cases h2a : mem2 a <;> rfl
  constructor
  · funext a
    cases h1a : code1 a <;> cases h2a : code2 a <;> rfl
  constructor
  · cases h1p : pc1 <;> cases h2p : pc2 <;> rfl
  constructor
  · cases h1p : publicValues1 <;> cases h2p : publicValues2 <;> rfl
  constructor
  · cases h1p : privateInput1 <;> cases h2p : privateInput2 <;> rfl
  · cases h1p : inputBufBase1 <;> cases h2p : inputBufBase2 <;> rfl

theorem wclh_sample_entryState_exists :
    wclhSampleState'.pc = wclhB ∧
    wclhCr.SatisfiedBy wclhSampleState' ∧
    (((.x2 : Reg) ↦ᵣ (0xa0050000 : Word)) ** regsAt wclhFrame wclhSampleVals **
      frameSlotsOwn wclhFrame ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12)) **
      wclhArgs (0 : Word) (0 : Word) (0x40000030 : Word) (0x40000010 : Word)
        (0xa0010008 : Word) (0xa0010010 : Word) (7 : Word) (3 : Word) (99 : Word)
        (4096 : Word) (5 : Word)).holdsFor wclhSampleState' := by
  constructor
  · rfl
  constructor
  · intro a i h
    exact h
  · refine ⟨wclhSamplePrePartial, ?_, ?_⟩
    · change
        (∀ r v, wclhSamplePrePartial.regs r = some v →
          (wclhSampleState'.getReg r = v)) ∧
        (∀ a v, wclhSamplePrePartial.mem a = some v →
          wclhSampleState'.getMem a = v) ∧
        (∀ a i, wclhSamplePrePartial.code a = some i →
          wclhSampleState'.code a = some i) ∧
        (∀ v, wclhSamplePrePartial.pc = some v →
          wclhSampleState'.pc = v) ∧
        (∀ v, wclhSamplePrePartial.publicValues = some v →
          wclhSampleState'.publicValues = v) ∧
        (∀ v, wclhSamplePrePartial.privateInput = some v →
          wclhSampleState'.privateInput = v) ∧
        (∀ v, wclhSamplePrePartial.inputBufBase = some v →
          wclhSampleState'.inputBufBase = v)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro r v h
        by_cases hr : r = .x0
        · subst r
          rw [wclhSamplePrePartial_x0] at h
          simp only [MachineState.getReg]
          simpa using h
        · rw [wclhSampleState'_getReg r hr, h]
      · intro a v h
        rw [wclhSampleState'_getMem a, h]
      · intro a i h
        rw [wclhSamplePrePartial_code_none a] at h
        cases h
      · intro v h
        rw [wclhSamplePrePartial_pc_none] at h
        cases h
      · intro v h; cases h
      · intro v h; cases h
      · intro v h; cases h
    · have hfold := sepConj_foldr_cross_satisfiable
          wclhAtomAssertion wclhAtomHeap wclhLeftAtoms
          wclhAtomAssertion wclhAtomHeap wclhRightAtoms
          wclh_left_hsat wclh_right_hsat wclh_cross_hdisjoint
      have hs0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
      have hs8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
      have hs16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
      have hs24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
      have hs32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
      have hs40 : signExtend12 (40 : BitVec 12) = (40 : Word) := by decide
      have hs48 : signExtend12 (48 : BitVec 12) = (48 : Word) := by decide
      have hs56 : signExtend12 (56 : BitVec 12) = (56 : Word) := by decide
      have hheap :
          (wclhLeftAtoms.foldr (fun x acc => (wclhAtomHeap x).union acc)
              PartialState.empty).union
            (wclhRightAtoms.foldr (fun x acc => (wclhAtomHeap x).union acc)
              PartialState.empty) = wclhSamplePrePartial := by
        simp [wclhLeftAtoms, wclhRightAtoms, wclhAtomHeap,
          wclhSamplePrePartial, wclhRegsPartial, wclhFramePartial,
          wclhArgsPartial, PartialState.union_empty_right, wclh_union_assoc]
      rw [hheap] at hfold
      unfold wclhFrame regsAt frameSlotsOwn wclhArgs
      simpa [wclhLeftAtoms, wclhRightAtoms, wclhAtomAssertion,
        wclhAtomHeap, wclhFrame, regsAt, frameSlotsOwn, wclhArgs,
        wclhSampleVals, addr_add_zero_bv, wclh_union_assoc,
        hs0, hs8, hs16, hs24, hs32, hs40, hs48, hs56,
        sepConj_assoc', sepConj_emp_right'] using hfold


/-! ## §9  Code-index builder: unclaimed scaffolding

    The builder definitions below are only the linked `CodeReq`, frame, and
    cell vocabulary needed for a future proof. No builder whole-routine
    theorem is claimed here, and the empty-section arm is deliberately left
    unclaimed until its state and validation contracts are available.
-/

def wcbB : Word := (GuestAddrs.witness_codes_index_build : Word)

def wcbCr : CodeReq := CodeReq.ofProg wcbB witnessCodesIndexBuild_prog

def wcbFrame : FrameDesc :=
  [(.x1, (0 : BitVec 12)), (.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12)),
   (.x18, (24 : BitVec 12)), (.x19, (32 : BitVec 12)), (.x20, (40 : BitVec 12)),
   (.x21, (48 : BitVec 12)), (.x22, (56 : BitVec 12)), (.x23, (64 : BitVec 12)),
   (.x24, (72 : BitVec 12)), (.x25, (80 : BitVec 12))]

def wcbBody : List Instr := (witnessCodesIndexBuild_prog.drop 12).take 133

theorem wcb_abiFrame_byte_tie :
    abiFrameProg (-96 : BitVec 12) (96 : BitVec 12) wcbFrame wcbBody =
      witnessCodesIndexBuild_prog := by
  decide

theorem wcbBody_length : wcbBody.length = 133 := by decide

theorem wcbFrame_length : wcbFrame.length = 11 := by decide

private theorem wcbClear_spec (A C v : Word)
    (hrange : laInRange A C)
    (hau : ∀ a i, CodeReq.singleton A (.AUIPC .x5 (Rv64.laHi A C)) a = some i →
      wcbCr a = some i)
    (had : ∀ a i, CodeReq.singleton (A + 4) (.ADDI .x5 .x5 (Rv64.laLo A C)) a = some i →
      wcbCr a = some i)
    (hsd : ∀ a i, CodeReq.singleton (A + 8) (.SD .x5 .x0 (0 : BitVec 12)) a = some i →
      wcbCr a = some i) :
    cpsTripleWithin 3 A (A + 12) wcbCr
      (((.x5 : Reg) ↦ᵣ v) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** memOwn C)
      (((.x5 : Reg) ↦ᵣ C) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (C ↦ₘ (0 : Word))) := by
  have hla := la_materialize_within .x5 v A C (by decide) hrange hau had
  have hstore := liftCode (cr' := wcbCr)
    (sd_spec_gen_own_within .x5 .x0 C (0 : Word) (0 : BitVec 12) (A + 8)) hsd
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show C + (0 : Word) = C from by bv_omega,
    show (A + 8 : Word) + 4 = A + 12 from by bv_omega] at hstore
  have hf := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** memOwn C) (by pcf) hla
  exact cpsTripleWithin_mono_nSteps (show 2 + 1 ≤ 3 by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_seq_same_cr hf hstore))

def WcbEnabledLoc : Word := (GuestAddrs.wcidx_enabled : Word)
def WcbBuildStatusLoc : Word := (GuestAddrs.wcidx_build_status : Word)
def WcbBuildSectionLenLoc : Word := (GuestAddrs.wcidx_build_section_len : Word)
def WcbBuildCountLoc : Word := (GuestAddrs.wcidx_build_count : Word)
def WcbSectionPtrLoc : Word := (GuestAddrs.wcidx_section_ptr : Word)
def WcbSectionLenLoc : Word := (GuestAddrs.wcidx_section_len : Word)
def WcbCountLoc : Word := (GuestAddrs.wcidx_count : Word)
def WcbLookupCallsLoc : Word := (GuestAddrs.wclh_lookup_calls : Word)
def WcbIndexedCallsLoc : Word := (GuestAddrs.wclh_indexed_calls : Word)
def WcbIndexedHitsLoc : Word := (GuestAddrs.wclh_indexed_hits : Word)
def WcbIndexedMissesLoc : Word := (GuestAddrs.wclh_indexed_misses : Word)
def WcbLinearCallsLoc : Word := (GuestAddrs.wclh_linear_calls : Word)
def WcbLinearHitsLoc : Word := (GuestAddrs.wclh_linear_hits : Word)
def WcbLinearMissesLoc : Word := (GuestAddrs.wclh_linear_misses : Word)
def WcbLinearIterationsLoc : Word := (GuestAddrs.wclh_linear_iterations : Word)
def WcbLinearLastLenLoc : Word := (GuestAddrs.wclh_linear_last_section_len : Word)
def WcbLinearMaxLenLoc : Word := (GuestAddrs.wclh_linear_max_section_len : Word)

def wcbInitCells (en status buildLen buildCount lookup indexedCall indexedHit indexedMiss
    linearCall linearHit linearMiss linearIter linearLast linearMax : Word) : Assertion :=
  (WcbEnabledLoc ↦ₘ en) ** (WcbBuildStatusLoc ↦ₘ status) **
  (WcbBuildSectionLenLoc ↦ₘ buildLen) ** (WcbBuildCountLoc ↦ₘ buildCount) **
  (WcbLookupCallsLoc ↦ₘ lookup) ** (WcbIndexedCallsLoc ↦ₘ indexedCall) **
  (WcbIndexedHitsLoc ↦ₘ indexedHit) ** (WcbIndexedMissesLoc ↦ₘ indexedMiss) **
  (WcbLinearCallsLoc ↦ₘ linearCall) ** (WcbLinearHitsLoc ↦ₘ linearHit) **
  (WcbLinearMissesLoc ↦ₘ linearMiss) ** (WcbLinearIterationsLoc ↦ₘ linearIter) **
  (WcbLinearLastLenLoc ↦ₘ linearLast) ** (WcbLinearMaxLenLoc ↦ₘ linearMax)

def wcbFinalCells (sectionPtr sectionLen : Word) : Assertion :=
  (WcbSectionPtrLoc ↦ₘ sectionPtr) ** (WcbSectionLenLoc ↦ₘ sectionLen) **
  (WcbCountLoc ↦ₘ (0 : Word)) ** (WcbEnabledLoc ↦ₘ (1 : Word))

theorem wcb_cells_distinct :
    WcbEnabledLoc ≠ WcbBuildStatusLoc ∧ WcbEnabledLoc ≠ WcbBuildSectionLenLoc ∧
    WcbEnabledLoc ≠ WcbBuildCountLoc ∧ WcbEnabledLoc ≠ WcbSectionPtrLoc ∧
    WcbEnabledLoc ≠ WcbSectionLenLoc ∧ WcbEnabledLoc ≠ WcbCountLoc ∧
    WcbBuildStatusLoc ≠ WcbBuildSectionLenLoc ∧ WcbBuildStatusLoc ≠ WcbBuildCountLoc ∧
    WcbBuildStatusLoc ≠ WcbSectionPtrLoc ∧ WcbBuildStatusLoc ≠ WcbSectionLenLoc ∧
    WcbBuildStatusLoc ≠ WcbCountLoc ∧ WcbBuildSectionLenLoc ≠ WcbBuildCountLoc ∧
    WcbBuildSectionLenLoc ≠ WcbSectionPtrLoc ∧ WcbBuildSectionLenLoc ≠ WcbSectionLenLoc ∧
    WcbBuildSectionLenLoc ≠ WcbCountLoc ∧ WcbBuildCountLoc ≠ WcbSectionPtrLoc ∧
    WcbBuildCountLoc ≠ WcbSectionLenLoc ∧ WcbBuildCountLoc ≠ WcbCountLoc ∧
    WcbSectionPtrLoc ≠ WcbSectionLenLoc ∧ WcbSectionPtrLoc ≠ WcbCountLoc ∧
    WcbSectionLenLoc ≠ WcbCountLoc := by
  unfold WcbEnabledLoc WcbBuildStatusLoc WcbBuildSectionLenLoc WcbBuildCountLoc
    WcbSectionPtrLoc WcbSectionLenLoc WcbCountLoc
  decide



end EvmAsm.Codegen.WitnessCodesLookupSpec
