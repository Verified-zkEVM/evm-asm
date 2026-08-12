/-
  EvmAsm.Codegen.Programs.WitnessLookupByHashSpec

  **Machine facts for the guest routine `witness_lookup_by_hash`** (GH #12036).

  `witnessLookupByHash_prog` (`MptWitnessLookup.lean`, 155 instructions) was
  transcribed in #12111 specifically so a `cpsTripleWithin` over the real
  linked program could be STATED. This module is the first tranche of that
  triple.

  ## §A  What is established here

  * `wlh_abiFrame_byte_tie` — the routine IS a standard 8-slot ABI frame
    around a 136-instruction body, so `abiFrame_spec_own` applies and the
    prologue/epilogue (`ra`, `s0`, `s1`, `s2`…`s6` save/restore, `sp`
    round-trip) are DERIVED, not assumed.
  * `wlhCounterBump_spec` — the five-instruction telemetry idiom
    (`la t0,C ; ld t1,0(t0) ; addi t1,t1,1 ; sd t1,0(t0)`) that occurs at
    EIGHT sites in this routine (instruction indices 14, 36, 43, 49, 55,
    96, 130, 139), proved once at a free `(A, C)`.
  * `witness_lookup_by_hash_spec_within_empty_section` — the **whole-routine
    triple**, entry `GuestAddrs.witness_lookup_by_hash` to the caller's
    return address, over `CodeReq.ofProg` of the real program, for the
    documented `section_len = 0 ⇒ guaranteed miss` domain with the witness
    index disabled. It pins `a0 = 1`, the callee-saved registers restored,
    the caller's out cells UNTOUCHED, and all six telemetry cells to their
    exact updated values.

  ## §B  What is NOT established (read before citing this module)

  The scan loop (`+308 … +552`), the SSZ offset-table guards (`+272 … +304`)
  and BOTH cross-`jal` arms are outside the claim:

  * `witness_lookup_by_hash_indexed` (idx 41) and `zkvm_keccak256` (idx 101)
    have no machine triple. On the domain proved here neither is REACHED
    (the `widx_enabled = 0` test at idx 22 jumps over the first, and the
    `section_len = 0` test at idx 68 jumps over the loop that contains the
    second), so this theorem carries no unproven-callee dependency — but the
    general routine does, and any extension of this proof past those two
    branches must carry the callee contracts as explicit hypotheses.
  * The size subtlety in `MptWitnessLookup.lean`'s docstring is respected:
    NOTHING here bounds `section_len` from above. The gate is
    `section_len = 0`, an input-domain restriction, not a size cap.

  ## §C  The `wlCallWithinShape` residual (#12144 status)

  `MptWalkResiduals.wlCallWithinShape` is the named residual at the three
  MPT-walk call sites. Blocker 1 (callee absent from walk `fullCode`) is
  **retired**: `MptWalkSpec.fullCode` now unions `wlhCr` and
  `MptWalkSpec.wlh_entry_in_walk_fullCode` witnesses membership.
  Blocker 2 (telemetry cells absent from the *generic* residual entry) is
  **retired** (#12144 half-2): generic `wlCallEntry`/`wlCallReturn` carry all
  six telemetry cells; three sites establish generic `wlCallWithinShape` via
  `MptWalkWlEmpty` applying `wlhCallWithin_empty_section` (no free `h_wl`).
  SAY SO: only `section_len = 0` / `widx_enabled = 0` miss domain.
  Hit-domain residual (`wlCallWithinShapeHit`) remains a DEPENDENCY until a
  hit machine triple lands.
-/

import EvmAsm.Codegen.Programs.MptWitnessLookup
import EvmAsm.Codegen.Programs.MptWalkResiduals
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.WitnessLookupByHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

/-! ## §1  The linked routine -/

/-- The routine's linked entry (`GuestAddrs.witness_lookup_by_hash`). -/
def wlhB : Word := (GuestAddrs.witness_lookup_by_hash : Word)

/-- The routine's own code requirement: the 155-instruction emitted program
    at its linked address. Every triple below is stated over this, so the
    machine is named in each of them. -/
def wlhCr : CodeReq := CodeReq.ofProg wlhB witnessLookupByHash_prog

/-- The 8-slot callee-save frame: `ra` plus `s0,s1,s2,s3,s4,s5,s6`
    (`x8,x9,x18,x19,x20,x21,x22`), 64 bytes. -/
def wlhFrame : FrameDesc :=
  [(.x1, (0 : BitVec 12)), (.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12)),
   (.x18, (24 : BitVec 12)), (.x19, (32 : BitVec 12)), (.x20, (40 : BitVec 12)),
   (.x21, (48 : BitVec 12)), (.x22, (56 : BitVec 12))]

/-- The framed body: instructions 9 … 144, i.e. everything between the
    prologue's last `sd` and the epilogue's first `ld`. -/
def wlhBody : List Instr := (witnessLookupByHash_prog.drop 9).take 136

/-- **The routine is an ABI frame around `wlhBody`.** Kernel-checked against
    the emitted program, so callee-saved preservation and the `sp`
    round-trip come from `abiFrame_spec_own` rather than being assumed. -/
theorem wlh_abiFrame_byte_tie :
    abiFrameProg (-64 : BitVec 12) (64 : BitVec 12) wlhFrame wlhBody =
      witnessLookupByHash_prog := by
  decide

theorem wlhBody_length : wlhBody.length = 136 := by decide

theorem wlhFrame_length : wlhFrame.length = 8 := by decide

/-! ## §2  The `.data` cells the routine reads and writes

    Six telemetry/dispatch cells lie on the `section_len = 0` path. They are
    part of the routine's FOOTPRINT: the pre must own them, or the frame rule
    is violated. -/

/-- `wlh_lookup_calls` — bumped on every call. -/
def CallsLoc : Word := (GuestAddrs.wlh_lookup_calls : Word)
/-- `widx_enabled` — the index-dispatch flag (read only). -/
def WidxEnLoc : Word := (GuestAddrs.widx_enabled : Word)
/-- `wlh_linear_calls` — bumped on every linear-path call. -/
def LinCallsLoc : Word := (GuestAddrs.wlh_linear_calls : Word)
/-- `wlh_linear_last_section_len` — overwritten with this call's length. -/
def LinLastLoc : Word := (GuestAddrs.wlh_linear_last_section_len : Word)
/-- `wlh_linear_max_section_len` — kept at the running maximum. -/
def LinMaxLoc : Word := (GuestAddrs.wlh_linear_max_section_len : Word)
/-- `wlh_linear_misses` — bumped when the linear path reports a miss. -/
def LinMissLoc : Word := (GuestAddrs.wlh_linear_misses : Word)

/-! ## §3  The telemetry-counter idiom

    `la t0, C ; ld t1, 0(t0) ; addi t1, t1, 1 ; sd t1, 0(t0)` — five
    instructions; three of the eight occurrences in this routine are on the
    `section_len = 0` path. Proved once, at a free `(A, C)`. -/

private theorem sext12_zero : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem sext12_one : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide

/-- **One telemetry bump**, at a free bump address `A` and free cell `C`.
    Code membership is hypothesis-shaped so each call site discharges it by
    evaluation against `wlhCr`. -/
theorem wlhCounterBump_spec (A C : Word) (v5 v6 n : Word)
    (hrange : laInRange A C)
    (hau : ∀ a i, CodeReq.singleton A (.AUIPC .x5 (Rv64.laHi A C)) a = some i →
      wlhCr a = some i)
    (had : ∀ a i, CodeReq.singleton (A + 4) (.ADDI .x5 .x5 (Rv64.laLo A C)) a = some i →
      wlhCr a = some i)
    (hld : ∀ a i, CodeReq.singleton (A + 8) (.LD .x6 .x5 (0 : BitVec 12)) a = some i →
      wlhCr a = some i)
    (hai : ∀ a i, CodeReq.singleton (A + 12) (.ADDI .x6 .x6 (1 : BitVec 12)) a = some i →
      wlhCr a = some i)
    (hsd : ∀ a i, CodeReq.singleton (A + 16) (.SD .x5 .x6 (0 : BitVec 12)) a = some i →
      wlhCr a = some i) :
    cpsTripleWithin 5 A (A + 20) wlhCr
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** (C ↦ₘ n))
      (((.x5 : Reg) ↦ᵣ C) ** ((.x6 : Reg) ↦ᵣ (n + 1)) ** (C ↦ₘ (n + 1))) := by
  have hla := la_materialize_within .x5 v5 A C (by decide) hrange hau had
  have h2 := liftCode (cr' := wlhCr)
    (ld_spec_gen_within .x6 .x5 C v6 n (0 : BitVec 12) (A + 8) (by decide)) hld
  rw [sext12_zero, show C + (0 : Word) = C from by bv_omega,
    show (A + 8 : Word) + 4 = A + 12 from by bv_omega] at h2
  have h3 := liftCode (cr' := wlhCr)
    (addi_spec_gen_same_within .x6 n (1 : BitVec 12) (A + 12) (by decide)) hai
  rw [sext12_one, show (A + 12 : Word) + 4 = A + 16 from by bv_omega] at h3
  have h4 := liftCode (cr' := wlhCr)
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

    Body entry is `wlhB + 36` (instruction 9, the first `mv`); body exit is
    `wlhB + 580` (instruction 145, the epilogue's first `ld`) — the address
    the routine's own `j` instructions target. Each segment below is stated
    with a TIGHT footprint (only what it touches); the composition frames the
    rest. -/

/-- **S1 — the argument moves** (idx 9…13): the five caller arguments are
    parked in the callee-saved registers the whole routine uses. Asymmetric
    by construction: `a0→s0`, `a1→s1`, `a2→s2`, `a3→s3`, `a4→s4` are five
    different pairs, so a swapped pair would not typecheck against the post. -/
theorem wlhArgMoves_spec (secPtr len hashPtr outOffP outLenP
    a8 a9 a18 a19 a20 : Word) :
    cpsTripleWithin 5 (wlhB + 36) (wlhB + 56) wlhCr
      (((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
        ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
        ((.x8 : Reg) ↦ᵣ a8) ** ((.x9 : Reg) ↦ᵣ a9) ** ((.x18 : Reg) ↦ᵣ a18) **
        ((.x19 : Reg) ↦ᵣ a19) ** ((.x20 : Reg) ↦ᵣ a20))
      (((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
        ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
        ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ hashPtr) **
        ((.x19 : Reg) ↦ᵣ outOffP) ** ((.x20 : Reg) ↦ᵣ outLenP)) := by
  have h9 := liftCode (cr' := wlhCr)
    (mv_spec_gen_within .x8 .x10 secPtr a8 (wlhB + 36) (by decide))
    (by unfold wlhCr; code_mem)
  rw [show (wlhB + 36 : Word) + 4 = wlhB + 40 from by bv_omega] at h9
  have h10 := liftCode (cr' := wlhCr)
    (mv_spec_gen_within .x9 .x11 len a9 (wlhB + 40) (by decide))
    (by unfold wlhCr; code_mem)
  rw [show (wlhB + 40 : Word) + 4 = wlhB + 44 from by bv_omega] at h10
  have h11 := liftCode (cr' := wlhCr)
    (mv_spec_gen_within .x18 .x12 hashPtr a18 (wlhB + 44) (by decide))
    (by unfold wlhCr; code_mem)
  rw [show (wlhB + 44 : Word) + 4 = wlhB + 48 from by bv_omega] at h11
  have h12 := liftCode (cr' := wlhCr)
    (mv_spec_gen_within .x19 .x13 outOffP a19 (wlhB + 48) (by decide))
    (by unfold wlhCr; code_mem)
  rw [show (wlhB + 48 : Word) + 4 = wlhB + 52 from by bv_omega] at h12
  have h13 := liftCode (cr' := wlhCr)
    (mv_spec_gen_within .x20 .x14 outLenP a20 (wlhB + 52) (by decide))
    (by unfold wlhCr; code_mem)
  rw [show (wlhB + 52 : Word) + 4 = wlhB + 56 from by bv_omega] at h13
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

/-- **S3 — the index dispatch** (idx 19…22): `widx_enabled` is read and, when
    it is zero, control jumps to the linear scan at `+220`. This is the
    branch that makes the `witness_lookup_by_hash_indexed` cross-`jal` (idx
    41) UNREACHED on this domain. -/
private theorem wlhWidxDispatch_spec (v5 : Word) :
    cpsTripleWithin 4 (wlhB + 76) (wlhB + 220) wlhCr
      (((.x5 : Reg) ↦ᵣ v5) ** (WidxEnLoc ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (((.x5 : Reg) ↦ᵣ (0 : Word)) ** (WidxEnLoc ↦ₘ (0 : Word)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word))) := by
  have hla := la_materialize_within .x5 v5 (wlhB + 76) WidxEnLoc (cr := wlhCr)
    (by decide) (by decide) (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem)
  rw [show (wlhB + 76 : Word) + 8 = wlhB + 84 from by bv_omega] at hla
  have hld := liftCode (cr' := wlhCr)
    (ld_spec_gen_same_within .x5 WidxEnLoc (0 : Word) (0 : BitVec 12) (wlhB + 84)
      (by decide))
    (by unfold wlhCr; code_mem)
  rw [sext12_zero, show WidxEnLoc + (0 : Word) = WidxEnLoc from by bv_omega,
    show (wlhB + 84 : Word) + 4 = wlhB + 88 from by bv_omega] at hld
  have hbr := cpsBranchWithin_extend_code (cr' := wlhCr)
    (by unfold wlhCr; code_mem)
    (beq_spec_gen_within .x5 .x0
      (brOff (GuestAddrs.witness_lookup_by_hash + 220)
        (GuestAddrs.witness_lookup_by_hash + 88)) (0 : Word) (0 : Word) (wlhB + 88))
  have hbt := cpsBranchWithin_takenStripPure2 hbr beq_same_absurd
  rw [show (wlhB + 88 : Word) + signExtend13
      (brOff (GuestAddrs.witness_lookup_by_hash + 220)
        (GuestAddrs.witness_lookup_by_hash + 88)) = wlhB + 220 from by decide] at hbt
  have f1 := cpsTripleWithin_frameR
    ((WidxEnLoc ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) (by pcf) hla
  have f2 := cpsTripleWithin_frameR (((.x0 : Reg) ↦ᵣ (0 : Word))) (by pcf) hld
  have f3 := cpsTripleWithin_frameR ((WidxEnLoc ↦ₘ (0 : Word))) (by pcf) hbt
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f1 f2
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 f3
  exact cpsTripleWithin_mono_nSteps (show 2 + 1 + 1 ≤ 4 by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c2)

/-- **S5 — the last-length telemetry store** (idx 60…62): this call's
    `section_len` (in `s1`) is written to `wlh_linear_last_section_len`. -/
private theorem wlhLastLen_spec (v5 len nLast : Word) :
    cpsTripleWithin 3 (wlhB + 240) (wlhB + 252) wlhCr
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x9 : Reg) ↦ᵣ len) ** (LinLastLoc ↦ₘ nLast))
      (((.x5 : Reg) ↦ᵣ LinLastLoc) ** ((.x9 : Reg) ↦ᵣ len) ** (LinLastLoc ↦ₘ len)) := by
  have hla := la_materialize_within .x5 v5 (wlhB + 240) LinLastLoc (cr := wlhCr)
    (by decide) (by decide) (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem)
  rw [show (wlhB + 240 : Word) + 8 = wlhB + 248 from by bv_omega] at hla
  have hsd := liftCode (cr' := wlhCr)
    (sd_spec_gen_within .x5 .x9 LinLastLoc len nLast (0 : BitVec 12) (wlhB + 248))
    (by unfold wlhCr; code_mem)
  rw [sext12_zero, show LinLastLoc + (0 : Word) = LinLastLoc from by bv_omega,
    show (wlhB + 248 : Word) + 4 = wlhB + 252 from by bv_omega] at hsd
  have f1 := cpsTripleWithin_frameR
    (((.x9 : Reg) ↦ᵣ len) ** (LinLastLoc ↦ₘ nLast)) (by pcf) hla
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f1 hsd
  exact cpsTripleWithin_mono_nSteps (show 2 + 1 ≤ 3 by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c1)

/-- **S6 — the max-length telemetry guard** (idx 63…66): the running maximum
    is read and the `bgeu` skips the update. With `section_len = 0` the guard
    ALWAYS skips, so `wlh_linear_max_section_len` is left unchanged — the
    routine never lowers its own high-water mark. -/
private theorem wlhMaxLen_spec (v5 v6 nMax : Word) :
    cpsTripleWithin 4 (wlhB + 252) (wlhB + 272) wlhCr
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
        (LinMaxLoc ↦ₘ nMax))
      (((.x5 : Reg) ↦ᵣ LinMaxLoc) ** ((.x6 : Reg) ↦ᵣ nMax) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** (LinMaxLoc ↦ₘ nMax)) := by
  have hla := la_materialize_within .x5 v5 (wlhB + 252) LinMaxLoc (cr := wlhCr)
    (by decide) (by decide) (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem)
  rw [show (wlhB + 252 : Word) + 8 = wlhB + 260 from by bv_omega] at hla
  have hld := liftCode (cr' := wlhCr)
    (ld_spec_gen_within .x6 .x5 LinMaxLoc v6 nMax (0 : BitVec 12) (wlhB + 260)
      (by decide))
    (by unfold wlhCr; code_mem)
  rw [sext12_zero, show LinMaxLoc + (0 : Word) = LinMaxLoc from by bv_omega,
    show (wlhB + 260 : Word) + 4 = wlhB + 264 from by bv_omega] at hld
  have hbr := cpsBranchWithin_extend_code (cr' := wlhCr)
    (by unfold wlhCr; code_mem)
    (bgeu_spec_gen_within .x6 .x9 (8 : BitVec 13) nMax (0 : Word) (wlhB + 264))
  have hbt := cpsBranchWithin_takenStripPure2 hbr bgeu_zero_absurd
  rw [show (wlhB + 264 : Word) + signExtend13 (8 : BitVec 13) = wlhB + 272
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
private theorem wlhZeroLenExit_spec :
    cpsTripleWithin 1 (wlhB + 272) (wlhB + 556) wlhCr
      (((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) := by
  have hbr := cpsBranchWithin_extend_code (cr' := wlhCr)
    (by unfold wlhCr; code_mem)
    (beq_spec_gen_within .x9 .x0
      (brOff (GuestAddrs.witness_lookup_by_hash + 556)
        (GuestAddrs.witness_lookup_by_hash + 272)) (0 : Word) (0 : Word) (wlhB + 272))
  have hbt := cpsBranchWithin_takenStripPure2 hbr beq_same_absurd
  rw [show (wlhB + 272 : Word) + signExtend13
      (brOff (GuestAddrs.witness_lookup_by_hash + 556)
        (GuestAddrs.witness_lookup_by_hash + 272)) = wlhB + 556 from by decide] at hbt
  exact hbt

/-- **S9 — the miss status** (idx 144): `a0 := 1`. -/
private theorem wlhMissStatus_spec (v10 : Word) :
    cpsTripleWithin 1 (wlhB + 576) (wlhB + 580) wlhCr
      (((.x10 : Reg) ↦ᵣ v10)) (((.x10 : Reg) ↦ᵣ (1 : Word))) := by
  have h := liftCode (cr' := wlhCr)
    (li_spec_gen_within .x10 v10 (1 : Word) (wlhB + 576) (by decide))
    (by unfold wlhCr; code_mem)
  rw [show (wlhB + 576 : Word) + 4 = wlhB + 580 from by bv_omega] at h
  exact h

/-! ## §5  The body, composed

    Nine segments, 33 machine steps, `wlhB + 36` → `wlhB + 580`. The exit is
    the epilogue's first instruction — the address the routine's own `j`
    instructions target — so this is the body `abiFrame_spec_own` expects. -/

/-- **The `section_len = 0` body**, with the tight footprint: the thirteen
    registers and six `.data` cells the path touches, and nothing else. -/
private theorem wlhEmptySectionBody_core (secPtr hashPtr outOffP outLenP
    v5 v6 a8 a9 a18 a19 a20 nCalls nLin nLast nMax nMiss : Word) :
    cpsTripleWithin 33 (wlhB + 36) (wlhB + 580) wlhCr
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x8 : Reg) ↦ᵣ a8) ** ((.x9 : Reg) ↦ᵣ a9) **
        ((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
        ((.x14 : Reg) ↦ᵣ outLenP) ** ((.x18 : Reg) ↦ᵣ a18) **
        ((.x19 : Reg) ↦ᵣ a19) ** ((.x20 : Reg) ↦ᵣ a20) ** (CallsLoc ↦ₘ nCalls) **
        (WidxEnLoc ↦ₘ (0 : Word)) ** (LinCallsLoc ↦ₘ nLin) **
        (LinLastLoc ↦ₘ nLast) ** (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nMiss))
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ LinMissLoc) **
        ((.x6 : Reg) ↦ᵣ (nMiss + 1)) ** ((.x8 : Reg) ↦ᵣ secPtr) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
        ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
        ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
        ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
        ((.x20 : Reg) ↦ᵣ outLenP) ** (CallsLoc ↦ₘ (nCalls + 1)) **
        (WidxEnLoc ↦ₘ (0 : Word)) ** (LinCallsLoc ↦ₘ (nLin + 1)) **
        (LinLastLoc ↦ₘ (0 : Word)) ** (LinMaxLoc ↦ₘ nMax) **
        (LinMissLoc ↦ₘ (nMiss + 1))) := by
  have h_s1 := wlhArgMoves_spec secPtr (0 : Word) hashPtr outOffP outLenP a8 a9 a18 a19 a20
  have h_b1 := wlhCounterBump_spec (wlhB + 56) CallsLoc v5 v6 nCalls (by decide)
    (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem)
  rw [show (wlhB + 56 : Word) + 20 = wlhB + 76 from by bv_omega] at h_b1
  have h_s3 := wlhWidxDispatch_spec CallsLoc
  have h_b2 := wlhCounterBump_spec (wlhB + 220) LinCallsLoc (0 : Word) (nCalls + 1) nLin
    (by decide) (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem)
  rw [show (wlhB + 220 : Word) + 20 = wlhB + 240 from by bv_omega] at h_b2
  have h_s5 := wlhLastLen_spec LinCallsLoc (0 : Word) nLast
  have h_s6 := wlhMaxLen_spec LinLastLoc (nLin + 1) nMax
  have h_s7 := wlhZeroLenExit_spec
  have h_b3 := wlhCounterBump_spec (wlhB + 556) LinMissLoc LinMaxLoc nMax nMiss
    (by decide) (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem) (by unfold wlhCr; code_mem)
  rw [show (wlhB + 556 : Word) + 20 = wlhB + 576 from by bv_omega] at h_b3
  have h_s9 := wlhMissStatus_spec secPtr
  have f_s1 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) **
      ((.x6 : Reg) ↦ᵣ v6) ** (CallsLoc ↦ₘ nCalls) **
      (WidxEnLoc ↦ₘ (0 : Word)) ** (LinCallsLoc ↦ₘ nLin) **
      (LinLastLoc ↦ₘ nLast) ** (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nMiss)) (by pcf) h_s1
  have f_b1 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x8 : Reg) ↦ᵣ secPtr) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ secPtr) **
      ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
      ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
      ((.x20 : Reg) ↦ᵣ outLenP) ** (WidxEnLoc ↦ₘ (0 : Word)) **
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
      (WidxEnLoc ↦ₘ (0 : Word)) ** (LinLastLoc ↦ₘ nLast) **
      (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nMiss)) (by pcf) h_b2
  have f_s5 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ (nLin + 1)) **
      ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x10 : Reg) ↦ᵣ secPtr) **
      ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
      ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
      ((.x20 : Reg) ↦ᵣ outLenP) ** (CallsLoc ↦ₘ (nCalls + 1)) **
      (WidxEnLoc ↦ₘ (0 : Word)) ** (LinCallsLoc ↦ₘ (nLin + 1)) **
      (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nMiss)) (by pcf) h_s5
  have f_s6 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x8 : Reg) ↦ᵣ secPtr) **
      ((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
      ((.x14 : Reg) ↦ᵣ outLenP) ** ((.x18 : Reg) ↦ᵣ hashPtr) **
      ((.x19 : Reg) ↦ᵣ outOffP) ** ((.x20 : Reg) ↦ᵣ outLenP) **
      (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (0 : Word)) **
      (LinCallsLoc ↦ₘ (nLin + 1)) ** (LinLastLoc ↦ₘ (0 : Word)) **
      (LinMissLoc ↦ₘ nMiss)) (by pcf) h_s6
  have f_s7 := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ LinMaxLoc) ** ((.x6 : Reg) ↦ᵣ nMax) **
      ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x10 : Reg) ↦ᵣ secPtr) **
      ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
      ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
      ((.x20 : Reg) ↦ᵣ outLenP) ** (CallsLoc ↦ₘ (nCalls + 1)) **
      (WidxEnLoc ↦ₘ (0 : Word)) ** (LinCallsLoc ↦ₘ (nLin + 1)) **
      (LinLastLoc ↦ₘ (0 : Word)) ** (LinMaxLoc ↦ₘ nMax) **
      (LinMissLoc ↦ₘ nMiss)) (by pcf) h_s7
  have f_b3 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x8 : Reg) ↦ᵣ secPtr) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ secPtr) **
      ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
      ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
      ((.x20 : Reg) ↦ᵣ outLenP) ** (CallsLoc ↦ₘ (nCalls + 1)) **
      (WidxEnLoc ↦ₘ (0 : Word)) ** (LinCallsLoc ↦ₘ (nLin + 1)) **
      (LinLastLoc ↦ₘ (0 : Word)) ** (LinMaxLoc ↦ₘ nMax)) (by pcf) h_b3
  have f_s9 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ LinMissLoc) **
      ((.x6 : Reg) ↦ᵣ (nMiss + 1)) ** ((.x8 : Reg) ↦ᵣ secPtr) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
      ((.x14 : Reg) ↦ᵣ outLenP) ** ((.x18 : Reg) ↦ᵣ hashPtr) **
      ((.x19 : Reg) ↦ᵣ outOffP) ** ((.x20 : Reg) ↦ᵣ outLenP) **
      (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (0 : Word)) **
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
    `.data` cells it touches — `widx_enabled` READ as zero (index disabled),
    the other five owned because the routine writes them. -/
def wlhArgs (v5 v6 secPtr hashPtr outOffP outLenP
    nCalls nLin nLast nMax nMiss : Word) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
  ((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
  ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
  ((.x14 : Reg) ↦ᵣ outLenP) **
  (CallsLoc ↦ₘ nCalls) ** (WidxEnLoc ↦ₘ (0 : Word)) ** (LinCallsLoc ↦ₘ nLin) **
  (LinLastLoc ↦ₘ nLast) ** (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nMiss)

/-- The caller-visible ambient at return: **`a0 = 1`, the miss status**, the
    argument registers `a1…a4` intact, and each telemetry cell at its exact
    new value. Asymmetric by construction — `wlh_lookup_calls` and
    `wlh_linear_calls` are bumped, `wlh_linear_last_section_len` is
    OVERWRITTEN with this call's length (zero) while
    `wlh_linear_max_section_len` is LEFT ALONE, and `wlh_linear_misses` is
    bumped. Swapping any two of the five would not typecheck. -/
def wlhMissOut (hashPtr outOffP outLenP
    nCalls nLin nMax nMiss : Word) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ LinMissLoc) **
  ((.x6 : Reg) ↦ᵣ (nMiss + 1)) **
  ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
  ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
  ((.x14 : Reg) ↦ᵣ outLenP) **
  (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (0 : Word)) **
  (LinCallsLoc ↦ₘ (nLin + 1)) ** (LinLastLoc ↦ₘ (0 : Word)) **
  (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ (nMiss + 1))

theorem wlhArgs_pcFree (v5 v6 secPtr hashPtr outOffP outLenP
    nCalls nLin nLast nMax nMiss : Word) :
    (wlhArgs v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax nMiss).pcFree := by
  unfold wlhArgs; pcf

theorem wlhMissOut_pcFree (hashPtr outOffP outLenP nCalls nLin nMax nMiss : Word) :
    (wlhMissOut hashPtr outOffP outLenP nCalls nLin nMax nMiss).pcFree := by
  unfold wlhMissOut; pcf

private theorem regsAt_wlhFrame (vals : Reg → Word) :
    regsAt wlhFrame vals =
      (((.x1 : Reg) ↦ᵣ vals .x1) ** ((.x8 : Reg) ↦ᵣ vals .x8) **
        ((.x9 : Reg) ↦ᵣ vals .x9) ** ((.x18 : Reg) ↦ᵣ vals .x18) **
        ((.x19 : Reg) ↦ᵣ vals .x19) ** ((.x20 : Reg) ↦ᵣ vals .x20) **
        ((.x21 : Reg) ↦ᵣ vals .x21) ** ((.x22 : Reg) ↦ᵣ vals .x22)) := by
  simp [wlhFrame, regsAt, sepConj_emp_right']

private theorem regsOwnAt_wlhFrame :
    regsOwnAt wlhFrame =
      (regOwn .x1 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
        regOwn .x20 ** regOwn .x21 ** regOwn .x22) := by
  simp [wlhFrame, regsOwnAt, sepConj_emp_right']

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
private theorem wlhEmptySectionBody (newSp : Word) (vals : Reg → Word)
    (v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax nMiss : Word) :
    cpsTripleWithin 33
      (wlhB + BitVec.ofNat 64 (4 * (1 + wlhFrame.length)))
      (wlhB + BitVec.ofNat 64 (4 * (1 + wlhFrame.length + wlhBody.length))) wlhCr
      ((((.x2 : Reg) ↦ᵣ newSp) ** regsAt wlhFrame vals **
        frameSlotsSaved wlhFrame newSp vals **
        wlhArgs v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax nMiss))
      ((((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt wlhFrame **
        frameSlotsSaved wlhFrame newSp vals **
        wlhMissOut hashPtr outOffP outLenP nCalls nLin nMax nMiss)) := by
  rw [wlhFrame_length, wlhBody_length]
  simp only [show 4 * (1 + 8) = 36 from rfl, show 4 * (1 + 8 + 136) = 580 from rfl]
  have core := wlhEmptySectionBody_core secPtr hashPtr outOffP outLenP v5 v6
    (vals .x8) (vals .x9) (vals .x18) (vals .x19) (vals .x20) nCalls nLin nLast nMax nMiss
  have framed := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) ** ((.x1 : Reg) ↦ᵣ vals .x1) **
      ((.x21 : Reg) ↦ᵣ vals .x21) ** ((.x22 : Reg) ↦ᵣ vals .x22) **
      frameSlotsSaved wlhFrame newSp vals) (by pcf) core
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) framed
  · rw [regsAt_wlhFrame] at hp
    unfold wlhArgs at hp
    xperm_hyp hp
  · show ((((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt wlhFrame **
      frameSlotsSaved wlhFrame newSp vals **
      wlhMissOut hashPtr outOffP outLenP nCalls nLin nMax nMiss)) h
    rw [regsOwnAt_wlhFrame]
    unfold wlhMissOut
    have hq2 : (((.x1 : Reg) ↦ᵣ vals .x1) ** ((.x8 : Reg) ↦ᵣ secPtr) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ hashPtr) **
        ((.x19 : Reg) ↦ᵣ outOffP) ** ((.x20 : Reg) ↦ᵣ outLenP) **
        ((.x21 : Reg) ↦ᵣ vals .x21) ** ((.x22 : Reg) ↦ᵣ vals .x22) **
        (((.x2 : Reg) ↦ᵣ newSp) ** frameSlotsSaved wlhFrame newSp vals **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ LinMissLoc) **
          ((.x6 : Reg) ↦ᵣ (nMiss + 1)) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
          ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
          ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
          (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (0 : Word)) **
          (LinCallsLoc ↦ₘ (nLin + 1)) ** (LinLastLoc ↦ₘ (0 : Word)) **
          (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ (nMiss + 1)))) h := by
      xperm_hyp hq
    have hq3 := ent_own8 .x1 .x8 .x9 .x18 .x19 .x20 .x21 .x22
      (vals .x1) secPtr (0 : Word) hashPtr outOffP outLenP (vals .x21) (vals .x22) _ h hq2
    xperm_hyp hq3

/-- **`witness_lookup_by_hash`, whole routine, at its linked guest address —
    on the `section_len = 0` domain.**

    From the routine's entry `GuestAddrs.witness_lookup_by_hash`, over the
    emitted program itself (`wlhCr = CodeReq.ofProg wlhB
    witnessLookupByHash_prog`), execution returns to the caller in at most 52
    steps with:

    * `a0 = 1` — the documented "`section_len = 0` ⇒ guaranteed miss";
    * every callee-saved register (`ra`, `s0`…`s6`) back at its ENTRY value
      and `sp` back at `sp0` — derived from `abiFrame_spec_own`, not assumed;
    * the caller's two out cells NEVER MENTIONED, hence untouched by the
      frame rule: a miss must not publish an offset or a length;
    * the six `.data` cells at their exact new values.

    Hypotheses are ABI/resource facts only: a two-byte-aligned return address
    held in `ra` at entry, and the 64-byte frame slots owned. The domain
    restriction is `a1 = 0` together with `widx_enabled = 0` — an
    INPUT-DOMAIN gate. There is deliberately no upper bound on `section_len`
    anywhere in this file (`MptWitnessLookup.lean`'s docstring records what a
    size cap here once broke). -/
theorem witness_lookup_by_hash_spec_within_empty_section
    (sp0 ret : Word) (vals : Reg → Word)
    (v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax nMiss : Word)
    (hret : vals .x1 = ret)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 52 wlhB ret wlhCr
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt wlhFrame vals **
        frameSlotsOwn wlhFrame (sp0 + signExtend12 (-64 : BitVec 12)) **
        wlhArgs v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax nMiss)
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt wlhFrame vals **
        frameSlotsSaved wlhFrame (sp0 + signExtend12 (-64 : BitVec 12)) vals **
        wlhMissOut hashPtr outOffP outLenP nCalls nLin nMax nMiss) := by
  have h := abiFrame_spec_own wlhB sp0 ret (-64 : BitVec 12) (64 : BitVec 12)
    wlhFrame (0 : BitVec 12)
    [(.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12)), (.x18, (24 : BitVec 12)),
     (.x19, (32 : BitVec 12)), (.x20, (40 : BitVec 12)), (.x21, (48 : BitVec 12)),
     (.x22, (56 : BitVec 12))]
    vals wlhBody 33
    (wlhArgs v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax nMiss)
    (wlhMissOut hashPtr outOffP outLenP nCalls nLin nMax nMiss)
    wlhCr rfl (by decide) (by decide)
    (by rw [wlh_abiFrame_byte_tie]; decide)
    hret halign (sext_frameRestore _ _ _ (by decide))
    (wlhArgs_pcFree _ _ _ _ _ _ _ _ _ _ _) (wlhMissOut_pcFree _ _ _ _ _ _ _)
    (by rw [wlh_abiFrame_byte_tie]; unfold wlhCr; code_mem)
    (wlhEmptySectionBody _ vals v5 v6 secPtr hashPtr outOffP outLenP
      nCalls nLin nLast nMax nMiss)
  rw [wlhFrame_length] at h
  exact h

/-! ## §7  Non-vacuity -/

/-- Sample entry values for the eight callee-saved registers — pairwise
    distinct, so the post's "restored to its ENTRY value" claim is
    discriminating rather than satisfied by a constant. -/
def wlhSampleVals : Reg → Word
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
    `wlhArgs` is not the empty assertion in disguise. -/
theorem wlhCells_distinct :
    CallsLoc ≠ WidxEnLoc ∧ CallsLoc ≠ LinCallsLoc ∧ CallsLoc ≠ LinLastLoc ∧
    CallsLoc ≠ LinMaxLoc ∧ CallsLoc ≠ LinMissLoc ∧
    WidxEnLoc ≠ LinCallsLoc ∧ WidxEnLoc ≠ LinLastLoc ∧ WidxEnLoc ≠ LinMaxLoc ∧
    WidxEnLoc ≠ LinMissLoc ∧ LinCallsLoc ≠ LinLastLoc ∧ LinCallsLoc ≠ LinMaxLoc ∧
    LinCallsLoc ≠ LinMissLoc ∧ LinLastLoc ≠ LinMaxLoc ∧ LinLastLoc ≠ LinMissLoc ∧
    LinMaxLoc ≠ LinMissLoc := by
  unfold CallsLoc WidxEnLoc LinCallsLoc LinLastLoc LinMaxLoc LinMissLoc
  decide

/-- ⭐ **A concrete satisfying instance of the whole-routine triple.**

    A closed instantiation: entry `sp = 0xa0050000`, return address
    `0x80006300`, the eight callee-saved registers holding eight DIFFERENT
    entry values, a zero-length section at `0x40000030`, a target hash at
    `0x40000010`, out cells at `0xa0010008`/`0xa0010010`, and telemetry
    counters starting at `(7, 3, 99, 4096, 5)`. Every hypothesis of
    `witness_lookup_by_hash_spec_within_empty_section` is discharged here and
    the post is fully concrete — in particular `a0 = 1`,
    `wlh_linear_last_section_len` becomes `0` while
    `wlh_linear_max_section_len` stays `4096`. -/
theorem wlh_empty_section_sample_witness :
    cpsTripleWithin 52 wlhB (0x80006300 : Word) wlhCr
      (((.x2 : Reg) ↦ᵣ (0xa0050000 : Word)) ** regsAt wlhFrame wlhSampleVals **
        frameSlotsOwn wlhFrame ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12)) **
        wlhArgs (0 : Word) (0 : Word) (0x40000030 : Word) (0x40000010 : Word)
          (0xa0010008 : Word) (0xa0010010 : Word) (7 : Word) (3 : Word) (99 : Word)
          (4096 : Word) (5 : Word))
      (((.x2 : Reg) ↦ᵣ (0xa0050000 : Word)) ** regsAt wlhFrame wlhSampleVals **
        frameSlotsSaved wlhFrame
          ((0xa0050000 : Word) + signExtend12 (-64 : BitVec 12)) wlhSampleVals **
        wlhMissOut (0x40000010 : Word) (0xa0010008 : Word) (0xa0010010 : Word)
          (7 : Word) (3 : Word) (4096 : Word) (5 : Word)) :=
  witness_lookup_by_hash_spec_within_empty_section (0xa0050000 : Word)
    (0x80006300 : Word) wlhSampleVals (0 : Word) (0 : Word) (0x40000030 : Word)
    (0x40000010 : Word) (0xa0010008 : Word) (0xa0010010 : Word) (7 : Word) (3 : Word)
    (99 : Word) (4096 : Word) (5 : Word) rfl (by decide)

/-! ## §8  The `wlCallWithinShape` residual after #12144 -/

/-- **Blocker 1 RETIRED** — re-export of `MptWalkSpec.wlh_entry_in_walk_fullCode`.
    Walk `fullCode` now unions `wlhCr`; the callee entry is constrained. -/
theorem wlh_entry_in_walk_fullCode : MptWalkSpec.fullCode wlhB ≠ none := by
  -- `wlhB` and `MptWalkSpec.WlhB` are both `GuestAddrs.witness_lookup_by_hash`.
  have h := MptWalkSpec.wlh_entry_in_walk_fullCode
  unfold MptWalkSpec.WlhB wlhB at *
  exact h

/-- **Blocker 2 still applies to the generic residual entry**
    (`MptWalkResiduals.wlCallEntry` names out cells only, not telemetry).

    The six `.data` cells this routine touches remain distinct from the two
    out cells the generic residual names. Empty-section discharge repairs this
    by using `wlhArgs`/`wlhMissOut` instead of bare `wlCallEntry` (see §9 and
    `MptWalkWlEmpty`). -/
theorem wlh_cells_outside_residual_footprint :
    CallsLoc ≠ MptWalkSpec.MwLookupOff ∧ CallsLoc ≠ MptWalkSpec.MwLookupLen ∧
    WidxEnLoc ≠ MptWalkSpec.MwLookupOff ∧ WidxEnLoc ≠ MptWalkSpec.MwLookupLen ∧
    LinCallsLoc ≠ MptWalkSpec.MwLookupOff ∧ LinCallsLoc ≠ MptWalkSpec.MwLookupLen ∧
    LinLastLoc ≠ MptWalkSpec.MwLookupOff ∧ LinLastLoc ≠ MptWalkSpec.MwLookupLen ∧
    LinMaxLoc ≠ MptWalkSpec.MwLookupOff ∧ LinMaxLoc ≠ MptWalkSpec.MwLookupLen ∧
    LinMissLoc ≠ MptWalkSpec.MwLookupOff ∧ LinMissLoc ≠ MptWalkSpec.MwLookupLen := by
  unfold CallsLoc WidxEnLoc LinCallsLoc LinLastLoc LinMaxLoc LinMissLoc
  decide

/-! ## §9  The discharge that IS available (empty-section domain)

    Blocker 1 retired; Blocker 2 repaired in the ambient below.
    Domain: `section_len = 0`, `widx_enabled = 0` only — hit residual open. -/

/-- The routine's 64-byte frame occupies exactly the eight free stack dwords
    below the caller's `sp` — the same cells `wlCallEntry` hands over as
    `stackFree sp0 8`. -/
theorem stackFree8_eq_frameSlotsOwn (sp : Word) :
    stackFree sp 8 = frameSlotsOwn wlhFrame (sp + signExtend12 (-64 : BitVec 12)) := by
  show (memOwn (sp - BitVec.ofNat 64 (8 * 8)) ** memOwn (sp - BitVec.ofNat 64 (8 * 7)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 6)) ** memOwn (sp - BitVec.ofNat 64 (8 * 5)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 4)) ** memOwn (sp - BitVec.ofNat 64 (8 * 3)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 2)) ** memOwn (sp - BitVec.ofNat 64 (8 * 1)) **
      empAssertion) = _
  show _ = (memOwn ((sp + signExtend12 (-64 : BitVec 12)) + signExtend12 (0 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-64 : BitVec 12)) + signExtend12 (8 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-64 : BitVec 12)) + signExtend12 (16 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-64 : BitVec 12)) + signExtend12 (24 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-64 : BitVec 12)) + signExtend12 (32 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-64 : BitVec 12)) + signExtend12 (40 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-64 : BitVec 12)) + signExtend12 (48 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-64 : BitVec 12)) + signExtend12 (56 : BitVec 12)) **
      empAssertion)
  rw [show signExtend12 (-64 : BitVec 12) = (-64 : Word) from by decide,
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
    show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
    show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
    show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide,
    show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide,
    show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide,
    show sp - BitVec.ofNat 64 (8 * 8) = sp + (-64 : Word) + (0 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 7) = sp + (-64 : Word) + (8 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 6) = sp + (-64 : Word) + (16 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 5) = sp + (-64 : Word) + (24 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 4) = sp + (-64 : Word) + (32 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 3) = sp + (-64 : Word) + (40 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 2) = sp + (-64 : Word) + (48 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 1) = sp + (-64 : Word) + (56 : Word) from by bv_omega]

/-- The seven callee-saved `s`-registers at their entry values (`ra` is
    handled separately by the call rule). -/
def wlhSregs (vals : Reg → Word) : Assertion :=
  ((.x8 : Reg) ↦ᵣ vals .x8) ** ((.x9 : Reg) ↦ᵣ vals .x9) **
  ((.x18 : Reg) ↦ᵣ vals .x18) ** ((.x19 : Reg) ↦ᵣ vals .x19) **
  ((.x20 : Reg) ↦ᵣ vals .x20) ** ((.x21 : Reg) ↦ᵣ vals .x21) **
  ((.x22 : Reg) ↦ᵣ vals .x22)

/-- **The call-site discharge, `section_len = 0`.**

    Instantiates `callWithin_spec` against
    `witness_lookup_by_hash_spec_within_empty_section`. Requires `cr` to
    contain the callee (`hcode` — satisfied by walk `fullCode` after #12144)
    and entry/return ambients carrying the six telemetry cells. The free
    stack the callee carves its frame from is `stackFree sp0 8`
    (`stackFree8_eq_frameSlotsOwn`). Site lemmas:
    `MptWalkSpec.root_wl_call_empty_section` and branch/ext twins. -/
theorem wlhCallWithin_empty_section (cr : CodeReq) (callerPC vOld sp0 : Word)
    (offset : BitVec 21) (vals : Reg → Word) (F : Assertion)
    (v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax nMiss : Word)
    (hF : F.pcFree)
    (hvals : vals .x1 = callerPC + 4)
    (halign : ((callerPC + 4) &&& ~~~(1 : Word)) = callerPC + 4)
    (htarget : callerPC + signExtend21 offset = wlhB)
    (hmem : ∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i → cr a = some i)
    (hcode : ∀ a i, wlhCr a = some i → cr a = some i) :
    cpsTripleWithin (1 + 52) callerPC (callerPC + 4) cr
      ((((.x1 : Reg) ↦ᵣ vOld) ** ((.x2 : Reg) ↦ᵣ sp0) ** stackFree sp0 8 **
        wlhSregs vals **
        wlhArgs v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax nMiss) ** F)
      ((((.x1 : Reg) ↦ᵣ (callerPC + 4)) ** ((.x2 : Reg) ↦ᵣ sp0) **
        frameSlotsSaved wlhFrame (sp0 + signExtend12 (-64 : BitVec 12)) vals **
        wlhSregs vals **
        wlhMissOut hashPtr outOffP outLenP nCalls nLin nMax nMiss) ** F) := by
  have hbase := cpsTripleWithin_extend_code hcode
    (witness_lookup_by_hash_spec_within_empty_section sp0 (callerPC + 4) vals
      v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax nMiss hvals halign)
  rw [regsAt_wlhFrame, hvals, ← stackFree8_eq_frameSlotsOwn] at hbase
  have hPfree : ((((.x2 : Reg) ↦ᵣ sp0) ** stackFree sp0 8 ** wlhSregs vals **
      wlhArgs v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax
        nMiss) ** F).pcFree := by
    unfold wlhSregs wlhArgs
    repeat' first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_stackFree _ _
      | exact hF
  have hcallee : cpsTripleWithin 52 wlhB (callerPC + 4) cr
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
        ((((.x2 : Reg) ↦ᵣ sp0) ** stackFree sp0 8 ** wlhSregs vals **
          wlhArgs v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax
            nMiss) ** F))
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
        ((((.x2 : Reg) ↦ᵣ sp0) **
          frameSlotsSaved wlhFrame (sp0 + signExtend12 (-64 : BitVec 12)) vals **
          wlhSregs vals **
          wlhMissOut hashPtr outOffP outLenP nCalls nLin nMax nMiss) ** F)) := by
    have hfr := cpsTripleWithin_frameR F hF hbase
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hfr
    · unfold wlhSregs at hp
      xperm_hyp hp
    · unfold wlhSregs
      xperm_hyp hq
  have hcall := callWithin_spec callerPC wlhB vOld offset 52 htarget hmem hPfree hcallee
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hcall

end EvmAsm.Codegen.WitnessLookupByHashSpec
