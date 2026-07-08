/-
  EvmAsm.Rv64.SAsm.AbiFrameCall

  Frame + cross-call composition at the `cpsTripleWithin` level (bead
  evm-asm-4ch8f.76 follow-up): the missing piece for the ~218 sp-frame guest
  routines that CALL OUT (block-verdict / MPT / tx / crypto).

  `abiFrame_spec` (AbiFrame.lean) lifts an arbitrary single-exit body into a
  whole prologue·body·epilogue·ret routine.  Its `vals'` (the body-clobbered
  register values) is COMPLETELY FREE — including `vals' .x1` — and the
  epilogue restores every saved register (ra included) from its frame slot
  (`loadSeq_spec` takes the slot value, ignoring the clobbered register).  So
  the ra-clobber-across-call is ALREADY supported at the frame level; what a
  cross-calling body needs is supplied here:

  1. **A free-stack region below `sp`** (`stackFree sp k`): `k` genuinely
     *owned* dword cells `sp - 8, sp - 16, …, sp - 8k` — the stack space a
     callee may carve its own frame from.  Being ordinary `memOwn` atoms they
     are disjoint (through `**`) from the caller's frame slots, saved-`ra`
     slot, and every caller region — no arbitrary stack read/write hole.
     `stackFree_split` splits off a callee-sized prefix, framing the rest.

  2. **The call composition rule** (`callWithin_spec` / `abiFrameCall_spec`):
     `jal ra, callee` links `ra := A + 4` (clobbering it — that is *why* the
     caller saved `ra` in its frame) and transfers to the callee, whose own
     whole-routine `cpsTripleWithin` contract (e.g. an `abiFrame_spec`
     instance, entered with `sp = newSp` and its frame carved from
     `stackFree newSp m`) runs back to `A + 4`.  Everything the callee does
     not own — the caller's frame slots, the saved `ra`, the unused stack,
     every caller region — is framed through the call, so its preservation is
     *proven* by separation, never assumed.  A *sequence* of calls composes
     by ordinary `cpsTripleWithin` sequencing: each `jal` re-clobbers `ra`
     (the rule takes the incumbent value as a free `vOld`).

  `AbiFrameCallDemo.lean` exercises the whole stack: a framed caller invokes
  a framed callee TWICE via real `jal`s, the callee carving its frame from
  the caller's free stack; `abiFrame_spec` then restores `sp`/`ra` to entry.

  Strictly additive: `cpsTripleWithin` only; no `Ast`/`Vc`/`StmtSound*`/
  `blockOk` changes.
-/

import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64
namespace SAsm

open EvmAsm.Rv64.Tactics

-- ============================================================================
-- The free-stack region below `sp`.
-- ============================================================================

/-- `stackFree sp k`: `k` genuinely owned dword cells immediately below `sp`
    (`sp - 8·(k)…sp - 8`, arbitrary contents).  The stack space a callee may
    allocate its own frame from; ordinary owned-memory atoms, so disjoint
    (through `**`) from the caller's frame slots and regions. -/
def stackFree (sp : Word) : Nat → Assertion
  | 0 => empAssertion
  | k + 1 => memOwn (sp - BitVec.ofNat 64 (8 * (k + 1))) ** stackFree sp k

@[simp] theorem stackFree_zero (sp : Word) : stackFree sp 0 = empAssertion := rfl

theorem stackFree_succ (sp : Word) (k : Nat) :
    stackFree sp (k + 1)
      = (memOwn (sp - BitVec.ofNat 64 (8 * (k + 1))) ** stackFree sp k) := rfl

theorem pcFree_stackFree (sp : Word) (k : Nat) : (stackFree sp k).pcFree := by
  induction k with
  | zero => exact pcFree_emp
  | succ n ih => exact pcFree_sepConj pcFree_memOwn ih

/-- Assertion-level (`=`) associativity, from the pointwise `sepConj_assoc`. -/
private theorem sepConj_assoc_eq {P Q R : Assertion} :
    ((P ** Q) ** R) = (P ** (Q ** R)) := by
  funext h; exact propext (sepConj_assoc h)

/-- Assertion-level (`=`) left identity. -/
private theorem sepConj_emp_left_eq {P : Assertion} : (empAssertion ** P) = P := by
  funext h; exact propext (sepConj_emp_left h)

/-- Split a free-stack region: the shallow `m` cells a callee will use, with
    the deeper remainder framed off. -/
theorem stackFree_split (sp : Word) {m K : Nat} (h : m ≤ K) :
    ∃ R : Assertion, R.pcFree ∧ stackFree sp K = (R ** stackFree sp m) := by
  induction K with
  | zero =>
    have hm : m = 0 := Nat.le_zero.mp h
    subst hm
    exact ⟨empAssertion, pcFree_emp, sepConj_emp_left_eq.symm⟩
  | succ K ih =>
    rcases Nat.lt_or_ge m (K + 1) with hlt | hge
    · obtain ⟨R, hRp, hReq⟩ := ih (Nat.lt_succ_iff.mp hlt)
      refine ⟨memOwn (sp - BitVec.ofNat 64 (8 * (K + 1))) ** R,
        pcFree_sepConj pcFree_memOwn hRp, ?_⟩
      rw [stackFree_succ, hReq, sepConj_assoc_eq]
    · have hm : m = K + 1 := Nat.le_antisymm h hge
      subst hm
      exact ⟨empAssertion, pcFree_emp, sepConj_emp_left_eq.symm⟩

-- ============================================================================
-- The linking jump: `jal ra, offset`.
-- ============================================================================

/-- One-step spec of the direct call jump `jal x1, offset`: the return
    address `addr + 4` lands in the separately owned `ra` (clobbering the
    incumbent `vOld`), and control transfers to `addr + offset`.  The direct
    (`JAL`) analogue of `jalr_call_spec_within`. -/
theorem jal_link_spec_within (offset : BitVec 21) (addr vOld : Word) :
    cpsTripleWithin 1 addr (addr + signExtend21 offset)
      (CodeReq.singleton addr (.JAL .x1 offset))
      ((.x1 : Reg) ↦ᵣ vOld)
      ((.x1 : Reg) ↦ᵣ (addr + 4)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.JAL .x1 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hstep' : step s = some (execInstrBr s (.JAL .x1 offset)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) rfl
  have hexec : execInstrBr s (.JAL .x1 offset)
      = (s.setReg .x1 (s.pc + 4)).setPC (s.pc + signExtend21 offset) := rfl
  refine ⟨1, Nat.le_refl 1,
    (s.setReg .x1 (s.pc + 4)).setPC (s.pc + signExtend21 offset), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec]; rfl
  · have h1 := holdsFor_sepConj_regIs_setReg (v' := s.pc + 4)
      (show (.x1 : Reg) ≠ .x0 from by decide) hPR
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h1

-- ============================================================================
-- The call composition rule.
-- ============================================================================

/-- **Compose one `jal ra, callee` with the callee's whole-routine
    contract.**  The callee is supplied as a `cpsTripleWithin` from its entry
    back to the return address `A + 4` (the shape every `abiFrame_spec`
    conclusion and every `FnHandle.sound` instance has, with `ret := A + 4`),
    entered with `ra` holding that return address; the call site holds an
    arbitrary incumbent `vOld` in `ra` (a second call in sequence passes the
    previous call's link — each `jal` re-clobbers `ra`).  Everything not in
    the callee's footprint `P`/`Q` is framed by the ordinary frame rule. -/
theorem callWithin_spec {cr : CodeReq} {P Q : Assertion}
    (A calleeEntry vOld : Word) (offset : BitVec 21) (n : Nat)
    (htarget : A + signExtend21 offset = calleeEntry)
    (hmem : ∀ a i, CodeReq.singleton A (.JAL .x1 offset) a = some i → cr a = some i)
    (hP : P.pcFree)
    (hcallee : cpsTripleWithin n calleeEntry (A + 4) cr
        (((.x1 : Reg) ↦ᵣ (A + 4)) ** P)
        (((.x1 : Reg) ↦ᵣ (A + 4)) ** Q)) :
    cpsTripleWithin (1 + n) A (A + 4) cr
      (((.x1 : Reg) ↦ᵣ vOld) ** P)
      (((.x1 : Reg) ↦ᵣ (A + 4)) ** Q) := by
  have hjal := jal_link_spec_within offset A vOld
  rw [htarget] at hjal
  have hjalF := cpsTripleWithin_frameR P hP hjal
  have hjal' := cpsTripleWithin_extend_code hmem hjalF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hjal' hcallee

/-- **The frame + cross-call composition rule** (`abiFrameCall_spec`),
    consumed inside an `abiFrame_spec` body hypothesis.

    A framed caller (already inside its prologue, `sp = spVal = newSp`)
    invokes a callee whose contract:

    * enters at `calleeEntry` with `ra = A + 4`, `sp = spVal`, and `m` owned
      free-stack dwords below `sp` (`stackFree spVal m` — the space the
      callee carves its own frame from), plus its caller-visible footprint
      `calleePre`;
    * returns to `A + 4` with `ra`/`sp` intact, the free stack RELEASED
      (owned again — the callee's epilogue deallocated its frame), and
      `calleePost`.

    `F` is everything the callee does not own — the **caller's frame slots
    and saved `ra` slot**, the deeper unused stack (`stackFree_split`), and
    any other caller region — and is preserved through the call by the frame
    rule: preservation is *proven* by separation, never assumed.  Sequencing
    N calls chains this rule N times (`vOld` absorbs the previous link). -/
theorem abiFrameCall_spec {cr : CodeReq} {calleePre calleePost F : Assertion}
    (A calleeEntry vOld spVal : Word) (offset : BitVec 21) (m n : Nat)
    (htarget : A + signExtend21 offset = calleeEntry)
    (hmem : ∀ a i, CodeReq.singleton A (.JAL .x1 offset) a = some i → cr a = some i)
    (hpre : calleePre.pcFree) (hF : F.pcFree)
    (hcallee : cpsTripleWithin n calleeEntry (A + 4) cr
        (((.x1 : Reg) ↦ᵣ (A + 4)) ** (.x2 ↦ᵣ spVal) ** stackFree spVal m
          ** calleePre)
        (((.x1 : Reg) ↦ᵣ (A + 4)) ** (.x2 ↦ᵣ spVal) ** stackFree spVal m
          ** calleePost)) :
    cpsTripleWithin (1 + n) A (A + 4) cr
      (((.x1 : Reg) ↦ᵣ vOld) ** (.x2 ↦ᵣ spVal) ** stackFree spVal m
        ** calleePre ** F)
      (((.x1 : Reg) ↦ᵣ (A + 4)) ** (.x2 ↦ᵣ spVal) ** stackFree spVal m
        ** calleePost ** F) := by
  have hcalleeF := cpsTripleWithin_frameR F hF hcallee
  have hc : cpsTripleWithin n calleeEntry (A + 4) cr
      (((.x1 : Reg) ↦ᵣ (A + 4)) ** ((.x2 ↦ᵣ spVal) ** stackFree spVal m
        ** calleePre ** F))
      (((.x1 : Reg) ↦ᵣ (A + 4)) ** ((.x2 ↦ᵣ spVal) ** stackFree spVal m
        ** calleePost ** F)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcalleeF
  have hcall := callWithin_spec A calleeEntry vOld offset n htarget hmem
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj (pcFree_stackFree _ _) (pcFree_sepConj hpre hF)))
    hc
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hcall

end SAsm
end EvmAsm.Rv64
