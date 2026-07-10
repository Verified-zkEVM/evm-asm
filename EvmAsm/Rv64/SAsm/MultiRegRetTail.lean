/-
  EvmAsm.Rv64.SAsm.MultiRegRetTail

  The **multi-register straight-line shared return-tail**
  (bead evm-asm-24uka).

  `sharedRetTail_spec` (#10041) proves the single-register `li rd, c ; ret`
  return arm; `storeRetTail_spec` (#10067) the `sd ; li ; ret` writable-
  output arm.  Validation routines like `message_call_gas` have error
  tails that set SEVERAL return registers before returning:

  ```
  .err1: li a0, 1 ; li a1, 0 ; li a2, 0 ; li a3, 0 ; ret
  .err2: li a0, 2 ; li a1, 0 ; li a2, 0 ; li a3, 0 ; ret
  ```

  `multiRegRetTail_spec` proves the general shape ONCE per tail address:
  a LIST of `li` register assignments followed by `ret`, the post pinning
  EXACTLY the assigned registers to their constants (`regsSet assigns`) —
  no arbitrary effect.  Register/value/length-agnostic; each guard station
  targeting the tail reuses the same instance.

  **Branch-over-tail needs no new lemma**: `retJoinStation_spec` /
  `breakStation_spec` take the taken-arm TARGET ADDRESS as a parameter
  and their tail hypothesis is an ordinary `cpsTripleWithin` from that
  address — nothing constrains it to the immediately-following tail.  A
  station whose branch jumps OVER intervening tails to a later shared
  tail simply instantiates the later tail's `multiRegRetTail_spec` at its
  (further) address; the skipped tails' bytes stay in the routine's
  single `CodeReq` (code is a persistent side-condition, not a consumed
  resource).  Consumer `message_call_gas`
  (`Codegen/Programs/MessageCallGasSAsm.lean`) exercises exactly this:
  its two output-overflow guards jump over the success and `status-1`
  tails to the `status-2` tail.

  Everything is at `cpsTripleWithin` level (additive; no `Ast`/`Vc`
  changes).
-/

import EvmAsm.Rv64.SAsm.TwoBreakWritable
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

/-- The `↦ᵣ` atoms pinning each assigned register to its constant — the
    EXACT footprint of a multi-register return tail's effect. -/
def regsSet : List (Reg × Word) → Assertion
  | [] => empAssertion
  | rc :: rest => (rc.1 ↦ᵣ rc.2) ** regsSet rest

@[simp] theorem regsSet_nil : regsSet [] = empAssertion := rfl

@[simp] theorem regsSet_cons (rc : Reg × Word) (rest : List (Reg × Word)) :
    regsSet (rc :: rest) = ((rc.1 ↦ᵣ rc.2) ** regsSet rest) := rfl

theorem regsSet_pcFree (assigns : List (Reg × Word)) :
    (regsSet assigns).pcFree := by
  induction assigns with
  | nil => exact pcFree_emp
  | cons rc rest ih => exact pcFree_sepConj pcFree_regIs ih

/-- The straight-line multi-register return tail: one `li` per assignment,
    then `ret`. -/
def liRetTailProg (assigns : List (Reg × Word)) : List Instr :=
  assigns.map (fun rc => .LI rc.1 rc.2) ++ [.JALR .x0 .x1 (0 : BitVec 12)]

/-- **The multi-register shared return tail**, proven once per tail
    address: from ownership of the assigned registers, the tail reaches
    the shared `ret` continuation with EXACTLY those registers pinned to
    their constants (`regsSet assigns`) — no other effect.  Length-,
    register- and value-agnostic; `sharedRetTail_spec`'s `li rd, c ; ret`
    is the singleton instance. -/
theorem multiRegRetTail_spec (cr : CodeReq) (addr ret : Word)
    (assigns : List (Reg × Word))
    (hnz : ∀ rc ∈ assigns, rc.1 ≠ .x0)
    (hlen : assigns.length < 2 ^ 60)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hmem : ∀ a i, CodeReq.ofProg addr (liRetTailProg assigns) a = some i →
      cr a = some i) :
    cpsTripleWithin (assigns.length + 1) addr ret cr
      (regOwns (assigns.map Prod.fst) ** ((.x1 : Reg) ↦ᵣ ret))
      (regsSet assigns ** ((.x1 : Reg) ↦ᵣ ret)) := by
  induction assigns generalizing addr with
  | nil =>
      have hret := cpsTripleWithin_extend_code (cr' := cr)
        (hmono := fun a i h => hmem a i (by
          rw [show liRetTailProg [] = [Instr.JALR .x0 .x1 (0 : BitVec 12)]
              from rfl,
            CodeReq.ofProg_singleton]
          exact h))
        (h := EvmAsm.Evm64.ret_spec_within' addr ret)
      rw [halign] at hret
      exact cpsTripleWithin_weaken
        (fun h hp => by
          simp only [List.map_nil, regOwns_nil, sepConj_emp_left'] at hp
          exact hp)
        (fun h hq => by
          simp only [regsSet_nil, sepConj_emp_left']
          exact hq)
        hret
  | cons rc rest ih =>
      obtain ⟨rr, c⟩ := rc
      have hcons : liRetTailProg ((rr, c) :: rest)
          = Instr.LI rr c :: liRetTailProg rest := rfl
      -- head membership
      have hmemLi : ∀ a i, CodeReq.singleton addr (.LI rr c) a = some i →
          cr a = some i := by
        intro a i h
        refine hmem a i ?_
        rw [hcons, CodeReq.ofProg_cons]
        simp only [CodeReq.union, h]
      -- tail membership (the suffix based 4 bytes further)
      have hmemRest : ∀ a i,
          CodeReq.ofProg (addr + 4) (liRetTailProg rest) a = some i →
          cr a = some i := by
        intro a i h
        refine hmem a i ?_
        rw [hcons, show (Instr.LI rr c :: liRetTailProg rest)
            = [Instr.LI rr c] ++ liRetTailProg rest from rfl]
        refine CodeReq.ofProg_mono_append_right addr [Instr.LI rr c]
          (liRetTailProg rest) ?_ a i ?_
        · have hlen' : rest.length < 2 ^ 60 := by
            simp only [List.length_cons] at hlen
            omega
          simp only [List.length_append, List.length_cons, List.length_nil,
            liRetTailProg, List.length_map]
          omega
        · rwa [show (addr + BitVec.ofNat 64
              (4 * ([Instr.LI rr c] : List Instr).length)) = addr + 4
            from rfl]
      have hli := cpsTripleWithin_extend_code (cr' := cr) (hmono := hmemLi)
        (h := li_spec_gen_own_within rr c addr
          (hnz (rr, c) (List.mem_cons_self ..)))
      have hnz' : ∀ rc' ∈ rest, rc'.1 ≠ .x0 :=
        fun rc' hrc' => hnz rc' (List.mem_cons_of_mem _ hrc')
      have hlen' : rest.length < 2 ^ 60 := by
        simp only [List.length_cons] at hlen
        omega
      have hih := ih (addr + 4) hnz' hlen' hmemRest
      have hliF := cpsTripleWithin_frameR
        (regOwns (rest.map Prod.fst) ** ((.x1 : Reg) ↦ᵣ ret))
        (pcFree_sepConj (pcFree_regOwns _) pcFree_regIs) hli
      have hihF := cpsTripleWithin_frameR (rr ↦ᵣ c)
        pcFree_regIs hih
      have hc := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) hliF hihF
      refine cpsTripleWithin_weaken
        (fun h hp => by
          simp only [List.map_cons, regOwns_cons] at hp
          xperm_hyp hp)
        (fun h hq => by
          simp only [regsSet_cons]
          xperm_hyp hq)
        (cpsTripleWithin_mono_nSteps (by simp only [List.length_cons]; omega) hc)

#print axioms multiRegRetTail_spec

end EvmAsm.Rv64.SAsm
