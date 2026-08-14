/-
  EvmAsm.Rv64.SAsm.RetFromLoop

  **Early-return-from-loop via the shared epilogue** (bead evm-asm-4ch8f.70.2).

  The shape survey (docs/agents/4ch8f-shape-survey.md §4.2) found exactly one
  emitted control shape no combinator byte-matched: `mpt_set` / `mpt_insert`
  (and their linked-image `mpt_set_acc` / `mpt_insert_acc` variants) return
  from the WHOLE function out of the bubble-up loop.  At the machine level the
  shape is:

  ```
  .Lbubble: beqz s7, .Lroot          -- loop guard → post
            …body…
            bnez a0, .Lfail          -- the "early return": break PAST the ret
            …body…
            j .Lbubble               -- back-edge
  .Lroot:   …post…                   -- falls through into the epilogue
  .Lret:    …frame restore…
            ret                      -- the ONE ret of the whole routine
  .Lfail:   li a0, 2
            j .Lret                  -- BACKWARD jump into the shared epilogue
  ```

  There is no second `ret`: the "mid-loop function return" is a break to a
  status-setting stub that jumps back into the single shared epilogue — both
  paths restore the same frame by construction.  So the shape resolves
  **byte-transparently** (survey option 1, whileBreak-to-epilogue): the loop
  is `twoBreakRetLoop_spec` / `breakStation_spec` (TwoBreakWritable.lean) with
  the shared continuation instantiated at the routine's exit, and the ONLY
  missing piece is the break tail — a `li*` register-assignment run ending in
  a `JAL x0` join instead of its own `ret`.  This file adds it:

  * `liJumpTailRaw` / `multiRegJumpTail_spec` — the raw `li rd, c ; … ; j`
    escape hatch, proven once per tail address.  The typed `joinTailBack` and
    `joinTailForward` constructors below are the checked interfaces used by
    callers: their jump offset is derived from the continuation layout rather
    than supplied as a `BitVec`.

  * `jumpJoinTail_spec` — the whileBreak-to-epilogue composition: given the
    shared epilogue's continuation triple at the join, the break tail reaches
    the function's `ret` continuation.  This is what a `breakStation_spec` /
    `twoBreakRetLoop_spec` break arm instantiates for the
    early-return-from-loop shape.

  * `EarlyRetLoop` — the end-to-end mechanism demo on the minimal
    8-instruction routine with the exact mpt shape (loop → break → fail stub
    → backward jump → shared `ret`), at a SYMBOLIC base, with a genuine
    input-dependent post.

  Everything is at `cpsTripleWithin` level (additive; no `Ast`/`Vc`/
  `StmtSound` changes).  The byte-identity check against the emitted
  `mptSetAcc_prog` / `mptInsertAcc_prog` lives in
  `EvmAsm/Codegen/Programs/MptEarlyRetShape.lean`.
-/

import EvmAsm.Rv64.SAsm.MultiRegRetTail
import EvmAsm.Rv64.SAsm.Flatten

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

-- ============================================================================
-- §1  The jump-join tail
-- ============================================================================

/-- Raw escape hatch for a straight-line multi-register jump tail.

    Callers that know the continuation layout should use `joinTailBack` or
    `joinTailForward` instead.  Keeping the offset-taking primitive named
    `Raw` makes the remaining unstructured uses auditable. -/
def liJumpTailRaw (assigns : List (Reg × Word)) (ofs : BitVec 21) : List Instr :=
  assigns.map (fun rc => .LI rc.1 rc.2) ++ [.JAL .x0 ofs]

/-- A named instruction span used as a join/skip layout.  The cached length
    keeps large emitted windows reducible while `length_eq` ties it back to
    the actual instructions. -/
structure JoinSpan where
  code : List Instr
  slots : Nat
  length_eq : code.length = slots

/-- A jump tail that joins a continuation immediately before the tail.

    The target is the start of `continuation`; the backward offset is derived
    from the continuation and assignment lengths.  The range hypotheses are
    part of the constructor so an out-of-range JAL cannot be represented by
    this typed interface. -/
def joinTailBack (assigns : List (Reg × Word)) (continuation : JoinSpan)
    (_hpos : 0 < continuation.slots + assigns.length)
    (_hrange : 4 * (continuation.slots + assigns.length) ≤ 2 ^ 20) : List Instr :=
  assigns.map (fun rc => .LI rc.1 rc.2) ++
    [.JAL .x0 (Stmt.jBack (continuation.slots + assigns.length))]

/-- A jump tail that skips `skipped` instructions before joining the following
    continuation.  The forward offset is derived from that skipped layout. -/
def joinTailForward (assigns : List (Reg × Word)) (skipped : JoinSpan)
    (_hrange : 4 * (skipped.slots + 1) < 2 ^ 20) : List Instr :=
  assigns.map (fun rc => .LI rc.1 rc.2) ++
    [.JAL .x0 (Stmt.jFwd (skipped.slots + 1))]

/-- **The multi-register jump-join tail**, proven once per tail address:
    from ownership of the assigned registers, the tail transfers control to
    the join address with EXACTLY those registers pinned to their constants
    (`regsSet assigns`) — no other effect.  The `multiRegRetTail_spec`
    sibling whose terminal instruction is an unconditional `JAL x0` into a
    shared epilogue instead of its own `ret`. -/
theorem multiRegJumpTail_spec (cr : CodeReq) (addr : Word) (ofs : BitVec 21)
    (assigns : List (Reg × Word))
    (hnz : ∀ rc ∈ assigns, rc.1 ≠ .x0)
    (hlen : assigns.length < 2 ^ 60)
    (hmem : ∀ a i, CodeReq.ofProg addr (liJumpTailRaw assigns ofs) a = some i →
      cr a = some i) :
    cpsTripleWithin (assigns.length + 1) addr
      (addr + BitVec.ofNat 64 (4 * assigns.length) + signExtend21 ofs) cr
      (regOwns (assigns.map Prod.fst)) (regsSet assigns) := by
  induction assigns generalizing addr with
  | nil =>
      have hjal := cpsTripleWithin_extend_code (cr' := cr)
        (hmono := fun a i h => hmem a i (by
          rw [show liJumpTailRaw [] ofs = [Instr.JAL .x0 ofs] from rfl,
            CodeReq.ofProg_singleton]
          exact h))
        (h := jal_x0_spec_gen_within ofs addr)
      rw [show addr + BitVec.ofNat 64 (4 * ([] : List (Reg × Word)).length)
          = addr from by
        rw [show BitVec.ofNat 64 (4 * ([] : List (Reg × Word)).length)
            = (0 : Word) from rfl]
        exact BitVec.add_zero addr]
      exact cpsTripleWithin_weaken
        (fun h hp => by
          simp only [List.map_nil, regOwns_nil] at hp
          exact hp)
        (fun h hq => by
          simp only [regsSet_nil]
          exact hq)
        hjal
  | cons rc rest ih =>
      obtain ⟨rr, c⟩ := rc
      have hcons : liJumpTailRaw ((rr, c) :: rest) ofs
          = Instr.LI rr c :: liJumpTailRaw rest ofs := rfl
      -- head membership
      have hmemLi : ∀ a i, CodeReq.singleton addr (.LI rr c) a = some i →
          cr a = some i := by
        intro a i h
        refine hmem a i ?_
        rw [hcons, CodeReq.ofProg_cons]
        simp only [CodeReq.union, h]
      -- tail membership (the suffix based 4 bytes further)
      have hmemRest : ∀ a i,
          CodeReq.ofProg (addr + 4) (liJumpTailRaw rest ofs) a = some i →
          cr a = some i := by
        intro a i h
        refine hmem a i ?_
        rw [hcons, show (Instr.LI rr c :: liJumpTailRaw rest ofs)
            = [Instr.LI rr c] ++ liJumpTailRaw rest ofs from rfl]
        refine CodeReq.ofProg_mono_append_right addr [Instr.LI rr c]
          (liJumpTailRaw rest ofs) ?_ a i ?_
        · have hlen' : rest.length < 2 ^ 60 := by
            simp only [List.length_cons] at hlen
            omega
          simp only [List.length_append, List.length_cons, List.length_nil,
            liJumpTailRaw, List.length_map]
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
      -- rebase the IH's join address at the cons head's address
      have hexit : (addr + 4) + BitVec.ofNat 64 (4 * rest.length)
          = addr + BitVec.ofNat 64 (4 * ((rr, c) :: rest).length) := by
        rw [BitVec.add_assoc]
        congr 1
        rw [show 4 * ((rr, c) :: rest).length = 4 + 4 * rest.length from by
          simp only [List.length_cons]; omega]
        rw [BitVec.ofNat_add]
        rfl
      rw [hexit] at hih
      have hliF := cpsTripleWithin_frameR
        (regOwns (rest.map Prod.fst))
        (pcFree_regOwns _) hli
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

/-- Typed backward-join adapter for `multiRegJumpTail_spec`.  The caller names
    the continuation whose start is the destination; it never supplies a raw
    JAL immediate. -/
theorem multiRegJumpTailBack_spec (cr : CodeReq) (addr : Word)
    (assigns : List (Reg × Word)) (continuation : JoinSpan)
    (hpos : 0 < continuation.slots + assigns.length)
    (hrange : 4 * (continuation.slots + assigns.length) ≤ 2 ^ 20)
    (hnz : ∀ rc ∈ assigns, rc.1 ≠ .x0)
    (hlen : assigns.length < 2 ^ 60)
    (hmem : ∀ a i,
      CodeReq.ofProg addr (joinTailBack assigns continuation hpos hrange) a = some i →
      cr a = some i) :
    cpsTripleWithin (assigns.length + 1) addr
      (addr + BitVec.ofNat 64 (4 * assigns.length) +
        signExtend21 (Stmt.jBack (continuation.slots + assigns.length))) cr
      (regOwns (assigns.map Prod.fst)) (regsSet assigns) := by
  simpa [joinTailBack, liJumpTailRaw] using
    (multiRegJumpTail_spec cr addr
      (Stmt.jBack (continuation.slots + assigns.length)) assigns hnz hlen
      (by
        intro a i hi
        exact hmem a i (by simpa [joinTailBack, liJumpTailRaw] using hi)))


-- ============================================================================
-- §2  whileBreak-to-epilogue: the tail joined to the shared epilogue
-- ============================================================================

/-- **whileBreak-to-epilogue.**  The break/fail tail sets its status
    registers and jumps (`JAL x0`) BACKWARD into the shared epilogue at the
    join; given the epilogue's continuation triple (proven ONCE per routine
    and reused by the fall-through exit as well), the tail reaches the
    function's `ret` continuation.  A `breakStation_spec` /
    `twoBreakRetLoop_spec` break arm instantiates this for the
    early-return-from-loop shape (shape survey §4.2): the mid-loop
    "function return" is exactly `jump tail ∘ shared epilogue`. -/
theorem jumpJoinTail_spec {m : Nat} (cr : CodeReq) (addr ret : Word)
    (ofs : BitVec 21) (assigns : List (Reg × Word)) {F Q : Assertion}
    (hnz : ∀ rc ∈ assigns, rc.1 ≠ .x0)
    (hlen : assigns.length < 2 ^ 60)
    (hmem : ∀ a i, CodeReq.ofProg addr (liJumpTailRaw assigns ofs) a = some i →
      cr a = some i)
    (hF : F.pcFree)
    (hjoin : cpsTripleWithin m
      (addr + BitVec.ofNat 64 (4 * assigns.length) + signExtend21 ofs) ret cr
      (regsSet assigns ** F) Q) :
    cpsTripleWithin (assigns.length + 1 + m) addr ret cr
      (regOwns (assigns.map Prod.fst) ** F) Q :=
  cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_frameR F hF
      (multiRegJumpTail_spec cr addr ofs assigns hnz hlen hmem))
    hjoin

/-- Typed backward-join adapter: the join address is the start of the supplied
    continuation, and the JAL offset is derived from its layout. -/
theorem jumpJoinTailBack_spec {m : Nat} (cr : CodeReq) (addr ret : Word)
    (assigns : List (Reg × Word)) (continuation : JoinSpan)
    (hpos : 0 < continuation.slots + assigns.length)
    (hrange : 4 * (continuation.slots + assigns.length) ≤ 2 ^ 20)
    {F Q : Assertion}
    (hnz : ∀ rc ∈ assigns, rc.1 ≠ .x0)
    (hlen : assigns.length < 2 ^ 60)
    (hmem : ∀ a i,
      CodeReq.ofProg addr (joinTailBack assigns continuation hpos hrange) a = some i →
      cr a = some i)
    (hF : F.pcFree)
    (hjoin : cpsTripleWithin m
      (addr + BitVec.ofNat 64 (4 * assigns.length) +
        signExtend21 (Stmt.jBack (continuation.slots + assigns.length))) ret cr
      (regsSet assigns ** F) Q) :
    cpsTripleWithin (assigns.length + 1 + m) addr ret cr
      (regOwns (assigns.map Prod.fst) ** F) Q :=
  cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_frameR F hF
      (multiRegJumpTailBack_spec cr addr assigns continuation hpos hrange
        hnz hlen hmem))
    hjoin


-- ============================================================================
-- §3  End-to-end mechanism demo: the minimal early-return-from-loop routine
-- ============================================================================

namespace EarlyRetLoop

/-- The minimal routine with the exact mpt early-return-from-loop shape:
    count `x5` down to zero, but return status 2 from INSIDE the loop
    (through the fail stub and the shared epilogue) as soon as `x6 ≠ 0`.

    ```
    +0  hdr:  beqz x5 → post          (loop guard)
    +4        bnez x6 → fail          (the "early return" break)
    +8        addi x5, x5, -1
    +12       j hdr                   (back-edge)
    +16 post: li x10, 0               (fall-through exit)
    +20 ret:  jalr x0, x1, 0          (the ONE shared ret)
    +24 fail: li x10, 2
    +28       j ret                   (backward jump into the epilogue)
    ``` -/
def earlyRetLoopProg : List Instr :=
  [ .BEQ .x5 .x0 (16 : BitVec 13),
    .BNE .x6 .x0 (20 : BitVec 13),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-12 : BitVec 21),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (2 : Word),
    .JAL .x0 (-8 : BitVec 21) ]

-- The fail stub IS the jump-join tail combinator's byte shape.
#guard earlyRetLoopProg.drop 6
  = liJumpTailRaw [(.x10, (2 : Word))] (-8 : BitVec 21)
-- Exactly one `ret` in the whole routine: the shared epilogue.
#guard (earlyRetLoopProg.filter
  (fun i => i = Instr.JALR .x0 .x1 (0 : BitVec 12))).length = 1

/-- Singleton code-membership at the symbolic base. -/
private theorem erl_mem (base A : Word) (k : Nat) (ins : Instr)
    (hA : A = base + BitVec.ofNat 64 (4 * k)) (hk : k < 8)
    (hins : ∀ h : k < earlyRetLoopProg.length, earlyRetLoopProg[k]'h = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i →
      CodeReq.ofProg base earlyRetLoopProg a = some i := by
  have hk' : k < earlyRetLoopProg.length := by
    rw [show earlyRetLoopProg.length = 8 from rfl]
    exact hk
  exact CodeReq.ofProg_mem_at base A earlyRetLoopProg k ins hA hk' (hins hk')
    (by decide)

/-- Genuine post: status 2 (with the counter untouched — the break fires on
    the FIRST header evaluation) when the mid-loop return took the fail
    stub, else status 0 with the counter run to zero. -/
def erlPost (N flag ret : Word) : Assertion :=
  if flag ≠ 0 ∧ N ≠ 0 then
    ((.x5 : Reg) ↦ᵣ N) ** ((.x6 : Reg) ↦ᵣ flag) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (2 : Word)) **
    ((.x1 : Reg) ↦ᵣ ret)
  else
    ((.x5 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ flag) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
    ((.x1 : Reg) ↦ᵣ ret)

/-- Loop invariant at the i-th header evaluation: the counter holds `N - i`;
    a non-initial header evaluation certifies the break never fired. -/
def erlInv (N flag ret : Word) (i : Nat) : Assertion :=
  ⌜i ≤ N.toNat ∧ (i ≠ 0 → flag = 0)⌝ **
  (((.x5 : Reg) ↦ᵣ (N - BitVec.ofNat 64 i)) ** ((.x6 : Reg) ↦ᵣ flag) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x10 ** ((.x1 : Reg) ↦ᵣ ret))

/-- The shared epilogue continuation (the single `ret` at `base + 20`),
    proven once and reused by BOTH exits: the fall-through post and the
    mid-loop fail stub. -/
private theorem erlEpilogue_spec (base ret : Word) (P : Assertion)
    (hP : P.pcFree)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 1 (base + 20) ret
      (CodeReq.ofProg base earlyRetLoopProg)
      (((.x1 : Reg) ↦ᵣ ret) ** P)
      (((.x1 : Reg) ↦ᵣ ret) ** P) := by
  have hret := cpsTripleWithin_extend_code
    (cr' := CodeReq.ofProg base earlyRetLoopProg)
    (hmono := erl_mem base (base + 20) 5 (.JALR .x0 .x1 (0 : BitVec 12))
      rfl (by decide) (fun _ => rfl))
    (h := EvmAsm.Evm64.ret_spec_within' (base + 20) ret)
  rw [halign] at hret
  exact cpsTripleWithin_frameR P hP hret

/-- The fail stub at `base + 24` — `li x10, 2 ; j (base + 20)` — through the
    shared epilogue: the `jumpJoinTail_spec` instance on this routine. -/
private theorem erlFail_spec (base ret : Word) {F : Assertion}
    (hF : F.pcFree)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 3 (base + 24) ret
      (CodeReq.ofProg base earlyRetLoopProg)
      (regOwn .x10 ** (((.x1 : Reg) ↦ᵣ ret) ** F))
      (((.x10 : Reg) ↦ᵣ (2 : Word)) ** (((.x1 : Reg) ↦ᵣ ret) ** F)) := by
  have hepi : cpsTripleWithin 1 (base + 20) ret
      (CodeReq.ofProg base earlyRetLoopProg)
      (regsSet [(.x10, (2 : Word))] ** (((.x1 : Reg) ↦ᵣ ret) ** F))
      (((.x10 : Reg) ↦ᵣ (2 : Word)) ** (((.x1 : Reg) ↦ᵣ ret) ** F)) := by
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_)
      (erlEpilogue_spec base ret (((.x10 : Reg) ↦ᵣ (2 : Word)) ** F)
        (pcFree_sepConj pcFree_regIs hF) halign)
    · simp only [regsSet_cons, regsSet_nil, sepConj_emp_right'] at hp
      xperm_hyp hp
    · xperm_hyp hq
  have h := jumpJoinTail_spec (m := 1)
    (CodeReq.ofProg base earlyRetLoopProg) (base + 24) ret
    (-8 : BitVec 21) [(.x10, (2 : Word))]
    (F := ((.x1 : Reg) ↦ᵣ ret) ** F)
    (by decide) (by decide)
    (CodeReq.ofProg_mono_sub base (base + 24) earlyRetLoopProg
      (liJumpTailRaw [(.x10, (2 : Word))] (-8 : BitVec 21)) 6 rfl
      rfl (by decide) (by decide))
    (pcFree_sepConj pcFree_regIs hF)
    (by
      rw [show (base + 24)
          + BitVec.ofNat 64
            (4 * ([((.x10 : Reg), (2 : Word))] : List (Reg × Word)).length)
          + signExtend21 (-8 : BitVec 21) = base + 20 from by
        rw [BitVec.add_assoc, BitVec.add_assoc]
        congr 1]
      exact hepi)
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq) h
  simp only [List.map_cons, List.map_nil, regOwns_cons, regOwns_nil,
    sepConj_emp_right']
  xperm_hyp hp

/-- One loop iteration (`i < N.toNat`): from the header with `erlInv i`,
    either the break fires — the fail stub and the shared epilogue complete
    with the genuine post — or control returns to the header with the
    invariant advanced.  Exactly the `twoBreakRetLoop_spec` iteration
    shape. -/
private theorem erlIter_spec (base ret N flag : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (i : Nat) (hi : i < N.toNat) :
    cpsBranchWithin 6 base
      (CodeReq.ofProg base earlyRetLoopProg)
      (erlInv N flag ret i)
      ret (erlPost N flag ret)
      base (erlInv N flag ret (i + 1)) := by
  set CR := CodeReq.ofProg base earlyRetLoopProg with hCR
  unfold erlInv
  refine cpsBranchWithin_pure_pre (fun hpure => ?_)
  obtain ⟨hile, hbrk⟩ := hpure
  have hctr_ne : N - BitVec.ofNat 64 i ≠ (0 : Word) := by
    intro h0
    have hiN : i < 2 ^ 64 := by
      have := N.isLt
      omega
    bv_omega
  -- ---- header guard: beqz x5 → post; not taken (the counter is nonzero) --
  have hbeq := cpsBranchWithin_extend_code
    (hmono := erl_mem base base 0 (.BEQ .x5 .x0 (16 : BitVec 13))
      (by rw [show BitVec.ofNat 64 (4 * 0) = (0 : Word) from rfl]
          exact (BitVec.add_zero base).symm)
      (by decide) (fun _ => rfl))
    (h := beq_spec_gen_within .x5 .x0 (16 : BitVec 13)
      (N - BitVec.ofNat 64 i) 0 base)
  rw [show base + signExtend13 (16 : BitVec 13) = base + 16 from by
    rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]]
    at hbeq
  have hbeqF := cpsBranchWithin_frameR
    (((.x6 : Reg) ↦ᵣ flag) ** regOwn .x10 ** ((.x1 : Reg) ↦ᵣ ret))
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regOwn pcFree_regIs))
    hbeq
  refine cpsBranchWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_merge_branch_same_cr (m := 5) hbeqF ?taken ?fall)
  case taken =>
    -- x5 = 0 contradicts the counter bound
    refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_pure_pre
        (H := (((.x5 : Reg) ↦ᵣ (N - BitVec.ofNat 64 i)) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ flag) **
          regOwn .x10 ** ((.x1 : Reg) ↦ᵣ ret)))
        (fun hc => absurd hc hctr_ne))
  case fall =>
    -- strip the (unused) header branch fact
    refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_pure_pre
        (H := (((.x5 : Reg) ↦ᵣ (N - BitVec.ofNat 64 i)) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ flag) **
          regOwn .x10 ** ((.x1 : Reg) ↦ᵣ ret)))
        (fun _hne => ?_))
    -- ---- at base+4: bnez x6 → fail stub (base+24) ----
    have hbne := cpsBranchWithin_extend_code
      (hmono := erl_mem base (base + 4) 1 (.BNE .x6 .x0 (20 : BitVec 13))
        rfl (by decide) (fun _ => rfl))
      (h := bne_spec_gen_within .x6 .x0 (20 : BitVec 13) flag 0 (base + 4))
    rw [show (base + 4) + signExtend13 (20 : BitVec 13) = base + 24 from by
        rw [BitVec.add_assoc]
        congr 1,
      show (base + 4) + 4 = base + 8 from by
        rw [BitVec.add_assoc]
        congr 1] at hbne
    have hbneF := cpsBranchWithin_frameR
      (((.x5 : Reg) ↦ᵣ (N - BitVec.ofNat 64 i)) ** regOwn .x10 **
        ((.x1 : Reg) ↦ᵣ ret))
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regOwn pcFree_regIs))
      hbne
    refine cpsBranchWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_merge_branch_same_cr (m := 4) hbneF ?brk ?cont)
    case brk =>
      -- flag ≠ 0: since a later iteration would force flag = 0, this is
      -- the FIRST header evaluation — the counter still holds N — and the
      -- fail stub + shared epilogue return with status 2.
      refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun _ hq => hq) (fun _ hq => hq)
        (cpsBranchWithin_pure_pre
          (H := (((.x6 : Reg) ↦ᵣ flag) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x5 : Reg) ↦ᵣ (N - BitVec.ofNat 64 i)) ** regOwn .x10 **
            ((.x1 : Reg) ↦ᵣ ret)))
          (fun hflag => ?_))
      have hizero : i = 0 := by
        by_contra hne
        exact hflag (hbrk hne)
      have hN0 : N - BitVec.ofNat 64 i = N := by
        rw [hizero]
        bv_omega
      have hNne : N ≠ 0 := fun h0 => hctr_ne (by rw [hN0, h0])
      refine cpsTripleWithin_as_cpsBranchWithin_left base
        (erlInv N flag ret (i + 1)) ?_
      have hfail := erlFail_spec base ret
        (F := ((.x5 : Reg) ↦ᵣ (N - BitVec.ofNat 64 i)) **
          ((.x6 : Reg) ↦ᵣ flag) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          pcFree_regIs)) halign
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
          (fun h hq => ?_) hfail)
      unfold erlPost
      rw [if_pos ⟨hflag, hNne⟩]
      rw [hN0] at hq
      xperm_hyp hq
    case cont =>
      -- flag = 0: decrement and take the back-edge to the header.
      refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun _ hq => hq) (fun _ hq => hq)
        (cpsBranchWithin_pure_pre
          (H := (((.x6 : Reg) ↦ᵣ flag) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x5 : Reg) ↦ᵣ (N - BitVec.ofNat 64 i)) ** regOwn .x10 **
            ((.x1 : Reg) ↦ᵣ ret)))
          (fun hflag0 => ?_))
      have haddi := cpsTripleWithin_extend_code (cr' := CR)
        (hmono := erl_mem base (base + 8) 2 (.ADDI .x5 .x5 (-1 : BitVec 12))
          rfl (by decide) (fun _ => rfl))
        (h := addi_spec_gen_same_within .x5 (N - BitVec.ofNat 64 i)
          (-1 : BitVec 12) (base + 8) (by decide))
      rw [show (base + 8) + 4 = base + 12 from by
        rw [BitVec.add_assoc]
        congr 1] at haddi
      have hdec : (N - BitVec.ofNat 64 i) + signExtend12 (-1 : BitVec 12)
          = N - BitVec.ofNat 64 (i + 1) := by
        rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide,
          BitVec.ofNat_add, show BitVec.ofNat 64 1 = (1 : Word) from rfl]
        bv_omega
      rw [hdec] at haddi
      have hjal := cpsTripleWithin_extend_code (cr' := CR)
        (hmono := erl_mem base (base + 12) 3 (.JAL .x0 (-12 : BitVec 21))
          rfl (by decide) (fun _ => rfl))
        (h := jal_x0_spec_gen_within (-12 : BitVec 21) (base + 12))
      rw [show (base + 12) + signExtend21 (-12 : BitVec 21) = base from by
        rw [BitVec.add_assoc,
          show (12 : Word) + signExtend21 (-12 : BitVec 21) = 0 from by
            decide]
        exact BitVec.add_zero base] at hjal
      have haddiF := cpsTripleWithin_frameR
        (((.x6 : Reg) ↦ᵣ flag) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x10 ** ((.x1 : Reg) ↦ᵣ ret))
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regOwn pcFree_regIs))) haddi
      have hjalF := cpsTripleWithin_frameR
        (((.x5 : Reg) ↦ᵣ (N - BitVec.ofNat 64 (i + 1))) **
          ((.x6 : Reg) ↦ᵣ flag) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x10 ** ((.x1 : Reg) ↦ᵣ ret))
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regOwn pcFree_regIs)))) hjal
      rw [sepConj_emp_left'] at hjalF
      have hbody := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) haddiF hjalF
      refine cpsTripleWithin_as_cpsBranchWithin_right ret
        (erlPost N flag ret) ?_
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
          (fun h hq => ?_) hbody)
      refine (sepConj_pure_left h).2 ⟨⟨by omega, fun _ => hflag0⟩, ?_⟩
      xperm_hyp hq

/-- The exhaustion path (`erlInv N.toNat` at the header): the guard fires,
    the fall-through post runs, and the shared epilogue — the SAME epilogue
    instance the fail stub jumps into — returns with status 0. -/
private theorem erlExhaust_spec (base ret N flag : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 3 base ret
      (CodeReq.ofProg base earlyRetLoopProg)
      (erlInv N flag ret N.toNat)
      (erlPost N flag ret) := by
  set CR := CodeReq.ofProg base earlyRetLoopProg with hCR
  unfold erlInv
  refine cpsTripleWithin_pure_pre (fun hpure => ?_)
  obtain ⟨-, hbrk⟩ := hpure
  have hctr0 : N - BitVec.ofNat 64 N.toNat = (0 : Word) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact BitVec.sub_self N
  have hnotif : ¬ (flag ≠ 0 ∧ N ≠ 0) := by
    rintro ⟨hflag, hN⟩
    refine hflag (hbrk (fun h0 => hN ?_))
    have := congrArg (BitVec.ofNat 64) h0
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  -- ---- header guard fires ----
  have hbeq := cpsBranchWithin_extend_code
    (hmono := erl_mem base base 0 (.BEQ .x5 .x0 (16 : BitVec 13))
      (by rw [show BitVec.ofNat 64 (4 * 0) = (0 : Word) from rfl]
          exact (BitVec.add_zero base).symm)
      (by decide) (fun _ => rfl))
    (h := beq_spec_gen_within .x5 .x0 (16 : BitVec 13)
      (N - BitVec.ofNat 64 N.toNat) 0 base)
  rw [show base + signExtend13 (16 : BitVec 13) = base + 16 from by
    rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]]
    at hbeq
  have hbeqF := cpsBranchWithin_frameR
    (((.x6 : Reg) ↦ᵣ flag) ** regOwn .x10 ** ((.x1 : Reg) ↦ᵣ ret))
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regOwn pcFree_regIs))
    hbeq
  -- ---- post: li x10, 0 then the shared epilogue ----
  have hli := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := erl_mem base (base + 16) 4 (.LI .x10 (0 : Word))
      rfl (by decide) (fun _ => rfl))
    (h := li_spec_gen_own_within .x10 (0 : Word) (base + 16) (by decide))
  rw [show (base + 16) + 4 = base + 20 from by
    rw [BitVec.add_assoc]
    congr 1] at hli
  have hliF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (N - BitVec.ofNat 64 N.toNat)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ flag) **
      ((.x1 : Reg) ↦ᵣ ret))
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs pcFree_regIs))) hli
  have hepi := erlEpilogue_spec base ret
    (((.x5 : Reg) ↦ᵣ (N - BitVec.ofNat 64 N.toNat)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ flag) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)))
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs pcFree_regIs))) halign
  have htail := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hliF hepi
  refine cpsTripleWithin_mono_nSteps (show 1 + 2 ≤ 3 from by omega) ?_
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsBranchWithin_merge_same_cr (nSteps2 := 2) hbeqF ?taken ?dead)
  case taken =>
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ hq => hq)
      (cpsTripleWithin_pure_pre
        (H := (((.x5 : Reg) ↦ᵣ (N - BitVec.ofNat 64 N.toNat)) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ flag) **
          regOwn .x10 ** ((.x1 : Reg) ↦ᵣ ret)))
        (fun _ => ?_))
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ?_) htail
    unfold erlPost
    rw [if_neg hnotif]
    rw [hctr0] at hq
    xperm_hyp hq
  case dead =>
    -- fall-through arm: x5 ≠ 0 contradicts the exhausted counter
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ hq => hq)
      (cpsTripleWithin_pure_pre
        (H := (((.x5 : Reg) ↦ᵣ (N - BitVec.ofNat 64 N.toNat)) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ flag) **
          regOwn .x10 ** ((.x1 : Reg) ↦ᵣ ret)))
        (fun hne => absurd hctr0 hne))

/-- **The end-to-end early-return-from-loop spec** at a symbolic base:
    from the entry register state, the routine reaches the shared `ret`
    continuation with the genuine input-dependent post — status 2 with the
    counter untouched when `flag ≠ 0` fires the mid-loop return, else
    status 0 with the counter exhausted.  The loop is
    `twoBreakRetLoop_spec`; the mid-loop return is the
    `breakStation`-shaped iteration + `jumpJoinTail_spec` through the ONE
    shared epilogue. -/
theorem earlyRetLoop_spec (base ret N flag : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (N.toNat * 6 + 3) base ret
      (CodeReq.ofProg base earlyRetLoopProg)
      (((.x5 : Reg) ↦ᵣ N) ** ((.x6 : Reg) ↦ᵣ flag) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x10 ** ((.x1 : Reg) ↦ᵣ ret))
      (erlPost N flag ret) := by
  have hloop := twoBreakRetLoop_spec (hdr := base) (ret := ret)
    (cr := CodeReq.ofProg base earlyRetLoopProg)
    (Q := erlPost N flag ret) N.toNat 6 3 (erlInv N flag ret)
    (fun i hi => erlIter_spec base ret N flag halign i hi)
    (erlExhaust_spec base ret N flag halign)
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq) hloop
  unfold erlInv
  refine (sepConj_pure_left h).2 ⟨⟨by omega, fun h0 => absurd rfl h0⟩, ?_⟩
  rw [show N - BitVec.ofNat 64 0 = N from by bv_omega]
  exact hp


end EarlyRetLoop

end EvmAsm.Rv64.SAsm
