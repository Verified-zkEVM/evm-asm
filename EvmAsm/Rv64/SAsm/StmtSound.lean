/-
  EvmAsm.Rv64.SAsm.StmtSound

  The generic soundness theorem of the SAsm VC generator: for every
  statement, if its labeled pure VCs hold then the flattened code satisfies
  a bounded CPS triple from `asrtM reg reach` to `asrtM reg (sp reg s reach)`
  — the exposed register file plus the function's read-only byte region.

  Proven once, by structural induction on `Stmt`; each constructor maps onto
  an existing WP combinator (docs/sasm-design.md §3.5).  The whole statement
  runs against one ambient `cr` that merely *contains* the flattened code
  (`hcode`), so no disjointness obligation ever reaches a user: sequential
  splits use `cpsTripleWithin_seq_same_cr` plus `CodeReq.ofProg` containment.

  This is the *leaf* theorem (`callFree` bodies): every non-exposed register
  — in particular `ra` — is untouched and framed, which is what lets
  `Fn.toHandle` package such functions as callees.  Bodies containing calls
  use `Stmt.soundR` (StmtSoundCall.lean).
-/

import EvmAsm.Rv64.SAsm.BlockSound
import EvmAsm.Rv64.SAsm.CtrlSpecs

namespace EvmAsm.Rv64
namespace SAsm

-- ============================================================================
-- CodeReq.ofProg containment lemmas
-- ============================================================================

/-- An address mapped by `ofProg` lies at some instruction slot. -/
theorem ofProg_some_range {base : Word} {prog : List Instr} {a : Word} {i : Instr}
    (h : CodeReq.ofProg base prog a = some i) :
    ∃ k, k < prog.length ∧ a = base + BitVec.ofNat 64 (4 * k) := by
  induction prog generalizing base with
  | nil => exact absurd h (by simp [CodeReq.ofProg_nil, CodeReq.empty])
  | cons j rest ih =>
      rw [CodeReq.ofProg_cons] at h
      simp only [CodeReq.union, CodeReq.singleton] at h
      by_cases ha : a = base
      · refine ⟨0, by simp, ?_⟩
        rw [ha]
        simp
      · rw [if_neg (by simpa using ha)] at h
        obtain ⟨k, hk, hak⟩ := ih h
        refine ⟨k + 1, by simpa using Nat.succ_lt_succ hk, ?_⟩
        rw [hak]
        bv_omega

/-- Code of a list prefix is contained in the whole list's `ofProg`. -/
theorem ofProg_mono_left {base : Word} {p1 p2 : List Instr} :
    ∀ a i, CodeReq.ofProg base p1 a = some i →
      CodeReq.ofProg base (p1 ++ p2) a = some i := by
  intro a i h
  rw [CodeReq.ofProg_append]
  simp only [CodeReq.union, h]

/-- Code of a list suffix is contained in the whole list's `ofProg`,
    provided the total footprint does not wrap the address space. -/
theorem ofProg_mono_right {base : Word} {p1 p2 : List Instr}
    (hlen : 4 * (p1.length + p2.length) ≤ 2 ^ 64) :
    ∀ a i, CodeReq.ofProg (base + BitVec.ofNat 64 (4 * p1.length)) p2 a = some i →
      CodeReq.ofProg base (p1 ++ p2) a = some i := by
  intro a i h
  rw [CodeReq.ofProg_append]
  have hnone : CodeReq.ofProg base p1 a = none := by
    apply CodeReq.ofProg_none_range
    intro k hk heq
    obtain ⟨j, hj, hja⟩ := ofProg_some_range h
    rw [heq, addr_shift] at hja
    have htn := congrArg BitVec.toNat hja
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at htn
    have hb := base.isLt
    omega
  simp only [CodeReq.union, hnone, h]

/-- The head instruction of a `cons` program is contained in its `ofProg`. -/
theorem ofProg_head {base : Word} {i : Instr} {rest : List Instr} :
    ∀ a j, CodeReq.singleton base i a = some j →
      CodeReq.ofProg base (i :: rest) a = some j := by
  intro a j h
  rw [CodeReq.ofProg_cons]
  simp only [CodeReq.union, h]

/-- The tail of a `cons` program is contained in its `ofProg` (no wrap). -/
theorem ofProg_cons_tail {base : Word} {i : Instr} {rest : List Instr}
    (hlen : 4 * (rest.length + 1) ≤ 2 ^ 64) :
    ∀ a j, CodeReq.ofProg (base + 4) rest a = some j →
      CodeReq.ofProg base (i :: rest) a = some j := by
  intro a j h
  exact ofProg_mono_right (p1 := [i])
    (by simpa [Nat.add_comm] using hlen) a j (by simpa using h)

-- ============================================================================
-- Reach-level helper triples
-- ============================================================================

/-- Split an `asrtOf` precondition into a per-register-file family. -/
theorem cpsTripleWithin_exists_pre {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {reach : Reach} {Q : Assertion}
    (h : ∀ rf, reach rf → cpsTripleWithin n entry exit_ cr (regFileIs rf) Q) :
    cpsTripleWithin n entry exit_ cr (asrtOf reach) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, ⟨rf, hrf1, hreach⟩, hR2⟩ := hPR
  exact h rf hreach R hR s hcr ⟨hp, hcompat, h1, h2, hd, hu, hrf1, hR2⟩ hpc

/-- Zero-step triple from a pointwise entailment. -/
theorem cpsTripleWithin_entails {entry : Word} {cr : CodeReq} {P Q : Assertion}
    (h : ∀ hp, P hp → Q hp) :
    cpsTripleWithin 0 entry entry cr P Q := by
  intro R hR s hcr hPR hpc
  refine ⟨0, Nat.le_refl 0, s, rfl, hpc, ?_⟩
  obtain ⟨hp, hcompat, hpq⟩ := hPR
  exact ⟨hp, hcompat, sepConj_mono_left h hp hpq⟩

/-- Any triple holds from an unsatisfiable precondition. -/
theorem cpsTripleWithin_unreachable {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} (h : ∀ hp, P hp → False) :
    cpsTripleWithin n entry exit_ cr P Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR
  exact absurd hP1 (h h1)

/-- `wf` is invariant under condition negation. -/
theorem Cond.wf_neg (c : Cond) : c.neg.wf = c.wf := by
  cases c <;> rfl

-- ============================================================================
-- The generic soundness theorem
-- ============================================================================

/-- Soundness of the SAsm VC generator (docs/sasm-design.md §3.5) for
    call-free statements: if the labeled VCs of `s` hold, the flattened code
    of `s` placed at `base` satisfies a bounded CPS triple from
    `asrtM reg reach` to `asrtM reg (sp reg s reach)`, within `s.steps`
    machine steps, under any code requirement `cr` containing the flattened
    code.

    `hofs`/`hsz` are decidable per program; `hreg` is the region's
    well-formedness (decidable for concrete regions, `omega`-shaped for
    symbolic ones). -/
theorem Stmt.sound (reg : Region) (s : Stmt) (base : Word) (pfx : String)
    (reach : Reach) {cr : CodeReq}
    (hreg : reg.wf)
    (hleaf : s.callFree = true)
    (hofs : s.offsetsOk = true)
    (hsz : 4 * s.size < 2 ^ 64)
    (hcode : ∀ a i, CodeReq.ofProg base (s.flatten base) a = some i → cr a = some i)
    (hvcs : VCs.Hold (Stmt.vcs reg s pfx reach)) :
    cpsTripleWithin s.steps base (base + BitVec.ofNat 64 (4 * s.size)) cr
      (asrtM reg reach) (asrtM reg (Stmt.sp reg s reach)) := by
  induction s generalizing base pfx reach cr with
  | block lbl is =>
      have hok : blockOk is = true := hvcs.head
      have hmem : ∀ rf, reach rf → blockVCs reg rf is := by
        by_cases hl : hasLoad is
        · have ht := hvcs.tail
          simp only [Stmt.vcs, hl, if_true] at ht
          exact ht.head
        · exact fun rf _ =>
            blockVCs_of_not_hasLoad reg rf is (by simpa using hl)
      apply cpsTripleWithin_exists_pre_M
      intro rf hreach
      have h := execBlock_sound reg is rf base hreg hok (hmem rf hreach)
        (by simpa [Stmt.size] using hsz)
      have h' := cpsTripleWithin_extend_code hcode h
      refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h'
      intro hp hh
      exact sepConj_mono_left
        (fun hq hr => ⟨execBlock reg rf is, hr, rf, hreach, rfl⟩) hp hh
  | seq a b iha ihb =>
      simp only [Stmt.callFree, Bool.and_eq_true] at hleaf
      simp only [Stmt.offsetsOk, Bool.and_eq_true] at hofs
      simp only [Stmt.size] at hsz
      have hsza : 4 * a.size < 2 ^ 64 := by omega
      have hszb : 4 * b.size < 2 ^ 64 := by omega
      have hla : (a.flatten base).length = a.size := Stmt.flatten_length a base
      have hcode_a : ∀ a' i,
          CodeReq.ofProg base (a.flatten base) a' = some i → cr a' = some i :=
        fun a' i h => hcode a' i (ofProg_mono_left a' i h)
      have hcode_b : ∀ a' i,
          CodeReq.ofProg (base + BitVec.ofNat 64 (4 * a.size))
            (b.flatten (base + BitVec.ofNat 64 (4 * a.size))) a' = some i →
          cr a' = some i := by
        intro a' i h
        apply hcode
        apply ofProg_mono_right
          (by rw [hla, Stmt.flatten_length]; omega)
        rw [hla]
        exact h
      have h1 := iha base pfx reach hleaf.1 hofs.1 hsza hcode_a hvcs.left
      have h2 := ihb (base + BitVec.ofNat 64 (4 * a.size)) pfx (Stmt.sp reg a reach)
        hleaf.2 hofs.2 hszb hcode_b hvcs.right
      have h3 := cpsTripleWithin_seq_same_cr h1 h2
      rw [addr_shift] at h3
      have : 4 * a.size + 4 * b.size = 4 * (a.size + b.size) := by omega
      rw [this] at h3
      exact h3
  | ite lbl c t e iht ihe =>
      simp only [Stmt.callFree, Bool.and_eq_true] at hleaf
      simp only [Stmt.offsetsOk, Bool.and_eq_true, decide_eq_true_eq] at hofs
      obtain ⟨⟨⟨⟨hwf, hofsT⟩, hofsJ⟩, hOT⟩, hOE⟩ := hofs
      simp only [Stmt.size] at hsz
      -- Layout facts
      have hlt : (t.flatten (base + 4)).length = t.size := Stmt.flatten_length ..
      have haddr1 : (base + 4) + BitVec.ofNat 64 (4 * t.size)
          = base + BitVec.ofNat 64 (4 * (t.size + 1)) := by bv_omega
      have haddr2 : (base + BitVec.ofNat 64 (4 * (t.size + 1)))
            + BitVec.ofNat 64 (4 * (e.size + 1))
          = base + BitVec.ofNat 64 (4 * (t.size + e.size + 2)) := by bv_omega
      have haddr3 : (base + BitVec.ofNat 64 (4 * (t.size + 2)))
            + BitVec.ofNat 64 (4 * e.size)
          = base + BitVec.ofNat 64 (4 * (t.size + e.size + 2)) := by bv_omega
      have haddr4 : (base + BitVec.ofNat 64 (4 * (t.size + 1))) + 4
          = base + BitVec.ofNat 64 (4 * (t.size + 2)) := by bv_omega
      -- Code containment for the four regions
      have hflat : Stmt.flatten base (.ite lbl c t e)
          = (c.neg.toInstr (Stmt.brOfs (t.size + 2)))
            :: (t.flatten (base + 4)
                ++ .JAL .x0 (Stmt.jFwd (e.size + 1))
                :: e.flatten (base + BitVec.ofNat 64 (4 * (t.size + 2)))) := rfl
      have hlenAll : 4 * ((t.flatten (base + 4)
          ++ .JAL .x0 (Stmt.jFwd (e.size + 1))
          :: e.flatten (base + BitVec.ofNat 64 (4 * (t.size + 2)))).length + 1)
          ≤ 2 ^ 64 := by
        simp only [List.length_append, List.length_cons, hlt, Stmt.flatten_length]
        omega
      have hcode_br : ∀ a' i,
          CodeReq.singleton base (c.neg.toInstr (Stmt.brOfs (t.size + 2))) a' = some i →
          cr a' = some i := by
        intro a' i h
        exact hcode a' i (hflat ▸ ofProg_head a' i h)
      have hcode_t : ∀ a' i,
          CodeReq.ofProg (base + 4) (t.flatten (base + 4)) a' = some i →
          cr a' = some i := by
        intro a' i h
        exact hcode a' i (hflat ▸ ofProg_cons_tail hlenAll a' i (ofProg_mono_left a' i h))
      have hcode_jal : ∀ a' i,
          CodeReq.singleton (base + BitVec.ofNat 64 (4 * (t.size + 1)))
            (.JAL .x0 (Stmt.jFwd (e.size + 1))) a' = some i →
          cr a' = some i := by
        intro a' i h
        apply hcode a' i
        rw [hflat]
        apply ofProg_cons_tail hlenAll
        apply ofProg_mono_right (p1 := t.flatten (base + 4))
          (by simp only [List.length_cons, hlt, Stmt.flatten_length]; omega)
        rw [hlt, haddr1]
        exact ofProg_head a' i h
      have hcode_e : ∀ a' i,
          CodeReq.ofProg (base + BitVec.ofNat 64 (4 * (t.size + 2)))
            (e.flatten (base + BitVec.ofNat 64 (4 * (t.size + 2)))) a' = some i →
          cr a' = some i := by
        intro a' i h
        apply hcode a' i
        rw [hflat]
        apply ofProg_cons_tail hlenAll
        apply ofProg_mono_right (p1 := t.flatten (base + 4))
          (by simp only [List.length_cons, hlt, Stmt.flatten_length]; omega)
        rw [hlt, haddr1]
        apply ofProg_cons_tail
          (by rw [Stmt.flatten_length]; omega)
        rw [haddr4]
        exact h
      -- Branch spec at the header
      have hbr := branch_spec_asrt c.neg (Stmt.brOfs (t.size + 2)) reach base
        (by rw [Cond.wf_neg]; exact hwf)
      rw [signExtend13_brOfs hofsT] at hbr
      have hbr' := cpsBranchWithin_frameR (bytesRegion reg.base reg.bytes)
        (bytesRegion_pcFree _ _) (cpsBranchWithin_extend_code hcode_br hbr)
      -- Then-arm: t's code then the skip jump
      have ht := iht (base + 4) (pfx ++ lbl ++ ".t.")
        (fun rf => reach rf ∧ c.holds rf) hleaf.1 hOT (by omega) hcode_t hvcs.left
      rw [haddr1] at ht
      have hjal := jal0_spec_pcFree (Stmt.jFwd (e.size + 1))
        (base + BitVec.ofNat 64 (4 * (t.size + 1)))
        (pcFree_asrtM reg (Stmt.sp reg t fun rf => reach rf ∧ c.holds rf))
      rw [signExtend21_jFwd hofsJ, haddr2] at hjal
      have hjal' := cpsTripleWithin_extend_code hcode_jal hjal
      have htj := cpsTripleWithin_seq_same_cr ht hjal'
      -- Else-arm
      have he := ihe (base + BitVec.ofNat 64 (4 * (t.size + 2))) (pfx ++ lbl ++ ".e.")
        (fun rf => reach rf ∧ ¬ c.holds rf) hleaf.2 hOE (by omega) hcode_e hvcs.right
      rw [haddr3] at he
      -- Weaken branch posts: neg-condition denotations and arm preconditions
      have hbr'' : cpsBranchWithin 1 base cr (asrtM reg reach)
          (base + BitVec.ofNat 64 (4 * (t.size + 2)))
            (asrtM reg fun rf => reach rf ∧ ¬ c.holds rf)
          (base + 4) (asrtM reg fun rf => reach rf ∧ c.holds rf) := by
        refine cpsBranchWithin_weaken (fun _ hp => hp) ?_ ?_ hbr'
        · exact asrtM_mono (fun rf hh =>
            ⟨hh.1, (Cond.holds_neg c rf).mp hh.2⟩)
        · exact asrtM_mono (fun rf hh =>
            ⟨hh.1, Decidable.of_not_not
              (fun hcc => hh.2 ((Cond.holds_neg c rf).mpr hcc))⟩)
      -- Merge: taken exit is the else entry, not-taken is the then entry
      have harmE : cpsTripleWithin (max (t.steps + 1) e.steps)
          (base + BitVec.ofNat 64 (4 * (t.size + 2)))
          (base + BitVec.ofNat 64 (4 * (t.size + e.size + 2))) cr
          (asrtM reg fun rf => reach rf ∧ ¬ c.holds rf)
          (asrtM reg (Stmt.sp reg (.ite lbl c t e) reach)) := by
        refine cpsTripleWithin_mono_nSteps (Nat.le_max_right _ _)
          (cpsTripleWithin_weaken (fun _ hp => hp) ?_ he)
        exact asrtM_mono (fun rf hsp => Or.inr hsp)
      have harmT : cpsTripleWithin (max (t.steps + 1) e.steps)
          (base + 4)
          (base + BitVec.ofNat 64 (4 * (t.size + e.size + 2))) cr
          (asrtM reg fun rf => reach rf ∧ c.holds rf)
          (asrtM reg (Stmt.sp reg (.ite lbl c t e) reach)) := by
        refine cpsTripleWithin_mono_nSteps (Nat.le_max_left _ _)
          (cpsTripleWithin_weaken (fun _ hp => hp) ?_ htj)
        exact asrtM_mono (fun rf hsp => Or.inl hsp)
      exact cpsBranchWithin_merge_same_cr hbr'' harmE harmT
  | «when» lbl c b ihb =>
      simp only [Stmt.offsetsOk, Bool.and_eq_true, decide_eq_true_eq] at hofs
      obtain ⟨⟨hwf, hofsB⟩, hOB⟩ := hofs
      simp only [Stmt.size] at hsz
      have hlenAll : 4 * ((b.flatten (base + 4)).length + 1) ≤ 2 ^ 64 := by
        rw [Stmt.flatten_length]; omega
      have hflat : Stmt.flatten base (.when lbl c b)
          = (c.neg.toInstr (Stmt.brOfs (b.size + 1))) :: b.flatten (base + 4) := rfl
      have hcode_br : ∀ a' i,
          CodeReq.singleton base (c.neg.toInstr (Stmt.brOfs (b.size + 1))) a' = some i →
          cr a' = some i :=
        fun a' i h => hcode a' i (hflat ▸ ofProg_head a' i h)
      have hcode_b : ∀ a' i,
          CodeReq.ofProg (base + 4) (b.flatten (base + 4)) a' = some i →
          cr a' = some i :=
        fun a' i h => hcode a' i (hflat ▸ ofProg_cons_tail hlenAll a' i h)
      have hbr := branch_spec_asrt c.neg (Stmt.brOfs (b.size + 1)) reach base
        (by rw [Cond.wf_neg]; exact hwf)
      rw [signExtend13_brOfs hofsB] at hbr
      have hbr' := cpsBranchWithin_frameR (bytesRegion reg.base reg.bytes)
        (bytesRegion_pcFree _ _) (cpsBranchWithin_extend_code hcode_br hbr)
      have hb := ihb (base + 4) (pfx ++ lbl ++ ".")
        (fun rf => reach rf ∧ c.holds rf) (by simpa [Stmt.callFree] using hleaf)
        hOB (by omega) hcode_b hvcs
      rw [show (base + 4) + BitVec.ofNat 64 (4 * b.size)
          = base + BitVec.ofNat 64 (4 * (b.size + 1)) from by bv_omega] at hb
      -- taken (¬c): skip directly to the exit
      have hskip : cpsTripleWithin b.steps
          (base + BitVec.ofNat 64 (4 * (b.size + 1)))
          (base + BitVec.ofNat 64 (4 * (b.size + 1))) cr
          (asrtM reg fun rf => reach rf ∧ c.neg.holds rf)
          (asrtM reg (Stmt.sp reg (.when lbl c b) reach)) := by
        apply cpsTripleWithin_mono_nSteps (Nat.zero_le _)
        apply cpsTripleWithin_entails
        exact asrtM_mono (fun rf hh =>
          Or.inr ⟨hh.1, (Cond.holds_neg c rf).mp hh.2⟩)
      -- not-taken (c): run the body
      have hbody : cpsTripleWithin b.steps (base + 4)
          (base + BitVec.ofNat 64 (4 * (b.size + 1))) cr
          (asrtM reg fun rf => reach rf ∧ ¬ c.neg.holds rf)
          (asrtM reg (Stmt.sp reg (.when lbl c b) reach)) := by
        refine cpsTripleWithin_weaken ?_ ?_ hb
        · exact asrtM_mono (fun rf hh =>
            ⟨hh.1, Decidable.of_not_not
              (fun hcc => hh.2 ((Cond.holds_neg c rf).mpr hcc))⟩)
        · exact asrtM_mono (fun rf hsp => Or.inl hsp)
      exact cpsBranchWithin_merge_same_cr hbr' hskip hbody
  | assert lbl P =>
      have hvc := hvcs _ (List.mem_singleton_self _)
      have h : cpsTripleWithin 0 base base cr (asrtM reg reach)
          (asrtM reg (Stmt.sp reg (.assert lbl P) reach)) :=
        cpsTripleWithin_entails (asrtM_mono (fun rf hr => ⟨hr, hvc rf hr⟩))
      have hz : base + BitVec.ofNat 64 (4 * Stmt.size (.assert lbl P)) = base := by
        simp [Stmt.size]
      simp only [Stmt.steps]
      rw [hz]
      exact h
  | «while» lbl c fuel inv b ihb =>
      simp only [Stmt.offsetsOk, Bool.and_eq_true, decide_eq_true_eq] at hofs
      obtain ⟨⟨⟨hwf, hofsHdr⟩, hofsBack⟩, hOB⟩ := hofs
      simp only [Stmt.size] at hsz
      -- VC pieces
      have hInvInit : ∀ rf, reach rf → inv 0 rf := hvcs.head
      have hInvStep : ∀ i, i < fuel →
          ∀ rf', Stmt.sp reg b (fun rf => inv i rf ∧ c.holds rf) rf' → inv (i + 1) rf' :=
        hvcs.tail.head
      have hExhausted : ∀ rf, inv fuel rf → ¬ c.holds rf := hvcs.tail.tail.head
      have hBodyVcs := hvcs.tail.tail.tail
      -- Code containment
      have hlenAll : 4 * ((b.flatten (base + 4)
          ++ [Instr.JAL Reg.x0 (Stmt.jBack (b.size + 1))]).length + 1) ≤ 2 ^ 64 := by
        simp only [List.length_append, List.length_cons, List.length_nil,
          Stmt.flatten_length]
        omega
      have hflat : Stmt.flatten base (.while lbl c fuel inv b)
          = (c.neg.toInstr (Stmt.brOfs (b.size + 2)))
            :: (b.flatten (base + 4) ++ [.JAL .x0 (Stmt.jBack (b.size + 1))]) := rfl
      have hcode_br : ∀ a' i,
          CodeReq.singleton base (c.neg.toInstr (Stmt.brOfs (b.size + 2))) a' = some i →
          cr a' = some i :=
        fun a' i h => hcode a' i (hflat ▸ ofProg_head a' i h)
      have hcode_b : ∀ a' i,
          CodeReq.ofProg (base + 4) (b.flatten (base + 4)) a' = some i →
          cr a' = some i :=
        fun a' i h => hcode a' i
          (hflat ▸ ofProg_cons_tail hlenAll a' i (ofProg_mono_left a' i h))
      have hcode_jal : ∀ a' i,
          CodeReq.singleton ((base + 4) + BitVec.ofNat 64 (4 * b.size))
            (.JAL .x0 (Stmt.jBack (b.size + 1))) a' = some i →
          cr a' = some i := by
        intro a' i h
        apply hcode a' i
        rw [hflat]
        apply ofProg_cons_tail hlenAll
        apply ofProg_mono_right (p1 := b.flatten (base + 4))
          (by simp only [List.length_cons, List.length_nil, Stmt.flatten_length]; omega)
        rw [Stmt.flatten_length]
        exact ofProg_head a' i h
      -- Loop skeleton addresses
      have hbodyEnd : (base + 4) + BitVec.ofNat 64 (4 * b.size)
          = base + BitVec.ofNat 64 (4 * (b.size + 1)) := by bv_omega
      -- Header branch at any invariant index
      have hheader : ∀ (r : Reach),
          cpsBranchWithin 1 base cr (asrtM reg r)
            (base + BitVec.ofNat 64 (4 * (b.size + 2)))
              (asrtM reg fun rf => r rf ∧ ¬ c.holds rf)
            (base + 4) (asrtM reg fun rf => r rf ∧ c.holds rf) := by
        intro r
        have hbr := branch_spec_asrt c.neg (Stmt.brOfs (b.size + 2)) r base
          (by rw [Cond.wf_neg]; exact hwf)
        rw [signExtend13_brOfs hofsHdr] at hbr
        have hbr' := cpsBranchWithin_frameR (bytesRegion reg.base reg.bytes)
          (bytesRegion_pcFree _ _) (cpsBranchWithin_extend_code hcode_br hbr)
        refine cpsBranchWithin_weaken (fun _ hp => hp) ?_ ?_ hbr'
        · exact asrtM_mono (fun rf hh =>
            ⟨hh.1, (Cond.holds_neg c rf).mp hh.2⟩)
        · exact asrtM_mono (fun rf hh =>
            ⟨hh.1, Decidable.of_not_not
              (fun hcc => hh.2 ((Cond.holds_neg c rf).mpr hcc))⟩)
      -- Body + back-jump triple for each iteration index
      have hbodyStep : ∀ i, i < fuel →
          cpsTripleWithin (b.steps + 1) (base + 4) base cr
            (asrtM reg fun rf => inv i rf ∧ c.holds rf)
            (asrtM reg fun rf => inv (i + 1) rf) := by
        intro i hi
        have hb := ihb (base + 4) (pfx ++ lbl ++ ".body.")
          (fun rf => inv i rf ∧ c.holds rf) (by simpa [Stmt.callFree] using hleaf)
          hOB (by omega) hcode_b
          (Stmt.vcs_antitone reg b _ (fun rf hr => ⟨i, hi, hr.1, hr.2⟩) hBodyVcs)
        have hjal := jal0_spec_pcFree (Stmt.jBack (b.size + 1))
          ((base + 4) + BitVec.ofNat 64 (4 * b.size))
          (pcFree_asrtM reg (Stmt.sp reg b fun rf => inv i rf ∧ c.holds rf))
        rw [hbodyEnd, add_jBack base (b.size + 1) (by omega) hofsBack] at hjal
        rw [← hbodyEnd] at hjal
        have hjal' := cpsTripleWithin_extend_code hcode_jal hjal
        have hseq := cpsTripleWithin_seq_same_cr hb hjal'
        exact cpsTripleWithin_weaken (fun _ hp => hp)
          (asrtM_mono (fun rf hsp => hInvStep i hi rf hsp)) hseq
      -- The loop certificate, by downward recursion on the remaining fuel
      have hcert : ∀ fuel' start, start + fuel' = fuel →
          WP.loopNatCert 1 (b.steps + 1) 1 base (base + 4)
            (base + BitVec.ofNat 64 (4 * (b.size + 2))) cr
            (fun i => asrtM reg fun rf => inv i rf)
            (fun i => asrtM reg fun rf => inv i rf ∧ c.holds rf)
            (fun i => asrtM reg fun rf => inv i rf ∧ ¬ c.holds rf)
            (asrtM reg fun rf => (∃ i, i ≤ fuel ∧ inv i rf) ∧ ¬ c.holds rf)
            start fuel' := by
        intro fuel'
        induction fuel' with
        | zero =>
            intro start hstart
            simp only [WP.loopNatCert]
            have hexit : cpsTripleWithin 0
                (base + BitVec.ofNat 64 (4 * (b.size + 2)))
                (base + BitVec.ofNat 64 (4 * (b.size + 2))) cr
                (asrtM reg fun rf => inv start rf ∧ ¬ c.holds rf)
                (asrtM reg fun rf => (∃ i, i ≤ fuel ∧ inv i rf) ∧ ¬ c.holds rf) :=
              cpsTripleWithin_entails (asrtM_mono (fun rf hh =>
                ⟨⟨start, by omega, hh.1⟩, hh.2⟩))
            have hsf : start = fuel := by omega
            have hdead : cpsTripleWithin 0 (base + 4)
                (base + BitVec.ofNat 64 (4 * (b.size + 2))) cr
                (asrtM reg fun rf => inv start rf ∧ c.holds rf)
                (asrtM reg fun rf => (∃ i, i ≤ fuel ∧ inv i rf) ∧ ¬ c.holds rf) :=
              cpsTripleWithin_unreachable (asrtM_unsat (fun rf hh =>
                hExhausted rf (hsf ▸ hh.1) hh.2))
            exact cpsBranchWithin_merge_same_cr
              (cpsBranchWithin_swap (hheader (fun rf => inv start rf))) hdead hexit
        | succ fuel' ih =>
            intro start hstart
            refine ⟨cpsBranchWithin_swap (hheader (fun rf => inv start rf)),
              hbodyStep start (by omega), ?_, ih (start + 1) (by omega)⟩
            exact asrtM_mono (fun rf hh => ⟨⟨start, by omega, hh.1⟩, hh.2⟩)
      have hsound := WP.loopNatCert_sound (hcert fuel 0 (by omega))
      exact cpsTripleWithin_weaken
        (asrtM_mono (fun rf hr => hInvInit rf hr))
        (fun _ hp => hp)
        hsound
  | call lbl f =>
      exact absurd hleaf (by simp [Stmt.callFree])

end SAsm
end EvmAsm.Rv64
