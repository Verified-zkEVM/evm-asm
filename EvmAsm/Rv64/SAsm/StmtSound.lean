/-
  EvmAsm.Rv64.SAsm.StmtSound

  The generic soundness theorem of the SAsm VC generator: for every
  statement, if its labeled pure VCs hold then the flattened code satisfies
  a bounded CPS triple from `asrtM reg rw reach` to `asrtM reg rw (sp reg s reach)`
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

/-- Split an `asrtOf` precondition into a per-symbolic-state family. -/
theorem cpsTripleWithin_exists_pre {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {rw : RwRegion} {reach : Reach} {Q : Assertion}
    (h : ∀ rf ws (A : Assertion), ws.length = rw.len → A.pcFree → reach rf ws A →
      cpsTripleWithin n entry exit_ cr
        (((regFileIs rf) ** bytesRegion rw.base ws) ** A) Q) :
    cpsTripleWithin n entry exit_ cr (asrtOf rw reach) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, ⟨rf, ws, A, hlen, hApc, hreach, hsts⟩, hR2⟩ := hPR
  exact h rf ws A hlen hApc hreach R hR s hcr ⟨hp, hcompat, h1, h2, hd, hu, hsts, hR2⟩ hpc

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
    `asrtM reg rw reach` to `asrtM reg rw (sp reg s reach)`, within `s.steps`
    machine steps, under any code requirement `cr` containing the flattened
    code.

    `hofs`/`hsz` are decidable per program; `hreg` is the region's
    well-formedness (decidable for concrete regions, `omega`-shaped for
    symbolic ones). -/
theorem Stmt.sound (reg : Region) (rw : RwRegion) (s : Stmt) (base : Word)
    (pfx : String) (reach : Reach) {cr : CodeReq}
    (hreg : reg.wf) (hrw : rw.wf)
    (hleaf : s.callFree = true)
    (hofs : s.offsetsOk = true)
    (hsz : 4 * s.size < 2 ^ 64)
    (hcode : ∀ a i, CodeReq.ofProg base (s.flatten base) a = some i → cr a = some i)
    (hvcs : VCs.Hold (Stmt.vcs reg rw s pfx reach)) :
    cpsTripleWithin s.steps base (base + BitVec.ofNat 64 (4 * s.size)) cr
      (asrtM reg rw reach) (asrtM reg rw (Stmt.sp reg rw s reach)) := by
  induction s generalizing base pfx reach cr with
  | block lbl is =>
      have hok : blockOk is = true := hvcs.head
      have hmem : ∀ rf ws (A : Assertion), ws.length = rw.len → reach rf ws A →
          blockVCs reg rw.base rf ws is := by
        by_cases hl : hasLoad is
        · have ht := hvcs.tail
          simp only [hl, if_true] at ht
          exact ht.head
        · exact fun rf ws _ _ _ =>
            blockVCs_of_not_hasLoad reg rw.base rf ws is (by simpa using hl)
      apply cpsTripleWithin_exists_pre_M
      intro rf ws A hlen hApc hreach
      have h := execBlock_sound reg rw is rf ws base hreg hrw hlen hok
        (hmem rf ws A hlen hreach) (by simpa [Stmt.size] using hsz)
      have hA := cpsTripleWithin_frameR A hApc h
      have h' := cpsTripleWithin_extend_code hcode hA
      refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h'
      intro hp hh
      rw [sepConj_assoc', sepConj_assoc',
        sepConj_comm' (bytesRegion reg.base reg.bytes),
        ← sepConj_assoc', ← sepConj_assoc'] at hh
      exact sepConj_mono_left
        (fun hq hr => ⟨(execBlock reg rw.base rf ws is).1,
          (execBlock reg rw.base rf ws is).2, A,
          by rw [execBlock_ws_length]; exact hlen, hApc,
          ⟨rf, ws, hlen, hreach, rfl, rfl⟩, hr⟩) hp hh
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
      have h2 := ihb (base + BitVec.ofNat 64 (4 * a.size)) pfx (Stmt.sp reg rw a reach)
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
      have hbr := branch_spec_asrt c.neg (Stmt.brOfs (t.size + 2)) rw reach base
        (by rw [Cond.wf_neg]; exact hwf)
      rw [signExtend13_brOfs hofsT] at hbr
      have hbr' := cpsBranchWithin_frameR (bytesRegion reg.base reg.bytes)
        (bytesRegion_pcFree _ _) (cpsBranchWithin_extend_code hcode_br hbr)
      -- Then-arm: t's code then the skip jump
      have ht := iht (base + 4) (pfx ++ lbl ++ ".t.")
        (fun rf ws A => reach rf ws A ∧ c.holds rf) hleaf.1 hOT (by omega) hcode_t hvcs.left
      rw [haddr1] at ht
      have hjal := jal0_spec_pcFree (Stmt.jFwd (e.size + 1))
        (base + BitVec.ofNat 64 (4 * (t.size + 1)))
        (pcFree_asrtM reg rw (Stmt.sp reg rw t fun rf ws A => reach rf ws A ∧ c.holds rf))
      rw [signExtend21_jFwd hofsJ, haddr2] at hjal
      have hjal' := cpsTripleWithin_extend_code hcode_jal hjal
      have htj := cpsTripleWithin_seq_same_cr ht hjal'
      -- Else-arm
      have he := ihe (base + BitVec.ofNat 64 (4 * (t.size + 2))) (pfx ++ lbl ++ ".e.")
        (fun rf ws A => reach rf ws A ∧ ¬ c.holds rf) hleaf.2 hOE (by omega) hcode_e hvcs.right
      rw [haddr3] at he
      -- Weaken branch posts: neg-condition denotations and arm preconditions
      have hbr'' : cpsBranchWithin 1 base cr (asrtM reg rw reach)
          (base + BitVec.ofNat 64 (4 * (t.size + 2)))
            (asrtM reg rw fun rf ws A => reach rf ws A ∧ ¬ c.holds rf)
          (base + 4) (asrtM reg rw fun rf ws A => reach rf ws A ∧ c.holds rf) := by
        refine cpsBranchWithin_weaken (fun _ hp => hp) ?_ ?_ hbr'
        · exact asrtM_mono (fun rf ws A hh =>
            ⟨hh.1, (Cond.holds_neg c rf).mp hh.2⟩)
        · exact asrtM_mono (fun rf ws A hh =>
            ⟨hh.1, Decidable.of_not_not
              (fun hcc => hh.2 ((Cond.holds_neg c rf).mpr hcc))⟩)
      -- Merge: taken exit is the else entry, not-taken is the then entry
      have harmE : cpsTripleWithin (max (t.steps + 1) e.steps)
          (base + BitVec.ofNat 64 (4 * (t.size + 2)))
          (base + BitVec.ofNat 64 (4 * (t.size + e.size + 2))) cr
          (asrtM reg rw fun rf ws A => reach rf ws A ∧ ¬ c.holds rf)
          (asrtM reg rw (Stmt.sp reg rw (.ite lbl c t e) reach)) := by
        refine cpsTripleWithin_mono_nSteps (Nat.le_max_right _ _)
          (cpsTripleWithin_weaken (fun _ hp => hp) ?_ he)
        exact asrtM_mono (fun rf ws A hsp => Or.inr hsp)
      have harmT : cpsTripleWithin (max (t.steps + 1) e.steps)
          (base + 4)
          (base + BitVec.ofNat 64 (4 * (t.size + e.size + 2))) cr
          (asrtM reg rw fun rf ws A => reach rf ws A ∧ c.holds rf)
          (asrtM reg rw (Stmt.sp reg rw (.ite lbl c t e) reach)) := by
        refine cpsTripleWithin_mono_nSteps (Nat.le_max_left _ _)
          (cpsTripleWithin_weaken (fun _ hp => hp) ?_ htj)
        exact asrtM_mono (fun rf ws A hsp => Or.inl hsp)
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
      have hbr := branch_spec_asrt c.neg (Stmt.brOfs (b.size + 1)) rw reach base
        (by rw [Cond.wf_neg]; exact hwf)
      rw [signExtend13_brOfs hofsB] at hbr
      have hbr' := cpsBranchWithin_frameR (bytesRegion reg.base reg.bytes)
        (bytesRegion_pcFree _ _) (cpsBranchWithin_extend_code hcode_br hbr)
      have hb := ihb (base + 4) (pfx ++ lbl ++ ".")
        (fun rf ws A => reach rf ws A ∧ c.holds rf) (by simpa [Stmt.callFree] using hleaf)
        hOB (by omega) hcode_b hvcs
      rw [show (base + 4) + BitVec.ofNat 64 (4 * b.size)
          = base + BitVec.ofNat 64 (4 * (b.size + 1)) from by bv_omega] at hb
      -- taken (¬c): skip directly to the exit
      have hskip : cpsTripleWithin b.steps
          (base + BitVec.ofNat 64 (4 * (b.size + 1)))
          (base + BitVec.ofNat 64 (4 * (b.size + 1))) cr
          (asrtM reg rw fun rf ws A => reach rf ws A ∧ c.neg.holds rf)
          (asrtM reg rw (Stmt.sp reg rw (.when lbl c b) reach)) := by
        apply cpsTripleWithin_mono_nSteps (Nat.zero_le _)
        apply cpsTripleWithin_entails
        exact asrtM_mono (fun rf ws A hh =>
          Or.inr ⟨hh.1, (Cond.holds_neg c rf).mp hh.2⟩)
      -- not-taken (c): run the body
      have hbody : cpsTripleWithin b.steps (base + 4)
          (base + BitVec.ofNat 64 (4 * (b.size + 1))) cr
          (asrtM reg rw fun rf ws A => reach rf ws A ∧ ¬ c.neg.holds rf)
          (asrtM reg rw (Stmt.sp reg rw (.when lbl c b) reach)) := by
        refine cpsTripleWithin_weaken ?_ ?_ hb
        · exact asrtM_mono (fun rf ws A hh =>
            ⟨hh.1, Decidable.of_not_not
              (fun hcc => hh.2 ((Cond.holds_neg c rf).mpr hcc))⟩)
        · exact asrtM_mono (fun rf ws A hsp => Or.inl hsp)
      exact cpsBranchWithin_merge_same_cr hbr' hskip hbody
  | assert lbl P =>
      have hvc := hvcs _ (List.mem_singleton_self _)
      have h : cpsTripleWithin 0 base base cr (asrtM reg rw reach)
          (asrtM reg rw (Stmt.sp reg rw (.assert lbl P) reach)) :=
        cpsTripleWithin_entails (asrtM_mono (fun rf ws A hr => ⟨hr, hvc rf ws A hr⟩))
      have hz : base + BitVec.ofNat 64 (4 * Stmt.size (.assert lbl P)) = base := by
        simp [Stmt.size]
      simp only [Stmt.steps]
      rw [hz]
      exact h
  | blockAt lbl p winR is =>
      have hok : blockOk is = true := hvcs.head
      have hfocus : ∀ rf ws A, reach rf ws A → A.pcFree → ∀ hp, A hp →
          ∃ win rest, winR rf ws A win rest
            ∧ (bytesRegion (rf.get p) win ** rest) hp
            ∧ rest.pcFree ∧ RwRegion.wf ⟨rf.get p, win.length⟩ := hvcs.tail.head
      have hmem : ∀ rf ws A win rest, ws.length = rw.len → reach rf ws A →
          winR rf ws A win rest →
          (∃ hp, (bytesRegion (rf.get p) win ** rest) hp) →
          blockVCs reg (rf.get p) rf win is := by
        by_cases hl : hasLoad is
        · have ht := hvcs.tail.tail
          simp only [hl, if_true] at ht
          exact ht.head
        · exact fun rf ws A win rest _ _ _ _ =>
            blockVCs_of_not_hasLoad reg (rf.get p) rf win is (by simpa using hl)
      apply cpsTripleWithin_exists_pre_M
      intro rf ws A hlen hApc hreach R hR s hcr hPR hpc
      obtain ⟨h0, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR
      obtain ⟨h3, h4, hd2, hu2, hP3, hA4⟩ := hP1
      obtain ⟨win, rest, hRw, hpair, hrestpc, hwf⟩ :=
        hfocus rf ws A hreach hApc h4 hA4
      have hPR' : ((((regFileIs rf) ** (bytesRegion reg.base reg.bytes **
          bytesRegion rw.base ws)) ** (bytesRegion (rf.get p) win ** rest))
          ** R).holdsFor s :=
        ⟨h0, hcompat, h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hP3, hpair⟩, hR2⟩
      have h := execBlock_sound reg ⟨rf.get p, win.length⟩ is rf win base hreg
        hwf rfl hok (hmem rf ws A win rest hlen hreach hRw ⟨h4, hpair⟩)
        (by simpa [Stmt.size] using hsz)
      have hA2 := cpsTripleWithin_frameR (bytesRegion rw.base ws ** rest)
        (pcFree_sepConj (bytesRegion_pcFree _ _) hrestpc) h
      have h' := cpsTripleWithin_extend_code hcode hA2
      refine cpsTripleWithin_weaken ?_ ?_ h' R hR s hcr hPR' hpc
      · intro hp hh
        xperm_hyp hh
      · intro hp hh
        have hh2 : ((((regFileIs (execBlock reg (rf.get p) rf win is).1) **
            bytesRegion rw.base ws) **
            (bytesRegion (rf.get p) (execBlock reg (rf.get p) rf win is).2
              ** rest)) **
            bytesRegion reg.base reg.bytes) hp := by xperm_hyp hh
        exact sepConj_mono_left (fun hq hx =>
          ⟨(execBlock reg (rf.get p) rf win is).1, ws,
            (bytesRegion (rf.get p) (execBlock reg (rf.get p) rf win is).2
              ** rest),
            hlen, pcFree_sepConj (bytesRegion_pcFree _ _) hrestpc,
            ⟨rf, A, win, rest, hlen, hreach, ⟨h4, hpair⟩, hRw, rfl, rfl⟩,
            hx⟩) hp hh2
  | readAt lbl p roR is =>
      have hok : blockOk is = true := hvcs.head
      have hfocus : ∀ rf ws A, reach rf ws A → A.pcFree → ∀ hp, A hp →
          ∃ robytes rest, roR rf ws A robytes rest
            ∧ (bytesRegion (rf.get p) robytes ** rest) hp
            ∧ rest.pcFree ∧ Region.wf ⟨rf.get p, robytes⟩ := hvcs.tail.head
      have hmem : ∀ rf ws A robytes rest, ws.length = rw.len → reach rf ws A →
          roR rf ws A robytes rest →
          (∃ hp, (bytesRegion (rf.get p) robytes ** rest) hp) →
          blockVCs ⟨rf.get p, robytes⟩ rw.base rf ws is := by
        by_cases hl : hasLoad is
        · have ht := hvcs.tail.tail
          simp only [hl, if_true] at ht
          exact ht.head
        · exact fun rf ws A robytes rest _ _ _ _ =>
            blockVCs_of_not_hasLoad ⟨rf.get p, robytes⟩ rw.base rf ws is (by simpa using hl)
      apply cpsTripleWithin_exists_pre_M
      intro rf ws A hlen hApc hreach R hR s hcr hPR hpc
      obtain ⟨h0, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR
      obtain ⟨h3, h4, hd2, hu2, hP3, hA4⟩ := hP1
      obtain ⟨robytes, rest, hRoR, hpair, hrestpc, hwf⟩ :=
        hfocus rf ws A hreach hApc h4 hA4
      have hPR' : ((((regFileIs rf) ** (bytesRegion reg.base reg.bytes **
          bytesRegion rw.base ws)) ** (bytesRegion (rf.get p) robytes ** rest))
          ** R).holdsFor s :=
        ⟨h0, hcompat, h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hP3, hpair⟩, hR2⟩
      have h := execBlock_sound ⟨rf.get p, robytes⟩ rw is rf ws base hwf
        hrw hlen hok (hmem rf ws A robytes rest hlen hreach hRoR ⟨h4, hpair⟩)
        (by simpa [Stmt.size] using hsz)
      have hA2 := cpsTripleWithin_frameR (bytesRegion reg.base reg.bytes ** rest)
        (pcFree_sepConj (bytesRegion_pcFree _ _) hrestpc) h
      have h' := cpsTripleWithin_extend_code hcode hA2
      refine cpsTripleWithin_weaken ?_ ?_ h' R hR s hcr hPR' hpc
      · intro hp hh
        xperm_hyp hh
      · intro hp hh
        have hh2 : ((((regFileIs (execBlock ⟨rf.get p, robytes⟩ rw.base rf ws is).1) **
            bytesRegion rw.base (execBlock ⟨rf.get p, robytes⟩ rw.base rf ws is).2) **
            (bytesRegion (rf.get p) robytes ** rest)) **
            bytesRegion reg.base reg.bytes) hp := by xperm_hyp hh
        exact sepConj_mono_left (fun hq hx =>
          ⟨(execBlock ⟨rf.get p, robytes⟩ rw.base rf ws is).1,
            (execBlock ⟨rf.get p, robytes⟩ rw.base rf ws is).2,
            (bytesRegion (rf.get p) robytes ** rest),
            by rw [execBlock_ws_length]; exact hlen,
            pcFree_sepConj (bytesRegion_pcFree _ _) hrestpc,
            ⟨rf, ws, A, robytes, rest, hlen, hreach, ⟨h4, hpair⟩, hRoR, rfl, rfl, rfl⟩,
            hx⟩) hp hh2
  | ghost lbl R =>
      have hvc := hvcs _ (List.mem_singleton_self _)
      have h : cpsTripleWithin 0 base base cr (asrtM reg rw reach)
          (asrtM reg rw (Stmt.sp reg rw (.ghost lbl R) reach)) := by
        apply cpsTripleWithin_entails
        intro hp hh
        refine sepConj_mono_left (fun hq hx => ?_) hp hh
        obtain ⟨rf, ws, A, hlen, hApc, hr, hsts⟩ := hx
        obtain ⟨g1, g2, gd, gu, hin, hA⟩ := hsts
        obtain ⟨A', hRw, hent, hpcf⟩ := hvc rf ws A hr hApc ⟨g2, hA⟩
        exact ⟨rf, ws, A', hlen, hpcf, ⟨A, hr, ⟨g2, hA⟩, hRw⟩,
          ⟨g1, g2, gd, gu, hin, hent g2 hA⟩⟩
      have hz : base + BitVec.ofNat 64 (4 * Stmt.size (.ghost lbl R)) = base := by
        simp [Stmt.size]
      simp only [Stmt.steps]
      rw [hz]
      exact h
  | «while» lbl c fuel inv b ihb =>
      simp only [Stmt.offsetsOk, Bool.and_eq_true, decide_eq_true_eq] at hofs
      obtain ⟨⟨⟨hwf, hofsHdr⟩, hofsBack⟩, hOB⟩ := hofs
      simp only [Stmt.size] at hsz
      -- VC pieces
      have hInvInit : ∀ rf ws A, reach rf ws A → inv 0 rf ws A := hvcs.head
      have hInvStep : ∀ i, i < fuel →
          ∀ rf' ws' A', Stmt.sp reg rw b
              (fun rf ws A => inv i rf ws A ∧ c.holds rf) rf' ws' A' →
            inv (i + 1) rf' ws' A' :=
        hvcs.tail.head
      have hExhausted : ∀ rf ws A, inv fuel rf ws A → ¬ c.holds rf := hvcs.tail.tail.head
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
          cpsBranchWithin 1 base cr (asrtM reg rw r)
            (base + BitVec.ofNat 64 (4 * (b.size + 2)))
              (asrtM reg rw fun rf ws A => r rf ws A ∧ ¬ c.holds rf)
            (base + 4) (asrtM reg rw fun rf ws A => r rf ws A ∧ c.holds rf) := by
        intro r
        have hbr := branch_spec_asrt c.neg (Stmt.brOfs (b.size + 2)) rw r base
          (by rw [Cond.wf_neg]; exact hwf)
        rw [signExtend13_brOfs hofsHdr] at hbr
        have hbr' := cpsBranchWithin_frameR (bytesRegion reg.base reg.bytes)
          (bytesRegion_pcFree _ _) (cpsBranchWithin_extend_code hcode_br hbr)
        refine cpsBranchWithin_weaken (fun _ hp => hp) ?_ ?_ hbr'
        · exact asrtM_mono (fun rf ws A hh =>
            ⟨hh.1, (Cond.holds_neg c rf).mp hh.2⟩)
        · exact asrtM_mono (fun rf ws A hh =>
            ⟨hh.1, Decidable.of_not_not
              (fun hcc => hh.2 ((Cond.holds_neg c rf).mpr hcc))⟩)
      -- Body + back-jump triple for each iteration index
      have hbodyStep : ∀ i, i < fuel →
          cpsTripleWithin (b.steps + 1) (base + 4) base cr
            (asrtM reg rw fun rf ws A => inv i rf ws A ∧ c.holds rf)
            (asrtM reg rw fun rf ws A => inv (i + 1) rf ws A) := by
        intro i hi
        have hb := ihb (base + 4) (pfx ++ lbl ++ ".body.")
          (fun rf ws A => inv i rf ws A ∧ c.holds rf) (by simpa [Stmt.callFree] using hleaf)
          hOB (by omega) hcode_b
          (Stmt.vcs_antitone reg rw b _ (fun rf ws A hr => ⟨i, hi, hr.1, hr.2⟩) hBodyVcs)
        have hjal := jal0_spec_pcFree (Stmt.jBack (b.size + 1))
          ((base + 4) + BitVec.ofNat 64 (4 * b.size))
          (pcFree_asrtM reg rw (Stmt.sp reg rw b fun rf ws A => inv i rf ws A ∧ c.holds rf))
        rw [hbodyEnd, add_jBack base (b.size + 1) (by omega) hofsBack] at hjal
        rw [← hbodyEnd] at hjal
        have hjal' := cpsTripleWithin_extend_code hcode_jal hjal
        have hseq := cpsTripleWithin_seq_same_cr hb hjal'
        exact cpsTripleWithin_weaken (fun _ hp => hp)
          (asrtM_mono (fun rf ws A hsp => hInvStep i hi rf ws A hsp)) hseq
      -- The loop certificate, by downward recursion on the remaining fuel
      have hcert : ∀ fuel' start, start + fuel' = fuel →
          WP.loopNatCert 1 (b.steps + 1) 1 base (base + 4)
            (base + BitVec.ofNat 64 (4 * (b.size + 2))) cr
            (fun i => asrtM reg rw fun rf ws A => inv i rf ws A)
            (fun i => asrtM reg rw fun rf ws A => inv i rf ws A ∧ c.holds rf)
            (fun i => asrtM reg rw fun rf ws A => inv i rf ws A ∧ ¬ c.holds rf)
            (asrtM reg rw fun rf ws A => (∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ c.holds rf)
            start fuel' := by
        intro fuel'
        induction fuel' with
        | zero =>
            intro start hstart
            simp only [WP.loopNatCert]
            have hexit : cpsTripleWithin 0
                (base + BitVec.ofNat 64 (4 * (b.size + 2)))
                (base + BitVec.ofNat 64 (4 * (b.size + 2))) cr
                (asrtM reg rw fun rf ws A => inv start rf ws A ∧ ¬ c.holds rf)
                (asrtM reg rw fun rf ws A => (∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ c.holds rf) :=
              cpsTripleWithin_entails (asrtM_mono (fun rf ws A hh =>
                ⟨⟨start, by omega, hh.1⟩, hh.2⟩))
            have hsf : start = fuel := by omega
            have hdead : cpsTripleWithin 0 (base + 4)
                (base + BitVec.ofNat 64 (4 * (b.size + 2))) cr
                (asrtM reg rw fun rf ws A => inv start rf ws A ∧ c.holds rf)
                (asrtM reg rw fun rf ws A => (∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ c.holds rf) :=
              cpsTripleWithin_unreachable (asrtM_unsat (fun rf ws A hh =>
                hExhausted rf ws A (hsf ▸ hh.1) hh.2))
            exact cpsBranchWithin_merge_same_cr
              (cpsBranchWithin_swap (hheader (fun rf ws A => inv start rf ws A))) hdead hexit
        | succ fuel' ih =>
            intro start hstart
            refine ⟨cpsBranchWithin_swap (hheader (fun rf ws A => inv start rf ws A)),
              hbodyStep start (by omega), ?_, ih (start + 1) (by omega)⟩
            exact asrtM_mono (fun rf ws A hh => ⟨⟨start, by omega, hh.1⟩, hh.2⟩)
      have hsound := WP.loopNatCert_sound (hcert fuel 0 (by omega))
      exact cpsTripleWithin_weaken
        (asrtM_mono (fun rf ws A hr => hInvInit rf ws A hr))
        (fun _ hp => hp)
        hsound
  | «whileS» lbl c fuel inv b ihb =>
      simp only [Stmt.offsetsOk, Bool.and_eq_true, decide_eq_true_eq] at hofs
      obtain ⟨⟨⟨hwf, hofsHdr⟩, hofsBack⟩, hOB⟩ := hofs
      simp only [Stmt.size] at hsz
      -- VC pieces (snapshot-quantified)
      have hInvInit : ∀ rf ws A, reach rf ws A → inv rf ws A 0 rf ws A := hvcs.head
      have hInvStep : ∀ rf₀ ws₀ A₀, reach rf₀ ws₀ A₀ → ∀ i, i < fuel →
          ∀ rf' ws' A', Stmt.sp reg rw b
              (fun rf ws A => inv rf₀ ws₀ A₀ i rf ws A ∧ c.holds rf) rf' ws' A' →
            inv rf₀ ws₀ A₀ (i + 1) rf' ws' A' :=
        hvcs.tail.head
      have hExhausted : ∀ rf₀ ws₀ A₀, reach rf₀ ws₀ A₀ →
          ∀ rf ws A, inv rf₀ ws₀ A₀ fuel rf ws A → ¬ c.holds rf :=
        hvcs.tail.tail.head
      have hBodyVcs := hvcs.tail.tail.tail
      -- Code containment (the flattened code is identical to `while`)
      have hlenAll : 4 * ((b.flatten (base + 4)
          ++ [Instr.JAL Reg.x0 (Stmt.jBack (b.size + 1))]).length + 1) ≤ 2 ^ 64 := by
        simp only [List.length_append, List.length_cons, List.length_nil,
          Stmt.flatten_length]
        omega
      have hflat : Stmt.flatten base (.whileS lbl c fuel inv b)
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
          cpsBranchWithin 1 base cr (asrtM reg rw r)
            (base + BitVec.ofNat 64 (4 * (b.size + 2)))
              (asrtM reg rw fun rf ws A => r rf ws A ∧ ¬ c.holds rf)
            (base + 4) (asrtM reg rw fun rf ws A => r rf ws A ∧ c.holds rf) := by
        intro r
        have hbr := branch_spec_asrt c.neg (Stmt.brOfs (b.size + 2)) rw r base
          (by rw [Cond.wf_neg]; exact hwf)
        rw [signExtend13_brOfs hofsHdr] at hbr
        have hbr' := cpsBranchWithin_frameR (bytesRegion reg.base reg.bytes)
          (bytesRegion_pcFree _ _) (cpsBranchWithin_extend_code hcode_br hbr)
        refine cpsBranchWithin_weaken (fun _ hp => hp) ?_ ?_ hbr'
        · exact asrtM_mono (fun rf ws A hh =>
            ⟨hh.1, (Cond.holds_neg c rf).mp hh.2⟩)
        · exact asrtM_mono (fun rf ws A hh =>
            ⟨hh.1, Decidable.of_not_not
              (fun hcc => hh.2 ((Cond.holds_neg c rf).mpr hcc))⟩)
      -- Fix the loop-entry state (the invariant's snapshot); from here the
      -- entry-instantiated invariant family is an ordinary `Nat`-indexed one.
      apply cpsTripleWithin_exists_pre_M
      intro rf₀ ws₀ A₀ hlen hApc hreach₀
      -- Body + back-jump triple for each iteration index
      have hbodyStep : ∀ i, i < fuel →
          cpsTripleWithin (b.steps + 1) (base + 4) base cr
            (asrtM reg rw fun rf ws A => inv rf₀ ws₀ A₀ i rf ws A ∧ c.holds rf)
            (asrtM reg rw fun rf ws A => inv rf₀ ws₀ A₀ (i + 1) rf ws A) := by
        intro i hi
        have hb := ihb (base + 4) (pfx ++ lbl ++ ".body.")
          (fun rf ws A => inv rf₀ ws₀ A₀ i rf ws A ∧ c.holds rf)
          (by simpa [Stmt.callFree] using hleaf)
          hOB (by omega) hcode_b
          (Stmt.vcs_antitone reg rw b _
            (fun rf ws A hr => ⟨rf₀, ws₀, A₀, hreach₀, i, hi, hr.1, hr.2⟩) hBodyVcs)
        have hjal := jal0_spec_pcFree (Stmt.jBack (b.size + 1))
          ((base + 4) + BitVec.ofNat 64 (4 * b.size))
          (pcFree_asrtM reg rw (Stmt.sp reg rw b
            fun rf ws A => inv rf₀ ws₀ A₀ i rf ws A ∧ c.holds rf))
        rw [hbodyEnd, add_jBack base (b.size + 1) (by omega) hofsBack] at hjal
        rw [← hbodyEnd] at hjal
        have hjal' := cpsTripleWithin_extend_code hcode_jal hjal
        have hseq := cpsTripleWithin_seq_same_cr hb hjal'
        exact cpsTripleWithin_weaken (fun _ hp => hp)
          (asrtM_mono (fun rf ws A hsp =>
            hInvStep rf₀ ws₀ A₀ hreach₀ i hi rf ws A hsp)) hseq
      -- The loop certificate, by downward recursion on the remaining fuel
      have hcert : ∀ fuel' start, start + fuel' = fuel →
          WP.loopNatCert 1 (b.steps + 1) 1 base (base + 4)
            (base + BitVec.ofNat 64 (4 * (b.size + 2))) cr
            (fun i => asrtM reg rw fun rf ws A => inv rf₀ ws₀ A₀ i rf ws A)
            (fun i => asrtM reg rw fun rf ws A =>
              inv rf₀ ws₀ A₀ i rf ws A ∧ c.holds rf)
            (fun i => asrtM reg rw fun rf ws A =>
              inv rf₀ ws₀ A₀ i rf ws A ∧ ¬ c.holds rf)
            (asrtM reg rw fun rf ws A =>
              (∃ i, i ≤ fuel ∧ inv rf₀ ws₀ A₀ i rf ws A) ∧ ¬ c.holds rf)
            start fuel' := by
        intro fuel'
        induction fuel' with
        | zero =>
            intro start hstart
            simp only [WP.loopNatCert]
            have hexit : cpsTripleWithin 0
                (base + BitVec.ofNat 64 (4 * (b.size + 2)))
                (base + BitVec.ofNat 64 (4 * (b.size + 2))) cr
                (asrtM reg rw fun rf ws A =>
                  inv rf₀ ws₀ A₀ start rf ws A ∧ ¬ c.holds rf)
                (asrtM reg rw fun rf ws A =>
                  (∃ i, i ≤ fuel ∧ inv rf₀ ws₀ A₀ i rf ws A) ∧ ¬ c.holds rf) :=
              cpsTripleWithin_entails (asrtM_mono (fun rf ws A hh =>
                ⟨⟨start, by omega, hh.1⟩, hh.2⟩))
            have hsf : start = fuel := by omega
            have hdead : cpsTripleWithin 0 (base + 4)
                (base + BitVec.ofNat 64 (4 * (b.size + 2))) cr
                (asrtM reg rw fun rf ws A =>
                  inv rf₀ ws₀ A₀ start rf ws A ∧ c.holds rf)
                (asrtM reg rw fun rf ws A =>
                  (∃ i, i ≤ fuel ∧ inv rf₀ ws₀ A₀ i rf ws A) ∧ ¬ c.holds rf) :=
              cpsTripleWithin_unreachable (asrtM_unsat (fun rf ws A hh =>
                hExhausted rf₀ ws₀ A₀ hreach₀ rf ws A (hsf ▸ hh.1) hh.2))
            exact cpsBranchWithin_merge_same_cr
              (cpsBranchWithin_swap
                (hheader (fun rf ws A => inv rf₀ ws₀ A₀ start rf ws A))) hdead hexit
        | succ fuel' ih =>
            intro start hstart
            refine ⟨cpsBranchWithin_swap
                (hheader (fun rf ws A => inv rf₀ ws₀ A₀ start rf ws A)),
              hbodyStep start (by omega), ?_, ih (start + 1) (by omega)⟩
            exact asrtM_mono (fun rf ws A hh => ⟨⟨start, by omega, hh.1⟩, hh.2⟩)
      have hsound := WP.loopNatCert_sound (hcert fuel 0 (by omega))
      refine cpsTripleWithin_weaken ?_ ?_ hsound
      · -- the fixed entry state enters the loop at invariant index 0
        intro hp hh
        have hh2 : ((((regFileIs rf₀) ** bytesRegion rw.base ws₀) ** A₀)
            ** bytesRegion reg.base reg.bytes) hp := by xperm_hyp hh
        exact sepConj_mono_left (fun hq hx =>
          ⟨rf₀, ws₀, A₀, hlen, hApc, hInvInit rf₀ ws₀ A₀ hreach₀, hx⟩) hp hh2
      · -- the exit records the entry state alongside the invariant
        exact asrtM_mono (fun rf ws A hh => ⟨rf₀, ws₀, A₀, hreach₀, hh.1, hh.2⟩)
  | «whileBreak» lbl guard fuel inv post bb breakCond ba ihbb ihba =>
      simp only [Stmt.callFree, Bool.and_eq_true] at hleaf
      obtain ⟨hleafBB, hleafBA⟩ := hleaf
      simp only [Stmt.offsetsOk, Bool.and_eq_true, decide_eq_true_eq] at hofs
      obtain ⟨⟨⟨⟨⟨⟨hwfG, hwfB⟩, hofsHdr⟩, hofsBreak⟩, hofsBack⟩, hOBB⟩, hOBA⟩ := hofs
      simp only [Stmt.size] at hsz
      -- VC pieces
      have hInvInit : ∀ rf ws A, reach rf ws A → inv 0 rf ws A := hvcs.head
      have hInvStep : ∀ i, i < fuel → ∀ rf' ws' A',
          Stmt.sp reg rw ba (fun rf ws A =>
            Stmt.sp reg rw bb (fun rf ws A => inv i rf ws A ∧ guard.holds rf) rf ws A
              ∧ ¬ breakCond.holds rf) rf' ws' A' →
          inv (i + 1) rf' ws' A' := hvcs.tail.head
      have hExhausted : ∀ rf ws A, inv fuel rf ws A → ¬ guard.holds rf :=
        hvcs.tail.tail.head
      have hGuardExit : ∀ i, i ≤ fuel → ∀ rf ws A,
          inv i rf ws A → ¬ guard.holds rf → post rf ws A := hvcs.tail.tail.tail.head
      have hBreak : ∀ i, i < fuel → ∀ rf' ws' A',
          Stmt.sp reg rw bb (fun rf ws A => inv i rf ws A ∧ guard.holds rf) rf' ws' A' →
          breakCond.holds rf' → post rf' ws' A' := hvcs.tail.tail.tail.tail.head
      have hBBVcs := hvcs.tail.tail.tail.tail.tail.left
      have hBAVcs := hvcs.tail.tail.tail.tail.tail.right
      -- Flattened layout
      have hflat : Stmt.flatten base (.whileBreak lbl guard fuel inv post bb breakCond ba)
          = guard.neg.toInstr (Stmt.brOfs (bb.size + ba.size + 3))
            :: (bb.flatten (base + 4)
                ++ breakCond.toInstr (Stmt.brOfs (ba.size + 2))
                :: (ba.flatten (base + BitVec.ofNat 64 (4 * (bb.size + 2)))
                    ++ [.JAL .x0 (Stmt.jBack (bb.size + ba.size + 2))])) := rfl
      have hlenAll : 4 * ((bb.flatten (base + 4)
          ++ breakCond.toInstr (Stmt.brOfs (ba.size + 2))
          :: (ba.flatten (base + BitVec.ofNat 64 (4 * (bb.size + 2)))
              ++ [.JAL .x0 (Stmt.jBack (bb.size + ba.size + 2))])).length + 1) ≤ 2 ^ 64 := by
        simp only [List.length_append, List.length_cons, List.length_nil, Stmt.flatten_length]
        omega
      -- Code containment for the five regions
      have hcode_header : ∀ a' i,
          CodeReq.singleton base (guard.neg.toInstr (Stmt.brOfs (bb.size + ba.size + 3)))
            a' = some i → cr a' = some i :=
        fun a' i h => hcode a' i (hflat ▸ ofProg_head a' i h)
      have hcode_bb : ∀ a' i,
          CodeReq.ofProg (base + 4) (bb.flatten (base + 4)) a' = some i → cr a' = some i :=
        fun a' i h => hcode a' i
          (hflat ▸ ofProg_cons_tail hlenAll a' i (ofProg_mono_left a' i h))
      have hcode_break : ∀ a' i,
          CodeReq.singleton (base + BitVec.ofNat 64 (4 * (bb.size + 1)))
            (breakCond.toInstr (Stmt.brOfs (ba.size + 2))) a' = some i → cr a' = some i := by
        intro a' i h
        apply hcode a' i
        rw [hflat]
        apply ofProg_cons_tail hlenAll
        apply ofProg_mono_right (p1 := bb.flatten (base + 4))
          (by simp only [List.length_append, List.length_cons, List.length_nil,
            Stmt.flatten_length]; omega)
        rw [Stmt.flatten_length,
          show (base + 4) + BitVec.ofNat 64 (4 * bb.size)
            = base + BitVec.ofNat 64 (4 * (bb.size + 1)) from by bv_omega]
        exact ofProg_head a' i h
      have hcode_ba : ∀ a' i,
          CodeReq.ofProg (base + BitVec.ofNat 64 (4 * (bb.size + 2)))
            (ba.flatten (base + BitVec.ofNat 64 (4 * (bb.size + 2)))) a' = some i →
          cr a' = some i := by
        intro a' i h
        apply hcode a' i
        rw [hflat]
        apply ofProg_cons_tail hlenAll
        apply ofProg_mono_right (p1 := bb.flatten (base + 4))
          (by simp only [List.length_append, List.length_cons, List.length_nil,
            Stmt.flatten_length]; omega)
        rw [Stmt.flatten_length,
          show (base + 4) + BitVec.ofNat 64 (4 * bb.size)
            = base + BitVec.ofNat 64 (4 * (bb.size + 1)) from by bv_omega]
        apply ofProg_cons_tail
          (by simp only [List.length_append, List.length_cons, List.length_nil,
            Stmt.flatten_length]; omega)
        rw [show (base + BitVec.ofNat 64 (4 * (bb.size + 1))) + 4
            = base + BitVec.ofNat 64 (4 * (bb.size + 2)) from by bv_omega]
        exact ofProg_mono_left a' i h
      have hcode_jal : ∀ a' i,
          CodeReq.singleton (base + BitVec.ofNat 64 (4 * (bb.size + ba.size + 2)))
            (.JAL .x0 (Stmt.jBack (bb.size + ba.size + 2))) a' = some i → cr a' = some i := by
        intro a' i h
        apply hcode a' i
        rw [hflat]
        apply ofProg_cons_tail hlenAll
        apply ofProg_mono_right (p1 := bb.flatten (base + 4))
          (by simp only [List.length_append, List.length_cons, List.length_nil,
            Stmt.flatten_length]; omega)
        rw [Stmt.flatten_length,
          show (base + 4) + BitVec.ofNat 64 (4 * bb.size)
            = base + BitVec.ofNat 64 (4 * (bb.size + 1)) from by bv_omega]
        apply ofProg_cons_tail
          (by simp only [List.length_append, List.length_cons, List.length_nil,
            Stmt.flatten_length]; omega)
        rw [show (base + BitVec.ofNat 64 (4 * (bb.size + 1))) + 4
            = base + BitVec.ofNat 64 (4 * (bb.size + 2)) from by bv_omega]
        apply ofProg_mono_right (p1 := ba.flatten (base + BitVec.ofNat 64 (4 * (bb.size + 2))))
          (by simp only [List.length_cons, List.length_nil, Stmt.flatten_length]; omega)
        rw [Stmt.flatten_length,
          show (base + BitVec.ofNat 64 (4 * (bb.size + 2))) + BitVec.ofNat 64 (4 * ba.size)
            = base + BitVec.ofNat 64 (4 * (bb.size + ba.size + 2)) from by bv_omega]
        exact ofProg_head a' i h
      -- Header branch at any invariant index: exit to `Lexit` when guard fails,
      -- fall to `base + 4` (the body) when guard holds.
      have hheader : ∀ (r : Reach),
          cpsBranchWithin 1 base cr (asrtM reg rw r)
            (base + BitVec.ofNat 64 (4 * (bb.size + ba.size + 3)))
              (asrtM reg rw fun rf ws A => r rf ws A ∧ ¬ guard.holds rf)
            (base + 4) (asrtM reg rw fun rf ws A => r rf ws A ∧ guard.holds rf) := by
        intro r
        have hbr := branch_spec_asrt guard.neg (Stmt.brOfs (bb.size + ba.size + 3)) rw r base
          (by rw [Cond.wf_neg]; exact hwfG)
        rw [signExtend13_brOfs hofsHdr] at hbr
        have hbr' := cpsBranchWithin_frameR (bytesRegion reg.base reg.bytes)
          (bytesRegion_pcFree _ _) (cpsBranchWithin_extend_code hcode_header hbr)
        refine cpsBranchWithin_weaken (fun _ hp => hp) ?_ ?_ hbr'
        · exact asrtM_mono (fun rf ws A hh =>
            ⟨hh.1, (Cond.holds_neg guard rf).mp hh.2⟩)
        · exact asrtM_mono (fun rf ws A hh =>
            ⟨hh.1, Decidable.of_not_not
              (fun hcc => hh.2 ((Cond.holds_neg guard rf).mpr hcc))⟩)
      -- Break branch at `breakPt`: exit to `Lexit` when `breakCond` holds,
      -- fall to `afterEntry` otherwise.
      have hbreak : ∀ (r : Reach),
          cpsBranchWithin 1 (base + BitVec.ofNat 64 (4 * (bb.size + 1))) cr (asrtM reg rw r)
            (base + BitVec.ofNat 64 (4 * (bb.size + ba.size + 3)))
              (asrtM reg rw fun rf ws A => r rf ws A ∧ breakCond.holds rf)
            (base + BitVec.ofNat 64 (4 * (bb.size + 2)))
              (asrtM reg rw fun rf ws A => r rf ws A ∧ ¬ breakCond.holds rf) := by
        intro r
        have hbr := branch_spec_asrt breakCond (Stmt.brOfs (ba.size + 2)) rw r
          (base + BitVec.ofNat 64 (4 * (bb.size + 1))) hwfB
        rw [signExtend13_brOfs hofsBreak,
          show (base + BitVec.ofNat 64 (4 * (bb.size + 1)))
              + BitVec.ofNat 64 (4 * (ba.size + 2))
            = base + BitVec.ofNat 64 (4 * (bb.size + ba.size + 3)) from by bv_omega,
          show (base + BitVec.ofNat 64 (4 * (bb.size + 1))) + 4
            = base + BitVec.ofNat 64 (4 * (bb.size + 2)) from by bv_omega] at hbr
        exact cpsBranchWithin_frameR (bytesRegion reg.base reg.bytes)
          (bytesRegion_pcFree _ _) (cpsBranchWithin_extend_code hcode_break hbr)
      -- Body-before triple: `base + 4` → `breakPt`.
      have hbeforeStep : ∀ i, i < fuel →
          cpsTripleWithin bb.steps (base + 4)
            (base + BitVec.ofNat 64 (4 * (bb.size + 1))) cr
            (asrtM reg rw fun rf ws A => inv i rf ws A ∧ guard.holds rf)
            (asrtM reg rw (Stmt.sp reg rw bb
              (fun rf ws A => inv i rf ws A ∧ guard.holds rf))) := by
        intro i hi
        have hb := ihbb (base + 4) (pfx ++ lbl ++ ".before.")
          (fun rf ws A => inv i rf ws A ∧ guard.holds rf) hleafBB hOBB (by omega) hcode_bb
          (Stmt.vcs_antitone reg rw bb _ (fun rf ws A hr => ⟨i, hi, hr.1, hr.2⟩) hBBVcs)
        rwa [show (base + 4) + BitVec.ofNat 64 (4 * bb.size)
            = base + BitVec.ofNat 64 (4 * (bb.size + 1)) from by bv_omega] at hb
      -- Body-after triple + back-jump: `afterEntry` → header, advancing the index.
      have hafterStep : ∀ i, i < fuel →
          cpsTripleWithin (ba.steps + 1)
            (base + BitVec.ofNat 64 (4 * (bb.size + 2))) base cr
            (asrtM reg rw fun rf ws A =>
              Stmt.sp reg rw bb (fun rf ws A => inv i rf ws A ∧ guard.holds rf) rf ws A
                ∧ ¬ breakCond.holds rf)
            (asrtM reg rw fun rf ws A => inv (i + 1) rf ws A) := by
        intro i hi
        have hb := ihba (base + BitVec.ofNat 64 (4 * (bb.size + 2))) (pfx ++ lbl ++ ".after.")
          (fun rf ws A =>
            Stmt.sp reg rw bb (fun rf ws A => inv i rf ws A ∧ guard.holds rf) rf ws A
              ∧ ¬ breakCond.holds rf) hleafBA hOBA (by omega) hcode_ba
          (Stmt.vcs_antitone reg rw ba _ (fun rf ws A hr => ⟨i, hi, hr.1, hr.2⟩) hBAVcs)
        have hjal := jal0_spec_pcFree (Stmt.jBack (bb.size + ba.size + 2))
          (base + BitVec.ofNat 64 (4 * (bb.size + ba.size + 2)))
          (pcFree_asrtM reg rw (Stmt.sp reg rw ba fun rf ws A =>
            Stmt.sp reg rw bb (fun rf ws A => inv i rf ws A ∧ guard.holds rf) rf ws A
              ∧ ¬ breakCond.holds rf))
        rw [show (base + BitVec.ofNat 64 (4 * (bb.size + 2)))
              + BitVec.ofNat 64 (4 * ba.size)
            = base + BitVec.ofNat 64 (4 * (bb.size + ba.size + 2)) from by bv_omega] at hb
        rw [add_jBack base (bb.size + ba.size + 2) (by omega) hofsBack] at hjal
        have hjal' := cpsTripleWithin_extend_code hcode_jal hjal
        have hseq := cpsTripleWithin_seq_same_cr hb hjal'
        exact cpsTripleWithin_weaken (fun _ hp => hp)
          (asrtM_mono (fun rf ws A hsp => hInvStep i hi rf ws A hsp)) hseq
      -- The body as a branch: from `base + 4`, either back to header (continue)
      -- or out to `Lexit` (break).
      have hBodyBranch : ∀ i, i < fuel →
          cpsBranchWithin (bb.steps + ba.steps + 2) (base + 4) cr
            (asrtM reg rw fun rf ws A => inv i rf ws A ∧ guard.holds rf)
            base (asrtM reg rw fun rf ws A => inv (i + 1) rf ws A)
            (base + BitVec.ofNat 64 (4 * (bb.size + ba.size + 3)))
              (asrtM reg rw fun rf ws A =>
                Stmt.sp reg rw bb (fun rf ws A => inv i rf ws A ∧ guard.holds rf) rf ws A
                  ∧ breakCond.holds rf) := by
        intro i hi
        have hcomposed1 := cpsTripleWithin_seq_cpsBranchWithin_same_cr (hbeforeStep i hi)
          (hbreak (Stmt.sp reg rw bb (fun rf ws A => inv i rf ws A ∧ guard.holds rf)))
        have hcomposed2 := cpsBranchWithin_seq_cpsTripleWithin_same_cr hcomposed1
          (hafterStep i hi) (fun _ hp => hp)
        rw [show bb.steps + 1 + (ba.steps + 1) = bb.steps + ba.steps + 2 from by omega]
          at hcomposed2
        exact cpsBranchWithin_swap hcomposed2
      -- The break-loop certificate, by downward recursion on the remaining fuel.
      have hcert : ∀ fuel' start, start + fuel' = fuel →
          WP.loopBreakNatCert 1 (bb.steps + ba.steps + 2) 1 base (base + 4)
            (base + BitVec.ofNat 64 (4 * (bb.size + ba.size + 3))) cr
            (fun i => asrtM reg rw fun rf ws A => inv i rf ws A)
            (fun i => asrtM reg rw fun rf ws A => inv i rf ws A ∧ guard.holds rf)
            (fun i => asrtM reg rw fun rf ws A => inv i rf ws A ∧ ¬ guard.holds rf)
            (fun i => asrtM reg rw fun rf ws A =>
              Stmt.sp reg rw bb (fun rf ws A => inv i rf ws A ∧ guard.holds rf) rf ws A
                ∧ breakCond.holds rf)
            (asrtM reg rw post) start fuel' := by
        intro fuel'
        induction fuel' with
        | zero =>
            intro start hstart
            simp only [WP.loopBreakNatCert]
            have hsf : start = fuel := by omega
            have hexit : cpsTripleWithin 0
                (base + BitVec.ofNat 64 (4 * (bb.size + ba.size + 3)))
                (base + BitVec.ofNat 64 (4 * (bb.size + ba.size + 3))) cr
                (asrtM reg rw fun rf ws A => inv start rf ws A ∧ ¬ guard.holds rf)
                (asrtM reg rw post) :=
              cpsTripleWithin_entails (asrtM_mono (fun rf ws A hh =>
                hGuardExit start (by omega) rf ws A hh.1 hh.2))
            have hdead : cpsTripleWithin 0 (base + 4)
                (base + BitVec.ofNat 64 (4 * (bb.size + ba.size + 3))) cr
                (asrtM reg rw fun rf ws A => inv start rf ws A ∧ guard.holds rf)
                (asrtM reg rw post) :=
              cpsTripleWithin_unreachable (asrtM_unsat (fun rf ws A hh =>
                hExhausted rf ws A (hsf ▸ hh.1) hh.2))
            exact cpsBranchWithin_merge_same_cr
              (cpsBranchWithin_swap (hheader (fun rf ws A => inv start rf ws A))) hdead hexit
        | succ fuel' ih =>
            intro start hstart
            refine ⟨cpsBranchWithin_swap (hheader (fun rf ws A => inv start rf ws A)),
              hBodyBranch start (by omega), ?_, ?_, ih (start + 1) (by omega)⟩
            · exact asrtM_mono (fun rf ws A hh =>
                hGuardExit start (by omega) rf ws A hh.1 hh.2)
            · exact asrtM_mono (fun rf ws A hh =>
                hBreak start (by omega) rf ws A hh.1 hh.2)
      have hsound := WP.loopBreakNatCert_sound (hcert fuel 0 (by omega))
      exact cpsTripleWithin_weaken
        (asrtM_mono (fun rf ws A hr => hInvInit rf ws A hr))
        (fun _ hp => hp)
        hsound
  | «doWhile» lbl c fuel inv b ihb =>
      simp only [Stmt.offsetsOk, Bool.and_eq_true, decide_eq_true_eq] at hofs
      obtain ⟨⟨⟨hwf, hsizepos⟩, hsizele⟩, hOB⟩ := hofs
      simp only [Stmt.size] at hsz
      -- VC pieces
      have hInvInit : ∀ rf' ws' A', Stmt.sp reg rw b reach rf' ws' A' → inv 0 rf' ws' A' :=
        hvcs.head
      have hInvStep : ∀ i, i < fuel →
          ∀ rf' ws' A', Stmt.sp reg rw b (fun rf ws A => inv i rf ws A ∧ c.holds rf) rf' ws' A' →
            inv (i + 1) rf' ws' A' :=
        hvcs.tail.head
      have hExhausted : ∀ rf ws A, inv fuel rf ws A → ¬ c.holds rf := hvcs.tail.tail.head
      have hBodyVcs := hvcs.tail.tail.tail
      -- Code containment: the flattened code is `b.flatten base ++ [guard]`,
      -- i.e. the body occupies the prefix and the guard branch the suffix
      -- (no header instruction before the body).
      have hflatlen : (b.flatten base).length = b.size := Stmt.flatten_length b base
      have hflat : Stmt.flatten base (.doWhile lbl c fuel inv b)
          = b.flatten base ++ [c.toInstr (Stmt.brOfsBack b.size)] := rfl
      have hlenAll : 4 * ((b.flatten base).length + 1) ≤ 2 ^ 64 := by
        rw [hflatlen]; omega
      have hcode_b : ∀ a' i,
          CodeReq.ofProg base (b.flatten base) a' = some i → cr a' = some i :=
        fun a' i h => hcode a' i (hflat ▸ ofProg_mono_left a' i h)
      have hcode_br : ∀ a' i,
          CodeReq.singleton (base + BitVec.ofNat 64 (4 * b.size))
            (c.toInstr (Stmt.brOfsBack b.size)) a' = some i → cr a' = some i := by
        intro a' i h
        apply hcode a' i
        rw [hflat]
        apply ofProg_mono_right (p1 := b.flatten base)
          (by simp only [List.length_cons, List.length_nil]; rw [hflatlen]; omega)
        rw [hflatlen]
        exact ofProg_head a' i h
      -- The trailing guard branch, at any invariant index: continue to
      -- `base` (the body's own entry) when `guard` holds, fall through to
      -- `exit_` when it fails.  Unlike `while`'s negated header, no swap is
      -- needed: the flattener emits `guard` (not `guard.neg`) since the
      -- branch itself *is* the back-edge.
      have hheader : ∀ (r : Reach),
          cpsBranchWithin 1 (base + BitVec.ofNat 64 (4 * b.size)) cr (asrtM reg rw r)
            base (asrtM reg rw fun rf ws A => r rf ws A ∧ c.holds rf)
            (base + BitVec.ofNat 64 (4 * (b.size + 1)))
              (asrtM reg rw fun rf ws A => r rf ws A ∧ ¬ c.holds rf) := by
        intro r
        have hbr := branch_spec_asrt c (Stmt.brOfsBack b.size) rw r
          (base + BitVec.ofNat 64 (4 * b.size)) hwf
        rw [add_brOfsBack base b.size hsizepos hsizele,
          show (base + BitVec.ofNat 64 (4 * b.size)) + 4
            = base + BitVec.ofNat 64 (4 * (b.size + 1)) from by bv_omega] at hbr
        exact cpsBranchWithin_frameR (bytesRegion reg.base reg.bytes)
          (bytesRegion_pcFree _ _) (cpsBranchWithin_extend_code hcode_br hbr)
      -- Body triple for each continuing iteration index: `inv i ∧ guard` to
      -- `inv (i+1)`, run at the body's entry `base`.
      have hbodyStep : ∀ i, i < fuel →
          cpsTripleWithin b.steps base (base + BitVec.ofNat 64 (4 * b.size)) cr
            (asrtM reg rw fun rf ws A => inv i rf ws A ∧ c.holds rf)
            (asrtM reg rw fun rf ws A => inv (i + 1) rf ws A) := by
        intro i hi
        have hb := ihb base (pfx ++ lbl ++ ".body.")
          (fun rf ws A => inv i rf ws A ∧ c.holds rf) (by simpa [Stmt.callFree] using hleaf)
          hOB (by omega) hcode_b
          (Stmt.vcs_antitone reg rw b _ (fun rf ws A hr => Or.inr ⟨i, hi, hr.1, hr.2⟩) hBodyVcs)
        exact cpsTripleWithin_weaken (fun _ hp => hp)
          (asrtM_mono (fun rf ws A hsp => hInvStep i hi rf ws A hsp)) hb
      -- Prologue: the body runs once, unconditionally, from the statement's
      -- entry reach — the bottom-test loop has no header check before its
      -- first iteration.
      have hprologue :
          cpsTripleWithin b.steps base (base + BitVec.ofNat 64 (4 * b.size)) cr
            (asrtM reg rw reach) (asrtM reg rw fun rf ws A => inv 0 rf ws A) := by
        have hb := ihb base (pfx ++ lbl ++ ".body.") reach
          (by simpa [Stmt.callFree] using hleaf) hOB (by omega) hcode_b
          (Stmt.vcs_antitone reg rw b _ (fun rf ws A hr => Or.inl hr) hBodyVcs)
        exact cpsTripleWithin_weaken (fun _ hp => hp) (asrtM_mono hInvInit) hb
      -- From the prologue's landing point `inv 0`, the remainder is an
      -- ordinary `while`-shaped loop with the guard branch as its header
      -- (`WP.loopNatCert`, unmodified — the bottom-test shape only changes
      -- how the *first* iteration's precondition is reached).
      have hcert : ∀ fuel' start, start + fuel' = fuel →
          WP.loopNatCert 1 b.steps 1 (base + BitVec.ofNat 64 (4 * b.size)) base
            (base + BitVec.ofNat 64 (4 * (b.size + 1))) cr
            (fun i => asrtM reg rw fun rf ws A => inv i rf ws A)
            (fun i => asrtM reg rw fun rf ws A => inv i rf ws A ∧ c.holds rf)
            (fun i => asrtM reg rw fun rf ws A => inv i rf ws A ∧ ¬ c.holds rf)
            (asrtM reg rw fun rf ws A => (∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ c.holds rf)
            start fuel' := by
        intro fuel'
        induction fuel' with
        | zero =>
            intro start hstart
            simp only [WP.loopNatCert]
            have hexit : cpsTripleWithin 0
                (base + BitVec.ofNat 64 (4 * (b.size + 1)))
                (base + BitVec.ofNat 64 (4 * (b.size + 1))) cr
                (asrtM reg rw fun rf ws A => inv start rf ws A ∧ ¬ c.holds rf)
                (asrtM reg rw fun rf ws A => (∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ c.holds rf) :=
              cpsTripleWithin_entails (asrtM_mono (fun rf ws A hh =>
                ⟨⟨start, by omega, hh.1⟩, hh.2⟩))
            have hsf : start = fuel := by omega
            have hdead : cpsTripleWithin 0 base
                (base + BitVec.ofNat 64 (4 * (b.size + 1))) cr
                (asrtM reg rw fun rf ws A => inv start rf ws A ∧ c.holds rf)
                (asrtM reg rw fun rf ws A => (∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ c.holds rf) :=
              cpsTripleWithin_unreachable (asrtM_unsat (fun rf ws A hh =>
                hExhausted rf ws A (hsf ▸ hh.1) hh.2))
            exact cpsBranchWithin_merge_same_cr
              (hheader (fun rf ws A => inv start rf ws A)) hdead hexit
        | succ fuel' ih =>
            intro start hstart
            refine ⟨hheader (fun rf ws A => inv start rf ws A),
              hbodyStep start (by omega), ?_, ih (start + 1) (by omega)⟩
            exact asrtM_mono (fun rf ws A hh => ⟨⟨start, by omega, hh.1⟩, hh.2⟩)
      have hsound := WP.loopNatCert_sound (hcert fuel 0 (by omega))
      simpa [Stmt.size, Stmt.steps] using
        cpsTripleWithin_seq_same_cr hprologue hsound
  | «doWhileS» lbl c fuel inv b ihb =>
      simp only [Stmt.offsetsOk, Bool.and_eq_true, decide_eq_true_eq] at hofs
      obtain ⟨⟨⟨hwf, hsizepos⟩, hsizele⟩, hOB⟩ := hofs
      simp only [Stmt.size] at hsz
      -- VC pieces (snapshot-quantified)
      have hInvInit : ∀ rf₀ ws₀ A₀, reach rf₀ ws₀ A₀ →
          ∀ rf' ws' A', Stmt.sp reg rw b (Reach.exact rf₀ ws₀ A₀) rf' ws' A' →
            inv rf₀ ws₀ A₀ 0 rf' ws' A' := hvcs.head
      have hInvStep : ∀ rf₀ ws₀ A₀, reach rf₀ ws₀ A₀ → ∀ i, i < fuel →
          ∀ rf' ws' A', Stmt.sp reg rw b
              (fun rf ws A => inv rf₀ ws₀ A₀ i rf ws A ∧ c.holds rf) rf' ws' A' →
            inv rf₀ ws₀ A₀ (i + 1) rf' ws' A' := hvcs.tail.head
      have hExhausted : ∀ rf₀ ws₀ A₀, reach rf₀ ws₀ A₀ →
          ∀ rf ws A, inv rf₀ ws₀ A₀ fuel rf ws A → ¬ c.holds rf := hvcs.tail.tail.head
      have hBodyVcs := hvcs.tail.tail.tail
      -- Code containment: identical layout to `doWhile`.
      have hflatlen : (b.flatten base).length = b.size := Stmt.flatten_length b base
      have hflat : Stmt.flatten base (.doWhileS lbl c fuel inv b)
          = b.flatten base ++ [c.toInstr (Stmt.brOfsBack b.size)] := rfl
      have hcode_b : ∀ a' i,
          CodeReq.ofProg base (b.flatten base) a' = some i → cr a' = some i :=
        fun a' i h => hcode a' i (hflat ▸ ofProg_mono_left a' i h)
      have hcode_br : ∀ a' i,
          CodeReq.singleton (base + BitVec.ofNat 64 (4 * b.size))
            (c.toInstr (Stmt.brOfsBack b.size)) a' = some i → cr a' = some i := by
        intro a' i h
        apply hcode a' i
        rw [hflat]
        apply ofProg_mono_right (p1 := b.flatten base)
          (by simp only [List.length_cons, List.length_nil]; rw [hflatlen]; omega)
        rw [hflatlen]
        exact ofProg_head a' i h
      have hheader : ∀ (r : Reach),
          cpsBranchWithin 1 (base + BitVec.ofNat 64 (4 * b.size)) cr (asrtM reg rw r)
            base (asrtM reg rw fun rf ws A => r rf ws A ∧ c.holds rf)
            (base + BitVec.ofNat 64 (4 * (b.size + 1)))
              (asrtM reg rw fun rf ws A => r rf ws A ∧ ¬ c.holds rf) := by
        intro r
        have hbr := branch_spec_asrt c (Stmt.brOfsBack b.size) rw r
          (base + BitVec.ofNat 64 (4 * b.size)) hwf
        rw [add_brOfsBack base b.size hsizepos hsizele,
          show (base + BitVec.ofNat 64 (4 * b.size)) + 4
            = base + BitVec.ofNat 64 (4 * (b.size + 1)) from by bv_omega] at hbr
        exact cpsBranchWithin_frameR (bytesRegion reg.base reg.bytes)
          (bytesRegion_pcFree _ _) (cpsBranchWithin_extend_code hcode_br hbr)
      -- Fix the loop-entry state (the invariant's snapshot); from here the
      -- entry-instantiated invariant family is an ordinary `Nat`-indexed one.
      apply cpsTripleWithin_exists_pre_M
      intro rf₀ ws₀ A₀ hlen hApc hreach₀
      have hbodyStep : ∀ i, i < fuel →
          cpsTripleWithin b.steps base (base + BitVec.ofNat 64 (4 * b.size)) cr
            (asrtM reg rw fun rf ws A => inv rf₀ ws₀ A₀ i rf ws A ∧ c.holds rf)
            (asrtM reg rw fun rf ws A => inv rf₀ ws₀ A₀ (i + 1) rf ws A) := by
        intro i hi
        have hb := ihb base (pfx ++ lbl ++ ".body.")
          (fun rf ws A => inv rf₀ ws₀ A₀ i rf ws A ∧ c.holds rf)
          (by simpa [Stmt.callFree] using hleaf) hOB (by omega) hcode_b
          (Stmt.vcs_antitone reg rw b _
            (fun rf ws A hr => Or.inr ⟨rf₀, ws₀, A₀, hreach₀, i, hi, hr.1, hr.2⟩) hBodyVcs)
        exact cpsTripleWithin_weaken (fun _ hp => hp)
          (asrtM_mono (fun rf ws A hsp =>
            hInvStep rf₀ ws₀ A₀ hreach₀ i hi rf ws A hsp)) hb
      -- Prologue: the body runs once, unconditionally, from the fixed entry
      -- state — `Reach.exact rf₀ ws₀ A₀` matches `.inv_init`'s snapshot shape.
      have hprologue :
          cpsTripleWithin b.steps base (base + BitVec.ofNat 64 (4 * b.size)) cr
            (asrtM reg rw (Reach.exact rf₀ ws₀ A₀))
            (asrtM reg rw fun rf ws A => inv rf₀ ws₀ A₀ 0 rf ws A) := by
        have hb := ihb base (pfx ++ lbl ++ ".body.") (Reach.exact rf₀ ws₀ A₀)
          (by simpa [Stmt.callFree] using hleaf) hOB (by omega) hcode_b
          (Stmt.vcs_antitone reg rw b _
            (by rintro rf ws A ⟨rfl, rfl, rfl⟩; exact Or.inl hreach₀) hBodyVcs)
        exact cpsTripleWithin_weaken (fun _ hp => hp)
          (asrtM_mono (hInvInit rf₀ ws₀ A₀ hreach₀)) hb
      -- From the prologue's landing point `inv rf₀ ws₀ A₀ 0`, the remainder
      -- is an ordinary `while`-shaped loop with the guard branch as its
      -- header (`WP.loopNatCert`, unmodified).
      have hcert : ∀ fuel' start, start + fuel' = fuel →
          WP.loopNatCert 1 b.steps 1 (base + BitVec.ofNat 64 (4 * b.size)) base
            (base + BitVec.ofNat 64 (4 * (b.size + 1))) cr
            (fun i => asrtM reg rw fun rf ws A => inv rf₀ ws₀ A₀ i rf ws A)
            (fun i => asrtM reg rw fun rf ws A => inv rf₀ ws₀ A₀ i rf ws A ∧ c.holds rf)
            (fun i => asrtM reg rw fun rf ws A => inv rf₀ ws₀ A₀ i rf ws A ∧ ¬ c.holds rf)
            (asrtM reg rw fun rf ws A =>
              (∃ i, i ≤ fuel ∧ inv rf₀ ws₀ A₀ i rf ws A) ∧ ¬ c.holds rf)
            start fuel' := by
        intro fuel'
        induction fuel' with
        | zero =>
            intro start hstart
            simp only [WP.loopNatCert]
            have hexit : cpsTripleWithin 0
                (base + BitVec.ofNat 64 (4 * (b.size + 1)))
                (base + BitVec.ofNat 64 (4 * (b.size + 1))) cr
                (asrtM reg rw fun rf ws A => inv rf₀ ws₀ A₀ start rf ws A ∧ ¬ c.holds rf)
                (asrtM reg rw fun rf ws A =>
                  (∃ i, i ≤ fuel ∧ inv rf₀ ws₀ A₀ i rf ws A) ∧ ¬ c.holds rf) :=
              cpsTripleWithin_entails (asrtM_mono (fun rf ws A hh =>
                ⟨⟨start, by omega, hh.1⟩, hh.2⟩))
            have hsf : start = fuel := by omega
            have hdead : cpsTripleWithin 0 base
                (base + BitVec.ofNat 64 (4 * (b.size + 1))) cr
                (asrtM reg rw fun rf ws A => inv rf₀ ws₀ A₀ start rf ws A ∧ c.holds rf)
                (asrtM reg rw fun rf ws A =>
                  (∃ i, i ≤ fuel ∧ inv rf₀ ws₀ A₀ i rf ws A) ∧ ¬ c.holds rf) :=
              cpsTripleWithin_unreachable (asrtM_unsat (fun rf ws A hh =>
                hExhausted rf₀ ws₀ A₀ hreach₀ rf ws A (hsf ▸ hh.1) hh.2))
            exact cpsBranchWithin_merge_same_cr
              (hheader (fun rf ws A => inv rf₀ ws₀ A₀ start rf ws A)) hdead hexit
        | succ fuel' ih =>
            intro start hstart
            refine ⟨hheader (fun rf ws A => inv rf₀ ws₀ A₀ start rf ws A),
              hbodyStep start (by omega), ?_, ih (start + 1) (by omega)⟩
            exact asrtM_mono (fun rf ws A hh => ⟨⟨start, by omega, hh.1⟩, hh.2⟩)
      have hsound := WP.loopNatCert_sound (hcert fuel 0 (by omega))
      have hcomp := cpsTripleWithin_seq_same_cr hprologue hsound
      refine cpsTripleWithin_weaken ?_ ?_ hcomp
      · -- the fixed entry state satisfies the prologue's `Reach.exact` precondition
        intro hp hh
        have hh2 : ((((regFileIs rf₀) ** bytesRegion rw.base ws₀) ** A₀)
            ** bytesRegion reg.base reg.bytes) hp := by xperm_hyp hh
        exact sepConj_mono_left (fun hq hx =>
          ⟨rf₀, ws₀, A₀, hlen, hApc, ⟨rfl, rfl, rfl⟩, hx⟩) hp hh2
      · -- the exit records the entry state alongside the invariant
        exact asrtM_mono (fun rf ws A hh => ⟨rf₀, ws₀, A₀, hreach₀, hh.1, hh.2⟩)
  | call lbl f =>
      exact absurd hleaf (by simp [Stmt.callFree])
  | callReg lbl rs handles =>
      exact absurd hleaf (by simp [Stmt.callFree])
  | callAt lbl roR f =>
      exact absurd hleaf (by simp [Stmt.callFree])
  | callRegS lbl rs handles =>
      exact absurd hleaf (by simp [Stmt.callFree])

end SAsm
end EvmAsm.Rv64
