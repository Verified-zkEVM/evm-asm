/-
  EvmAsm.Rv64.SAsm.StmtSoundCall

  Caller-shaped soundness of the SAsm VC generator: like `Stmt.sound`, but
  the triple carries ownership of `ra` (`regOwn .x1`) so that `call` nodes
  can be verified via `WP.cpsCallWithin` against the callee's `FnHandle`.

  Compared to the leaf theorem, the pre/postcondition is
  `asrtR reg reach := asrtOf reach ** regOwn .x1`: `ra` is owned throughout but
  its *value* is only tracked across call-free segments internally — after a
  call it holds the call's return address, which the shape deliberately
  forgets.  Call-free bodies should keep using `Stmt.sound` (via `Fn.sound`)
  so they can be packaged as `FnHandle`s (`Fn.toHandle`), where `ra`
  invariance matters.

  Design: docs/sasm-design.md §3.6 (Milestone M4).
-/

import EvmAsm.Rv64.SAsm.StmtSound
import EvmAsm.Rv64.WP.Call

namespace EvmAsm.Rv64
namespace SAsm

/-- Caller-shaped embedding of a reachable set: the exposed register file,
    the function's read-only region, plus ownership of `ra`. -/
def asrtR (reg : Region) (reach : Reach) : Assertion :=
  asrtM reg reach ** regOwn .x1

theorem pcFree_asrtR (reg : Region) (reach : Reach) : (asrtR reg reach).pcFree :=
  pcFree_sepConj (pcFree_asrtM _ _) pcFree_regOwn

theorem asrtR_mono {reg : Region} {r₁ r₂ : Reach} (h : ∀ rf, r₁ rf → r₂ rf) :
    ∀ hp, asrtR reg r₁ hp → asrtR reg r₂ hp :=
  fun hp => sepConj_mono_left (asrtM_mono h) hp

theorem asrtR_unsat {reg : Region} {r : Reach} (h : ∀ rf, r rf → False) :
    ∀ hp, asrtR reg r hp → False := by
  rintro hp ⟨h1, h2, -, -, hM, -⟩
  exact asrtM_unsat h h1 hM

/-- Eliminate the unknown `ra` value of an `asrtR`-shaped precondition. -/
theorem cpsTripleWithin_regOwn_right_pre {n : Nat} {entry exit_ : Word}
    {cr : CodeReq} {P Q : Assertion} {r : Reg}
    (h : ∀ v : Word, cpsTripleWithin n entry exit_ cr (P ** (r ↦ᵣ v)) Q) :
    cpsTripleWithin n entry exit_ cr (P ** regOwn r) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR
  obtain ⟨h1a, h1b, hd1, hu1, hPa, ⟨v, hv⟩⟩ := hP1
  exact h v R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu, ⟨h1a, h1b, hd1, hu1, hPa, hv⟩, hR2⟩ hpc

/-- Caller-shaped soundness (Milestone M4): the flattened code of `s`
    satisfies a bounded CPS triple at `asrtR` granularity, provided the
    ambient `cr` also contains every callee's code (`hcallees`) and the call
    sites' address side-conditions hold (`hcalls`). -/
theorem Stmt.soundR (reg : Region) (s : Stmt) (base : Word) (pfx : String)
    (reach : Reach) {cr : CodeReq}
    (hreg : reg.wf)
    (hofs : s.offsetsOk = true)
    (hsz : 4 * s.size < 2 ^ 64)
    (hcode : ∀ a i, CodeReq.ofProg base (s.flatten base) a = some i → cr a = some i)
    (hcallees : s.CalleesIn reg cr)
    (hcalls : s.callsOk base)
    (hvcs : VCs.Hold (Stmt.vcs reg s pfx reach)) :
    cpsTripleWithin s.steps base (base + BitVec.ofNat 64 (4 * s.size)) cr
      (asrtR reg reach) (asrtR reg (Stmt.sp reg s reach)) := by
  induction s generalizing base pfx reach cr with
  | block lbl is =>
      exact cpsTripleWithin_frameR (regOwn .x1) pcFree_regOwn
        (Stmt.sound reg (.block lbl is) base pfx reach hreg rfl hofs hsz hcode hvcs)
  | assert lbl P =>
      exact cpsTripleWithin_frameR (regOwn .x1) pcFree_regOwn
        (Stmt.sound reg (.assert lbl P) base pfx reach hreg rfl hofs hsz hcode hvcs)
  | seq a b iha ihb =>
      simp only [Stmt.offsetsOk, Bool.and_eq_true] at hofs
      simp only [Stmt.size] at hsz
      obtain ⟨hcallees_a, hcallees_b⟩ := hcallees
      obtain ⟨hcalls_a, hcalls_b⟩ := hcalls
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
      have h1 := iha base pfx reach hofs.1 hsza hcode_a hcallees_a hcalls_a hvcs.left
      have h2 := ihb (base + BitVec.ofNat 64 (4 * a.size)) pfx (Stmt.sp reg a reach)
        hofs.2 hszb hcode_b hcallees_b hcalls_b hvcs.right
      have h3 := cpsTripleWithin_seq_same_cr h1 h2
      rw [addr_shift] at h3
      have : 4 * a.size + 4 * b.size = 4 * (a.size + b.size) := by omega
      rw [this] at h3
      exact h3
  | ite lbl c t e iht ihe =>
      simp only [Stmt.offsetsOk, Bool.and_eq_true, decide_eq_true_eq] at hofs
      obtain ⟨⟨⟨⟨hwf, hofsT⟩, hofsJ⟩, hOT⟩, hOE⟩ := hofs
      obtain ⟨hcallees_t, hcallees_e⟩ := hcallees
      obtain ⟨hcalls_t, hcalls_e⟩ := hcalls
      simp only [Stmt.size] at hsz
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
      have hbr := branch_spec_asrt c.neg (Stmt.brOfs (t.size + 2)) reach base
        (by rw [Cond.wf_neg]; exact hwf)
      rw [signExtend13_brOfs hofsT] at hbr
      have hbr' := cpsBranchWithin_frameR (regOwn .x1) pcFree_regOwn
        (cpsBranchWithin_frameR (bytesRegion reg.base reg.bytes)
          (bytesRegion_pcFree _ _) (cpsBranchWithin_extend_code hcode_br hbr))
      have ht := iht (base + 4) (pfx ++ lbl ++ ".t.")
        (fun rf => reach rf ∧ c.holds rf) hOT (by omega) hcode_t
        hcallees_t hcalls_t hvcs.left
      rw [haddr1] at ht
      have hjal := jal0_spec_pcFree (Stmt.jFwd (e.size + 1))
        (base + BitVec.ofNat 64 (4 * (t.size + 1)))
        (pcFree_asrtR reg (Stmt.sp reg t fun rf => reach rf ∧ c.holds rf))
      rw [signExtend21_jFwd hofsJ, haddr2] at hjal
      have hjal' := cpsTripleWithin_extend_code hcode_jal hjal
      have htj := cpsTripleWithin_seq_same_cr ht hjal'
      have he := ihe (base + BitVec.ofNat 64 (4 * (t.size + 2))) (pfx ++ lbl ++ ".e.")
        (fun rf => reach rf ∧ ¬ c.holds rf) hOE (by omega) hcode_e
        hcallees_e hcalls_e hvcs.right
      rw [haddr3] at he
      have hbr'' : cpsBranchWithin 1 base cr (asrtR reg reach)
          (base + BitVec.ofNat 64 (4 * (t.size + 2)))
            (asrtR reg fun rf => reach rf ∧ ¬ c.holds rf)
          (base + 4) (asrtR reg fun rf => reach rf ∧ c.holds rf) := by
        refine cpsBranchWithin_weaken (fun _ hp => hp) ?_ ?_ hbr'
        · exact asrtR_mono (fun rf hh =>
            ⟨hh.1, (Cond.holds_neg c rf).mp hh.2⟩)
        · exact asrtR_mono (fun rf hh =>
            ⟨hh.1, Decidable.of_not_not
              (fun hcc => hh.2 ((Cond.holds_neg c rf).mpr hcc))⟩)
      have harmE : cpsTripleWithin (max (t.steps + 1) e.steps)
          (base + BitVec.ofNat 64 (4 * (t.size + 2)))
          (base + BitVec.ofNat 64 (4 * (t.size + e.size + 2))) cr
          (asrtR reg fun rf => reach rf ∧ ¬ c.holds rf)
          (asrtR reg (Stmt.sp reg (.ite lbl c t e) reach)) := by
        refine cpsTripleWithin_mono_nSteps (Nat.le_max_right _ _)
          (cpsTripleWithin_weaken (fun _ hp => hp) ?_ he)
        exact asrtR_mono (fun rf hsp => Or.inr hsp)
      have harmT : cpsTripleWithin (max (t.steps + 1) e.steps)
          (base + 4)
          (base + BitVec.ofNat 64 (4 * (t.size + e.size + 2))) cr
          (asrtR reg fun rf => reach rf ∧ c.holds rf)
          (asrtR reg (Stmt.sp reg (.ite lbl c t e) reach)) := by
        refine cpsTripleWithin_mono_nSteps (Nat.le_max_left _ _)
          (cpsTripleWithin_weaken (fun _ hp => hp) ?_ htj)
        exact asrtR_mono (fun rf hsp => Or.inl hsp)
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
      have hbr' := cpsBranchWithin_frameR (regOwn .x1) pcFree_regOwn
        (cpsBranchWithin_frameR (bytesRegion reg.base reg.bytes)
          (bytesRegion_pcFree _ _) (cpsBranchWithin_extend_code hcode_br hbr))
      have hb := ihb (base + 4) (pfx ++ lbl ++ ".")
        (fun rf => reach rf ∧ c.holds rf)
        hOB (by omega) hcode_b hcallees hcalls hvcs
      rw [show (base + 4) + BitVec.ofNat 64 (4 * b.size)
          = base + BitVec.ofNat 64 (4 * (b.size + 1)) from by bv_omega] at hb
      have hskip : cpsTripleWithin b.steps
          (base + BitVec.ofNat 64 (4 * (b.size + 1)))
          (base + BitVec.ofNat 64 (4 * (b.size + 1))) cr
          (asrtR reg fun rf => reach rf ∧ c.neg.holds rf)
          (asrtR reg (Stmt.sp reg (.when lbl c b) reach)) := by
        apply cpsTripleWithin_mono_nSteps (Nat.zero_le _)
        apply cpsTripleWithin_entails
        exact asrtR_mono (fun rf hh =>
          Or.inr ⟨hh.1, (Cond.holds_neg c rf).mp hh.2⟩)
      have hbody : cpsTripleWithin b.steps (base + 4)
          (base + BitVec.ofNat 64 (4 * (b.size + 1))) cr
          (asrtR reg fun rf => reach rf ∧ ¬ c.neg.holds rf)
          (asrtR reg (Stmt.sp reg (.when lbl c b) reach)) := by
        refine cpsTripleWithin_weaken ?_ ?_ hb
        · exact asrtR_mono (fun rf hh =>
            ⟨hh.1, Decidable.of_not_not
              (fun hcc => hh.2 ((Cond.holds_neg c rf).mpr hcc))⟩)
        · exact asrtR_mono (fun rf hsp => Or.inl hsp)
      exact cpsBranchWithin_merge_same_cr hbr' hskip hbody
  | «while» lbl c fuel inv b ihb =>
      simp only [Stmt.offsetsOk, Bool.and_eq_true, decide_eq_true_eq] at hofs
      obtain ⟨⟨⟨hwf, hofsHdr⟩, hofsBack⟩, hOB⟩ := hofs
      simp only [Stmt.size] at hsz
      have hInvInit : ∀ rf, reach rf → inv 0 rf := hvcs.head
      have hInvStep : ∀ i, i < fuel →
          ∀ rf', Stmt.sp reg b (fun rf => inv i rf ∧ c.holds rf) rf' → inv (i + 1) rf' :=
        hvcs.tail.head
      have hExhausted : ∀ rf, inv fuel rf → ¬ c.holds rf := hvcs.tail.tail.head
      have hBodyVcs := hvcs.tail.tail.tail
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
      have hbodyEnd : (base + 4) + BitVec.ofNat 64 (4 * b.size)
          = base + BitVec.ofNat 64 (4 * (b.size + 1)) := by bv_omega
      have hheader : ∀ (r : Reach),
          cpsBranchWithin 1 base cr (asrtR reg r)
            (base + BitVec.ofNat 64 (4 * (b.size + 2)))
              (asrtR reg fun rf => r rf ∧ ¬ c.holds rf)
            (base + 4) (asrtR reg fun rf => r rf ∧ c.holds rf) := by
        intro r
        have hbr := branch_spec_asrt c.neg (Stmt.brOfs (b.size + 2)) r base
          (by rw [Cond.wf_neg]; exact hwf)
        rw [signExtend13_brOfs hofsHdr] at hbr
        have hbr' := cpsBranchWithin_frameR (regOwn .x1) pcFree_regOwn
          (cpsBranchWithin_frameR (bytesRegion reg.base reg.bytes)
            (bytesRegion_pcFree _ _) (cpsBranchWithin_extend_code hcode_br hbr))
        refine cpsBranchWithin_weaken (fun _ hp => hp) ?_ ?_ hbr'
        · exact asrtR_mono (fun rf hh =>
            ⟨hh.1, (Cond.holds_neg c rf).mp hh.2⟩)
        · exact asrtR_mono (fun rf hh =>
            ⟨hh.1, Decidable.of_not_not
              (fun hcc => hh.2 ((Cond.holds_neg c rf).mpr hcc))⟩)
      have hbodyStep : ∀ i, i < fuel →
          cpsTripleWithin (b.steps + 1) (base + 4) base cr
            (asrtR reg fun rf => inv i rf ∧ c.holds rf)
            (asrtR reg fun rf => inv (i + 1) rf) := by
        intro i hi
        have hb := ihb (base + 4) (pfx ++ lbl ++ ".body.")
          (fun rf => inv i rf ∧ c.holds rf)
          hOB (by omega) hcode_b hcallees hcalls
          (Stmt.vcs_antitone reg b _ (fun rf hr => ⟨i, hi, hr.1, hr.2⟩) hBodyVcs)
        have hjal := jal0_spec_pcFree (Stmt.jBack (b.size + 1))
          ((base + 4) + BitVec.ofNat 64 (4 * b.size))
          (pcFree_asrtR reg (Stmt.sp reg b fun rf => inv i rf ∧ c.holds rf))
        rw [hbodyEnd, add_jBack base (b.size + 1) (by omega) hofsBack] at hjal
        rw [← hbodyEnd] at hjal
        have hjal' := cpsTripleWithin_extend_code hcode_jal hjal
        have hseq := cpsTripleWithin_seq_same_cr hb hjal'
        exact cpsTripleWithin_weaken (fun _ hp => hp)
          (asrtR_mono (fun rf hsp => hInvStep i hi rf hsp)) hseq
      have hcert : ∀ fuel' start, start + fuel' = fuel →
          WP.loopNatCert 1 (b.steps + 1) 1 base (base + 4)
            (base + BitVec.ofNat 64 (4 * (b.size + 2))) cr
            (fun i => asrtR reg fun rf => inv i rf)
            (fun i => asrtR reg fun rf => inv i rf ∧ c.holds rf)
            (fun i => asrtR reg fun rf => inv i rf ∧ ¬ c.holds rf)
            (asrtR reg fun rf => (∃ i, i ≤ fuel ∧ inv i rf) ∧ ¬ c.holds rf)
            start fuel' := by
        intro fuel'
        induction fuel' with
        | zero =>
            intro start hstart
            simp only [WP.loopNatCert]
            have hexit : cpsTripleWithin 0
                (base + BitVec.ofNat 64 (4 * (b.size + 2)))
                (base + BitVec.ofNat 64 (4 * (b.size + 2))) cr
                (asrtR reg fun rf => inv start rf ∧ ¬ c.holds rf)
                (asrtR reg fun rf => (∃ i, i ≤ fuel ∧ inv i rf) ∧ ¬ c.holds rf) :=
              cpsTripleWithin_entails (asrtR_mono (fun rf hh =>
                ⟨⟨start, by omega, hh.1⟩, hh.2⟩))
            have hsf : start = fuel := by omega
            have hdead : cpsTripleWithin 0 (base + 4)
                (base + BitVec.ofNat 64 (4 * (b.size + 2))) cr
                (asrtR reg fun rf => inv start rf ∧ c.holds rf)
                (asrtR reg fun rf => (∃ i, i ≤ fuel ∧ inv i rf) ∧ ¬ c.holds rf) :=
              cpsTripleWithin_unreachable (asrtR_unsat (fun rf hh =>
                hExhausted rf (hsf ▸ hh.1) hh.2))
            exact cpsBranchWithin_merge_same_cr
              (cpsBranchWithin_swap (hheader (fun rf => inv start rf))) hdead hexit
        | succ fuel' ih =>
            intro start hstart
            refine ⟨cpsBranchWithin_swap (hheader (fun rf => inv start rf)),
              hbodyStep start (by omega), ?_, ih (start + 1) (by omega)⟩
            exact asrtR_mono (fun rf hh => ⟨⟨start, by omega, hh.1⟩, hh.2⟩)
      have hsound := WP.loopNatCert_sound (hcert fuel 0 (by omega))
      exact cpsTripleWithin_weaken
        (asrtR_mono (fun rf hr => hInvInit rf hr))
        (fun _ hp => hp)
        hsound
  | call lbl f =>
      obtain ⟨hoffset, halign, hnotself⟩ := hcalls
      obtain ⟨hcalleeCode, hregeq⟩ := hcallees
      have hpreVC : ∀ rf, reach rf → f.pre rf := hvcs _ (List.mem_singleton_self _)
      -- callee triple, retargeted at the aligned return address
      have hret' : cpsTripleWithin f.nSteps f.entry ((base + 4) &&& ~~~(1 : Word))
          f.code
          ((.x1 ↦ᵣ (base + 4)) ** asrtM reg f.pre)
          ((.x1 ↦ᵣ (base + 4)) ** asrtM reg f.post) := by
        rw [halign, ← hregeq]
        exact f.sound (base + 4) halign
      have hdisj : (CodeReq.singleton base
          (.JAL .x1 (BitVec.setWidth 21 (f.entry - base)))).Disjoint f.code := by
        intro a
        by_cases ha : a = base
        · subst ha
          exact Or.inr hnotself
        · left
          simp [CodeReq.singleton, ha]
      have hmono : ∀ a i,
          ((CodeReq.singleton base
            (.JAL .x1 (BitVec.setWidth 21 (f.entry - base)))).union f.code) a = some i →
          cr a = some i := by
        intro a i h
        simp only [CodeReq.union] at h
        cases hs : CodeReq.singleton base
            (.JAL .x1 (BitVec.setWidth 21 (f.entry - base))) a with
        | none =>
            rw [hs] at h
            exact hcalleeCode a i h
        | some j =>
            rw [hs] at h
            apply hcode a i
            rw [show Stmt.flatten base (.call lbl f)
              = [.JAL .x1 (BitVec.setWidth 21 (f.entry - base))] from rfl,
              CodeReq.ofProg_singleton]
            rw [hs]
            exact h
      -- the framed call triple, for each old value of ra
      have hcall : ∀ vOld : Word,
          cpsTripleWithin (1 + f.nSteps) base (base + 4) cr
            ((asrtM reg f.pre) ** (.x1 ↦ᵣ vOld))
            ((asrtM reg (Stmt.sp reg (.call lbl f) reach)) ** regOwn .x1) := by
        intro vOld
        have h := WP.cpsCallWithin (vOld := vOld)
          (BitVec.setWidth 21 (f.entry - base)) hoffset halign
          (pcFree_asrtM reg f.pre) hdisj hret'
        have h' := cpsTripleWithin_extend_code hmono h
        refine cpsTripleWithin_weaken ?_ ?_ h'
        · intro hp hh
          rw [sepConj_comm'] at hh
          exact hh
        · intro hp hh
          rw [sepConj_comm' (.x1 ↦ᵣ (base + 4))] at hh
          exact sepConj_mono_right (fun hq hx => ⟨base + 4, hx⟩) hp hh
      -- assemble: eliminate the unknown ra value, weaken the entry reach
      have hfinal : cpsTripleWithin (1 + f.nSteps) base (base + 4) cr
          (asrtR reg reach) (asrtR reg (Stmt.sp reg (.call lbl f) reach)) := by
        refine cpsTripleWithin_weaken
          (sepConj_mono_left (asrtM_mono (fun rf hr => hpreVC rf hr)))
          (fun _ hp => hp)
          (cpsTripleWithin_regOwn_right_pre hcall)
      simp only [Stmt.steps, Stmt.size, Nat.mul_one]
      have h4 : base + BitVec.ofNat 64 4 = base + 4 := rfl
      rw [h4]
      exact hfinal

end SAsm
end EvmAsm.Rv64
