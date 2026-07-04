/-
  EvmAsm.Rv64.SAsm.StmtSoundCall

  Caller-shaped soundness of the SAsm VC generator: like `Stmt.sound`, but
  the triple carries ownership of `ra` (`regOwn .x1`) so that `call` nodes
  can be verified via `WP.cpsCallWithin` against the callee's `FnHandle`.

  Compared to the leaf theorem, the pre/postcondition is
  `asrtR reg rw reach := asrtOf reach ** regOwn .x1`: `ra` is owned throughout but
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
def asrtR (reg : Region) (rw : RwRegion) (reach : Reach) : Assertion :=
  asrtM reg rw reach ** regOwn .x1

theorem pcFree_asrtR (reg : Region) (rw : RwRegion) (reach : Reach) :
    (asrtR reg rw reach).pcFree :=
  pcFree_sepConj (pcFree_asrtM _ _ _) pcFree_regOwn

theorem asrtR_mono {reg : Region} {rw : RwRegion} {r₁ r₂ : Reach}
    (h : ∀ rf ws A, r₁ rf ws A → r₂ rf ws A) :
    ∀ hp, asrtR reg rw r₁ hp → asrtR reg rw r₂ hp :=
  fun hp => sepConj_mono_left (asrtM_mono h) hp

theorem asrtR_unsat {reg : Region} {rw : RwRegion} {r : Reach}
    (h : ∀ rf ws A, r rf ws A → False) :
    ∀ hp, asrtR reg rw r hp → False := by
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

/-- Split `asrtM ** X` into a per-symbolic-state family (both regions and the
    extra atom `X` alongside). -/
theorem cpsTripleWithin_exists_pre_M_frame {n : Nat} {entry exit_ : Word}
    {cr : CodeReq} {X : Assertion} {reg : Region} {rw : RwRegion}
    {reach : Reach} {Q : Assertion}
    (h : ∀ rf ws (A : Assertion), ws.length = rw.len → A.pcFree → reach rf ws A →
      cpsTripleWithin n entry exit_ cr
        ((((regFileIs rf) ** bytesRegion rw.base ws) ** A) **
          (bytesRegion reg.base reg.bytes ** X)) Q) :
    cpsTripleWithin n entry exit_ cr (asrtM reg rw reach ** X) Q := by
  intro R hR s hcr hPR hpc
  rw [show asrtM reg rw reach
      = (asrtOf rw reach ** bytesRegion reg.base reg.bytes) from rfl,
    sepConj_assoc', sepConj_assoc'] at hPR
  -- hPR : (asrtOf ** (bytesRegion reg ** (X ** R)))
  obtain ⟨hp, hcompat, h1, h2, hd, hu, ⟨rf, ws, A, hlen, hApc, hreach, hsts⟩, hR2⟩ := hPR
  have hPR' : (((((regFileIs rf) ** bytesRegion rw.base ws) ** A) **
      (bytesRegion reg.base reg.bytes ** (X ** R)))).holdsFor s :=
    ⟨hp, hcompat, h1, h2, hd, hu, hsts, hR2⟩
  rw [← sepConj_assoc' (bytesRegion reg.base reg.bytes) X R,
    ← sepConj_assoc'] at hPR'
  exact h rf ws A hlen hApc hreach R hR s hcr hPR' hpc

/-- One-step spec of the indirect-call jump `jalr x1, rs, 0`: the (exposed)
    target register is read out of `regFileIs`, the return address lands in
    the separately owned `ra`, and control transfers to the masked target.
    The `regFileIs`-based analogue of `generic_jalr_spec_within`. -/
theorem jalr_call_spec_within (rs : Reg) (rf : RegFile) (vOld base : Word)
    (hrs : Reg.isExposed rs = true) :
    cpsTripleWithin 1 base
      ((rf.get rs + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word))
      (CodeReq.singleton base (.JALR .x1 rs 0))
      (((.x1 : Reg) ↦ᵣ vOld) ** regFileIs rf)
      (((.x1 : Reg) ↦ᵣ (base + 4)) ** regFileIs rf) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.JALR .x1 rs 0) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hPR1 := hPR
  rw [sepConj_assoc', sepConj_left_comm] at hPR1
  -- hPR1 : (regFileIs rf ** ((.x1 ↦ᵣ vOld) ** R))
  have hrsv : s.getReg rs = rf.get rs :=
    holdsFor_regFileIs_agree hPR1 (by rw [hrs]; rfl)
  have hstep' : step s = some (execInstrBr s (.JALR .x1 rs 0)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  have hexec : execInstrBr s (.JALR .x1 rs 0)
      = (s.setReg .x1 (s.pc + 4)).setPC
          ((rf.get rs + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) := by
    simp only [execInstrBr, hrsv]
    rfl
  refine ⟨1, Nat.le_refl 1, (s.setReg .x1 (s.pc + 4)).setPC
    ((rf.get rs + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec]; rfl
  · have hPR2 := hPR
    rw [sepConj_assoc'] at hPR2
    -- hPR2 : ((.x1 ↦ᵣ vOld) ** (regFileIs rf ** R))
    have h1 := holdsFor_sepConj_regIs_setReg (v' := s.pc + 4)
      (show (.x1 : Reg) ≠ .x0 from by decide) hPR2
    rw [← sepConj_assoc'] at h1
    exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj (by pcFree) (pcFree_regFileIs _)) hR) h1

/-- A table member's step bound is below the table's folded maximum. -/
theorem FnHandle.nSteps_le_foldr_max {h : FnHandle} :
    ∀ {hs : List FnHandle}, h ∈ hs →
      h.nSteps ≤ hs.foldr (fun f m => max f.nSteps m) 0
  | a :: as, hmem => by
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (FnHandle.nSteps_le_foldr_max hmem')
          (Nat.le_max_right _ _)

/-- A table member's step bound is below the table's folded maximum
    (snapshot-parameterized handles). -/
theorem FnHandleS.nSteps_le_foldr_max {h : FnHandleS} :
    ∀ {hs : List FnHandleS}, h ∈ hs →
      h.nSteps ≤ hs.foldr (fun f m => max f.nSteps m) 0
  | a :: as, hmem => by
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (FnHandleS.nSteps_le_foldr_max hmem')
          (Nat.le_max_right _ _)

/-- Caller-shaped soundness (Milestone M4): the flattened code of `s`
    satisfies a bounded CPS triple at `asrtR` granularity, provided the
    ambient `cr` also contains every callee's code (`hcallees`) and the call
    sites' address side-conditions hold (`hcalls`). -/
theorem Stmt.soundR (reg : Region) (rw : RwRegion) (s : Stmt) (base : Word)
    (pfx : String) (reach : Reach) {cr : CodeReq}
    (hreg : reg.wf) (hrw : rw.wf)
    (hofs : s.offsetsOk = true)
    (hsz : 4 * s.size < 2 ^ 64)
    (hcode : ∀ a i, CodeReq.ofProg base (s.flatten base) a = some i → cr a = some i)
    (hcallees : s.CalleesIn reg rw cr)
    (hcalls : s.callsOk base)
    (hvcs : VCs.Hold (Stmt.vcs reg rw s pfx reach)) :
    cpsTripleWithin s.steps base (base + BitVec.ofNat 64 (4 * s.size)) cr
      (asrtR reg rw reach) (asrtR reg rw (Stmt.sp reg rw s reach)) := by
  induction s generalizing base pfx reach cr with
  | block lbl is =>
      exact cpsTripleWithin_frameR (regOwn .x1) pcFree_regOwn
        (Stmt.sound reg rw (.block lbl is) base pfx reach hreg hrw rfl hofs hsz hcode hvcs)
  | assert lbl P =>
      exact cpsTripleWithin_frameR (regOwn .x1) pcFree_regOwn
        (Stmt.sound reg rw (.assert lbl P) base pfx reach hreg hrw rfl hofs hsz hcode hvcs)
  | ghost lbl R =>
      exact cpsTripleWithin_frameR (regOwn .x1) pcFree_regOwn
        (Stmt.sound reg rw (.ghost lbl R) base pfx reach hreg hrw rfl hofs hsz hcode hvcs)
  | blockAt lbl p winR is =>
      exact cpsTripleWithin_frameR (regOwn .x1) pcFree_regOwn
        (Stmt.sound reg rw (.blockAt lbl p winR is) base pfx reach hreg hrw rfl hofs hsz
          hcode hvcs)
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
      have h2 := ihb (base + BitVec.ofNat 64 (4 * a.size)) pfx (Stmt.sp reg rw a reach)
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
      have hbr := branch_spec_asrt c.neg (Stmt.brOfs (t.size + 2)) rw reach base
        (by rw [Cond.wf_neg]; exact hwf)
      rw [signExtend13_brOfs hofsT] at hbr
      have hbr' := cpsBranchWithin_frameR (regOwn .x1) pcFree_regOwn
        (cpsBranchWithin_frameR (bytesRegion reg.base reg.bytes)
          (bytesRegion_pcFree _ _) (cpsBranchWithin_extend_code hcode_br hbr))
      have ht := iht (base + 4) (pfx ++ lbl ++ ".t.")
        (fun rf ws A => reach rf ws A ∧ c.holds rf) hOT (by omega) hcode_t
        hcallees_t hcalls_t hvcs.left
      rw [haddr1] at ht
      have hjal := jal0_spec_pcFree (Stmt.jFwd (e.size + 1))
        (base + BitVec.ofNat 64 (4 * (t.size + 1)))
        (pcFree_asrtR reg rw (Stmt.sp reg rw t fun rf ws A => reach rf ws A ∧ c.holds rf))
      rw [signExtend21_jFwd hofsJ, haddr2] at hjal
      have hjal' := cpsTripleWithin_extend_code hcode_jal hjal
      have htj := cpsTripleWithin_seq_same_cr ht hjal'
      have he := ihe (base + BitVec.ofNat 64 (4 * (t.size + 2))) (pfx ++ lbl ++ ".e.")
        (fun rf ws A => reach rf ws A ∧ ¬ c.holds rf) hOE (by omega) hcode_e
        hcallees_e hcalls_e hvcs.right
      rw [haddr3] at he
      have hbr'' : cpsBranchWithin 1 base cr (asrtR reg rw reach)
          (base + BitVec.ofNat 64 (4 * (t.size + 2)))
            (asrtR reg rw fun rf ws A => reach rf ws A ∧ ¬ c.holds rf)
          (base + 4) (asrtR reg rw fun rf ws A => reach rf ws A ∧ c.holds rf) := by
        refine cpsBranchWithin_weaken (fun _ hp => hp) ?_ ?_ hbr'
        · exact asrtR_mono (fun rf ws A hh =>
            ⟨hh.1, (Cond.holds_neg c rf).mp hh.2⟩)
        · exact asrtR_mono (fun rf ws A hh =>
            ⟨hh.1, Decidable.of_not_not
              (fun hcc => hh.2 ((Cond.holds_neg c rf).mpr hcc))⟩)
      have harmE : cpsTripleWithin (max (t.steps + 1) e.steps)
          (base + BitVec.ofNat 64 (4 * (t.size + 2)))
          (base + BitVec.ofNat 64 (4 * (t.size + e.size + 2))) cr
          (asrtR reg rw fun rf ws A => reach rf ws A ∧ ¬ c.holds rf)
          (asrtR reg rw (Stmt.sp reg rw (.ite lbl c t e) reach)) := by
        refine cpsTripleWithin_mono_nSteps (Nat.le_max_right _ _)
          (cpsTripleWithin_weaken (fun _ hp => hp) ?_ he)
        exact asrtR_mono (fun rf ws A hsp => Or.inr hsp)
      have harmT : cpsTripleWithin (max (t.steps + 1) e.steps)
          (base + 4)
          (base + BitVec.ofNat 64 (4 * (t.size + e.size + 2))) cr
          (asrtR reg rw fun rf ws A => reach rf ws A ∧ c.holds rf)
          (asrtR reg rw (Stmt.sp reg rw (.ite lbl c t e) reach)) := by
        refine cpsTripleWithin_mono_nSteps (Nat.le_max_left _ _)
          (cpsTripleWithin_weaken (fun _ hp => hp) ?_ htj)
        exact asrtR_mono (fun rf ws A hsp => Or.inl hsp)
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
      have hbr' := cpsBranchWithin_frameR (regOwn .x1) pcFree_regOwn
        (cpsBranchWithin_frameR (bytesRegion reg.base reg.bytes)
          (bytesRegion_pcFree _ _) (cpsBranchWithin_extend_code hcode_br hbr))
      have hb := ihb (base + 4) (pfx ++ lbl ++ ".")
        (fun rf ws A => reach rf ws A ∧ c.holds rf)
        hOB (by omega) hcode_b hcallees hcalls hvcs
      rw [show (base + 4) + BitVec.ofNat 64 (4 * b.size)
          = base + BitVec.ofNat 64 (4 * (b.size + 1)) from by bv_omega] at hb
      have hskip : cpsTripleWithin b.steps
          (base + BitVec.ofNat 64 (4 * (b.size + 1)))
          (base + BitVec.ofNat 64 (4 * (b.size + 1))) cr
          (asrtR reg rw fun rf ws A => reach rf ws A ∧ c.neg.holds rf)
          (asrtR reg rw (Stmt.sp reg rw (.when lbl c b) reach)) := by
        apply cpsTripleWithin_mono_nSteps (Nat.zero_le _)
        apply cpsTripleWithin_entails
        exact asrtR_mono (fun rf ws A hh =>
          Or.inr ⟨hh.1, (Cond.holds_neg c rf).mp hh.2⟩)
      have hbody : cpsTripleWithin b.steps (base + 4)
          (base + BitVec.ofNat 64 (4 * (b.size + 1))) cr
          (asrtR reg rw fun rf ws A => reach rf ws A ∧ ¬ c.neg.holds rf)
          (asrtR reg rw (Stmt.sp reg rw (.when lbl c b) reach)) := by
        refine cpsTripleWithin_weaken ?_ ?_ hb
        · exact asrtR_mono (fun rf ws A hh =>
            ⟨hh.1, Decidable.of_not_not
              (fun hcc => hh.2 ((Cond.holds_neg c rf).mpr hcc))⟩)
        · exact asrtR_mono (fun rf ws A hsp => Or.inl hsp)
      exact cpsBranchWithin_merge_same_cr hbr' hskip hbody
  | «while» lbl c fuel inv b ihb =>
      simp only [Stmt.offsetsOk, Bool.and_eq_true, decide_eq_true_eq] at hofs
      obtain ⟨⟨⟨hwf, hofsHdr⟩, hofsBack⟩, hOB⟩ := hofs
      simp only [Stmt.size] at hsz
      have hInvInit : ∀ rf ws A, reach rf ws A → inv 0 rf ws A := hvcs.head
      have hInvStep : ∀ i, i < fuel →
          ∀ rf' ws' A', Stmt.sp reg rw b
              (fun rf ws A => inv i rf ws A ∧ c.holds rf) rf' ws' A' →
            inv (i + 1) rf' ws' A' :=
        hvcs.tail.head
      have hExhausted : ∀ rf ws A, inv fuel rf ws A → ¬ c.holds rf := hvcs.tail.tail.head
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
          cpsBranchWithin 1 base cr (asrtR reg rw r)
            (base + BitVec.ofNat 64 (4 * (b.size + 2)))
              (asrtR reg rw fun rf ws A => r rf ws A ∧ ¬ c.holds rf)
            (base + 4) (asrtR reg rw fun rf ws A => r rf ws A ∧ c.holds rf) := by
        intro r
        have hbr := branch_spec_asrt c.neg (Stmt.brOfs (b.size + 2)) rw r base
          (by rw [Cond.wf_neg]; exact hwf)
        rw [signExtend13_brOfs hofsHdr] at hbr
        have hbr' := cpsBranchWithin_frameR (regOwn .x1) pcFree_regOwn
          (cpsBranchWithin_frameR (bytesRegion reg.base reg.bytes)
            (bytesRegion_pcFree _ _) (cpsBranchWithin_extend_code hcode_br hbr))
        refine cpsBranchWithin_weaken (fun _ hp => hp) ?_ ?_ hbr'
        · exact asrtR_mono (fun rf ws A hh =>
            ⟨hh.1, (Cond.holds_neg c rf).mp hh.2⟩)
        · exact asrtR_mono (fun rf ws A hh =>
            ⟨hh.1, Decidable.of_not_not
              (fun hcc => hh.2 ((Cond.holds_neg c rf).mpr hcc))⟩)
      have hbodyStep : ∀ i, i < fuel →
          cpsTripleWithin (b.steps + 1) (base + 4) base cr
            (asrtR reg rw fun rf ws A => inv i rf ws A ∧ c.holds rf)
            (asrtR reg rw fun rf ws A => inv (i + 1) rf ws A) := by
        intro i hi
        have hb := ihb (base + 4) (pfx ++ lbl ++ ".body.")
          (fun rf ws A => inv i rf ws A ∧ c.holds rf)
          hOB (by omega) hcode_b hcallees hcalls
          (Stmt.vcs_antitone reg rw b _ (fun rf ws A hr => ⟨i, hi, hr.1, hr.2⟩) hBodyVcs)
        have hjal := jal0_spec_pcFree (Stmt.jBack (b.size + 1))
          ((base + 4) + BitVec.ofNat 64 (4 * b.size))
          (pcFree_asrtR reg rw (Stmt.sp reg rw b fun rf ws A => inv i rf ws A ∧ c.holds rf))
        rw [hbodyEnd, add_jBack base (b.size + 1) (by omega) hofsBack] at hjal
        rw [← hbodyEnd] at hjal
        have hjal' := cpsTripleWithin_extend_code hcode_jal hjal
        have hseq := cpsTripleWithin_seq_same_cr hb hjal'
        exact cpsTripleWithin_weaken (fun _ hp => hp)
          (asrtR_mono (fun rf ws A hsp => hInvStep i hi rf ws A hsp)) hseq
      have hcert : ∀ fuel' start, start + fuel' = fuel →
          WP.loopNatCert 1 (b.steps + 1) 1 base (base + 4)
            (base + BitVec.ofNat 64 (4 * (b.size + 2))) cr
            (fun i => asrtR reg rw fun rf ws A => inv i rf ws A)
            (fun i => asrtR reg rw fun rf ws A => inv i rf ws A ∧ c.holds rf)
            (fun i => asrtR reg rw fun rf ws A => inv i rf ws A ∧ ¬ c.holds rf)
            (asrtR reg rw fun rf ws A => (∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ c.holds rf)
            start fuel' := by
        intro fuel'
        induction fuel' with
        | zero =>
            intro start hstart
            simp only [WP.loopNatCert]
            have hexit : cpsTripleWithin 0
                (base + BitVec.ofNat 64 (4 * (b.size + 2)))
                (base + BitVec.ofNat 64 (4 * (b.size + 2))) cr
                (asrtR reg rw fun rf ws A => inv start rf ws A ∧ ¬ c.holds rf)
                (asrtR reg rw fun rf ws A => (∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ c.holds rf) :=
              cpsTripleWithin_entails (asrtR_mono (fun rf ws A hh =>
                ⟨⟨start, by omega, hh.1⟩, hh.2⟩))
            have hsf : start = fuel := by omega
            have hdead : cpsTripleWithin 0 (base + 4)
                (base + BitVec.ofNat 64 (4 * (b.size + 2))) cr
                (asrtR reg rw fun rf ws A => inv start rf ws A ∧ c.holds rf)
                (asrtR reg rw fun rf ws A => (∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ c.holds rf) :=
              cpsTripleWithin_unreachable (asrtR_unsat (fun rf ws A hh =>
                hExhausted rf ws A (hsf ▸ hh.1) hh.2))
            exact cpsBranchWithin_merge_same_cr
              (cpsBranchWithin_swap (hheader (fun rf ws A => inv start rf ws A))) hdead hexit
        | succ fuel' ih =>
            intro start hstart
            refine ⟨cpsBranchWithin_swap (hheader (fun rf ws A => inv start rf ws A)),
              hbodyStep start (by omega), ?_, ih (start + 1) (by omega)⟩
            exact asrtR_mono (fun rf ws A hh => ⟨⟨start, by omega, hh.1⟩, hh.2⟩)
      have hsound := WP.loopNatCert_sound (hcert fuel 0 (by omega))
      exact cpsTripleWithin_weaken
        (asrtR_mono (fun rf ws A hr => hInvInit rf ws A hr))
        (fun _ hp => hp)
        hsound
  | «whileS» lbl c fuel inv b ihb =>
      simp only [Stmt.offsetsOk, Bool.and_eq_true, decide_eq_true_eq] at hofs
      obtain ⟨⟨⟨hwf, hofsHdr⟩, hofsBack⟩, hOB⟩ := hofs
      simp only [Stmt.size] at hsz
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
      have hbodyEnd : (base + 4) + BitVec.ofNat 64 (4 * b.size)
          = base + BitVec.ofNat 64 (4 * (b.size + 1)) := by bv_omega
      have hheader : ∀ (r : Reach),
          cpsBranchWithin 1 base cr (asrtR reg rw r)
            (base + BitVec.ofNat 64 (4 * (b.size + 2)))
              (asrtR reg rw fun rf ws A => r rf ws A ∧ ¬ c.holds rf)
            (base + 4) (asrtR reg rw fun rf ws A => r rf ws A ∧ c.holds rf) := by
        intro r
        have hbr := branch_spec_asrt c.neg (Stmt.brOfs (b.size + 2)) rw r base
          (by rw [Cond.wf_neg]; exact hwf)
        rw [signExtend13_brOfs hofsHdr] at hbr
        have hbr' := cpsBranchWithin_frameR (regOwn .x1) pcFree_regOwn
          (cpsBranchWithin_frameR (bytesRegion reg.base reg.bytes)
            (bytesRegion_pcFree _ _) (cpsBranchWithin_extend_code hcode_br hbr))
        refine cpsBranchWithin_weaken (fun _ hp => hp) ?_ ?_ hbr'
        · exact asrtR_mono (fun rf ws A hh =>
            ⟨hh.1, (Cond.holds_neg c rf).mp hh.2⟩)
        · exact asrtR_mono (fun rf ws A hh =>
            ⟨hh.1, Decidable.of_not_not
              (fun hcc => hh.2 ((Cond.holds_neg c rf).mpr hcc))⟩)
      -- Fix the loop-entry state (the invariant's snapshot)
      show cpsTripleWithin _ _ _ _ (asrtM reg rw reach ** regOwn .x1) _
      apply cpsTripleWithin_exists_pre_M_frame
      intro rf₀ ws₀ A₀ hlen hApc hreach₀
      have hbodyStep : ∀ i, i < fuel →
          cpsTripleWithin (b.steps + 1) (base + 4) base cr
            (asrtR reg rw fun rf ws A => inv rf₀ ws₀ A₀ i rf ws A ∧ c.holds rf)
            (asrtR reg rw fun rf ws A => inv rf₀ ws₀ A₀ (i + 1) rf ws A) := by
        intro i hi
        have hb := ihb (base + 4) (pfx ++ lbl ++ ".body.")
          (fun rf ws A => inv rf₀ ws₀ A₀ i rf ws A ∧ c.holds rf)
          hOB (by omega) hcode_b hcallees hcalls
          (Stmt.vcs_antitone reg rw b _
            (fun rf ws A hr => ⟨rf₀, ws₀, A₀, hreach₀, i, hi, hr.1, hr.2⟩) hBodyVcs)
        have hjal := jal0_spec_pcFree (Stmt.jBack (b.size + 1))
          ((base + 4) + BitVec.ofNat 64 (4 * b.size))
          (pcFree_asrtR reg rw (Stmt.sp reg rw b
            fun rf ws A => inv rf₀ ws₀ A₀ i rf ws A ∧ c.holds rf))
        rw [hbodyEnd, add_jBack base (b.size + 1) (by omega) hofsBack] at hjal
        rw [← hbodyEnd] at hjal
        have hjal' := cpsTripleWithin_extend_code hcode_jal hjal
        have hseq := cpsTripleWithin_seq_same_cr hb hjal'
        exact cpsTripleWithin_weaken (fun _ hp => hp)
          (asrtR_mono (fun rf ws A hsp =>
            hInvStep rf₀ ws₀ A₀ hreach₀ i hi rf ws A hsp)) hseq
      have hcert : ∀ fuel' start, start + fuel' = fuel →
          WP.loopNatCert 1 (b.steps + 1) 1 base (base + 4)
            (base + BitVec.ofNat 64 (4 * (b.size + 2))) cr
            (fun i => asrtR reg rw fun rf ws A => inv rf₀ ws₀ A₀ i rf ws A)
            (fun i => asrtR reg rw fun rf ws A =>
              inv rf₀ ws₀ A₀ i rf ws A ∧ c.holds rf)
            (fun i => asrtR reg rw fun rf ws A =>
              inv rf₀ ws₀ A₀ i rf ws A ∧ ¬ c.holds rf)
            (asrtR reg rw fun rf ws A =>
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
                (asrtR reg rw fun rf ws A =>
                  inv rf₀ ws₀ A₀ start rf ws A ∧ ¬ c.holds rf)
                (asrtR reg rw fun rf ws A =>
                  (∃ i, i ≤ fuel ∧ inv rf₀ ws₀ A₀ i rf ws A) ∧ ¬ c.holds rf) :=
              cpsTripleWithin_entails (asrtR_mono (fun rf ws A hh =>
                ⟨⟨start, by omega, hh.1⟩, hh.2⟩))
            have hsf : start = fuel := by omega
            have hdead : cpsTripleWithin 0 (base + 4)
                (base + BitVec.ofNat 64 (4 * (b.size + 2))) cr
                (asrtR reg rw fun rf ws A =>
                  inv rf₀ ws₀ A₀ start rf ws A ∧ c.holds rf)
                (asrtR reg rw fun rf ws A =>
                  (∃ i, i ≤ fuel ∧ inv rf₀ ws₀ A₀ i rf ws A) ∧ ¬ c.holds rf) :=
              cpsTripleWithin_unreachable (asrtR_unsat (fun rf ws A hh =>
                hExhausted rf₀ ws₀ A₀ hreach₀ rf ws A (hsf ▸ hh.1) hh.2))
            exact cpsBranchWithin_merge_same_cr
              (cpsBranchWithin_swap
                (hheader (fun rf ws A => inv rf₀ ws₀ A₀ start rf ws A))) hdead hexit
        | succ fuel' ih =>
            intro start hstart
            refine ⟨cpsBranchWithin_swap
                (hheader (fun rf ws A => inv rf₀ ws₀ A₀ start rf ws A)),
              hbodyStep start (by omega), ?_, ih (start + 1) (by omega)⟩
            exact asrtR_mono (fun rf ws A hh => ⟨⟨start, by omega, hh.1⟩, hh.2⟩)
      have hsound := WP.loopNatCert_sound (hcert fuel 0 (by omega))
      refine cpsTripleWithin_weaken ?_ ?_ hsound
      · -- the fixed entry state enters the loop at invariant index 0
        intro hp hh
        have hh2 : (((((regFileIs rf₀) ** bytesRegion rw.base ws₀) ** A₀)
            ** bytesRegion reg.base reg.bytes) ** regOwn .x1) hp := by xperm_hyp hh
        exact sepConj_mono_left (sepConj_mono_left (fun hq hx =>
          ⟨rf₀, ws₀, A₀, hlen, hApc, hInvInit rf₀ ws₀ A₀ hreach₀, hx⟩)) hp hh2
      · -- the exit records the entry state alongside the invariant
        exact asrtR_mono (fun rf ws A hh => ⟨rf₀, ws₀, A₀, hreach₀, hh.1, hh.2⟩)
  | call lbl f =>
      obtain ⟨hoffset, halign, hnotself⟩ := hcalls
      obtain ⟨hcalleeCode, hregeq, hrweq⟩ := hcallees
      have hpreVC : ∀ rf ws A, reach rf ws A → f.pre rf ws A := hvcs _ (List.mem_singleton_self _)
      -- callee triple, retargeted at the aligned return address
      have hret' : cpsTripleWithin f.nSteps f.entry ((base + 4) &&& ~~~(1 : Word))
          f.code
          ((.x1 ↦ᵣ (base + 4)) ** asrtM reg rw f.pre)
          ((.x1 ↦ᵣ (base + 4)) ** asrtM reg rw f.post) := by
        rw [halign, ← hregeq, ← hrweq]
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
            ((asrtM reg rw f.pre) ** (.x1 ↦ᵣ vOld))
            ((asrtM reg rw (Stmt.sp reg rw (.call lbl f) reach)) ** regOwn .x1) := by
        intro vOld
        have h := WP.cpsCallWithin (vOld := vOld)
          (BitVec.setWidth 21 (f.entry - base)) hoffset halign
          (pcFree_asrtM reg rw f.pre) hdisj hret'
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
          (asrtR reg rw reach) (asrtR reg rw (Stmt.sp reg rw (.call lbl f) reach)) := by
        refine cpsTripleWithin_weaken
          (sepConj_mono_left (asrtM_mono (fun rf ws A hr => hpreVC rf ws A hr)))
          (fun _ hp => hp)
          (cpsTripleWithin_regOwn_right_pre hcall)
      simp only [Stmt.steps, Stmt.size, Nat.mul_one]
      have h4 : base + BitVec.ofNat 64 4 = base + 4 := rfl
      rw [h4]
      exact hfinal
  | callReg lbl rs handles =>
      obtain ⟨halignRet, hentries⟩ := hcalls
      have hrs : Reg.isExposed rs = true := hofs
      have hpreVC : ∀ rf ws A, reach rf ws A →
          ∃ h ∈ handles, rf.get rs = h.entry ∧ h.pre rf ws A :=
        hvcs _ (List.mem_singleton_self _)
      have hcodeJalr : ∀ a' i,
          CodeReq.singleton base (.JALR .x1 rs 0) a' = some i →
          cr a' = some i := by
        intro a' i h
        apply hcode a' i
        rw [show Stmt.flatten base (.callReg lbl rs handles)
          = [.JALR .x1 rs 0] from rfl, CodeReq.ofProg_singleton]
        exact h
      have hfinal : cpsTripleWithin
          (1 + handles.foldr (fun f m => max f.nSteps m) 0)
          base (base + 4) cr
          (asrtR reg rw reach)
          (asrtR reg rw (Stmt.sp reg rw (.callReg lbl rs handles) reach)) := by
        show cpsTripleWithin _ _ _ _ (asrtM reg rw reach ** regOwn .x1) _
        apply cpsTripleWithin_regOwn_right_pre
        intro vOld
        apply cpsTripleWithin_exists_pre_M_frame
        intro rf ws A hlen hApc hreach
        obtain ⟨h, hmem, hrsentry, hpre⟩ := hpreVC rf ws A hreach
        obtain ⟨hcalleeCode, hregeq, hrweq⟩ := hcallees h hmem
        have htarget : ((rf.get rs + signExtend12 (0 : BitVec 12))
            &&& ~~~(1 : Word)) = h.entry := by
          rw [hrsentry,
            show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
            show h.entry + (0 : Word) = h.entry from by bv_omega]
          exact hentries h hmem
        -- the jump
        have hjal := jalr_call_spec_within rs rf vOld base hrs
        rw [htarget] at hjal
        have hjalC := cpsTripleWithin_extend_code hcodeJalr hjal
        have hjalF := cpsTripleWithin_frameR
          ((bytesRegion rw.base ws ** A) ** bytesRegion reg.base reg.bytes)
          (pcFree_sepConj (pcFree_sepConj (bytesRegion_pcFree _ _) hApc)
            (bytesRegion_pcFree _ _))
          hjalC
        -- the callee, retargeted at the return address
        have hsound := h.sound (base + 4) halignRet
        rw [hregeq, hrweq] at hsound
        have hsoundC := cpsTripleWithin_extend_code hcalleeCode hsound
        -- glue the shapes
        have hjalW := cpsTripleWithin_weaken
          (P := (((.x1 : Reg) ↦ᵣ vOld) ** regFileIs rf) **
            ((bytesRegion rw.base ws ** A) ** bytesRegion reg.base reg.bytes))
          (P' := (((regFileIs rf) ** bytesRegion rw.base ws) ** A) **
            (bytesRegion reg.base reg.bytes ** ((.x1 : Reg) ↦ᵣ vOld)))
          (Q' := (((.x1 : Reg) ↦ᵣ (base + 4)) ** regFileIs rf) **
            ((bytesRegion rw.base ws ** A) ** bytesRegion reg.base reg.bytes))
          (fun hp hh => by
            rw [show ((((regFileIs rf) ** bytesRegion rw.base ws) ** A) **
                (bytesRegion reg.base reg.bytes ** ((.x1 : Reg) ↦ᵣ vOld)))
              = ((((.x1 : Reg) ↦ᵣ vOld) ** regFileIs rf) **
                ((bytesRegion rw.base ws ** A) ** bytesRegion reg.base reg.bytes))
              from by ac_rfl] at hh
            exact hh)
          (fun hp hh => hh)
          hjalF
        have hsoundW := cpsTripleWithin_weaken
          (P := ((.x1 : Reg) ↦ᵣ (base + 4)) ** asrtM reg rw h.pre)
          (P' := (((.x1 : Reg) ↦ᵣ (base + 4)) ** regFileIs rf) **
            ((bytesRegion rw.base ws ** A) ** bytesRegion reg.base reg.bytes))
          (Q' := asrtR reg rw (Stmt.sp reg rw (.callReg lbl rs handles) reach))
          (fun hp hh => by
            rw [show ((((.x1 : Reg) ↦ᵣ (base + 4)) ** regFileIs rf) **
                ((bytesRegion rw.base ws ** A) ** bytesRegion reg.base reg.bytes))
              = (((.x1 : Reg) ↦ᵣ (base + 4)) **
                ((((regFileIs rf) ** bytesRegion rw.base ws) ** A) **
                  bytesRegion reg.base reg.bytes))
              from by ac_rfl] at hh
            refine sepConj_mono_right (fun hq hx => ?_) hp hh
            show asrtM reg rw h.pre hq
            exact sepConj_mono_left
              (fun hv hy => ⟨rf, ws, A, hlen, hApc, hpre, hy⟩) hq hx)
          (fun hp hh => by
            rw [sepConj_comm'] at hh
            -- hh : (asrtM reg rw h.post ** ((.x1) ↦ᵣ (base + 4))) hp
            refine sepConj_mono_right
              (fun hq hx => (⟨base + 4, hx⟩ : regOwn .x1 hq)) hp ?_
            exact sepConj_mono_left
              (asrtM_mono (fun rf' ws' A' hp' => ⟨h, hmem, hp'⟩)) hp hh)
          hsoundC
        exact cpsTripleWithin_mono_nSteps
          (Nat.add_le_add_left (FnHandle.nSteps_le_foldr_max hmem) 1)
          (cpsTripleWithin_seq_same_cr hjalW hsoundW)
      simp only [Stmt.steps, Stmt.size, Nat.mul_one]
      have h4 : base + BitVec.ofNat 64 4 = base + 4 := rfl
      rw [h4]
      exact hfinal
  | callRegS lbl rs handles =>
      obtain ⟨halignRet, hentries⟩ := hcalls
      have hrs : Reg.isExposed rs = true := hofs
      have hpreVC : ∀ rf ws A, reach rf ws A →
          ∃ h ∈ handles, rf.get rs = h.entry ∧ h.pre rf ws A :=
        hvcs _ (List.mem_singleton_self _)
      have hcodeJalr : ∀ a' i,
          CodeReq.singleton base (.JALR .x1 rs 0) a' = some i →
          cr a' = some i := by
        intro a' i h
        apply hcode a' i
        rw [show Stmt.flatten base (.callRegS lbl rs handles)
          = [.JALR .x1 rs 0] from rfl, CodeReq.ofProg_singleton]
        exact h
      have hfinal : cpsTripleWithin
          (1 + handles.foldr (fun f m => max f.nSteps m) 0)
          base (base + 4) cr
          (asrtR reg rw reach)
          (asrtR reg rw (Stmt.sp reg rw (.callRegS lbl rs handles) reach)) := by
        show cpsTripleWithin _ _ _ _ (asrtM reg rw reach ** regOwn .x1) _
        apply cpsTripleWithin_regOwn_right_pre
        intro vOld
        apply cpsTripleWithin_exists_pre_M_frame
        intro rf ws A hlen hApc hreach
        obtain ⟨h, hmem, hrsentry, hpre⟩ := hpreVC rf ws A hreach
        obtain ⟨hcalleeCode, hregeq, hrweq⟩ := hcallees h hmem
        have htarget : ((rf.get rs + signExtend12 (0 : BitVec 12))
            &&& ~~~(1 : Word)) = h.entry := by
          rw [hrsentry,
            show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
            show h.entry + (0 : Word) = h.entry from by bv_omega]
          exact hentries h hmem
        -- the jump
        have hjal := jalr_call_spec_within rs rf vOld base hrs
        rw [htarget] at hjal
        have hjalC := cpsTripleWithin_extend_code hcodeJalr hjal
        have hjalF := cpsTripleWithin_frameR
          ((bytesRegion rw.base ws ** A) ** bytesRegion reg.base reg.bytes)
          (pcFree_sepConj (pcFree_sepConj (bytesRegion_pcFree _ _) hApc)
            (bytesRegion_pcFree _ _))
          hjalC
        -- the callee, retargeted at the return address and instantiated at
        -- THIS entry state (the snapshot that its post may depend on)
        have hsound := h.sound rf ws A (by rw [hrweq]; exact hlen) hApc hpre
          (base + 4) halignRet
        rw [hregeq, hrweq] at hsound
        have hsoundC := cpsTripleWithin_extend_code hcalleeCode hsound
        -- glue the shapes
        have hjalW := cpsTripleWithin_weaken
          (P := (((.x1 : Reg) ↦ᵣ vOld) ** regFileIs rf) **
            ((bytesRegion rw.base ws ** A) ** bytesRegion reg.base reg.bytes))
          (P' := (((regFileIs rf) ** bytesRegion rw.base ws) ** A) **
            (bytesRegion reg.base reg.bytes ** ((.x1 : Reg) ↦ᵣ vOld)))
          (Q' := (((.x1 : Reg) ↦ᵣ (base + 4)) ** regFileIs rf) **
            ((bytesRegion rw.base ws ** A) ** bytesRegion reg.base reg.bytes))
          (fun hp hh => by
            rw [show ((((regFileIs rf) ** bytesRegion rw.base ws) ** A) **
                (bytesRegion reg.base reg.bytes ** ((.x1 : Reg) ↦ᵣ vOld)))
              = ((((.x1 : Reg) ↦ᵣ vOld) ** regFileIs rf) **
                ((bytesRegion rw.base ws ** A) ** bytesRegion reg.base reg.bytes))
              from by ac_rfl] at hh
            exact hh)
          (fun hp hh => hh)
          hjalF
        have hsoundW := cpsTripleWithin_weaken
          (P := ((.x1 : Reg) ↦ᵣ (base + 4))
            ** asrtM reg rw (Reach.exact rf ws A))
          (P' := (((.x1 : Reg) ↦ᵣ (base + 4)) ** regFileIs rf) **
            ((bytesRegion rw.base ws ** A) ** bytesRegion reg.base reg.bytes))
          (Q' := asrtR reg rw (Stmt.sp reg rw (.callRegS lbl rs handles) reach))
          (fun hp hh => by
            rw [show ((((.x1 : Reg) ↦ᵣ (base + 4)) ** regFileIs rf) **
                ((bytesRegion rw.base ws ** A) ** bytesRegion reg.base reg.bytes))
              = (((.x1 : Reg) ↦ᵣ (base + 4)) **
                ((((regFileIs rf) ** bytesRegion rw.base ws) ** A) **
                  bytesRegion reg.base reg.bytes))
              from by ac_rfl] at hh
            refine sepConj_mono_right (fun hq hx => ?_) hp hh
            show asrtM reg rw (Reach.exact rf ws A) hq
            exact sepConj_mono_left
              (fun hv hy => ⟨rf, ws, A, hlen, hApc, ⟨rfl, rfl, rfl⟩, hy⟩) hq hx)
          (fun hp hh => by
            rw [sepConj_comm'] at hh
            -- hh : (asrtM reg rw (h.post rf ws A) ** ((.x1) ↦ᵣ (base + 4))) hp
            refine sepConj_mono_right
              (fun hq hx => (⟨base + 4, hx⟩ : regOwn .x1 hq)) hp ?_
            exact sepConj_mono_left
              (asrtM_mono (fun rf' ws' A' hp' =>
                ⟨rf, ws, A, hreach, h, hmem, hrsentry, hpre, hp'⟩)) hp hh)
          hsoundC
        exact cpsTripleWithin_mono_nSteps
          (Nat.add_le_add_left (FnHandleS.nSteps_le_foldr_max hmem) 1)
          (cpsTripleWithin_seq_same_cr hjalW hsoundW)
      simp only [Stmt.steps, Stmt.size, Nat.mul_one]
      have h4 : base + BitVec.ofNat 64 4 = base + 4 := rfl
      rw [h4]
      exact hfinal

end SAsm
end EvmAsm.Rv64
