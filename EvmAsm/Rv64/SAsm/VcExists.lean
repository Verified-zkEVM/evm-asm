/-
  EvmAsm.Rv64.SAsm.VcExists

  Existential commutation lemmas for the SAsm VC generator, supporting the
  proof-first derivation layer (`EvmAsm.Rv64.SAsm.Deriv`):

  - `Stmt.sp_exists`: the strongest-postcondition transformer commutes with
    existentials over any nonempty index — `sp s (∃ x, R x) ⊢ ∃ x, sp s (R x)`.
  - `Stmt.vcs_exists`: obligations proven for each member of an indexed
    family of reachable sets cover their union — the dual of
    `Stmt.vcs_antitone`, needed to instantiate a loop-body derivation
    (given per-iteration) at the ∃i-union reach the VC generator emits.

  Both are plain structural inductions over the AST, mirroring
  `sp_mono`/`vcs_antitone` in Vc.lean.
-/

import EvmAsm.Rv64.SAsm.Vc

namespace EvmAsm.Rv64
namespace SAsm
namespace Stmt

/-- `sp` commutes with existentials over a nonempty index: a strongest
    postcondition reached from a union of entry sets is reached from one
    of its members.  (Nonemptiness is needed because loop/call nodes'
    `sp` ignores the entry reach entirely.) -/
theorem sp_exists (reg : Region) (rw : RwRegion) (s : Stmt)
    {ι : Sort*} [hι : Nonempty ι] (R : ι → Reach) :
    ∀ rf ws A, sp reg rw s (fun rf ws A => ∃ x, R x rf ws A) rf ws A →
      ∃ x, sp reg rw s (R x) rf ws A := by
  induction s generalizing R with
  | block lbl is =>
      rintro rf ws A ⟨rf₀, ws₀, hlen, ⟨x, hr⟩, hrf, hws⟩
      exact ⟨x, rf₀, ws₀, hlen, hr, hrf, hws⟩
  | blockA lbl a is =>
      rintro rf ws A ⟨rf₀, ws₀, hlen, ⟨x, hr⟩, hrf, hws⟩
      exact ⟨x, rf₀, ws₀, hlen, hr, hrf, hws⟩
  | seq a b iha ihb =>
      intro rf ws A hsp
      exact ihb (fun x => sp reg rw a (R x)) rf ws A
        (sp_mono reg rw b (iha R) rf ws A hsp)
  | ite lbl c t e iht ihe =>
      rintro rf ws A (ht | he)
      · rcases iht (fun x rf ws A => R x rf ws A ∧ c.holds rf) rf ws A
          (sp_mono reg rw t
            (fun rf ws A h => h.1.elim fun x hx => ⟨x, hx, h.2⟩) rf ws A ht)
          with ⟨x, hx⟩
        exact ⟨x, Or.inl hx⟩
      · rcases ihe (fun x rf ws A => R x rf ws A ∧ ¬ c.holds rf) rf ws A
          (sp_mono reg rw e
            (fun rf ws A h => h.1.elim fun x hx => ⟨x, hx, h.2⟩) rf ws A he)
          with ⟨x, hx⟩
        exact ⟨x, Or.inr hx⟩
  | «when» lbl c b ihb =>
      rintro rf ws A (hb | ⟨⟨x, hr⟩, hn⟩)
      · rcases ihb (fun x rf ws A => R x rf ws A ∧ c.holds rf) rf ws A
          (sp_mono reg rw b
            (fun rf ws A h => h.1.elim fun x hx => ⟨x, hx, h.2⟩) rf ws A hb)
          with ⟨x, hx⟩
        exact ⟨x, Or.inl hx⟩
      · exact ⟨x, Or.inr ⟨hr, hn⟩⟩
  | assert lbl P =>
      rintro rf ws A ⟨⟨x, hr⟩, hP⟩
      exact ⟨x, hr, hP⟩
  | ghost lbl Rr =>
      rintro rf ws A' ⟨A, ⟨x, hr⟩, hsat, hR⟩
      exact ⟨x, A, hr, hsat, hR⟩
  | blockAt lbl p winR is =>
      rintro rf' ws' A'' ⟨rf, A, win, rest, hlen, ⟨x, hr⟩, hsat, hR, hrf, hA⟩
      exact ⟨x, rf, A, win, rest, hlen, hr, hsat, hR, hrf, hA⟩
  | readAt lbl p roR is =>
      rintro rf' ws' A'' ⟨rf, ws, A, robytes, rest, hlen, ⟨x, hr⟩, hsat, hR,
        hrf, hws, hA⟩
      exact ⟨x, rf, ws, A, robytes, rest, hlen, hr, hsat, hR, hrf, hws, hA⟩
  | «while» lbl c fuel inv b ihb =>
      exact fun rf ws A hsp => hι.elim fun x => ⟨x, hsp⟩
  | whileHeader lbl h c fuel inv b ihh ihb =>
      exact fun rf ws A hsp => hι.elim fun x => ⟨x, hsp⟩
  | «whileS» lbl c fuel inv b ihb =>
      rintro rf ws A ⟨rf₀, ws₀, A₀, ⟨x, hr⟩, hrest⟩
      exact ⟨x, rf₀, ws₀, A₀, hr, hrest⟩
  | «whileBreak» lbl guard fuel inv post bb breakCond ba ihbb ihba =>
      exact fun rf ws A hsp => hι.elim fun x => ⟨x, hsp⟩
  | while2BreakJoin lbl guard fuel inv post before breakA breakB step selA selB ihBefore ihStep ihSelA ihSelB =>
      exact fun rf ws A hsp => hι.elim fun x => ⟨x, hsp⟩
  | «doWhileBreak» lbl fuel inv post bb breakCond ba ihbb ihba =>
      exact fun rf ws A hsp => hι.elim fun x => ⟨x, hsp⟩
  | «doWhile» lbl c fuel inv b ihb =>
      exact fun rf ws A hsp => hι.elim fun x => ⟨x, hsp⟩
  | «doWhileS» lbl c fuel inv b ihb =>
      rintro rf ws A ⟨rf₀, ws₀, A₀, ⟨x, hr⟩, hrest⟩
      exact ⟨x, rf₀, ws₀, A₀, hr, hrest⟩
  | «retWhileBreak» lbl guard fuel inv bb breakCond ba gt bt ihbb ihba ihgt ihbt =>
      exact fun rf ws A hsp => hι.elim fun x => ⟨x, hsp⟩
  | call lbl f =>
      exact fun rf ws A hsp => hι.elim fun x => ⟨x, hsp⟩
  | callReg lbl rs handles =>
      exact fun rf ws A hsp => hι.elim fun x => ⟨x, hsp⟩
  | callRegS lbl rs handles =>
      rintro rf ws A ⟨rf₀, ws₀, A₀, ⟨x, hr⟩, hrest⟩
      exact ⟨x, rf₀, ws₀, A₀, hr, hrest⟩
  | callAt lbl roR f =>
      rintro rf' ws' A'' ⟨rf, ws, A, rest, hlen, ⟨x, hr⟩, hsat, hR, hpost, hA⟩
      exact ⟨x, rf, ws, A, rest, hlen, hr, hsat, hR, hpost, hA⟩
  | retJalr lbl =>
      rintro rf ws A ⟨x, hr⟩
      exact ⟨x, hr⟩
  | retIf lbl c t e iht ihe =>
      rintro rf ws A (ht | he)
      · rcases iht (fun x rf ws A => R x rf ws A ∧ c.holds rf) rf ws A
          (sp_mono reg rw t
            (fun rf ws A h => h.1.elim fun x hx => ⟨x, hx, h.2⟩) rf ws A ht)
          with ⟨x, hx⟩
        exact ⟨x, Or.inl hx⟩
      · rcases ihe (fun x rf ws A => R x rf ws A ∧ ¬ c.holds rf) rf ws A
          (sp_mono reg rw e
            (fun rf ws A h => h.1.elim fun x hx => ⟨x, hx, h.2⟩) rf ws A he)
          with ⟨x, hx⟩
        exact ⟨x, Or.inr hx⟩

/-- `vcs` covers unions: obligations proven for every member of an indexed
    family of entry reaches also hold for the ∃-union reach.  This is how a
    per-iteration loop-body derivation (index `i : Nat`) discharges the body
    VCs the generator emits at the union over iterations.  (Nonemptiness is
    needed for the reach-independent obligations, e.g. `blockOk`.) -/
theorem vcs_exists (reg : Region) (rw : RwRegion) (s : Stmt)
    {ι : Sort*} [hι : Nonempty ι] (pfx : String) (R : ι → Reach)
    (h : ∀ x, VCs.Hold (vcs reg rw s pfx (R x))) :
    VCs.Hold (vcs reg rw s pfx (fun rf ws A => ∃ x, R x rf ws A)) := by
  induction s generalizing pfx R with
  | block lbl is =>
      by_cases hl : hasLoad is
      · simp only [vcs, if_pos hl] at h ⊢
        refine VCs.Hold.cons_intro (hι.elim fun x => (h x).head)
          (VCs.Hold.cons_intro ?_ VCs.Hold.nil)
        rintro rf ws A hlen ⟨x, hr⟩
        exact (h x).tail.head rf ws A hlen hr
      · simp only [vcs, if_neg hl] at h ⊢
        exact VCs.Hold.cons_intro (hι.elim fun x => (h x).head) VCs.Hold.nil
  | blockA lbl a is =>
      by_cases hl : hasLoad is
      · simp only [vcs, if_pos hl] at h ⊢
        refine VCs.Hold.cons_intro (hι.elim fun x => (h x).head)
          (VCs.Hold.cons_intro ?_ VCs.Hold.nil)
        rintro rf ws A hlen ⟨x, hr⟩
        exact (h x).tail.head rf ws A hlen hr
      · simp only [vcs, if_neg hl] at h ⊢
        exact VCs.Hold.cons_intro (hι.elim fun x => (h x).head) VCs.Hold.nil
  | seq a b iha ihb =>
      refine VCs.Hold.append_intro (iha pfx R fun x => (h x).left) ?_
      exact vcs_antitone reg rw b pfx (sp_exists reg rw a R)
        (ihb pfx (fun x => sp reg rw a (R x)) fun x => (h x).right)
  | ite lbl c t e iht ihe =>
      refine VCs.Hold.append_intro ?_ ?_
      · exact vcs_antitone reg rw t _
          (fun rf ws A hr => hr.1.elim fun x hx => ⟨x, hx, hr.2⟩)
          (iht _ (fun x rf ws A => R x rf ws A ∧ c.holds rf)
            fun x => (h x).left)
      · exact vcs_antitone reg rw e _
          (fun rf ws A hr => hr.1.elim fun x hx => ⟨x, hx, hr.2⟩)
          (ihe _ (fun x rf ws A => R x rf ws A ∧ ¬ c.holds rf)
            fun x => (h x).right)
  | «when» lbl c b ihb =>
      exact vcs_antitone reg rw b _
        (fun rf ws A hr => hr.1.elim fun x hx => ⟨x, hx, hr.2⟩)
        (ihb _ (fun x rf ws A => R x rf ws A ∧ c.holds rf) fun x => h x)
  | assert lbl P =>
      refine VCs.Hold.cons_intro ?_ VCs.Hold.nil
      rintro rf ws A ⟨x, hr⟩
      exact (h x).head rf ws A hr
  | ghost lbl Rr =>
      refine VCs.Hold.cons_intro ?_ VCs.Hold.nil
      rintro rf ws A ⟨x, hr⟩
      exact (h x).head rf ws A hr
  | blockAt lbl p winR is =>
      by_cases hl : hasLoad is
      · simp only [vcs, if_pos hl] at h ⊢
        refine VCs.Hold.cons_intro (hι.elim fun x => (h x).head)
          (VCs.Hold.cons_intro ?_ (VCs.Hold.cons_intro ?_ VCs.Hold.nil))
        · rintro rf ws A ⟨x, hr⟩
          exact (h x).tail.head rf ws A hr
        · rintro rf ws A win rest hlen ⟨x, hr⟩
          exact (h x).tail.tail.head rf ws A win rest hlen hr
      · simp only [vcs, if_neg hl] at h ⊢
        refine VCs.Hold.cons_intro (hι.elim fun x => (h x).head)
          (VCs.Hold.cons_intro ?_ VCs.Hold.nil)
        rintro rf ws A ⟨x, hr⟩
        exact (h x).tail.head rf ws A hr
  | readAt lbl p roR is =>
      by_cases hl : hasLoad is
      · simp only [vcs, if_pos hl] at h ⊢
        refine VCs.Hold.cons_intro (hι.elim fun x => (h x).head)
          (VCs.Hold.cons_intro ?_ (VCs.Hold.cons_intro ?_ VCs.Hold.nil))
        · rintro rf ws A ⟨x, hr⟩
          exact (h x).tail.head rf ws A hr
        · rintro rf ws A robytes rest hlen ⟨x, hr⟩
          exact (h x).tail.tail.head rf ws A robytes rest hlen hr
      · simp only [vcs, if_neg hl] at h ⊢
        refine VCs.Hold.cons_intro (hι.elim fun x => (h x).head)
          (VCs.Hold.cons_intro ?_ VCs.Hold.nil)
        rintro rf ws A ⟨x, hr⟩
        exact (h x).tail.head rf ws A hr
  | «while» lbl c fuel inv b ihb =>
      refine VCs.Hold.cons_intro ?_ (VCs.Hold.cons_intro
        (hι.elim fun x => (h x).tail.head)
        (VCs.Hold.cons_intro (hι.elim fun x => (h x).tail.tail.head)
          (hι.elim fun x => (h x).tail.tail.tail)))
      rintro rf ws A ⟨x, hr⟩
      exact (h x).head rf ws A hr
  | whileHeader lbl hd c fuel inv b ihh ihb =>
      refine VCs.Hold.cons_intro ?_ (VCs.Hold.cons_intro
        (hι.elim fun x => (h x).tail.head)
        (VCs.Hold.cons_intro (hι.elim fun x => (h x).tail.tail.head)
          (VCs.Hold.append_intro ?_
            (hι.elim fun x => (h x).tail.tail.tail.right))))
      · intro rf ws A hsp
        rcases sp_exists reg rw hd R rf ws A hsp with ⟨x, hx⟩
        exact (h x).head rf ws A hx
      · refine vcs_antitone reg rw hd _
          (fun rf ws A hr => ?_)
          (ihh _ (fun x rf ws A => R x rf ws A ∨
            ∃ i, i < fuel ∧
              sp reg rw b (fun rf ws A => inv i rf ws A ∧ c.holds rf) rf ws A)
            fun x => (h x).tail.tail.tail.left)
        rcases hr with ⟨x, hr⟩ | hr
        · exact ⟨x, Or.inl hr⟩
        · exact hι.elim fun x => ⟨x, Or.inr hr⟩
  | «whileS» lbl c fuel inv b ihb =>
      refine VCs.Hold.cons_intro ?_ (VCs.Hold.cons_intro ?_
        (VCs.Hold.cons_intro ?_ ?_))
      · rintro rf ws A ⟨x, hr⟩
        exact (h x).head rf ws A hr
      · rintro rf₀ ws₀ A₀ ⟨x, hr⟩
        exact (h x).tail.head rf₀ ws₀ A₀ hr
      · rintro rf₀ ws₀ A₀ ⟨x, hr⟩
        exact (h x).tail.tail.head rf₀ ws₀ A₀ hr
      · refine vcs_antitone reg rw b _
          (fun rf ws A hr => ?_)
          (ihb _ (fun x rf ws A => ∃ rf₀ ws₀ A₀, R x rf₀ ws₀ A₀
            ∧ ∃ i, i < fuel ∧ inv rf₀ ws₀ A₀ i rf ws A ∧ c.holds rf)
            fun x => (h x).tail.tail.tail)
        rcases hr with ⟨rf₀, ws₀, A₀, ⟨x, hr⟩, hrest⟩
        exact ⟨x, rf₀, ws₀, A₀, hr, hrest⟩
  | «whileBreak» lbl guard fuel inv post bb breakCond ba ihbb ihba =>
      refine VCs.Hold.cons_intro ?_ (VCs.Hold.cons_intro
        (hι.elim fun x => (h x).tail.head)
        (VCs.Hold.cons_intro (hι.elim fun x => (h x).tail.tail.head)
          (VCs.Hold.cons_intro (hι.elim fun x => (h x).tail.tail.tail.head)
            (VCs.Hold.cons_intro
              (hι.elim fun x => (h x).tail.tail.tail.tail.head)
              (hι.elim fun x => (h x).tail.tail.tail.tail.tail)))))
      rintro rf ws A ⟨x, hr⟩
      exact (h x).head rf ws A hr
  | while2BreakJoin lbl guard fuel inv post before breakA breakB step selA selB ihBefore ihStep ihSelA ihSelB =>
      refine VCs.Hold.cons_intro ?_ (VCs.Hold.cons_intro
        (hι.elim fun x => (h x).tail.head)
        (VCs.Hold.cons_intro (hι.elim fun x => (h x).tail.tail.head)
          (VCs.Hold.cons_intro (hι.elim fun x => (h x).tail.tail.tail.head)
            (VCs.Hold.cons_intro
              (hι.elim fun x => (h x).tail.tail.tail.tail.head)
              (hι.elim fun x => (h x).tail.tail.tail.tail.tail)))))
      rintro rf ws A ⟨x, hr⟩
      exact (h x).head rf ws A hr
  | «doWhileBreak» lbl fuel inv post bb breakCond ba ihbb ihba =>
      refine VCs.Hold.cons_intro ?_ (VCs.Hold.cons_intro
        (hι.elim fun x => (h x).tail.head)
        (VCs.Hold.cons_intro (hι.elim fun x => (h x).tail.tail.head)
          (VCs.Hold.cons_intro (hι.elim fun x => (h x).tail.tail.tail.head)
            (hι.elim fun x => (h x).tail.tail.tail.tail))))
      rintro rf ws A ⟨x, hr⟩
      exact (h x).head rf ws A hr
  | «doWhile» lbl c fuel inv b ihb =>
      refine VCs.Hold.cons_intro ?_ (VCs.Hold.cons_intro
        (hι.elim fun x => (h x).tail.head)
        (VCs.Hold.cons_intro (hι.elim fun x => (h x).tail.tail.head) ?_))
      · intro rf ws A hsp
        rcases sp_exists reg rw b R rf ws A hsp with ⟨x, hx⟩
        exact (h x).head rf ws A hx
      · refine vcs_antitone reg rw b _
          (fun rf ws A hr => ?_)
          (ihb _ (fun x rf ws A => R x rf ws A ∨
            ∃ i, i < fuel ∧ inv i rf ws A ∧ c.holds rf)
            fun x => (h x).tail.tail.tail)
        rcases hr with ⟨x, hr⟩ | hr
        · exact ⟨x, Or.inl hr⟩
        · exact hι.elim fun x => ⟨x, Or.inr hr⟩
  | «doWhileS» lbl c fuel inv b ihb =>
      refine VCs.Hold.cons_intro ?_ (VCs.Hold.cons_intro ?_
        (VCs.Hold.cons_intro ?_ ?_))
      · rintro rf₀ ws₀ A₀ ⟨x, hr⟩
        exact (h x).head rf₀ ws₀ A₀ hr
      · rintro rf₀ ws₀ A₀ ⟨x, hr⟩
        exact (h x).tail.head rf₀ ws₀ A₀ hr
      · rintro rf₀ ws₀ A₀ ⟨x, hr⟩
        exact (h x).tail.tail.head rf₀ ws₀ A₀ hr
      · refine vcs_antitone reg rw b _
          (fun rf ws A hr => ?_)
          (ihb _ (fun x rf ws A => R x rf ws A ∨
            ∃ rf₀ ws₀ A₀, R x rf₀ ws₀ A₀
              ∧ ∃ i, i < fuel ∧ inv rf₀ ws₀ A₀ i rf ws A ∧ c.holds rf)
            fun x => (h x).tail.tail.tail)
        rcases hr with ⟨x, hr⟩ | ⟨rf₀, ws₀, A₀, ⟨x, hr⟩, hrest⟩
        · exact ⟨x, Or.inl hr⟩
        · exact ⟨x, Or.inr ⟨rf₀, ws₀, A₀, hr, hrest⟩⟩
  | «retWhileBreak» lbl guard fuel inv bb breakCond ba gt bt ihbb ihba ihgt ihbt =>
      refine VCs.Hold.cons_intro ?_ (VCs.Hold.cons_intro
        (hι.elim fun x => (h x).tail.head)
        (VCs.Hold.cons_intro (hι.elim fun x => (h x).tail.tail.head)
          (hι.elim fun x => (h x).tail.tail.tail)))
      rintro rf ws A ⟨x, hr⟩
      exact (h x).head rf ws A hr
  | call lbl f =>
      refine VCs.Hold.cons_intro ?_ VCs.Hold.nil
      rintro rf ws A ⟨x, hr⟩
      exact (h x).head rf ws A hr
  | callReg lbl rs handles =>
      refine VCs.Hold.cons_intro ?_ VCs.Hold.nil
      rintro rf ws A ⟨x, hr⟩
      exact (h x).head rf ws A hr
  | callRegS lbl rs handles =>
      refine VCs.Hold.cons_intro ?_ VCs.Hold.nil
      rintro rf ws A ⟨x, hr⟩
      exact (h x).head rf ws A hr
  | callAt lbl roR f =>
      refine VCs.Hold.cons_intro ?_ (VCs.Hold.cons_intro ?_
        (VCs.Hold.cons_intro (hι.elim fun x => (h x).tail.tail.head)
          VCs.Hold.nil))
      · rintro rf ws A ⟨x, hr⟩
        exact (h x).head rf ws A hr
      · rintro rf ws A rest hlen ⟨x, hr⟩
        exact (h x).tail.head rf ws A rest hlen hr
  | retJalr lbl =>
      exact VCs.Hold.nil
  | retIf lbl c t e iht ihe =>
      refine VCs.Hold.append_intro ?_ ?_
      · exact vcs_antitone reg rw t _
          (fun rf ws A hr => hr.1.elim fun x hx => ⟨x, hx, hr.2⟩)
          (iht _ (fun x rf ws A => R x rf ws A ∧ c.holds rf)
            fun x => (h x).left)
      · exact vcs_antitone reg rw e _
          (fun rf ws A hr => hr.1.elim fun x hx => ⟨x, hx, hr.2⟩)
          (ihe _ (fun x rf ws A => R x rf ws A ∧ ¬ c.holds rf)
            fun x => (h x).right)

end Stmt
end SAsm
end EvmAsm.Rv64
