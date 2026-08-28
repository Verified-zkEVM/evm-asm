/-
  Frame adapters for the architectural zero register.

  At the machine level x0 is vacuous: reads are definitionally zero and writes
  are no-ops.  The separation layer is finer than the machine layer,
  however: `regIs .x0 0` is still an ownable, exclusive singleton resource.
  It therefore cannot be dropped from a CPS precondition under an arbitrary
  frame.  The adapters below split that resource from the frame, synthesize it
  when the frame does not own it, and discard or reattach it at the post.
-/
import EvmAsm.Rv64.SAsm.MeasureLoop

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

def x0FreeAssertion (P : Assertion) : Prop :=
  ∀ h, P h → h.regs .x0 = none

private def dropX0 (h : PartialState) : PartialState where
  regs := fun r => if r == .x0 then none else h.regs r
  mem := h.mem
  code := h.code
  pc := h.pc
  publicValues := h.publicValues
  privateInput := h.privateInput
  inputBufBase := h.inputBufBase

private theorem dropX0_regs_x0 (h : PartialState) : (dropX0 h).regs .x0 = none := by
  simp [dropX0]

private theorem dropX0_disjoint_x0 (h : PartialState) :
    (dropX0 h).Disjoint (PartialState.singletonReg .x0 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    by_cases hr : r = .x0
    · subst hr; exact Or.inl (dropX0_regs_x0 h)
    · exact Or.inr (by simp [PartialState.singletonReg, hr])
  · intro a; exact Or.inr (by simp [PartialState.singletonReg])
  · intro a; exact Or.inr (by simp [PartialState.singletonReg])
  · exact Or.inr (by simp [PartialState.singletonReg])
  · exact Or.inr (by simp [PartialState.singletonReg])
  · exact Or.inr (by simp [PartialState.singletonReg])
  · exact Or.inr (by simp [PartialState.singletonReg])

private theorem x0_union_dropX0 (h : PartialState)
    (he : h.regs .x0 = some 0) :
    (PartialState.singletonReg .x0 0).union (dropX0 h) = h := by
  cases h with
  | mk regs mem code pc publicValues privateInput inputBufBase =>
    simp only [PartialState.union, dropX0, PartialState.singletonReg]
    simp only [PartialState.mk.injEq]
    constructor
    · funext r
      by_cases hr : r = .x0
      · subst hr; exact he.symm
      · simp [hr]
    · simp

private theorem dropX0_substate (h : PartialState) :
    (dropX0 h).SubStateOf h := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r v hv
    simp only [dropX0] at hv
    by_cases hr : r = .x0
    · subst hr; simp at hv
    · simpa [hr] using hv
  · intro a v hv; exact hv
  · intro a i hv; exact hv
  · intro v hv; exact hv
  · intro v hv; exact hv
  · intro v hv; exact hv
  · intro v hv; exact hv

private theorem x0_atom_compatible (s : MachineState) :
    (PartialState.singletonReg .x0 0).CompatibleWith s := by
  exact PartialState.CompatibleWith_singletonReg.mpr rfl

private theorem union_disjoint_right {h1 h2 h3 : PartialState}
    (hd13 : h1.Disjoint h3) (hd23 : h2.Disjoint h3) :
    (h1.union h2).Disjoint h3 := by
  obtain ⟨h1r, h1m, h1c, h1pc, h1pv, h1pi, h1ib⟩ := hd13
  obtain ⟨h2r, h2m, h2c, h2pc, h2pv, h2pi, h2ib⟩ := hd23
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    rcases h1r r with h1none | h3none
    · rcases h2r r with h2none | h3none
      · left; simp [PartialState.union, h1none, h2none]
      · exact Or.inr h3none
    · exact Or.inr h3none
  · intro a
    rcases h1m a with h1none | h3none
    · rcases h2m a with h2none | h3none
      · left; simp [PartialState.union, h1none, h2none]
      · exact Or.inr h3none
    · exact Or.inr h3none
  · intro a
    rcases h1c a with h1none | h3none
    · rcases h2c a with h2none | h3none
      · left; simp [PartialState.union, h1none, h2none]
      · exact Or.inr h3none
    · exact Or.inr h3none
  · rcases h1pc with h1none | h3none
    · rcases h2pc with h2none | h3none
      · left; simp [PartialState.union, h1none, h2none]
      · exact Or.inr h3none
    · exact Or.inr h3none
  · rcases h1pv with h1none | h3none
    · rcases h2pv with h2none | h3none
      · left; simp [PartialState.union, h1none, h2none]
      · exact Or.inr h3none
    · exact Or.inr h3none
  · rcases h1pi with h1none | h3none
    · rcases h2pi with h2none | h3none
      · left; simp [PartialState.union, h1none, h2none]
      · exact Or.inr h3none
    · exact Or.inr h3none
  · rcases h1ib with h1none | h3none
    · rcases h2ib with h2none | h3none
      · left; simp [PartialState.union, h1none, h2none]
      · exact Or.inr h3none
    · exact Or.inr h3none

private theorem substate_left_union (h1 h2 : PartialState) :
    h1.SubStateOf (h1.union h2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r v hv; simp [PartialState.union, hv]
  · intro a v hv; simp [PartialState.union, hv]
  · intro a i hv; simp [PartialState.union, hv]
  · intro v hv; simp [PartialState.union, hv]
  · intro v hv; simp [PartialState.union, hv]
  · intro v hv; simp [PartialState.union, hv]
  · intro v hv; simp [PartialState.union, hv]

private def exactAssertion (h : PartialState) : Assertion := fun h' => h' = h

private theorem exactAssertion_pcFree (h : PartialState) (hpc : h.pc = none) :
    (exactAssertion h).pcFree := by
  intro h' hh
  rw [hh]
  exact hpc

private theorem x0_disjoint_left_of_none {h : PartialState}
    (he : h.regs .x0 = none) :
    (PartialState.singletonReg .x0 0).Disjoint h := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    by_cases hr : r = .x0
    · subst hr; exact Or.inr he
    · exact Or.inl (by simp [PartialState.singletonReg, hr])
  · intro a; exact Or.inl (by simp [PartialState.singletonReg])
  · intro a; exact Or.inl (by simp [PartialState.singletonReg])
  · exact Or.inl (by simp [PartialState.singletonReg])
  · exact Or.inl (by simp [PartialState.singletonReg])
  · exact Or.inl (by simp [PartialState.singletonReg])
  · exact Or.inl (by simp [PartialState.singletonReg])

private theorem drop_x0_post
    {Q R : Assertion} {hF : PartialState} {s : MachineState}
    (hR : R hF)
    (hpost : ((Q ** regIs .x0 0) ** exactAssertion hF).holdsFor s) :
    (Q ** R).holdsFor s := by
  obtain ⟨htotal, hcompat, hassert⟩ := hpost
  obtain ⟨hq0, hf, hd, hun, hq0p, hfp⟩ := hassert
  change hf = hF at hfp
  subst hf
  obtain ⟨hq, h0, hd0, hun0, hqp, h0p⟩ := hq0p
  have hqsub : hq.SubStateOf hq0 := by
    rw [← hun0]
    exact substate_left_union hq h0
  have hqF : hq.Disjoint hF :=
    PartialState.SubStateOf_Disjoint hd hqsub
  rw [← hun] at hcompat
  have ⟨hcq0, hcf⟩ := (PartialState.CompatibleWith_union hd).mp hcompat
  rw [← hun0] at hcq0
  have ⟨hcq, _⟩ := (PartialState.CompatibleWith_union hd0).mp hcq0
  exact ⟨hq.union hF,
    (PartialState.CompatibleWith_union hqF).mpr ⟨hcq, hcf⟩,
    hq, hF, hqF, rfl, hqp, hR⟩

private theorem reattach_x0_post
    {Q R : Assertion} {hF hRest : PartialState} {s : MachineState}
    (hF_eq : (PartialState.singletonReg .x0 0).union hRest = hF)
    (hRest_x0 : hRest.regs .x0 = none)
    (hR : R hF)
    (hpost : ((Q ** regIs .x0 0) ** exactAssertion hRest).holdsFor s) :
    (Q ** R).holdsFor s := by
  obtain ⟨htotal, hcompat, hassert⟩ := hpost
  obtain ⟨hq0, hf, hd, hun, hq0p, hfp⟩ := hassert
  change hf = hRest at hfp
  subst hf
  obtain ⟨hq, h0, hd0, hun0, hqp, h0p⟩ := hq0p
  have h0_eq : h0 = PartialState.singletonReg .x0 0 := by
    simpa [regIs] using h0p
  subst h0
  have hqsub : hq.SubStateOf hq0 := by
    rw [← hun0]
    exact substate_left_union hq _
  have hqRest : hq.Disjoint hRest :=
    PartialState.SubStateOf_Disjoint hd hqsub
  have hqF : hq.Disjoint hF := by
    rw [← hF_eq]
    exact (union_disjoint_right hd0.symm hqRest.symm).symm
  rw [← hun] at hcompat
  have ⟨hcq0, hcrest⟩ := (PartialState.CompatibleWith_union hd).mp hcompat
  rw [← hun0] at hcq0
  have ⟨hcq, _⟩ := (PartialState.CompatibleWith_union hd0).mp hcq0
  have hcF : hF.CompatibleWith s := by
    rw [← hF_eq]
    exact (PartialState.CompatibleWith_union
      (x0_disjoint_left_of_none hRest_x0)).mpr
      ⟨x0_atom_compatible s, hcrest⟩
  exact ⟨hq.union hF,
    (PartialState.CompatibleWith_union hqF).mpr ⟨hcq, hcF⟩,
    hq, hF, hqF, rfl, hqp, hR⟩

private theorem cpsBranchWithin_drop_x0
    {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {P : Assertion} {exit_t : Word} {Q_t : Assertion}
    {exit_f : Word} {Q_f : Assertion}
    (hP_free : x0FreeAssertion P)
    (hbr : cpsBranchWithin nSteps entry cr
      (P ** regIs .x0 0) exit_t (Q_t ** regIs .x0 0)
        exit_f (Q_f ** regIs .x0 0)) :
    cpsBranchWithin nSteps entry cr P exit_t Q_t exit_f Q_f := by
  intro R hR s hcr hPR hpc
  obtain ⟨htotal, hcompat, hassert⟩ := hPR
  obtain ⟨hPstate, hFstate, hdPF, hun, hPp, hFp⟩ := hassert
  rw [← hun] at hcompat
  have ⟨hcP, hcF⟩ := (PartialState.CompatibleWith_union hdPF).mp hcompat
  cases hx : hFstate.regs .x0 with
  | none =>
      let h0 := PartialState.singletonReg .x0 0
      have hdP0 : hPstate.Disjoint h0 :=
        (x0_disjoint_left_of_none (hP_free hPstate hPp)).symm
      have hd0F : h0.Disjoint hFstate := x0_disjoint_left_of_none hx
      have hdP0F : (hPstate.union h0).Disjoint hFstate :=
        union_disjoint_right hdPF hd0F
      let R' : Assertion := exactAssertion hFstate
      have hR' : R'.pcFree := by
        exact exactAssertion_pcFree hFstate (hR hFstate hFp)
      have hcP0 : (hPstate.union h0).CompatibleWith s :=
        (PartialState.CompatibleWith_union hdP0).mpr
          ⟨hcP, x0_atom_compatible s⟩
      have hcTotal : ((hPstate.union h0).union hFstate).CompatibleWith s :=
        (PartialState.CompatibleWith_union hdP0F).mpr ⟨hcP0, hcF⟩
      have hP0 : (P ** regIs .x0 0) (hPstate.union h0) :=
        ⟨hPstate, h0, hdP0, rfl, hPp, rfl⟩
      have hIn : ((P ** regIs .x0 0) ** R')
          ((hPstate.union h0).union hFstate) :=
        ⟨hPstate.union h0, hFstate, hdP0F, rfl, hP0, rfl⟩
      obtain ⟨k, hk, s', hstep, hcase⟩ :=
        hbr R' hR' s hcr ⟨_, hcTotal, hIn⟩ hpc
      refine ⟨k, hk, s', hstep, ?_⟩
      rcases hcase with ⟨hpc_t, hpost_t⟩ | ⟨hpc_f, hpost_f⟩
      · exact Or.inl ⟨hpc_t, drop_x0_post hFp (by simpa [R'] using hpost_t)⟩
      · exact Or.inr ⟨hpc_f, drop_x0_post hFp (by simpa [R'] using hpost_f)⟩
  | some v =>
      have hv : v = 0 := by
        have hv' := hcF.1 .x0 v hx
        simpa [MachineState.getReg] using hv'.symm
      have hx0 : hFstate.regs .x0 = some 0 := by simpa [hv] using hx
      let hRest := dropX0 hFstate
      let h0 := PartialState.singletonReg .x0 0
      have hdP0 : hPstate.Disjoint h0 :=
        (x0_disjoint_left_of_none (hP_free hPstate hPp)).symm
      have hd0Rest : h0.Disjoint hRest :=
        (dropX0_disjoint_x0 hFstate).symm
      have hdRestP : hPstate.Disjoint hRest := by
        exact (PartialState.SubStateOf_Disjoint hdPF.symm
          (dropX0_substate hFstate)).symm
      have hdP0Rest : (hPstate.union h0).Disjoint hRest :=
        union_disjoint_right hdRestP hd0Rest
      have hcRest : hRest.CompatibleWith s :=
        PartialState.SubStateOf_CompatibleWith (dropX0_substate hFstate) hcF
      let R' : Assertion := exactAssertion hRest
      have hR' : R'.pcFree := by
        exact exactAssertion_pcFree hRest (by
          simpa [hRest, dropX0] using hR hFstate hFp)
      have hcP0 : (hPstate.union h0).CompatibleWith s :=
        (PartialState.CompatibleWith_union hdP0).mpr
          ⟨hcP, x0_atom_compatible s⟩
      have hcTotal : ((hPstate.union h0).union hRest).CompatibleWith s :=
        (PartialState.CompatibleWith_union hdP0Rest).mpr ⟨hcP0, hcRest⟩
      have hP0 : (P ** regIs .x0 0) (hPstate.union h0) :=
        ⟨hPstate, h0, hdP0, rfl, hPp, rfl⟩
      have hIn : ((P ** regIs .x0 0) ** R')
          ((hPstate.union h0).union hRest) :=
        ⟨hPstate.union h0, hRest, hdP0Rest, rfl, hP0, rfl⟩
      obtain ⟨k, hk, s', hstep, hcase⟩ :=
        hbr R' hR' s hcr ⟨_, hcTotal, hIn⟩ hpc
      refine ⟨k, hk, s', hstep, ?_⟩
      have hF_eq : h0.union hRest = hFstate := by
        exact x0_union_dropX0 hFstate hx0
      rcases hcase with ⟨hpc_t, hpost_t⟩ | ⟨hpc_f, hpost_f⟩
      · exact Or.inl ⟨hpc_t, reattach_x0_post hF_eq
          (by simpa [hRest] using dropX0_regs_x0 hFstate) hFp
          (by simpa [R'] using hpost_t)⟩
      · exact Or.inr ⟨hpc_f, reattach_x0_post hF_eq
          (by simpa [hRest] using dropX0_regs_x0 hFstate) hFp
          (by simpa [R'] using hpost_f)⟩

theorem cpsNBranchWithin_drop_x0
    {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {P : Assertion} {exits : List (Word × Assertion)}
    (hP_free : x0FreeAssertion P)
    (hbr : cpsNBranchWithin nSteps entry cr (P ** regIs .x0 0)
      (exits.map (fun ex => (ex.1, ex.2 ** regIs .x0 0)))) :
    cpsNBranchWithin nSteps entry cr P exits := by
  intro R hR s hcr hPR hpc
  obtain ⟨htotal, hcompat, hassert⟩ := hPR
  obtain ⟨hPstate, hFstate, hdPF, hun, hPp, hFp⟩ := hassert
  rw [← hun] at hcompat
  have ⟨hcP, hcF⟩ := (PartialState.CompatibleWith_union hdPF).mp hcompat
  cases hx : hFstate.regs .x0 with
  | none =>
      let h0 := PartialState.singletonReg .x0 0
      have hdP0 : hPstate.Disjoint h0 :=
        (x0_disjoint_left_of_none (hP_free hPstate hPp)).symm
      have hd0F : h0.Disjoint hFstate := x0_disjoint_left_of_none hx
      have hdP0F : (hPstate.union h0).Disjoint hFstate :=
        union_disjoint_right hdPF hd0F
      let R' : Assertion := exactAssertion hFstate
      have hR' : R'.pcFree := by
        exact exactAssertion_pcFree hFstate (hR hFstate hFp)
      have hcP0 : (hPstate.union h0).CompatibleWith s :=
        (PartialState.CompatibleWith_union hdP0).mpr
          ⟨hcP, x0_atom_compatible s⟩
      have hcTotal : ((hPstate.union h0).union hFstate).CompatibleWith s :=
        (PartialState.CompatibleWith_union hdP0F).mpr ⟨hcP0, hcF⟩
      have hP0 : (P ** regIs .x0 0) (hPstate.union h0) :=
        ⟨hPstate, h0, hdP0, rfl, hPp, rfl⟩
      have hIn : ((P ** regIs .x0 0) ** R')
          ((hPstate.union h0).union hFstate) :=
        ⟨hPstate.union h0, hFstate, hdP0F, rfl, hP0, rfl⟩
      obtain ⟨k, hk, s', hstep, ex, he, hpc', hpost⟩ :=
        hbr R' hR' s hcr ⟨_, hcTotal, hIn⟩ hpc
      rcases List.mem_map.mp he with ⟨ex0, hex0, rfl⟩
      refine ⟨k, hk, s', hstep, ex0, hex0, hpc', ?_⟩
      exact drop_x0_post hFp (by simpa [R'] using hpost)
  | some v =>
      have hv : v = 0 := by
        have hv' := hcF.1 .x0 v hx
        simpa [MachineState.getReg] using hv'.symm
      have hx0 : hFstate.regs .x0 = some 0 := by simpa [hv] using hx
      let hRest := dropX0 hFstate
      let h0 := PartialState.singletonReg .x0 0
      have hdP0 : hPstate.Disjoint h0 :=
        (x0_disjoint_left_of_none (hP_free hPstate hPp)).symm
      have hd0Rest : h0.Disjoint hRest :=
        (dropX0_disjoint_x0 hFstate).symm
      have hdRestP : hPstate.Disjoint hRest := by
        exact (PartialState.SubStateOf_Disjoint hdPF.symm
          (dropX0_substate hFstate)).symm
      have hdP0Rest : (hPstate.union h0).Disjoint hRest :=
        union_disjoint_right hdRestP hd0Rest
      have hcRest : hRest.CompatibleWith s :=
        PartialState.SubStateOf_CompatibleWith (dropX0_substate hFstate) hcF
      let R' : Assertion := exactAssertion hRest
      have hR' : R'.pcFree := by
        exact exactAssertion_pcFree hRest (by
          simpa [hRest, dropX0] using hR hFstate hFp)
      have hcP0 : (hPstate.union h0).CompatibleWith s :=
        (PartialState.CompatibleWith_union hdP0).mpr
          ⟨hcP, x0_atom_compatible s⟩
      have hcTotal : ((hPstate.union h0).union hRest).CompatibleWith s :=
        (PartialState.CompatibleWith_union hdP0Rest).mpr ⟨hcP0, hcRest⟩
      have hP0 : (P ** regIs .x0 0) (hPstate.union h0) :=
        ⟨hPstate, h0, hdP0, rfl, hPp, rfl⟩
      have hIn : ((P ** regIs .x0 0) ** R')
          ((hPstate.union h0).union hRest) :=
        ⟨hPstate.union h0, hRest, hdP0Rest, rfl, hP0, rfl⟩
      obtain ⟨k, hk, s', hstep, ex, he, hpc', hpost⟩ :=
        hbr R' hR' s hcr ⟨_, hcTotal, hIn⟩ hpc
      rcases List.mem_map.mp he with ⟨ex0, hex0, rfl⟩
      refine ⟨k, hk, s', hstep, ex0, hex0, hpc', ?_⟩
      have hF_eq : h0.union hRest = hFstate := by
        exact x0_union_dropX0 hFstate hx0
      exact reattach_x0_post hF_eq
        (by simpa [hRest] using dropX0_regs_x0 hFstate) hFp
        (by simpa [R'] using hpost)

end EvmAsm.Rv64.SAsm
