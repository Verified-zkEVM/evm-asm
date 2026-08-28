/- Composition adapter for the K70 exit-divide and output tail windows. -/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody6Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody8Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14TerminalSpec

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen
open EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell
open EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody5Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody6Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody7Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody10Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14TerminalSpec

set_option maxRecDepth 8000

@[reducible] def exitdivOutputCells
    (outPtr o0 o1 o2 o3 : Word) : Assertion :=
  ((outPtr + BitVec.ofNat 64 0) ↦ₘ o0) **
    ((outPtr + BitVec.ofNat 64 8) ↦ₘ o1) **
      ((outPtr + BitVec.ofNat 64 16) ↦ₘ o2) **
        ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3)

@[reducible] def exitdivPre
    (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v5 v6 v7 v19 v20 v28 v29 v30 v31 : Word) (FR : Assertion) : Assertion :=
  (.x2 ↦ᵣ newSp) **
    (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) **
        (.x11 ↦ᵣ outPtr) **
          (.x8 ↦ᵣ excess) **
            (.x9 ↦ᵣ taylorDW) **
              (.x18 ↦ᵣ iVal) **
                (.x19 ↦ᵣ v19) **
                  (.x20 ↦ᵣ v20) **
                    (.x21 ↦ᵣ outPtr) **
                      (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
                        (.x0 ↦ᵣ (0 : Word)) **
                          (.x5 ↦ᵣ v5) **
                            (.x6 ↦ᵣ v6) **
                              (.x7 ↦ᵣ v7) **
                                (.x28 ↦ᵣ v28) **
                                  (.x29 ↦ᵣ v29) **
                                    (.x30 ↦ᵣ v30) **
                                      (.x31 ↦ᵣ v31) **
                                        frameSlotsSaved priceFrame newSp vals **
                                          (((newSp + signExtend12 (64 : BitVec 12)) +
                                              signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
                                            (((newSp + signExtend12 (64 : BitVec 12)) +
                                                signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
                                              (((newSp + signExtend12 (64 : BitVec 12)) +
                                                  signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
                                                (((newSp + signExtend12 (64 : BitVec 12)) +
                                                    signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
                                                  (((newSp + signExtend12 (64 : BitVec 12)) +
                                                      signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
                                                    (((newSp + signExtend12 (64 : BitVec 12)) +
                                                        signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
                                                      (((newSp + signExtend12 (112 : BitVec 12)) +
                                                          signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
                                                        (((newSp + signExtend12 (112 : BitVec 12)) +
                                                            signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
                                                          (((newSp + signExtend12 (112 : BitVec 12)) +
                                                              signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
                                                            (((newSp + signExtend12 (112 : BitVec 12)) +
                                                                signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
                                                              (((newSp + signExtend12 (112 : BitVec 12)) +
                                                                  signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
                                                                (((newSp + signExtend12 (112 : BitVec 12)) +
                                                                    signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
                                                                  (((newSp + signExtend12 (160 : BitVec 12)) +
                                                                      signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
                                                                    (((newSp + signExtend12 (160 : BitVec 12)) +
                                                                        signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
                                                                      (((newSp + signExtend12 (160 : BitVec 12)) +
                                                                          signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
                                                                        (((newSp + signExtend12 (160 : BitVec 12)) +
                                                                            signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
                                                                          (((newSp + signExtend12 (160 : BitVec 12)) +
                                                                              signExtend12 (32 : BitVec 12)) ↦ₘ s4) **
                                                                            (((newSp + signExtend12 (160 : BitVec 12)) +
                                                                                signExtend12 (40 : BitVec 12)) ↦ₘ s5) ** FR

@[reducible] def exitdivZ5 (s5 : Word) : Word × Word × Word :=
  divst taylorDW (0 : Word) s5 (0 : Word) 64

@[reducible] def exitdivZ4 (s4 s5 : Word) : Word × Word × Word :=
  divst taylorDW (exitdivZ5 s5).1 s4 (0 : Word) 64

@[reducible] def exitdivZ3 (s3 s4 s5 : Word) : Word × Word × Word :=
  divst taylorDW (exitdivZ4 s4 s5).1 s3 (0 : Word) 64

@[reducible] def exitdivZ2 (s2 s3 s4 s5 : Word) : Word × Word × Word :=
  divst taylorDW (exitdivZ3 s3 s4 s5).1 s2 (0 : Word) 64

@[reducible] def exitdivZ1 (s1 s2 s3 s4 s5 : Word) : Word × Word × Word :=
  divst taylorDW (exitdivZ2 s2 s3 s4 s5).1 s1 (0 : Word) 64

@[reducible] def exitdivZ0
    (s0 s1 s2 s3 s4 s5 : Word) : Word × Word × Word :=
  divst taylorDW (exitdivZ1 s1 s2 s3 s4 s5).1 s0 (0 : Word) 64

@[reducible] def exitdivQ0
    (s0 s1 s2 s3 s4 s5 : Word) : Word :=
  (exitdivZ0 s0 s1 s2 s3 s4 s5).2.2

@[reducible] def exitdivQ1
    (_s0 s1 s2 s3 s4 s5 : Word) : Word :=
  (exitdivZ1 s1 s2 s3 s4 s5).2.2

@[reducible] def exitdivQ2
    (_s0 _s1 s2 s3 s4 s5 : Word) : Word :=
  (exitdivZ2 s2 s3 s4 s5).2.2

@[reducible] def exitdivQ3
    (_s0 _s1 _s2 s3 s4 s5 : Word) : Word :=
  (exitdivZ3 s3 s4 s5).2.2

@[reducible] def exitdivQ4
    (_s0 _s1 _s2 _s3 s4 s5 : Word) : Word :=
  (exitdivZ4 s4 s5).2.2

@[reducible] def exitdivQ5
    (_s0 _s1 _s2 _s3 _s4 s5 : Word) : Word :=
  (exitdivZ5 s5).2.2

@[reducible] def tailCorePre
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 : Word)
    (v5 v6 v7 v18 v19 v20 v28 v29 v30 v31 : Word)
    (FR : Assertion) : Assertion :=
  (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ q4) **
    (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ q5) **
      (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
          (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
            (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
              (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ outPtr) **
                (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
                  (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
                    (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
                      (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
                        frameSlotsSaved priceFrame newSp vals **
                          (((newSp + signExtend12 (64 : BitVec 12)) +
                              signExtend12 (0 : BitVec 12)) ↦ₘ a0) **
                            (((newSp + signExtend12 (64 : BitVec 12)) +
                                signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
                              (((newSp + signExtend12 (64 : BitVec 12)) +
                                  signExtend12 (16 : BitVec 12)) ↦ₘ a2) **
                                (((newSp + signExtend12 (64 : BitVec 12)) +
                                    signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
                                  (((newSp + signExtend12 (64 : BitVec 12)) +
                                      signExtend12 (32 : BitVec 12)) ↦ₘ a4) **
                                    (((newSp + signExtend12 (64 : BitVec 12)) +
                                        signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
                                      (((newSp + signExtend12 (112 : BitVec 12)) +
                                          signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
                                        (((newSp + signExtend12 (112 : BitVec 12)) +
                                            signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
                                          (((newSp + signExtend12 (112 : BitVec 12)) +
                                              signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
                                            (((newSp + signExtend12 (112 : BitVec 12)) +
                                                signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
                                              (((newSp + signExtend12 (112 : BitVec 12)) +
                                                  signExtend12 (32 : BitVec 12)) ↦ₘ p4) **
                                                (((newSp + signExtend12 (112 : BitVec 12)) +
                                                    signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
                                                  (((newSp + signExtend12 (160 : BitVec 12)) +
                                                      BitVec.ofNat 64 0) ↦ₘ q0) **
                                                    (((newSp + signExtend12 (160 : BitVec 12)) +
                                                        BitVec.ofNat 64 8) ↦ₘ q1) **
                                                      (((newSp + signExtend12 (160 : BitVec 12)) +
                                                          BitVec.ofNat 64 16) ↦ₘ q2) **
                                                        (((newSp + signExtend12 (160 : BitVec 12)) +
                                                            BitVec.ofNat 64 24) ↦ₘ q3) **
                                                          ((outPtr + BitVec.ofNat 64 0) ↦ₘ o0) **
                                                            ((outPtr + BitVec.ofNat 64 8) ↦ₘ o1) **
                                                              ((outPtr + BitVec.ofNat 64 16) ↦ₘ o2) **
                                                                ((outPtr + BitVec.ofNat 64 24) ↦ₘ o3) ** FR

@[reducible] def exitdivTailPre
    (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 v19 v20 : Word) (FR : Assertion) : Assertion :=
  tailCorePre newSp excess outPtr vals
    (exitdivQ0 s0 s1 s2 s3 s4 s5) (exitdivQ1 s0 s1 s2 s3 s4 s5)
    (exitdivQ2 s0 s1 s2 s3 s4 s5) (exitdivQ3 s0 s1 s2 s3 s4 s5)
    (exitdivQ4 s0 s1 s2 s3 s4 s5) (exitdivQ5 s0 s1 s2 s3 s4 s5)
    o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
    taylorDW (exitdivZ0 s0 s1 s2 s3 s4 s5).1
    (exitdivZ0 s0 s1 s2 s3 s4 s5).2.1 iVal v19 v20
    (exitdivQ0 s0 s1 s2 s3 s4 s5) (0 : Word)
    (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) +
      signExtend12 (-8 : BitVec 12))
    (lcnt 5 + signExtend12 (-1 : BitVec 12)) FR

theorem exitdiv_seq_tail
    (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 v5 v6 v7 v19 v20 v28 v29 v30 v31 : Word)
    (FR : Assertion) (hFR : FR.pcFree)
    {exits : List (Word × Assertion)}
    (hTail : cpsNBranchWithin 296 (PriceK + 900) priceCode
      (exitdivTailPre newSp excess outPtr iVal vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        o0 o1 o2 o3 v19 v20 FR) exits) :
    cpsNBranchWithin 4183 (PriceK + 804) priceCode
      (exitdivPre newSp excess outPtr iVal vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v5 v6 v7 v19 v20 v28 v29 v30 v31
        (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) exits := by
  have hFR0 : (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR).pcFree := by
    pcFree
    exact hFR
  have hExit := exitdiv_core newSp excess outPtr iVal vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v5 v6 v7 v19 v20 v28 v29 v30 v31
    (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) hFR0
  have hSeq := cpsTripleWithin_seq_cpsNBranchWithin_perm_same_cr
    (hperm := by
      intro h hh
      simp only [exitdivTailPre, tailCorePre, exitdivOutputCells,
        exitdivZ0, exitdivZ1, exitdivZ2, exitdivZ3, exitdivZ4, exitdivZ5,
        exitdivQ0, exitdivQ1, exitdivQ2, exitdivQ3, exitdivQ4, exitdivQ5,
        EvmAsm.Rv64.AddrNorm.se12_0, EvmAsm.Rv64.AddrNorm.se12_8,
        EvmAsm.Rv64.AddrNorm.se12_16, EvmAsm.Rv64.AddrNorm.se12_24,
        EvmAsm.Rv64.AddrNorm.se12_32, EvmAsm.Rv64.AddrNorm.se12_40,
        EvmAsm.Rv64.AddrNorm.word_add_zero,
        show (BitVec.ofNat 64 0 : Word) = 0 by decide,
        show (BitVec.ofNat 64 8 : Word) = 8 by decide,
        show (BitVec.ofNat 64 16 : Word) = 16 by decide,
        show (BitVec.ofNat 64 24 : Word) = 24 by decide] at hh ⊢
      xperm_hyp hh)
    hExit hTail
  simpa [exitdivPre, exitdivOutputCells] using hSeq

/- Compose a continuation onto the head exit of an N-branch.  The original
   head is replaced by the continuation's exits; all later exits are retained
   in their original order. -/
theorem nb_extend_head_same_cr {n1 n2 : Nat} {entry mid : Word} {cr : CodeReq}
    {P Qm : Assertion} {rest exits2 : List (Word × Assertion)}
    (h1 : cpsNBranchWithin n1 entry cr P ((mid, Qm) :: rest))
    (h2 : cpsNBranchWithin n2 mid cr Qm exits2) :
    cpsNBranchWithin (n1 + n2) entry cr P (exits2 ++ rest) := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, ex, hmem, hpc1, hQ1⟩ :=
    h1 R hR s hcr hPR hpc
  simp only [List.mem_cons] at hmem
  rcases hmem with hhead | hrest
  · cases hhead
    have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, ex2, hmem2, hpc2, hQ2⟩ :=
      h2 R hR s1 hcr' hQ1 hpc1
    exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2,
      stepN_add_eq hstep1 hstep2, ex2,
      List.mem_append.mpr (Or.inl hmem2), hpc2, hQ2⟩
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right n1 n2), s1,
      hstep1, ex, List.mem_append.mpr (Or.inr hrest), hpc1, hQ1⟩

/- Compose a uniform continuation onto every exit of an N-branch.  The
   unchanged exits use the zero-step identity below, lifted to the common
   continuation bound; the selected exits may instead advance through the
   shared status tail. -/
private theorem cpsTripleWithin_refl_same_cr {addr : Word} {cr : CodeReq}
    {P Q : Assertion} (h : ∀ hp, P hp → Q hp) :
    cpsTripleWithin 0 addr addr cr P Q := by
  intro R hR s hcr hPR hpc
  exact ⟨0, Nat.le_refl 0, s, stepN_zero, hpc, by
    obtain ⟨hp, hcompat, hpq⟩ := hPR
    exact ⟨hp, hcompat, sepConj_mono_left h hp hpq⟩⟩

private theorem nb_extend_each_same_cr {n1 n2 : Nat} {entry : Word}
    {cr : CodeReq} {P : Assertion}
    {exits exits' : List (Word × Assertion)}
    (h1 : cpsNBranchWithin n1 entry cr P exits)
    (h2 : ∀ ex ∈ exits, ∃ ex' ∈ exits',
      cpsTripleWithin n2 ex.1 ex'.1 cr ex.2 ex'.2) :
    cpsNBranchWithin (n1 + n2) entry cr P exits' := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, ex, hmem, hpc1, hQ1⟩ :=
    h1 R hR s hcr hPR hpc
  obtain ⟨ex', hmem', hseq⟩ := h2 ex hmem
  have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
  obtain ⟨k2, hk2, s2, hstep2, hpc2, hQ2⟩ :=
    hseq R hR s1 hcr' hQ1 hpc1
  exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2,
    stepN_add_eq hstep1 hstep2, ex', hmem', hpc2, hQ2⟩

/- Compose a continuation at an exit after an arbitrary retained prefix.  The
   prefix form is useful for the round's status arms: each arm is adjacent to
   the remaining concrete exits, but spelling that whole list at every step
   would duplicate the generated postconditions. -/
theorem nb_extend_after_prefix {n1 n2 : Nat} {entry mid : Word}
    {cr : CodeReq} {P Qm : Assertion}
    {preExits rest exits2 : List (Word × Assertion)}
    (h1 : cpsNBranchWithin n1 entry cr P
      (preExits ++ ((mid, Qm) :: rest)))
    (h2 : cpsNBranchWithin n2 mid cr Qm exits2) :
    cpsNBranchWithin (n1 + n2) entry cr P
      (preExits ++ (exits2 ++ rest)) := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, ex, hmem, hpc1, hQ1⟩ :=
    h1 R hR s hcr hPR hpc
  simp only [List.mem_append, List.mem_cons] at hmem
  rcases hmem with hprefix | hmid | hrest
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right n1 n2), s1,
      hstep1, ex, List.mem_append_left (exits2 ++ rest) hprefix, hpc1, hQ1⟩
  · subst ex
    have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, ex2, hmem2, hpc2, hQ2⟩ :=
      h2 R hR s1 hcr' hQ1 hpc1
    exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2,
      stepN_add_eq hstep1 hstep2, ex2,
        List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hmem2))),
      hpc2, hQ2⟩
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right n1 n2), s1,
        hstep1, ex,
        List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hrest))),
        hpc1, hQ1⟩

/- The same operation with one already-transformed exit in front of the
   selected arm.  Keeping this association explicit avoids reopening the
   generated source post list merely to reach the next overflow arm. -/
theorem nb_extend_after_second {n1 n2 : Nat} {entry mid : Word}
    {cr : CodeReq} {P Qfirst Qm : Assertion}
    {first : Word} {preExits rest exits2 : List (Word × Assertion)}
    (h1 : cpsNBranchWithin n1 entry cr P
      (preExits ++ ((first, Qfirst) :: (mid, Qm) :: rest)))
    (h2 : cpsNBranchWithin n2 mid cr Qm exits2) :
    cpsNBranchWithin (n1 + n2) entry cr P
      (preExits ++ ((first, Qfirst) :: (exits2 ++ rest))) := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, ex, hmem, hpc1, hQ1⟩ :=
    h1 R hR s hcr hPR hpc
  simp only [List.mem_append, List.mem_cons] at hmem
  rcases hmem with hprefix | hfirst | hmid | hrest
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right n1 n2), s1,
      hstep1, ex,
      List.mem_append.mpr (Or.inl hprefix), hpc1, hQ1⟩
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right n1 n2), s1,
      hstep1, ex,
      List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl hfirst))),
      hpc1, hQ1⟩
  · subst ex
    have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, ex2, hmem2, hpc2, hQ2⟩ :=
      h2 R hR s1 hcr' hQ1 hpc1
    exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2,
      stepN_add_eq hstep1 hstep2, ex2,
      List.mem_append.mpr (Or.inr (List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inl hmem2))))), hpc2, hQ2⟩
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right n1 n2), s1,
      hstep1, ex,
      List.mem_append.mpr (Or.inr (List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inr hrest))))), hpc1, hQ1⟩

/- The zero-accumulator arm reaches the exit-divide window with the concrete
   values produced by the round dispatch: `x5 = w`, `x6 = a5`, and the
   caller's `AB`/`PB` bases in `x19`/`x20`.  This adapter is the first point
   where that branch is joined to the common output tail; the tail theorem is
   supplied by the caller so its alignment and readable-region facts remain
   explicit at the real call site. -/
theorem round_zero_exitdiv_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion) (hFR : FR.pcFree)
    (hAB : AB = newSp + signExtend12 (64 : BitVec 12))
    (hPB : PB = newSp + signExtend12 (112 : BitVec 12))
    {exits : List (Word × Assertion)}
    (hTail : cpsNBranchWithin 296 (PriceK + 900) priceCode
      (exitdivTailPre newSp excess outPtr iVal vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        o0 o1 o2 o3 AB PB FR) exits) :
    cpsNBranchWithin 4183 (PriceK + 804) priceCode
      (roundZero newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) exits := by
  have hSeq := exitdiv_seq_tail newSp excess outPtr iVal vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    o0 o1 o2 o3 (roundAccum a0 a1 a2 a3 a4 a5) a5 v7 AB PB v28 v29 v30 v31
    FR hFR hTail
  refine cpsNBranchWithin_weaken_pre ?_ hSeq
  intro h hp
  simp only [roundZero] at hp
  have hp' := pure_drop_mid
    (L1 := (.x18 ↦ᵣ iVal))
    (L2 := ((.x5 ↦ᵣ (roundAccum a0 a1 a2 a3 a4 a5)) ** (.x0 ↦ᵣ (0 : Word))))
    (P := roundAccum a0 a1 a2 a3 a4 a5 = (0 : Word))
    (R := roundFrame newSp excess outPtr AB PB vals a5 v7 v28 v29 v30 v31
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
    h (by
      simpa only [sepConj_assoc'] using hp)
  simp only [roundFrame, exitdivPre, exitdivOutputCells, hAB, hPB,
    EvmAsm.Rv64.AddrNorm.se12_0, EvmAsm.Rv64.AddrNorm.se12_8,
    EvmAsm.Rv64.AddrNorm.se12_16, EvmAsm.Rv64.AddrNorm.se12_24,
    EvmAsm.Rv64.AddrNorm.se12_32, EvmAsm.Rv64.AddrNorm.se12_40,
    EvmAsm.Rv64.AddrNorm.word_add_zero] at hp' ⊢
  xperm_hyp hp'

/- Apply the zero-arm continuation to the first exit of the already-proved
   outer round.  This keeps the other round exits intact, while replacing the
   +804 stop with the two +968 tail outcomes. -/
theorem taylor_round_zero_exitdiv_tail
    {P Qzero : Assertion} {rest exits : List (Word × Assertion)}
    (hRound : cpsNBranchWithin 4028 (PriceK + 144) priceCode P
      ((PriceK + 804, Qzero) :: rest))
    (hZero : cpsNBranchWithin 4183 (PriceK + 804) priceCode Qzero exits) :
    cpsNBranchWithin (4028 + 4183) (PriceK + 144) priceCode P
      (exits ++ rest) :=
  nb_extend_head_same_cr hRound hZero

/- Replace the zero-accumulator exit in the terminal-index BGEU round.  The
   linked artifact takes this arm through `li t0, 496` at `0x8000b414` and
   `bgeu` at `0x8000b418`, targeting `0x8000b710`.  The status-1 terminal
   exit remains in the list, so this is an arm-for-arm composition rather
   than a theorem that silently drops the alternate branch. -/
theorem taylor_round_terminal_496_status1_exitdiv_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion)
    (hFR : FR.pcFree) (h_i : iVal = (496 : Word))
    (hAB : AB = newSp + signExtend12 (64 : BitVec 12))
    (hPB : PB = newSp + signExtend12 (112 : BitVec 12))
    {exits : List (Word × Assertion)}
    (hTail : cpsNBranchWithin 296 (PriceK + 900) priceCode
      (exitdivTailPre newSp excess outPtr iVal vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        o0 o1 o2 o3 AB PB FR) exits) :
    cpsNBranchWithin (17 + 4183) (PriceK + 144) priceCode
      (roundEntry newSp excess outPtr iVal AB PB vals
        v5 v6 v7 v28 v29 v30 v31
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
      (exits ++
        [(PriceK + 968,
          roundTerminalStatus1 newSp excess outPtr iVal AB PB vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
            v7 v28 v29 v30 v31
            (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))]) := by
  let FR0 : Assertion := exitdivOutputCells outPtr o0 o1 o2 o3 ** FR
  have hFR0 : FR0.pcFree := by
    unfold FR0
    pcFree
    exact hFR
  have hRound := taylor_round_terminal_496_status1
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v5 v6 v7 v28 v29 v30 v31 FR0 hFR0 h_i
  have hRoundN := cpsBranchWithin_as_cpsNBranchWithin hRound
  have hZero := round_zero_exitdiv_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 o0 o1 o2 o3 FR hFR hAB hPB hTail
  have hAll := nb_extend_head_same_cr hRoundN hZero
  simpa [FR0] using hAll

/- The common linked status-1 exit is a one-instruction continuation from
   every overflow post at `PriceK + 964`.  Keeping the continuation
   assertion generic lets the later arm adapters retain the complete
   overflow-specific state while changing only the ABI status register. -/
theorem status1_tail
    (excess : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      ((.x10 ↦ᵣ excess) ** FR)
      ((.x10 ↦ᵣ (1 : Word)) ** FR) := by
  have hLi := li_spec_gen_within .x10 excess (1 : Word)
    (PriceK + 964) (by decide)
  have hLiF := cpsTripleWithin_frameR FR hFR hLi
  refine cpsTripleWithin_extend_code ?_ hLiF
  intro a i hi
  have hins : amsterdamBlobGasPriceU256_prog[241]'(by decide) =
      .LI .x10 (1 : Word) := by decide
  show priceCode a = some i
  exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 964)
    amsterdamBlobGasPriceU256_prog 241 (.LI .x10 (1 : Word))
    (by decide) (by decide) hins (by decide) a i hi

/- The `mul6PQOVF0` post has the status input in the middle of its exact
   resource chain.  This residual assertion is the same chain with that one
   register removed, so the status continuation cannot duplicate ownership or
   silently discard the overflow-specific arithmetic state. -/
@[reducible] def mul6OverflowRest
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (r29 x5 x6 x7 x28 x30 x31 : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  (((.x29 ↦ᵣ r29) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜r29 ≠ (0 : Word)⌝) **
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
    (.x11 ↦ᵣ outPtr) ** (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
    (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ AB) ** (.x20 ↦ᵣ PB) **
    (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 160)) **
    (.x5 ↦ᵣ x5) ** (.x6 ↦ᵣ x6) ** (.x7 ↦ᵣ x7) **
    (.x28 ↦ᵣ x28) ** (.x30 ↦ᵣ x30) ** (.x31 ↦ᵣ x31) **
    frameSlotsSaved priceFrame newSp vals **
    (((AB) + signExtend12 0) ↦ₘ a0) **
    (((AB) + signExtend12 8) ↦ₘ a1) **
    (((AB) + signExtend12 16) ↦ₘ a2) **
    (((AB) + signExtend12 24) ↦ₘ a3) **
    (((AB) + signExtend12 32) ↦ₘ a4) **
    (((AB) + signExtend12 40) ↦ₘ a5) **
    (((PB) + signExtend12 0) ↦ₘ p0) **
    (((PB) + signExtend12 8) ↦ₘ p1) **
    (((PB) + signExtend12 16) ↦ₘ p2) **
    (((PB) + signExtend12 24) ↦ₘ p3) **
    (((PB) + signExtend12 32) ↦ₘ p4) **
    (((PB) + signExtend12 40) ↦ₘ p5) **
    (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) **
    (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
    (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) **
    (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
    (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) **
    (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5) ** FR)

theorem mul6PQOVF0_status1_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      (mul6PQOVF0 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 ** FR)
      ((.x10 ↦ᵣ (1 : Word)) **
        (mul6OverflowRest newSp excess outPtr iVal AB PB vals
          (if BitVec.ult ((rv64_mulhu a0 excess) +
              (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess)
                then (1 : Word) else (0 : Word))) (rv64_mulhu a0 excess)
            then (1 : Word) else (0 : Word))
          a0 (a0 * excess) (rv64_mulhu a0 excess) ((a0 * excess) + (0 : Word))
          ((rv64_mulhu a0 excess) +
            (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess)
              then (1 : Word) else (0 : Word))) (0 : Word)
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR)) := by
  let FR' : Assertion :=
    mul6OverflowRest newSp excess outPtr iVal AB PB vals
      (if BitVec.ult ((rv64_mulhu a0 excess) +
          (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess)
            then (1 : Word) else (0 : Word))) (rv64_mulhu a0 excess)
        then (1 : Word) else (0 : Word))
      a0 (a0 * excess) (rv64_mulhu a0 excess) ((a0 * excess) + (0 : Word))
      ((rv64_mulhu a0 excess) +
        (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess)
          then (1 : Word) else (0 : Word))) (0 : Word)
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR
  have hFR' : FR'.pcFree := by
    unfold FR'
    pcFree
    exact hFR
  have hTail := status1_tail excess FR' hFR'
  apply cpsTripleWithin_weaken
    (hpre := ?_) (hpost := fun _ hp => hp) hTail
  intro h hh
  simp only [mul6PQOVF0, FR', mul6OverflowRest] at hh ⊢
  xperm_hyp hh

/- The seven multiply-overflow exits have the same ownership shape.  These
   helpers name the low-word, low-word carry, and high-word carry recurrence
   used by the generated posts, so the arm-specific adapters below expose only
   the changing arithmetic values rather than duplicating the ownership chain.
   The definitions unfold to the emitted expressions in Body10Spec. -/
@[reducible] def mul6Low (a excess carryIn : Word) : Word :=
  (a * excess) + carryIn

@[reducible] def mul6LowCarry (a excess carryIn : Word) : Word :=
  if BitVec.ult (mul6Low a excess carryIn) (a * excess) then
    (1 : Word) else 0

@[reducible] def mul6HighCarry (a excess carryIn : Word) : Word :=
  (rv64_mulhu a excess) + mul6LowCarry a excess carryIn

@[reducible] def mul6Low0 (a0 excess : Word) : Word :=
  mul6Low a0 excess (0 : Word)

@[reducible] def mul6HighCarry0 (a0 excess : Word) : Word :=
  mul6HighCarry a0 excess (0 : Word)

@[reducible] def mul6Low1 (a0 a1 excess : Word) : Word :=
  mul6Low a1 excess (mul6HighCarry0 a0 excess)

@[reducible] def mul6HighCarry1 (a0 a1 excess : Word) : Word :=
  mul6HighCarry a1 excess (mul6HighCarry0 a0 excess)

@[reducible] def mul6Low2 (a0 a1 a2 excess : Word) : Word :=
  mul6Low a2 excess (mul6HighCarry1 a0 a1 excess)

@[reducible] def mul6HighCarry2 (a0 a1 a2 excess : Word) : Word :=
  mul6HighCarry a2 excess (mul6HighCarry1 a0 a1 excess)

@[reducible] def mul6Low3 (a0 a1 a2 a3 excess : Word) : Word :=
  mul6Low a3 excess (mul6HighCarry2 a0 a1 a2 excess)

@[reducible] def mul6HighCarry3 (a0 a1 a2 a3 excess : Word) : Word :=
  mul6HighCarry a3 excess (mul6HighCarry2 a0 a1 a2 excess)

@[reducible] def mul6Low4 (a0 a1 a2 a3 a4 excess : Word) : Word :=
  mul6Low a4 excess (mul6HighCarry3 a0 a1 a2 a3 excess)

@[reducible] def mul6HighCarry4 (a0 a1 a2 a3 a4 excess : Word) : Word :=
  mul6HighCarry a4 excess (mul6HighCarry3 a0 a1 a2 a3 excess)

@[reducible] def mul6Low5 (a0 a1 a2 a3 a4 a5 excess : Word) : Word :=
  mul6Low a5 excess (mul6HighCarry4 a0 a1 a2 a3 a4 excess)

@[reducible] def mul6HighCarry5 (a0 a1 a2 a3 a4 a5 excess : Word) : Word :=
  mul6HighCarry a5 excess (mul6HighCarry4 a0 a1 a2 a3 a4 excess)

private theorem mul6Overflow_status1_tail
    (excess : Word) (Q FR : Assertion) (hFR : FR.pcFree)
    (hQ : ∀ h, Q h → ((.x10 ↦ᵣ excess) ** FR) h) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      Q ((.x10 ↦ᵣ (1 : Word)) ** FR) := by
  apply cpsTripleWithin_weaken (hpre := hQ) (hpost := fun _ hp => hp)
    (status1_tail excess FR hFR)

theorem mul6PQOVF1_status1_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      (mul6PQOVF1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 ** FR)
      ((.x10 ↦ᵣ (1 : Word)) **
        (mul6OverflowRest newSp excess outPtr iVal AB PB vals
          (if BitVec.ult (mul6HighCarry1 a0 a1 excess) (rv64_mulhu a1 excess)
            then (1 : Word) else 0)
          a1 (a1 * excess) (rv64_mulhu a1 excess) (mul6Low1 a0 a1 excess)
          (mul6HighCarry1 a0 a1 excess) (mul6HighCarry0 a0 excess)
          a0 a1 a2 a3 a4 a5 (mul6Low0 a0 excess) p1 p2 p3 p4 p5
          s0 s1 s2 s3 s4 s5 FR)) := by
  let FR' : Assertion :=
    mul6OverflowRest newSp excess outPtr iVal AB PB vals
      (if BitVec.ult (mul6HighCarry1 a0 a1 excess) (rv64_mulhu a1 excess)
        then (1 : Word) else 0)
      a1 (a1 * excess) (rv64_mulhu a1 excess) (mul6Low1 a0 a1 excess)
      (mul6HighCarry1 a0 a1 excess) (mul6HighCarry0 a0 excess)
      a0 a1 a2 a3 a4 a5 (mul6Low0 a0 excess) p1 p2 p3 p4 p5
      s0 s1 s2 s3 s4 s5 FR
  have hFR' : FR'.pcFree := by
    unfold FR'
    pcFree
    exact hFR
  apply mul6Overflow_status1_tail excess
    (mul6PQOVF1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 ** FR) FR' hFR'
  intro h hh
  simp only [mul6PQOVF1, FR', mul6OverflowRest,
    mul6Low, mul6LowCarry, mul6HighCarry, mul6Low0, mul6HighCarry0,
    mul6Low1, mul6HighCarry1] at hh ⊢
  xperm_hyp hh

theorem mul6PQOVF2_status1_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      (mul6PQOVF2 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 ** FR)
      ((.x10 ↦ᵣ (1 : Word)) **
        (mul6OverflowRest newSp excess outPtr iVal AB PB vals
          (if BitVec.ult (mul6HighCarry2 a0 a1 a2 excess) (rv64_mulhu a2 excess)
            then (1 : Word) else 0)
          a2 (a2 * excess) (rv64_mulhu a2 excess) (mul6Low2 a0 a1 a2 excess)
          (mul6HighCarry2 a0 a1 a2 excess) (mul6HighCarry1 a0 a1 excess)
          a0 a1 a2 a3 a4 a5 (mul6Low0 a0 excess) (mul6Low1 a0 a1 excess)
          p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR)) := by
  let FR' : Assertion :=
    mul6OverflowRest newSp excess outPtr iVal AB PB vals
      (if BitVec.ult (mul6HighCarry2 a0 a1 a2 excess) (rv64_mulhu a2 excess)
        then (1 : Word) else 0)
      a2 (a2 * excess) (rv64_mulhu a2 excess) (mul6Low2 a0 a1 a2 excess)
      (mul6HighCarry2 a0 a1 a2 excess) (mul6HighCarry1 a0 a1 excess)
      a0 a1 a2 a3 a4 a5 (mul6Low0 a0 excess) (mul6Low1 a0 a1 excess)
      p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR
  have hFR' : FR'.pcFree := by
    unfold FR'
    pcFree
    exact hFR
  apply mul6Overflow_status1_tail excess
    (mul6PQOVF2 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 ** FR) FR' hFR'
  intro h hh
  simp only [mul6PQOVF2, FR', mul6OverflowRest,
    mul6Low, mul6LowCarry, mul6HighCarry, mul6Low0, mul6HighCarry0,
    mul6Low1, mul6HighCarry1, mul6Low2, mul6HighCarry2] at hh ⊢
  xperm_hyp hh

theorem mul6PQOVF3_status1_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      (mul6PQOVF3 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p3 p4 p5 s0 s1 s2 s3 s4 s5 ** FR)
      ((.x10 ↦ᵣ (1 : Word)) **
        (mul6OverflowRest newSp excess outPtr iVal AB PB vals
          (if BitVec.ult (mul6HighCarry3 a0 a1 a2 a3 excess) (rv64_mulhu a3 excess)
            then (1 : Word) else 0)
          a3 (a3 * excess) (rv64_mulhu a3 excess) (mul6Low3 a0 a1 a2 a3 excess)
          (mul6HighCarry3 a0 a1 a2 a3 excess) (mul6HighCarry2 a0 a1 a2 excess)
          a0 a1 a2 a3 a4 a5 (mul6Low0 a0 excess) (mul6Low1 a0 a1 excess)
          (mul6Low2 a0 a1 a2 excess) p3 p4 p5 s0 s1 s2 s3 s4 s5 FR)) := by
  let FR' : Assertion :=
    mul6OverflowRest newSp excess outPtr iVal AB PB vals
      (if BitVec.ult (mul6HighCarry3 a0 a1 a2 a3 excess) (rv64_mulhu a3 excess)
        then (1 : Word) else 0)
      a3 (a3 * excess) (rv64_mulhu a3 excess) (mul6Low3 a0 a1 a2 a3 excess)
      (mul6HighCarry3 a0 a1 a2 a3 excess) (mul6HighCarry2 a0 a1 a2 excess)
      a0 a1 a2 a3 a4 a5 (mul6Low0 a0 excess) (mul6Low1 a0 a1 excess)
      (mul6Low2 a0 a1 a2 excess) p3 p4 p5 s0 s1 s2 s3 s4 s5 FR
  have hFR' : FR'.pcFree := by
    unfold FR'
    pcFree
    exact hFR
  apply mul6Overflow_status1_tail excess
    (mul6PQOVF3 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p3 p4 p5 s0 s1 s2 s3 s4 s5 ** FR) FR' hFR'
  intro h hh
  simp only [mul6PQOVF3, FR', mul6OverflowRest,
    mul6Low, mul6LowCarry, mul6HighCarry, mul6Low0, mul6HighCarry0,
    mul6Low1, mul6HighCarry1, mul6Low2, mul6HighCarry2,
    mul6Low3, mul6HighCarry3] at hh ⊢
  xperm_hyp hh

theorem mul6PQOVF4_status1_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      (mul6PQOVF4 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p4 p5 s0 s1 s2 s3 s4 s5 ** FR)
      ((.x10 ↦ᵣ (1 : Word)) **
        (mul6OverflowRest newSp excess outPtr iVal AB PB vals
          (if BitVec.ult (mul6HighCarry4 a0 a1 a2 a3 a4 excess) (rv64_mulhu a4 excess)
            then (1 : Word) else 0)
          a4 (a4 * excess) (rv64_mulhu a4 excess) (mul6Low4 a0 a1 a2 a3 a4 excess)
          (mul6HighCarry4 a0 a1 a2 a3 a4 excess) (mul6HighCarry3 a0 a1 a2 a3 excess)
          a0 a1 a2 a3 a4 a5 (mul6Low0 a0 excess) (mul6Low1 a0 a1 excess)
          (mul6Low2 a0 a1 a2 excess) (mul6Low3 a0 a1 a2 a3 excess) p4 p5
          s0 s1 s2 s3 s4 s5 FR)) := by
  let FR' : Assertion :=
    mul6OverflowRest newSp excess outPtr iVal AB PB vals
      (if BitVec.ult (mul6HighCarry4 a0 a1 a2 a3 a4 excess) (rv64_mulhu a4 excess)
        then (1 : Word) else 0)
      a4 (a4 * excess) (rv64_mulhu a4 excess) (mul6Low4 a0 a1 a2 a3 a4 excess)
      (mul6HighCarry4 a0 a1 a2 a3 a4 excess) (mul6HighCarry3 a0 a1 a2 a3 excess)
      a0 a1 a2 a3 a4 a5 (mul6Low0 a0 excess) (mul6Low1 a0 a1 excess)
      (mul6Low2 a0 a1 a2 excess) (mul6Low3 a0 a1 a2 a3 excess) p4 p5
      s0 s1 s2 s3 s4 s5 FR
  have hFR' : FR'.pcFree := by
    unfold FR'
    pcFree
    exact hFR
  apply mul6Overflow_status1_tail excess
    (mul6PQOVF4 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p4 p5 s0 s1 s2 s3 s4 s5 ** FR) FR' hFR'
  intro h hh
  simp only [mul6PQOVF4, FR', mul6OverflowRest,
    mul6Low, mul6LowCarry, mul6HighCarry, mul6Low0, mul6HighCarry0,
    mul6Low1, mul6HighCarry1, mul6Low2, mul6HighCarry2,
    mul6Low3, mul6HighCarry3, mul6Low4, mul6HighCarry4] at hh ⊢
  xperm_hyp hh

theorem mul6PQOVF5_status1_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      (mul6PQOVF5 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p5 s0 s1 s2 s3 s4 s5 ** FR)
      ((.x10 ↦ᵣ (1 : Word)) **
        (mul6OverflowRest newSp excess outPtr iVal AB PB vals
          (if BitVec.ult (mul6HighCarry5 a0 a1 a2 a3 a4 a5 excess) (rv64_mulhu a5 excess)
            then (1 : Word) else 0)
          a5 (a5 * excess) (rv64_mulhu a5 excess) (mul6Low5 a0 a1 a2 a3 a4 a5 excess)
          (mul6HighCarry5 a0 a1 a2 a3 a4 a5 excess) (mul6HighCarry4 a0 a1 a2 a3 a4 excess)
          a0 a1 a2 a3 a4 a5 (mul6Low0 a0 excess) (mul6Low1 a0 a1 excess)
          (mul6Low2 a0 a1 a2 excess) (mul6Low3 a0 a1 a2 a3 excess)
          (mul6Low4 a0 a1 a2 a3 a4 excess) p5 s0 s1 s2 s3 s4 s5 FR)) := by
  let FR' : Assertion :=
    mul6OverflowRest newSp excess outPtr iVal AB PB vals
      (if BitVec.ult (mul6HighCarry5 a0 a1 a2 a3 a4 a5 excess) (rv64_mulhu a5 excess)
        then (1 : Word) else 0)
      a5 (a5 * excess) (rv64_mulhu a5 excess) (mul6Low5 a0 a1 a2 a3 a4 a5 excess)
      (mul6HighCarry5 a0 a1 a2 a3 a4 a5 excess) (mul6HighCarry4 a0 a1 a2 a3 a4 excess)
      a0 a1 a2 a3 a4 a5 (mul6Low0 a0 excess) (mul6Low1 a0 a1 excess)
      (mul6Low2 a0 a1 a2 excess) (mul6Low3 a0 a1 a2 a3 excess)
      (mul6Low4 a0 a1 a2 a3 a4 excess) p5 s0 s1 s2 s3 s4 s5 FR
  have hFR' : FR'.pcFree := by
    unfold FR'
    pcFree
    exact hFR
  apply mul6Overflow_status1_tail excess
    (mul6PQOVF5 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p5 s0 s1 s2 s3 s4 s5 ** FR) FR' hFR'
  intro h hh
  simp only [mul6PQOVF5, FR', mul6OverflowRest,
    mul6Low, mul6LowCarry, mul6HighCarry, mul6Low0, mul6HighCarry0,
    mul6Low1, mul6HighCarry1, mul6Low2, mul6HighCarry2,
    mul6Low3, mul6HighCarry3, mul6Low4, mul6HighCarry4,
    mul6Low5, mul6HighCarry5] at hh ⊢
  xperm_hyp hh

@[reducible] def mul6FinalOverflowRest
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (x5 x6 x7 x28 x29 x30 x31 : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  (((.x31 ↦ᵣ x31) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜x31 ≠ (0 : Word)⌝) **
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
    (.x11 ↦ᵣ outPtr) ** (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
    (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ AB) ** (.x20 ↦ᵣ PB) **
    (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 160)) **
    (.x5 ↦ᵣ x5) ** (.x6 ↦ᵣ x6) ** (.x7 ↦ᵣ x7) **
    (.x28 ↦ᵣ x28) ** (.x29 ↦ᵣ x29) ** (.x30 ↦ᵣ x30) **
    frameSlotsSaved priceFrame newSp vals **
    (((AB) + signExtend12 0) ↦ₘ a0) **
    (((AB) + signExtend12 8) ↦ₘ a1) **
    (((AB) + signExtend12 16) ↦ₘ a2) **
    (((AB) + signExtend12 24) ↦ₘ a3) **
    (((AB) + signExtend12 32) ↦ₘ a4) **
    (((AB) + signExtend12 40) ↦ₘ a5) **
    (((PB) + signExtend12 0) ↦ₘ p0) **
    (((PB) + signExtend12 8) ↦ₘ p1) **
    (((PB) + signExtend12 16) ↦ₘ p2) **
    (((PB) + signExtend12 24) ↦ₘ p3) **
    (((PB) + signExtend12 32) ↦ₘ p4) **
    (((PB) + signExtend12 40) ↦ₘ p5) **
    (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) **
    (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
    (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) **
    (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
    (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) **
    (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5) ** FR)

theorem mul6PQOVFF_status1_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      (mul6PQOVFF newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 ** FR)
      ((.x10 ↦ᵣ (1 : Word)) **
        (mul6FinalOverflowRest newSp excess outPtr iVal AB PB vals
          (a5) (a5 * excess) (rv64_mulhu a5 excess)
          (mul6Low5 a0 a1 a2 a3 a4 a5 excess)
          (if BitVec.ult (mul6HighCarry5 a0 a1 a2 a3 a4 a5 excess)
              (rv64_mulhu a5 excess) then (1 : Word) else 0)
          (mul6HighCarry5 a0 a1 a2 a3 a4 a5 excess)
          (mul6HighCarry5 a0 a1 a2 a3 a4 a5 excess)
          a0 a1 a2 a3 a4 a5
          (mul6Low0 a0 excess) (mul6Low1 a0 a1 excess)
          (mul6Low2 a0 a1 a2 excess) (mul6Low3 a0 a1 a2 a3 excess)
          (mul6Low4 a0 a1 a2 a3 a4 excess)
          (mul6Low5 a0 a1 a2 a3 a4 a5 excess)
          s0 s1 s2 s3 s4 s5 FR)) := by
  let FR' : Assertion :=
    mul6FinalOverflowRest newSp excess outPtr iVal AB PB vals
      a5 (a5 * excess) (rv64_mulhu a5 excess)
      (mul6Low5 a0 a1 a2 a3 a4 a5 excess)
      (if BitVec.ult (mul6HighCarry5 a0 a1 a2 a3 a4 a5 excess)
          (rv64_mulhu a5 excess) then (1 : Word) else 0)
      (mul6HighCarry5 a0 a1 a2 a3 a4 a5 excess)
      (mul6HighCarry5 a0 a1 a2 a3 a4 a5 excess)
      a0 a1 a2 a3 a4 a5
      (mul6Low0 a0 excess) (mul6Low1 a0 a1 excess)
      (mul6Low2 a0 a1 a2 excess) (mul6Low3 a0 a1 a2 a3 excess)
      (mul6Low4 a0 a1 a2 a3 a4 excess)
      (mul6Low5 a0 a1 a2 a3 a4 a5 excess)
      s0 s1 s2 s3 s4 s5 FR
  have hFR' : FR'.pcFree := by
    unfold FR'
    pcFree
    exact hFR
  apply mul6Overflow_status1_tail excess
    (mul6PQOVFF newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 ** FR) FR' hFR'
  intro h hh
  simp only [mul6PQOVFF, FR', mul6FinalOverflowRest,
    mul6Low, mul6LowCarry, mul6HighCarry, mul6Low0, mul6HighCarry0,
    mul6Low1, mul6HighCarry1, mul6Low2, mul6HighCarry2,
    mul6Low3, mul6HighCarry3, mul6Low4, mul6HighCarry4,
    mul6Low5, mul6HighCarry5] at hh ⊢
  xperm_hyp hh

/- The carry-overflow post has the same status-register seam as the multiply
   exits, but its head flag is the ripple carry rather than a product flag.
   Keep the six resulting sum cells and every live arithmetic register in the
   residual so the continuation cannot discard the carry computation. -/
@[reducible] def add6CarryRest
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (c x6 x7 x28 x29 x30 x31 : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 : Word)
    (t0 t1 t2 t3 t4 t5 : Word) (FR : Assertion) : Assertion :=
  (((.x5 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜c ≠ (0 : Word)⌝) **
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
    (.x11 ↦ᵣ outPtr) ** (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
    (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ AB) ** (.x20 ↦ᵣ PB) **
    (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 160)) **
    (.x6 ↦ᵣ x6) ** (.x7 ↦ᵣ x7) ** (.x28 ↦ᵣ x28) **
    (.x29 ↦ᵣ x29) ** (.x30 ↦ᵣ x30) ** (.x31 ↦ᵣ x31) **
    frameSlotsSaved priceFrame newSp vals **
    ((AB + signExtend12 0) ↦ₘ a0) **
    ((AB + signExtend12 8) ↦ₘ a1) **
    ((AB + signExtend12 16) ↦ₘ a2) **
    ((AB + signExtend12 24) ↦ₘ a3) **
    ((AB + signExtend12 32) ↦ₘ a4) **
    ((AB + signExtend12 40) ↦ₘ a5) **
    ((PB + signExtend12 0) ↦ₘ p0) **
    ((PB + signExtend12 8) ↦ₘ p1) **
    ((PB + signExtend12 16) ↦ₘ p2) **
    ((PB + signExtend12 24) ↦ₘ p3) **
    ((PB + signExtend12 32) ↦ₘ p4) **
    ((PB + signExtend12 40) ↦ₘ p5) **
    (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ t0) **
    (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ t1) **
    (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ t2) **
    (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ t3) **
    (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ t4) **
    (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ t5) ** FR))

theorem add6Carry_status1_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (c x6 x7 x28 x29 x30 x31 : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 : Word)
    (t0 t1 t2 t3 t4 t5 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      (((.x5 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜c ≠ (0 : Word)⌝) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ AB) ** (.x20 ↦ᵣ PB) **
        (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 160)) **
        (.x6 ↦ᵣ x6) ** (.x7 ↦ᵣ x7) ** (.x28 ↦ᵣ x28) **
        (.x29 ↦ᵣ x29) ** (.x30 ↦ᵣ x30) ** (.x31 ↦ᵣ x31) **
        frameSlotsSaved priceFrame newSp vals **
        ((AB + signExtend12 0) ↦ₘ a0) **
        ((AB + signExtend12 8) ↦ₘ a1) **
        ((AB + signExtend12 16) ↦ₘ a2) **
        ((AB + signExtend12 24) ↦ₘ a3) **
        ((AB + signExtend12 32) ↦ₘ a4) **
        ((AB + signExtend12 40) ↦ₘ a5) **
        ((PB + signExtend12 0) ↦ₘ p0) **
        ((PB + signExtend12 8) ↦ₘ p1) **
        ((PB + signExtend12 16) ↦ₘ p2) **
        ((PB + signExtend12 24) ↦ₘ p3) **
        ((PB + signExtend12 32) ↦ₘ p4) **
        ((PB + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ t0) **
        (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ t1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ t2) **
        (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ t3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ t4) **
        (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ t5) ** FR))
      ((.x10 ↦ᵣ (1 : Word)) **
        (add6CarryRest newSp excess outPtr iVal AB PB vals
          c x6 x7 x28 x29 x30 x31 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
          t0 t1 t2 t3 t4 t5 FR)) := by
  let FR' : Assertion := add6CarryRest newSp excess outPtr iVal AB PB vals
    c x6 x7 x28 x29 x30 x31 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
    t0 t1 t2 t3 t4 t5 FR
  have hFR' : FR'.pcFree := by
    unfold FR'
    pcFree
    exact hFR
  apply mul6Overflow_status1_tail excess
    (((.x5 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜c ≠ (0 : Word)⌝) **
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
      (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
      (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
      (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ AB) ** (.x20 ↦ᵣ PB) **
      (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 160)) **
      (.x6 ↦ᵣ x6) ** (.x7 ↦ᵣ x7) ** (.x28 ↦ᵣ x28) **
      (.x29 ↦ᵣ x29) ** (.x30 ↦ᵣ x30) ** (.x31 ↦ᵣ x31) **
      frameSlotsSaved priceFrame newSp vals **
      ((AB + signExtend12 0) ↦ₘ a0) **
      ((AB + signExtend12 8) ↦ₘ a1) **
      ((AB + signExtend12 16) ↦ₘ a2) **
      ((AB + signExtend12 24) ↦ₘ a3) **
      ((AB + signExtend12 32) ↦ₘ a4) **
      ((AB + signExtend12 40) ↦ₘ a5) **
      ((PB + signExtend12 0) ↦ₘ p0) **
      ((PB + signExtend12 8) ↦ₘ p1) **
      ((PB + signExtend12 16) ↦ₘ p2) **
      ((PB + signExtend12 24) ↦ₘ p3) **
      ((PB + signExtend12 32) ↦ₘ p4) **
      ((PB + signExtend12 40) ↦ₘ p5) **
      (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ t0) **
      (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ t1) **
      (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ t2) **
      (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ t3) **
      (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ t4) **
      (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ t5) ** FR)) FR' hFR'
  intro h hh
  simp only [FR', add6CarryRest] at hh ⊢
  xperm_hyp hh

/- The quotient-overflow exit uses the same status tail, but is at the other
   buffer parity: `x19 = PB`, `x20 = AB`, with the divisor product in `x5`
   and its high word in the flagged `x6`.  Preserve that complete state while
   removing only the old excess value for the one-instruction continuation. -/
@[reducible] def qOverflowRest
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (x6 x5 x7 x28 x29 x30 x31 : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  (((.x6 ↦ᵣ x6) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜x6 ≠ (0 : Word)⌝) **
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
    (.x11 ↦ᵣ outPtr) ** (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
    (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ PB) ** (.x20 ↦ᵣ AB) **
    (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 160)) **
    (.x5 ↦ᵣ x5) ** (.x7 ↦ᵣ x7) ** (.x28 ↦ᵣ x28) **
    (.x29 ↦ᵣ x29) ** (.x30 ↦ᵣ x30) ** (.x31 ↦ᵣ x31) **
    frameSlotsSaved priceFrame newSp vals **
    ((AB + signExtend12 0) ↦ₘ a0) **
    ((AB + signExtend12 8) ↦ₘ a1) **
    ((AB + signExtend12 16) ↦ₘ a2) **
    ((AB + signExtend12 24) ↦ₘ a3) **
    ((AB + signExtend12 32) ↦ₘ a4) **
    ((AB + signExtend12 40) ↦ₘ a5) **
    ((PB + signExtend12 0) ↦ₘ p0) **
    ((PB + signExtend12 8) ↦ₘ p1) **
    ((PB + signExtend12 16) ↦ₘ p2) **
    ((PB + signExtend12 24) ↦ₘ p3) **
    ((PB + signExtend12 32) ↦ₘ p4) **
    ((PB + signExtend12 40) ↦ₘ p5) **
    (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ s0) **
    (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ s1) **
    (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ s2) **
    (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ s3) **
    (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ s4) **
    (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ s5) ** FR))

theorem QOVFDIVP_status1_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      (QOVFDIVP newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      ((.x10 ↦ᵣ (1 : Word)) **
        (qOverflowRest newSp excess outPtr iVal AB PB vals
          (rv64_mulhu taylorDW iVal) (taylorDW * iVal) v7 v28 v29 v30 v31
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR)) := by
  let FR' : Assertion := qOverflowRest newSp excess outPtr iVal AB PB vals
    (rv64_mulhu taylorDW iVal) (taylorDW * iVal) v7 v28 v29 v30 v31
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR
  have hFR' : FR'.pcFree := by
    unfold FR'
    pcFree
    exact hFR
  apply mul6Overflow_status1_tail excess
    (QOVFDIVP newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR) FR' hFR'
  intro h hh
  simp only [QOVFDIVP, FR', qOverflowRest] at hh ⊢
  xperm_hyp hh

/- The cap exit also reports status one.  Unlike `roundTerminal`, this
   residual deliberately does not require the accumulator's nonzero fact:
   that fact is not part of the `taylor_round` cap post. -/
@[reducible] def terminalIndexRest
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) : Assertion :=
  (.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) **
  ⌜¬ BitVec.ult iVal (496 : Word)⌝ ** (.x0 ↦ᵣ (0 : Word)) **
    roundFrameNoX10 newSp excess outPtr AB PB vals a5 v7 v28 v29 v30 v31
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR

theorem terminalIndex_status1_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      ((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) **
        ⌜¬ BitVec.ult iVal (496 : Word)⌝ **
        ((.x0 ↦ᵣ (0 : Word)) **
          roundFrame newSp excess outPtr AB PB vals a5 v7 v28 v29 v30 v31
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
            s0 s1 s2 s3 s4 s5 FR))
      ((.x10 ↦ᵣ (1 : Word)) **
        terminalIndexRest newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v7 v28 v29 v30 v31 FR) := by
  let FR' : Assertion := terminalIndexRest newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR
  have hFR' : FR'.pcFree := by
    unfold FR'
    pcFree
    exact hFR
  apply mul6Overflow_status1_tail excess
    ((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) **
      ⌜¬ BitVec.ult iVal (496 : Word)⌝ **
      ((.x0 ↦ᵣ (0 : Word)) **
        roundFrame newSp excess outPtr AB PB vals a5 v7 v28 v29 v30 v31
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR)) FR' hFR'
  intro h hh
  simp only [FR', terminalIndexRest, roundFrame, roundFrameNoX10] at hh ⊢
  xperm_hyp hh

/- Apply the terminal-index continuation after the zero-accumulator exit has
   already been replaced by its output-tail exits.  This small list-level
   theorem keeps the BGEU arm's source post and its exact one-instruction
   continuation separate from the arithmetic expressions in `taylor_round`. -/
theorem taylor_round_zero_terminal_status1
    {P Qzero Qterm Qterm' : Assertion}
    {rest exits : List (Word × Assertion)}
    (hRound : cpsNBranchWithin 4028 (PriceK + 144) priceCode P
      ((PriceK + 804, Qzero) :: (PriceK + 964, Qterm) :: rest))
    (hZero : cpsNBranchWithin 4183 (PriceK + 804) priceCode Qzero exits)
    (hTerm : cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      Qterm Qterm') :
    cpsNBranchWithin (4028 + 4183 + 1) (PriceK + 144) priceCode P
      (exits ++ ((PriceK + 968, Qterm') :: rest)) := by
  have hAll := taylor_round_zero_exitdiv_tail hRound hZero
  have hTermN := cpsTripleWithin_as_cpsNBranchWithin hTerm
  have hOut := nb_extend_after_prefix hAll hTermN
  simpa using hOut

theorem taylor_round_zero_terminal_status1_weaken
    {P Qzero Qterm Qzero' Qterm' QtermOut : Assertion}
    {rest exits : List (Word × Assertion)}
    (hRound : cpsNBranchWithin 4028 (PriceK + 144) priceCode P
      ((PriceK + 804, Qzero) :: (PriceK + 964, Qterm) :: rest))
    (hZero : cpsNBranchWithin 4183 (PriceK + 804) priceCode Qzero' exits)
    (hZero_pre : ∀ h, Qzero h → Qzero' h)
    (hTerm : cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      Qterm' QtermOut)
    (hTerm_pre : ∀ h, Qterm h → Qterm' h) :
    cpsNBranchWithin (4028 + 4183 + 1) (PriceK + 144) priceCode P
      (exits ++ ((PriceK + 968, QtermOut) :: rest)) := by
  have hZero' := cpsNBranchWithin_weaken_pre hZero_pre hZero
  have hTerm' := cpsTripleWithin_weaken
    (hpre := hTerm_pre) (hpost := fun _ hp => hp) hTerm
  exact taylor_round_zero_terminal_status1 hRound hZero' hTerm'

/- Continue one more arm after the terminal status tail.  The explicit
   three-entry shape is intentional: it records that the terminal outcome is
   retained before the carry-overflow outcome is replaced by its status tail. -/
theorem taylor_round_zero_terminal_carry_status1
    {P Qzero Qterm Qcarry Qzero' Qterm' Qcarry' QtermOut QcarryOut : Assertion}
    {rest exits : List (Word × Assertion)}
    (hRound : cpsNBranchWithin 4028 (PriceK + 144) priceCode P
      ((PriceK + 804, Qzero) :: (PriceK + 964, Qterm) ::
        (PriceK + 964, Qcarry) :: rest))
    (hZero : cpsNBranchWithin 4183 (PriceK + 804) priceCode Qzero' exits)
    (hZero_pre : ∀ h, Qzero h → Qzero' h)
    (hTerm : cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      Qterm' QtermOut)
    (hTerm_pre : ∀ h, Qterm h → Qterm' h)
    (hCarry : cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      Qcarry' QcarryOut)
    (hCarry_pre : ∀ h, Qcarry h → Qcarry' h) :
    cpsNBranchWithin (4028 + 4183 + 1 + 1) (PriceK + 144) priceCode P
      (exits ++ ((PriceK + 968, QtermOut) ::
        ((PriceK + 968, QcarryOut) :: rest))) := by
  have h1 := taylor_round_zero_terminal_status1_weaken
    (rest := (PriceK + 964, Qcarry) :: rest)
    hRound hZero hZero_pre hTerm hTerm_pre
  have hCarry' := cpsTripleWithin_weaken
    (hpre := hCarry_pre) (hpost := fun _ hp => hp) hCarry
  have h3 := nb_extend_after_second h1
    (cpsTripleWithin_as_cpsNBranchWithin hCarry')
  simpa [Nat.add_assoc] using h3

/- A concrete witness for the completed zero-arm boundary.  This is kept
   beside the adapter because the arm's pure `w = 0` fact and its output
   cells are part of the applied precondition, not facts supplied by a later
   caller proof.  The four output cells also make the witness explicitly
   non-empty on the continuation boundary. -/

def roundWitnessSp : Word := (0xa004ff30 : Word)
def roundWitnessAB : Word := roundWitnessSp + signExtend12 (64 : BitVec 12)
def roundWitnessPB : Word := roundWitnessSp + signExtend12 (112 : BitVec 12)
def roundWitnessSum : Word := roundWitnessSp + signExtend12 (160 : BitVec 12)
def roundWitnessOut : Word := (0xa0010100 : Word)

def roundWitnessVals : Reg → Word := fun _ => 0

private inductive WitnessResource where
  | pure
  | reg (r : Reg)
  | mem (a : Word)
  deriving DecidableEq

private inductive WitnessAtom where
  | pure
  | regVal (r : Reg) (v : Word)
  | memVal (a : Word) (v : Word) (valid : isValidDwordAccess a = true)
  deriving DecidableEq

private def witnessAtomResource : WitnessAtom → WitnessResource
  | .pure => .pure
  | .regVal r _ => .reg r
  | .memVal a _ _ => .mem a

private def witnessAtomAssertion : WitnessAtom → Assertion
  | .pure => ⌜(0 : Word) = 0⌝
  | .regVal r v => r ↦ᵣ v
  | .memVal a v _ => a ↦ₘ v

private def witnessAtomHeap : WitnessAtom → PartialState
  | .pure => PartialState.empty
  | .regVal r v => PartialState.singletonReg r v
  | .memVal a v _ => PartialState.singletonMem a v

private theorem witnessSingletonReg_disjoint
    {r1 r2 : Reg} {v1 v2 : Word} (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint
      (PartialState.singletonReg r2 v2) := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r
  by_cases h : r = r1
  · subst r
    right
    simp [PartialState.singletonReg, hne]
  · left
    simp [PartialState.singletonReg, h]

private theorem witnessSingletonMem_disjoint
    {a1 a2 : Word} {v1 v2 : Word} (hne : a1 ≠ a2) :
    (PartialState.singletonMem a1 v1).Disjoint
      (PartialState.singletonMem a2 v2) := by
  refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro a
  by_cases h : a = a1
  · subst a
    right
    simp [PartialState.singletonMem, hne]
  · left
    simp [PartialState.singletonMem, h]

private theorem witnessReg_mem_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem witnessMem_reg_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonMem a v).Disjoint
      (PartialState.singletonReg r w) :=
  witnessReg_mem_disjoint.symm

private theorem witnessAtomHeap_disjoint_of_resource_ne {x y : WitnessAtom}
    (h : witnessAtomResource x ≠ witnessAtomResource y) :
    (witnessAtomHeap x).Disjoint (witnessAtomHeap y) := by
  cases x with
  | pure => exact PartialState.Disjoint_empty_left
  | regVal r v =>
      cases y with
      | pure => exact PartialState.Disjoint_empty_right
      | regVal r' v' =>
          apply witnessSingletonReg_disjoint
          simpa [witnessAtomResource] using h
      | memVal a v' hvalid => exact witnessReg_mem_disjoint
  | memVal a v hvalid =>
      cases y with
      | pure => exact PartialState.Disjoint_empty_right
      | regVal r v' => exact witnessMem_reg_disjoint
      | memVal a' v' hvalid' =>
          apply witnessSingletonMem_disjoint
          simpa [witnessAtomResource] using h

private def roundWitnessAtoms : List WitnessAtom :=
  [ .regVal .x18 1, .regVal .x5 0, .regVal .x0 0, .pure,
    .regVal .x2 roundWitnessSp, .regVal .x1 0,
    .regVal .x10 0, .regVal .x11 roundWitnessOut,
    .regVal .x8 0, .regVal .x9 taylorDW,
    .regVal .x19 roundWitnessAB, .regVal .x20 roundWitnessPB,
    .regVal .x21 roundWitnessOut, .regVal .x22 roundWitnessSum,
    .regVal .x6 0, .regVal .x7 0, .regVal .x28 0,
    .regVal .x29 0, .regVal .x30 0, .regVal .x31 0,
    .memVal (roundWitnessSp + signExtend12 (0 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessSp + signExtend12 (8 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessSp + signExtend12 (16 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessSp + signExtend12 (24 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessSp + signExtend12 (32 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessSp + signExtend12 (40 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessSp + signExtend12 (48 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessSp + signExtend12 (56 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessAB + signExtend12 (0 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessAB + signExtend12 (8 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessAB + signExtend12 (16 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessAB + signExtend12 (24 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessAB + signExtend12 (32 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessAB + signExtend12 (40 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessPB + signExtend12 (0 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessPB + signExtend12 (8 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessPB + signExtend12 (16 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessPB + signExtend12 (24 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessPB + signExtend12 (32 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessPB + signExtend12 (40 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessSum + signExtend12 (0 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessSum + signExtend12 (8 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessSum + signExtend12 (16 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessSum + signExtend12 (24 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessSum + signExtend12 (32 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessSum + signExtend12 (40 : BitVec 12)) 0 (by decide),
    .memVal (roundWitnessOut + BitVec.ofNat 64 0) 0 (by decide),
    .memVal (roundWitnessOut + BitVec.ofNat 64 8) 0 (by decide),
    .memVal (roundWitnessOut + BitVec.ofNat 64 16) 0 (by decide),
    .memVal (roundWitnessOut + BitVec.ofNat 64 24) 0 (by decide) ]

private def roundWitnessAtomsAssert : Assertion :=
  roundWitnessAtoms.foldr
    (fun x acc => witnessAtomAssertion x ** acc) empAssertion

private def roundWitnessHeap : PartialState :=
  roundWitnessAtoms.foldr
    (fun x acc => (witnessAtomHeap x).union acc) PartialState.empty

private theorem roundWitnessAtoms_pairwise :
    roundWitnessAtoms.Pairwise
      (fun x y => witnessAtomResource x ≠ witnessAtomResource y) := by
  unfold roundWitnessAtoms witnessAtomResource roundWitnessSp roundWitnessAB
    roundWitnessPB roundWitnessSum roundWitnessOut
  decide

private theorem roundWitnessAtoms_hsat :
    roundWitnessAtomsAssert roundWitnessHeap := by
  apply sepConj_foldr_satisfiable witnessAtomAssertion witnessAtomHeap
    roundWitnessAtoms
  · intro x hx
    cases x with
    | pure => exact ⟨rfl, by decide⟩
    | regVal r v => exact rfl
    | memVal a v hvalid => exact ⟨rfl, hvalid⟩
  · exact List.Pairwise.imp
      (fun {_ _} h => witnessAtomHeap_disjoint_of_resource_ne h)
      roundWitnessAtoms_pairwise

theorem round_zero_pre_inhabited :
    ∃ h : PartialState,
      roundZero roundWitnessSp 0 roundWitnessOut 1 roundWitnessAB roundWitnessPB
        roundWitnessVals
        0 0 0 0 0 0 0
        0 0 0 0 0 0
        0 0 0 0 0 0
        0 0 0 0 0
        (exitdivOutputCells roundWitnessOut 0 0 0 0) h := by
  refine ⟨roundWitnessHeap, ?_⟩
  simpa [roundZero, roundFrame, frameSlotsSaved, priceFrame,
    roundWitnessAtomsAssert, roundWitnessAtoms, witnessAtomAssertion,
    roundWitnessHeap, witnessAtomHeap, roundWitnessVals,
    roundWitnessSp, roundWitnessAB, roundWitnessPB, roundWitnessSum,
    roundWitnessOut, exitdivOutputCells, sepConj_emp_right', sepConj_assoc'] using
    roundWitnessAtoms_hsat

theorem roundWitness_output_present :
    roundWitnessHeap.mem roundWitnessOut = some (0 : Word) := by
  unfold roundWitnessHeap roundWitnessAtoms witnessAtomHeap
    roundWitnessOut roundWitnessSp roundWitnessAB roundWitnessPB roundWitnessSum
  decide

#print axioms exitdiv_seq_tail
#print axioms round_zero_exitdiv_tail
#print axioms taylor_round_zero_exitdiv_tail
#print axioms taylor_round_terminal_496_status1_exitdiv_tail
#print axioms round_zero_pre_inhabited
#print axioms roundWitness_output_present

end EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec
