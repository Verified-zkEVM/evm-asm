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

end EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec
