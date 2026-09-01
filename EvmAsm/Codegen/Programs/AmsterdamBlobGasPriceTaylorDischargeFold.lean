/-
  Step (B)/(C) of the Amsterdam blob gas price Taylor outer-loop discharge
  (#12851): the finite indexed fold over 495 rounds and the terminal round.

  The per-round round theorem `taylor_round_invariant_to_parity` (step (A),
  in `AmsterdamBlobGasPriceTaylorDischarge`) is folded with
  `finite_nbranch_loop_spec_indexed`; the invariant family threads the
  quotient/sum limbs from one round to the next, and the terminal round is
  discharged at its odd parity (the repository's
  `taylor_round_terminal_496_from_parity_exitdiv_tail_core` is the even
  instance). -/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceTaylorDischarge

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceTaylorDischarge

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
open EvmAsm.Codegen.AmsterdamBlobGasPrice
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceOuterSpec

set_option maxRecDepth 8000

/-! ## Step (B): the finite outer fold

The indexed fold (`finite_nbranch_loop_spec_indexed`) sequences `N` rounds and
a final continuation.  Its per-round hypotheses take the round invariant and
the non-backedge exits; the backedge is threaded to the next round by the fold
itself.  Step (A)'s round theorem carries the QBACK backedge back into the
next-round invariant, but with the *quotient/sum* limbs of the current round's
static limbs.  Closing the fold therefore needs the invariant family `inv j`
whose limbs at round `j` are exactly the values the loop holds there.  The
families below compute those limbs by recursion: the accumulator at `j + 1` is
the division quotient of round `j`, the product buffer receives round `j`'s
accumulator, and the sum accumulates. -/

/-- The per-round status-1 posts, with the backedge element removed.  This is
    `taylorRoundAnyStatus` without its final `(PriceK + 144, …)` element; the
    fold sequences the backedge itself. -/
@[reducible] private def taylorRoundStatusPosts
    (j : Nat) (newSp excess outPtr iVal evenBase oddBase : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR0 : Assertion) : List (Word × Assertion) :=
  [(PriceK + 968,
    taylorRoundTerminalStatus1Any newSp excess outPtr iVal
      (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0),
   (PriceK + 968,
    taylorRoundCarryStatus1 newSp excess outPtr iVal
      (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0),
   (PriceK + 968,
    taylorRoundSourceMul0Status1 newSp excess outPtr iVal
      (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0),
   (PriceK + 968,
    taylorRoundSourceMul1Status1 newSp excess outPtr iVal
      (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0),
   (PriceK + 968,
    taylorRoundSourceMul2Status1 newSp excess outPtr iVal
      (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0),
   (PriceK + 968,
    taylorRoundSourceMul3Status1 newSp excess outPtr iVal
      (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0),
   (PriceK + 968,
    taylorRoundSourceMul4Status1 newSp excess outPtr iVal
      (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0),
   (PriceK + 968,
    taylorRoundSourceMul5Status1Any newSp excess outPtr iVal
      (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0),
   (PriceK + 968,
    taylorRoundSourceMulFFStatus1Any newSp excess outPtr iVal
      (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0),
   (PriceK + 968,
    taylorRoundSourceQOVFComputedStatus1Any newSp excess outPtr iVal
      (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
      a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 FR0)]

/-- `taylorRoundAnyStatus` is exactly the ten status posts followed by the
    backedge. -/
private theorem taylorRoundAnyStatus_eq_append_backedge
    (j : Nat) (newSp excess outPtr iVal evenBase oddBase : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR0 : Assertion) :
    taylorRoundAnyStatus j newSp excess outPtr iVal evenBase oddBase vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0 =
    taylorRoundStatusPosts j newSp excess outPtr iVal evenBase oddBase vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0 ++
      [(PriceK + 144,
        taylorRoundBackedge j newSp excess outPtr evenBase oddBase vals
          a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 FR0)] := by
  rfl

/-- The full per-round terminal list with the backedge element removed.  This
    is the exit list the fold sequences per round; the backedge is appended by
    the fold's `hround` and threaded into the next round. -/
@[reducible] private def taylorRoundNoBackedge
    (j : Nat) (newSp excess outPtr iVal evenBase oddBase : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion) : List (Word × Assertion) :=
  taylorRoundTailPosts j newSp excess outPtr iVal evenBase oddBase vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR ++
  taylorRoundStatusPosts j newSp excess outPtr iVal evenBase oddBase vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)

/-- `terminal j` is exactly the non-backedge exits followed by the backedge. -/
private theorem terminal_eq_append_backedge
    {j : Nat} {newSp excess outPtr iVal evenBase oddBase : Word} {vals : Reg → Word}
    {a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word}
    {o0 o1 o2 o3 : Word} {FR : Assertion} :
    terminal j newSp excess outPtr iVal evenBase oddBase vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR =
    taylorRoundNoBackedge j newSp excess outPtr iVal evenBase oddBase vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR ++
      [(PriceK + 144,
        taylorRoundBackedge j newSp excess outPtr evenBase oddBase vals
          a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))] := by
  simp only [terminal, taylorRoundNoBackedge]
  rw [taylorRoundAnyStatus_eq_append_backedge]
  rw [List.append_assoc]

/-! The round-`j` limb families.  The accumulator at round `j + 1` is the
    division quotient of round `j`'s accumulator; the product buffer receives
    round `j`'s accumulator; the sum limbs are the `roundS` ripple of the
    current accumulator against the previous sum.  The recursion matches on the
    six-element lists; a length lemma guarantees the fallback case is never
    the one that matters. -/

@[reducible] private def taylorRoundAccList
    (excess : Word) (a0 a1 a2 a3 a4 a5 : Word) : Nat → List Word
  | 0 => [a0, a1, a2, a3, a4, a5]
  | j + 1 =>
    match taylorRoundAccList excess a0 a1 a2 a3 a4 a5 j with
    | [x0, x1, x2, x3, x4, x5] =>
        taylorRoundBackedgeQuotient (taylorLoopIndex j) excess x0 x1 x2 x3 x4 x5
    | _ => [0, 0, 0, 0, 0, 0]

@[reducible] private def taylorRoundProdList
    (excess : Word) (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 : Word) : Nat → List Word
  | 0 => [p0, p1, p2, p3, p4, p5]
  | j + 1 => taylorRoundAccList excess a0 a1 a2 a3 a4 a5 j

@[reducible] private def taylorRoundSumList
    (excess : Word) (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word) : Nat → List Word
  | 0 => [s0, s1, s2, s3, s4, s5]
  | j + 1 =>
    match taylorRoundAccList excess a0 a1 a2 a3 a4 a5 j,
      taylorRoundSumList excess a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 j with
    | [x0, x1, x2, x3, x4, x5], [z0, z1, z2, z3, z4, z5] =>
        taylorRoundBackedgeSum x0 x1 x2 x3 x4 x5 z0 z1 z2 z3 z4 z5
    | _, _ => [0, 0, 0, 0, 0, 0]

/-- A length-six list splits into exactly six elements. -/
private theorem length_six_eq (l : List Word) (h : l.length = 6) :
    ∃ x0 x1 x2 x3 x4 x5 : Word, l = [x0, x1, x2, x3, x4, x5] := by
  cases l with
  | nil => simp at h
  | cons x0 l =>
      cases l with
      | nil => simp at h
      | cons x1 l =>
          cases l with
          | nil => simp at h
          | cons x2 l =>
              cases l with
              | nil => simp at h
              | cons x3 l =>
                  cases l with
                  | nil => simp at h
                  | cons x4 l =>
                      cases l with
                      | nil => simp at h
                      | cons x5 l =>
                          cases l with
                          | nil => exact ⟨x0, x1, x2, x3, x4, x5, rfl⟩
                          | cons x6 l => simp at h

/-- The accumulator limbs always form a six-element list. -/
private theorem taylorRoundAccList_length
    (excess a0 a1 a2 a3 a4 a5 : Word) (j : Nat) :
    (taylorRoundAccList excess a0 a1 a2 a3 a4 a5 j).length = 6 := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [taylorRoundAccList]
      rcases length_six_eq (taylorRoundAccList excess a0 a1 a2 a3 a4 a5 j) ih with
        ⟨x0, x1, x2, x3, x4, x5, hl⟩
      rw [hl]
      rfl

/-- The product limbs always form a six-element list. -/
private theorem taylorRoundProdList_length
    (excess a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 : Word) (j : Nat) :
    (taylorRoundProdList excess a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 j).length = 6 := by
  cases j with
  | zero => rfl
  | succ j =>
      rw [taylorRoundProdList]
      exact taylorRoundAccList_length excess a0 a1 a2 a3 a4 a5 j

/-- The sum limbs always form a six-element list. -/
private theorem taylorRoundSumList_length
    (excess a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word) (j : Nat) :
    (taylorRoundSumList excess a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 j).length = 6 := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [taylorRoundSumList]
      rcases length_six_eq (taylorRoundAccList excess a0 a1 a2 a3 a4 a5 j)
        (taylorRoundAccList_length excess a0 a1 a2 a3 a4 a5 j) with
        ⟨x0, x1, x2, x3, x4, x5, hl⟩
      rcases length_six_eq (taylorRoundSumList excess a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 j) ih with
        ⟨z0, z1, z2, z3, z4, z5, hs⟩
      rw [hl, hs]
      rfl

/-- The accumulator list at round `j + 1` is the quotient of round `j`. -/
private theorem taylorRoundAccList_succ
    (excess a0 a1 a2 a3 a4 a5 : Word) (j : Nat) :
    taylorRoundAccList excess a0 a1 a2 a3 a4 a5 (j + 1) =
      match taylorRoundAccList excess a0 a1 a2 a3 a4 a5 j with
      | [x0, x1, x2, x3, x4, x5] =>
          taylorRoundBackedgeQuotient (taylorLoopIndex j) excess x0 x1 x2 x3 x4 x5
      | _ => [0, 0, 0, 0, 0, 0] := by
  rfl

/-- The sum list at round `j + 1` is the ripple of round `j`'s accumulator
    against round `j`'s sum. -/
private theorem taylorRoundSumList_succ
    (excess a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word) (j : Nat) :
    taylorRoundSumList excess a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 (j + 1) =
      match taylorRoundAccList excess a0 a1 a2 a3 a4 a5 j,
        taylorRoundSumList excess a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 j with
      | [x0, x1, x2, x3, x4, x5], [z0, z1, z2, z3, z4, z5] =>
          taylorRoundBackedgeSum x0 x1 x2 x3 x4 x5 z0 z1 z2 z3 z4 z5
      | _, _ => [0, 0, 0, 0, 0, 0] := by
  rfl


/-- The round-`j` invariant with the limbs the loop actually holds there. -/
@[reducible] private def taylorLoopInvariant
    (newSp excess outPtr : Word) (vals : Reg → Word) (evenBase oddBase : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion) (j : Nat) : Assertion :=
  taylorLoopInvParityAt newSp excess outPtr vals j (taylorLoopIndex j) evenBase oddBase
    (taylorRoundAccList excess a0 a1 a2 a3 a4 a5 j)
    (taylorRoundProdList excess a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 j)
    (taylorRoundSumList excess a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 j)
    (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) **
    (.x0 ↦ᵣ (0 : Word))

/-- The two exit-divide tail posts of the terminal round, with the `x0` rider
    factored out (the terminal continuation drops it).  At the terminal round
    `495` the parity is odd, so the accumulator limbs live in the second
    physical buffer and the `a`/`p` arguments are swapped. -/
@[reducible] private def taylorRoundTerminalTail
    (j : Nat) (newSp excess outPtr iVal evenBase oddBase : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion) : List (Word × Assertion) :=
  let q0 : Word := exitdivQ0 s0 s1 s2 s3 s4 s5
  let q1 : Word := exitdivQ1 s0 s1 s2 s3 s4 s5
  let q2 : Word := exitdivQ2 s0 s1 s2 s3 s4 s5
  let q3 : Word := exitdivQ3 s0 s1 s2 s3 s4 s5
  let q4 : Word := exitdivQ4 s0 s1 s2 s3 s4 s5
  let q5 : Word := exitdivQ5 s0 s1 s2 s3 s4 s5
  [(PriceK + 968,
    tailStatus1NoX0 newSp excess outPtr vals
      q0 q1 q2 q3 q4 q5 o0 o1 o2 o3
      p0 p1 p2 p3 p4 p5 a0 a1 a2 a3 a4 a5
      (exitdivZ0 s0 s1 s2 s3 s4 s5).2.1 iVal
      (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase)
      q0 (0 : Word)
      (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) +
        signExtend12 (-8 : BitVec 12))
      (lcnt 5 + signExtend12 (-1 : BitVec 12)) FR),
   (PriceK + 968,
    tailStatus0BytesNoX0 newSp excess outPtr vals
      q0 q1 q2 q3 q4 q5
      p0 p1 p2 p3 p4 p5 a0 a1 a2 a3 a4 a5 iVal
      (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase)
      (lcnt 5 + signExtend12 (-1 : BitVec 12)) FR)]

/-- The exit list the indexed fold sequences: the non-backedge exits of round
    `j` for `j < 495`, and the closed terminal-round exits at `495`.  The limb
    words are the values the loop actually holds at round `j`. -/
@[irreducible] private def taylorLoopFoldTerminal
    (newSp excess outPtr evenBase oddBase : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion) (j : Nat) : List (Word × Assertion) :=
  match taylorRoundAccList excess a0 a1 a2 a3 a4 a5 j,
    taylorRoundProdList excess a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 j,
    taylorRoundSumList excess a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 j with
  | [a0', a1', a2', a3', a4', a5'],
    [p0', p1', p2', p3', p4', p5'],
    [s0', s1', s2', s3', s4', s5'] =>
      if j < 495 then
        taylorRoundNoBackedge j newSp excess outPtr (taylorLoopIndex j) evenBase oddBase vals
          a0' a1' a2' a3' a4' a5' p0' p1' p2' p3' p4' p5' s0' s1' s2' s3' s4' s5' o0 o1 o2 o3 FR
      else
        taylorRoundTerminalTail j newSp excess outPtr (taylorLoopIndex j) evenBase oddBase vals
          a0' a1' a2' a3' a4' a5' p0' p1' p2' p3' p4' p5' s0' s1' s2' s3' s4' s5' o0 o1 o2 o3 FR ++
          [(PriceK + 968,
            terminalStatus1Any newSp excess outPtr (taylorLoopIndex j)
              (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
              (roundAccum a0' a1' a2' a3' a4' a5')
              a0' a1' a2' a3' a4' a5' p0' p1' p2' p3' p4' p5' s0' s1' s2' s3' s4' s5'
              (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))]
  | _, _, _ => []

/-- The round-`j` backedge, instantiated at the round-`j` limb words, is
    exactly the next-round invariant. -/
private theorem taylorRoundBackedge_eq_invariant_at_words
    (newSp excess outPtr evenBase oddBase : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion) (j : Nat)
    (a0' a1' a2' a3' a4' a5' s0' s1' s2' s3' s4' s5' : Word)
    (hAcc : taylorRoundAccList excess a0 a1 a2 a3 a4 a5 j = [a0', a1', a2', a3', a4', a5'])
    (hSum : taylorRoundSumList excess a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 j = [s0', s1', s2', s3', s4', s5']) :
    taylorRoundBackedge j newSp excess outPtr evenBase oddBase vals
      a0' a1' a2' a3' a4' a5' s0' s1' s2' s3' s4' s5'
      (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) =
    taylorLoopInvariant newSp excess outPtr vals evenBase oddBase
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR (j + 1) := by
  rw [taylorRoundBackedge]
  unfold taylorLoopInvariant
  have h1 : taylorRoundBackedgeQuotient (taylorLoopIndex j) excess a0' a1' a2' a3' a4' a5' =
      taylorRoundAccList excess a0 a1 a2 a3 a4 a5 (j + 1) := by
    rw [taylorRoundAccList_succ, hAcc]
  have h2 : ([a0', a1', a2', a3', a4', a5'] : List Word) =
      taylorRoundProdList excess a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 (j + 1) := by
    simp [taylorRoundProdList, hAcc]
  have h3 : taylorRoundBackedgeSum a0' a1' a2' a3' a4' a5' s0' s1' s2' s3' s4' s5' =
      taylorRoundSumList excess a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 (j + 1) := by
    rw [taylorRoundSumList_succ, hAcc, hSum]
  rw [h1, h2, h3]

/-- The per-round hypothesis of the indexed fold: one round from `taylorLoopInvariant j`
    exits on the non-backedge posts or continues to `taylorLoopInvariant (j + 1)`. -/
private theorem taylor_round_hround
    (newSp excess outPtr evenBase oddBase : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion)
    (hEvenBase : evenBase = newSp + signExtend12 (64 : BitVec 12))
    (hOddBase : oddBase = newSp + signExtend12 (112 : BitVec 12))
    (hSumAlign : (newSp + signExtend12 (160 : BitVec 12)).toNat % 8 = 0)
    (hOutAlign : outPtr.toNat % 8 = 0)
    (hSumRange : (newSp + signExtend12 (160 : BitVec 12)).toNat + 40 < 2 ^ 64)
    (hOutRange : outPtr.toNat + 32 < 2 ^ 64)
    (hSumValid : ∀ i < 32,
      isValidByteAccess ((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 i) = true)
    (hOutValid : ∀ i < 32, isValidByteAccess (outPtr + BitVec.ofNat 64 i) = true)
    (hFR : FR.pcFree) :
    ∀ j, j < 495 →
      cpsNBranchWithin
        (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (PriceK + 144) priceCode
        (taylorLoopInvariant newSp excess outPtr vals evenBase oddBase
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR j)
        (taylorLoopFoldTerminal newSp excess outPtr evenBase oddBase vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR j ++
          [(PriceK + 144,
            taylorLoopInvariant newSp excess outPtr vals evenBase oddBase
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR (j + 1))]) := by
  intro j hj
  rcases length_six_eq (taylorRoundAccList excess a0 a1 a2 a3 a4 a5 j)
    (taylorRoundAccList_length excess a0 a1 a2 a3 a4 a5 j) with ⟨a0', a1', a2', a3', a4', a5', hAcc⟩
  rcases length_six_eq (taylorRoundProdList excess a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 j)
    (taylorRoundProdList_length excess a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 j) with
    ⟨p0', p1', p2', p3', p4', p5', hProd⟩
  rcases length_six_eq (taylorRoundSumList excess a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 j)
    (taylorRoundSumList_length excess a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 j) with
    ⟨s0', s1', s2', s3', s4', s5', hSum⟩
  have hT : taylorLoopFoldTerminal newSp excess outPtr evenBase oddBase vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR j =
    taylorRoundNoBackedge j newSp excess outPtr (taylorLoopIndex j) evenBase oddBase vals
      a0' a1' a2' a3' a4' a5' p0' p1' p2' p3' p4' p5' s0' s1' s2' s3' s4' s5' o0 o1 o2 o3 FR := by
    unfold taylorLoopFoldTerminal
    rw [hAcc, hProd, hSum]
    simp [hj]
  have hA := taylor_round_invariant_to_parity
    newSp excess outPtr evenBase oddBase vals j
    a0' a1' a2' a3' a4' a5' p0' p1' p2' p3' p4' p5' s0' s1' s2' s3' s4' s5'
    o0 o1 o2 o3 FR hEvenBase hOddBase hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid hFR
  have hPre : taylorLoopInvariant newSp excess outPtr vals evenBase oddBase
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR j =
    (taylorLoopInvParityAt newSp excess outPtr vals j (taylorLoopIndex j) evenBase oddBase
      [a0', a1', a2', a3', a4', a5'] [p0', p1', p2', p3', p4', p5'] [s0', s1', s2', s3', s4', s5']
      (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) **
      (.x0 ↦ᵣ (0 : Word))) := by
    unfold taylorLoopInvariant
    rw [hAcc, hProd, hSum]
  have hA' := cpsNBranchWithin_weaken_pre
    (P := (taylorLoopInvParityAt newSp excess outPtr vals j (taylorLoopIndex j) evenBase oddBase
      [a0', a1', a2', a3', a4', a5'] [p0', p1', p2', p3', p4', p5'] [s0', s1', s2', s3', s4', s5']
      (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) **
      (.x0 ↦ᵣ (0 : Word))))
    (P' := taylorLoopInvariant newSp excess outPtr vals evenBase oddBase
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR j)
    (fun h hh => hPre ▸ hh) hA
  refine cpsNBranchWithin_weaken_posts hA' ?_
  intro ex hex
  have hEq : terminal j newSp excess outPtr (taylorLoopIndex j) evenBase oddBase vals
      a0' a1' a2' a3' a4' a5' p0' p1' p2' p3' p4' p5' s0' s1' s2' s3' s4' s5' o0 o1 o2 o3 FR =
    taylorRoundNoBackedge j newSp excess outPtr (taylorLoopIndex j) evenBase oddBase vals
      a0' a1' a2' a3' a4' a5' p0' p1' p2' p3' p4' p5' s0' s1' s2' s3' s4' s5' o0 o1 o2 o3 FR ++
      [(PriceK + 144,
        taylorRoundBackedge j newSp excess outPtr evenBase oddBase vals
          a0' a1' a2' a3' a4' a5' s0' s1' s2' s3' s4' s5'
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))] :=
    terminal_eq_append_backedge (j := j) (newSp := newSp) (excess := excess) (outPtr := outPtr)
      (iVal := taylorLoopIndex j) (evenBase := evenBase) (oddBase := oddBase) (vals := vals)
      (a0 := a0') (a1 := a1') (a2 := a2') (a3 := a3') (a4 := a4') (a5 := a5')
      (p0 := p0') (p1 := p1') (p2 := p2') (p3 := p3') (p4 := p4') (p5 := p5')
      (s0 := s0') (s1 := s1') (s2 := s2') (s3 := s3') (s4 := s4') (s5 := s5')
      (o0 := o0) (o1 := o1) (o2 := o2) (o3 := o3) (FR := FR)
  rcases List.mem_append.mp (hEq ▸ hex) with hexb | hexlast
  · refine ⟨ex, ?_, rfl, fun _ hx => hx⟩
    exact List.mem_append.mpr (Or.inl (hT.symm ▸ hexb))
  · simp only [List.mem_singleton] at hexlast
    subst ex
    refine ⟨(PriceK + 144, taylorLoopInvariant newSp excess outPtr vals evenBase oddBase
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR (j + 1)), ?_, rfl, ?_⟩
    · exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    · intro h hh
      exact (taylorRoundBackedge_eq_invariant_at_words newSp excess outPtr evenBase oddBase vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR j
        a0' a1' a2' a3' a4' a5' s0' s1' s2' s3' s4' s5' hAcc hSum) ▸ hh

/-! ## Step (C): the terminal round

The indexed fold's final continuation runs the terminal round (iVal = 496).
Step (A)'s round theorems carry the even parity base in `evenBase`; the
terminal round at index `495` is at *odd* parity, so the accumulator lives in
the second physical buffer and the exit-divide tail is taken with the
`a`/`p` limb arguments swapped.  The repository's
`taylor_round_terminal_496_from_parity_exitdiv_tail_core` pins the even
instance (`parityBuffer 495 evenBase oddBase = newSp + 64`); round `495` of the
fold instead requires `AB = newSp + 112`.  The swapped continuation below is
the odd instance that matches the fold's round-`495` state. -/

/-- The odd-parity exit-divide continuation of the terminal round: `AB` is the
    `+112` buffer, `PB` the `+64` buffer, and the exit-divide tail is taken
    with swapped `a`/`p` limbs.  Mirrors `terminal_zero_any_to_exitdiv`. -/
private theorem taylor_x0Free_sepConj {P Q : Assertion}
    (hP : x0FreeAssertion P) (hQ : x0FreeAssertion Q) : x0FreeAssertion (P ** Q) := by
  intro h hh
  obtain ⟨h1, h2, hd, hu, hp, hq⟩ := hh
  have h1x := hP h1 hp
  have h2x := hQ h2 hq
  rw [← hu]
  simp [PartialState.union, h1x, h2x]

private theorem taylor_x0Free_regIs {r : Reg} {v : Word} (hr : r ≠ .x0) :
    x0FreeAssertion (r ↦ᵣ v) := by
  intro h hh
  rw [hh]
  simp [PartialState.singletonReg, Ne.symm hr]

private theorem taylor_x0Free_memIs {a v : Word} : x0FreeAssertion (a ↦ₘ v) := by
  intro h hh
  rw [hh.1]
  rfl

private theorem taylor_x0Free_frameSlotsSaved
    (frame : FrameDesc) (newSp : Word) (vals : Reg → Word) :
    x0FreeAssertion (frameSlotsSaved frame newSp vals) := by
  induction frame with
  | nil => intro h hh; rw [hh]; rfl
  | cons p rest ih =>
      simpa only [frameSlotsSaved_cons] using taylor_x0Free_sepConj taylor_x0Free_memIs ih

private theorem taylor_x0Free_pure {P : Prop} : x0FreeAssertion (⌜P⌝) := by
  intro h hh
  rw [hh.1]
  rfl

private theorem taylor_x0Free_exitdivOutputCells
    (outPtr o0 o1 o2 o3 : Word) (FR : Assertion) (hFR : x0FreeAssertion FR) :
    x0FreeAssertion (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) := by
  unfold exitdivOutputCells
  repeat' first
    | apply taylor_x0Free_sepConj
    | exact taylor_x0Free_memIs
    | assumption

private theorem taylor_x0Free_roundZeroNoX0
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (w a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : x0FreeAssertion FR) :
    x0FreeAssertion (roundZeroNoX0 newSp excess outPtr iVal AB PB vals w
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR) := by
  unfold roundZeroNoX0 roundFrame
  repeat' first
    | apply taylor_x0Free_sepConj
    | exact taylor_x0Free_regIs (by decide)
    | exact taylor_x0Free_memIs
    | exact taylor_x0Free_frameSlotsSaved _ _ _
    | exact taylor_x0Free_pure
    | assumption

private theorem terminal_zero_any_to_exitdiv_swapped
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion)
    (hFR : FR.pcFree) (hFRx0 : x0FreeAssertion FR)
    (hAB : AB = newSp + signExtend12 (112 : BitVec 12))
    (hPB : PB = newSp + signExtend12 (64 : BitVec 12))
    {exits : List (Word × Assertion)}
    (hTail : cpsNBranchWithin 296 (PriceK + 900) priceCode
      (exitdivTailPre newSp excess outPtr iVal vals
        p0 p1 p2 p3 p4 p5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
        o0 o1 o2 o3 AB PB FR)
      (exits.map (fun ex => (ex.1, ex.2 ** regIs .x0 (0 : Word))))) :
    cpsNBranchWithin 4183 (PriceK + 804) priceCode
      (terminalZeroAny newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
        s2 s3 s4 s5 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
      exits := by
  let FR0 : Assertion := exitdivOutputCells outPtr o0 o1 o2 o3 ** FR
  have hFR0Free : x0FreeAssertion FR0 := by
    unfold FR0
    exact taylor_x0Free_exitdivOutputCells outPtr o0 o1 o2 o3 FR hFRx0
  have hZero : ∀ v7 v28 v29 v30 v31 : Word,
      cpsNBranchWithin 4183 (PriceK + 804) priceCode
        (roundZeroNoX0 newSp excess outPtr iVal AB PB vals
          (roundAccum a0 a1 a2 a3 a4 a5)
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
          s2 s3 s4 s5 v7 v28 v29 v30 v31 FR0) exits := by
    intro v7 v28 v29 v30 v31
    have hZeroX := round_zero_exitdiv_tail_swapped
      newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
      s2 s3 s4 s5 v7 v28 v29 v30 v31 o0 o1 o2 o3 FR hFR hAB hPB
      (exits := exits.map (fun ex => (ex.1, ex.2 ** regIs .x0 (0 : Word))))
      hTail
    have hZeroX' :
        cpsNBranchWithin 4183 (PriceK + 804) priceCode
          ((roundZeroNoX0 newSp excess outPtr iVal AB PB vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
            s2 s3 s4 s5 v7 v28 v29 v30 v31 FR0) **
            regIs .x0 (0 : Word))
          (exits.map (fun ex => (ex.1, ex.2 ** regIs .x0 (0 : Word)))) := by
      refine cpsNBranchWithin_weaken_pre ?_ hZeroX
      intro h hp
      simp only [roundZeroNoX0, roundZero] at hp ⊢
      xperm_hyp hp
    have hZeroFree := taylor_x0Free_roundZeroNoX0
      newSp excess outPtr iVal AB PB vals
      (roundAccum a0 a1 a2 a3 a4 a5)
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
      s2 s3 s4 s5 v7 v28 v29 v30 v31 FR0 hFR0Free
    have hDrop := cpsNBranchWithin_drop_x0
      (P := roundZeroNoX0 newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
        s2 s3 s4 s5 v7 v28 v29 v30 v31 FR0)
      (exits := exits) hZeroFree hZeroX'
    simpa [FR0] using hDrop
  intro R hR s hcr hP hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hP
  obtain ⟨v7, v28, v29, v30, v31, hv⟩ := hPP
  exact hZero v7 v28 v29 v30 v31 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu, hv, hRb⟩ hpc

/-- The closed terminal round at index `495` (odd parity): the seventeen-step
    terminal round followed by the odd exit-divide tail, exposing the concrete
    exit list `taylorRoundTerminalTail 495 ++ [terminalStatus1Any]`. -/
private theorem taylor_round_terminal_495_closed
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (evenBase oddBase : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion)
    (hFR : FR.pcFree) (hFRx0 : x0FreeAssertion FR)
    (hEvenBase : evenBase = newSp + signExtend12 (64 : BitVec 12))
    (hOddBase : oddBase = newSp + signExtend12 (112 : BitVec 12))
    (hSumAlign : (newSp + signExtend12 (160 : BitVec 12)).toNat % 8 = 0)
    (hOutAlign : outPtr.toNat % 8 = 0)
    (hSumRange : (newSp + signExtend12 (160 : BitVec 12)).toNat + 40 < 2 ^ 64)
    (hOutRange : outPtr.toNat + 32 < 2 ^ 64)
    (hSumValid : ∀ i < 32,
      isValidByteAccess ((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 i) = true)
    (hOutValid : ∀ i < 32, isValidByteAccess (outPtr + BitVec.ofNat 64 i) = true) :
    cpsNBranchWithin (17 + 4183) (PriceK + 144) priceCode
      (taylorLoopInvParityAt newSp excess outPtr vals 495 (496 : Word)
        evenBase oddBase [a0, a1, a2, a3, a4, a5]
        [p0, p1, p2, p3, p4, p5] [s0, s1, s2, s3, s4, s5]
        (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
      (taylorRoundTerminalTail 495 newSp excess outPtr (496 : Word) evenBase oddBase vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR ++
        [(PriceK + 968,
          terminalStatus1Any newSp excess outPtr (496 : Word)
            (parityBuffer 495 evenBase oddBase) (parityBuffer 495 oddBase evenBase) vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
            (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))]) := by
  let FR0 : Assertion := exitdivOutputCells outPtr o0 o1 o2 o3 ** FR
  let AB := parityBuffer 495 evenBase oddBase
  let PB := parityBuffer 495 oddBase evenBase
  let Q1 : Assertion :=
    tailStatus1NoX0 newSp excess outPtr vals
      (exitdivQ0 s0 s1 s2 s3 s4 s5) (exitdivQ1 s0 s1 s2 s3 s4 s5)
      (exitdivQ2 s0 s1 s2 s3 s4 s5) (exitdivQ3 s0 s1 s2 s3 s4 s5)
      (exitdivQ4 s0 s1 s2 s3 s4 s5) (exitdivQ5 s0 s1 s2 s3 s4 s5)
      o0 o1 o2 o3 p0 p1 p2 p3 p4 p5 a0 a1 a2 a3 a4 a5
      (exitdivZ0 s0 s1 s2 s3 s4 s5).2.1 (496 : Word) AB PB
      (exitdivQ0 s0 s1 s2 s3 s4 s5) (0 : Word)
      (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) +
        signExtend12 (-8 : BitVec 12)) (lcnt 5 + signExtend12 (-1 : BitVec 12)) FR
  let Q0 : Assertion :=
    tailStatus0BytesNoX0 newSp excess outPtr vals
      (exitdivQ0 s0 s1 s2 s3 s4 s5) (exitdivQ1 s0 s1 s2 s3 s4 s5)
      (exitdivQ2 s0 s1 s2 s3 s4 s5) (exitdivQ3 s0 s1 s2 s3 s4 s5)
      (exitdivQ4 s0 s1 s2 s3 s4 s5) (exitdivQ5 s0 s1 s2 s3 s4 s5)
      p0 p1 p2 p3 p4 p5 a0 a1 a2 a3 a4 a5 (496 : Word) AB PB
      (lcnt 5 + signExtend12 (-1 : BitVec 12)) FR
  let exits : List (Word × Assertion) := [(PriceK + 968, Q1), (PriceK + 968, Q0)]
  have hFR0 : FR0.pcFree := by
    unfold FR0
    pcFree
    exact hFR
  have hTail0 := exitdiv_tail_core_x0_split
    newSp excess outPtr (496 : Word) vals
    p0 p1 p2 p3 p4 p5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
    o0 o1 o2 o3 AB PB FR
    hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid hFR
  have hTail : cpsNBranchWithin 296 (PriceK + 900) priceCode
      (exitdivTailPre newSp excess outPtr (496 : Word) vals
        p0 p1 p2 p3 p4 p5 a0 a1 a2 a3 a4 a5 s0 s1
        s2 s3 s4 s5 o0 o1 o2 o3 AB PB FR)
      (exits.map (fun ex => (ex.1, ex.2 ** regIs .x0 (0 : Word)))) := by
    simpa [AB, PB, Q1, Q0, exits] using hTail0
  have hRound := taylor_round_terminal_496_from_parity
    newSp excess outPtr vals evenBase oddBase
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0 hFR0
  have hZero := terminal_zero_any_to_exitdiv_swapped
    newSp excess outPtr (496 : Word) AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    o0 o1 o2 o3 FR hFR hFRx0
    (show AB = newSp + signExtend12 (112 : BitVec 12) from by simp [AB, parityBuffer, hOddBase])
    (show PB = newSp + signExtend12 (64 : BitVec 12) from by simp [PB, parityBuffer, hEvenBase])
    hTail
  have hAll := nb_extend_head_same_cr hRound hZero
  simpa [FR0, exits, AB, PB, Q1, Q0, taylorRoundTerminalTail] using hAll

/-- The terminal-round hypothesis of the indexed fold: `taylorLoopFoldTerminal 495`
    is the closed terminal exit list reachable from `taylorLoopInvariant 495`. -/
private def exactAssertionT (h : PartialState) : Assertion := fun h' => h' = h

private theorem substate_left_unionT (h1 h2 : PartialState) : h1.SubStateOf (h1.union h2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r v hv; simp [PartialState.union, hv]
  · intro a v hv; simp [PartialState.union, hv]
  · intro a i hv; simp [PartialState.union, hv]
  · intro v hv; simp [PartialState.union, hv]
  · intro v hv; simp [PartialState.union, hv]
  · intro v hv; simp [PartialState.union, hv]
  · intro v hv; simp [PartialState.union, hv]

private theorem drop_x0_postT {Q R : Assertion} {hF : PartialState} {s : MachineState}
    (hR : R hF)
    (hpost : ((Q ** regIs .x0 0) ** exactAssertionT hF).holdsFor s) :
    (Q ** R).holdsFor s := by
  obtain ⟨htotal, hcompat, hassert⟩ := hpost
  obtain ⟨hq0, hf, hd, hun, hq0p, hfp⟩ := hassert
  change hf = hF at hfp
  subst hf
  obtain ⟨hq, h0, hd0, hun0, hqp, h0p⟩ := hq0p
  have hqsub : hq.SubStateOf hq0 := by
    rw [← hun0]
    exact substate_left_unionT hq h0
  have hqF : hq.Disjoint hF := PartialState.SubStateOf_Disjoint hd hqsub
  rw [← hun] at hcompat
  have ⟨hcq0, hcf⟩ := (PartialState.CompatibleWith_union hd).mp hcompat
  rw [← hun0] at hcq0
  have ⟨hcq, _⟩ := (PartialState.CompatibleWith_union hd0).mp hcq0
  exact ⟨hq.union hF, (PartialState.CompatibleWith_union hqF).mpr ⟨hcq, hcf⟩, hq, hF, hqF, rfl, hqp, hR⟩

private theorem drop_x0_holds {Q R : Assertion} {s : MachineState}
    (hQ : ((Q ** regIs .x0 (0 : Word)) ** R).holdsFor s) : (Q ** R).holdsFor s := by
  obtain ⟨htotal, hcompat, hassert⟩ := hQ
  obtain ⟨hq0, hR, hd, hun, hq0p, hRp⟩ := hassert
  have hIn : ((Q ** regIs .x0 (0 : Word)) ** exactAssertionT hR).holdsFor s :=
    ⟨htotal, hcompat, hq0, hR, hd, hun, hq0p, rfl⟩
  exact drop_x0_postT hRp hIn

/-- Attach the architectural-zero resource to the precondition, leaving the
    exit list unchanged.  The x0 is transferred to the caller frame and dropped
    from the final post, where the machine's hardwired zero makes it vacuous. -/
private theorem nbranch_attach_x0 {P : Assertion} {n : Nat} {entry : Word} {cr : CodeReq}
    {exits : List (Word × Assertion)}
    (h : cpsNBranchWithin n entry cr P exits) :
    cpsNBranchWithin n entry cr (P ** regIs .x0 (0 : Word)) exits := by
  intro R hR s hcr hPR hpc
  let R' : Assertion := regIs .x0 (0 : Word) ** R
  have hPR' : (P ** R').holdsFor s := by
    simpa only [R', sepConj_assoc'] using hPR
  have hR' : R'.pcFree := by
    unfold R'
    exact pcFree_sepConj (by pcFree) hR
  obtain ⟨k, hk, s', hstep, ex, hmem, hpc', hQ⟩ := h R' hR' s hcr hPR' hpc
  exact ⟨k, hk, s', hstep, ex, hmem, hpc',
    drop_x0_holds (by simpa only [R', sepConj_assoc'] using hQ)⟩

theorem taylor_round_htail
    (newSp excess outPtr evenBase oddBase : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion)
    (hEvenBase : evenBase = newSp + signExtend12 (64 : BitVec 12))
    (hOddBase : oddBase = newSp + signExtend12 (112 : BitVec 12))
    (hSumAlign : (newSp + signExtend12 (160 : BitVec 12)).toNat % 8 = 0)
    (hOutAlign : outPtr.toNat % 8 = 0)
    (hSumRange : (newSp + signExtend12 (160 : BitVec 12)).toNat + 40 < 2 ^ 64)
    (hOutRange : outPtr.toNat + 32 < 2 ^ 64)
    (hSumValid : ∀ i < 32,
      isValidByteAccess ((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 i) = true)
    (hOutValid : ∀ i < 32, isValidByteAccess (outPtr + BitVec.ofNat 64 i) = true)
    (hFR : FR.pcFree) (hFRx0 : x0FreeAssertion FR) :
    cpsNBranchWithin (17 + 4183) (PriceK + 144) priceCode
      (taylorLoopInvariant newSp excess outPtr vals evenBase oddBase
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR 495)
      (taylorLoopFoldTerminal newSp excess outPtr evenBase oddBase vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR 495) := by
  rcases length_six_eq (taylorRoundAccList excess a0 a1 a2 a3 a4 a5 495)
    (taylorRoundAccList_length excess a0 a1 a2 a3 a4 a5 495) with ⟨a0', a1', a2', a3', a4', a5', hAcc⟩
  rcases length_six_eq (taylorRoundProdList excess a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 495)
    (taylorRoundProdList_length excess a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 495) with
    ⟨p0', p1', p2', p3', p4', p5', hProd⟩
  rcases length_six_eq (taylorRoundSumList excess a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 495)
    (taylorRoundSumList_length excess a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 495) with
    ⟨s0', s1', s2', s3', s4', s5', hSum⟩
  have hT495 : taylorLoopFoldTerminal newSp excess outPtr evenBase oddBase vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR 495 =
    taylorRoundTerminalTail 495 newSp excess outPtr (taylorLoopIndex 495) evenBase oddBase vals
      a0' a1' a2' a3' a4' a5' p0' p1' p2' p3' p4' p5' s0' s1' s2' s3' s4' s5' o0 o1 o2 o3 FR ++
      [(PriceK + 968,
        terminalStatus1Any newSp excess outPtr (taylorLoopIndex 495)
          (parityBuffer 495 evenBase oddBase) (parityBuffer 495 oddBase evenBase) vals
          (roundAccum a0' a1' a2' a3' a4' a5')
          a0' a1' a2' a3' a4' a5' p0' p1' p2' p3' p4' p5' s0' s1' s2' s3' s4' s5'
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))] := by
    unfold taylorLoopFoldTerminal
    rw [hAcc, hProd, hSum]
    simp
  have hClosed := taylor_round_terminal_495_closed newSp excess outPtr vals evenBase oddBase
    a0' a1' a2' a3' a4' a5' p0' p1' p2' p3' p4' p5' s0' s1' s2' s3' s4' s5' o0 o1 o2 o3 FR
    hFR hFRx0 hEvenBase hOddBase hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
  have hPreEq : taylorLoopInvariant newSp excess outPtr vals evenBase oddBase
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR 495 =
    (taylorLoopInvParityAt newSp excess outPtr vals 495 (496 : Word) evenBase oddBase
      [a0', a1', a2', a3', a4', a5'] [p0', p1', p2', p3', p4', p5'] [s0', s1', s2', s3', s4', s5']
      (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) **
      (.x0 ↦ᵣ (0 : Word))) := by
    unfold taylorLoopInvariant
    rw [hAcc, hProd, hSum]
    rfl
  have hCl := nbranch_attach_x0 hClosed
  have hCl' := cpsNBranchWithin_weaken_pre
    (P := (taylorLoopInvParityAt newSp excess outPtr vals 495 (496 : Word) evenBase oddBase
      [a0', a1', a2', a3', a4', a5'] [p0', p1', p2', p3', p4', p5'] [s0', s1', s2', s3', s4', s5']
      (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) **
      (.x0 ↦ᵣ (0 : Word))))
    (P' := taylorLoopInvariant newSp excess outPtr vals evenBase oddBase
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR 495)
    (fun h hh => hPreEq ▸ hh) hCl
  exact hT495.symm ▸ hCl'

/-- The outer loop over 495 rounds folds the per-round round theorem and the
    terminal round into one triple from the round-`0` invariant. -/
theorem taylor_loop_invariant_fold
    (newSp excess outPtr evenBase oddBase : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion)
    (hEvenBase : evenBase = newSp + signExtend12 (64 : BitVec 12))
    (hOddBase : oddBase = newSp + signExtend12 (112 : BitVec 12))
    (hSumAlign : (newSp + signExtend12 (160 : BitVec 12)).toNat % 8 = 0)
    (hOutAlign : outPtr.toNat % 8 = 0)
    (hSumRange : (newSp + signExtend12 (160 : BitVec 12)).toNat + 40 < 2 ^ 64)
    (hOutRange : outPtr.toNat + 32 < 2 ^ 64)
    (hSumValid : ∀ i < 32,
      isValidByteAccess ((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 i) = true)
    (hOutValid : ∀ i < 32, isValidByteAccess (outPtr + BitVec.ofNat 64 i) = true)
    (hFR : FR.pcFree) (hFRx0 : x0FreeAssertion FR) :
    cpsNBranchWithin
      ((4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) * 495 + (17 + 4183))
      (PriceK + 144) priceCode
      (taylorLoopInvariant newSp excess outPtr vals evenBase oddBase
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR 0)
      ((List.range 495).flatMap (fun j =>
        taylorLoopFoldTerminal newSp excess outPtr evenBase oddBase vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR j) ++
        taylorLoopFoldTerminal newSp excess outPtr evenBase oddBase vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR 495) := by
  exact finite_nbranch_loop_spec_indexed
    (N := 495)
    (m := 4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
    (mLast := 17 + 4183)
    (hdr := PriceK + 144) (cr := priceCode)
    (inv := fun j => taylorLoopInvariant newSp excess outPtr vals evenBase oddBase
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR j)
    (terminal := fun j => taylorLoopFoldTerminal newSp excess outPtr evenBase oddBase vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR j)
    (hround := taylor_round_hround newSp excess outPtr evenBase oddBase vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR
      hEvenBase hOddBase hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid hFR)
    (htail := taylor_round_htail newSp excess outPtr evenBase oddBase vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR
      hEvenBase hOddBase hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid hFR hFRx0)

#check taylor_loop_invariant_fold
#print axioms taylor_loop_invariant_fold

end EvmAsm.Codegen.AmsterdamBlobGasPriceTaylorDischarge
