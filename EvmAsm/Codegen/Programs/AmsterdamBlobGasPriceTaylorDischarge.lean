/- Per-round invariant discharge for the Amsterdam blob gas price Taylor
   outer loop (#12851).  This is step (A) of the general taylorPriceContract
   discharge: one round of the linked source composition, stated on the
   parity-aware loop invariant and closing the QBACK backedge back into the
   next-round invariant.  Step (B) folds this with `finite_nbranch_loop_spec_indexed`. -/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14RoundQBackComposition
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14RoundComposition
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14Backedge
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14TerminalSpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody7Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody8Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceOuterSpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceU256Sat
import EvmAsm.Rv64.MemSat
import Batteries.Tactic.OpenPrivate

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

/-! ## The per-round terminal exit list

The linked source composition appends ten status-1 posts after the two
exit-divide tail posts and before the parity backedge.  Four of the ten posts
retain the concrete scratch values `v7 v28 v29 v30 v31`; the remaining six are
constant in those registers.  The `Any` variants hide the scratch witnesses so
the terminal list is a pure function of the round index and the limb contents,
which is what the finite outer fold needs. -/

@[reducible] def taylorRoundTerminalStatus1Any
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  fun h => ∃ v7 v28 v29 v30 v31 : Word,
    taylorRoundTerminalStatus1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR h

@[reducible] def taylorRoundSourceMul5Status1Any
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  fun h => ∃ v7 v28 v29 v30 v31 : Word,
    taylorRoundSourceMul5Status1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR h

@[reducible] def taylorRoundSourceMulFFStatus1Any
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  fun h => ∃ v7 v28 v29 v30 v31 : Word,
    taylorRoundSourceMulFFStatus1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR h

@[reducible] def taylorRoundSourceQOVFComputedStatus1Any
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  fun h => ∃ v7 v28 v29 v30 v31 : Word,
    taylorRoundSourceQOVFComputedStatus1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR h

/- The two exit-divide tail posts at even parity: the accumulator limbs
   (a-limbs) live at the `AB` buffer, the p-limbs at `PB`.  The `x0` rider is
   a separate separating conjunct, exactly as `exitdiv_tail_core_x0_split`
   emits it. -/
@[reducible] def taylorRoundTailPostsEven
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
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
      (exitdivZ0 s0 s1 s2 s3 s4 s5).2.1 iVal
      (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase)
      q0 (0 : Word)
      (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) +
        signExtend12 (-8 : BitVec 12))
      (lcnt 5 + signExtend12 (-1 : BitVec 12)) FR **
      (.x0 ↦ᵣ (0 : Word))),
   (PriceK + 968,
    tailStatus0BytesNoX0 newSp excess outPtr vals
      q0 q1 q2 q3 q4 q5
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 iVal
      (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase)
      (lcnt 5 + signExtend12 (-1 : BitVec 12)) FR **
      (.x0 ↦ᵣ (0 : Word)))]

/- The two exit-divide tail posts at odd parity: the p-limbs live at the `AB`
   buffer, the accumulator limbs at `PB`. -/
@[reducible] def taylorRoundTailPostsOdd
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
      (lcnt 5 + signExtend12 (-1 : BitVec 12)) FR **
      (.x0 ↦ᵣ (0 : Word))),
   (PriceK + 968,
    tailStatus0BytesNoX0 newSp excess outPtr vals
      q0 q1 q2 q3 q4 q5
      p0 p1 p2 p3 p4 p5 a0 a1 a2 a3 a4 a5 iVal
      (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase)
      (lcnt 5 + signExtend12 (-1 : BitVec 12)) FR **
      (.x0 ↦ᵣ (0 : Word)))]

/- The exit-divide tail posts, parity-selected.  `exitdiv_tail_core_x0_split`
   names the physical cells as its `a`/`p` arguments, so at odd `j` the limb
   order swaps exactly as the linked tail does. -/
@[reducible] def taylorRoundTailPosts
    (j : Nat) (newSp excess outPtr iVal evenBase oddBase : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion) : List (Word × Assertion) :=
  if j % 2 = 0 then
    taylorRoundTailPostsEven j newSp excess outPtr iVal evenBase oddBase vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR
  else
    taylorRoundTailPostsOdd j newSp excess outPtr iVal evenBase oddBase vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR

/- The QBACK backedge post as the source composition emits it: the next-round
   invariant with the concrete `iVal + 1` index and the `x0` rider. -/
@[reducible] private def taylorRoundBackedgePinned
    (j : Nat) (newSp excess outPtr iVal evenBase oddBase : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word)
    (FR0 : Assertion) : Assertion :=
  taylorLoopInvParityAt newSp excess outPtr vals (j + 1)
    (iVal + signExtend12 (1 : BitVec 12)) evenBase oddBase
    (taylorRoundBackedgeQuotient iVal excess a0 a1 a2 a3 a4 a5)
    [a0, a1, a2, a3, a4, a5]
    (taylorRoundBackedgeSum a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) FR0 **
    (.x0 ↦ᵣ (0 : Word))

/- The QBACK backedge post in the loop-index form: `taylorLoopIndex (j + 1)`. -/
@[reducible] def taylorRoundBackedge
    (j : Nat) (newSp excess outPtr evenBase oddBase : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word)
    (FR0 : Assertion) : Assertion :=
  taylorLoopInvParityAt newSp excess outPtr vals (j + 1)
    (taylorLoopIndex (j + 1)) evenBase oddBase
    (taylorRoundBackedgeQuotient (taylorLoopIndex j) excess a0 a1 a2 a3 a4 a5)
    [a0, a1, a2, a3, a4, a5]
    (taylorRoundBackedgeSum a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) FR0 **
    (.x0 ↦ᵣ (0 : Word))

/- The ten status-1 posts with the retained scratch values still concrete,
   followed by the pinned backedge.  `FR0` carries the four output cells,
   matching the source composition's `exitdivOutputCells outPtr o0 o1 o2 o3 ** FR`. -/
@[reducible] private def taylorRoundPinnedStatus
    (j : Nat) (newSp excess outPtr iVal evenBase oddBase : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR0 : Assertion) : List (Word × Assertion) :=
  [(PriceK + 968,
    taylorRoundTerminalStatus1 newSp excess outPtr iVal
      (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR0),
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
    taylorRoundSourceMul5Status1 newSp excess outPtr iVal
      (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR0),
   (PriceK + 968,
    taylorRoundSourceMulFFStatus1 newSp excess outPtr iVal
      (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR0),
   (PriceK + 968,
    taylorRoundSourceQOVFComputedStatus1 newSp excess outPtr iVal
      (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
      a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR0),
   (PriceK + 144,
    taylorRoundBackedgePinned j newSp excess outPtr iVal evenBase oddBase vals
      a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 FR0)]

/- The ten status-1 posts with the retained scratch values hidden
   existentially, followed by the loop-index backedge. -/
@[reducible] def taylorRoundAnyStatus
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
      a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 FR0),
   (PriceK + 144,
    taylorRoundBackedge j newSp excess outPtr evenBase oddBase vals
      a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 FR0)]

/- The full per-round terminal list: the two exit-divide tail posts, the ten
   status-1 posts, and the backedge. -/
@[reducible] def terminal
    (j : Nat) (newSp excess outPtr iVal evenBase oddBase : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion) : List (Word × Assertion) :=
  let FR0 : Assertion := exitdivOutputCells outPtr o0 o1 o2 o3 ** FR
  taylorRoundTailPosts j newSp excess outPtr iVal evenBase oddBase vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR ++
  taylorRoundAnyStatus j newSp excess outPtr iVal evenBase oddBase vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0

/- `taylorRoundSourcePre` without the seven owned scratch registers.  The
   seven registers are lifted by the bulk N-branch ownership adapter, so the
   family theorem exposes only this non-temp core plus the owned tokens. -/
@[reducible] def taylorRoundSourcePreNoTemps
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  (regIs .x2 newSp) ** (regIs .x1 (vals .x1)) **
  (regIs .x10 excess) ** (regIs .x11 outPtr) **
  (regIs .x8 excess) ** (regIs .x9 taylorDW) **
  (regIs .x18 iVal) ** (regIs .x19 AB) **
  (regIs .x20 PB) ** (regIs .x21 outPtr) **
  (regIs .x22 (newSp + signExtend12 (160 : BitVec 12))) **
  (regIs .x0 0) **
  frameSlotsSaved priceFrame newSp vals **
  (memIs (AB + signExtend12 (0 : BitVec 12)) a0) **
  (memIs (AB + signExtend12 (8 : BitVec 12)) a1) **
  (memIs (AB + signExtend12 (16 : BitVec 12)) a2) **
  (memIs (AB + signExtend12 (24 : BitVec 12)) a3) **
  (memIs (AB + signExtend12 (32 : BitVec 12)) a4) **
  (memIs (AB + signExtend12 (40 : BitVec 12)) a5) **
  (memIs (PB + signExtend12 (0 : BitVec 12)) p0) **
  (memIs (PB + signExtend12 (8 : BitVec 12)) p1) **
  (memIs (PB + signExtend12 (16 : BitVec 12)) p2) **
  (memIs (PB + signExtend12 (24 : BitVec 12)) p3) **
  (memIs (PB + signExtend12 (32 : BitVec 12)) p4) **
  (memIs (PB + signExtend12 (40 : BitVec 12)) p5) **
  (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) s0) **
  (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) s1) **
  (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) s2) **
  (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) s3) **
  (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) s4) **
  (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) s5) ** FR

/- The bulk N-branch ownership lift for exactly the seven scratch registers.
   The library provides a nine-register version; this seven-register adapter
   matches K70's round exactly. -/
private theorem nbranch_regOwn7
    {n : Nat} {entry : Word} {r1 r2 r3 r4 r5 r6 r7 : Reg}
    {P : Assertion} {exits : List (Word × Assertion)} {cr : CodeReq}
    (h : ∀ v1 v2 v3 v4 v5 v6 v7, cpsNBranchWithin n entry cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) **
       (r4 ↦ᵣ v4) ** (r5 ↦ᵣ v5) ** (r6 ↦ᵣ v6) **
       (r7 ↦ᵣ v7)) exits) :
    cpsNBranchWithin n entry cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 **
       regOwn r4 ** regOwn r5 ** regOwn r6 ** regOwn r7) exits := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨v3, hv3⟩, hO4⟩ := hO3
  obtain ⟨g8, g9, d5, u5, ⟨v4, hv4⟩, hO5⟩ := hO4
  obtain ⟨g10, g11, d6, u6, ⟨v5, hv5⟩, hO6⟩ := hO5
  obtain ⟨g12, g13, d7, u7, ⟨v6, hv6⟩, ⟨v7, hv7⟩⟩ := hO6
  exact h v1 v2 v3 v4 v5 v6 v7 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP0, g2, g3, d2, u2, hv1,
       g4, g5, d3, u3, hv2, g6, g7, d4, u4, hv3,
       g8, g9, d5, u5, hv4, g10, g11, d6, u6, hv5,
       g12, g13, d7, u7, hv6, hv7⟩, hRb⟩ hpc

/- The linked exit-divide tail at either parity, on the fixed two-post list
   `taylorRoundTailPosts`.  This is the `round_zero_from_parity_tail_core`
   existential unwrapped to a concrete exit list, so the per-round theorem
   can close against the named `terminal` list. -/
private theorem round_zero_from_parity_tail_fixed
    (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (j : Nat) (evenBase oddBase : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word)
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
    cpsNBranchWithin 4183 (PriceK + 804) priceCode
      (roundZero newSp excess outPtr iVal
        (parityBuffer j evenBase oddBase)
        (parityBuffer j oddBase evenBase) vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31
        (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
      (taylorRoundTailPosts j newSp excess outPtr iVal evenBase oddBase vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR) := by
  by_cases h_even : j % 2 = 0
  · have hAB : parityBuffer j evenBase oddBase =
        newSp + signExtend12 (64 : BitVec 12) := by
      simp [parityBuffer, h_even, hEvenBase]
    have hPB : parityBuffer j oddBase evenBase =
        newSp + signExtend12 (112 : BitVec 12) := by
      simp [parityBuffer, h_even, hOddBase]
    have hTail := exitdiv_tail_core_x0_split
      newSp excess outPtr iVal vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      o0 o1 o2 o3 (parityBuffer j evenBase oddBase)
      (parityBuffer j oddBase evenBase) FR
      hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid hFR
    have hTailEq : taylorRoundTailPosts j newSp excess outPtr iVal evenBase oddBase vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR =
        taylorRoundTailPostsEven j newSp excess outPtr iVal evenBase oddBase vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR := by
      simp [taylorRoundTailPosts, h_even]
    have hZero := round_zero_exitdiv_tail
      newSp excess outPtr iVal
      (parityBuffer j evenBase oddBase)
      (parityBuffer j oddBase evenBase) vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 o0 o1 o2 o3 FR hFR hAB hPB
      (exits := taylorRoundTailPostsEven j newSp excess outPtr iVal evenBase oddBase vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR)
      hTail
    rw [hTailEq]
    exact hZero
  · have h_odd : j % 2 = 1 := by omega
    have hAB : parityBuffer j evenBase oddBase =
        newSp + signExtend12 (112 : BitVec 12) := by
      simp [parityBuffer, h_odd, hOddBase]
    have hPB : parityBuffer j oddBase evenBase =
        newSp + signExtend12 (64 : BitVec 12) := by
      simp [parityBuffer, h_odd, hEvenBase]
    have hTail := exitdiv_tail_core_x0_split
      newSp excess outPtr iVal vals
      p0 p1 p2 p3 p4 p5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
      o0 o1 o2 o3 (parityBuffer j evenBase oddBase)
      (parityBuffer j oddBase evenBase) FR
      hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid hFR
    have hTailEq : taylorRoundTailPosts j newSp excess outPtr iVal evenBase oddBase vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR =
        taylorRoundTailPostsOdd j newSp excess outPtr iVal evenBase oddBase vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR := by
      simp [taylorRoundTailPosts, h_odd]
    have hZero := round_zero_exitdiv_tail_swapped
      newSp excess outPtr iVal
      (parityBuffer j evenBase oddBase)
      (parityBuffer j oddBase evenBase) vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 o0 o1 o2 o3 FR hFR hAB hPB
      (exits := taylorRoundTailPostsOdd j newSp excess outPtr iVal evenBase oddBase vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR)
      hTail
    rw [hTailEq]
    exact hZero

/-- One outer-loop round from the parity-aware invariant: the source round
    with the exit-divide tail, the ten status-1 posts, and the QBACK backedge
    closed back into the `(j + 1)` invariant.  The step bound is the linked
    `taylor_round_source_full_status1_to_parity` bound. -/
theorem taylor_round_invariant_to_parity
    (newSp excess outPtr evenBase oddBase : Word) (vals : Reg → Word)
    (j : Nat)
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
    cpsNBranchWithin
        (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (PriceK + 144) priceCode
        (taylorLoopInvParityAt newSp excess outPtr vals j (taylorLoopIndex j)
          evenBase oddBase [a0, a1, a2, a3, a4, a5]
          [p0, p1, p2, p3, p4, p5] [s0, s1, s2, s3, s4, s5]
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) **
          (.x0 ↦ᵣ (0 : Word)))
        (terminal j newSp excess outPtr (taylorLoopIndex j) evenBase oddBase vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          o0 o1 o2 o3 FR) := by
  let exits : List (Word × Assertion) :=
    terminal j newSp excess outPtr (taylorLoopIndex j) evenBase oddBase vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR
  have hse : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hPinned : ∀ v5 v6 v7 v28 v29 v30 v31 : Word,
      cpsNBranchWithin
        (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
        (taylorRoundTailPosts j newSp excess outPtr (taylorLoopIndex j) evenBase oddBase vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR ++
          taylorRoundPinnedStatus j newSp excess outPtr (taylorLoopIndex j)
            evenBase oddBase vals
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31
            (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) := by
    intro v5 v6 v7 v28 v29 v30 v31
    have hZero := round_zero_from_parity_tail_fixed
      newSp excess outPtr (taylorLoopIndex j) vals j evenBase oddBase
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 o0 o1 o2 o3 FR
      hEvenBase hOddBase hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid hFR
    simpa only [taylorRoundPinnedStatus, taylorRoundBackedgePinned] using
      (taylor_round_source_full_status1_to_parity
        newSp excess outPtr (taylorLoopIndex j)
        (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals j evenBase oddBase
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v5 v6 v7 v28 v29 v30 v31 o0 o1 o2 o3 FR hFR rfl rfl
        (exits := taylorRoundTailPosts j newSp excess outPtr (taylorLoopIndex j) evenBase oddBase vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR)
        hZero)
  have hStatusWeak : ∀ (v7 v28 v29 v30 v31 : Word) (ex : Word × Assertion),
      ex ∈ [(PriceK + 968,
        taylorRoundTerminalStatus1 newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 968,
        taylorRoundCarryStatus1 newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 968,
        taylorRoundSourceMul0Status1 newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 968,
        taylorRoundSourceMul1Status1 newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 968,
        taylorRoundSourceMul2Status1 newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 968,
        taylorRoundSourceMul3Status1 newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 968,
        taylorRoundSourceMul4Status1 newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 968,
        taylorRoundSourceMul5Status1 newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 968,
        taylorRoundSourceMulFFStatus1 newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 968,
        taylorRoundSourceQOVFComputedStatus1 newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 144,
        taylorRoundBackedgePinned j newSp excess outPtr (taylorLoopIndex j)
          evenBase oddBase vals
          a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))] →
      ∃ ex' ∈
      [(PriceK + 968,
        taylorRoundTerminalStatus1Any newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 968,
        taylorRoundCarryStatus1 newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 968,
        taylorRoundSourceMul0Status1 newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 968,
        taylorRoundSourceMul1Status1 newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 968,
        taylorRoundSourceMul2Status1 newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 968,
        taylorRoundSourceMul3Status1 newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 968,
        taylorRoundSourceMul4Status1 newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 968,
        taylorRoundSourceMul5Status1Any newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 968,
        taylorRoundSourceMulFFStatus1Any newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 968,
        taylorRoundSourceQOVFComputedStatus1Any newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
       (PriceK + 144,
        taylorRoundBackedge j newSp excess outPtr evenBase oddBase vals
          a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))],
      ex'.1 = ex.1 ∧ ∀ h, ex.2 h → ex'.2 h := by
    intro v7 v28 v29 v30 v31 ex hex
    simp only [List.mem_cons] at hex
    rcases hex with rfl | hex
    · refine ⟨_, List.Mem.head _, rfl, ?_⟩
      intro h hp
      exact ⟨v7, v28, v29, v30, v31, hp⟩
    · rcases hex with rfl | hex
      · refine ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, fun _ hx => hx⟩
      · rcases hex with rfl | hex
        · refine ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), rfl, fun _ hx => hx⟩
        · rcases hex with rfl | hex
          · refine ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))), rfl, fun _ hx => hx⟩
          · rcases hex with rfl | hex
            · refine ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))), rfl, fun _ hx => hx⟩
            · rcases hex with rfl | hex
              · refine ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))), rfl, fun _ hx => hx⟩
              · rcases hex with rfl | hex
                · refine ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))), rfl, fun _ hx => hx⟩
                · rcases hex with rfl | hex
                  · refine ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))), rfl, ?_⟩
                    intro h hp
                    exact ⟨v7, v28, v29, v30, v31, hp⟩
                  · rcases hex with rfl | hex
                    · refine ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))), rfl, ?_⟩
                      intro h hp
                      exact ⟨v7, v28, v29, v30, v31, hp⟩
                    · rcases hex with rfl | hex
                      · refine ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))), rfl, ?_⟩
                        intro h hp
                        exact ⟨v7, v28, v29, v30, v31, hp⟩
                      · rcases hex with rfl | hex
                        · refine ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))), rfl, ?_⟩
                          intro h hp
                          change (taylorLoopInvParityAt newSp excess outPtr vals (j + 1)
                            (taylorLoopIndex j + signExtend12 (1 : BitVec 12)) evenBase oddBase
                            (taylorRoundBackedgeQuotient (taylorLoopIndex j) excess a0 a1 a2 a3 a4 a5)
                            [a0, a1, a2, a3, a4, a5]
                            (taylorRoundBackedgeSum a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5)
                            (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) **
                            (.x0 ↦ᵣ (0 : Word))) h at hp
                          change (taylorLoopInvParityAt newSp excess outPtr vals (j + 1)
                            (taylorLoopIndex (j + 1)) evenBase oddBase
                            (taylorRoundBackedgeQuotient (taylorLoopIndex j) excess a0 a1 a2 a3 a4 a5)
                            [a0, a1, a2, a3, a4, a5]
                            (taylorRoundBackedgeSum a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5)
                            (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) **
                            (.x0 ↦ᵣ (0 : Word))) h
                          rw [taylorLoopIndex_succ (j := j)]
                          rw [hse] at hp
                          exact hp
                        · exfalso; simp at hex
  have hAny : ∀ v5 v6 v7 v28 v29 v30 v31 : Word,
      cpsNBranchWithin
        (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
        exits := by
    intro v5 v6 v7 v28 v29 v30 v31
    refine cpsNBranchWithin_weaken_posts (hPinned v5 v6 v7 v28 v29 v30 v31) ?_
    intro ex hex
    have hsplit : ex ∈ taylorRoundTailPosts j newSp excess outPtr (taylorLoopIndex j) evenBase oddBase vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR ∨
        ex ∈ taylorRoundPinnedStatus j newSp excess outPtr (taylorLoopIndex j)
            evenBase oddBase vals
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31
            (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) :=
      List.mem_append.mp hex
    rcases hsplit with htail | hpost
    · refine ⟨ex, ?_, rfl, fun _ hx => hx⟩
      change ex ∈ terminal j newSp excess outPtr (taylorLoopIndex j) evenBase oddBase vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR
      simp only [terminal]
      exact List.mem_append.mpr (Or.inl htail)
    · obtain ⟨ex', hmem', heq, hpost'⟩ := hStatusWeak v7 v28 v29 v30 v31 ex hpost
      refine ⟨ex', ?_, heq, hpost'⟩
      change ex' ∈ terminal j newSp excess outPtr (taylorLoopIndex j) evenBase oddBase vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 o0 o1 o2 o3 FR
      simp only [terminal]
      exact List.mem_append.mpr (Or.inr hmem')
  have hFam : ∀ v5 v6 v7 v28 v29 v30 v31 : Word,
      cpsNBranchWithin
        (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (PriceK + 144) priceCode
        (taylorRoundSourcePreNoTemps newSp excess outPtr (taylorLoopIndex j)
          (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) **
          (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
        exits := by
    intro v5 v6 v7 v28 v29 v30 v31
    refine cpsNBranchWithin_weaken_pre ?_ (hAny v5 v6 v7 v28 v29 v30 v31)
    intro h hx
    simp only [taylorRoundSourcePre, taylorRoundSourcePreNoTemps] at hx ⊢
    xperm_hyp hx
  have hOwned : cpsNBranchWithin
      (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
      (PriceK + 144) priceCode
      (taylorRoundSourcePreNoTemps newSp excess outPtr (taylorLoopIndex j)
        (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31)
      exits := by
    exact nbranch_regOwn7 (P := taylorRoundSourcePreNoTemps newSp excess outPtr (taylorLoopIndex j)
        (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) hFam
  have hPreWeak : ∀ h,
      (taylorLoopInvParityAt newSp excess outPtr vals j (taylorLoopIndex j)
        evenBase oddBase [a0, a1, a2, a3, a4, a5]
        [p0, p1, p2, p3, p4, p5] [s0, s1, s2, s3, s4, s5]
        (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) **
        (.x0 ↦ᵣ (0 : Word))) h →
      (taylorRoundSourcePreNoTemps newSp excess outPtr (taylorLoopIndex j)
        (parityBuffer j evenBase oddBase) (parityBuffer j oddBase evenBase) vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31) h := by
    intro h hh
    simp only [taylorLoopInvParityAt, taylorRoundSourcePreNoTemps, cellsOf_six,
      EvmAsm.Rv64.AddrNorm.se12_0, EvmAsm.Rv64.AddrNorm.se12_8,
      EvmAsm.Rv64.AddrNorm.se12_16, EvmAsm.Rv64.AddrNorm.se12_24,
      EvmAsm.Rv64.AddrNorm.se12_32, EvmAsm.Rv64.AddrNorm.se12_40,
      EvmAsm.Rv64.AddrNorm.word_add_zero] at hh ⊢
    xperm_hyp hh
  have hFinal := cpsNBranchWithin_weaken_pre hPreWeak hOwned
  simpa only [exits, terminal] using hFinal

#check taylor_round_invariant_to_parity
#print axioms taylor_round_invariant_to_parity


end EvmAsm.Codegen.AmsterdamBlobGasPriceTaylorDischarge
