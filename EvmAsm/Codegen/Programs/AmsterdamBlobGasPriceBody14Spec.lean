/-
Outer-loop ROUND for `amsterdam_blob_gas_price_u256` (#12851): one full taylor
iteration at PriceK+144 as a 12-exit cpsNBranchWithin (exit PriceK+804 on
acc = 0, PriceK+964 on the nine overflow paths, back-edge PriceK+144). AB/PB
parametric — both loop parities are instances. Consumes the parametric windows
or_chainP2 / add6P_core / mul6P_core / swapdivP_core and the branch leaves.
-/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBodySpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceModel
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceDivisionBridge
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceMem
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody10Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody11Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody13Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14OrChain
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody7Spec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.SAsm.X0Frame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec

/-! The pure limb/model and cell-chain support is adopted from k3's rescued
    K70 work after a standalone build and axiom audit.  The corresponding
    `AmsterdamBlobGasPriceDiv` rescue is intentionally not imported: it still
    contains three `sorry`s and is not a premise for this machine proof. -/

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody7Spec EvmAsm.Codegen.AmsterdamBlobGasPriceBody10Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec EvmAsm.Codegen.AmsterdamBlobGasPriceBody13Spec
open EvmAsm.Codegen.AmsterdamBlobGasPrice

set_option maxRecDepth 8000

/-! The final multiply/accumulate values are named once here.  The outer
    round sees the sixth low product in `x28`, not the incoming `v28`; the
    short definitions also keep the two exit assertions readable. -/

@[reducible] def roundP0 (a0 excess : Word) : Word :=
  (a0 * excess) + (0 : Word)

@[reducible] def roundP1 (a0 a1 excess : Word) : Word :=
  (a1 * excess) + (rv64_mulhu a0 excess +
    if BitVec.ult (roundP0 a0 excess) (a0 * excess) then (1 : Word) else 0)

@[reducible] def roundP2 (a0 a1 a2 excess : Word) : Word :=
  (a2 * excess) + (rv64_mulhu a1 excess +
    if BitVec.ult (roundP1 a0 a1 excess) (a1 * excess) then (1 : Word) else 0)

@[reducible] def roundP3 (a0 a1 a2 a3 excess : Word) : Word :=
  (a3 * excess) + (rv64_mulhu a2 excess +
    if BitVec.ult (roundP2 a0 a1 a2 excess) (a2 * excess) then (1 : Word) else 0)

@[reducible] def roundP4 (a0 a1 a2 a3 a4 excess : Word) : Word :=
  (a4 * excess) + (rv64_mulhu a3 excess +
    if BitVec.ult (roundP3 a0 a1 a2 a3 excess) (a3 * excess) then (1 : Word) else 0)

@[reducible] def roundP5 (a0 a1 a2 a3 a4 a5 excess : Word) : Word :=
  (a5 * excess) + (rv64_mulhu a4 excess +
    if BitVec.ult (roundP4 a0 a1 a2 a3 a4 excess) (a4 * excess) then (1 : Word) else 0)

@[reducible] private def roundHigh (a0 a1 a2 a3 a4 a5 excess : Word) : Word :=
  rv64_mulhu a5 excess +
    if BitVec.ult (roundP5 a0 a1 a2 a3 a4 a5 excess) (a5 * excess) then (1 : Word) else 0

@[reducible] private def roundOverflow (a0 a1 a2 a3 a4 a5 excess : Word) : Word :=
  if BitVec.ult (roundHigh a0 a1 a2 a3 a4 a5 excess) (rv64_mulhu a5 excess) then
    (1 : Word) else 0

/-! The old rescued window named the incoming `v28`/`v29`/`v30`/`v31` at
    the Q exits.  Those are not the registers after the final multiply.  Keep
    the old call sites readable while making the exit constructor use the
    values produced by the linked instructions. -/

@[reducible] private def QOVFDIVP
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      _v7 _v28 _v29 _v30 _v31 : Word) (FR : Assertion) : Assertion :=
  EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec.QOVFDIVP
    newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5
    p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    (rv64_mulhu a5 excess) (roundP5 a0 a1 a2 a3 a4 a5 excess)
    (roundOverflow a0 a1 a2 a3 a4 a5 excess)
    (roundHigh a0 a1 a2 a3 a4 a5 excess)
    (roundHigh a0 a1 a2 a3 a4 a5 excess) FR

@[reducible] def QBACKP
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 : Word) (FR : Assertion) : Assertion :=
  EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec.QBACKP
    newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5
    p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31 FR

@[reducible] def roundS0 (a0 s0 : Word) : Word := (a0 + s0) + (0 : Word)
@[reducible] def roundS1 (a0 a1 s0 s1 : Word) : Word :=
  (a1 + s1) + rCry a0 s0 (0 : Word)
@[reducible] def roundS2 (a0 a1 a2 s0 s1 s2 : Word) : Word :=
  (a2 + s2) + rCry a1 s1 (rCry a0 s0 (0 : Word))
@[reducible] def roundS3 (a0 a1 a2 a3 s0 s1 s2 s3 : Word) : Word :=
  (a3 + s3) + rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))
@[reducible] def roundS4 (a0 a1 a2 a3 a4 s0 s1 s2 s3 s4 : Word) : Word :=
  (a4 + s4) + rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))
@[reducible] def roundS5 (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word) : Word :=
  (a5 + s5) + rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))

@[reducible] private def roundQOVF
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word) (FR : Assertion) : Assertion :=
  QOVFDIVP newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5
    (roundP0 a0 excess) (roundP1 a0 a1 excess) (roundP2 a0 a1 a2 excess)
    (roundP3 a0 a1 a2 a3 excess) (roundP4 a0 a1 a2 a3 a4 excess)
    (roundP5 a0 a1 a2 a3 a4 a5 excess)
    (roundS0 a0 s0) (roundS1 a0 a1 s0 s1) (roundS2 a0 a1 a2 s0 s1 s2)
    (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
    (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
    (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5)
    (rv64_mulhu a5 excess) (roundP5 a0 a1 a2 a3 a4 a5 excess)
    (roundOverflow a0 a1 a2 a3 a4 a5 excess)
    (roundHigh a0 a1 a2 a3 a4 a5 excess)
    (roundHigh a0 a1 a2 a3 a4 a5 excess) FR

@[reducible] def roundQBACK
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word) (FR : Assertion) : Assertion :=
  QBACKP newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5
    (roundP0 a0 excess) (roundP1 a0 a1 excess) (roundP2 a0 a1 a2 excess)
    (roundP3 a0 a1 a2 a3 excess) (roundP4 a0 a1 a2 a3 a4 excess)
    (roundP5 a0 a1 a2 a3 a4 a5 excess)
    (roundS0 a0 s0) (roundS1 a0 a1 s0 s1) (roundS2 a0 a1 a2 s0 s1 s2)
    (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
    (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
    (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5)
    (rv64_mulhu a5 excess) (roundP5 a0 a1 a2 a3 a4 a5 excess)
    (roundOverflow a0 a1 a2 a3 a4 a5 excess)
    (roundHigh a0 a1 a2 a3 a4 a5 excess)
    (roundHigh a0 a1 a2 a3 a4 a5 excess) FR

/-! Public name for the round's back-edge post.  The concrete scratch values
    remain hidden behind the machine post; consumers only need the swapped
    six-cell buffers and the incremented index exposed by the adapter. -/
@[reducible] def taylorRoundBackedgePost
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word) (FR : Assertion) : Assertion :=
  roundQBACK newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 FR

@[reducible] def taylorRoundBackedgeQuotient
    (iVal excess a0 a1 a2 a3 a4 a5 : Word) : List Word :=
  (EvmAsm.Codegen.AmsterdamBlobGasPriceDivisionBridge.divstSix (taylorDW * iVal)
    (roundP0 a0 excess) (roundP1 a0 a1 excess) (roundP2 a0 a1 a2 excess)
    (roundP3 a0 a1 a2 a3 excess) (roundP4 a0 a1 a2 a3 a4 excess)
    (roundP5 a0 a1 a2 a3 a4 a5 excess)).1

@[reducible] def taylorRoundBackedgeSum
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word) : List Word :=
  [roundS0 a0 s0, roundS1 a0 a1 s0 s1, roundS2 a0 a1 a2 s0 s1 s2,
    roundS3 a0 a1 a2 a3 s0 s1 s2 s3,
    roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4,
    roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5]

/-! Body13 carries the same instruction window, but its generic core leaves
    the incoming x28 parameter in the Q exits.  The linked final multiply has
    already produced the low limb in x28, so instantiate that core at the
    measured post-multiply values before matching the local exit constructors. -/
set_option linter.defProp false in
@[reducible] private def swapdivP_core_fixed
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v5 v6 _v7 _v28 _v29 _v30 _v31 : Word)
    (FR : Assertion) (hFR : FR.pcFree) :=
  EvmAsm.Codegen.AmsterdamBlobGasPriceBody13Spec.swapdivP_core
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v5 v6 (rv64_mulhu a5 excess)
    (roundP5 a0 a1 a2 a3 a4 a5 excess)
    (roundOverflow a0 a1 a2 a3 a4 a5 excess)
    (roundHigh a0 a1 a2 a3 a4 a5 excess)
    (roundHigh a0 a1 a2 a3 a4 a5 excess) FR hFR


/-- Sequence an N-branch onto the LAST exit of another (same CodeReq):
    runs that continue at the final station replace it; earlier exits pass
    through unchanged. -/
private theorem nb_snoc {n1 n2 : Nat} {entry m : Word} {cr : CodeReq}
    {P Qm : Assertion} {pre : List (Word × Assertion)} {exits2 : List (Word × Assertion)}
    (h1 : cpsNBranchWithin n1 entry cr P (pre ++ [(m, Qm)]))
    (h2 : cpsNBranchWithin n2 m cr Qm exits2) :
    cpsNBranchWithin (n1 + n2) entry cr P (pre ++ exits2) := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, ex, hmem, hpc1, hQ1⟩ := h1 R hR s hcr hPR hpc
  simp only [List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hmem | hlast
  · refine ⟨k1, Nat.le_trans hk1 (Nat.le_add_right n1 n2), s1, hstep1, ex, ?_, hpc1, hQ1⟩
    exact List.mem_append.mpr (Or.inl hmem)
  · subst hlast
    have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, ex2, hmem2, hpc2, hQ2⟩ := h2 R hR s1 hcr' hQ1 hpc1
    exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2, ex2,
      List.mem_append.mpr (Or.inr hmem2), hpc2, hQ2⟩

/-- Pre-weakening for N-branches (same exits, stronger precondition). -/
private theorem nb_prew {n : Nat} {entry : Word} {cr : CodeReq}
    {P P' : Assertion} {exits : List (Word × Assertion)}
    (hpre : ∀ h, P' h → P h) (h : cpsNBranchWithin n entry cr P exits) :
    cpsNBranchWithin n entry cr P' exits := by
  intro R hR s hcr hP'R hpc
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hP'R
    exact ⟨hp, hcompat, sepConj_mono_left hpre hp hpq⟩
  exact h R hR s hcr hPR hpc

/-- Drop a pure riding as the second conjunct's tail: `(L1 ** (L2 ** ⌜P⌝)) h`
    implies `(L1 ** L2) h`. -/
private theorem pure_drop1 {L1 L2 : Assertion} {P : Prop} :
    ∀ h, (L1 ** (L2 ** ⌜P⌝)) h → (L1 ** L2) h := by
  intro h hx
  obtain ⟨g1, g2p, gd, gu, hL1, hL2p⟩ := hx
  obtain ⟨g2, gP, gd2, gu2, hL2, hP⟩ := hL2p
  obtain ⟨heq, -⟩ := hP
  have gu' : g2p = g2 := by
    rw [heq, PartialState.union_empty_right] at gu2
    exact gu2.symm
  rw [gu'] at gd gu
  exact ⟨g1, g2, gd, gu, hL1, hL2⟩

/-! ## Parity-aware outer-loop invariant

The two six-limb work buffers are fixed in memory, but the linked loop swaps
their roles at the end of every successful round.  Keeping the two physical
bases as parameters and selecting the active one from the iteration parity
makes that fact explicit; a caller can instantiate the same round theorem at
either orientation without duplicating a second assertion by hand. -/

@[reducible] def parityBuffer (j : Nat) (evenBase oddBase : Word) : Word :=
  if j % 2 = 0 then evenBase else oddBase

theorem parityBuffer_succ_swap (j : Nat) (evenBase oddBase : Word) :
    parityBuffer (j + 1) evenBase oddBase = parityBuffer j oddBase evenBase := by
  by_cases h_even : j % 2 = 0
  · have h_odd : (j + 1) % 2 ≠ 0 := by omega
    simp [parityBuffer, h_even, h_odd]
  · have h_odd : (j + 1) % 2 = 0 := by omega
    simp [parityBuffer, h_even, h_odd]

theorem parityBuffer_succ_swap' (j : Nat) (evenBase oddBase : Word) :
    parityBuffer (j + 1) oddBase evenBase = parityBuffer j evenBase oddBase := by
  exact parityBuffer_succ_swap (j := j) (evenBase := oddBase) (oddBase := evenBase)

@[reducible] def taylorLoopIndex (j : Nat) : Word := BitVec.ofNat 64 (j + 1)

theorem taylorLoopIndex_zero : taylorLoopIndex 0 = (1 : Word) := by decide

theorem taylorLoopIndex_succ (j : Nat) :
    taylorLoopIndex (j + 1) = taylorLoopIndex j + (1 : Word) := by
  apply BitVec.eq_of_toNat_eq
  rw [show taylorLoopIndex (j + 1) = BitVec.ofNat 64 ((j + 1) + 1) by rfl]
  simp only [taylorLoopIndex, BitVec.toNat_ofNat, BitVec.toNat_add]
  rw [show ((1 : Word)).toNat = 1 from rfl]
  omega

@[reducible] def taylorLoopInvParityAt
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (j : Nat) (iVal evenBase oddBase : Word)
    (accC prodC sumC : List Word) (FR : Assertion) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) ** (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
  (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ iVal) **
  (.x19 ↦ᵣ parityBuffer j evenBase oddBase) **
  (.x20 ↦ᵣ parityBuffer j oddBase evenBase) ** (.x21 ↦ᵣ outPtr) **
  (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
  frameSlotsSaved priceFrame newSp vals **
  (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31) **
  (cellsOf (parityBuffer j evenBase oddBase) accC **
    cellsOf (parityBuffer j oddBase evenBase) prodC **
    cellsOf (newSp + signExtend12 (160 : BitVec 12)) sumC ** FR)

/-! The public invariant ties the machine's index register to the outer-loop
    iteration.  The `At` form above is retained for one-round composition,
    where a branch post supplies the concrete next index before this relation
    is reintroduced. -/

@[reducible] def taylorLoopInvParity
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (j : Nat) (evenBase oddBase : Word)
    (accC prodC sumC : List Word) (FR : Assertion) : Assertion :=
  taylorLoopInvParityAt newSp excess outPtr vals j (taylorLoopIndex j)
    evenBase oddBase accC prodC sumC FR

theorem taylorLoopInvParityAt_swap
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (j : Nat) (iVal evenBase oddBase : Word)
    (accC prodC sumC : List Word) (FR : Assertion) :
    taylorLoopInvParityAt newSp excess outPtr vals (j + 1) iVal
        evenBase oddBase accC prodC sumC FR =
      taylorLoopInvParityAt newSp excess outPtr vals j iVal
        oddBase evenBase accC prodC sumC FR := by
  simp only [taylorLoopInvParityAt, parityBuffer_succ_swap]

theorem taylorLoopInvParity_index_step
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (j : Nat) (evenBase oddBase : Word)
    (accC prodC sumC : List Word) (FR : Assertion) :
    taylorLoopInvParity newSp excess outPtr vals (j + 1)
        evenBase oddBase accC prodC sumC FR =
      taylorLoopInvParityAt newSp excess outPtr vals j
        (taylorLoopIndex j + (1 : Word)) oddBase evenBase accC prodC sumC FR := by
  rw [taylorLoopInvParity, taylorLoopIndex_succ, taylorLoopInvParityAt_swap]

/-! The round theorem exposes the three six-limb workspaces as individual
    dword atoms.  Keep that representation at the boundary, but name the
    corresponding x0-free entry assertion so the parity invariant can feed
    the linked round without smuggling the architectural zero register into
    the caller's frame. -/

@[reducible] def taylorRoundFootprint
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (accC prodC sumC : List Word) (FR : Assertion) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
  (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
  (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
  (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ AB) ** (.x20 ↦ᵣ PB) **
  (.x21 ↦ᵣ outPtr) **
  (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
  regOwns [.x5, .x6, .x7, .x28, .x29, .x30, .x31] **
  frameSlotsSaved priceFrame newSp vals **
  cellsOf AB accC ** cellsOf PB prodC **
  cellsOf (newSp + signExtend12 (160 : BitVec 12)) sumC ** FR

/-! `taylorRoundFootprint` is deliberately only the entry footprint.  The
    temporary registers are owned rather than assigned arbitrary values; the
    concrete values needed by `taylor_round` are introduced when its
    `regOwns` riders are peeled.  This theorem checks the structural part of
    the parity-to-round wiring before any branch post is exposed. -/
theorem taylorLoopInvParityAt_to_taylorRoundFootprint
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (j : Nat) (iVal evenBase oddBase : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) :
    ∀ h,
      taylorLoopInvParityAt newSp excess outPtr vals j iVal
        evenBase oddBase [a0, a1, a2, a3, a4, a5]
        [p0, p1, p2, p3, p4, p5] [s0, s1, s2, s3, s4, s5] FR h →
      taylorRoundFootprint newSp excess outPtr iVal
        (parityBuffer j evenBase oddBase)
        (parityBuffer j oddBase evenBase) vals
        [a0, a1, a2, a3, a4, a5] [p0, p1, p2, p3, p4, p5]
        [s0, s1, s2, s3, s4, s5] FR h := by
  intro h hh
  unfold taylorLoopInvParityAt at hh
  unfold taylorRoundFootprint
  simp only [regOwns, sepConj_emp_right'] at hh ⊢
  simp only [cellsOf_six] at hh ⊢
  xperm_hyp hh



/-- One full outer-loop round of the taylor recurrence, PriceK+144..: the
or-chain zero test (exit PriceK+804 on acc = 0), the i < 496 cap (overflow
exit PriceK+964), the 6-limb ripple add (carry overflow), the 6-limb multiply
by excess (seven overflow exits), and the divisor/division window jumping back
to PriceK+144. Both loop parities are instances (AB/PB swap). -/
theorem taylor_round (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31 : Word)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsNBranchWithin 4028 (PriceK + 144) priceCode
      (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))
      [(PriceK + 804, (((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) = (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))),
    (PriceK + 964, (((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜¬ BitVec.ult iVal (496 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))),
    (PriceK + 964, (((.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ≠ (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ s5) ** (.x28 ↦ᵣ (a5 + s5)) **
       (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       FR))),
    (PriceK + 964, mul6PQOVF0 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF1 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF2 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF3 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF4 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF5 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVFF newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, QOVFDIVP newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 * excess) + (0 : Word)) ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) v7 v28 v29 v30 v31 FR),
    (PriceK + 144, QBACKP newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 * excess) + (0 : Word)) ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) v7 v28 v29 v30 v31 FR)] := by
  have hOr2 := or_chainP2 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5
    p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31 FR hFR
  have hA : cpsTripleWithin 13 (PriceK + 144) (PriceK + 196) priceCode
      (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)) (((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word))) **
              ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)) :=
    cpsTripleWithin_weaken (fun _ hx => hx) (by intro h hx; xperm_hyp hx) hOr2
  have hBe := AmsterdamBlobGasPriceBodySpec.loop_test_beqz_branch ((((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5))
  have hBeF := cpsBranchWithin_frameR (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)) (by pcFree; exact hFR) hBe
  have nbBeqz := cpsNBranchWithin_of_branch hBeF
  have nb0 := cpsTripleWithin_seq_cpsNBranchWithin_same_cr hA nbBeqz
  -- li t0, 496 (PriceK+200)
  have hLi := li_spec_gen_within .x5 ((((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) (496 : Word) (PriceK + 200) (by decide)
  have hLiF : cpsTripleWithin 1 (PriceK + 200) (PriceK + 204) priceCode
      ((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) **
              ((.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) ≠ (0 : Word)⌝ **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)) ((.x5 ↦ᵣ (496 : Word)) **
              ((.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) ≠ (0 : Word)⌝ **
       (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR _ (by pcFree; exact hFR) hLi)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[50]'(by decide) = .LI .x5 (496 : Word) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 200) amsterdamBlobGasPriceU256_prog
      50 (.LI .x5 (496 : Word)) (by decide) (by decide) hins (by decide) a i hi
  have hLiF' : cpsTripleWithin 1 (PriceK + 200) (PriceK + 204) priceCode
      ((((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) ≠ (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))) ((((.x5 ↦ᵣ (496 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) ≠ (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))) :=
    cpsTripleWithin_weaken (by intro h hx; xperm_hyp hx) (by intro h hx; xperm_hyp hx) hLiF
  have nbLi : cpsNBranchWithin 1 (PriceK + 200) priceCode
      ((((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) ≠ (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))) [(PriceK + 204, (((.x5 ↦ᵣ (496 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) ≠ (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)))] :=
    cpsNBranchWithin_of_triple (by simp) hLiF'
  have nb1 := nb_snoc (pre := [(PriceK + 804, (((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) = (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)))]) nb0 nbLi
  -- bgeu s2, t0 (PriceK+204)
  have hBg := AmsterdamBlobGasPriceBodySpec.loop_test_bgeu_branch iVal (496 : Word)
  have hBgF := cpsBranchWithin_frameR (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)) (by pcFree; exact hFR) hBg
  have hBgF' : cpsBranchWithin 1 (PriceK + 204) priceCode
      ((((.x5 ↦ᵣ (496 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) ≠ (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)))
      (PriceK + 964)
      ((((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜¬ BitVec.ult iVal (496 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)))
      (PriceK + 208)
      ((((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜BitVec.ult iVal (496 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))) := by
    refine cpsBranchWithin_weaken ?_ (fun _ hx => hx) (fun _ hx => hx) hBgF
    intro h hx
    obtain ⟨h1, h2, hd, hu, hlead, hfr⟩ := hx
    have hlead' := pure_drop1 _ hlead
    have hx' : (((.x5 ↦ᵣ (496 : Word)) ** (.x0 ↦ᵣ (0 : Word))) ** (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))) h :=
      ⟨h1, h2, hd, hu, hlead', hfr⟩
    xperm_hyp hx'
  have nbBg := cpsNBranchWithin_of_branch hBgF'
  have nb2 := nb_snoc (pre := [(PriceK + 804, (((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) = (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)))]) nb1 nbBg
  -- add6 (PriceK+208..428)
  have hAddInst := add6P_core newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 (496 : Word) a5 v7 v28 v29 v30 v31
  have hAddF := cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word)) ** FR)
      (pcFree_sepConj pcFree_regIs hFR) hAddInst
  have hAdd' : cpsTripleWithin 55 (PriceK + 208) (PriceK + 428) priceCode
      ((((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜BitVec.ult iVal (496 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))) (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ s5) **
       (.x28 ↦ᵣ (a5 + s5)) ** (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))))) **
        FR) := by
    refine cpsTripleWithin_weaken ?_ (by intro h hx; xperm_hyp hx) hAddF
    intro h hx
    obtain ⟨h1, h2, hd, hu, hlead, hfbg⟩ := hx
    have hlead' := pure_drop1 _ hlead
    have hx' : (((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word))) ** (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))) h :=
      ⟨h1, h2, hd, hu, hlead', hfbg⟩
    xperm_hyp hx'
  have nbAdd : cpsNBranchWithin 55 (PriceK + 208) priceCode
      ((((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜BitVec.ult iVal (496 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))) [(PriceK + 428,       ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ s5) **
       (.x28 ↦ᵣ (a5 + s5)) ** (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))))) ** FR)] :=
    cpsNBranchWithin_of_triple (by simp) hAdd'
  have nb3 := nb_snoc (pre := [(PriceK + 804, (((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) = (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))), (PriceK + 964, (((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜¬ BitVec.ult iVal (496 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)))]) nb2 nbAdd
  -- carry branch (PriceK+428)
  have hCr := AmsterdamBlobGasPriceBodySpec.add6_carry_branch ((rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))))
  have hCrF := cpsBranchWithin_frameR (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ s5) ** (.x28 ↦ᵣ (a5 + s5)) **
       (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       FR)) (by pcFree; exact hFR) hCr
  have hCrF' : cpsBranchWithin 1 (PriceK + 428) priceCode
      ((      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ s5) **
       (.x28 ↦ᵣ (a5 + s5)) ** (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))))) ** FR))
      (PriceK + 964)
      ((((.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ≠ (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ s5) ** (.x28 ↦ᵣ (a5 + s5)) **
       (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       FR)))
      (PriceK + 432)
      ((((.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) = (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ s5) ** (.x28 ↦ᵣ (a5 + s5)) **
       (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       FR))) := by
    refine cpsBranchWithin_weaken ?_ (fun _ hx => hx) (fun _ hx => hx) hCrF
    intro h hx
    xperm_hyp hx
  have nbCr := cpsNBranchWithin_of_branch hCrF'
  have nb4 := nb_snoc (pre := [(PriceK + 804, (((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) = (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))), (PriceK + 964, (((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜¬ BitVec.ult iVal (496 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR)))]) nb3 nbCr
  -- mul6 (PriceK+432..680)
  have hMulF : cpsNBranchWithin 62 (PriceK + 432) priceCode
      (((mul6PPRE newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) a5 s5 (a5 + s5) (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) ** FR))
      [(PriceK + 964, mul6PQOVF0 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF1 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF2 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF3 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF4 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF5 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVFF newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 680, mul6PQFALL newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR)] :=
    cpsNBranchWithin_frameR hFR (mul6P_core newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) a5 s5 (a5 + s5) (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word)))
  have hMul' : cpsNBranchWithin 62 (PriceK + 432) priceCode
      ((((.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) = (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ s5) ** (.x28 ↦ᵣ (a5 + s5)) **
       (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       FR)))
      [(PriceK + 964, mul6PQOVF0 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF1 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF2 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF3 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF4 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF5 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVFF newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 680, mul6PQFALL newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR)] := by
    refine nb_prew ?_ hMulF
    intro h hx
    obtain ⟨h1, h2, hd, hu, hlead, hfcr⟩ := hx
    have hlead' := pure_drop1 _ hlead
    have hx' : (((.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x0 ↦ᵣ (0 : Word))) ** (      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ s5) ** (.x28 ↦ᵣ (a5 + s5)) **
       (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       FR))) h :=
      ⟨h1, h2, hd, hu, hlead', hfcr⟩
    xperm_hyp hx'
  have nb5 := nb_snoc (pre := [(PriceK + 804, (((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) = (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))),
    (PriceK + 964, (((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜¬ BitVec.ult iVal (496 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))),
    (PriceK + 964, (((.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ≠ (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ s5) ** (.x28 ↦ᵣ (a5 + s5)) **
       (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       FR)))]) nb4 hMul'
  -- swapdiv (PriceK+680..: back to PriceK+144)
  have hSd' : cpsNBranchWithin 3894 (PriceK + 680) priceCode
      ((mul6PQFALL newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5
        ((a0 + s0) + (0 : Word))
        ((a1 + s1) + (rCry a0 s0 (0 : Word)))
        ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))
        ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))
        ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))
        ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR))
      [(PriceK + 964, QOVFDIVP newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 * excess) + (0 : Word)) ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) v7 v28 v29 v30 v31 FR),
      (PriceK + 144, QBACKP newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 * excess) + (0 : Word)) ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) v7 v28 v29 v30 v31 FR)] := by
    let swapdivP_core := swapdivP_core_fixed
    refine nb_prew ?_ (swapdivP_core_fixed newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 ((a0 * excess) + (0 : Word)) ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) a5 (a5 * excess) (rv64_mulhu a5 excess) ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word))) (if BitVec.ult ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) (a5 * excess) then (1 : Word) else (0 : Word))) (rv64_mulhu a5 excess) then (1 : Word) else (0 : Word)) ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) (a5 * excess) then (1 : Word) else (0 : Word))) ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) (a5 * excess) then (1 : Word) else (0 : Word))) FR hFR)
    intro h hx
    unfold mul6PQFALL at hx
    rw [sepConj_assoc'] at hx
    have hx3 := pure_drop_mid
      (L1 := (.x31 ↦ᵣ roundHigh a0 a1 a2 a3 a4 a5 excess))
      (L2 := (.x0 ↦ᵣ (0 : Word)))
      (P := roundHigh a0 a1 a2 a3 a4 a5 excess = (0 : Word)) h hx
    obtain ⟨h1, h2, hd, hu, hqf, hfrw⟩ := hx
    /-
    have hx2 : ((((.x31 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) (a5 * excess) then (1 : Word) else (0 : Word)))) ** (.x0 ↦ᵣ (0 : Word)))) **
              ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x5 ↦ᵣ a5) **
       (.x6 ↦ᵣ (a5 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a5 excess)) **
       (.x28 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) (a5 * excess) then (1 : Word) else (0 : Word))) (rv64_mulhu a5 excess) then (1 : Word) else (0 : Word))) **
       (.x30 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) (a5 * excess) then (1 : Word) else (0 : Word)))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word))))) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word))))) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word))))) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word))))) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word))))) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))))) h1 :=
      pure_drop_mid _ hqf
    have hx3 : (((((.x31 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) (a5 * excess) then (1 : Word) else (0 : Word)))) ** (.x0 ↦ᵣ (0 : Word)))) **
              ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x5 ↦ᵣ a5) **
       (.x6 ↦ᵣ (a5 * excess)) ** (.x7 ↦ᵣ (rv64_mulhu a5 excess)) **
       (.x28 ↦ᵣ ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) ** (.x29 ↦ᵣ (if BitVec.ult ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) (a5 * excess) then (1 : Word) else (0 : Word))) (rv64_mulhu a5 excess) then (1 : Word) else (0 : Word))) **
       (.x30 ↦ᵣ ((rv64_mulhu a5 excess) + (if BitVec.ult ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word)))) (a5 * excess) then (1 : Word) else (0 : Word)))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 * excess) + (0 : Word))) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word))))) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word))))) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word))))) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word))))) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 * excess) + ((rv64_mulhu a4 excess) + (if BitVec.ult ((a4 * excess) + ((rv64_mulhu a3 excess) + (if BitVec.ult ((a3 * excess) + ((rv64_mulhu a2 excess) + (if BitVec.ult ((a2 * excess) + ((rv64_mulhu a1 excess) + (if BitVec.ult ((a1 * excess) + ((rv64_mulhu a0 excess) + (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess) then (1 : Word) else (0 : Word)))) (a1 * excess) then (1 : Word) else (0 : Word)))) (a2 * excess) then (1 : Word) else (0 : Word)))) (a3 * excess) then (1 : Word) else (0 : Word)))) (a4 * excess) then (1 : Word) else (0 : Word))))) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))))) ** FR) h :=
      ⟨h1, h2, hd, hu, hx2, hfrw⟩
    xperm_hyp hx3
    -/
    xperm_hyp hx3
  have nb6 := nb_snoc (pre := [(PriceK + 804, (((.x5 ↦ᵣ (((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(((((((0 : Word) ||| a0) ||| a1) ||| a2) ||| a3) ||| a4) ||| a5) = (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))),
    (PriceK + 964, (((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) ** ⌜¬ BitVec.ult iVal (496 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x19 ↦ᵣ (AB)) ** (.x20 ↦ᵣ (PB)) **
       (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) **
       (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ s0) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) ↦ₘ s2) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) ↦ₘ s4) ** (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) ↦ₘ s5) **
       FR))),
    (PriceK + 964, (((.x5 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜(rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ≠ (0 : Word)⌝) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
       (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
       (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
       (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ (AB)) **
       (.x20 ↦ᵣ (PB)) ** (.x21 ↦ᵣ outPtr) **
       (.x22 ↦ᵣ (newSp + signExtend12 (160 : BitVec 12))) ** (.x6 ↦ᵣ a5) **
       (.x7 ↦ᵣ s5) ** (.x28 ↦ᵣ (a5 + s5)) **
       (.x29 ↦ᵣ (rCry a5 s5 (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) ** (.x30 ↦ᵣ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       (.x31 ↦ᵣ (if BitVec.ult ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) (a5 + s5) then (1 : Word) else (0 : Word))) ** frameSlotsSaved priceFrame newSp vals **
       (((AB) + signExtend12 (0 : BitVec 12)) ↦ₘ a0) ** (((AB) + signExtend12 (8 : BitVec 12)) ↦ₘ a1) **
       (((AB) + signExtend12 (16 : BitVec 12)) ↦ₘ a2) ** (((AB) + signExtend12 (24 : BitVec 12)) ↦ₘ a3) **
       (((AB) + signExtend12 (32 : BitVec 12)) ↦ₘ a4) ** (((AB) + signExtend12 (40 : BitVec 12)) ↦ₘ a5) **
       (((PB) + signExtend12 (0 : BitVec 12)) ↦ₘ p0) ** (((PB) + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
       (((PB) + signExtend12 (16 : BitVec 12)) ↦ₘ p2) ** (((PB) + signExtend12 (24 : BitVec 12)) ↦ₘ p3) **
       (((PB) + signExtend12 (32 : BitVec 12)) ↦ₘ p4) ** (((PB) + signExtend12 (40 : BitVec 12)) ↦ₘ p5) **
       (((newSp + signExtend12 160) + signExtend12 (0 : BitVec 12)) ↦ₘ ((a0 + s0) + (0 : Word))) ** (((newSp + signExtend12 160) + signExtend12 (8 : BitVec 12)) ↦ₘ ((a1 + s1) + (rCry a0 s0 (0 : Word)))) **
       (((newSp + signExtend12 160) + signExtend12 (16 : BitVec 12)) ↦ₘ ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ** (((newSp + signExtend12 160) + signExtend12 (24 : BitVec 12)) ↦ₘ ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) **
       (((newSp + signExtend12 160) + signExtend12 (32 : BitVec 12)) ↦ₘ ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** (((newSp + signExtend12 160) + signExtend12 (40 : BitVec 12)) ↦ₘ ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))))) **
       FR))),
    (PriceK + 964, mul6PQOVF0 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF1 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF2 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p2 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF3 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p3 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF4 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p4 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVF5 newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5 p5 ((a0 + s0) + (0 : Word)) ((a1 + s1) + (rCry a0 s0 (0 : Word))) ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word)))) ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))) ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))) ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR),
    (PriceK + 964, mul6PQOVFF newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5
      ((a0 + s0) + (0 : Word))
      ((a1 + s1) + (rCry a0 s0 (0 : Word)))
      ((a2 + s2) + (rCry a1 s1 (rCry a0 s0 (0 : Word))))
      ((a3 + s3) + (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word)))))
      ((a4 + s4) + (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))
      ((a5 + s5) + (rCry a4 s4 (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 (0 : Word))))))) ** FR)]) nb5 hSd'
  simpa using nb6

private theorem x0Free_sepConj {P Q : Assertion}
    (hP : x0FreeAssertion P) (hQ : x0FreeAssertion Q) :
    x0FreeAssertion (P ** Q) := by
  intro h hh
  obtain ⟨h1, h2, hd, hu, hp, hq⟩ := hh
  have h1x := hP h1 hp
  have h2x := hQ h2 hq
  rw [← hu]
  simp [PartialState.union, h1x, h2x]

private theorem x0Free_regIs {r : Reg} {v : Word} (hr : r ≠ .x0) :
    x0FreeAssertion (regIs r v) := by
  intro h hh
  rw [hh]
  simp [PartialState.singletonReg, Ne.symm hr]

/-! The linked terminal-index pair can be used without making the caller's
    frame own the architectural zero register.  This is the exact artifact
    window cited by `loop_test_li_bgeu_terminal_496`; the frame is added only
    after the x0 transfer, so the theorem remains valid for an arbitrary
    pc-free caller assertion, including one that owns x0. -/
theorem loop_test_li_bgeu_terminal_496_drop_x0
    (iVal vOld : Word) (h_i : iVal = (496 : Word))
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 2 (PriceK + 200) (PriceK + 964) priceCode
      (((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ vOld)) ** FR)
      (((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) **
        ⌜¬ BitVec.ult iVal (496 : Word)⌝) ** FR) := by
  have hbase :=
    EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec.loop_test_li_bgeu_terminal_496
      iVal vOld h_i
  have hbase_x0 := cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) hbase
  have hn_x0 := cpsTripleWithin_as_cpsNBranchWithin hbase_x0
  have hfree : x0FreeAssertion ((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ vOld)) :=
    x0Free_sepConj (x0Free_regIs (by decide)) (x0Free_regIs (by decide))
  have hn := cpsNBranchWithin_drop_x0
    (exits := [(PriceK + 964,
      (.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) **
        ⌜¬ BitVec.ult iVal (496 : Word)⌝)]) hfree hn_x0
  have hdrop := cpsNBranchWithin_as_cpsTripleWithin hn
  exact cpsTripleWithin_frameR FR hFR hdrop

/-! The complementary, non-terminal side of the same linked pair.  The
    caller supplies the static `iVal < 496` fact, while the x0 transfer is
    discharged before an arbitrary pc-free frame is reattached. -/
theorem loop_test_li_bgeu_continue_496_drop_x0
    (iVal vOld : Word) (h_i : BitVec.ult iVal (496 : Word))
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 2 (PriceK + 200) (PriceK + 208) priceCode
      (((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ vOld)) ** FR)
      (((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) **
        ⌜BitVec.ult iVal (496 : Word)⌝) ** FR) := by
  have hLi := li_spec_gen_within .x5 vOld (496 : Word) (PriceK + 200) (by decide)
  have hLiF : cpsTripleWithin 1 (PriceK + 200) (PriceK + 204) priceCode
      ((.x5 ↦ᵣ vOld) ** (.x18 ↦ᵣ iVal))
      ((.x5 ↦ᵣ (496 : Word)) ** (.x18 ↦ᵣ iVal)) := by
    refine cpsTripleWithin_extend_code ?_
      (cpsTripleWithin_frameR (.x18 ↦ᵣ iVal) (by pcFree) hLi)
    intro a i hi
    have hins : amsterdamBlobGasPriceU256_prog[50]'(by decide) =
        .LI .x5 (496 : Word) := by decide
    show priceCode a = some i
    exact CodeReq.ofProg_mem_at (PriceK : Word) (PriceK + 200)
      amsterdamBlobGasPriceU256_prog 50 (.LI .x5 (496 : Word))
      (by decide) (by decide) hins (by decide) a i hi
  have hLiF' : cpsTripleWithin 1 (PriceK + 200) (PriceK + 204) priceCode
      ((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ vOld))
      ((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word))) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hLiF
  have hContinue : cpsTripleWithin 1 (PriceK + 204) (PriceK + 208) priceCode
      ((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)))
      ((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) **
        ⌜BitVec.ult iVal (496 : Word)⌝) := by
    apply cpsBranchWithin_ntakenPath
      (EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec.loop_test_bgeu_branch
        iVal (496 : Word))
    intro _ hQt
    obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
    have h_not_ult := ((sepConj_pure_right _).1 h_pure).2
    exact h_not_ult h_i
  have hseq := cpsTripleWithin_seq_same_cr hLiF' hContinue
  exact cpsTripleWithin_frameR FR hFR hseq

/-! The arithmetic values exposed by `taylor_round` are the same pure six-limb
    transitions used by the model.  Keep these bridges next to the private
    machine-value abbreviations: the outer-loop composition can then reason
    about `mul384Run`/`add384Run` without unfolding the 12-exit body proof. -/

theorem roundP_eq_mul384Run
    (a0 a1 a2 a3 a4 a5 excess : Word) :
    [roundP0 a0 excess, roundP1 a0 a1 excess, roundP2 a0 a1 a2 excess,
      roundP3 a0 a1 a2 a3 excess, roundP4 a0 a1 a2 a3 a4 excess,
      roundP5 a0 a1 a2 a3 a4 a5 excess] =
      (mul384Run [a0, a1, a2, a3, a4, a5] excess 0).1 := by
  simp [mul384Run, mulLimbStep, roundP0, roundP1, roundP2, roundP3,
    roundP4, roundP5]

theorem roundP_high_eq_mul384Run
    (a0 a1 a2 a3 a4 a5 excess : Word) :
    roundHigh a0 a1 a2 a3 a4 a5 excess =
      (mul384Run [a0, a1, a2, a3, a4, a5] excess 0).2 := by
  simp [mul384Run, mulLimbStep, roundP0, roundP1, roundP2, roundP3,
    roundP4, roundP5, roundHigh]

theorem roundS_eq_add384Run
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word) :
    [roundS0 a0 s0, roundS1 a0 a1 s0 s1,
      roundS2 a0 a1 a2 s0 s1 s2, roundS3 a0 a1 a2 a3 s0 s1 s2 s3,
      roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4,
      roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5] =
      (add384Run [a0, a1, a2, a3, a4, a5]
        [s0, s1, s2, s3, s4, s5] 0).1 := by
  simp [add384Run, addLimbStep, roundS0, roundS1, roundS2, roundS3,
    roundS4, roundS5,
    EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec.rCry]

theorem roundS_carry_eq_add384Run
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word) :
    EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec.rCry a5 s5
      (EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec.rCry a4 s4
        (EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec.rCry a3 s3
          (EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec.rCry a2 s2
            (EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec.rCry a1 s1
              (EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec.rCry a0 s0 0))))) =
      (add384Run [a0, a1, a2, a3, a4, a5]
        [s0, s1, s2, s3, s4, s5] 0).2 := by
  simp [EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec.rCry,
    add384Run, addLimbStep]

#print axioms taylor_round
#print axioms loop_test_li_bgeu_terminal_496_drop_x0
#print axioms loop_test_li_bgeu_continue_496_drop_x0
#print axioms roundP_eq_mul384Run
#print axioms roundP_high_eq_mul384Run
#print axioms roundS_eq_add384Run
#print axioms roundS_carry_eq_add384Run
#print axioms EvmAsm.Codegen.AmsterdamBlobGasPrice.limbsToNat_natToLimbs
#print axioms EvmAsm.Codegen.AmsterdamBlobGasPrice.div384by64_spec
#print axioms EvmAsm.Codegen.AmsterdamBlobGasPrice.priceLoopFuel_done_taylor
#print axioms EvmAsm.Codegen.AmsterdamBlobGasPrice.cellsOf_eq_bytesRegion
#print axioms EvmAsm.Codegen.AmsterdamBlobGasPrice.bytesRegion_imp_cellsOwn
