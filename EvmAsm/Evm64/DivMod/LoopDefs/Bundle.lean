/-
  EvmAsm.Evm64.DivMod.LoopDefs.Bundle

  Precondition bundles for the Knuth Algorithm D loop body, packaging the
  register/memory layout at loop entry (before the first iteration of a
  multi-iteration path) into reusable `Assertion` defs:

    * loopN3Pre / loopN3PreWithScratch — n=3 two-iteration path
    * loopN2Pre / loopN2PreWithScratch — n=2 three-iteration path
    * loopN2Iter10Pre / loopN2Iter10PreWithScratch — n=2 two-iteration path
    * loopN1Pre / loopN1PreWithScratch — n=1 four-iteration path
    * loopN1Iter10Pre / loopN1Iter10PreWithScratch — n=1 two-iteration path
    * loopN1Iter210Pre / loopN1Iter210PreWithScratch — n=1 three-iteration path

  These are plain `Assertion`s (no iter/mulsub computations), so this file
  depends only on `Rv64.SepLogic`.
-/

module

public import EvmAsm.Rv64.SepLogic

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Two-iteration loop precondition for n=3
-- ============================================================================

/-- Precondition for the n=3 two-iteration loop (base+448 → base+904).
    Bundles registers, v-cells, u-cells at j=1 base, and extra j=0 cells. -/
@[irreducible]
def loopN3Pre (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word) : Assertion :=
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (1 : Word)) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base_1 + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base_1 + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base_1 + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base_1 + signExtend12 4072) ↦ₘ u3) **
  ((u_base_1 + signExtend12 4064) ↦ₘ uTop) **
  (q_addr_1 ↦ₘ q1Old) **
  ((u_base_0 + signExtend12 0) ↦ₘ u0Orig) **
  (q_addr_0 ↦ₘ q0Old)


-- ============================================================================
-- Two-iteration loop precondition for n=3 with scratch cells
-- ============================================================================

/-- Precondition for the n=3 two-iteration loop with scratch cells.
    Used when at least one iteration takes the call (div128) path. -/
@[irreducible]
def loopN3PreWithScratch (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
    retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  loopN3Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1

/-- Callable-ready n=3 two-iteration loop precondition with scratch cells
    and no ownership claim over `x1`. -/
@[irreducible]
def loopN3PreWithScratchNoX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  loopN3Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

/-- Callable-ready n=3 v4 loop precondition with scratch cells and no `x1`.
    The v4 call-body path also preserves the scratch cell at `sp+3936`. -/
@[irreducible]
def loopN3PreWithScratchV4NoX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 scratchMem : Word) : Assertion :=
  loopN3PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
    v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
    retMem dMem dloMem scratch_un0 **
  (sp + signExtend12 3936 ↦ₘ scratchMem)

theorem loopN3PreWithScratchV4NoX1_pcFree
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 scratchMem : Word) :
    (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old
      v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 scratchMem).pcFree := by
  delta loopN3PreWithScratchV4NoX1 loopN3PreWithScratchNoX1 loopN3Pre
  pcFree

instance pcFreeInst_loopN3PreWithScratchV4NoX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 scratchMem : Word) :
    Assertion.PCFree
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old
        v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0 scratchMem) :=
  ⟨loopN3PreWithScratchV4NoX1_pcFree sp jOld v5Old v6Old v7Old v10Old
    v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
    retMem dMem dloMem scratch_un0 scratchMem⟩

theorem loopN3PreWithScratchNoX1_unfold
    {sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word} :
    loopN3PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
      v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 =
    (loopN3Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old **
    (sp + signExtend12 3968 ↦ₘ retMem) **
    (sp + signExtend12 3960 ↦ₘ dMem) **
    (sp + signExtend12 3952 ↦ₘ dloMem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)) := by
  delta loopN3PreWithScratchNoX1
  rfl

theorem loopN3PreWithScratchNoX1_pcFree
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) :
    (loopN3PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
      v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0).pcFree := by
  delta loopN3PreWithScratchNoX1 loopN3Pre
  pcFree

instance pcFreeInst_loopN3PreWithScratchNoX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) :
    Assertion.PCFree
      (loopN3PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
        v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0) :=
  ⟨loopN3PreWithScratchNoX1_pcFree sp jOld v5Old v6Old v7Old v10Old
    v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
    retMem dMem dloMem scratch_un0⟩

theorem loopN3PreWithScratchNoX1_to_loopN3PreWithScratch
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) :
    ∀ h,
      (loopN3PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
        v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0 ** regOwn .x1) h →
      loopN3PreWithScratch sp jOld v5Old v6Old v7Old v10Old
        v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0 h := by
  intro h hp
  delta loopN3PreWithScratchNoX1 loopN3PreWithScratch at hp ⊢
  simpa only [sepConj_assoc'] using hp


-- ============================================================================
-- Three-iteration loop precondition for n=2 (j=2, j=1, j=0)
-- ============================================================================

/-- Precondition for the n=2 three-iteration loop (j starts at 2).
    Includes j=2's iteration precondition plus pre-existing atoms
    for j=1 (u0_orig_1, q1Old) and j=0 (u0_orig_0, q0Old). -/
@[irreducible]
def loopN2Pre (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_1 u0_orig_0
    q2Old q1Old q0Old : Word) : Assertion :=
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (2 : Word)) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base_2 + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base_2 + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base_2 + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base_2 + signExtend12 4072) ↦ₘ u3) **
  ((u_base_2 + signExtend12 4064) ↦ₘ uTop) **
  (q_addr_2 ↦ₘ q2Old) **
  ((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) **
  (q_addr_1 ↦ₘ q1Old) **
  ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) **
  (q_addr_0 ↦ₘ q0Old)

/-- Precondition for n=2 three-iteration loop with scratch cells.
    Used when at least one iteration may take the call (div128) path. -/
@[irreducible]
def loopN2PreWithScratch (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_1 u0_orig_0
    q2Old q1Old q0Old
    retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  loopN2Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_1 u0_orig_0 q2Old q1Old q0Old **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1

/-- Callable-ready n=2 three-iteration loop precondition with scratch cells
    and no ownership claim over `x1`. -/
@[irreducible]
def loopN2PreWithScratchNoX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0
      q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  loopN2Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_1 u0_orig_0 q2Old q1Old q0Old **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

theorem loopN2PreWithScratchNoX1_unfold
    {sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0
      q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word} :
    loopN2PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
      v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0 q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 =
    (loopN2Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0 q2Old q1Old q0Old **
    (sp + signExtend12 3968 ↦ₘ retMem) **
    (sp + signExtend12 3960 ↦ₘ dMem) **
    (sp + signExtend12 3952 ↦ₘ dloMem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)) := by
  delta loopN2PreWithScratchNoX1
  rfl

theorem loopN2PreWithScratchNoX1_pcFree
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0
      q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) :
    (loopN2PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
      v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0 q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0).pcFree := by
  delta loopN2PreWithScratchNoX1 loopN2Pre
  pcFree

instance pcFreeInst_loopN2PreWithScratchNoX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0
      q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) :
    Assertion.PCFree
      (loopN2PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
        v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0) :=
  ⟨loopN2PreWithScratchNoX1_pcFree sp jOld v5Old v6Old v7Old v10Old
    v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0
    q2Old q1Old q0Old retMem dMem dloMem scratch_un0⟩

@[irreducible]
def loopN2PreWithScratchV4NoX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0
      q2Old q1Old q0Old
      retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  loopN2PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
    v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_1 u0_orig_0 q2Old q1Old q0Old
    retMem dMem dloMem scratchUn0 **
  (sp + signExtend12 3936 ↦ₘ scratchMem)

theorem loopN2PreWithScratchV4NoX1_pcFree
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0
      q2Old q1Old q0Old
      retMem dMem dloMem scratchUn0 scratchMem : Word) :
    (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old
      v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0 q2Old q1Old q0Old
      retMem dMem dloMem scratchUn0 scratchMem).pcFree := by
  delta loopN2PreWithScratchV4NoX1
  pcFree

instance pcFreeInst_loopN2PreWithScratchV4NoX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0
      q2Old q1Old q0Old
      retMem dMem dloMem scratchUn0 scratchMem : Word) :
    Assertion.PCFree
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old
        v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem) :=
  ⟨loopN2PreWithScratchV4NoX1_pcFree sp jOld v5Old v6Old v7Old v10Old
    v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0
    q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem⟩

theorem loopN2PreWithScratchNoX1_to_loopN2PreWithScratch
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0
      q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) :
    ∀ h,
      (loopN2PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
        v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0 ** regOwn .x1) h →
      loopN2PreWithScratch sp jOld v5Old v6Old v7Old v10Old
        v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0 h := by
  intro h hp
  delta loopN2PreWithScratchNoX1 loopN2PreWithScratch at hp ⊢
  simpa only [sepConj_assoc'] using hp


-- ============================================================================
-- Two-iteration loop precondition for n=2 (j=1, j=0)
-- ============================================================================

/-- Precondition for n=2 two-iteration loop (j=1, j=0).
    Same structure as loopN3Pre but with nMem = 2. -/
@[irreducible]
def loopN2Iter10Pre (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word) : Assertion :=
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (1 : Word)) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base_1 + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base_1 + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base_1 + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base_1 + signExtend12 4072) ↦ₘ u3) **
  ((u_base_1 + signExtend12 4064) ↦ₘ uTop) **
  (q_addr_1 ↦ₘ q1Old) **
  ((u_base_0 + signExtend12 0) ↦ₘ u0Orig) **
  (q_addr_0 ↦ₘ q0Old)

/-- Precondition for n=2 two-iteration loop with scratch cells. -/
@[irreducible]
def loopN2Iter10PreWithScratch (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
    retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  loopN2Iter10Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1

/-- Callable-ready n=2 two-iteration loop precondition with scratch cells
    and no ownership claim over `x1`. -/
@[irreducible]
def loopN2Iter10PreWithScratchNoX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  loopN2Iter10Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

theorem loopN2Iter10PreWithScratchNoX1_unfold
    {sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word} :
    loopN2Iter10PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
      v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 =
    (loopN2Iter10Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old **
    (sp + signExtend12 3968 ↦ₘ retMem) **
    (sp + signExtend12 3960 ↦ₘ dMem) **
    (sp + signExtend12 3952 ↦ₘ dloMem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)) := by
  delta loopN2Iter10PreWithScratchNoX1
  rfl

theorem loopN2Iter10PreWithScratchNoX1_pcFree
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) :
    (loopN2Iter10PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
      v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0).pcFree := by
  delta loopN2Iter10PreWithScratchNoX1 loopN2Iter10Pre
  pcFree

instance pcFreeInst_loopN2Iter10PreWithScratchNoX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) :
    Assertion.PCFree
      (loopN2Iter10PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
        v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0) :=
  ⟨loopN2Iter10PreWithScratchNoX1_pcFree sp jOld v5Old v6Old v7Old v10Old
    v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
    retMem dMem dloMem scratch_un0⟩

theorem loopN2Iter10PreWithScratchNoX1_to_loopN2Iter10PreWithScratch
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) :
    ∀ h,
      (loopN2Iter10PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
        v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0 ** regOwn .x1) h →
      loopN2Iter10PreWithScratch sp jOld v5Old v6Old v7Old v10Old
        v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0 h := by
  intro h hp
  delta loopN2Iter10PreWithScratchNoX1 loopN2Iter10PreWithScratch at hp ⊢
  simpa only [sepConj_assoc'] using hp


-- ============================================================================
-- Four-iteration loop precondition for n=1 (j=3, j=2, j=1, j=0)
-- ============================================================================

/-- Precondition for the n=1 four-iteration loop (j starts at 3).
    Includes j=3's iteration precondition plus pre-existing atoms
    for j=2 (u0_orig_2, q2Old), j=1 (u0_orig_1, q1Old), and j=0 (u0_orig_0, q0Old). -/
@[irreducible]
def loopN1Pre (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_2 u0_orig_1 u0_orig_0
    q3Old q2Old q1Old q0Old : Word) : Assertion :=
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (3 : Word)) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base_3 + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base_3 + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base_3 + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base_3 + signExtend12 4072) ↦ₘ u3) **
  ((u_base_3 + signExtend12 4064) ↦ₘ uTop) **
  (q_addr_3 ↦ₘ q3Old) **
  ((u_base_2 + signExtend12 0) ↦ₘ u0_orig_2) **
  (q_addr_2 ↦ₘ q2Old) **
  ((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) **
  (q_addr_1 ↦ₘ q1Old) **
  ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) **
  (q_addr_0 ↦ₘ q0Old)

/-- Precondition for n=1 four-iteration loop with scratch cells.
    Used when at least one iteration may take the call (div128) path. -/
@[irreducible]
def loopN1PreWithScratch (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_2 u0_orig_1 u0_orig_0
    q3Old q2Old q1Old q0Old
    retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  loopN1Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_2 u0_orig_1 u0_orig_0 q3Old q2Old q1Old q0Old **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1

/-- Callable-ready n=1 four-iteration loop precondition with scratch cells
    and no ownership claim over `x1`. This lets callers frame exact return
    addresses through the loop body instead of consuming them as `regOwn .x1`. -/
@[irreducible]
def loopN1PreWithScratchNoX1 (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_2 u0_orig_1 u0_orig_0
    q3Old q2Old q1Old q0Old
    retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  loopN1Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_2 u0_orig_1 u0_orig_0 q3Old q2Old q1Old q0Old **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

theorem loopN1PreWithScratchNoX1_unfold
    {sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_2 u0_orig_1 u0_orig_0
      q3Old q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word} :
    loopN1PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old
      v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_2 u0_orig_1 u0_orig_0 q3Old q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 =
    (
    loopN1Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_2 u0_orig_1 u0_orig_0 q3Old q2Old q1Old q0Old **
    (sp + signExtend12 3968 ↦ₘ retMem) **
    (sp + signExtend12 3960 ↦ₘ dMem) **
    (sp + signExtend12 3952 ↦ₘ dloMem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)) := by
  delta loopN1PreWithScratchNoX1
  rfl

theorem loopN1PreWithScratchNoX1_pcFree
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_2 u0_orig_1 u0_orig_0
      q3Old q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) :
    (loopN1PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_2 u0_orig_1 u0_orig_0
      q3Old q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0).pcFree := by
  delta loopN1PreWithScratchNoX1 loopN1Pre
  pcFree

instance pcFreeInst_loopN1PreWithScratchNoX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_2 u0_orig_1 u0_orig_0
      q3Old q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) :
    Assertion.PCFree
      (loopN1PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0
        q3Old q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0) :=
  ⟨loopN1PreWithScratchNoX1_pcFree sp jOld v5Old v6Old v7Old v10Old v11Old
    v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0
    q3Old q2Old q1Old q0Old retMem dMem dloMem scratch_un0⟩

theorem loopN1PreWithScratchNoX1_to_loopN1PreWithScratch
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_2 u0_orig_1 u0_orig_0
      q3Old q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) :
    ∀ h,
      (loopN1PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old
        v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0
        q3Old q2Old q1Old q0Old retMem dMem dloMem scratch_un0 ** regOwn .x1) h →
      loopN1PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old
        v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0
        q3Old q2Old q1Old q0Old retMem dMem dloMem scratch_un0 h := by
  intro h hp
  delta loopN1PreWithScratchNoX1 loopN1PreWithScratch at hp ⊢
  simpa only [sepConj_assoc'] using hp


-- ============================================================================
-- Two-iteration loop precondition for n=1 (j=1, j=0)
-- ============================================================================

/-- Precondition for n=1 two-iteration loop (j=1, j=0).
    Same structure as loopN2Iter10Pre but with nMem = 1. -/
@[irreducible]
def loopN1Iter10Pre (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word) : Assertion :=
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (1 : Word)) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base_1 + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base_1 + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base_1 + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base_1 + signExtend12 4072) ↦ₘ u3) **
  ((u_base_1 + signExtend12 4064) ↦ₘ uTop) **
  (q_addr_1 ↦ₘ q1Old) **
  ((u_base_0 + signExtend12 0) ↦ₘ u0Orig) **
  (q_addr_0 ↦ₘ q0Old)

/-- Precondition for n=1 two-iteration loop with scratch cells. -/
@[irreducible]
def loopN1Iter10PreWithScratch (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
    retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  loopN1Iter10Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1

/-- Callable-ready n=1 two-iteration loop precondition with scratch cells
    and no ownership claim over `x1`. -/
@[irreducible]
def loopN1Iter10PreWithScratchNoX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  loopN1Iter10Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

theorem loopN1Iter10PreWithScratchNoX1_unfold
    {sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word} :
    loopN1Iter10PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
      v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 =
    (
    loopN1Iter10Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old **
    (sp + signExtend12 3968 ↦ₘ retMem) **
    (sp + signExtend12 3960 ↦ₘ dMem) **
    (sp + signExtend12 3952 ↦ₘ dloMem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)) := by
  delta loopN1Iter10PreWithScratchNoX1
  rfl

theorem loopN1Iter10PreWithScratchNoX1_pcFree
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) :
    (loopN1Iter10PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
      v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0).pcFree := by
  delta loopN1Iter10PreWithScratchNoX1 loopN1Iter10Pre
  pcFree

instance pcFreeInst_loopN1Iter10PreWithScratchNoX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) :
    Assertion.PCFree
      (loopN1Iter10PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
        v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0) :=
  ⟨loopN1Iter10PreWithScratchNoX1_pcFree sp jOld v5Old v6Old v7Old v10Old
    v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
    retMem dMem dloMem scratch_un0⟩

theorem loopN1Iter10PreWithScratchNoX1_to_loopN1Iter10PreWithScratch
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) :
    ∀ h,
      (loopN1Iter10PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
        v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0 ** regOwn .x1) h →
      loopN1Iter10PreWithScratch sp jOld v5Old v6Old v7Old v10Old
        v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0 h := by
  intro h hp
  delta loopN1Iter10PreWithScratchNoX1 loopN1Iter10PreWithScratch at hp ⊢
  simpa only [sepConj_assoc'] using hp


-- ============================================================================
-- Three-iteration loop precondition for n=1 (j=2, j=1, j=0)
-- ============================================================================

/-- Precondition for n=1 three-iteration loop (j=2, j=1, j=0).
    Same structure as loopN2Pre but with nMem = 1, starting at j=2. -/
@[irreducible]
def loopN1Iter210Pre (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_1 u0_orig_0
    q2Old q1Old q0Old : Word) : Assertion :=
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (2 : Word)) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base_2 + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base_2 + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base_2 + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base_2 + signExtend12 4072) ↦ₘ u3) **
  ((u_base_2 + signExtend12 4064) ↦ₘ uTop) **
  (q_addr_2 ↦ₘ q2Old) **
  ((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) **
  (q_addr_1 ↦ₘ q1Old) **
  ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) **
  (q_addr_0 ↦ₘ q0Old)

/-- Precondition for n=1 three-iteration loop with scratch cells. -/
@[irreducible]
def loopN1Iter210PreWithScratch (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_1 u0_orig_0
    q2Old q1Old q0Old
    retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  loopN1Iter210Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_1 u0_orig_0 q2Old q1Old q0Old **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1

/-- Callable-ready n=1 three-iteration loop precondition with scratch cells
    and no ownership claim over `x1`. -/
@[irreducible]
def loopN1Iter210PreWithScratchNoX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0
      q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  loopN1Iter210Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_1 u0_orig_0 q2Old q1Old q0Old **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

theorem loopN1Iter210PreWithScratchNoX1_unfold
    {sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0
      q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word} :
    loopN1Iter210PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
      v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0 q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 =
    (
    loopN1Iter210Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0 q2Old q1Old q0Old **
    (sp + signExtend12 3968 ↦ₘ retMem) **
    (sp + signExtend12 3960 ↦ₘ dMem) **
    (sp + signExtend12 3952 ↦ₘ dloMem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)) := by
  delta loopN1Iter210PreWithScratchNoX1
  rfl

theorem loopN1Iter210PreWithScratchNoX1_pcFree
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0
      q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) :
    (loopN1Iter210PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
      v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0 q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0).pcFree := by
  delta loopN1Iter210PreWithScratchNoX1 loopN1Iter210Pre
  pcFree

instance pcFreeInst_loopN1Iter210PreWithScratchNoX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0
      q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) :
    Assertion.PCFree
      (loopN1Iter210PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
        v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0) :=
  ⟨loopN1Iter210PreWithScratchNoX1_pcFree sp jOld v5Old v6Old v7Old v10Old
    v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0
    q2Old q1Old q0Old retMem dMem dloMem scratch_un0⟩

theorem loopN1Iter210PreWithScratchNoX1_to_loopN1Iter210PreWithScratch
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_1 u0_orig_0
      q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 : Word) :
    ∀ h,
      (loopN1Iter210PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old
        v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0 ** regOwn .x1) h →
      loopN1Iter210PreWithScratch sp jOld v5Old v6Old v7Old v10Old
        v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0 h := by
  intro h hp
  delta loopN1Iter210PreWithScratchNoX1 loopN1Iter210PreWithScratch at hp ⊢
  simpa only [sepConj_assoc'] using hp

-- (Removed dead defs `loopBodyPre` and `loopBodyPreWithScratch`: shared
-- one-iteration loop-body preconditions parametric on the stored divisor
-- limb count, plus a four-scratch-cell extension for the call path. Both
-- had no consumers anywhere in EvmAsm/ — call-path specs build the
-- scratch chain inline and the surface specs work directly with their
-- per-N preconditions. Authored by @pirapira;
-- implemented by Hermes-bot (evm-hermes).)

end EvmAsm.Evm64
