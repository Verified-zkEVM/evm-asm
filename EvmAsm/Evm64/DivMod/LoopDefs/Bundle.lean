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

import EvmAsm.Rv64.SepLogic

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
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
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
  (sp + signExtend12 3944 ↦ₘ scratch_un0)


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
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (2 : Word)) **
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
  (sp + signExtend12 3944 ↦ₘ scratch_un0)


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
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
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
  (sp + signExtend12 3944 ↦ₘ scratch_un0)


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
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (3 : Word)) **
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
  (sp + signExtend12 3944 ↦ₘ scratch_un0)


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
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
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
  (sp + signExtend12 3944 ↦ₘ scratch_un0)


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
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (2 : Word)) **
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
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

-- ============================================================================
-- One-iteration loop body precondition (parametric on limb count n)
-- ============================================================================

/-- Precondition for a single-iteration loop body (no scratch cells).
    Shared across max_skip, max_addback, and the unified max-path specs.
    Parametric on `n : Word` (the stored divisor limb count, used only in the
    `sp + signExtend12 3984 ↦ₘ n` cell). -/
@[irreducible]
def loopBodyPre (n : Word)
    (sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
  ((uBase + signExtend12 4064) ↦ₘ uTop) **
  (qAddr ↦ₘ qOld)

/-- Precondition for a single-iteration loop body with scratch cells (call path).
    Shared across call_skip, call_addback, and the unified call-path specs. -/
@[irreducible]
def loopBodyPreWithScratch (n : Word)
    (sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
     retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  loopBodyPre n sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

end EvmAsm.Evm64
