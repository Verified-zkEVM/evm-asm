/-
  EvmAsm.Evm64.DivMod.BzeroPublicPostFramed

  Bzero lane wrapper at the public dispatch-post surface, framed with the
  `memOwn (sp + signExtend12 3936)` atom from the V4 callable surface.

  This makes the bzero wrapper compose uniformly with the N1/N2/N3
  callable→public-post bridges (PRs #7047/#7049/#7050), all of which carry
  the same `memOwn 3936` framing artifact.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.UnifiedBzero
public import EvmAsm.Rv64.SepLogic
public import EvmAsm.Rv64.CPSSpec

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Bzero lane at the public dispatch-post surface, framed with the
    `memOwn (sp + 3936)` atom to match the N1/N2/N3 callable→public-post
    output shape. -/
theorem evm_div_bzero_stack_spec_within_dispatch_publicPost_framed
    (sp base : Word) (a b : EvmWord)
    (v1 v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (scratchMem : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPost sp a b **
       memOwn (sp + signExtend12 3936)) := by
  -- Frame the (sp + 3936) memory cell on the right of the existing dispatch
  -- bzero theorem.
  have hbase := evm_div_bzero_stack_spec_within_dispatch_uni sp base a b
    v1 v2 v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 hbz
  -- Frame ((sp+3936) ↦ₘ scratchMem) into both pre and post, then weaken post
  -- to memOwn.
  have hframed := cpsTripleWithin_frameR
    ((sp + signExtend12 3936) ↦ₘ scratchMem) pcFree_memIs hbase
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by
      obtain ⟨h1, h2, hd, hu, hL, hR⟩ := hp
      exact ⟨h1, h2, hd, hu, hL, memIs_implies_memOwn _ hR⟩)
    hframed

end EvmAsm.Evm64
