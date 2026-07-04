/-
  EvmAsm.Rv64.SAsm.Handle

  The C-like caller interface of a verified routine (docs/sasm-design.md
  §3.6): everything a call site needs, deliberately forgetting the body.

  A handle's `sound` field says: called with any aligned return address in
  `ra` and the exposed register file satisfying `pre`, the routine returns
  to that address within `nSteps` steps with the register file satisfying
  `post` (ghost data is baked in through the ambient binders used when the
  handle is constructed).  `Fn.toHandle` (Fn.lean) packages a verified
  call-free SAsm function this way; hand-verified routines can be packaged
  by proving the same shape directly.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SAsm.RegionSound

namespace EvmAsm.Rv64
namespace SAsm

/-- Caller-facing interface of a verified routine in the project's C-like
    ABI: arguments/results in the exposed a-registers (constrained by
    `pre`/`post`), `ra` respected, everything outside the exposed register
    file and `code` framed. -/
structure FnHandle where
  entry : Word
  code : CodeReq
  nSteps : Nat
  region : Region
  rw : RwRegion
  pre : Reach
  post : Reach
  sound : ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
    cpsTripleWithin nSteps entry ret code
      ((.x1 ↦ᵣ ret) ** asrtM region rw pre)
      ((.x1 ↦ᵣ ret) ** asrtM region rw post)

/-- The one-point reachable set: exactly the symbolic state
    `(rf₀, ws₀, A₀)`.  Used to state snapshot-parameterized callee
    contracts (`FnHandleS`): the callee family is verified at every
    concrete entry state, so its postcondition may *depend* on that
    state. -/
def Reach.exact (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion) :
    Reach :=
  fun rf ws A => rf = rf₀ ∧ ws = ws₀ ∧ A = A₀

/-- Caller-facing interface of a verified routine whose postcondition is
    parameterized by the *entry snapshot* (docs/4ch8f-interp-strategy.md).

    A monomorphic `FnHandle` states one fixed `pre`/`post` pair, which
    cannot relate the callee's exit state to its entry state — fatal for
    a state-transforming callee invoked repeatedly at one call site (an
    opcode handler inside the dispatch loop).  `FnHandleS` is the
    universally-quantified (auxiliary-variable) contract: `sound` holds
    at every concrete entry state satisfying `pre`, with the exit state
    constrained by `post rf₀ ws₀ A₀` — the callee analogue of
    `Stmt.whileS`'s entry-snapshot invariants. -/
structure FnHandleS where
  entry : Word
  code : CodeReq
  nSteps : Nat
  region : Region
  rw : RwRegion
  pre : Reach
  post : RegFile → List (BitVec 8) → Assertion → Reach
  sound : ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
    ws₀.length = rw.len → A₀.pcFree → pre rf₀ ws₀ A₀ →
    ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
    cpsTripleWithin nSteps entry ret code
      ((.x1 ↦ᵣ ret) ** asrtM region rw (Reach.exact rf₀ ws₀ A₀))
      ((.x1 ↦ᵣ ret) ** asrtM region rw (post rf₀ ws₀ A₀))

/-- A stub handle with an unsatisfiable precondition: lets `Stmt` values
    mention a routine that is not verified yet.  Any call to it generates
    an unprovable `.pre` VC, so nothing can be concluded past it. -/
def FnHandle.stub (entry : Word) : FnHandle where
  entry := entry
  code := CodeReq.empty
  nSteps := 0
  region := Region.empty
  rw := RwRegion.empty
  pre := fun _ _ _ => False
  post := fun _ _ _ => True
  sound := by
    intro ret _ R hR s hcr hPR hpc
    obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR
    obtain ⟨h1a, h1b, hd1, hu1, hx1, hM⟩ := hP1
    exact (asrtM_unsat (fun _ _ _ hf => hf) h1b hM).elim

end SAsm
end EvmAsm.Rv64
