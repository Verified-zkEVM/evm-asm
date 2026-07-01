/-
  EvmAsm.Rv64.SAsm.Fn

  SAsm functions: a body with an entry condition and an exit condition over
  the exposed register file.  Ghost data (input byte lists, lengths, …)
  enters through the ambient Lean binders of the defining `def`.

  `Fn.Spec` is the ordinary bounded CPS triple of the flattened body;
  `Fn.sound` reduces it to the labeled pure VCs, which the `vcgen` tactic
  (Tactic.lean) splits into named goals.

  Design: docs/sasm-design.md §3.6 (the `FnHandle` caller interface and the
  `ret` epilogue land with calls in Milestone M4).
-/

import EvmAsm.Rv64.SAsm.StmtSound

namespace EvmAsm.Rv64
namespace SAsm

/-- An SAsm function: entry/exit conditions over the exposed register file
    around a structured body. -/
structure Fn where
  name : String
  pre : Reach
  post : Reach
  body : Stmt

namespace Fn

/-- The flattened machine code of the function at `base`. -/
def program (f : Fn) (base : Word) : Program :=
  f.body.flatten base

/-- The function's code requirement: one contiguous `ofProg`, no manual
    disjointness anywhere. -/
def codeReq (f : Fn) (base : Word) : CodeReq :=
  CodeReq.ofProg base (f.program base)

/-- The function's correctness statement: an ordinary bounded CPS triple of
    the flattened body, from `asrtOf pre` to `asrtOf post`, within
    `body.steps` machine steps. -/
def Spec (f : Fn) (base : Word) : Prop :=
  cpsTripleWithin f.body.steps base (base + BitVec.ofNat 64 (4 * f.body.size))
    (f.codeReq base) (asrtOf f.pre) (asrtOf f.post)

/-- The function's labeled verification conditions:
    - `<name>.flat`: offsets fit and the code does not wrap (decidable;
      `vcgen` discharges it with `decide`);
    - the body's VCs;
    - `<name>.post`: the strongest postcondition entails the stated one. -/
def vcs (f : Fn) : List VC :=
  ⟨f.name ++ ".flat", f.body.callFree = true ∧ f.body.offsetsOk = true
      ∧ 4 * f.body.size < 2 ^ 64⟩ ::
  (f.body.vcs (f.name ++ ".") f.pre ++
   [⟨f.name ++ ".post", ∀ rf, f.body.sp f.pre rf → f.post rf⟩])

/-- Soundness: the labeled pure VCs imply the CPS triple. -/
theorem sound (f : Fn) (base : Word) (h : VCs.Hold f.vcs) : f.Spec base := by
  have hflat := h.head
  have hbody := Stmt.sound f.body base (f.name ++ ".") f.pre
    hflat.1 hflat.2.1 hflat.2.2 (fun _ _ hc => hc) h.tail.left
  have hpost := h.tail.right.head
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun hp hh => by
      obtain ⟨rf, hrf, hsp⟩ := hh
      exact ⟨rf, hrf, hpost rf hsp⟩)
    hbody

end Fn

end SAsm
end EvmAsm.Rv64
