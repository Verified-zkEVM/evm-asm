/-
  EvmAsm.Rv64.SAsm.Fn

  SAsm functions: a body with an entry condition and an exit condition over
  the exposed register file.  Ghost data (input byte lists, lengths, …)
  enters through the ambient Lean binders of the defining `def`.

  `Fn.Spec` is the ordinary bounded CPS triple of the flattened body;
  `Fn.sound` reduces it to the labeled pure VCs, which the `vcgen` tactic
  (Tactic.lean) splits into named goals.

  Design: docs/sasm-design.md §3.6.  `Fn.SpecR`/`Fn.soundR` are the
  caller-shaped variants for bodies containing calls; `Fn.toHandle` packages
  a verified call-free function (plus the `jalr` return epilogue) as a
  callee `FnHandle`.
-/

import EvmAsm.Rv64.SAsm.StmtSoundCall

namespace EvmAsm.Rv64
namespace SAsm

/-- An SAsm function: entry/exit conditions over the exposed register file
    around a structured body. -/
structure Fn where
  name : String
  pre : Reach
  post : Reach
  body : Stmt
  /-- The function's read-only byte region (`Region.empty` when no memory
      is touched). -/
  region : Region := Region.empty
  /-- The function's writable byte region (`RwRegion.empty` when nothing is
      written).  Its contents live in the symbolic state. -/
  rw : RwRegion := RwRegion.empty

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
    (f.codeReq base) (asrtM f.region f.rw f.pre) (asrtM f.region f.rw f.post)

/-- The function's labeled verification conditions:
    - `<name>.flat`: offsets fit and the code does not wrap (decidable;
      `vcgen` discharges it with `decide`);
    - the body's VCs;
    - `<name>.post`: the strongest postcondition entails the stated one. -/
def vcs (f : Fn) : List VC :=
  ⟨f.name ++ ".flat", f.body.callFree = true ∧ f.body.offsetsOk = true
      ∧ 4 * f.body.size < 2 ^ 64⟩ ::
  (Stmt.vcs f.region f.rw f.body (f.name ++ ".") f.pre ++
   [⟨f.name ++ ".post",
      ∀ rf ws, Stmt.sp f.region f.rw f.body f.pre rf ws → f.post rf ws⟩])

/-- Soundness: the labeled pure VCs imply the CPS triple. -/
theorem sound (f : Fn) (base : Word) (hreg : f.region.wf ∧ f.rw.wf)
    (h : VCs.Hold f.vcs) : f.Spec base := by
  have hflat := h.head
  have hbody := Stmt.sound f.region f.rw f.body base (f.name ++ ".") f.pre
    hreg.1 hreg.2 hflat.1 hflat.2.1 hflat.2.2 (fun _ _ hc => hc) h.tail.left
  have hpost := h.tail.right.head
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (asrtM_mono (fun rf ws hsp => hpost rf ws hsp))
    hbody

-- ============================================================================
-- Caller-shaped specs (bodies that may contain calls) — Milestone M4
-- ============================================================================

/-- Caller-shaped correctness: like `Spec` but at `asrtR` granularity
    (`ra` owned, its value forgotten across calls), against an ambient `cr`
    that must contain the body's code and every callee's code. -/
def SpecR (f : Fn) (base : Word) (cr : CodeReq) : Prop :=
  cpsTripleWithin f.body.steps base (base + BitVec.ofNat 64 (4 * f.body.size))
    cr (asrtR f.region f.rw f.pre) (asrtR f.region f.rw f.post)

/-- VCs of a caller-shaped function (no `callFree` requirement). -/
def vcsR (f : Fn) : List VC :=
  ⟨f.name ++ ".flat", f.body.offsetsOk = true ∧ 4 * f.body.size < 2 ^ 64⟩ ::
  (Stmt.vcs f.region f.rw f.body (f.name ++ ".") f.pre ++
   [⟨f.name ++ ".post",
      ∀ rf ws, Stmt.sp f.region f.rw f.body f.pre rf ws → f.post rf ws⟩])

/-- Caller-shaped soundness.  `hcode`/`hcallees` locate the body's and the
    callees' code inside `cr`; `hcalls` are the call sites' address side
    conditions (`decide`/`bv_omega` for concrete or relative layouts). -/
theorem soundR (f : Fn) (base : Word) (cr : CodeReq)
    (hreg : f.region.wf ∧ f.rw.wf)
    (hcode : ∀ a i, CodeReq.ofProg base (f.body.flatten base) a = some i →
      cr a = some i)
    (hcallees : f.body.CalleesIn f.region f.rw cr)
    (hcalls : f.body.callsOk base)
    (h : VCs.Hold f.vcsR) : f.SpecR base cr := by
  have hflat := h.head
  have hbody := Stmt.soundR f.region f.rw f.body base (f.name ++ ".") f.pre
    hreg.1 hreg.2 hflat.1 hflat.2 hcode hcallees hcalls h.tail.left
  have hpost := h.tail.right.head
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (asrtR_mono (fun rf ws hsp => hpost rf ws hsp))
    hbody

-- ============================================================================
-- Packaging a verified (call-free) function as a callee handle
-- ============================================================================

/-- The function's code with the C-ABI return epilogue. -/
def programRet (f : Fn) (base : Word) : Program :=
  f.body.flatten base ++ [.JALR .x0 .x1 0]

/-- `jalr x0, ra, 0`: return to the (aligned) address held in `ra`,
    changing nothing else. -/
theorem jalr_ret_spec (base ret : Word) (halign : (ret &&& ~~~(1 : Word)) = ret)
    {P : Assertion} (hP : P.pcFree) :
    cpsTripleWithin 1 base ret (CodeReq.singleton base (.JALR .x0 .x1 0))
      ((.x1 ↦ᵣ ret) ** P) ((.x1 ↦ᵣ ret) ** P) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.JALR .x0 .x1 0) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hstep' : step s = some (execInstrBr s (.JALR .x0 .x1 0)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) rfl
  have hx1 : s.getReg .x1 = ret :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hexec : execInstrBr s (.JALR .x0 .x1 0) = s.setPC ret := by
    rw [execInstrBr_jalr_x0, hx1]
    congr 1
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show ret + (0 : Word) = ret from by bv_omega]
    exact halign
  refine ⟨1, Nat.le_refl 1, s.setPC ret, ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec]; rfl
  · exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj (by pcFree) hP) hR) hPR

/-- A verified call-free function, with the return epilogue, satisfies the
    `FnHandle` calling contract: enter with any aligned return address in
    `ra`, come back to it with `post` and `ra` intact. -/
theorem retSpec (f : Fn) (base : Word) (hspec : f.Spec base)
    (hsz : 4 * (f.body.size + 1) ≤ 2 ^ 64) :
    ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin (f.body.steps + 1) base ret
        (CodeReq.ofProg base (f.programRet base))
        ((.x1 ↦ᵣ ret) ** asrtM f.region f.rw f.pre)
        ((.x1 ↦ᵣ ret) ** asrtM f.region f.rw f.post) := by
  intro ret halign
  have hla : (f.body.flatten base).length = f.body.size := Stmt.flatten_length ..
  -- body triple, framed with the untouched return address
  have h1 := cpsTripleWithin_frameR (.x1 ↦ᵣ ret) (by pcFree) hspec
  rw [sepConj_comm' (asrtM f.region f.rw f.pre), sepConj_comm' (asrtM f.region f.rw f.post)] at h1
  have h1' := cpsTripleWithin_extend_code
    (ofProg_mono_left (p2 := [.JALR .x0 .x1 0])) h1
  -- return epilogue
  have h2 := jalr_ret_spec (base + BitVec.ofNat 64 (4 * f.body.size)) ret halign
    (pcFree_asrtM f.region f.rw f.post)
  have h2' := cpsTripleWithin_extend_code
    (fun a i h => ofProg_mono_right (p1 := f.body.flatten base)
      (p2 := [.JALR .x0 .x1 0])
      (by simp [hla]; omega)
      a i (by rw [hla, CodeReq.ofProg_singleton]; exact h)) h2
  exact cpsTripleWithin_seq_same_cr h1' h2'

/-- Package a verified call-free function as a callee handle
    (docs/sasm-design.md §3.6). -/
def toHandle (f : Fn) (base : Word) (hspec : f.Spec base)
    (hsz : 4 * (f.body.size + 1) ≤ 2 ^ 64) : FnHandle where
  entry := base
  code := CodeReq.ofProg base (f.programRet base)
  nSteps := f.body.steps + 1
  region := f.region
  rw := f.rw
  pre := f.pre
  post := f.post
  sound := f.retSpec base hspec hsz

end Fn

end SAsm
end EvmAsm.Rv64
