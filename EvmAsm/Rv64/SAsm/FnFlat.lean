/-
  EvmAsm.Rv64.SAsm.FnFlat

  **The flat-contract adapter** (bead evm-asm-el1w2): derive a
  `callWithin_spec`/`abiFrameCall_spec`-consumable FLAT callee contract from
  an existing call-free leaf's `Fn.Spec` — so any leaf that already has an
  `Fn.Spec` becomes a usable callee for the ABI-frame cross-call rules
  without a hand-written per-callee flat theorem.

  ## The bridge

  `Fn.retSpec` already gives the right OUTER shape (`ra := ret` in, `ra`
  intact out, any aligned `ret`), but over `asrtM` — an existential around
  `regFileIs rf` (ONE indivisible atom owning the whole exposed register
  file) plus the rw-region bytes.  A flat ABI-frame caller works with
  individual `↦ᵣ`/`regOwn` atoms.  This file supplies:

  * `regFileIs_eq_regAtoms` — the pack/unpack: `regFileIs rf` IS the
    separated conjunction of the fifteen exposed-register atoms (a genuine
    partial-state identity, both directions);
  * `Fn.retSpecFlat` — the adapter: instantiates the `asrtM` precondition
    at a caller-chosen `rf`/`ws` (ambient `empAssertion`) and eliminates the
    postcondition existential into a caller-chosen flat `Q`, FAITHFULLY —
    `Q` must follow from the leaf's own `f.post` (hypothesis `hpost`), so
    the adapter cannot be instantiated to anything the leaf's spec does not
    guarantee;
  * `cpsTripleWithin_peel_regOwns` — generic ownership peeling over a
    register list, so derived contracts can expose don't-care registers as
    `regOwn` riders instead of concrete values.

  ## Inherent side-conditions (named; see the porting guide §5a)

  1. **Footprint width**: an adapted contract owns the WHOLE exposed file
     (that is what `Fn.Spec` claims) — the caller carries `regOwn` riders
     for the registers it doesn't track.  A hand-written flat theorem can be
     strictly stronger (smaller footprint); the adapter trades that for
     zero per-callee boilerplate.
  2. **Post completeness**: the adapter carries exactly `f.post` — if the
     caller needs a final register value (e.g. the advanced `a0` cursor),
     the leaf's `Fn` post must pin it (the strongest-post already tracks
     it; strengthening the `Fn` post is a small local edit).
  3. **Ambient pinning** (`hpostEmp`): the leaf's post must pin the ambient
     `A = empAssertion` (leaves own no pointer-shaped extras); posts that
     are silent on `A` cannot identify the residual ambient across the
     existential.

  Strictly additive: `cpsTripleWithin` level only.
-/

import EvmAsm.Rv64.SAsm.Fn
import EvmAsm.Rv64.SAsm.AbiFrameLoopBottom
import EvmAsm.Rv64.SAsm.RaSpill
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64
namespace SAsm

open EvmAsm.Rv64.Tactics

-- ============================================================================
-- regFileIs ↔ separated register atoms.
-- ============================================================================

/-- The separated conjunction of `(r ↦ᵣ rf.get r)` over a register list. -/
def regAtoms (rf : RegFile) : List Reg → Assertion
  | [] => empAssertion
  | r :: rs => (r ↦ᵣ rf.get r) ** regAtoms rf rs

@[simp] theorem regAtoms_nil (rf : RegFile) : regAtoms rf [] = empAssertion := rfl

@[simp] theorem regAtoms_cons (rf : RegFile) (r : Reg) (rs : List Reg) :
    regAtoms rf (r :: rs) = ((r ↦ᵣ rf.get r) ** regAtoms rf rs) := rfl

theorem pcFree_regAtoms (rf : RegFile) (rs : List Reg) : (regAtoms rf rs).pcFree := by
  induction rs with
  | nil => exact pcFree_emp
  | cons r rs ih => exact pcFree_sepConj pcFree_regIs ih

/-- The partial state owning exactly the registers in `rs`, valued by `rf`. -/
private def stateOver (rf : RegFile) (rs : List Reg) : PartialState where
  regs := fun r => if r ∈ rs then some (rf.get r) else none
  mem := fun _ => none
  code := fun _ => none
  pc := none

private theorem stateOver_nil (rf : RegFile) : stateOver rf [] = PartialState.empty := by
  simp only [stateOver, PartialState.empty, List.not_mem_nil, if_false]

private theorem stateOver_cons (rf : RegFile) (r : Reg) (rs : List Reg)
    (hr_notin : r ∉ rs) :
    PartialState.union (PartialState.singletonReg r (rf.get r)) (stateOver rf rs)
      = stateOver rf (r :: rs) := by
  simp only [PartialState.union, PartialState.singletonReg, stateOver]
  congr 1
  funext r'
  by_cases hrr : r' = r
  · subst hrr
    simp [List.mem_cons]
  · simp only [beq_iff_eq, hrr, if_false, List.mem_cons]
    by_cases hmem : r' ∈ rs <;> simp [hmem]

private theorem singletonReg_disjoint_stateOver (rf : RegFile) (r : Reg)
    (v : Word) (rs : List Reg) (hr_notin : r ∉ rs) :
    (PartialState.singletonReg r v).Disjoint (stateOver rf rs) := by
  refine ⟨fun r' => ?_, fun a => Or.inl rfl, fun a => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  by_cases hrr : r' = r
  · subst hrr
    right
    simp only [stateOver, if_neg hr_notin]
  · left
    simp [PartialState.singletonReg, hrr]

private theorem regAtoms_eq_stateOver (rf : RegFile) (rs : List Reg)
    (hnd : rs.Nodup) :
    ∀ h, regAtoms rf rs h ↔ h = stateOver rf rs := by
  induction rs with
  | nil =>
    intro h
    rw [stateOver_nil]
    exact Iff.rfl
  | cons r rs ih =>
    have hr_notin : r ∉ rs := (List.nodup_cons.mp hnd).1
    have hnd' : rs.Nodup := (List.nodup_cons.mp hnd).2
    intro h
    constructor
    · rintro ⟨h1, h2, hd, hu, hh1, hh2⟩
      rw [regIs] at hh1
      rw [(ih hnd' h2).mp hh2] at hu
      subst hh1
      rw [← hu]
      exact stateOver_cons rf r rs hr_notin
    · intro hp
      refine ⟨PartialState.singletonReg r (rf.get r), stateOver rf rs,
        singletonReg_disjoint_stateOver rf r (rf.get r) rs hr_notin, ?_, rfl,
        (ih hnd' _).mpr rfl⟩
      rw [hp]
      exact stateOver_cons rf r rs hr_notin

/-- **Pack/unpack**: ownership of the whole exposed register file is exactly
    the separated conjunction of the fifteen exposed-register atoms. -/
theorem regFileIs_eq_regAtoms (rf : RegFile) :
    regFileIs rf = regAtoms rf exposedRegs := by
  funext h
  apply propext
  rw [regAtoms_eq_stateOver rf exposedRegs (by decide)]
  show h = PartialState.ofRegFile rf ↔ h = stateOver rf exposedRegs
  have : PartialState.ofRegFile rf = stateOver rf exposedRegs := by
    simp only [PartialState.ofRegFile, stateOver]
    congr 1
    funext r
    by_cases hex : Reg.isExposed r
    · rw [if_pos hex, if_pos ((Reg.isExposed_iff_mem r).mp hex)]
    · rw [if_neg hex, if_neg (fun hmem =>
        hex ((Reg.isExposed_iff_mem r).mpr hmem))]
  rw [this]

-- ============================================================================
-- Generic ownership peeling over a register list.
-- ============================================================================

/-- `regOwn` over a register list. -/
def regOwns : List Reg → Assertion
  | [] => empAssertion
  | r :: rs => regOwn r ** regOwns rs

@[simp] theorem regOwns_nil : regOwns [] = empAssertion := rfl

@[simp] theorem regOwns_cons (r : Reg) (rs : List Reg) :
    regOwns (r :: rs) = (regOwn r ** regOwns rs) := rfl

theorem pcFree_regOwns (rs : List Reg) : (regOwns rs).pcFree := by
  induction rs with
  | nil => exact pcFree_emp
  | cons r rs ih => exact pcFree_sepConj pcFree_regOwn ih

/-- Atoms valued by an arbitrary valuation `vf` (not through `RegFile.get`,
    so `x0` never needs special-casing here). -/
def regAtomsOf (vf : Reg → Word) : List Reg → Assertion
  | [] => empAssertion
  | r :: rs => (r ↦ᵣ vf r) ** regAtomsOf vf rs

@[simp] theorem regAtomsOf_nil (vf : Reg → Word) : regAtomsOf vf [] = empAssertion := rfl

@[simp] theorem regAtomsOf_cons (vf : Reg → Word) (r : Reg) (rs : List Reg) :
    regAtomsOf vf (r :: rs) = ((r ↦ᵣ vf r) ** regAtomsOf vf rs) := rfl

theorem pcFree_regAtomsOf (vf : Reg → Word) (rs : List Reg) :
    (regAtomsOf vf rs).pcFree := by
  induction rs with
  | nil => exact pcFree_emp
  | cons r rs ih => exact pcFree_sepConj pcFree_regIs ih

theorem regAtomsOf_congr (vf vf' : Reg → Word) (rs : List Reg)
    (h : ∀ r ∈ rs, vf r = vf' r) : regAtomsOf vf rs = regAtomsOf vf' rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [regAtomsOf_cons, regAtomsOf_cons, h r (List.mem_cons_self ..),
      ih (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))]

/-- **Generic ownership peeling**: to prove a triple whose precondition
    exposes a register list only as `regOwns rs`, it suffices to prove it
    for every concrete valuation of those registers.  Folds
    `cpsTripleWithin_of_forall_regIs_to_regOwn` over the (duplicate-free)
    list. -/
theorem cpsTripleWithin_peel_regOwns (rs : List Reg) (hnd : rs.Nodup)
    {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq} {P Q : Assertion}
    (h : ∀ vf : Reg → Word,
      cpsTripleWithin nSteps entry exit_ cr (P ** regAtomsOf vf rs) Q) :
    cpsTripleWithin nSteps entry exit_ cr (P ** regOwns rs) Q := by
  induction rs generalizing P with
  | nil => exact h (fun _ => 0)
  | cons r rs ih =>
    have hr_notin : r ∉ rs := (List.nodup_cons.mp hnd).1
    have hnd' : rs.Nodup := (List.nodup_cons.mp hnd).2
    -- (P ** (regOwn r ** regOwns rs)) → peel `regOwn r` first, then recurse.
    rw [regOwns_cons]
    refine cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := r)
        (P := P ** regOwns rs) (fun vOld => ?_))
    -- ((P ** regOwns rs) ** (r ↦ᵣ vOld)) : recurse on rs with P extended.
    refine cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
      (ih hnd' (P := P ** (r ↦ᵣ vOld)) (fun vf => ?_))
    -- ((P ** (r ↦ᵣ vOld)) ** regAtomsOf vf rs) → h at the combined valuation.
    have hcomb := h (fun r' => if r' = r then vOld else vf r')
    rw [show regAtomsOf (fun r' => if r' = r then vOld else vf r') (r :: rs)
          = ((r ↦ᵣ vOld) ** regAtomsOf vf rs) from by
        rw [regAtomsOf_cons,
            regAtomsOf_congr (fun r' => if r' = r then vOld else vf r') vf rs
              (fun r' hr' => by
                show (if r' = r then vOld else vf r') = vf r'
                rw [if_neg]
                rintro rfl
                exact hr_notin hr')]
        congr 1
        show regIs r (if r = r then vOld else vf r) = regIs r vOld
        rw [if_pos rfl]] at hcomb
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) hcomb

-- ============================================================================
-- The adapter: Fn.Spec → flat callee contract.
-- ============================================================================

/-- Introduce `asrtOf`: a concrete register file + rw-window pair with the
    reach's pure fact (ambient `empAssertion`) is one witness. -/
theorem asrtOf_intro (rw : RwRegion) (reach : Reach) (rf : RegFile)
    (ws : List (BitVec 8)) (hlen : ws.length = rw.len)
    (hreach : reach rf ws empAssertion) :
    ∀ hp, ((regFileIs rf) ** bytesRegion rw.base ws) hp → asrtOf rw reach hp := by
  intro hp hh
  exact ⟨rf, ws, empAssertion, hlen, pcFree_emp, hreach,
    (sepConj_emp_right' ((regFileIs rf) ** bytesRegion rw.base ws)).symm ▸ hh⟩

/-- Eliminate `asrtOf` into a caller-chosen flat `Q`, FAITHFULLY: `Q` must
    follow from the reach itself (for every witness), so nothing weaker than
    the leaf's own postcondition can be produced.  Requires the reach to pin
    its ambient to `empAssertion` (leaves own no pointer-shaped extras). -/
theorem asrtOf_elim (rw : RwRegion) (reach : Reach) {Q : Assertion}
    (hEmp : ∀ rf ws A, reach rf ws A → A = empAssertion)
    (h : ∀ (rf : RegFile) (ws : List (BitVec 8)), ws.length = rw.len →
      reach rf ws empAssertion →
      ∀ hp, ((regFileIs rf) ** bytesRegion rw.base ws) hp → Q hp) :
    ∀ hp, asrtOf rw reach hp → Q hp := by
  rintro hp ⟨rf, ws, A, hlen, hApc, hreach, hsts⟩
  have hA := hEmp rf ws A hreach
  subst hA
  rw [sepConj_emp_right'] at hsts
  exact h rf ws hlen hreach hp hsts

/-- **The flat-contract adapter** (bead evm-asm-el1w2).

    From a call-free leaf's `Fn.Spec`, derive the whole-routine flat callee
    contract `callWithin_spec`/`abiFrameCall_spec` consume: entered at
    `base` with any aligned return address in `ra`, the exposed register
    file at a caller-chosen valuation `rf`, and the leaf's rw window `ws`
    (`f.pre` holding), it returns to `ra` with `ra` intact and a
    caller-chosen flat `Q` that — via `hpost` — must FOLLOW from the leaf's
    own `f.post`: the adapter cannot be instantiated to anything the leaf's
    spec does not guarantee.  The leaf's read-only region rides framed on
    the outside (it is `empAssertion` when `f.region = Region.empty`).

    Combine with `regFileIs_eq_regAtoms` (split the file into the fifteen
    exposed atoms) and `cpsTripleWithin_peel_regOwns` (expose don't-care
    registers as `regOwn` riders) to shape the contract for a flat caller —
    see `Bn254Fq12SetOneSAsm.bnqZeroFlat_spec` for the worked pattern. -/
theorem Fn.retSpecFlat (f : Fn) (base : Word) (hspec : f.Spec base)
    (hsz : 4 * (f.body.size + 1) ≤ 2 ^ 64)
    (ret : Word) (halign : (ret &&& ~~~(1 : Word)) = ret)
    (rf : RegFile) (ws : List (BitVec 8))
    (hlen : ws.length = f.rw.len)
    (hpre : f.pre rf ws empAssertion)
    {Q : Assertion}
    (hpostEmp : ∀ rf' ws' A, f.post rf' ws' A → A = empAssertion)
    (hpost : ∀ (rf' : RegFile) (ws' : List (BitVec 8)),
      ws'.length = f.rw.len → f.post rf' ws' empAssertion →
      ∀ hp, ((regFileIs rf') ** bytesRegion f.rw.base ws') hp → Q hp) :
    cpsTripleWithin (f.body.steps + 1) base ret
      (CodeReq.ofProg base (f.programRet base))
      ((((.x1 : Reg) ↦ᵣ ret) ** (regFileIs rf) ** bytesRegion f.rw.base ws)
        ** bytesRegion f.region.base f.region.bytes)
      ((((.x1 : Reg) ↦ᵣ ret) ** Q) ** bytesRegion f.region.base f.region.bytes) := by
  have hr := Fn.retSpec f base hspec hsz ret halign
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hr
  · -- flat pre ⊢ (x1 ↦ ret) ** asrtM f.region f.rw f.pre
    have hp1 : ((((.x1 : Reg) ↦ᵣ ret)
        ** ((regFileIs rf) ** bytesRegion f.rw.base ws))
        ** bytesRegion f.region.base f.region.bytes) h := by
      xperm_hyp hp
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (asrtOf_intro f.rw f.pre rf ws hlen hpre)) h hp1
    show (((.x1 : Reg) ↦ᵣ ret) ** asrtM f.region f.rw f.pre) h
    unfold asrtM
    xperm_hyp hp2
  · -- (x1 ↦ ret) ** asrtM f.region f.rw f.post ⊢ flat post
    unfold asrtM at hq
    have hq1 : ((((.x1 : Reg) ↦ᵣ ret) ** asrtOf f.rw f.post)
        ** bytesRegion f.region.base f.region.bytes) h := by
      xperm_hyp hq
    exact sepConj_mono_left (sepConj_mono_right
      (asrtOf_elim f.rw f.post hpostEmp hpost)) h hq1

-- ============================================================================
-- Glue: atoms → ownership, `get` elimination, dword-region ↔ byte-region.
-- ============================================================================

/-- Forget the concrete values of an atom list (pointwise `regIs → regOwn`). -/
theorem regAtomsOf_to_regOwns (vf : Reg → Word) (rs : List Reg) :
    ∀ h, regAtomsOf vf rs h → regOwns rs h := by
  induction rs with
  | nil => exact fun _ hp => hp
  | cons r rs ih =>
    exact fun h hp => sepConj_mono (regIs_to_regOwn r (vf r)) ih h hp

/-- Over an `x0`-free register list, `regAtoms` (valued through
    `RegFile.get`) and `regAtomsOf` (raw valuation) coincide. -/
theorem regAtoms_eq_regAtomsOf (rf : RegFile) (rs : List Reg)
    (hx0 : Reg.x0 ∉ rs) :
    regAtoms rf rs = regAtomsOf (fun r => rf r) rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hr : r ≠ .x0 := fun hc => hx0 (hc ▸ List.mem_cons_self ..)
    rw [regAtoms_cons, regAtomsOf_cons,
      ih (fun hmem => hx0 (List.mem_cons_of_mem _ hmem)),
      show rf.get r = rf r from by rw [RegFile.get, if_neg hr]]

/-- The writable dword-array region IS a byte region (little-endian dword
    chunks) — the bridge between dword-flavored flat contracts and the
    byte-flavored `Fn` rw window. -/
theorem dwordsIs_eq_bytesRegion (base : Word) (vs : List Word) :
    dwordsIs base vs = bytesRegion base (vs.flatMap dwordBytes) := by
  induction vs generalizing base with
  | nil => rw [List.flatMap_nil, dwordsIs_nil, bytesRegion_nil]
  | cons v vs ih =>
    rw [List.flatMap_cons, dwordsIs_cons, ih,
      bytesRegion_eq_cons base _ (by
        intro hc
        have := congrArg List.length hc
        simp [length_dwordBytes] at this),
      List.take_left' (length_dwordBytes v),
      List.drop_left' (length_dwordBytes v),
      packBytes_dwordBytes]

/-- Zero dwords flatten to zero bytes. -/
theorem replicate_zero_flatMap_dwordBytes (n : Nat) :
    (List.replicate n (0 : Word)).flatMap dwordBytes
      = List.replicate (8 * n) (0 : BitVec 8) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.flatMap_cons, ih,
      show dwordBytes (0 : Word) = List.replicate 8 (0 : BitVec 8) from by decide,
      ← List.replicate_add,
      show 8 + 8 * k = 8 * (k + 1) from by omega]

theorem length_flatMap_dwordBytes (vs : List Word) :
    (vs.flatMap dwordBytes).length = 8 * vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [List.flatMap_cons, List.length_append, length_dwordBytes, ih,
      List.length_cons]
    omega

end SAsm
end EvmAsm.Rv64

#print axioms EvmAsm.Rv64.SAsm.regFileIs_eq_regAtoms
#print axioms EvmAsm.Rv64.SAsm.cpsTripleWithin_peel_regOwns
#print axioms EvmAsm.Rv64.SAsm.Fn.retSpecFlat
