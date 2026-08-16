/-
  EvmAsm.Rv64.SAsm.RecKnotDemo

  **Proof of concept: a genuinely self-recursive verified machine routine.**

  The framework has never had a subroutine that calls *itself* (dispatch
  loops re-enter one loop; nothing re-enters a function).  This demo shows
  the knot can be tied with the existing machinery only:

  * the recursive edge is a `Stmt.callReg` with a **singleton handle table**
    (a direct `Stmt.call` cannot self-reference: its `callsOk` requires the
    callee's code to be absent at the call site, which is false when callee
    = caller; `callReg`'s `callsOk` has no such condition);
  * the callee handle is the routine's **own handle at a strictly smaller
    ghost index**, built by induction on that index — handle *contents*
    (`recKnotHandleAt`) are a structure literal so projections reduce, and
    only the `sound` field (`RecKnotSound`, a plain `Prop` family) recurses;
  * each activation owns a **per-frame window**: the callee's rw region is
    the caller's minus the caller's own 8-byte `ra`-spill frame, adapted at
    the call site with `FnHandle.widenRw` (the caller's spilled `ra` rides
    across the call as the widening's `preB` ghost);
  * the base case's dead call arm carries a handle with `pre := False` AND
    `post := False` — pre-False makes the (unreachable) call site
    dischargeable, post-False makes the arm's strongest-post eliminable
    (callReg's sp forgets the entry reach, so a `post := True` stub would
    leak an unprovable arm into the caller's `.post` VC).

  The routine: `recknot(x10 = n, x13 = fp)` returns `x11 = n` by recursing
  on `n - 1` (frame at `fp + 8`) and adding 1 — the minimal body whose value
  flows back through a real machine `jalr`-return chain of depth `n`.
  The stack arena is `⟨fp, 8*(n+1)⟩`: one `ra`-spill dword per activation.

  This is the mechanism the RLP task needs: `rlp_decode` mirroring the
  reference's recursion (`ethereum_rlp` 0.1.6) with a depth-budget index.
-/

import EvmAsm.Rv64.SAsm.RaSpill
import EvmAsm.Rv64.SAsm.HandleWiden
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Rv64
namespace SAsm
namespace RecKnotDemo

open Stmt

/-- Entry address of the (single) routine. -/
def rkEntry : Word := 0x1000

/-- Per-activation writable region: the `ra`-spill dword at `fp`, then the
    callee's whole window. -/
def rkRw (n : Nat) (fp : Word) : RwRegion := ⟨fp, 8 * (n + 1)⟩

/-- Ghost-free (caller-facing) precondition at index `(n, fp)`. -/
def rkPre (n : Nat) (fp : Word) : Reach :=
  fun rf _ _ => rf.get .x10 = BitVec.ofNat 64 n ∧ rf.get .x13 = fp

/-- Ghost-free postcondition: the result and the restored frame pointer. -/
def rkPost (n : Nat) (fp : Word) : Reach :=
  fun rf _ _ => rf.get .x11 = BitVec.ofNat 64 n ∧ rf.get .x13 = fp

/-- Step budget of the packaged handle at index `n` (loose; monotone). -/
def rkSteps (n : Nat) : Nat := 10 * n + 10

/-- The handle-soundness family, indexed by the recursion measure `n` and
    the frame pointer.  This is the *only* recursive component: everything
    else about the handle is a structure literal. -/
def RecKnotSound (n : Nat) (fp : Word) (cr : CodeReq) : Prop :=
  (rkRw n fp).wf →
  ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
    cpsTripleWithin (rkSteps n) rkEntry ret cr
      (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty (rkRw n fp) (rkPre n fp))
      (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty (rkRw n fp) (rkPost n fp))

/-- Handle contents at index `(n, fp)` — a literal, so `.entry`, `.pre`,
    `.post`, `.rw` reduce definitionally at every use site. -/
def recKnotHandleAt (n : Nat) (fp : Word) (cr : CodeReq)
    (hwf : (rkRw n fp).wf) (snd : RecKnotSound n fp cr) : FnHandle where
  entry := rkEntry
  code := cr
  nSteps := rkSteps n
  region := Region.empty
  rw := rkRw n fp
  pre := rkPre n fp
  post := rkPost n fp
  sound := snd hwf

/-- The dead callee for the base case's (unreachable) call arm: matches the
    caller's regions so `CalleesIn` holds, is never callable (`pre = False`)
    and never yields a post-state (`post = False`). -/
def deadHandle (rw : RwRegion) : FnHandle where
  entry := rkEntry
  code := CodeReq.empty
  nSteps := 0
  region := Region.empty
  rw := rw
  pre := fun _ _ _ => False
  post := fun _ _ _ => False
  sound := by
    intro ret _ R hR s hcr hPR hpc
    obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR
    obtain ⟨h1a, h1b, hd1, hu1, hx1, hM⟩ := hP1
    exact (asrtM_unsat (fun _ _ _ hf => hf) h1b hM).elim

/-- The ghost-indexed body family: `child` is the (already widened) callee
    handle, `v` the caller's own spilled return address. -/
def rkFnV (child : FnHandle) (n : Nat) (fp v : Word) : Fn where
  name := "recknot"
  region := Region.empty
  rw := rkRw n fp
  pre := fun rf ws _ => rf.get .x10 = BitVec.ofNat 64 n ∧ rf.get .x13 = fp
    ∧ ws.take 8 = dwordBytes v
  post := fun rf ws _ => rf.get .x11 = BitVec.ofNat 64 n ∧ rf.get .x13 = fp
    ∧ ws.take 8 = dwordBytes v
  body :=
    .ite "z" (.beq .x10 .x0)
      (.block "base" [.LI .x11 0])
      (.block "dec" [.ADDI .x10 .x10 (-1), .ADDI .x13 .x13 8,
                     .LI .x28 (BitVec.ofNat 64 0x1000)] ;;;
       .callReg "self" .x28 [child] ;;;
       .block "inc" [.ADDI .x11 .x11 1, .ADDI .x13 .x13 (-8)])

/-- Ghost-free view (what the packaged handle exposes). -/
def rkFn (child : FnHandle) (n : Nat) (fp : Word) : Fn :=
  { rkFnV child n fp 0 with
    pre := rkPre n fp
    post := rkPost n fp }

/-- The routine's code: the `ra`-spill wrapper around the flattened body.
    The flattened program does not depend on the embedded handle (a
    `callReg` flattens to `jalr ra, rs, 0` regardless), so any child
    instantiation names the same bytes. -/
def rkProg : Program :=
  (rkFn (deadHandle (rkRw 0 0)) 0 0).programRetR .x13 0 rkEntry

/-- The ambient code requirement: just the routine itself. -/
def rkCr : CodeReq := CodeReq.ofProg rkEntry rkProg

/-- Flattened code is child/ghost-independent. -/
theorem rkFnV_flatten (child : FnHandle) (n : Nat) (fp v : Word) (a : Word) :
    (rkFnV child n fp v).body.flatten a
      = (rkFn (deadHandle (rkRw 0 0)) 0 0).body.flatten a := rfl

#guard rkProg.length = 12

/-- Alignment/bounds of the callee's window follow from the caller's. -/
theorem rkRw_wf_child {n : Nat} {fp : Word} (h : (rkRw (n + 1) fp).wf) :
    (rkRw n (fp + 8)).wf := by
  obtain ⟨halign, hbound, hvalid⟩ := h
  have halign' : fp.toNat % 8 = 0 := halign
  have hbound' : fp.toNat + 8 * (n + 1 + 1) < 2 ^ 64 := hbound
  have hfp8 : (fp + (8 : Word)).toNat = fp.toNat + 8 := by
    rw [BitVec.toNat_add]
    simp only [show ((8 : Word)).toNat = 8 from rfl]
    omega
  refine ⟨?_, ?_, ?_⟩
  · show (fp + (8 : Word)).toNat % 8 = 0
    omega
  · show (fp + (8 : Word)).toNat + 8 * (n + 1) < 2 ^ 64
    omega
  · intro k hk
    have hk' : k < 8 * (n + 1) := hk
    show isValidMemAddr (fp + (8 : Word) + BitVec.ofNat 64 k) = true
    have haddr : fp + (8 : Word) + BitVec.ofNat 64 k
        = fp + BitVec.ofNat 64 (8 + k) := by
      bv_omega
    rw [haddr]
    exact hvalid (8 + k) (by show 8 + k < 8 * (n + 1 + 1); omega)

/-- The callee handle, widened to the caller's region: the caller's own
    spilled `ra` (`dwordBytes v`) rides across the call as the prefix
    frame. -/
def rkChildW (n : Nat) (fp v : Word) (hwfc : (rkRw n (fp + 8)).wf)
    (snd : RecKnotSound n (fp + 8) rkCr) : FnHandle :=
  (recKnotHandleAt n (fp + 8) rkCr hwfc snd).widenRw (rkRw (n + 1) fp)
    (dwordBytes v) []
    (by simp [recKnotHandleAt, rkRw, length_dwordBytes])
    (by simp [recKnotHandleAt, rkRw, length_dwordBytes]; omega)
    (by simp [length_dwordBytes])
    ⟨n + 1, rfl⟩

private theorem sext_neg1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by
  decide
private theorem sext_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
private theorem sext_8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
private theorem sext_neg8 : signExtend12 (-8 : BitVec 12) = (-8 : Word) := by
  decide

private theorem ofNat_succ_pred (n : Nat) :
    BitVec.ofNat 64 (n + 1) + (-1 : Word) = BitVec.ofNat 64 n := by
  bv_omega

private theorem ofNat_pred_succ (n : Nat) :
    BitVec.ofNat 64 n + (1 : Word) = BitVec.ofNat 64 (n + 1) := by
  bv_omega

private theorem fp_plus_minus (fp : Word) :
    fp + (8 : Word) + (-8 : Word) = fp := by bv_omega

/-- The caller-shaped body spec at successor index: the recursive call is
    the widened own handle one index down. -/
theorem rkFnV_spec_succ (n : Nat) (fp v : Word)
    (hn : n + 1 < 2 ^ 64)
    (hwf : (rkRw (n + 1) fp).wf)
    (hwfc : (rkRw n (fp + 8)).wf)
    (snd : RecKnotSound n (fp + 8) rkCr) :
    (rkFnV (rkChildW n fp v hwfc snd) (n + 1) fp v).SpecR (rkEntry + 4) rkCr := by
  show Fn.SpecR _ _ _
  vcgen
  case region =>
    exact ⟨Region.empty_wf, hwf⟩
  case code =>
    intro a i h
    show CodeReq.ofProg rkEntry (.SD .x13 .x1 0 ::
        ((rkFnV (rkChildW n fp v hwfc snd) (n + 1) fp v).body.flatten
            (rkEntry + 4)
          ++ [.LD .x1 .x13 0, .JALR .x0 .x1 0])) a = some i
    exact ofProg_cons_tail
      (by exact (by decide : 4 * (11 + 1) ≤ 2 ^ 64))
      a i (ofProg_mono_left a i h)
  case callees =>
    refine ⟨trivial, trivial, ?_, trivial⟩
    intro h hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    subst hmem
    exact ⟨fun a i h => h, rfl, rfl⟩
  case calls =>
    refine ⟨trivial, trivial, ⟨?_, ?_⟩, trivial⟩
    · exact (by decide :
        (((0x101C : Word) + 4) &&& ~~~(1 : Word)) = (0x101C : Word) + 4)
    · intro h hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      exact (by decide : ((0x1000 : Word) &&& ~~~(1 : Word)) = 0x1000)
  case recknot.z.e.self.pre =>
    rintro rf ws A ⟨rf₀, ws₀, hlen, ⟨⟨hx10, hx13, htake⟩, hncond⟩, rfl, rfl⟩
    refine ⟨rkChildW n fp v hwfc snd, by simp, ?_, ?_⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · refine ⟨ws.drop 8, ?_, ?_, ?_, ?_⟩
      · rw [List.length_drop]
        have hproj : (recKnotHandleAt n (fp + 8) rkCr hwfc snd).rw.len
            = 8 * (n + 1) := rfl
        rw [hproj]
        have hlen' : ws.length = 8 * (n + 1 + 1) := hlen
        omega
      · rw [List.append_nil, ← htake, List.take_append_drop]
      · -- x10 = n after the decrement
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_ne _ _ _ _ (by decide),
            RegFile.get_set_ne _ _ _ _ (by decide),
            RegFile.get_set_self _ _ _ (by decide), hx10, sext_neg1,
            ofNat_succ_pred]
      · -- x13 = fp + 8
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_ne _ _ _ _ (by decide),
            RegFile.get_set_self _ _ _ (by decide),
            RegFile.get_set_ne _ _ _ _ (by decide), hx13, sext_8]
  case recknot.post =>
    apply Stmt.sp_ite_split
    · -- then arm: unreachable at successor index (x10 = n+1 ≠ 0)
      rintro rf ws A ⟨rf₀, ws₀, hlen, ⟨⟨hx10, hx13, htake⟩, hcond⟩, rfl, rfl⟩
      exfalso
      have h0 : rf₀.get .x10 = 0 := by simpa using hcond
      rw [hx10] at h0
      bv_omega
    · -- else arm: value flows back through the recursive call
      rintro rf ws A hsp
      obtain ⟨rf₁, ws₁, hlen₁, hcall, hrf, hws⟩ := hsp
      obtain ⟨h, hmem, hpost⟩ := hcall
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      obtain ⟨win, hwl, hdecomp, hx11, hx13⟩ := hpost
      subst hrf hws
      refine ⟨?_, ?_, ?_⟩
      · -- x11 = n+1 after the increment
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_ne _ _ _ _ (by decide),
            RegFile.get_set_self _ _ _ (by decide), hx11, sext_1,
            ofNat_pred_succ]
      · -- x13 = fp after the restore
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_self _ _ _ (by decide),
            RegFile.get_set_ne _ _ _ _ (by decide), hx13, sext_neg8,
            fp_plus_minus]
      · -- the spilled ra survives: ws unchanged by the ALU block
        show List.take 8 ws = dwordBytes v
        rw [hdecomp, List.append_nil,
            List.take_append_of_le_length (by rw [length_dwordBytes]),
            List.take_of_length_le (by rw [length_dwordBytes])]

/-- The caller-shaped body spec at index zero: the call arm is dead
    (`x10 = 0` contradicts the taken branch), the base arm returns 0. -/
theorem rkFnV_spec_zero (fp v : Word) (hwf : (rkRw 0 fp).wf) :
    (rkFnV (deadHandle (rkRw 0 fp)) 0 fp v).SpecR (rkEntry + 4) rkCr := by
  show Fn.SpecR _ _ _
  vcgen
  case region =>
    exact ⟨Region.empty_wf, hwf⟩
  case code =>
    intro a i h
    show CodeReq.ofProg rkEntry (.SD .x13 .x1 0 ::
        ((rkFnV (deadHandle (rkRw 0 fp)) 0 fp v).body.flatten (rkEntry + 4)
          ++ [.LD .x1 .x13 0, .JALR .x0 .x1 0])) a = some i
    exact ofProg_cons_tail
      (by exact (by decide : 4 * (11 + 1) ≤ 2 ^ 64))
      a i (ofProg_mono_left a i h)
  case callees =>
    refine ⟨trivial, trivial, ?_, trivial⟩
    intro h hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    subst hmem
    refine ⟨?_, rfl, rfl⟩
    intro a i h
    cases h
  case calls =>
    refine ⟨trivial, trivial, ⟨?_, ?_⟩, trivial⟩
    · exact (by decide :
        (((0x101C : Word) + 4) &&& ~~~(1 : Word)) = (0x101C : Word) + 4)
    · intro h hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      exact (by decide : ((0x1000 : Word) &&& ~~~(1 : Word)) = 0x1000)
  case recknot.z.e.self.pre =>
    rintro rf ws A ⟨rf₀, ws₀, hlen, ⟨⟨hx10, hx13, htake⟩, hncond⟩, rfl, rfl⟩
    exfalso
    exact hncond (by show rf₀.get .x10 = rf₀.get .x0; rw [hx10]; rfl)
  case recknot.post =>
    apply Stmt.sp_ite_split
    · -- then arm: return 0
      rintro rf ws A ⟨rf₀, ws₀, hlen, ⟨⟨hx10, hx13, htake⟩, hcond⟩, rfl, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_self _ _ _ (by decide)]
        rfl
      · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        rw [RegFile.get_set_ne _ _ _ _ (by decide), hx13]
      · show List.take 8 ws = dwordBytes v
        exact htake
    · -- else arm: dead (post = False)
      rintro rf ws A hsp
      obtain ⟨rf₁, ws₁, hlen₁, hcall, hrf, hws⟩ := hsp
      obtain ⟨h, hmem, hpost⟩ := hcall
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      exact hpost.elim

-- ============================================================================
-- The knot: handle soundness by induction on the measure
-- ============================================================================

private theorem rk_haddr (n : Nat) (fp : Word) :
    ∀ rf (ws : List (BitVec 8)) (A : Assertion), rkPre n fp rf ws A →
      rf.get .x13 + signExtend12 0 = fp + BitVec.ofNat 64 0 := by
  intro rf ws A h
  rw [h.2, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
  rfl

private theorem rk_haddrPost (child : FnHandle) (n : Nat) (fp : Word) :
    ∀ (v : Word) rf (ws : List (BitVec 8)) (A : Assertion),
      (rkFnV child n fp v).post rf ws A →
      rf.get .x13 + signExtend12 0 = fp + BitVec.ofNat 64 0 := by
  intro v rf ws A h
  rw [h.2.1, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
  rfl

private theorem rk_hspre (child : FnHandle) (n : Nat) (fp : Word) :
    ∀ (v : Word) rf (ws : List (BitVec 8)) (A : Assertion),
      rkPre n fp rf ws A → ws.length = 8 * (n + 1) →
      (rkFnV child n fp v).pre rf (setBytes ws 0 (dwordBytes v)) A := by
  intro v rf ws A h hlen
  refine ⟨h.1, h.2, ?_⟩
  have hs := setBytes_slot ws (dwordBytes v) 0
    (by rw [length_dwordBytes]; omega)
  rw [List.drop_zero, length_dwordBytes] at hs
  exact hs

private theorem rk_hspost (child : FnHandle) (n : Nat) (fp : Word) :
    ∀ (v : Word) rf (ws : List (BitVec 8)) (A : Assertion),
      (rkFnV child n fp v).post rf ws A → rkPost n fp rf ws A :=
  fun _ _ _ _ h => ⟨h.1, h.2.1⟩

private theorem rk_hslot (child : FnHandle) (n : Nat) (fp : Word) :
    ∀ (v : Word) rf (ws : List (BitVec 8)) (A : Assertion),
      (rkFnV child n fp v).post rf ws A → ws.length = 8 * (n + 1) →
      (ws.drop 0).take 8 = dwordBytes v := by
  intro v rf ws A h _
  rw [List.drop_zero]
  exact h.2.2

private theorem rkSteps_zero_bound (fp : Word) :
    1 + (rkFn (deadHandle (rkRw 0 fp)) 0 fp).body.steps + 2 ≤ rkSteps 0 := by
  simp only [rkFn, rkFnV, Stmt.steps, deadHandle, List.foldr,
    List.length_cons, List.length_nil, rkSteps]
  omega

private theorem rkSteps_succ_bound (n : Nat) (fp v : Word)
    (hwfc : (rkRw n (fp + 8)).wf) (snd : RecKnotSound n (fp + 8) rkCr) :
    1 + (rkFn (rkChildW n fp v hwfc snd) (n + 1) fp).body.steps + 2
      ≤ rkSteps (n + 1) := by
  simp only [rkFn, rkFnV, Stmt.steps, rkChildW, FnHandle.widenRw,
    recKnotHandleAt, List.foldr, List.length_cons, List.length_nil, rkSteps]
  omega

/-- **The recursion knot**: the routine's handle contract holds at every
    index, by induction on the measure `n`. -/
theorem recKnotSound : ∀ (n : Nat) (fp : Word), RecKnotSound n fp rkCr := by
  intro n
  induction n with
  | zero =>
    intro fp hwf ret halign
    refine cpsTripleWithin_mono_nSteps (rkSteps_zero_bound fp) ?_
    exact Fn.retSpecR (rkFn (deadHandle (rkRw 0 fp)) 0 fp) rkEntry rkCr
      .x13 0 0
      (fun v => (rkFnV (deadHandle (rkRw 0 fp)) 0 fp v).pre)
      (fun v => (rkFnV (deadHandle (rkRw 0 fp)) 0 fp v).post)
      (by decide) hwf ⟨0, rfl⟩ (by show 0 + 8 ≤ 8 * (0 + 1); omega)
      (by exact (by decide : 4 * (9 + 3) ≤ 2 ^ 64))
      (fun v => rkFnV_spec_zero fp v hwf)
      (fun a i h => h)
      (rk_haddr 0 fp)
      (rk_haddrPost (deadHandle (rkRw 0 fp)) 0 fp)
      (rk_hspre (deadHandle (rkRw 0 fp)) 0 fp)
      (rk_hspost (deadHandle (rkRw 0 fp)) 0 fp)
      (rk_hslot (deadHandle (rkRw 0 fp)) 0 fp)
      ret halign
  | succ n ih =>
    intro fp hwf ret halign
    have hwfc : (rkRw n (fp + 8)).wf := rkRw_wf_child hwf
    have snd : RecKnotSound n (fp + 8) rkCr := ih (fp + 8)
    have hn : n + 1 < 2 ^ 64 := by
      have h2 := hwf.2.1
      have h2' : fp.toNat + 8 * (n + 1 + 1) < 2 ^ 64 := h2
      omega
    refine cpsTripleWithin_mono_nSteps (rkSteps_succ_bound n fp 0 hwfc snd) ?_
    exact Fn.retSpecR (rkFn (rkChildW n fp 0 hwfc snd) (n + 1) fp) rkEntry rkCr
      .x13 0 0
      (fun v => (rkFnV (rkChildW n fp v hwfc snd) (n + 1) fp v).pre)
      (fun v => (rkFnV (rkChildW n fp v hwfc snd) (n + 1) fp v).post)
      (by decide) hwf ⟨0, rfl⟩ (by show 0 + 8 ≤ 8 * (n + 1 + 1); omega)
      (by exact (by decide : 4 * (9 + 3) ≤ 2 ^ 64))
      (fun v => rkFnV_spec_succ n fp v hn hwf hwfc snd)
      (fun a i h => h)
      (rk_haddr (n + 1) fp)
      (fun v => rk_haddrPost (rkChildW n fp v hwfc snd) (n + 1) fp v)
      (fun v => rk_hspre (rkChildW n fp v hwfc snd) (n + 1) fp v)
      (fun v => rk_hspost (rkChildW n fp v hwfc snd) (n + 1) fp v)
      (fun v => rk_hslot (rkChildW n fp v hwfc snd) (n + 1) fp v)
      ret halign

/-- The packaged handle at any index — a self-recursive verified routine. -/
def recKnotHandle (n : Nat) (fp : Word) (hwf : (rkRw n fp).wf) : FnHandle :=
  recKnotHandleAt n fp rkCr hwf (recKnotSound n fp)

-- ============================================================================
-- Anti-vacuity: the contract is inhabited and the code actually runs
-- ============================================================================

/-- The stack arena at `0x10000` is well-formed for depth 3. -/
theorem rkRw_wf_3 : (rkRw 3 0x10000).wf := by decide

/-- The handle exists at a concrete index — the premise set is inhabited. -/
def recKnotHandle3 : FnHandle := recKnotHandle 3 0x10000 rkRw_wf_3

/-- Concrete emulation: load the 12 instructions at `0x1000`, enter with
    `x10 = 3`, `x13 = 0x10000`, `ra = 0x2000`, run to completion.  The final
    state must sit at the return address with `x11 = 3` — the value built by
    three genuine recursive activations returning through `jalr`. -/
private def rkTestRun : Option (Word × Word) := do
  let s0 : MachineState := {
    regs := fun r => if r = .x10 then 3 else if r = .x13 then 0x10000
      else if r = .x1 then 0x2000 else 0
    mem := fun _ => 0
    code := rkCr
    pc := rkEntry }
  let s ← stepN 36 s0
  some (s.pc, s.regs .x11)

#guard rkTestRun = some (0x2000, 3)

end RecKnotDemo
end SAsm
end EvmAsm.Rv64
