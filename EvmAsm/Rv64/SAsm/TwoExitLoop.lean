/-
  EvmAsm.Rv64.SAsm.TwoExitLoop

  **Two-exit countdown loops + cursor-immediate dword reads** (bead
  evm-asm-4ch8f.43.1, the exec-log scan kit).

  `twoBreakRetLoop_spec` (#10067) folds a loop whose break and exhaustion
  arms reach the SAME continuation.  The BAL validators' exec-log scans
  exit to DIFFERENT continuations: a mid-cascade full match breaks to the
  FOUND join, while running out of entries falls through to the reject
  stub — and in the pointer-countdown form the exhaustion test lives at
  the BOTTOM of the round (`bne cursor, base, hdr`), so the last round is
  itself two-exit.  Two folds, both concluding `cpsBranchWithin`:

  * `twoExitRetLoop_spec` — head-exhaustion variant (final round is a
    plain triple to `exitB`);
  * `twoExitRetLoopBottom_spec` — bottom-test variant (final round is
    itself a two-exit branch) — the exec-log scan shape.

  Plus `bytesRegion_ld_cursor_imm_within`: `LD rd, (8*q)(rs1)` with
  `rs1 = regionBase + 8*q0` reads dword slot `q0 + q` — generalizing
  `bytesRegion_ld_within` (`q0 = 0`, SelectedRead) and
  `bytesRegion_ld_cursor_within` (`q = 0`, AccumLoop); the 128-byte
  log-entry field compares (`ld x29, 0/8/…/56(x28)`) are exactly this.

  Everything additive, `cpsTripleWithin`/`cpsBranchWithin` level — no
  `Ast`/`Vc`/`StmtSound` changes.
-/

import EvmAsm.Rv64.SAsm.TwoBreakWritable
import EvmAsm.Rv64.SAsm.AccumLoop

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

/-- Two-exit countdown loop: per-iteration branch either BREAKS to `exitA`
    (with `QA`) or returns to the header with the next invariant; exhaustion
    exits to `exitB` (with `QB`).  `twoBreakRetLoop_spec` generalized to
    DISTINCT break and exhaustion continuations. -/
theorem twoExitRetLoop_spec {hdr exitA exitB : Word} {cr : CodeReq}
    {QA QB : Assertion}
    (N m e : Nat) (inv : Nat → Assertion)
    (hiter : ∀ j, j < N →
      cpsBranchWithin m hdr cr (inv j) exitA QA hdr (inv (j + 1)))
    (hexh : cpsTripleWithin e hdr exitB cr (inv N) QB) :
    cpsBranchWithin (N * m + e) hdr cr (inv 0) exitA QA exitB QB := by
  suffices h : ∀ M j, j + M = N →
      cpsBranchWithin (M * m + e) hdr cr (inv j) exitA QA exitB QB from
    h N 0 (by omega)
  intro M
  induction M with
  | zero =>
      intro j hj
      rw [show j = N from by omega]
      simpa using cpsTripleWithin_as_cpsBranchWithin_right exitA QA hexh
  | succ n ih =>
      intro j hj
      have hstayA : cpsBranchWithin (n * m + e) exitA cr QA exitA QA exitB QB := by
        intro R hR s hcr hQR hpc
        exact ⟨0, Nat.zero_le _, s, rfl, Or.inl ⟨hpc, hQR⟩⟩
      have hmerge := cpsBranchWithin_merge_branch_same_cr
        (hiter j (by omega)) hstayA (ih (j + 1) (by omega))
      rw [show (n + 1) * m + e = m + (n * m + e) from by
        rw [Nat.succ_mul]; omega]
      exact hmerge

/-- Bottom-test two-exit countdown loop: each of the first `N` rounds either
    BREAKS to `exitA` or returns to the header; the FINAL round is itself a
    two-exit branch (`exitA` or `exitB`).  The exec-log scan shape: FOUND can
    fire in any round, ABSENT only in the last (`bne cursor, base`
    fall-through). -/
theorem twoExitRetLoopBottom_spec {hdr exitA exitB : Word} {cr : CodeReq}
    {QA QB : Assertion}
    (N m e : Nat) (inv : Nat → Assertion)
    (hiter : ∀ j, j < N →
      cpsBranchWithin m hdr cr (inv j) exitA QA hdr (inv (j + 1)))
    (hlast : cpsBranchWithin e hdr cr (inv N) exitA QA exitB QB) :
    cpsBranchWithin (N * m + e) hdr cr (inv 0) exitA QA exitB QB := by
  suffices h : ∀ M j, j + M = N →
      cpsBranchWithin (M * m + e) hdr cr (inv j) exitA QA exitB QB from
    h N 0 (by omega)
  intro M
  induction M with
  | zero =>
      intro j hj
      rw [show j = N from by omega]
      simpa using hlast
  | succ n ih =>
      intro j hj
      have hstayA : cpsBranchWithin (n * m + e) exitA cr QA exitA QA exitB QB := by
        intro R hR s hcr hQR hpc
        exact ⟨0, Nat.zero_le _, s, rfl, Or.inl ⟨hpc, hQR⟩⟩
      have hmerge := cpsBranchWithin_merge_branch_same_cr
        (hiter j (by omega)) hstayA (ih (j + 1) (by omega))
      rw [show (n + 1) * m + e = m + (n * m + e) from by
        rw [Nat.succ_mul]; omega]
      exact hmerge

/-- Dword load through an advanced cursor PLUS a small immediate:
    `LD rd, (8*q)(rs1)` with `rs1 = regionBase + 8*q0` reads dword slot
    `q0 + q` of the region. -/
theorem bytesRegion_ld_cursor_imm_within (rd rs1 : Reg) (regionBase vOld : Word)
    (base : Word) (bs : List (BitVec 8)) (q0 q : Nat)
    (hrd : rd ≠ .x0) (hq : 8 * (q0 + q) < bs.length) (himm : 8 * q < 2 ^ 11) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LD rd rs1 (BitVec.ofNat 12 (8 * q))))
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 (8 * q0))) ** (rd ↦ᵣ vOld) **
        bytesRegion regionBase bs)
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 (8 * q0))) **
        (rd ↦ᵣ packBytes ((bs.drop (8 * (q0 + q))).take 8)) **
        bytesRegion regionBase bs) := by
  obtain ⟨front, rest, hf, hr, heq⟩ := bytesRegion_dword_at regionBase bs (q0 + q) hq
  have hld := ld_spec_gen_within rd rs1 (regionBase + BitVec.ofNat 64 (8 * q0))
    vOld (packBytes ((bs.drop (8 * (q0 + q))).take 8)) (BitVec.ofNat 12 (8 * q)) base hrd
  rw [show (regionBase + BitVec.ofNat 64 (8 * q0)) + signExtend12 (BitVec.ofNat 12 (8 * q))
      = regionBase + BitVec.ofNat 64 (8 * (q0 + q)) from by
    rw [signExtend12_ofNat_small (8 * q) himm]
    rw [BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega] at hld
  rw [heq]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hr) hld)

/-- Range-separated `ofProg`s are disjoint: if the two 4-byte-per-slot code
    windows `[base1, base1 + 4·len1)` and `[base2, base2 + 4·len2)` do not
    overlap (as non-wrapping `toNat` ranges), the code requirements are
    disjoint — ONE range argument instead of `len1 × len2` per-pair address
    inequalities (the `crDisjoint` blow-up on 100+-instruction routines).
    At concrete linked addresses all three side conditions are
    `decide +kernel`. -/
theorem _root_.EvmAsm.Rv64.CodeReq.Disjoint.ofProg_ranges (base1 base2 : Word)
    (p1 p2 : List Instr)
    (hw1 : base1.toNat + 4 * p1.length ≤ 2 ^ 64)
    (hw2 : base2.toNat + 4 * p2.length ≤ 2 ^ 64)
    (hsep : base1.toNat + 4 * p1.length ≤ base2.toNat ∨
            base2.toNat + 4 * p2.length ≤ base1.toNat) :
    (CodeReq.ofProg base1 p1).Disjoint (CodeReq.ofProg base2 p2) := by
  intro a
  by_cases h1 : ∃ k, k < p1.length ∧ a = base1 + BitVec.ofNat 64 (4 * k)
  · right
    obtain ⟨k, hk, rfl⟩ := h1
    apply CodeReq.ofProg_none_range
    intro k' hk' heq
    have := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    omega
  · left
    apply CodeReq.ofProg_none_range
    intro k hk heq
    exact h1 ⟨k, hk, heq⟩

#print axioms twoExitRetLoop_spec
#print axioms twoExitRetLoopBottom_spec
#print axioms bytesRegion_ld_cursor_imm_within
#print axioms EvmAsm.Rv64.CodeReq.Disjoint.ofProg_ranges

end EvmAsm.Rv64.SAsm
