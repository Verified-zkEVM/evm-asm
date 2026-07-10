/-
  EvmAsm.Rv64.SAsm.AccumLoop

  The **single-exit accumulate loop** (bead evm-asm-pr5lu).

  `DualReadScan` (#10038) covers early-exit dual-read equality scans;
  `bloom_eq` is the SINGLE-EXIT variant: a constant-cycle XOR/OR
  accumulate over two buffers (no early exit — timing invariance), with
  the verdict derived from the accumulator and stored through an `SD` to
  an rw out-cell:

  ```
        li   ctr, N ; mv pA, a0 ; mv pB, a1 ; li acc, 0
  hdr:  beq  ctr, x0, .done
        ld   tA, 0(pA) ; ld tB, 0(pB)
        xor  tA, tA, tB ; or acc, acc, tA
        addi pA, pA, 8 ; addi pB, pB, 8 ; addi ctr, ctr, -1 ; j hdr
  .done: sltiu acc, acc, 1 ; sd acc, 0(out) ; li a0, 0 ; ret
  ```

  Three reusable pieces:

  * `retLoop_spec` — the single-exit countdown loop at `cpsTripleWithin`
    level: each iteration is an ordinary triple back to the header (no
    break arm); exhaustion runs the tail to `ret`.  Derived from
    `twoBreakRetLoop_spec` (#10067) with the early-return arm vacuous.

  * `xorAcc` + `xorAcc_eq_zero_iff_bytes_eq` — the OR-of-XOR dword-slot
    accumulator and its **result bridge**: the accumulator is zero after
    `N` slots iff the two `8·N`-byte lists are EQUAL (per-slot facts via
    `xorAcc_eq_zero_iff`, then #10038's `bytes_eq_of_dwordSlots_eq`) —
    what turns the accumulator residue into the genuine equality post.

  * `bytesRegion_ld_cursor_within` — dword load through an ADVANCING
    cursor (`LD rd, 0(rs1)` with `rs1 = base + 8q`), the cursor analogue
    of `bytesRegion_ld_within` (#10060, fixed base + immediate).

  Consumer: `bloom_eq` (`Codegen/Programs/BloomEqSAsm.lean`).
  Everything additive, `cpsTripleWithin` level.
-/

import EvmAsm.Rv64.SAsm.TwoBreakWritable
import EvmAsm.Rv64.SAsm.DualReadScan
import EvmAsm.Rv64.SAsm.SelectedRead

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

/-- **The single-exit countdown loop**: every iteration is an ordinary
    triple back to the header (no break arm); after `N` iterations the
    exhaustion path runs the tail to `ret` with the final post.  The
    degenerate (vacuous-break) instance of `twoBreakRetLoop_spec`. -/
theorem retLoop_spec {hdr ret : Word} {cr : CodeReq} {Q : Assertion}
    (N m e : Nat) (inv : Nat → Assertion)
    (hiter : ∀ i, i < N → cpsTripleWithin m hdr hdr cr (inv i) (inv (i + 1)))
    (hexh : cpsTripleWithin e hdr ret cr (inv N) Q) :
    cpsTripleWithin (N * m + e) hdr ret cr (inv 0) Q :=
  twoBreakRetLoop_spec N m e inv
    (fun i hi => cpsTripleWithin_as_cpsBranchWithin_right ret Q (hiter i hi))
    hexh

namespace AccumLoop

/-- The OR-of-XOR dword-slot accumulator after `i` slots: zero exactly
    when every processed slot pair matched. -/
def xorAcc (bsA bsB : List (BitVec 8)) : Nat → Word
  | 0 => 0
  | i + 1 => xorAcc bsA bsB i
      ||| (dwordSlot bsA i ^^^ dwordSlot bsB i)

@[simp] theorem xorAcc_zero (bsA bsB : List (BitVec 8)) :
    xorAcc bsA bsB 0 = 0 := rfl

theorem xorAcc_succ (bsA bsB : List (BitVec 8)) (i : Nat) :
    xorAcc bsA bsB (i + 1) = (xorAcc bsA bsB i
      ||| (dwordSlot bsA i ^^^ dwordSlot bsB i)) :=
  rfl

private theorem or_eq_zero_iff (a b : Word) :
    (a ||| b) = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    constructor
    · apply BitVec.eq_of_getLsbD_eq
      intro i _hi
      have hbit := congrArg (fun w : Word => w.getLsbD i) h
      simp only [BitVec.getLsbD_or] at hbit
      simp only [show ((0 : Word)).getLsbD i = false from by
        simp [BitVec.getLsbD]] at hbit ⊢
      exact (Bool.or_eq_false_iff.mp hbit).1
    · apply BitVec.eq_of_getLsbD_eq
      intro i _hi
      have hbit := congrArg (fun w : Word => w.getLsbD i) h
      simp only [BitVec.getLsbD_or] at hbit
      simp only [show ((0 : Word)).getLsbD i = false from by
        simp [BitVec.getLsbD]] at hbit ⊢
      exact (Bool.or_eq_false_iff.mp hbit).2
  · rintro ⟨rfl, rfl⟩
    simp

private theorem xor_eq_zero_iff (a b : Word) : (a ^^^ b) = 0 ↔ a = b := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i _hi
    have hbit := congrArg (fun w : Word => w.getLsbD i) h
    simp only [BitVec.getLsbD_xor] at hbit
    simp only [show ((0 : Word)).getLsbD i = false from by
      simp [BitVec.getLsbD]] at hbit
    revert hbit
    cases a.getLsbD i <;> cases b.getLsbD i <;> simp
  · rintro rfl
    simp

/-- The accumulator → per-slot bridge: zero after `N` slots iff every
    slot pair matched. -/
theorem xorAcc_eq_zero_iff (bsA bsB : List (BitVec 8)) (N : Nat) :
    xorAcc bsA bsB N = 0
      ↔ ∀ j, j < N →
          dwordSlot bsA j = dwordSlot bsB j := by
  induction N with
  | zero =>
      constructor
      · intro _ j hj
        exact absurd hj (Nat.not_lt_zero j)
      · intro _
        rfl
  | succ n ih =>
      rw [xorAcc_succ, or_eq_zero_iff, ih, xor_eq_zero_iff]
      constructor
      · rintro ⟨hall, hn⟩ j hj
        by_cases hjn : j < n
        · exact hall j hjn
        · have : j = n := by omega
          subst this
          exact hn
      · intro h
        exact ⟨fun j hj => h j (by omega), h n (by omega)⟩

/-- **The result bridge**: the accumulator is zero after `N` slots iff
    the two `8·N`-byte lists are EQUAL — the genuine equality post of a
    single-exit accumulate compare (per-slot facts + #10038's
    `bytes_eq_of_dwordSlots_eq`). -/
theorem xorAcc_eq_zero_iff_bytes_eq (bsA bsB : List (BitVec 8)) (N : Nat)
    (hlenA : bsA.length = 8 * N) (hlenB : bsB.length = 8 * N) :
    xorAcc bsA bsB N = 0 ↔ bsA = bsB := by
  rw [xorAcc_eq_zero_iff]
  constructor
  · exact bytes_eq_of_dwordSlots_eq N bsA bsB hlenA hlenB
  · intro h j _
    exact dwordSlot_congr h j

end AccumLoop

/-- **`LD rd, 0(rs1)` through an advancing cursor** reads dword chunk `q`
    of the region when `rs1 = base + 8q` — the cursor analogue of
    `bytesRegion_ld_within` (fixed base + immediate). -/
theorem bytesRegion_ld_cursor_within (rd rs1 : Reg) (regionBase vOld : Word)
    (base : Word) (bs : List (BitVec 8)) (q : Nat)
    (hrd : rd ≠ .x0) (hq : 8 * q < bs.length) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LD rd rs1 (0 : BitVec 12)))
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 (8 * q))) ** (rd ↦ᵣ vOld) **
        bytesRegion regionBase bs)
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 (8 * q))) **
        (rd ↦ᵣ packBytes ((bs.drop (8 * q)).take 8)) **
        bytesRegion regionBase bs) := by
  obtain ⟨front, rest, hf, hr, heq⟩ := bytesRegion_dword_at regionBase bs q hq
  have hld := ld_spec_gen_within rd rs1 (regionBase + BitVec.ofNat 64 (8 * q))
    vOld (packBytes ((bs.drop (8 * q)).take 8)) (0 : BitVec 12) base hrd
  rw [show (regionBase + BitVec.ofNat 64 (8 * q)) + signExtend12 (0 : BitVec 12)
      = regionBase + BitVec.ofNat 64 (8 * q) from by
    rw [signExtend12_0]
    bv_omega] at hld
  rw [heq]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq' => by xperm_hyp hq')
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hr) hld)

#print axioms retLoop_spec
#print axioms AccumLoop.xorAcc_eq_zero_iff_bytes_eq
#print axioms bytesRegion_ld_cursor_within

end EvmAsm.Rv64.SAsm
