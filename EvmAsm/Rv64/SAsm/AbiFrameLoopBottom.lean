/-
  EvmAsm.Rv64.SAsm.AbiFrameLoopBottom

  Two reusable pieces for the bottom-test (`do-while`) converter loops the
  guest emits everywhere (`bnq_zero`/`bnq_copy`/`blq_*` and the other
  4ch8f.58 helpers), companions to `countdownLoop_spec` (top-guard shape):

  * `dwordsIs base vs` — a writable dword-array region: `|vs|` consecutive
    owned dword cells holding `vs`.  `dwordsIs_at_set` extracts the `p`-th
    cell with a SHARED frame for both the old and the updated list, so a
    plain `sd` lands exactly on `vs.set p w` — the store-side analogue of
    `bytesRegion_dword_at_set` at dword granularity.

  * `countdownLoopBottom_spec` — the register-agnostic bottom-decrement
    do-while loop:

    ```
      hdr:  <body>                  -- decrements ctr (n+1 → n)
      tst:  bne  ctr, x0, backOff   -- back-edge to hdr while ctr ≠ 0
      exit:                         -- tst + 4
    ```

    Given a per-iteration body triple, the whole loop runs `ctr` from
    `N ≥ 1` down to `0` (a do-while executes its body at least once).  As
    with `countdownLoop_spec`, `ctr` and the invariant family are FREE, so
    they may reference callee-saved `s`-registers.

  Strictly additive: `cpsTripleWithin` only.
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64
namespace SAsm

open EvmAsm.Rv64.Tactics

-- ============================================================================
-- The writable dword-array region.
-- ============================================================================

/-- `|vs|` consecutive owned dword cells from `base`, holding `vs`. -/
def dwordsIs (base : Word) : List Word → Assertion
  | [] => empAssertion
  | v :: vs => (base ↦ₘ v) ** dwordsIs (base + 8) vs

@[simp] theorem dwordsIs_nil (base : Word) : dwordsIs base [] = empAssertion := rfl

@[simp] theorem dwordsIs_cons (base : Word) (v : Word) (vs : List Word) :
    dwordsIs base (v :: vs) = ((base ↦ₘ v) ** dwordsIs (base + 8) vs) := rfl

theorem pcFree_dwordsIs (base : Word) (vs : List Word) : (dwordsIs base vs).pcFree := by
  induction vs generalizing base with
  | nil => exact pcFree_emp
  | cons v vs ih => exact pcFree_sepConj pcFree_memIs (ih _)

private theorem sepConj_assoc_eq {P Q R : Assertion} :
    ((P ** Q) ** R) = (P ** (Q ** R)) := by
  funext h; exact propext (sepConj_assoc h)

private theorem sepConj_emp_left_eq {P : Assertion} : (empAssertion ** P) = P := by
  funext h; exact propext (sepConj_emp_left h)

private theorem addr_shift (base : Word) (k : Nat) :
    (base + 8) + BitVec.ofNat 64 (8 * k) = base + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show ((8 : Word)).toNat = 8 from by decide]
  omega

/-- Extract the `p`-th dword cell with a frame SHARED between `vs` and
    `vs.set p w`: a store on that cell lands exactly on the updated array. -/
theorem dwordsIs_at_set (base : Word) (vs : List Word) (p : Nat) (w : Word)
    (hp : p < vs.length) :
    ∃ front rest : Assertion, front.pcFree ∧ rest.pcFree ∧
      dwordsIs base vs
        = (front ** (((base + BitVec.ofNat 64 (8 * p)) ↦ₘ vs.getD p 0) ** rest)) ∧
      dwordsIs base (vs.set p w)
        = (front ** (((base + BitVec.ofNat 64 (8 * p)) ↦ₘ w) ** rest)) := by
  induction p generalizing base vs with
  | zero =>
    obtain ⟨v, vs', rfl⟩ : ∃ v vs', vs = v :: vs' := by
      cases vs with
      | nil => exact absurd hp (by simp)
      | cons v vs' => exact ⟨v, vs', rfl⟩
    have haddr : base + BitVec.ofNat 64 (8 * 0) = base := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, show (8 * 0 : Nat) = 0 from rfl, BitVec.toNat_ofNat]
      have := base.isLt
      omega
    refine ⟨empAssertion, dwordsIs (base + 8) vs', pcFree_emp, pcFree_dwordsIs _ _, ?_, ?_⟩
    · rw [dwordsIs_cons, haddr, sepConj_emp_left_eq]; rfl
    · rw [show (v :: vs').set 0 w = w :: vs' from rfl, dwordsIs_cons, haddr,
        sepConj_emp_left_eq]
  | succ k ih =>
    obtain ⟨v, vs', rfl⟩ : ∃ v vs', vs = v :: vs' := by
      cases vs with
      | nil => exact absurd hp (by simp)
      | cons v vs' => exact ⟨v, vs', rfl⟩
    have hk : k < vs'.length := by simpa using hp
    obtain ⟨front', rest', hf', hr', heq1, heq2⟩ := ih (base + 8) vs' hk
    refine ⟨(base ↦ₘ v) ** front', rest', pcFree_sepConj pcFree_memIs hf', hr', ?_, ?_⟩
    · rw [dwordsIs_cons, heq1, addr_shift, ← sepConj_assoc_eq]; rfl
    · rw [show (v :: vs').set (k + 1) w = v :: vs'.set k w from rfl, dwordsIs_cons,
        heq2, addr_shift, ← sepConj_assoc_eq]

-- ============================================================================
-- The bottom-test countdown loop.
-- ============================================================================

private theorem word_ofNat_succ_ne_zero (n : Nat) (h : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  intro heq
  have h2 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at h2
  have hz : ((0 : Word).toNat) = 0 := by decide
  omega

/-- **General s-register-exposed bottom-test countdown-loop lemma** (the
    `do-while` companion to `countdownLoop_spec`).

    ```
      hdr:  <body>                  -- decrements ctr (n+1 → n)
      tst:  bne  ctr, x0, backOff   -- back-edge while ctr ≠ 0
      exit:                         -- tst + 4
    ```

    Given a per-iteration body triple from `hdr` to `tst` taking `ctr` from
    `n + 1` to `n` and the invariant from `inv (n + 1)` to `inv n`, the whole
    loop runs from `hdr` to `tst + 4` with `ctr` draining from `N` to `0`,
    for any `N ≥ 1` (a do-while runs its body at least once). -/
theorem countdownLoopBottom_spec
    (cr : CodeReq) (hdr tst : Word) (ctr : Reg) (backOff : BitVec 13)
    (bodyStep N : Nat) (inv : Nat → Assertion)
    (_hctr_ne : ctr ≠ .x0)
    (hN1 : 1 ≤ N)
    (hNbound : N < 18446744073709551616)
    (hback : tst + signExtend13 backOff = hdr)
    (hpcFree : ∀ n, (inv n).pcFree)
    (hguardMem : ∀ a i,
      CodeReq.singleton tst (.BNE ctr .x0 backOff) a = some i → cr a = some i)
    (hbody : ∀ n, n < N →
      cpsTripleWithin bodyStep hdr tst cr
        ((ctr ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (Reg.x0 ↦ᵣ (0 : Word)) ** inv (n + 1))
        ((ctr ↦ᵣ BitVec.ofNat 64 n) ** (Reg.x0 ↦ᵣ (0 : Word)) ** inv n)) :
    cpsTripleWithin (N * (bodyStep + 1)) hdr (tst + 4) cr
      ((ctr ↦ᵣ BitVec.ofNat 64 N) ** (Reg.x0 ↦ᵣ (0 : Word)) ** inv N)
      ((ctr ↦ᵣ BitVec.ofNat 64 0) ** (Reg.x0 ↦ᵣ (0 : Word)) ** inv 0) := by
  -- Strengthened statement over every `1 ≤ n ≤ N`, by induction on `n`.
  suffices h : ∀ n, 1 ≤ n → n ≤ N →
      cpsTripleWithin (n * (bodyStep + 1)) hdr (tst + 4) cr
        ((ctr ↦ᵣ BitVec.ofNat 64 n) ** (Reg.x0 ↦ᵣ (0 : Word)) ** inv n)
        ((ctr ↦ᵣ BitVec.ofNat 64 0) ** (Reg.x0 ↦ᵣ (0 : Word)) ** inv 0) from
    h N hN1 (Nat.le_refl N)
  intro n
  induction n with
  | zero => intro h1 _; exact absurd h1 (by omega)
  | succ k ih =>
    intro _ hk
    have hkN : k < N := Nat.lt_of_succ_le hk
    -- One body pass: k+1 → k.
    have hbodyk := hbody k hkN
    -- The bottom test with ctr = ofNat k.
    have hbne := bne_spec_gen_within ctr .x0 backOff (BitVec.ofNat 64 k) (0 : Word) tst
    rw [hback] at hbne
    have hbr := cpsBranchWithin_extend_code hguardMem
      (cpsBranchWithin_frameR (inv k) (hpcFree k) hbne)
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- k = 0: the test falls through to the exit.
      subst hk0
      have hexit := cpsBranchWithin_ntakenPath hbr
        (fun hp hQt => by
          obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
          exact ((sepConj_pure_right _).1 h_pure).2 rfl)
      have hstep := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) hbodyk hexit
      rw [show (0 + 1) * (bodyStep + 1) = bodyStep + 1 from by omega]
      -- Strip the not-taken pure `≠` fact and reassociate.
      refine cpsTripleWithin_weaken (fun _ hp => hp)
        (fun h hq => ?_) hstep
      have hq1 := sepConj_mono_left
        (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
      xperm_hyp hq1
    · -- k ≥ 1: the test takes the back edge; recurse.
      have hne : BitVec.ofNat 64 k ≠ (0 : Word) := by
        have : k - 1 + 1 = k := by omega
        rw [← this]
        exact word_ofNat_succ_ne_zero (k - 1) (by omega)
      have htaken := cpsBranchWithin_takenPath hbr
        (fun hp hQf => by
          obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
          exact hne ((sepConj_pure_right _).1 h_pure).2)
      have ihk := ih hkpos (Nat.le_of_lt hkN)
      -- body ; test(back-edge) — plain perm glue.
      have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
        hbodyk htaken
      -- (body ; test) ; tail — strip the taken pure `=` in the glue.
      have s2 := cpsTripleWithin_seq_perm_same_cr
        (fun h hp => by
          have hp2 := sepConj_mono_left
            (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
          xperm_hyp hp2) s1 ihk
      have hstep : (k + 1) * (bodyStep + 1)
          = bodyStep + 1 + k * (bodyStep + 1) := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      rw [hstep]
      exact s2

-- ============================================================================
-- The bottom-test count-up loop (bead evm-asm-ipt7m).
-- ============================================================================

private theorem ofNat_ne_ofNat {a b : Nat} (hne : a ≠ b)
    (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro heq
  have h2 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at h2
  exact hne h2

/-- **General s-register-exposed bottom-test COUNT-UP loop lemma** (bead
    evm-asm-ipt7m): the `for i in 0..N` shape whose body may itself be an
    `abiFrameCall_spec`/`callWithin_spec` composition (a call in the loop):

    ```
      hdr:  <body>                   -- counts ctr up (i → i+1); reloads bnd
      tst:  bne  ctr, bnd, backOff   -- back-edge while ctr ≠ N
      exit:                          -- tst + 4
    ```

    The bound register `bnd` is scratch inside the body (owned on entry) and
    must hold `N` at the test — the emitted pattern reloads it with `li`
    every iteration, so the body postcondition pins it.  Given a
    per-iteration body triple from `hdr` to `tst` taking `ctr` from `i` to
    `i + 1` and the invariant from `inv i` to `inv (i + 1)` — the body being
    an arbitrary `cpsTripleWithin`, e.g. a `callWithin_spec` composition —
    the whole loop runs from `hdr` to `tst + 4` with `ctr` counting `0 → N`,
    for any `N ≥ 1` (a do-while runs its body at least once).  `ctr`, `bnd`,
    and the invariant family are FREE (they may reference `s`-registers). -/
theorem countupLoopBottom_spec
    (cr : CodeReq) (hdr tst : Word) (ctr bnd : Reg) (backOff : BitVec 13)
    (bodyStep N : Nat) (inv : Nat → Assertion)
    (hN1 : 1 ≤ N)
    (hNbound : N < 18446744073709551616)
    (hback : tst + signExtend13 backOff = hdr)
    (hpcFree : ∀ n, (inv n).pcFree)
    (hguardMem : ∀ a i,
      CodeReq.singleton tst (.BNE ctr bnd backOff) a = some i → cr a = some i)
    (hbody : ∀ i, i < N →
      cpsTripleWithin bodyStep hdr tst cr
        ((ctr ↦ᵣ BitVec.ofNat 64 i) ** regOwn bnd ** inv i)
        ((ctr ↦ᵣ BitVec.ofNat 64 (i + 1)) ** (bnd ↦ᵣ BitVec.ofNat 64 N)
          ** inv (i + 1))) :
    cpsTripleWithin (N * (bodyStep + 1)) hdr (tst + 4) cr
      ((ctr ↦ᵣ BitVec.ofNat 64 0) ** regOwn bnd ** inv 0)
      ((ctr ↦ᵣ BitVec.ofNat 64 N) ** (bnd ↦ᵣ BitVec.ofNat 64 N) ** inv N) := by
  -- Strengthened statement over the REMAINING count `k` (`i + k = N`).
  suffices h : ∀ k, 1 ≤ k → ∀ i, i + k = N →
      cpsTripleWithin (k * (bodyStep + 1)) hdr (tst + 4) cr
        ((ctr ↦ᵣ BitVec.ofNat 64 i) ** regOwn bnd ** inv i)
        ((ctr ↦ᵣ BitVec.ofNat 64 N) ** (bnd ↦ᵣ BitVec.ofNat 64 N) ** inv N) from
    h N hN1 0 (by omega)
  intro k
  induction k with
  | zero => intro h1 _ _; exact absurd h1 (by omega)
  | succ m ih =>
    intro _ i hiN
    have hiL : i < N := by omega
    -- One body pass: i → i+1.
    have hbodyi := hbody i hiL
    -- The bottom test with ctr = ofNat (i+1), bnd = ofNat N.
    have hbne := bne_spec_gen_within ctr bnd backOff (BitVec.ofNat 64 (i + 1))
      (BitVec.ofNat 64 N) tst
    rw [hback] at hbne
    have hbr := cpsBranchWithin_extend_code hguardMem
      (cpsBranchWithin_frameR (inv (i + 1)) (hpcFree (i + 1)) hbne)
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · -- m = 0: i + 1 = N, the test falls through to the exit.
      subst hm0
      have hiN' : i + 1 = N := by omega
      have hexit := cpsBranchWithin_ntakenPath hbr
        (fun hp hQt => by
          obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
          exact ((sepConj_pure_right _).1 h_pure).2 (by rw [hiN']))
      have hstep := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) hbodyi hexit
      rw [show (0 + 1) * (bodyStep + 1) = bodyStep + 1 from by omega]
      refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hstep
      have hq1 := sepConj_mono_left
        (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
      rw [hiN'] at hq1
      xperm_hyp hq1
    · -- m ≥ 1: i + 1 < N, the test takes the back edge; recurse.
      have hne : BitVec.ofNat 64 (i + 1) ≠ BitVec.ofNat 64 N :=
        ofNat_ne_ofNat (by omega) (by omega) hNbound
      have htaken := cpsBranchWithin_takenPath hbr
        (fun hp hQf => by
          obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
          exact hne ((sepConj_pure_right _).1 h_pure).2)
      have ihk := ih hmpos (i + 1) (by omega)
      -- body ; test(back-edge) — plain perm glue.
      have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
        hbodyi htaken
      -- (body ; test) ; tail — strip the taken pure `≠`, release `bnd`.
      have s2 := cpsTripleWithin_seq_perm_same_cr
        (fun h hp => by
          have hp2 := sepConj_mono_left
            (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
          have hp3 := sepConj_mono_left (sepConj_mono_right
            (regIs_to_regOwn bnd (BitVec.ofNat 64 N))) h hp2
          xperm_hyp hp3) s1 ihk
      have hstep : (m + 1) * (bodyStep + 1)
          = bodyStep + 1 + m * (bodyStep + 1) := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      rw [hstep]
      exact s2

end SAsm
end EvmAsm.Rv64
