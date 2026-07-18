/-
  EvmAsm.Rv64.SAsm.AbiFrameLoop

  An s-register-exposed loop-composition bridge at the `cpsTripleWithin` level
  (bead evm-asm-4ch8f.76, loop-leaf follow-up).

  `AbiFrame.lean` gives `abiFrame_spec`: it lifts an *arbitrary single-exit
  body* (supplied as a `cpsTripleWithin` hypothesis over the body region) into
  a whole prologue·body·epilogue·ret routine that restores `sp`/`ra`/every
  saved `s`-register.  The body may contain an internal loop that falls through
  to the epilogue — the loop is entirely internal to the body region, so the
  routine is still single-exit at the frame boundary.

  The missing piece for such a body is a way to discharge the internal loop's
  `cpsTripleWithin` with a real loop invariant.  The structured-layer loop
  combinators (`doWhileBreak`/`whileHeader`/…) only expose *caller* registers
  (`Reg.isExposed` excludes the `s`-registers), so they cannot be used for a
  body whose accumulators live in callee-saved registers.

  This file supplies a **general, register-agnostic countdown-loop lemma**
  (`countdownLoop_spec`) living entirely at the `cpsTripleWithin` level.  It is
  the direct analogue of the hand-proven RLP accumulation loops
  (`cu64_loop_spec_within` &c.), but parameterized over:

  * an arbitrary counter register `ctr` (may be an `s`-register — nothing in
    the proof looks at `Reg.isExposed`; a register is just a `↦ᵣ` atom);
  * an arbitrary loop-invariant assertion family `inv : Nat → Assertion` (may
    freely mention `s`-register atoms, memory, caller regions, …);
  * a per-iteration body triple `hbody` running from the fall-through address
    back to the loop header.

  The shape it recognizes is the standard bottom-decrement countdown emitted by
  the guest:

  ```
    hdr:  beq  ctr, x0, exitOff     -- exit when the counter hits 0
          <body>                    -- runs with inv exposed; decrements ctr
          jal  x0, hdr              -- back-edge to the header
    exit:                           -- falls through here
  ```

  Preservation of the frame slots is *not* this file's concern — that is the
  `abiFrame_spec` frame rule.  Here the frame slots are simply not mentioned in
  the loop's footprint, so they are framed (untouched) for free.  This file is
  strictly additive: it does not touch `Ast.lean`/`Vc.lean`/`StmtSound*.lean`/
  `blockOk`, only `cpsTripleWithin`.
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64
namespace SAsm

open EvmAsm.Rv64.Tactics

/-- `BitVec.ofNat 64 (n+1)` is never the zero word when `n+1 < 2^64`. -/
private theorem word_ofNat_succ_ne_zero (n : Nat) (h : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  intro heq
  have h2 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at h2
  have hz : ((0 : Word).toNat) = 0 := by decide
  omega

/-- **General s-register-exposed countdown-loop lemma.**

    Recognizes the standard guest bottom-decrement loop

    ```
      hdr:  beq  ctr, x0, exitOff      -- header guard at `hdr`
            <body>                     -- fall-through at `hdr + 4`
            jal  x0, hdr               -- back-edge (part of `<body>`)
      exit:                            -- `hdr + signExtend13 exitOff`
    ```

    Given a per-iteration body triple `hbody` that, for every remaining count
    `n < N`, runs from the fall-through address `hdr + 4` back to the header
    `hdr` taking `ctr` from `n+1` to `n` and stepping the invariant from
    `inv (n+1)` to `inv n`, the whole loop runs from the header `hdr` to `exit`
    with the counter draining from `N` to `0`.

    `ctr` and every atom in `inv` are ordinary `↦ᵣ`/memory atoms, so `ctr` and
    the invariant may reference callee-saved `s`-registers freely — this is the
    capability the structured-layer combinators lack. -/
theorem countdownLoop_spec
    (cr : CodeReq) (hdr exitAddr : Word) (ctr : Reg) (exitOff : BitVec 13)
    (bodyStep N : Nat) (inv : Nat → Assertion)
    (_hctr_ne : ctr ≠ .x0)
    (hNbound : N < 18446744073709551616)
    (hexit : hdr + signExtend13 exitOff = exitAddr)
    (hpcFree : ∀ n, (inv n).pcFree)
    (hguardMem : ∀ a i,
      CodeReq.singleton hdr (.BEQ ctr .x0 exitOff) a = some i → cr a = some i)
    (hbody : ∀ n, n < N →
      cpsTripleWithin bodyStep (hdr + 4) hdr cr
        ((ctr ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (Reg.x0 ↦ᵣ (0 : Word)) ** inv (n + 1))
        ((ctr ↦ᵣ BitVec.ofNat 64 n) ** (Reg.x0 ↦ᵣ (0 : Word)) ** inv n)) :
    cpsTripleWithin (N * (bodyStep + 1) + 1) hdr exitAddr cr
      ((ctr ↦ᵣ BitVec.ofNat 64 N) ** (Reg.x0 ↦ᵣ (0 : Word)) ** inv N)
      ((ctr ↦ᵣ BitVec.ofNat 64 0) ** (Reg.x0 ↦ᵣ (0 : Word)) ** inv 0) := by
  -- Prove the stronger `∀ n ≤ N` statement, by induction on the remaining
  -- count `n`, then specialize at `n = N`.
  suffices h : ∀ n, n ≤ N →
      cpsTripleWithin (n * (bodyStep + 1) + 1) hdr exitAddr cr
        ((ctr ↦ᵣ BitVec.ofNat 64 n) ** (Reg.x0 ↦ᵣ (0 : Word)) ** inv n)
        ((ctr ↦ᵣ BitVec.ofNat 64 0) ** (Reg.x0 ↦ᵣ (0 : Word)) ** inv 0) from
    h N (Nat.le_refl N)
  intro n
  induction n with
  | zero =>
    intro _
    -- ctr = ofNat 0 = 0, x0 = 0 : the guard is taken and jumps to `exit`.
    have hbeq := beq_spec_gen_within ctr .x0 exitOff (BitVec.ofNat 64 0) (0 : Word) hdr
    rw [hexit] at hbeq
    have hbr := cpsBranchWithin_extend_code hguardMem
      (cpsBranchWithin_frameR (inv 0) (hpcFree 0) hbeq)
    have htaken := cpsBranchWithin_takenPath hbr
      (fun hp hQf => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
        exact ((sepConj_pure_right _).1 h_pure).2 (by decide))
    -- Reconcile the step count and pre/post shapes.
    simp only [Nat.zero_mul, Nat.zero_add]
    exact cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by
        -- Strip the taken pure `0#64 = 0` and reassociate.
        have hq1 := sepConj_mono_left
          (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
        xperm_hyp hq1) htaken
  | succ k ih =>
    intro hk
    have hkN : k < N := Nat.lt_of_succ_le hk
    -- Header guard: ctr = ofNat (k+1) ≠ 0, so the branch is NOT taken.
    have hbeq := beq_spec_gen_within ctr .x0 exitOff (BitVec.ofNat 64 (k + 1)) (0 : Word) hdr
    rw [hexit] at hbeq
    have hbr := cpsBranchWithin_extend_code hguardMem
      (cpsBranchWithin_frameR (inv (k + 1)) (hpcFree (k + 1)) hbeq)
    have hne : BitVec.ofNat 64 (k + 1) ≠ (0 : Word) :=
      word_ofNat_succ_ne_zero k (by omega)
    have hguard := cpsBranchWithin_ntakenPath hbr
      (fun hp hQt => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
        exact hne ((sepConj_pure_right _).1 h_pure).2)
    -- `hguard : cpsTripleWithin 1 hdr (hdr+4) cr P Qguard` with the `⌜≠⌝` pure.
    -- Body (fall-through → header), and inductive tail (header → exit).
    have hbodyk := hbody k hkN
    have ihk := ih (Nat.le_of_lt hkN)
    -- guard ; body
    have s1 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp2 := sepConj_mono_left
          (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
        xperm_hyp hp2) hguard hbodyk
    -- (guard ; body) ; tail
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 ihk
    -- Step count: 1 + bodyStep + (k*(bodyStep+1)+1) = (k+1)*(bodyStep+1)+1.
    have hstep : (k + 1) * (bodyStep + 1) + 1
        = 1 + bodyStep + (k * (bodyStep + 1) + 1) := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    rw [hstep]
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) s2

end SAsm
end EvmAsm.Rv64
