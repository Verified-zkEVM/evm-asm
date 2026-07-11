/-
  EvmAsm.Rv64.SAsm.UpLoop

  **General s-register-exposed up-counting loop lemma** (bead
  evm-asm-4ch8f.16.3.1, sibling of `countdownLoop_spec` in
  `AbiFrameLoop.lean`).

  `countdownLoop_spec` recognizes the bottom-decrement countdown
  (`beq ctr, x0, exit` header).  Several emitted guest loops instead count a
  cursor UP against a limit register with an unsigned-compare top guard — the
  `hp_decode_nibbles` nibble loop is the canonical instance:

  ```
    hdr:  bgeu idx, lim, exitOff     -- exit when idx ≥ lim (unsigned)
          <body>                     -- runs with inv exposed; increments idx
          jal  x0, hdr               -- back-edge (part of `<body>`)
    exit:                            -- `hdr + signExtend13 exitOff`
  ```

  `upLoop_spec` is the direct analogue: parameterized over an arbitrary index
  register `idx`, limit register `lim` (both may be callee-saved
  `s`-registers — a register is just a `↦ᵣ` atom at this level), and an
  invariant family `inv : Nat → Assertion`.  Given a per-iteration body triple
  from the fall-through address back to the header taking `idx` from `i` to
  `i+1` (`start ≤ i < len`), the whole loop runs from the header to the exit
  with the index climbing from `start` to `len`.

  Strictly additive: `cpsTripleWithin` level only — no `Ast`/`Vc`/
  `StmtSound*`/`blockOk` changes.
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64
namespace SAsm

open EvmAsm.Rv64.Tactics

/-- Unsigned word comparison of in-range `ofNat`s is the `Nat` comparison. -/
private theorem word_ofNat_ult_iff {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 i) (BitVec.ofNat 64 j) ↔ i < j := by
  simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]

/-- **General s-register-exposed up-counting loop lemma** — the
    `bgeu idx, lim, exit` top-guard analogue of `countdownLoop_spec`.

    Given a per-iteration body triple `hbody` that, for every index
    `i` with `start ≤ i < len`, runs from the fall-through address `hdr + 4`
    back to the header `hdr` taking `idx` from `i` to `i+1` and stepping the
    invariant from `inv i` to `inv (i+1)`, the whole loop runs from the header
    `hdr` to `exit` with the index climbing from `start` to `len`. -/
theorem upLoop_spec
    (cr : CodeReq) (hdr exitAddr : Word) (idx lim : Reg) (exitOff : BitVec 13)
    (bodyStep len : Nat) (inv : Nat → Assertion)
    (hlen : len < 2 ^ 64)
    (hexit : hdr + signExtend13 exitOff = exitAddr)
    (hpcFree : ∀ n, (inv n).pcFree)
    (hguardMem : ∀ a i,
      CodeReq.singleton hdr (.BGEU idx lim exitOff) a = some i → cr a = some i)
    (start : Nat) (hstart : start ≤ len)
    (hbody : ∀ i, start ≤ i → i < len →
      cpsTripleWithin bodyStep (hdr + 4) hdr cr
        ((idx ↦ᵣ BitVec.ofNat 64 i) ** (lim ↦ᵣ BitVec.ofNat 64 len) ** inv i)
        ((idx ↦ᵣ BitVec.ofNat 64 (i + 1)) ** (lim ↦ᵣ BitVec.ofNat 64 len)
          ** inv (i + 1))) :
    cpsTripleWithin ((len - start) * (bodyStep + 1) + 1) hdr exitAddr cr
      ((idx ↦ᵣ BitVec.ofNat 64 start) ** (lim ↦ᵣ BitVec.ofNat 64 len) ** inv start)
      ((idx ↦ᵣ BitVec.ofNat 64 len) ** (lim ↦ᵣ BitVec.ofNat 64 len) ** inv len) := by
  -- Induction on the remaining distance `len - s` for cursors `s ≥ start`.
  suffices h : ∀ d s, start ≤ s → s ≤ len → len - s = d →
      cpsTripleWithin (d * (bodyStep + 1) + 1) hdr exitAddr cr
        ((idx ↦ᵣ BitVec.ofNat 64 s) ** (lim ↦ᵣ BitVec.ofNat 64 len) ** inv s)
        ((idx ↦ᵣ BitVec.ofNat 64 len) ** (lim ↦ᵣ BitVec.ofNat 64 len) ** inv len) by
    exact h (len - start) start (Nat.le_refl start) hstart rfl
  intro d
  induction d with
  | zero =>
    intro start' hge hle hd
    have hsl : start' = len := by omega
    subst hsl
    -- idx = lim: the guard is taken (¬ ult) and jumps to `exit`.
    have hbgeu := bgeu_spec_gen_within idx lim exitOff (BitVec.ofNat 64 start')
      (BitVec.ofNat 64 start') hdr
    rw [hexit] at hbgeu
    have hbr := cpsBranchWithin_extend_code hguardMem
      (cpsBranchWithin_frameR (inv start') (hpcFree start') hbgeu)
    have htaken := cpsBranchWithin_takenPath hbr
      (fun hp hQf => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
        have hult := ((sepConj_pure_right _).1 h_pure).2
        exact absurd ((word_ofNat_ult_iff (by omega) (by omega)).1 hult)
          (Nat.lt_irrefl start'))
    simp only [Nat.zero_mul, Nat.zero_add]
    exact cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by
        have hq1 := sepConj_mono_left
          (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
        xperm_hyp hq1) htaken
  | succ k ih =>
    intro start' hge hle hd
    have hsl : start' < len := by omega
    -- Header guard: start' < len so `ult` holds and the branch is NOT taken.
    have hbgeu := bgeu_spec_gen_within idx lim exitOff (BitVec.ofNat 64 start')
      (BitVec.ofNat 64 len) hdr
    rw [hexit] at hbgeu
    have hbr := cpsBranchWithin_extend_code hguardMem
      (cpsBranchWithin_frameR (inv start') (hpcFree start') hbgeu)
    have hguard := cpsBranchWithin_ntakenPath hbr
      (fun hp hQt => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
        have hnult := ((sepConj_pure_right _).1 h_pure).2
        exact hnult ((word_ofNat_ult_iff (by omega) hlen).2 hsl))
    -- Body (fall-through → header), and inductive tail (header → exit).
    have hbodyk := hbody start' hge hsl
    have ihk := ih (start' + 1) (by omega) (by omega) (by omega)
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
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp) s2

end SAsm
end EvmAsm.Rv64
