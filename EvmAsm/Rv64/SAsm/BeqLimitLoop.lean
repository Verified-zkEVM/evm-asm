/-
  EvmAsm.Rv64.SAsm.BeqLimitLoop

  **General s-register-exposed up-counting loop lemma with an EQUALITY top
  guard against a LIMIT REGISTER** — the third sibling of
  `countdownLoop_spec` (`AbiFrameLoop.lean`) and `upLoop_spec`
  (`UpLoop.lean`).

  The two existing combinators recognize:

  * `countdownLoop_spec` — `beq ctr, x0, exit`: a counter draining to zero,
    compared against the ZERO register;
  * `upLoop_spec` — `bgeu idx, lim, exit`: a cursor climbing against a limit
    register, with an UNSIGNED-COMPARE guard.

  Neither matches the (also common) emitted shape where the cursor climbs and
  the guard is an *equality* test against a limit register — the compiler
  knows the cursor hits the limit exactly, so it emits the cheaper `beq`.
  `address_from_pubkey`'s 20-byte digest→output copy loop (GH #12224) is the
  canonical instance:

  ```
    hdr:  beq  idx, lim, exitOff     -- exit when idx = lim
          <body>                     -- runs with inv exposed; idx += stride
          jal  x0, hdr               -- back-edge (part of `<body>`)
    exit:                            -- `hdr + signExtend13 exitOff`
  ```

  `beqLimitLoop_spec` is parameterized over an arbitrary cursor register
  `idx`, limit register `lim` (either may be callee-saved — a register is
  just a `↦ᵣ` atom at this level), a start value, a positive `stride`, an
  iteration count, and an invariant family `inv : Nat → Assertion` indexed
  by the ITERATION NUMBER (not by the cursor value, so a non-unit stride
  needs no arithmetic inside the invariant's index).

  Two shape notes that matter when applying it:

  * The per-iteration hypothesis is a triple from the fall-through address
    `hdr + 4` back to the header `hdr`; it is an arbitrary
    `cpsTripleWithin`, so a back-edge that lands *before* the header (a
    `jal` to `hdr - 4` followed by a limit reload, which is exactly what
    `address_from_pubkey` emits) is simply absorbed into the body triple —
    no extra combinator parameter is needed, only a larger `bodyStep`.
  * Because the guard is an equality test, termination hinges on the cursor
    hitting the limit EXACTLY.  That is what `0 < stride` plus the no-wrap
    side condition `start + count * stride < 2 ^ 64` buy: the cursor takes
    the values `start + i * stride` for `i ≤ count`, pairwise distinct as
    machine words, and only the last equals the limit.
  * The guard's operand order is fixed as emitted (`beq idx, lim`), matching
    how `countdownLoop_spec`/`upLoop_spec` fix theirs.  A routine that emits
    `beq lim, idx` instead needs a sibling with the swapped `hguardMem`.

  Strictly additive: `cpsTripleWithin` level only — no `Ast`/`Vc`/
  `StmtSound*`/`blockOk` changes, and no change to the statement of
  `countdownLoop_spec`/`upLoop_spec`.
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64
namespace SAsm

open EvmAsm.Rv64.Tactics

/-- In-range `ofNat`s that differ as naturals differ as words. -/
private theorem word_ofNat_ne_of_lt {a b : Nat} (hab : a < b) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro heq
  have h := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt hb] at h
  omega

/-- **General up-counting loop lemma with a `beq idx, lim` top guard.**

    Given a per-iteration body triple `hbody` that, for every iteration
    index `i < count`, runs from the fall-through address `hdr + 4` back to
    the header `hdr` taking `idx` from `start + i * stride` to
    `start + (i + 1) * stride` and stepping the invariant from `inv i` to
    `inv (i + 1)`, the whole loop runs from the header `hdr` to `exit` with
    the cursor climbing from `start` to the limit `start + count * stride`
    and the invariant advancing from `inv 0` to `inv count`.

    `idx`, `lim` and every atom in `inv` are ordinary `↦ᵣ`/memory atoms, so
    they may reference callee-saved `s`-registers freely — the capability
    the structured-layer combinators lack. -/
theorem beqLimitLoop_spec
    (cr : CodeReq) (hdr exitAddr : Word) (idx lim : Reg) (exitOff : BitVec 13)
    (bodyStep start stride count : Nat) (inv : Nat → Assertion)
    (hstride : 0 < stride)
    (hbound : start + count * stride < 2 ^ 64)
    (hexit : hdr + signExtend13 exitOff = exitAddr)
    (hpcFree : ∀ n, (inv n).pcFree)
    (hguardMem : ∀ a i,
      CodeReq.singleton hdr (.BEQ idx lim exitOff) a = some i → cr a = some i)
    (hbody : ∀ i, i < count →
      cpsTripleWithin bodyStep (hdr + 4) hdr cr
        ((idx ↦ᵣ BitVec.ofNat 64 (start + i * stride))
          ** (lim ↦ᵣ BitVec.ofNat 64 (start + count * stride)) ** inv i)
        ((idx ↦ᵣ BitVec.ofNat 64 (start + (i + 1) * stride))
          ** (lim ↦ᵣ BitVec.ofNat 64 (start + count * stride)) ** inv (i + 1))) :
    cpsTripleWithin (count * (bodyStep + 1) + 1) hdr exitAddr cr
      ((idx ↦ᵣ BitVec.ofNat 64 start)
        ** (lim ↦ᵣ BitVec.ofNat 64 (start + count * stride)) ** inv 0)
      ((idx ↦ᵣ BitVec.ofNat 64 (start + count * stride))
        ** (lim ↦ᵣ BitVec.ofNat 64 (start + count * stride)) ** inv count) := by
  -- Induction on the remaining iteration budget `d = count - i`.
  suffices h : ∀ d i, i ≤ count → count - i = d →
      cpsTripleWithin (d * (bodyStep + 1) + 1) hdr exitAddr cr
        ((idx ↦ᵣ BitVec.ofNat 64 (start + i * stride))
          ** (lim ↦ᵣ BitVec.ofNat 64 (start + count * stride)) ** inv i)
        ((idx ↦ᵣ BitVec.ofNat 64 (start + count * stride))
          ** (lim ↦ᵣ BitVec.ofNat 64 (start + count * stride)) ** inv count) by
    have h0 := h count 0 (Nat.zero_le count) (by omega)
    simpa using h0
  intro d
  induction d with
  | zero =>
    intro i hle hd
    have hic : i = count := by omega
    subst hic
    -- idx = lim: the guard is taken and jumps to `exit`.
    have hbeq := beq_spec_gen_within idx lim exitOff
      (BitVec.ofNat 64 (start + i * stride)) (BitVec.ofNat 64 (start + i * stride)) hdr
    rw [hexit] at hbeq
    have hbr := cpsBranchWithin_extend_code hguardMem
      (cpsBranchWithin_frameR (inv i) (hpcFree i) hbeq)
    have htaken := cpsBranchWithin_takenPath hbr
      (fun _hp h_not_taken_post => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := h_not_taken_post
        exact ((sepConj_pure_right _).1 h_pure).2 rfl)
    simp only [Nat.zero_mul, Nat.zero_add]
    exact cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by
        have hq1 := sepConj_mono_left
          (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
        xperm_hyp hq1) htaken
  | succ k ih =>
    intro i hle hd
    have hic : i < count := by omega
    -- Header guard: `start + i * stride < start + count * stride`, so the
    -- cursor and the limit differ as words and the branch is NOT taken.
    have hlt : start + i * stride < start + count * stride := by
      have : i * stride < count * stride := Nat.mul_lt_mul_of_lt_of_le' hic (Nat.le_refl stride)
        hstride
      omega
    have hne : BitVec.ofNat 64 (start + i * stride)
        ≠ BitVec.ofNat 64 (start + count * stride) :=
      word_ofNat_ne_of_lt hlt hbound
    have hbeq := beq_spec_gen_within idx lim exitOff
      (BitVec.ofNat 64 (start + i * stride)) (BitVec.ofNat 64 (start + count * stride)) hdr
    rw [hexit] at hbeq
    have hbr := cpsBranchWithin_extend_code hguardMem
      (cpsBranchWithin_frameR (inv i) (hpcFree i) hbeq)
    have hguard := cpsBranchWithin_ntakenPath hbr
      (fun _hp h_taken_post => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := h_taken_post
        exact hne ((sepConj_pure_right _).1 h_pure).2)
    -- Body (fall-through → header), and inductive tail (header → exit).
    have hbodyk := hbody i hic
    have ihk := ih (i + 1) (by omega) (by omega)
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

/-- The unit-stride, zero-start specialization of `beqLimitLoop_spec` — the
    shape emitted for a plain `for (i = 0; i != n; ++i)` byte loop, and the
    one `address_from_pubkey` uses.  The cursor register simply holds the
    iteration index and the limit register holds `count`. -/
theorem beqCountLoop_spec
    (cr : CodeReq) (hdr exitAddr : Word) (idx lim : Reg) (exitOff : BitVec 13)
    (bodyStep count : Nat) (inv : Nat → Assertion)
    (hbound : count < 2 ^ 64)
    (hexit : hdr + signExtend13 exitOff = exitAddr)
    (hpcFree : ∀ n, (inv n).pcFree)
    (hguardMem : ∀ a i,
      CodeReq.singleton hdr (.BEQ idx lim exitOff) a = some i → cr a = some i)
    (hbody : ∀ i, i < count →
      cpsTripleWithin bodyStep (hdr + 4) hdr cr
        ((idx ↦ᵣ BitVec.ofNat 64 i) ** (lim ↦ᵣ BitVec.ofNat 64 count) ** inv i)
        ((idx ↦ᵣ BitVec.ofNat 64 (i + 1)) ** (lim ↦ᵣ BitVec.ofNat 64 count)
          ** inv (i + 1))) :
    cpsTripleWithin (count * (bodyStep + 1) + 1) hdr exitAddr cr
      ((idx ↦ᵣ BitVec.ofNat 64 0) ** (lim ↦ᵣ BitVec.ofNat 64 count) ** inv 0)
      ((idx ↦ᵣ BitVec.ofNat 64 count) ** (lim ↦ᵣ BitVec.ofNat 64 count)
        ** inv count) := by
  have h := beqLimitLoop_spec cr hdr exitAddr idx lim exitOff bodyStep 0 1 count inv
    Nat.zero_lt_one (by simpa using hbound) hexit hpcFree hguardMem
    (by simpa using hbody)
  simpa using h

end SAsm
end EvmAsm.Rv64
