/-
  EvmAsm.Rv64.RLP.RecDecode.Correct

  The final machine↔reference correspondence for the recursive RLP
  decoder.  `rlp_decode_correct` states, as a bounded CPS triple about
  the RISC-V code at `decEntry`, that the routine halts cleanly through
  its `jalr` return with

    x10 = 0  and  ∃ item, Ref.decode (window) = some item ∧ listDepth ≤ d
      — the machine accepts exactly what the pinned reference
        (`ethereum_rlp` 0.1.6) accepts within the nesting budget `d` —
    or
    x10 = 1  and  every reference-accepted item overflows the budget
      (in particular whenever the reference rejects outright).

  The budget `d` is a *parameter* of the program (register `x12`), the
  contracts, and this theorem — never a constant.  Rejection at the cap
  mirrors the reference, whose decoder raises `RecursionError` past
  interpreter recursion depth (measured: accepts nesting ≤ 332, raises
  at 333 under CPython's default limit).

  The termination measure of the reference — never stated in the Python —
  is `3·|window| + phase` (`RefDecode.lean`); the machine induction is on
  the budget `d`, tied to the spec by `decodeD_eq_some_iff`
  (`RefDecodeDepth.lean`).  Under `|input| < 256^8` the reference decoder
  agrees with `decodeFully` outright (`RefDecodeBridge.lean`).

  Anti-vacuity: the premise set is inhabited by the concrete layout below,
  and the same program bytes pass a 749-vector differential run against
  the budgeted spec (`EmuDiff.lean`).
-/

import EvmAsm.Rv64.RLP.RecDecode.Knot
import EvmAsm.EL.RLP.RefDecodeDepth

namespace EvmAsm.Rv64
namespace SAsm
namespace RecDecode

open EvmAsm.EL.RLP (Byte RLPItem)
open EvmAsm.EL.RLP.Ref (decodeD win RLPItem.listDepth decodeD_eq_some_iff)

private theorem idxOf_ofNat' (inBase : Word) (k bnd : Nat)
    (hk : k ≤ bnd) (hb : inBase.toNat + bnd < 2 ^ 64) :
    idxOf inBase (inBase + BitVec.ofNat 64 k) = k := by
  unfold idxOf
  have haddr : (inBase + BitVec.ofNat 64 k).toNat = inBase.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [BitVec.toNat_sub, haddr]
  omega

-- ============================================================================
-- The status word, characterized against the unbudgeted reference
-- ============================================================================

theorem decStatus_eq_zero_iff (bs : List Byte) (off len d : Nat) :
    decStatus bs off len d = 0
      ↔ ∃ item, EvmAsm.EL.RLP.Ref.decode (win bs off len) = some item
          ∧ RLPItem.listDepth item ≤ d := by
  unfold decStatus
  cases hopt : decodeD d (win bs off len) with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, if_neg,
      not_false_eq_true]
    constructor
    · intro h
      exact absurd h (by decide)
    · rintro ⟨item, hdec, hdepth⟩
      have := (decodeD_eq_some_iff d (win bs off len)
        item).mpr ⟨hdec, hdepth⟩
      rw [hopt] at this
      exact absurd this (by simp)
  | some item =>
    simp only [Option.isSome_some, if_pos]
    have h := (decodeD_eq_some_iff d (win bs off len)
      item).mp hopt
    exact ⟨fun _ => ⟨item, h.1, h.2⟩, fun _ => trivial⟩

theorem decStatus_eq_one_iff (bs : List Byte) (off len d : Nat) :
    decStatus bs off len d = 1
      ↔ ∀ item, EvmAsm.EL.RLP.Ref.decode (win bs off len) = some item
          → d < RLPItem.listDepth item := by
  constructor
  · intro h item hdec
    by_contra hle
    have h0 := (decStatus_eq_zero_iff bs off len d).mpr
      ⟨item, hdec, by omega⟩
    rw [h] at h0
    exact absurd h0 (by decide)
  · intro h
    unfold decStatus
    cases hopt : decodeD d (win bs off len) with
    | none => simp
    | some item =>
      have hd := (decodeD_eq_some_iff d (win bs off len)
        item).mp hopt
      exact absurd (h item hd.1) (by omega)

/-- The status is always binary. -/
theorem decStatus_cases (bs : List Byte) (off len d : Nat) :
    decStatus bs off len d = 0 ∨ decStatus bs off len d = 1 := by
  unfold decStatus
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

-- ============================================================================
-- The correspondence theorem
-- ============================================================================

/-- **Machine↔reference correspondence.**  Entering the decoder at
    `decEntry` with a window `(off, len)` of the input region in
    `x10`/`x11`, the nesting budget in `x12`, and a frame pointer in
    `x13`, the machine reaches the return address within
    `decSteps |bs| d` steps with the frame pointer restored, the ambient
    assertion untouched, and `x10` reporting exactly whether the pinned
    reference decodes the window to an item within the budget. -/
theorem rlp_decode_correct
    (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (off len : Nat)
    (L : RdLayout inBase bs fp (40 * d + 8))
    (hoff : off + len ≤ bs.length)
    (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion)
    (hlen : ws₀.length = 40 * d + 8) (hpc : A₀.pcFree)
    (hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off)
    (hx11 : rf₀.get .x11 = BitVec.ofNat 64 len)
    (hx12 : rf₀.get .x12 = BitVec.ofNat 64 d)
    (hx13 : rf₀.get .x13 = fp)
    (ret : Word) (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (decSteps bs.length d) decEntry ret decCr
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM ⟨inBase, bs⟩ (decRw d fp) (Reach.exact rf₀ ws₀ A₀))
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM ⟨inBase, bs⟩ (decRw d fp)
            (fun rf _ A =>
              ((rf.get .x10 = 0
                  ∧ ∃ item, EvmAsm.EL.RLP.Ref.decode (win bs off len)
                      = some item ∧ RLPItem.listDepth item ≤ d)
                ∨ (rf.get .x10 = 1
                  ∧ ∀ item, EvmAsm.EL.RLP.Ref.decode (win bs off len)
                      = some item → d < RLPItem.listDepth item))
              ∧ rf.get .x13 = fp ∧ A = A₀)) := by
  have hb : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
  have hfpb : fp.toNat + (40 * d + 8) < 2 ^ 64 := L.rwWf.2.1
  have ho : offOf inBase rf₀ = off := by
    unfold offOf
    rw [hx10]
    exact idxOf_ofNat' inBase off bs.length (by omega) hb
  have hl : lenOf rf₀ = len := by
    unfold lenOf
    rw [hx11, BitVec.toNat_ofNat]
    omega
  have h := decSound_all bs inBase d fp L rf₀ ws₀ A₀ hlen hpc
    ⟨off, len, hx10, hx11, hx12, hx13, hoff⟩ ret halign
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h
  intro hp hh
  refine sepConj_mono_right (asrtM_mono ?_) hp hh
  rintro rf ws A ⟨h10, h13, hA⟩
  rw [ho, hl] at h10
  refine ⟨?_, h13, hA⟩
  rcases decStatus_cases bs off len d with hz | hone
  · exact Or.inl ⟨by rw [h10, hz],
      (decStatus_eq_zero_iff bs off len d).mp hz⟩
  · exact Or.inr ⟨by rw [h10, hone],
      (decStatus_eq_one_iff bs off len d).mp hone⟩

-- ============================================================================
-- Anti-vacuity: the premise set is inhabited
-- ============================================================================

/-- A concrete input region and frame layout: `[0xC2, 0xC1, 0x80]`
    (a list containing a list containing the empty byte string —
    nesting depth 2) at `0x8000`, frame arena at `0x10000`, budget 2. -/
theorem exLayout : RdLayout 0x8000 [0xC2, 0xC1, 0x80] 0x10000
    (40 * 2 + 8) :=
  ⟨by decide, by decide, by decide⟩

/-- A concrete entry register file for the example. -/
def exRf : RegFile := fun r =>
  if r = .x10 then 0x8000 else
  if r = .x11 then 3 else
  if r = .x12 then 2 else
  if r = .x13 then 0x10000 else 0

/-- The correspondence theorem instantiated at the concrete layout: its
    premise set is inhabited (nothing is vacuously true). -/
example : cpsTripleWithin (decSteps 3 2) decEntry 0x2000 decCr
    (((.x1 : Reg) ↦ᵣ (0x2000 : Word))
      ** asrtM ⟨0x8000, [0xC2, 0xC1, 0x80]⟩ (decRw 2 0x10000)
          (Reach.exact exRf (List.replicate 88 0) (bytesRegion 0 [])))
    (((.x1 : Reg) ↦ᵣ (0x2000 : Word))
      ** asrtM ⟨0x8000, [0xC2, 0xC1, 0x80]⟩ (decRw 2 0x10000)
          (fun rf _ A =>
            ((rf.get .x10 = 0
                ∧ ∃ item, EvmAsm.EL.RLP.Ref.decode
                    (win [0xC2, 0xC1, 0x80] 0 3)
                    = some item ∧ RLPItem.listDepth item ≤ 2)
              ∨ (rf.get .x10 = 1
                ∧ ∀ item, EvmAsm.EL.RLP.Ref.decode
                    (win [0xC2, 0xC1, 0x80] 0 3)
                    = some item → 2 < RLPItem.listDepth item))
            ∧ rf.get .x13 = 0x10000 ∧ A = bytesRegion 0 [])) :=
  rlp_decode_correct [0xC2, 0xC1, 0x80] 0x8000 2 0x10000 0 3 exLayout
    (by decide) exRf (List.replicate 88 0) (bytesRegion 0 [])
    (by decide) (bytesRegion_pcFree _ _)
    (by decide) (by decide) (by decide) (by decide)
    0x2000 (by decide)

-- The budget is live: the depth-2 vector is accepted at budget 2 and
-- rejected at budget 1 — the cap parameter genuinely gates recursion.
#guard decStatus [0xC2, 0xC1, 0x80] 0 3 2 = 0
#guard decStatus [0xC2, 0xC1, 0x80] 0 3 1 = 1
-- A reference-rejected input is rejected at every budget.
#guard decStatus [0xC2, 0xC1] 0 2 2 = 1

end RecDecode
end SAsm
end EvmAsm.Rv64
