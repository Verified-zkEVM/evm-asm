/-
  EvmAsm.Codegen.Programs.BgvU32leSpec

  GH #11352 — the whole-routine triple for `bgv_u32le`, row 10 of
  `docs/leaf-routine-targets.md`, plus its tie to the reference.

  WHAT WAS ALREADY THERE, AND WHAT WAS NOT. `bgvU32leFn_spec`
  (`BalGasValidSAsm.lean:66`) already proves the structured SAsm contract
  `a0 = leU32 bs 0`, `#guard`-tied to the emitted `bgvU32le_prog`. Two things were
  missing:

  1. **A flat `cpsTripleWithin` at the linked guest address.** An SAsm `Fn.Spec` is the
     bounded CPS triple of the *flattened body*; callers compose against
     `cpsTripleWithin … (GuestAddrs.bgv_u32le) …`. `bgvU32leFlat_spec` is that shape,
     DERIVED from the structured spec by the `Fn.retSpecFlat` adapter
     (`Rv64/SAsm/FnFlat.lean:290`) — no hand-written re-proof. Same pattern as
     `Bn254Fq12SetOneSAsm.bnqZeroFlat_spec:133`, and simpler here because the routine
     has no writable region.
  2. **A tie to the reference.** `leU32` is a local `BitVec` accessor
     (`SgLoadU32leSAsm.lean:41`); the reference is the fixed-width little-endian read
     inside `deserialize_stateless_input` (`SpecRef/Guest.lean:29`), which bottoms out
     in `bytesLEtoNat` (`SpecRef/Crypto.lean:38`). Landing the triple *without* this
     would enter the registry as `.machineOnly` — the exact grade #11341 is retiring —
     so the bridge is paid up front rather than filed as a follow-up.

  ⭐ THE LOAD-BEARING LEMMA is `toNat_or_shift`: OR-ing a byte shifted past the already
  accumulated width is *addition*. `leU32` assembles four bytes with `|||`, the
  reference accumulates with `+`, and nothing in the tree related the two. The proof
  goes through `BitVec.add_eq_or_of_and_eq_zero` / `BitVec.toNat_add_of_and_eq_zero`
  (Lean **core**, `Init/Data/BitVec/Bitblast.lean` — not Mathlib), with disjointness by
  per-bit `getElem` reasoning. No `bv_decide`.

  ⚠️ SCOPE. This is the u32 accessor those reads reduce to — not
  `deserialize_stateless_input` as a whole, which additionally does the schema-id check
  and SSZ container decoding. #11352 scopes it that way deliberately. Row 10 was chosen
  in #11312 partly because it has **8 fixture in-edges**, so every caller that reads a
  witness-section offset takes a step from this one theorem.
-/

import EvmAsm.Codegen.Programs.BalGasValidSAsm
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Stateless.SpecRef.Crypto

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace BgvU32leSpec

open BalGasValidSAsm (bgvU32leFn bgvU32leFn_spec)
open SgLoadU32leSAsm (leByte leU32)

/-! ## The accessor bridge

    `leU32` ORs four shifted bytes; `bytesLEtoNat` adds them with weights. The two are
    the same function, but only because the operands are bitwise disjoint. -/

/-- ⭐ **OR past the accumulated width is addition.** If `x` already fits in `m` bits,
    OR-ing in a byte shifted left by `m` adds `z * 2 ^ m`.

    Both halves come from Lean core's bitblasting support: `add_eq_or_of_and_eq_zero`
    turns the `|||` into `+` under disjointness, and `toNat_add_of_and_eq_zero` gives
    the sum without a wrapping `%`. Disjointness is per-bit — below `m` the shifted
    operand is zero, at or above `m` the accumulator is. -/
theorem toNat_or_shift (x : Word) (z : BitVec 8) (m : Nat)
    (hx : x.toNat < 2 ^ m) (hm : m + 8 ≤ 64) :
    (x ||| (z.zeroExtend 64 <<< m)).toNat = x.toNat + z.toNat * 2 ^ m := by
  have hdisj : x &&& (z.zeroExtend 64 <<< m) = 0#64 := by
    ext i
    have hi : i < 64 := by assumption
    simp only [BitVec.getElem_and, BitVec.getElem_zero, Bool.and_eq_false_iff]
    by_cases hlt : i < m
    · right
      simp [BitVec.getElem_shiftLeft, hlt]
    · left
      rw [BitVec.getElem_eq_testBit_toNat]
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hdisj, BitVec.toNat_add_of_and_eq_zero hdisj]
  congr 1
  have hz := z.isLt
  have hlt64 : z.toNat * 2 ^ m < 2 ^ 64 := by
    calc z.toNat * 2 ^ m < 2 ^ 8 * 2 ^ m :=
          Nat.mul_lt_mul_of_lt_of_le hz (Nat.le_refl _) (Nat.two_pow_pos m)
      _ ≤ 2 ^ 64 := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : z.toNat < 2 ^ 64), Nat.mod_eq_of_lt hlt64]

/-- A single `leByte` is just the byte, widened. -/
private theorem toNat_leByte (bs : List (BitVec 8)) (i : Nat) :
    (leByte bs i).toNat = (bs.getD i 0).toNat := by
  rw [leByte, show BitVec.zeroExtend 64 (bs.getD i 0)
      = BitVec.setWidth 64 (bs.getD i 0) from rfl, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (bs.getD i 0).isLt (by norm_num))

set_option maxRecDepth 8000 in
/-- ⭐ **The accessor bridge.** The routine's little-endian u32 is exactly the
    reference's little-endian read of the first four bytes. -/
theorem leU32_eq_bytesLEtoNat (bs : List (BitVec 8)) (hlen : 4 ≤ bs.length) :
    (leU32 bs 0).toNat = EvmAsm.Stateless.SpecRef.bytesLEtoNat (bs.take 4) := by
  have b0 := (bs.getD 0 0).isLt
  have b1 := (bs.getD 1 0).isLt
  have b2 := (bs.getD 2 0).isLt
  have b3 := (bs.getD 3 0).isLt
  -- accumulate left to right, carrying the running width bound
  have h1 : (leByte bs 0 ||| leByte bs 1 <<< 8).toNat
      = (bs.getD 0 0).toNat + (bs.getD 1 0).toNat * 2 ^ 8 := by
    rw [show (leByte bs 1) = (bs.getD 1 0).zeroExtend 64 from rfl,
      toNat_or_shift _ _ 8 (by rw [toNat_leByte]; omega) (by omega), toNat_leByte]
  have h2 : ((leByte bs 0 ||| leByte bs 1 <<< 8) ||| leByte bs 2 <<< 16).toNat
      = (bs.getD 0 0).toNat + (bs.getD 1 0).toNat * 2 ^ 8
        + (bs.getD 2 0).toNat * 2 ^ 16 := by
    rw [show (leByte bs 2) = (bs.getD 2 0).zeroExtend 64 from rfl,
      toNat_or_shift _ _ 16 (by rw [h1]; omega) (by omega), h1]
  have h3 : (leU32 bs 0).toNat
      = (bs.getD 0 0).toNat + (bs.getD 1 0).toNat * 2 ^ 8
        + (bs.getD 2 0).toNat * 2 ^ 16 + (bs.getD 3 0).toNat * 2 ^ 24 := by
    show (((leByte bs 0 ||| leByte bs 1 <<< 8) ||| leByte bs 2 <<< 16)
      ||| leByte bs 3 <<< 24).toNat = _
    rw [show (leByte bs 3) = (bs.getD 3 0).zeroExtend 64 from rfl,
      toNat_or_shift _ _ 24 (by rw [h2]; omega) (by omega), h2]
  rw [h3]
  -- the reference side, on the first four bytes. Peeled with `rcases` rather than a
  -- `match … hlen`: the equation compiler diverges on a list pattern discriminated by
  -- a `4 ≤ length` proof, and no `maxRecDepth` bump fixes it.
  rcases bs with _ | ⟨c0, tl0⟩
  · simp at hlen
  rcases tl0 with _ | ⟨c1, tl1⟩
  · simp at hlen
  rcases tl1 with _ | ⟨c2, tl2⟩
  · simp at hlen
  rcases tl2 with _ | ⟨c3, rest⟩
  · simp at hlen
  simp only [List.take_succ_cons, List.take_zero, List.getD_cons_zero,
    List.getD_cons_succ, EvmAsm.Stateless.SpecRef.bytesLEtoNat]
  ring

/-! ## Non-vacuity pins

    Both sides of the accessor bridge evaluated at the boundaries that matter for a
    little-endian read: byte order (so a BE/LE swap cannot hide), the all-zero and
    all-ones words, and a value with a high bit set in each of the four lanes. -/

section Pins

private def b (n : Nat) : BitVec 8 := BitVec.ofNat 8 n

-- byte ORDER: 0x04030201, not 0x01020304 -- a BE/LE swap fails here
#guard (leU32 [b 1, b 2, b 3, b 4] 0).toNat == 0x04030201
#guard EvmAsm.Stateless.SpecRef.bytesLEtoNat ([b 1, b 2, b 3, b 4].take 4) == 0x04030201
-- the two extremes
#guard (leU32 [b 0, b 0, b 0, b 0] 0).toNat
  == EvmAsm.Stateless.SpecRef.bytesLEtoNat ([b 0, b 0, b 0, b 0].take 4)
#guard (leU32 [b 255, b 255, b 255, b 255] 0).toNat == 0xffffffff
-- a high bit in each lane, so no lane is silently dropped or sign-extended
#guard (leU32 [b 0x80, b 0, b 0, b 0] 0).toNat == 0x80
#guard (leU32 [b 0, b 0x80, b 0, b 0] 0).toNat == 0x8000
#guard (leU32 [b 0, b 0, b 0x80, b 0] 0).toNat == 0x800000
#guard (leU32 [b 0, b 0, b 0, b 0x80] 0).toNat == 0x80000000
-- trailing bytes beyond the first four are ignored
#guard (leU32 [b 1, b 2, b 3, b 4, b 9, b 9] 0).toNat == 0x04030201

end Pins

/-! ## The flat whole-routine triple, derived by the adapter -/

/-- The routine's `CodeReq`, at its linked guest address. -/
def bgvCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.bgv_u32le : Word) bgvU32le_prog

/-- The exposed registers other than `a0`: the callee owns the whole exposed file (that
    is what its `Fn.Spec` claims), surfaced to callers as `regOwn` riders. -/
def bgvScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** regAtomsOf vf bgvScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [bgvScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_scratch : (.x10 : Reg) ∉ bgvScratch := by decide

/-- ⭐ **`bgv_u32le` at its linked guest address.** Entered with a buffer pointer in
    `a0`, an aligned return address in `ra`, ownership of the remaining exposed
    registers and a read-only `bytesRegion` of at least 4 bytes, it returns
    `a0 = leU32 bs 0` with the region intact.

    DERIVED from `bgvU32leFn_spec` by `Fn.retSpecFlat` — the machine reasoning is the
    SAsm proof, not repeated here. Simpler than the `bnqZeroFlat_spec` exemplar because
    `rw := RwRegion.empty`, so the adapter's writable buffer is `[]` and its
    `bytesRegion` collapses. -/
theorem bgvU32leFlat_spec (ret p : Word) (bs : List (BitVec 8))
    (hlen : 4 ≤ bs.length)
    (hwf : (Region.mk p bs).wf)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((bgvU32leFn p bs).body.steps + 1)
      (GuestAddrs.bgv_u32le : Word) ret bgvCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ p) ** regOwns bgvScratch ** bytesRegion p bs)
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ leU32 bs 0) ** regOwns bgvScratch **
        bytesRegion p bs) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns bgvScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ p) ** bytesRegion p bs)
      (fun vf => ?_))
  have had := Fn.retSpecFlat (bgvU32leFn p bs) (GuestAddrs.bgv_u32le : Word)
    (bgvU32leFn_spec p bs hwf (GuestAddrs.bgv_u32le : Word))
    (by show 4 * (11 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then p else vf r)
    ([] : List (BitVec 8))
    rfl
    (by
      refine ⟨?_, hlen, rfl⟩
      show RegFile.get (fun r => if r = .x10 then p else vf r) .x10 = p
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl)
    (fun _ _ _ h => h.2)
    (Q := (.x10 ↦ᵣ leU32 bs 0) ** regOwns bgvScratch)
    (fun rf' ws' hws' hpost' hp hh => by
      obtain ⟨hx10', -⟩ := hpost'
      obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hws'
      rw [show (bgvU32leFn p bs).rw.base = RwRegion.empty.base from rfl,
        bytesRegion_nil, sepConj_emp_right'] at hh
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split,
        show rf' .x10 = leU32 bs 0 from by
          rw [show rf' .x10 = rf'.get .x10 from by
            rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]]
          exact hx10'] at hh
      have hh2 := sepConj_mono_right
        (regAtomsOf_to_regOwns (fun r => rf' r) bgvScratch) hp hh
      xperm_hyp hh2)
  rw [show (bgvU32leFn p bs).programRet (GuestAddrs.bgv_u32le : Word)
      = bgvU32le_prog from rfl] at had
  have hadC := liftCode (cr' := bgvCr) had (by unfold bgvCr; code_mem)
  rw [show (bgvU32leFn p bs).rw = RwRegion.empty from rfl,
    show (bgvU32leFn p bs).region = Region.mk p bs from rfl,
    bytesRegion_nil, sepConj_emp_right'] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split,
    show (if (Reg.x10 : Reg) = .x10 then p else vf .x10) = p from if_pos rfl,
    regAtomsOf_congr (fun r => if r = .x10 then p else vf r) vf bgvScratch
      (fun r hr => by
        show (if r = .x10 then p else vf r) = vf r
        exact if_neg (fun (hc : r = .x10) => x10_notin_scratch (hc ▸ hr)))] at hadC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hadC

end BgvU32leSpec

end EvmAsm.Codegen
