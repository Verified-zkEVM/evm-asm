/-
  EvmAsm.Rv64.RLP.ScalarSpillChain

  Spill a u64 value register into the output struct region, little-endian: `N`
  `rlp_spill_iter` blocks in sequence (block `j` at `base + 12*j`) write `x11`'s bytes
  to output positions `[di0, di0+N)`, shifting `x11` right by 8 each block. For a u64
  scalar field `N = 8`, writing the value's 8 LE bytes into the unified output-struct
  `bytesRegion` (the same region the address/hash fields target).

  Mirrors the byte-copy chain (`ByteCopyChainInfra`/`Gen`): a 3-slot iteration CodeReq,
  range-based disjointness, a recursive chain CodeReq, and the inductive spec.
-/

import EvmAsm.Rv64.RLP.ScalarSpillIter
import EvmAsm.Rv64.RLP.ByteCopyChainInfra

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64

/-- One spill iteration's 3-slot CodeReq (matches `rlp_spill_iter_spec_within`). -/
def spillIterCR (base : Word) : CodeReq :=
  ((CodeReq.singleton base (.SB .x14 .x11 0)).union
      (CodeReq.singleton (base + 4) (.SRLI .x11 .x11 8))).union
      (CodeReq.singleton (base + 8) (.ADDI .x14 .x14 1))

theorem spillIterCR_none (base a : Word) (h : ∀ k, k < 3 → a ≠ base + BitVec.ofNat 64 (4 * k)) :
    spillIterCR base a = none := by
  have s0 : CodeReq.singleton base (.SB .x14 .x11 0) a = none :=
    CodeReq.singleton_miss (by have := h 0 (by omega); simpa using this)
  have s1 : CodeReq.singleton (base + 4) (.SRLI .x11 .x11 8) a = none :=
    CodeReq.singleton_miss (by have := h 1 (by omega); bv_omega)
  have s2 : CodeReq.singleton (base + 8) (.ADDI .x14 .x14 1) a = none :=
    CodeReq.singleton_miss (by have := h 2 (by omega); bv_omega)
  simp only [spillIterCR, CodeReq.union, s0, s1, s2]

theorem spillIterCR_disjoint (base1 base2 : Word)
    (hsep : base1.toNat + 12 ≤ base2.toNat) (hov : base2.toNat + 12 < 2 ^ 64) :
    (spillIterCR base1).Disjoint (spillIterCR base2) := by
  intro a
  by_cases hin : ∀ k, k < 3 → a ≠ base1 + BitVec.ofNat 64 (4 * k)
  · exact Or.inl (spillIterCR_none base1 a hin)
  · push Not at hin
    obtain ⟨k, hk, rfl⟩ := hin
    exact Or.inr (spillIterCR_none base2 _ (fun k2 hk2 => by bv_omega))

/-- CodeReq of the unrolled N-block spill chain: block `j` (a `spillIterCR`) at `base + 12*j`. -/
def spillChainCR (base : Word) : Nat → CodeReq
  | 0 => CodeReq.empty
  | n + 1 => (spillIterCR base).union (spillChainCR (base + 12) n)

theorem spillIterCR_disjoint_chainCR (base bw : Word) (N : Nat)
    (hsep : base.toNat + 12 ≤ bw.toNat) (hov : bw.toNat + 12 * N < 2 ^ 64) :
    (spillIterCR base).Disjoint (spillChainCR bw N) := by
  induction N generalizing bw with
  | zero => simpa [spillChainCR] using CodeReq.Disjoint.empty_right (spillIterCR base)
  | succ k ih =>
    rw [spillChainCR]
    refine CodeReq.Disjoint.union_right ?_ ?_
    · exact spillIterCR_disjoint base bw hsep (by omega)
    · exact ih (bw + 12)
        (by have : (bw + 12).toNat = bw.toNat + 12 := by
              have : bw.toNat + 12 < 2 ^ 64 := by omega
              bv_omega
            omega)
        (by have : (bw + 12).toNat = bw.toNat + 12 := by
              have : bw.toNat + 12 < 2 ^ 64 := by omega
              bv_omega
            omega)

/-- The output bytes after spilling `N` bytes of `v` (LE) into positions `[di0, di0+N)`. -/
def spillRange (dst : List (BitVec 8)) (v : Word) (di0 : Nat) : Nat → List (BitVec 8)
  | 0 => dst
  | n + 1 => spillRange (dst.set di0 (v.truncate 8)) (v >>> 8) (di0 + 1) n

set_option maxRecDepth 8000 in
/-- **Scalar register-spill chain.** Spill `N` bytes of `x11 = v` (little-endian) into
    output positions `[di0, di0+N)`, leaving the output region equal to
    `spillRange outBytes v di0 N`. -/
theorem rlp_spill_chain_spec
    (outBase : Word) (hdalign : outBase.toNat % 8 = 0) :
    ∀ (N di0 : Nat) (v : Word) (outBytes : List (BitVec 8)) (base : Word),
      di0 + N ≤ outBytes.length →
      outBase.toNat + outBytes.length < 2 ^ 64 →
      (∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true) →
      base.toNat + 12 * N < 2 ^ 64 →
      cpsTripleWithin (3 * N) base (base + BitVec.ofNat 64 (12 * N))
        (spillChainCR base N)
        ((.x11 ↦ᵣ v) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 di0)) ** bytesRegion outBase outBytes)
        ((regOwn .x11) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + N))) **
         bytesRegion outBase (spillRange outBytes v di0 N)) := by
  intro N
  induction N with
  | zero =>
    intro di0 v outBytes base _ _ _ _
    simp only [Nat.mul_zero, Nat.add_zero, spillChainCR, spillRange]
    rw [show base + BitVec.ofNat 64 0 = base from by bv_omega]
    refine cpsTripleWithin_refl (fun h hp => ?_)
    exact (sepConj_mono_left (regIs_implies_regOwn .x11)) h hp
  | succ n ih =>
    intro di0 v outBytes base hdst hdov hdval hcode
    have hdst' : di0 < outBytes.length := by omega
    have hdover' : outBase.toNat + di0 < 2 ^ 64 := by omega
    have hdvalid' : isValidByteAccess (outBase + BitVec.ofNat 64 di0) = true := hdval di0 (by omega)
    have iter := rlp_spill_iter_spec_within outBase outBytes di0 v base hdalign hdst' hdover' hdvalid'
    have hIH := ih (di0 + 1) (v >>> 8) (outBytes.set di0 (v.truncate 8)) (base + 12)
      (by rw [List.length_set]; omega)
      (by rw [List.length_set]; exact hdov)
      (by intro i hi; rw [List.length_set] at hi; exact hdval i hi)
      (by have : (base + 12).toNat = base.toNat + 12 := by
            have : base.toNat + 12 < 2 ^ 64 := by omega
            bv_omega
          omega)
    have hd : (spillIterCR base).Disjoint (spillChainCR (base + 12) n) :=
      spillIterCR_disjoint_chainCR base (base + 12) n
        (by have : (base + 12).toNat = base.toNat + 12 := by
              have : base.toNat + 12 < 2 ^ 64 := by omega
              bv_omega
            omega)
        (by have : (base + 12).toNat = base.toNat + 12 := by
              have : base.toNat + 12 < 2 ^ 64 := by omega
              bv_omega
            omega)
    simp only [spillChainCR, spillRange, Nat.mul_succ]
    rw [show 3 * n + 3 = 3 + 3 * n from by omega,
        show di0 + (n + 1) = (di0 + 1) + n from by omega,
        show base + BitVec.ofNat 64 (12 * n + 12)
          = (base + 12) + BitVec.ofNat 64 (12 * n) from by bv_omega]
    refine cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_seq hd
        (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp)
          (show cpsTripleWithin 3 base (base + 12) (spillIterCR base) _ _ from iter)) hIH)

end EvmAsm.Rv64.RLP
