/-
  EvmAsm.Rv64.RLP.ByteCopyChainInfra

  Infrastructure for the unrolled byte-array copy chain: copying N bytes is N
  `rlp_copy_iter` blocks in sequence (block `j` at `base + 20*j`), the destination
  region evolving one byte per block. (Field sizes are fixed — 20-byte address,
  32-byte hash — so unrolling avoids the hardware-loop branch/back-edge machinery;
  a tight loop is a future code-size optimization.)

  This file provides, mirroring `ScalarFieldWalkInfra`:
    * `copyIterCR base` — one iteration's 5-slot CodeReq (defeq to `rlp_copy_iter_spec_within`'s);
    * `copyIterCR_none` / `copyIterCR_disjoint` — range-based disjointness, proved once;
    * `byteCopyChainCR base N` — the recursive CodeReq of the unrolled N-block chain;
    * `copyIterCR_disjoint_chainCR` — one block ⊥ the rest-of-chain (by induction);
    * `copyRange` — the destination-bytes result of copying N bytes.
-/

import EvmAsm.Rv64.RLP.ByteCopyIter

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64

/-- One copy-iteration's 5-slot CodeReq (matches `rlp_copy_iter_spec_within`). -/
def copyIterCR (base : Word) : CodeReq :=
  ((((CodeReq.singleton base (.LBU .x12 .x13 0)).union
      (CodeReq.singleton (base + 4) (.SB .x14 .x12 0))).union
      (CodeReq.singleton (base + 8) (.ADDI .x13 .x13 1))).union
      (CodeReq.singleton (base + 12) (.ADDI .x14 .x14 1))).union
      (CodeReq.singleton (base + 16) (.ADDI .x15 .x15 (-1)))

/-- A copy iteration maps to `none` outside its 5 instruction slots `{base+4k : k<5}`. -/
theorem copyIterCR_none (base a : Word)
    (h : ∀ k, k < 5 → a ≠ base + BitVec.ofNat 64 (4 * k)) :
    copyIterCR base a = none := by
  have s0 : CodeReq.singleton base (.LBU .x12 .x13 0) a = none :=
    CodeReq.singleton_miss (by have := h 0 (by omega); simpa using this)
  have s1 : CodeReq.singleton (base + 4) (.SB .x14 .x12 0) a = none :=
    CodeReq.singleton_miss (by have := h 1 (by omega); bv_omega)
  have s2 : CodeReq.singleton (base + 8) (.ADDI .x13 .x13 1) a = none :=
    CodeReq.singleton_miss (by have := h 2 (by omega); bv_omega)
  have s3 : CodeReq.singleton (base + 12) (.ADDI .x14 .x14 1) a = none :=
    CodeReq.singleton_miss (by have := h 3 (by omega); bv_omega)
  have s4 : CodeReq.singleton (base + 16) (.ADDI .x15 .x15 (-1)) a = none :=
    CodeReq.singleton_miss (by have := h 4 (by omega); bv_omega)
  simp only [copyIterCR, CodeReq.union, s0, s1, s2, s3, s4]

/-- **Reusable copy-iteration disjointness.** Two iterations whose 20-byte code ranges
    don't overlap (`base2 ≥ base1 + 20`) have disjoint CodeReqs. -/
theorem copyIterCR_disjoint (base1 base2 : Word)
    (hsep : base1.toNat + 20 ≤ base2.toNat) (hov : base2.toNat + 20 < 2 ^ 64) :
    (copyIterCR base1).Disjoint (copyIterCR base2) := by
  intro a
  by_cases hin : ∀ k, k < 5 → a ≠ base1 + BitVec.ofNat 64 (4 * k)
  · exact Or.inl (copyIterCR_none base1 a hin)
  · push Not at hin
    obtain ⟨k, hk, rfl⟩ := hin
    exact Or.inr (copyIterCR_none base2 _ (fun k2 hk2 => by bv_omega))

/-- CodeReq of the unrolled N-block copy chain: block `j` (a `copyIterCR`) at `base + 20*j`. -/
def byteCopyChainCR (base : Word) : Nat → CodeReq
  | 0 => CodeReq.empty
  | n + 1 => (copyIterCR base).union (byteCopyChainCR (base + 20) n)

/-- **One block ⊥ rest-of-chain.** A copy iteration at `base` is disjoint from the
    chain starting at `bw ≥ base + 20`. Proved by induction on the block count. -/
theorem copyIterCR_disjoint_chainCR (base bw : Word) (N : Nat)
    (hsep : base.toNat + 20 ≤ bw.toNat) (hov : bw.toNat + 20 * N < 2 ^ 64) :
    (copyIterCR base).Disjoint (byteCopyChainCR bw N) := by
  induction N generalizing bw with
  | zero => simpa [byteCopyChainCR] using CodeReq.Disjoint.empty_right (copyIterCR base)
  | succ k ih =>
    rw [byteCopyChainCR]
    refine CodeReq.Disjoint.union_right ?_ ?_
    · exact copyIterCR_disjoint base bw hsep (by omega)
    · exact ih (bw + 20)
        (by have : (bw + 20).toNat = bw.toNat + 20 := by
              have : bw.toNat + 20 < 2 ^ 64 := by omega
              bv_omega
            omega)
        (by have hb : (bw + 20).toNat = bw.toNat + 20 := by
              have : bw.toNat + 20 < 2 ^ 64 := by omega
              bv_omega
            omega)

/-- The destination bytes after copying `N` bytes (`src[off+k0 .. off+k0+N)` into
    positions `[k0, k0+N)` of `dst`), one byte per block. -/
def copyRange (dst src : List (BitVec 8)) (off k0 : Nat) : Nat → List (BitVec 8)
  | 0 => dst
  | n + 1 => copyRange (dst.set k0 (getByteAt src (off + k0))) src off (k0 + 1) n

end EvmAsm.Rv64.RLP
