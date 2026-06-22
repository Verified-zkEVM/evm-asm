/-
  EvmAsm.Rv64.RLP.ByteCopyChain

  The unrolled byte-array copy chain: copy `N` bytes `src[off+k0 .. off+k0+N)` into
  positions `[k0, k0+N)` of the destination region, as `N` `rlp_copy_iter` blocks in
  sequence. The straight-line primitive a fixed-size (20-byte address / 32-byte hash)
  RLP field decoder uses to write its payload into the output struct.

  Proved by induction on `N`, reusing `rlp_copy_iter_spec_within` and the chain
  infrastructure (`byteCopyChainCR`, `copyIterCR_disjoint_chainCR`, `copyRange`) — the
  same skeleton as `unified_n_scalar_field_walk`, with the destination `bytesRegion`
  evolving one byte per block.
-/

import EvmAsm.Rv64.RLP.ByteCopyChainInfra

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- `getByteAt` of an in-range index is the indexed element. -/
private theorem getByteAt_of_lt {l : List (BitVec 8)} {i : Nat} (h : i < l.length) :
    getByteAt l i = l[i] := by
  rw [getByteAt, dif_pos h]

set_option maxRecDepth 8000 in
/-- **Unrolled byte-copy chain.** Copies `N` bytes from `src[off+k0 ..]` into
    destination positions `[k0, k0+N)`, leaving `src` unchanged and the destination
    region equal to `copyRange dstBytes srcBytes off k0 N`. -/
theorem rlp_copy_chain_spec
    (srcBase dstBase : Word) (srcBytes : List (BitVec 8)) (off : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hdalign : dstBase.toNat % 8 = 0)
    (hsover : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ i, i < srcBytes.length → isValidByteAccess (srcBase + BitVec.ofNat 64 i) = true) :
    ∀ (N k0 : Nat) (cnt v12Old : Word) (dstBytes : List (BitVec 8)) (base : Word),
      off + k0 + N ≤ srcBytes.length →
      k0 + N ≤ dstBytes.length →
      dstBase.toNat + dstBytes.length < 2 ^ 64 →
      (∀ i, i < dstBytes.length → isValidByteAccess (dstBase + BitVec.ofNat 64 i) = true) →
      base.toNat + 20 * N < 2 ^ 64 →
      cpsTripleWithin (5 * N) base (base + BitVec.ofNat 64 (20 * N))
        (byteCopyChainCR base N)
        ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (off + k0))) **
         (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 k0)) ** (.x15 ↦ᵣ cnt) **
         bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
        ((regOwn .x12) ** (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (off + k0 + N))) **
         (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 (k0 + N))) ** (regOwn .x15) **
         bytesRegion srcBase srcBytes ** bytesRegion dstBase (copyRange dstBytes srcBytes off k0 N)) := by
  intro N
  induction N with
  | zero =>
    intro k0 cnt v12Old dstBytes base _ _ _ _ _
    simp only [Nat.mul_zero, Nat.add_zero, byteCopyChainCR, copyRange]
    rw [show base + BitVec.ofNat 64 0 = base from by bv_omega]
    refine cpsTripleWithin_refl (fun h hp => ?_)
    exact (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (regIs_implies_regOwn .x15))))) h
      ((sepConj_mono_left (regIs_implies_regOwn .x12)) h hp)
  | succ n ih =>
    intro k0 cnt v12Old dstBytes base hsrc hdst hdov hdval hcode
    -- Head-block hypotheses.
    have hsrc' : off + k0 < srcBytes.length := by omega
    have hdst' : k0 < dstBytes.length := by omega
    have hsover' : srcBase.toNat + (off + k0) < 2 ^ 64 := by omega
    have hdover' : dstBase.toNat + k0 < 2 ^ 64 := by omega
    have hsvalid' : isValidByteAccess (srcBase + BitVec.ofNat 64 (off + k0)) = true :=
      hsvalid (off + k0) (by omega)
    have hdvalid' : isValidByteAccess (dstBase + BitVec.ofNat 64 k0) = true := hdval k0 (by omega)
    have hbyte : (srcBytes[off + k0]'hsrc') = getByteAt srcBytes (off + k0) :=
      (getByteAt_of_lt hsrc').symm
    -- One copy iteration at `base` (block k0).
    have iter := rlp_copy_iter_spec_within srcBase dstBase srcBytes dstBytes off k0 cnt v12Old base
      hsalign hdalign hsrc' hdst' hsover' hdover' hsvalid' hdvalid'
    rw [hbyte, show off + k0 + 1 = off + (k0 + 1) from by omega] at iter
    -- The rest of the chain at `base + 20` (blocks k0+1 .. k0+n).
    have hIH := ih (k0 + 1) (cnt + signExtend12 (-1 : BitVec 12))
      ((getByteAt srcBytes (off + k0)).zeroExtend 64)
      (dstBytes.set k0 (getByteAt srcBytes (off + k0))) (base + 20)
      (by omega)
      (by rw [List.length_set]; omega)
      (by rw [List.length_set]; exact hdov)
      (by intro i hi; rw [List.length_set] at hi; exact hdval i hi)
      (by have : (base + 20).toNat = base.toNat + 20 := by
            have : base.toNat + 20 < 2 ^ 64 := by omega
            bv_omega
          omega)
    -- Disjointness: head block ⊥ rest-of-chain.
    have hd : (copyIterCR base).Disjoint (byteCopyChainCR (base + 20) n) :=
      copyIterCR_disjoint_chainCR base (base + 20) n
        (by have : (base + 20).toNat = base.toNat + 20 := by
              have : base.toNat + 20 < 2 ^ 64 := by omega
              bv_omega
            omega)
        (by have : (base + 20).toNat = base.toNat + 20 := by
              have : base.toNat + 20 < 2 ^ 64 := by omega
              bv_omega
            omega)
    -- Normalise the chain CR / step count / exit / final dst to the cons forms.
    simp only [byteCopyChainCR, copyRange, Nat.mul_succ]
    rw [show 5 * n + 5 = 5 + 5 * n from by omega,
        show off + k0 + (n + 1) = off + (k0 + 1) + n from by omega,
        show k0 + (n + 1) = (k0 + 1) + n from by omega,
        show base + BitVec.ofNat 64 (20 * n + 20)
          = (base + 20) + BitVec.ofNat 64 (20 * n) from by bv_omega]
    -- The iteration's CR is `copyIterCR base` (defeq); compose with the rest.
    refine cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_seq hd
        (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp)
          (show cpsTripleWithin 5 base (base + 20) (copyIterCR base) _ _ from iter)) hIH)

end EvmAsm.Rv64.RLP
