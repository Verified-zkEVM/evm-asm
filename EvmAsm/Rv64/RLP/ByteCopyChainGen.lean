/-
  EvmAsm.Rv64.RLP.ByteCopyChainGen

  The unrolled byte-array copy chain with INDEPENDENT source/destination start indices
  `si0`/`di0`: copy `N` bytes `src[si0 .. si0+N)` into destination positions
  `[di0, di0+N)`, as `N` `rlp_copy_iter_gen` blocks in sequence. The straight-line
  primitive a fixed-size (20-byte address / 32-byte hash) RLP field decoder uses to
  write its payload into the (whole, dword-aligned) output-struct region — the field's
  destination offset `di0` is arbitrary (possibly unaligned), only the region base is
  aligned, and `si0` (the input-buffer payload position) is unrelated to `di0`.

  Proved by induction on `N`, reusing `rlp_copy_iter_gen_spec_within` and the chain
  infrastructure (`byteCopyChainCR`, `copyIterCR_disjoint_chainCR`).
-/

import EvmAsm.Rv64.RLP.ByteCopyIterGen
import EvmAsm.Rv64.RLP.ByteCopyChainInfra

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- Destination bytes after copying `N` bytes (`src[si0 .. si0+N)` into positions
    `[di0, di0+N)` of `dst`), one byte per block. -/
def copyRangeGen (dst src : List (BitVec 8)) (si0 di0 : Nat) : Nat → List (BitVec 8)
  | 0 => dst
  | n + 1 => copyRangeGen (dst.set di0 (getByteAt src si0)) src (si0 + 1) (di0 + 1) n

/-- `getByteAt` of an in-range index is the indexed element. -/
private theorem getByteAt_of_lt {l : List (BitVec 8)} {i : Nat} (h : i < l.length) :
    getByteAt l i = l[i] := by
  rw [getByteAt, dif_pos h]

set_option maxRecDepth 8000 in
/-- **Unrolled byte-copy chain (independent indices).** Copies `N` bytes from
    `src[si0 ..]` into destination positions `[di0, di0+N)`, leaving `src` unchanged and
    the destination region equal to `copyRangeGen dstBytes srcBytes si0 di0 N`. -/
theorem rlp_copy_chain_gen_spec
    (srcBase dstBase : Word) (srcBytes : List (BitVec 8))
    (hsalign : srcBase.toNat % 8 = 0) (hdalign : dstBase.toNat % 8 = 0)
    (hsover : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ i, i < srcBytes.length → isValidByteAccess (srcBase + BitVec.ofNat 64 i) = true) :
    ∀ (N si0 di0 : Nat) (cnt v12Old : Word) (dstBytes : List (BitVec 8)) (base : Word),
      si0 + N ≤ srcBytes.length →
      di0 + N ≤ dstBytes.length →
      dstBase.toNat + dstBytes.length < 2 ^ 64 →
      (∀ i, i < dstBytes.length → isValidByteAccess (dstBase + BitVec.ofNat 64 i) = true) →
      base.toNat + 20 * N < 2 ^ 64 →
      cpsTripleWithin (5 * N) base (base + BitVec.ofNat 64 (20 * N))
        (byteCopyChainCR base N)
        ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 si0)) **
         (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 di0)) ** (.x15 ↦ᵣ cnt) **
         bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
        ((regOwn .x12) ** (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (si0 + N))) **
         (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 (di0 + N))) ** (regOwn .x15) **
         bytesRegion srcBase srcBytes ** bytesRegion dstBase (copyRangeGen dstBytes srcBytes si0 di0 N)) := by
  intro N
  induction N with
  | zero =>
    intro si0 di0 cnt v12Old dstBytes base _ _ _ _ _
    simp only [Nat.mul_zero, Nat.add_zero, byteCopyChainCR, copyRangeGen]
    rw [show base + BitVec.ofNat 64 0 = base from by bv_omega]
    refine cpsTripleWithin_refl (fun h hp => ?_)
    exact (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (regIs_implies_regOwn .x15))))) h
      ((sepConj_mono_left (regIs_implies_regOwn .x12)) h hp)
  | succ n ih =>
    intro si0 di0 cnt v12Old dstBytes base hsrc hdst hdov hdval hcode
    have hsrc' : si0 < srcBytes.length := by omega
    have hdst' : di0 < dstBytes.length := by omega
    have hsover' : srcBase.toNat + si0 < 2 ^ 64 := by omega
    have hdover' : dstBase.toNat + di0 < 2 ^ 64 := by omega
    have hsvalid' : isValidByteAccess (srcBase + BitVec.ofNat 64 si0) = true := hsvalid si0 (by omega)
    have hdvalid' : isValidByteAccess (dstBase + BitVec.ofNat 64 di0) = true := hdval di0 (by omega)
    have hbyte : (srcBytes[si0]'hsrc') = getByteAt srcBytes si0 := (getByteAt_of_lt hsrc').symm
    have iter := rlp_copy_iter_gen_spec_within srcBase dstBase srcBytes dstBytes si0 di0 cnt v12Old
      base hsalign hdalign hsrc' hdst' hsover' hdover' hsvalid' hdvalid'
    rw [hbyte] at iter
    have hIH := ih (si0 + 1) (di0 + 1) (cnt + signExtend12 (-1 : BitVec 12))
      ((getByteAt srcBytes si0).zeroExtend 64)
      (dstBytes.set di0 (getByteAt srcBytes si0)) (base + 20)
      (by omega)
      (by rw [List.length_set]; omega)
      (by rw [List.length_set]; exact hdov)
      (by intro i hi; rw [List.length_set] at hi; exact hdval i hi)
      (by have : (base + 20).toNat = base.toNat + 20 := by
            have : base.toNat + 20 < 2 ^ 64 := by omega
            bv_omega
          omega)
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
    simp only [byteCopyChainCR, copyRangeGen, Nat.mul_succ]
    rw [show 5 * n + 5 = 5 + 5 * n from by omega,
        show si0 + (n + 1) = (si0 + 1) + n from by omega,
        show di0 + (n + 1) = (di0 + 1) + n from by omega,
        show base + BitVec.ofNat 64 (20 * n + 20)
          = (base + 20) + BitVec.ofNat 64 (20 * n) from by bv_omega]
    refine cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_seq hd
        (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp)
          (show cpsTripleWithin 5 base (base + 20) (copyIterCR base) _ _ from iter)) hIH)

end EvmAsm.Rv64.RLP
