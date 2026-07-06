/-
  EvmAsm.Rv64.RLP.ByteCopyIterGen

  One iteration of the byte-array copy loop, with INDEPENDENT source and destination
  byte indices `si`/`di`: read src byte `si` (`LBU` from the source `bytesRegion`),
  store it to dst byte `di` (`SB` into the destination `bytesRegion`), and advance the
  src pointer, dst pointer, and counter. The straight-line core (5 instructions) of the
  copy chain that decodes 20-byte address / 32-byte hash RLP fields into the output
  struct — independent indices let the destination be the whole (dword-aligned) output
  struct region with the field landing at an arbitrary (possibly unaligned) byte offset.

  src and dst are separate `**` conjuncts, so each instruction frames the region it
  doesn't touch — no explicit disjointness hypothesis is needed.

      base       LBU  x12, x13, 0      ; x12 = src[si]
      base+4     SB   x12, x14, 0      ; dst[di] := x12
      base+8     ADDI x13, x13, 1      ; src ptr += 1
      base+12    ADDI x14, x14, 1      ; dst ptr += 1
      base+16    ADDI x15, x15, -1     ; counter -= 1
      base+20    (exit)
-/

import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.SeqFrame
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- `pcFree` for separating conjunctions whose leaves may include `bytesRegion`
    (which the default `pcFree` tactic doesn't know). -/
local macro "pcfree_region" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact pcFree_emp
    | apply pcFree_sepConj)

set_option maxRecDepth 8000 in
/-- **One copy iteration (independent indices).** Reads `srcBytes[si]` and writes it to
    `dst` byte `di`, advancing the src pointer to `si+1`, the dst pointer to `di+1`, and
    decrementing the counter. The source region is unchanged; the destination region's
    byte `di` becomes `srcBytes[si]`. -/
theorem rlp_copy_iter_gen_spec_within
    (srcBase dstBase : Word) (srcBytes dstBytes : List (BitVec 8))
    (si di : Nat) (cnt v12Old : Word) (base : Word)
    (hsalign : srcBase.toNat % 8 = 0) (hdalign : dstBase.toNat % 8 = 0)
    (hsrc : si < srcBytes.length) (hdst : di < dstBytes.length)
    (hsover : srcBase.toNat + (si) < 2 ^ 64) (hdover : dstBase.toNat + di < 2 ^ 64)
    (hsvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 (si)) = true)
    (hdvalid : isValidByteAccess (dstBase + BitVec.ofNat 64 di) = true) :
    cpsTripleWithin 5 base (base + 20)
      (((((CodeReq.singleton base (.LBU .x12 .x13 0)).union
          (CodeReq.singleton (base + 4) (.SB .x14 .x12 0))).union
          (CodeReq.singleton (base + 8) (.ADDI .x13 .x13 1))).union
          (CodeReq.singleton (base + 12) (.ADDI .x14 .x14 1))).union
          (CodeReq.singleton (base + 16) (.ADDI .x15 .x15 (-1))))
      ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (si))) **
       (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 di)) ** (.x15 ↦ᵣ cnt) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      ((.x12 ↦ᵣ (srcBytes[si]'hsrc).zeroExtend 64) **
       (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
       (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 (di + 1))) **
       (.x15 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsrc))) := by
  -- (1) LBU x12, x13, 0 : x12 := src[off+di]; frame the dst region + x14, x15.
  have lbu := bytesRegion_lbu_within .x12 .x13 srcBase v12Old base srcBytes (si)
    (by decide) hsalign hsrc hsover hsvalid
  have s_lbu : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU .x12 .x13 0))
      ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (si))) **
       (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 di)) ** (.x15 ↦ᵣ cnt) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      ((.x12 ↦ᵣ (srcBytes[si]'hsrc).zeroExtend 64) **
       (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (si))) **
       (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 di)) ** (.x15 ↦ᵣ cnt) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 di)) ** (.x15 ↦ᵣ cnt) ** bytesRegion dstBase dstBytes)
        (by pcfree_region) lbu)
  -- (2) SB x12, x14, 0 : dst[di] := x12; frame the src region + x13, x15.
  have hbtrunc : ((srcBytes[si]'hsrc).zeroExtend 64).truncate 8 = srcBytes[si]'hsrc := by
    simp
  have sb := bytesRegion_sb_within .x14 .x12 dstBase ((srcBytes[si]'hsrc).zeroExtend 64)
    (base + 4) dstBytes di hdalign hdst hdover hdvalid
  rw [hbtrunc] at sb
  have s_sb : cpsTripleWithin 1 (base + 4) (base + 4 + 4)
      (CodeReq.singleton (base + 4) (.SB .x14 .x12 0))
      ((.x12 ↦ᵣ (srcBytes[si]'hsrc).zeroExtend 64) **
       (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (si))) **
       (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 di)) ** (.x15 ↦ᵣ cnt) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      ((.x12 ↦ᵣ (srcBytes[si]'hsrc).zeroExtend 64) **
       (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (si))) **
       (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 di)) ** (.x15 ↦ᵣ cnt) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsrc))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (si))) ** (.x15 ↦ᵣ cnt) **
         bytesRegion srcBase srcBytes) (by pcfree_region) sb)
  rw [show base + 4 + 4 = base + 8 from by bv_omega] at s_sb
  -- (3) ADDI x13, x13, 1 : src ptr += 1.
  have addi13 := addi_spec_gen_same_within .x13 (srcBase + BitVec.ofNat 64 (si)) 1 (base + 8)
    (by nofun)
  rw [show (srcBase + BitVec.ofNat 64 (si)) + signExtend12 (1 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (si + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at addi13
  -- (4) ADDI x14, x14, 1 : dst ptr += 1.
  have addi14 := addi_spec_gen_same_within .x14 (dstBase + BitVec.ofNat 64 di) 1 (base + 12)
    (by nofun)
  rw [show (dstBase + BitVec.ofNat 64 di) + signExtend12 (1 : BitVec 12)
      = dstBase + BitVec.ofNat 64 (di + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at addi14
  -- (5) ADDI x15, x15, -1 : counter -= 1.
  have addi15 := addi_spec_gen_same_within .x15 cnt (-1 : BitVec 12) (base + 16) (by nofun)
  -- Compose 1⨾2⨾3⨾4⨾5.
  have c12 := cpsTripleWithin_seq (CodeReq.Disjoint.singleton (by bv_omega)) s_lbu s_sb
  -- frame x12/x13/x14/x15/regions around addi13 (operates on x13) and weaken to match c12's post
  have s3 : cpsTripleWithin 1 (base + 8) (base + 8 + 4)
      (CodeReq.singleton (base + 8) (.ADDI .x13 .x13 1))
      ((.x12 ↦ᵣ (srcBytes[si]'hsrc).zeroExtend 64) **
       (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (si))) **
       (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 di)) ** (.x15 ↦ᵣ cnt) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsrc)))
      ((.x12 ↦ᵣ (srcBytes[si]'hsrc).zeroExtend 64) **
       (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
       (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 di)) ** (.x15 ↦ᵣ cnt) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsrc))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x12 ↦ᵣ (srcBytes[si]'hsrc).zeroExtend 64) **
         (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 di)) ** (.x15 ↦ᵣ cnt) **
         bytesRegion srcBase srcBytes ** bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsrc)))
        (by pcfree_region) addi13)
  rw [show base + 8 + 4 = base + 12 from by bv_omega] at s3
  have s4 : cpsTripleWithin 1 (base + 12) (base + 12 + 4)
      (CodeReq.singleton (base + 12) (.ADDI .x14 .x14 1))
      ((.x12 ↦ᵣ (srcBytes[si]'hsrc).zeroExtend 64) **
       (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
       (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 di)) ** (.x15 ↦ᵣ cnt) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsrc)))
      ((.x12 ↦ᵣ (srcBytes[si]'hsrc).zeroExtend 64) **
       (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
       (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 (di + 1))) ** (.x15 ↦ᵣ cnt) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsrc))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x12 ↦ᵣ (srcBytes[si]'hsrc).zeroExtend 64) **
         (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) ** (.x15 ↦ᵣ cnt) **
         bytesRegion srcBase srcBytes ** bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsrc)))
        (by pcfree_region) addi14)
  rw [show base + 12 + 4 = base + 16 from by bv_omega] at s4
  have s5 : cpsTripleWithin 1 (base + 16) (base + 16 + 4)
      (CodeReq.singleton (base + 16) (.ADDI .x15 .x15 (-1)))
      ((.x12 ↦ᵣ (srcBytes[si]'hsrc).zeroExtend 64) **
       (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
       (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 (di + 1))) ** (.x15 ↦ᵣ cnt) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsrc)))
      ((.x12 ↦ᵣ (srcBytes[si]'hsrc).zeroExtend 64) **
       (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
       (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 (di + 1))) **
       (.x15 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsrc))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x12 ↦ᵣ (srcBytes[si]'hsrc).zeroExtend 64) **
         (.x13 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         (.x14 ↦ᵣ (dstBase + BitVec.ofNat 64 (di + 1))) **
         bytesRegion srcBase srcBytes ** bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsrc)))
        (by pcfree_region) addi15)
  rw [show base + 16 + 4 = base + 20 from by bv_omega] at s5
  have c123 := cpsTripleWithin_seq
    (CodeReq.Disjoint.union_left (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega))) c12 s3
  have c1234 := cpsTripleWithin_seq
    (CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_left (CodeReq.Disjoint.singleton (by bv_omega))
        (CodeReq.Disjoint.singleton (by bv_omega)))
      (CodeReq.Disjoint.singleton (by bv_omega))) c123 s4
  have c12345 := cpsTripleWithin_seq
    (CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.union_left (CodeReq.Disjoint.singleton (by bv_omega))
          (CodeReq.Disjoint.singleton (by bv_omega)))
        (CodeReq.Disjoint.singleton (by bv_omega)))
      (CodeReq.Disjoint.singleton (by bv_omega))) c1234 s5
  exact c12345

end EvmAsm.Rv64.RLP
