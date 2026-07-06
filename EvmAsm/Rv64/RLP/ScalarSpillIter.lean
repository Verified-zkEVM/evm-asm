/-
  EvmAsm.Rv64.RLP.ScalarSpillIter

  EL.3 / Phase 5 — one iteration of the scalar register-spill: write the low byte of a
  u64 value register `x11` into the output struct region, shift the value right by 8, and
  advance the destination pointer. Spilling all 8 bytes (little-endian) writes the value
  into the unified output-struct `bytesRegion` — the scalar analog of one copy-loop block,
  used to store decoded u64 fields (nonce, gas_limit, …) into the same whole-struct region
  the byte-array (address/hash) fields use.

      base       SB   x11, x14, 0     ; region[di] := x11 & 0xFF   (low byte)
      base+4     SRLI x11, x11, 8     ; x11 >>= 8
      base+8     ADDI x14, x14, 1     ; dst ptr += 1
      base+12    (exit)
-/

import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.SeqFrame
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

local macro "pcfree_region" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact pcFree_emp
    | apply pcFree_sepConj)

set_option maxRecDepth 8000 in
/-- **One scalar-spill iteration.** Writes `x11`'s low byte to output byte `di`, shifts
    `x11` right by 8, and advances the dst pointer. The output region's byte `di` becomes
    `v.truncate 8` (the current low byte). -/
theorem rlp_spill_iter_spec_within
    (outBase : Word) (outBytes : List (BitVec 8)) (di : Nat) (v : Word) (base : Word)
    (hdalign : outBase.toNat % 8 = 0) (hdst : di < outBytes.length)
    (hdover : outBase.toNat + di < 2 ^ 64)
    (hdvalid : isValidByteAccess (outBase + BitVec.ofNat 64 di) = true) :
    cpsTripleWithin 3 base (base + 12)
      (((CodeReq.singleton base (.SB .x14 .x11 0)).union
          (CodeReq.singleton (base + 4) (.SRLI .x11 .x11 8))).union
          (CodeReq.singleton (base + 8) (.ADDI .x14 .x14 1)))
      ((.x11 ↦ᵣ v) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 di)) ** bytesRegion outBase outBytes)
      ((.x11 ↦ᵣ (v >>> 8)) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di + 1))) **
       bytesRegion outBase (outBytes.set di (v.truncate 8))) := by
  -- (1) SB x14, x11, 0 : region[di] := x11.truncate 8.
  have sb := bytesRegion_sb_within .x14 .x11 outBase v base outBytes di hdalign hdst hdover hdvalid
  have s_sb : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SB .x14 .x11 0))
      ((.x11 ↦ᵣ v) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 di)) ** bytesRegion outBase outBytes)
      ((.x11 ↦ᵣ v) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 di)) **
       bytesRegion outBase (outBytes.set di (v.truncate 8))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) sb
  -- (2) SRLI x11, x11, 8 : x11 >>= 8.
  have srli := srli_spec_gen_same_within .x11 v 8 (base + 4) (by decide)
  have s_srli : cpsTripleWithin 1 (base + 4) (base + 4 + 4)
      (CodeReq.singleton (base + 4) (.SRLI .x11 .x11 8))
      ((.x11 ↦ᵣ v) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 di)) **
       bytesRegion outBase (outBytes.set di (v.truncate 8)))
      ((.x11 ↦ᵣ (v >>> 8)) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 di)) **
       bytesRegion outBase (outBytes.set di (v.truncate 8))) := by
    have : (8 : BitVec 6).toNat = 8 := by decide
    rw [this] at srli
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x14 ↦ᵣ (outBase + BitVec.ofNat 64 di)) ** bytesRegion outBase (outBytes.set di (v.truncate 8)))
        (by pcfree_region) srli)
  rw [show base + 4 + 4 = base + 8 from by bv_omega] at s_srli
  -- (3) ADDI x14, x14, 1 : dst ptr += 1.
  have addi := addi_spec_gen_same_within .x14 (outBase + BitVec.ofNat 64 di) 1 (base + 8) (by nofun)
  rw [show (outBase + BitVec.ofNat 64 di) + signExtend12 (1 : BitVec 12)
      = outBase + BitVec.ofNat 64 (di + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at addi
  have s_addi : cpsTripleWithin 1 (base + 8) (base + 8 + 4)
      (CodeReq.singleton (base + 8) (.ADDI .x14 .x14 1))
      ((.x11 ↦ᵣ (v >>> 8)) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 di)) **
       bytesRegion outBase (outBytes.set di (v.truncate 8)))
      ((.x11 ↦ᵣ (v >>> 8)) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di + 1))) **
       bytesRegion outBase (outBytes.set di (v.truncate 8))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x11 ↦ᵣ (v >>> 8)) ** bytesRegion outBase (outBytes.set di (v.truncate 8)))
        (by pcfree_region) addi)
  rw [show base + 8 + 4 = base + 12 from by bv_omega] at s_addi
  have c12 := cpsTripleWithin_seq (CodeReq.Disjoint.singleton (by bv_omega)) s_sb s_srli
  exact cpsTripleWithin_seq
    (CodeReq.Disjoint.union_left (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega))) c12 s_addi

end EvmAsm.Rv64.RLP
