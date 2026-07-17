/-
  Infrastructure for discharging `BgvOffsetAssumed` (a4gbr residual).

  Loop-site `bgv_u32le` reads at `txBase+4*i` (only 4-aligned for odd i).
  Proven `bgvFlat_spec` needs `Region.wf` (8-aligned focus). Ambient LBU
  composition (any address) is the honest discharge path.

  This file lands the key helper `bytesRegion_lbu_imm_within` (LBU with
  small imm over ambient `bytesRegion`) plus `leU32_eq_bytes`. Full 12-instr
  ambient compose + `BgvOffsetAssumed` package is the next commit on this branch.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm

namespace EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec

open EvmAsm.Rv64
open EvmAsm.Codegen.SgLoadU32leSAsm (leU32 leByte)

private theorem se12_ofNat_lt4 (k : Nat) (hk : k < 4) :
    signExtend12 (BitVec.ofNat 12 k) = BitVec.ofNat 64 k := by
  interval_cases k <;> decide

/-- Unfold `leU32` to the four zero-extended OR/shift bytes. -/
theorem leU32_eq_bytes (bs : List (BitVec 8)) (off : Nat)
    (h0 : off < bs.length) (h1 : off + 1 < bs.length)
    (h2 : off + 2 < bs.length) (h3 : off + 3 < bs.length) :
    leU32 bs off =
      ((bs[off]'h0).zeroExtend 64) |||
      (((bs[off + 1]'h1).zeroExtend 64) <<< 8) |||
      (((bs[off + 2]'h2).zeroExtend 64) <<< 16) |||
      (((bs[off + 3]'h3).zeroExtend 64) <<< 24) := by
  simp only [leU32, leByte, List.getD_eq_getElem?_getD]
  simp only [List.getElem?_eq_getElem h0, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, List.getElem?_eq_getElem h3, Option.getD]

set_option maxRecDepth 8000 in
/-- LBU with small positive imm over ambient `bytesRegion` (rs1 holds loadPtr =
    regionBase+off). Effective address = regionBase+(off+k). classical-3. -/
theorem bytesRegion_lbu_imm_within
    (rd rs1 : Reg) (regionBase vOld loadPtr : Word) (pc : Word)
    (bs : List (BitVec 8)) (off k : Nat)
    (hrd : rd ≠ .x0)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (halign : regionBase.toNat % 8 = 0)
    (hi : off + k < bs.length)
    (hover : regionBase.toNat + (off + k) < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 (off + k)) = true)
    (hk : k < 4) :
    cpsTripleWithin 1 pc (pc + 4)
      (CodeReq.singleton pc (.LBU rd rs1 (BitVec.ofNat 12 k)))
      ((rs1 ↦ᵣ loadPtr) ** (rd ↦ᵣ vOld) ** bytesRegion regionBase bs)
      ((rs1 ↦ᵣ loadPtr) **
        (rd ↦ᵣ ((bs[off + k]'hi).zeroExtend 64)) ** bytesRegion regionBase bs) := by
  have hse : signExtend12 (BitVec.ofNat 12 k) = BitVec.ofNat 64 k := se12_ofNat_lt4 k hk
  have haddr : loadPtr + signExtend12 (BitVec.ofNat 12 k) =
      regionBase + BitVec.ofNat 64 (off + k) := by
    rw [hptr, hse, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hq : 8 * ((off + k) / 8) < bs.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegion_dword_at regionBase bs ((off + k) / 8) hq
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * ((off + k) / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * ((off + k) / 8))).take 8) with hwv
  have halign' :
      alignToDword (loadPtr + signExtend12 (BitVec.ofNat 12 k)) = dwordAddr := by
    rw [haddr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have hvalid' :
      isValidByteAccess (loadPtr + signExtend12 (BitVec.ofNat 12 k)) = true := by
    rw [haddr]; exact hvalid
  have lbu := generic_lbu_spec_within rd rs1 loadPtr vOld (BitVec.ofNat 12 k) pc
    dwordAddr wordVal hrd halign' hvalid'
  have hbyte :
      extractByte wordVal (byteOffset (loadPtr + signExtend12 (BitVec.ofNat 12 k))) =
        bs[off + k]'hi := by
    rw [haddr, byteOffset_add_ofNat_of_aligned halign hover, hwv,
      extractByte_packBytes _ _ (by omega)
        (by rw [List.length_take, List.length_drop]; omega),
      List.getElem_take, List.getElem_drop]
    congr 1; omega
  rw [hbyte] at lbu
  rw [heq]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hr) lbu)

#print axioms bytesRegion_lbu_imm_within
#print axioms leU32_eq_bytes

end EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
