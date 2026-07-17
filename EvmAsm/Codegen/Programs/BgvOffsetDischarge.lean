/-
  Infrastructure for discharging `BgvOffsetAssumed` (a4gbr residual).

  Loop-site `bgv_u32le` reads at `txBase+4*i` (only 4-aligned for odd i).
  Proven `bgvFlat_spec` needs `Region.wf` (8-aligned focus). Ambient LBU
  composition (any address) is the honest discharge path.

  Helpers: `bytesRegion_lbu_imm_within`, `leU32_eq_bytes`.
  Full 12-instr ambient compose: `bgvOffset_ambient_core` → `BgvOffsetAssumed`.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayHeader
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayLoop
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec

open EvmAsm.Rv64
open EvmAsm.Codegen
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

private theorem bgv_bound : 4 * bgvProg.length < 2 ^ 64 := by
  simp only [bgv_length]; decide

private theorem Bgv4 : Bgv + 4 = Bgv + BitVec.ofNat 64 4 := by
  simp only [Bgv, GuestAddrs.bgv_u32le]; decide
private theorem Bgv8 : Bgv + 8 = Bgv + BitVec.ofNat 64 8 := by
  simp only [Bgv, GuestAddrs.bgv_u32le]; decide
private theorem Bgv12 : Bgv + 12 = Bgv + BitVec.ofNat 64 12 := by
  simp only [Bgv, GuestAddrs.bgv_u32le]; decide
private theorem Bgv16 : Bgv + 16 = Bgv + BitVec.ofNat 64 16 := by
  simp only [Bgv, GuestAddrs.bgv_u32le]; decide
private theorem Bgv20 : Bgv + 20 = Bgv + BitVec.ofNat 64 20 := by
  simp only [Bgv, GuestAddrs.bgv_u32le]; decide
private theorem Bgv24 : Bgv + 24 = Bgv + BitVec.ofNat 64 24 := by
  simp only [Bgv, GuestAddrs.bgv_u32le]; decide
private theorem Bgv28 : Bgv + 28 = Bgv + BitVec.ofNat 64 28 := by
  simp only [Bgv, GuestAddrs.bgv_u32le]; decide
private theorem Bgv32 : Bgv + 32 = Bgv + BitVec.ofNat 64 32 := by
  simp only [Bgv, GuestAddrs.bgv_u32le]; decide
private theorem Bgv36 : Bgv + 36 = Bgv + BitVec.ofNat 64 36 := by
  simp only [Bgv, GuestAddrs.bgv_u32le]; decide
private theorem Bgv40 : Bgv + 40 = Bgv + BitVec.ofNat 64 40 := by
  simp only [Bgv, GuestAddrs.bgv_u32le]; decide
private theorem Bgv44 : Bgv + 44 = Bgv + BitVec.ofNat 64 44 := by
  simp only [Bgv, GuestAddrs.bgv_u32le]; decide

local macro "bgv_pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact bytesRegion_pcFree _ _
      | exact pcFree_emp
      | exact pcFree_pure)

private theorem shamt8 : ((8 : BitVec 6)).toNat = 8 := by decide
private theorem shamt16 : ((16 : BitVec 6)).toNat = 16 := by decide
private theorem shamt24 : ((24 : BitVec 6)).toNat = 24 := by decide

set_option maxRecDepth 8000 in
/-- Core ambient path (x1/x10/x5/x6 + bytes only). classical-3. -/
theorem bgvOffset_ambient_core
    (ret loadPtr regionBase : Word) (bs : List (BitVec 8)) (off : Nat)
    (v5 v6 : Word)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : off + 4 ≤ bs.length)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + off + 3 < 2 ^ 64)
    (hvalid : ∀ k, k < 4 →
      isValidByteAccess (regionBase + BitVec.ofNat 64 (off + k)) = true) :
    cpsTripleWithin nBgvSteps Bgv ret bgvCode
      ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ loadPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        bytesRegion regionBase bs)
      ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ leU32 bs off) **
        (.x5 ↦ᵣ leU32 bs off) **
        (.x6 ↦ᵣ (((bs[off + 3]'(by omega)).zeroExtend 64) <<< 24)) **
        bytesRegion regionBase bs) := by
  have h0 : off < bs.length := by omega
  have h1 : off + 1 < bs.length := by omega
  have h2 : off + 2 < bs.length := by omega
  have h3 : off + 3 < bs.length := by omega
  have hv0 := hvalid 0 (by omega)
  have hv1 := hvalid 1 (by omega)
  have hv2 := hvalid 2 (by omega)
  have hv3 := hvalid 3 (by omega)
  have hover0 : regionBase.toNat + off < 2 ^ 64 := by omega
  have hover1 : regionBase.toNat + (off + 1) < 2 ^ 64 := by omega
  have hover2 : regionBase.toNat + (off + 2) < 2 ^ 64 := by omega
  have hover3 : regionBase.toNat + (off + 3) < 2 ^ 64 := by omega
  -- [0] LBU x5,0(a0)
  have e0 := bytesRegion_lbu_imm_within .x5 .x10 regionBase v5 loadPtr Bgv
    bs off 0 (by decide) hptr halign h0 hover0 hv0 (by omega)
  have e0e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at Bgv Bgv bgvProg 0 (.LBU .x5 .x10 (0 : BitVec 12))
      (by decide) (by rw [bgv_length]; decide) rfl bgv_bound) e0
  have e0F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (.x6 ↦ᵣ v6)) (by bgv_pcf) e0e
  -- [1] LBU x6,1(a0)
  have e1 := bytesRegion_lbu_imm_within .x6 .x10 regionBase v6 loadPtr (Bgv + 4)
    bs off 1 (by decide) hptr halign h1 hover1 hv1 (by omega)
  have e1e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at Bgv (Bgv + 4) bgvProg 1 (.LBU .x6 .x10 (1 : BitVec 12))
      Bgv4 (by rw [bgv_length]; decide) rfl bgv_bound) e1
  have e1F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (.x5 ↦ᵣ ((bs[off]'h0).zeroExtend 64))) (by bgv_pcf) e1e
  -- [2] SLLI x6,x6,8
  have e2 := slli_spec_gen_same_within .x6 ((bs[off + 1]'h1).zeroExtend 64)
    (8 : BitVec 6) (Bgv + 8) (by decide)
  rw [shamt8] at e2
  have e2e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at Bgv (Bgv + 8) bgvProg 2 (.SLLI .x6 .x6 (8 : BitVec 6))
      Bgv8 (by rw [bgv_length]; decide) rfl bgv_bound) e2
  have e2F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ loadPtr) **
      (.x5 ↦ᵣ ((bs[off]'h0).zeroExtend 64)) ** bytesRegion regionBase bs)
    (by bgv_pcf) e2e
  -- [3] OR x5,x5,x6
  have e3 := or_spec_gen_rd_eq_rs1_within .x5 .x6
    ((bs[off]'h0).zeroExtend 64)
    (((bs[off + 1]'h1).zeroExtend 64) <<< 8) (Bgv + 12) (by decide)
  have e3e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at Bgv (Bgv + 12) bgvProg 3 (.OR .x5 .x5 .x6)
      Bgv12 (by rw [bgv_length]; decide) rfl bgv_bound) e3
  have e3F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ loadPtr) ** bytesRegion regionBase bs)
    (by bgv_pcf) e3e
  -- [4] LBU x6,2(a0)
  have e4 := bytesRegion_lbu_imm_within .x6 .x10 regionBase
    (((bs[off + 1]'h1).zeroExtend 64) <<< 8) loadPtr (Bgv + 16)
    bs off 2 (by decide) hptr halign h2 hover2 hv2 (by omega)
  have e4e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at Bgv (Bgv + 16) bgvProg 4 (.LBU .x6 .x10 (2 : BitVec 12))
      Bgv16 (by rw [bgv_length]; decide) rfl bgv_bound) e4
  have e4F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) **
      (.x5 ↦ᵣ (((bs[off]'h0).zeroExtend 64) |||
        (((bs[off + 1]'h1).zeroExtend 64) <<< 8)))) (by bgv_pcf) e4e
  -- [5] SLLI x6,x6,16
  have e5 := slli_spec_gen_same_within .x6 ((bs[off + 2]'h2).zeroExtend 64)
    (16 : BitVec 6) (Bgv + 20) (by decide)
  rw [shamt16] at e5
  have e5e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at Bgv (Bgv + 20) bgvProg 5 (.SLLI .x6 .x6 (16 : BitVec 6))
      Bgv20 (by rw [bgv_length]; decide) rfl bgv_bound) e5
  have e5F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ loadPtr) **
      (.x5 ↦ᵣ (((bs[off]'h0).zeroExtend 64) |||
        (((bs[off + 1]'h1).zeroExtend 64) <<< 8))) **
      bytesRegion regionBase bs) (by bgv_pcf) e5e
  -- [6] OR x5,x5,x6
  have e6 := or_spec_gen_rd_eq_rs1_within .x5 .x6
    (((bs[off]'h0).zeroExtend 64) ||| (((bs[off + 1]'h1).zeroExtend 64) <<< 8))
    (((bs[off + 2]'h2).zeroExtend 64) <<< 16) (Bgv + 24) (by decide)
  have e6e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at Bgv (Bgv + 24) bgvProg 6 (.OR .x5 .x5 .x6)
      Bgv24 (by rw [bgv_length]; decide) rfl bgv_bound) e6
  have e6F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ loadPtr) ** bytesRegion regionBase bs)
    (by bgv_pcf) e6e
  -- [7] LBU x6,3(a0)
  have e7 := bytesRegion_lbu_imm_within .x6 .x10 regionBase
    (((bs[off + 2]'h2).zeroExtend 64) <<< 16) loadPtr (Bgv + 28)
    bs off 3 (by decide) hptr halign h3 hover3 hv3 (by omega)
  have e7e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at Bgv (Bgv + 28) bgvProg 7 (.LBU .x6 .x10 (3 : BitVec 12))
      Bgv28 (by rw [bgv_length]; decide) rfl bgv_bound) e7
  have e7F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) **
      (.x5 ↦ᵣ ((((bs[off]'h0).zeroExtend 64) |||
        (((bs[off + 1]'h1).zeroExtend 64) <<< 8)) |||
        (((bs[off + 2]'h2).zeroExtend 64) <<< 16)))) (by bgv_pcf) e7e
  -- [8] SLLI x6,x6,24
  have e8 := slli_spec_gen_same_within .x6 ((bs[off + 3]'h3).zeroExtend 64)
    (24 : BitVec 6) (Bgv + 32) (by decide)
  rw [shamt24] at e8
  have e8e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at Bgv (Bgv + 32) bgvProg 8 (.SLLI .x6 .x6 (24 : BitVec 6))
      Bgv32 (by rw [bgv_length]; decide) rfl bgv_bound) e8
  have e8F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ loadPtr) **
      (.x5 ↦ᵣ ((((bs[off]'h0).zeroExtend 64) |||
        (((bs[off + 1]'h1).zeroExtend 64) <<< 8)) |||
        (((bs[off + 2]'h2).zeroExtend 64) <<< 16))) **
      bytesRegion regionBase bs) (by bgv_pcf) e8e
  -- [9] OR x5,x5,x6
  have e9 := or_spec_gen_rd_eq_rs1_within .x5 .x6
    (((((bs[off]'h0).zeroExtend 64) ||| (((bs[off + 1]'h1).zeroExtend 64) <<< 8)) |||
      (((bs[off + 2]'h2).zeroExtend 64) <<< 16)))
    (((bs[off + 3]'h3).zeroExtend 64) <<< 24) (Bgv + 36) (by decide)
  have e9e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at Bgv (Bgv + 36) bgvProg 9 (.OR .x5 .x5 .x6)
      Bgv36 (by rw [bgv_length]; decide) rfl bgv_bound) e9
  have e9F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ loadPtr) ** bytesRegion regionBase bs)
    (by bgv_pcf) e9e
  -- [10] MV a0,x5
  have e10 := mv_spec_gen_within .x10 .x5
    ((((((bs[off]'h0).zeroExtend 64) ||| (((bs[off + 1]'h1).zeroExtend 64) <<< 8)) |||
      (((bs[off + 2]'h2).zeroExtend 64) <<< 16)) |||
      (((bs[off + 3]'h3).zeroExtend 64) <<< 24)))
    loadPtr (Bgv + 40) (by decide)
  have e10e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at Bgv (Bgv + 40) bgvProg 10 (.MV .x10 .x5)
      Bgv40 (by rw [bgv_length]; decide) rfl bgv_bound) e10
  have e10F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) **
      (.x6 ↦ᵣ (((bs[off + 3]'h3).zeroExtend 64) <<< 24)) **
      bytesRegion regionBase bs) (by bgv_pcf) e10e
  -- [11] JALR
  have hexit : ((ret + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) = ret := by
    have hz : ret + signExtend12 (0 : BitVec 12) = ret := by
      show ret + (0 : Word) = ret; exact BitVec.add_zero ret
    rw [hz, hret]
  have e11 := jalr_x0_spec_gen_within .x1 ret (0 : BitVec 12) (Bgv + 44)
  rw [hexit] at e11
  have e11e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at Bgv (Bgv + 44) bgvProg 11 (.JALR .x0 .x1 (0 : BitVec 12))
      Bgv44 (by rw [bgv_length]; decide) rfl bgv_bound) e11
  have e11F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ ((((((bs[off]'h0).zeroExtend 64) |||
        (((bs[off + 1]'h1).zeroExtend 64) <<< 8)) |||
        (((bs[off + 2]'h2).zeroExtend 64) <<< 16)) |||
        (((bs[off + 3]'h3).zeroExtend 64) <<< 24)))) **
      (.x5 ↦ᵣ ((((((bs[off]'h0).zeroExtend 64) |||
        (((bs[off + 1]'h1).zeroExtend 64) <<< 8)) |||
        (((bs[off + 2]'h2).zeroExtend 64) <<< 16)) |||
        (((bs[off + 3]'h3).zeroExtend 64) <<< 24)))) **
      (.x6 ↦ᵣ (((bs[off + 3]'h3).zeroExtend 64) <<< 24)) **
      bytesRegion regionBase bs) (by bgv_pcf) e11e
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e0F e1F
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 e2F
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 e3F
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 e4F
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 e5F
  have c06 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c05 e6F
  have c07 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c06 e7F
  have c08 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c07 e8F
  have c09 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c08 e9F
  have c10 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c09 e10F
  have c11 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c10 e11F
  have hle := leU32_eq_bytes bs off h0 h1 h2 h3
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by rw [hle]; xperm_hyp hq) c11

#print axioms bytesRegion_lbu_imm_within
#print axioms leU32_eq_bytes
#print axioms bgvOffset_ambient_core

end EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
