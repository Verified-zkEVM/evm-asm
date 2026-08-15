/-
Copyright (c) 2025 zkSecurity. All rights reserved.
Released under Apache 2.0 license.
Authors: EvmAsm contributors

# SHA-256 final path: bit-length BE write (unrolled concrete steps)

Geometry @ B = GuestAddrs.zkvm_sha256:
- ADDI x5,x21,56 @ B+332 (idx 83)
- (SRLI/SB) pairs idx 84-97 offs 0..6; final SB idx 98 off 7
- Next la params @ B+396

Bit-length source: x20 = input_len << 3 (setup).
-/
import EvmAsm.Codegen.Proofs.HashBridgeSha256Rem
import EvmAsm.Codegen.Proofs.HashBridgeSha256Pad
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.zkvm_sha256
private abbrev sha256ProgL : List Instr := zkvmSha256_prog
private abbrev sha256Cr : CodeReq := CodeReq.ofProg B sha256ProgL

private theorem sha256ProgL_len : sha256ProgL.length = 121 := by
  simp only [sha256ProgL, zkvmSha256_prog, zkvmSha256_prog_of]
  decide

private theorem sha256ProgL_bound : 4 * sha256ProgL.length < 2 ^ 64 := by
  rw [sha256ProgL_len]; norm_num

private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < sha256ProgL.length)
    (hins : sha256ProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → sha256Cr a = some i :=
  fun a i h => CodeReq.ofProg_mem_at B A sha256ProgL k ins hA hk hins
    sha256ProgL_bound a i h

local macro "pcf" : tactic =>
  `(tactic| repeat' first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact bytesRegion_pcFree _ _
    | assumption)

/-! ## SB with nonzero imm into `bytesRegion` -/

theorem bytesRegion_sb_imm_within (rs1 rs2 : Reg) (regionBase v_rs1 v_data : Word)
    (base : Word) (bs : List (BitVec 8)) (i : Nat) (offset : BitVec 12)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hrs1 : v_rs1 + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SB rs1 rs2 offset))
      ((rs1 ↦ᵣ v_rs1) ** (rs2 ↦ᵣ v_data) ** bytesRegion regionBase bs)
      ((rs1 ↦ᵣ v_rs1) ** (rs2 ↦ᵣ v_data) **
       bytesRegion regionBase (bs.set i (v_data.truncate 8))) := by
  have hr : i % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hi_eq : 8 * (i / 8) + i % 8 = i := Nat.div_add_mod i 8
  obtain ⟨front, rest, hf, hrst, heq, heqset⟩ :=
    bytesRegion_dword_at_set regionBase bs (i / 8) (i % 8) (v_data.truncate 8) hr (by omega)
  rw [hi_eq] at heqset
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have haddr : v_rs1 + signExtend12 offset = regionBase + BitVec.ofNat 64 i := hrs1
  have halign' :
      alignToDword (v_rs1 + signExtend12 offset) = dwordAddr := by
    rw [haddr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have hvalid' :
      isValidByteAccess (v_rs1 + signExtend12 offset) = true := by
    rw [haddr]; exact hvalid
  have sb := generic_sb_spec_within rs1 rs2 v_rs1 v_data offset base
    dwordAddr wordVal halign' hvalid'
  have hbo : byteOffset (v_rs1 + signExtend12 offset) = i % 8 := by
    rw [haddr]; exact byteOffset_add_ofNat_of_aligned halign hover
  have hchunk_len : i % 8 < ((bs.drop (8 * (i / 8))).take 8).length := by
    rw [List.length_take, List.length_drop]; omega
  rw [hbo, hwv, packBytes_set _ (i % 8) (v_data.truncate 8) hr hchunk_len] at sb
  rw [heq, heqset]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hrst) sb)

/-! ## Pure bitlen BE post -/

def sha256BitlenBE (scratch : List (BitVec 8)) (bitLen : Word) : List (BitVec 8) :=
  scratch.set 56 ((bitLen >>> 56).truncate 8)
    |>.set 57 ((bitLen >>> 48).truncate 8)
    |>.set 58 ((bitLen >>> 40).truncate 8)
    |>.set 59 ((bitLen >>> 32).truncate 8)
    |>.set 60 ((bitLen >>> 24).truncate 8)
    |>.set 61 ((bitLen >>> 16).truncate 8)
    |>.set 62 ((bitLen >>> 8).truncate 8)
    |>.set 63 (bitLen.truncate 8)

theorem length_sha256BitlenBE (scratch : List (BitVec 8)) (bitLen : Word)
    (h : scratch.length = 64) :
    (sha256BitlenBE scratch bitLen).length = 64 := by
  simp only [sha256BitlenBE, List.length_set, h]

/-! ## ADDI x5, x21, 56 @ B+332 -/

private theorem se56 : signExtend12 (56 : BitVec 12) = (56 : Word) := by decide

theorem sha256Bitlen_addi56_spec (scratchBase : Word) (v5 : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (B + 332) (B + 336) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x5 ↦ᵣ v5) ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x5 ↦ᵣ (scratchBase + (56 : Word))) ** F) := by
  have hadd := addi_spec_gen_within .x5 .x21 v5 scratchBase (56 : BitVec 12)
    (B + 332) (by decide)
  simp only [se56] at hadd
  have haddC := cpsTripleWithin_extend_code
    (mem_at 83 (.ADDI .x5 .x21 (56 : BitVec 12)) (B + 332) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hadd
  rw [show (B + 332 : Word) + 4 = B + 336 from by decide] at haddC
  have hfr := cpsTripleWithin_frameR F hF haddC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hfr

/-! ## Byte 0: SRLI x6,x20,56; SB x5,x6,0 @ B+336 (idx 84-85) -/

private theorem se0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem word56 : (56 : Word) = BitVec.ofNat 64 56 := rfl

private theorem cursor56_off0 (scratchBase : Word) :
    scratchBase + (56 : Word) + signExtend12 (0 : BitVec 12) =
      scratchBase + BitVec.ofNat 64 56 := by
  rw [se0, word56]
  ac_rfl

/-- SRLI 56 + SB imm 0 writing scratch[56]. -/
theorem sha256Bitlen_byte0 (bitLen scratchBase : Word) (scratch : List (BitVec 8))
    (v6 : Word) (F : Assertion) (hF : F.pcFree)
    (hscratch : scratch.length = 64) (hbase : scratchBase.toNat % 8 = 0)
    (hover : scratchBase.toNat + 64 < 2 ^ 64)
    (hvalid : isValidByteAccess (scratchBase + BitVec.ofNat 64 56) = true) :
    cpsTripleWithin 2 (B + 336) (B + 344) sha256Cr
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ v6) ** bytesRegion scratchBase scratch ** F)
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 56)) **
        bytesRegion scratchBase
          (scratch.set 56 ((bitLen >>> 56).truncate 8)) ** F) := by
  -- SRLI x6, x20, 56 @ B+336
  have hsrli0 := srli_spec_gen_within .x6 .x20 v6 bitLen (56 : BitVec 6)
    (B + 336) (by decide)
  have hsh : ((56 : BitVec 6).toNat) = 56 := by decide
  simp only [hsh] at hsrli0
  have hsrliC := cpsTripleWithin_extend_code
    (mem_at 84 (.SRLI .x6 .x20 (56 : BitVec 6)) (B + 336) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hsrli0
  rw [show (B + 336 : Word) + 4 = B + 340 from by decide] at hsrliC
  have hsrliF0 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (scratchBase + (56 : Word))) ** bytesRegion scratchBase scratch ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _
        | exact hF) hsrliC
  have hsrliF : cpsTripleWithin 1 (B + 336) (B + 340) sha256Cr
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ v6) ** bytesRegion scratchBase scratch ** F)
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 56)) ** bytesRegion scratchBase scratch ** F) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hsrliF0
  -- SB x5, x6, 0 @ B+340
  have haddr := cursor56_off0 scratchBase
  have hsb0 := bytesRegion_sb_imm_within .x5 .x6 scratchBase
    (scratchBase + (56 : Word)) (bitLen >>> 56)
    (B + 340) scratch 56 (0 : BitVec 12)
    hbase (by omega) (by omega) haddr hvalid
  have hsbC := cpsTripleWithin_extend_code
    (mem_at 85 (.SB .x5 .x6 (0 : BitVec 12)) (B + 340) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hsb0
  rw [show (B + 340 : Word) + 4 = B + 344 from by decide] at hsbC
  have hsbF0 := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ bitLen) ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact hF) hsbC
  have hsbF : cpsTripleWithin 1 (B + 340) (B + 344) sha256Cr
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 56)) ** bytesRegion scratchBase scratch ** F)
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 56)) **
        bytesRegion scratchBase
          (scratch.set 56 ((bitLen >>> 56).truncate 8)) ** F) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hsbF0
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hsrliF hsbF


/-! ## Bitlen bytes 1..7 (concrete, mirror byte0) -/

private theorem se1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
private theorem se2 : signExtend12 (2 : BitVec 12) = (2 : Word) := by decide
private theorem se3 : signExtend12 (3 : BitVec 12) = (3 : Word) := by decide
private theorem se4 : signExtend12 (4 : BitVec 12) = (4 : Word) := by decide
private theorem se5 : signExtend12 (5 : BitVec 12) = (5 : Word) := by decide
private theorem se6 : signExtend12 (6 : BitVec 12) = (6 : Word) := by decide
private theorem se7 : signExtend12 (7 : BitVec 12) = (7 : Word) := by decide

private theorem ofNat_add_small (a b : Nat) (h : a + b < 256) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  have ha : a < 2 ^ 64 := Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h) (by decide)
  have hb : b < 2 ^ 64 := Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h) (by decide)
  have hab : a + b < 2 ^ 64 := Nat.lt_trans h (by decide)
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hab]

private theorem cursor56_off (i : Nat) (imm : BitVec 12)
    (himm : signExtend12 imm = BitVec.ofNat 64 i) (hi : i < 8) (scratchBase : Word) :
    scratchBase + (56 : Word) + signExtend12 imm =
      scratchBase + BitVec.ofNat 64 (56 + i) := by
  rw [himm, word56, BitVec.add_assoc, ofNat_add_small 56 i (by omega)]

/-- SRLI sh + SB imm writing scratch[56+i] at concrete PCs. -/
private theorem bitlen_pair_at (bitLen scratchBase : Word)
    (scratch : List (BitVec 8)) (v6 : Word) (F : Assertion) (hF : F.pcFree)
    (shN i : Nat) (sh : BitVec 6) (imm : BitVec 12)
    (pcSRLI pcSB pcExit : Word) (idxS idxB : Nat)
    (hscratch : scratch.length = 64) (hbase : scratchBase.toNat % 8 = 0)
    (hover : scratchBase.toNat + 64 < 2 ^ 64)
    (hi : i < 8)
    (hsh : sh.toNat = shN)
    (_himm : signExtend12 imm = BitVec.ofNat 64 i)
    (haddr :
      scratchBase + (56 : Word) + signExtend12 imm =
        scratchBase + BitVec.ofNat 64 (56 + i))
    (hvalid : isValidByteAccess (scratchBase + BitVec.ofNat 64 (56 + i)) = true)
    (hpc4 : pcSRLI + 4 = pcSB) (hpc8 : pcSB + 4 = pcExit)
    (hA_s : pcSRLI = B + BitVec.ofNat 64 (4 * idxS))
    (hA_b : pcSB = B + BitVec.ofNat 64 (4 * idxB))
    (hidxS : idxS < 121) (hidxB : idxB < 121)
    (hsrliRfl : sha256ProgL[idxS]'(by rw [sha256ProgL_len]; exact hidxS) =
      .SRLI .x6 .x20 sh)
    (hsbRfl : sha256ProgL[idxB]'(by rw [sha256ProgL_len]; exact hidxB) =
      .SB .x5 .x6 imm) :
    cpsTripleWithin 2 pcSRLI pcExit sha256Cr
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ v6) ** bytesRegion scratchBase scratch ** F)
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> shN)) **
        bytesRegion scratchBase
          (scratch.set (56 + i) ((bitLen >>> shN).truncate 8)) ** F) := by
  have hsrli0 := srli_spec_gen_within .x6 .x20 v6 bitLen sh pcSRLI (by decide)
  simp only [hsh] at hsrli0
  have hkS : idxS < sha256ProgL.length := by rw [sha256ProgL_len]; exact hidxS
  have hkB : idxB < sha256ProgL.length := by rw [sha256ProgL_len]; exact hidxB
  have hsrliC := cpsTripleWithin_extend_code
    (mem_at idxS (.SRLI .x6 .x20 sh) pcSRLI hA_s hkS hsrliRfl) hsrli0
  rw [hpc4] at hsrliC
  have hsrliF0 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (scratchBase + (56 : Word))) ** bytesRegion scratchBase scratch ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _
        | exact hF) hsrliC
  have hsrliF : cpsTripleWithin 1 pcSRLI pcSB sha256Cr
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ v6) ** bytesRegion scratchBase scratch ** F)
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> shN)) ** bytesRegion scratchBase scratch ** F) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hsrliF0
  have hi_len : 56 + i < scratch.length := by omega
  have hover_i : scratchBase.toNat + (56 + i) < 2 ^ 64 := by omega
  have hsb0 := bytesRegion_sb_imm_within .x5 .x6 scratchBase
    (scratchBase + (56 : Word)) (bitLen >>> shN)
    pcSB scratch (56 + i) imm
    hbase hi_len hover_i haddr hvalid
  have hsbC := cpsTripleWithin_extend_code
    (mem_at idxB (.SB .x5 .x6 imm) pcSB hA_b hkB hsbRfl) hsb0
  rw [hpc8] at hsbC
  have hsbF0 := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ bitLen) ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact hF) hsbC
  have hsbF : cpsTripleWithin 1 pcSB pcExit sha256Cr
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> shN)) ** bytesRegion scratchBase scratch ** F)
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> shN)) **
        bytesRegion scratchBase
          (scratch.set (56 + i) ((bitLen >>> shN).truncate 8)) ** F) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hsbF0
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hsrliF hsbF

/-- SB low byte; `v6` framed through (not written). -/
theorem sha256Bitlen_byte7 (bitLen scratchBase : Word) (scratch : List (BitVec 8))
    (v6 : Word) (F : Assertion) (hF : F.pcFree)
    (hscratch : scratch.length = 64) (hbase : scratchBase.toNat % 8 = 0)
    (hover : scratchBase.toNat + 64 < 2 ^ 64)
    (hvalid : isValidByteAccess (scratchBase + BitVec.ofNat 64 63) = true) :
    cpsTripleWithin 1 (B + 392) (B + 396) sha256Cr
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ v6) ** bytesRegion scratchBase scratch ** F)
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ v6) **
        bytesRegion scratchBase (scratch.set 63 (bitLen.truncate 8)) ** F) := by
  have haddr := cursor56_off 7 (7 : BitVec 12) se7 (by decide) scratchBase
  have hi_len : 63 < scratch.length := by omega
  have hover_i : scratchBase.toNat + 63 < 2 ^ 64 := by omega
  have hsb0 := bytesRegion_sb_imm_within .x5 .x20 scratchBase
    (scratchBase + (56 : Word)) bitLen
    (B + 392) scratch 63 (7 : BitVec 12)
    hbase hi_len hover_i haddr hvalid
  have hsbC := cpsTripleWithin_extend_code
    (mem_at 98 (.SB .x5 .x20 (7 : BitVec 12)) (B + 392) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hsb0
  rw [show (B + 392 : Word) + 4 = B + 396 from by decide] at hsbC
  -- Frame x6 through SB (SB focuses x5,x20,mem only)
  have hsbF0 := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** F)
    (by
      apply pcFree_sepConj
      · exact pcFree_regIs
      · exact hF) hsbC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hsbF0

/-- Full bitlen BE write fuel 16: ADDI + 7×(SRLI/SB) + SB low. -/
theorem sha256Bitlen_write_spec (bitLen scratchBase : Word)
    (scratch0 : List (BitVec 8)) (v5 v6 : Word)
    (F : Assertion) (hF : F.pcFree)
    (hscratch : scratch0.length = 64) (hbase : scratchBase.toNat % 8 = 0)
    (hover : scratchBase.toNat + 64 < 2 ^ 64)
    (hv56 : isValidByteAccess (scratchBase + BitVec.ofNat 64 56) = true)
    (hv57 : isValidByteAccess (scratchBase + BitVec.ofNat 64 57) = true)
    (hv58 : isValidByteAccess (scratchBase + BitVec.ofNat 64 58) = true)
    (hv59 : isValidByteAccess (scratchBase + BitVec.ofNat 64 59) = true)
    (hv60 : isValidByteAccess (scratchBase + BitVec.ofNat 64 60) = true)
    (hv61 : isValidByteAccess (scratchBase + BitVec.ofNat 64 61) = true)
    (hv62 : isValidByteAccess (scratchBase + BitVec.ofNat 64 62) = true)
    (hv63 : isValidByteAccess (scratchBase + BitVec.ofNat 64 63) = true) :
    cpsTripleWithin 16 (B + 332) (B + 396) sha256Cr
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        bytesRegion scratchBase scratch0 **
        ((.x21 ↦ᵣ scratchBase) ** F))
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 8)) **
        bytesRegion scratchBase (sha256BitlenBE scratch0 bitLen) **
        ((.x21 ↦ᵣ scratchBase) ** F)) := by
  let F21 : Assertion := (.x21 ↦ᵣ scratchBase) ** F
  have hF21 : F21.pcFree := by
    apply pcFree_sepConj
    · exact pcFree_regIs
    · exact hF
  have h0 := sha256Bitlen_addi56_spec scratchBase v5
    ((.x20 ↦ᵣ bitLen) ** (.x6 ↦ᵣ v6) ** bytesRegion scratchBase scratch0 ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _
        | exact hF)
  have h0' : cpsTripleWithin 1 (B + 332) (B + 336) sha256Cr
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        bytesRegion scratchBase scratch0 **
        ((.x21 ↦ᵣ scratchBase) ** F))
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ v6) ** bytesRegion scratchBase scratch0 **
        ((.x21 ↦ᵣ scratchBase) ** F)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) h0
  have b0 := sha256Bitlen_byte0 bitLen scratchBase scratch0 v6 F21 hF21
    hscratch hbase hover hv56
  -- Keep F21 packed (matches pair posts)
  have b0' : cpsTripleWithin 2 (B + 336) (B + 344) sha256Cr
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ v6) ** bytesRegion scratchBase scratch0 ** F21)
      ((.x20 ↦ᵣ bitLen) ** (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 56)) **
        bytesRegion scratchBase
          (scratch0.set 56 ((bitLen >>> 56).truncate 8)) ** F21) := b0
  -- Bytes 1..6 via bitlen_pair_at with decide PCs
  let sc0 := scratch0.set 56 ((bitLen >>> 56).truncate 8)
  have hsc0 : sc0.length = 64 := by simp [sc0, List.length_set, hscratch]
  have b1raw := bitlen_pair_at bitLen scratchBase sc0 (bitLen >>> 56) F21 hF21
    48 1 (48 : BitVec 6) (1 : BitVec 12)
    (B + 344) (B + 348) (B + 352) 86 87
    hsc0 hbase hover (by decide) (by decide) se1
    (cursor56_off 1 (1 : BitVec 12) se1 (by decide) scratchBase) hv57
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rfl) (by rfl)
  have b1 := b1raw
  let sc1 := sc0.set 57 ((bitLen >>> 48).truncate 8)
  have hsc1 : sc1.length = 64 := by simp [sc1, sc0, List.length_set, hscratch]
  have b2raw := bitlen_pair_at bitLen scratchBase sc1 (bitLen >>> 48) F21 hF21
    40 2 (40 : BitVec 6) (2 : BitVec 12)
    (B + 352) (B + 356) (B + 360) 88 89
    hsc1 hbase hover (by decide) (by decide) se2
    (cursor56_off 2 (2 : BitVec 12) se2 (by decide) scratchBase) hv58
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rfl) (by rfl)
  have b2 := b2raw
  let sc2 := sc1.set 58 ((bitLen >>> 40).truncate 8)
  have hsc2 : sc2.length = 64 := by simp [sc2, sc1, sc0, List.length_set, hscratch]
  have b3raw := bitlen_pair_at bitLen scratchBase sc2 (bitLen >>> 40) F21 hF21
    32 3 (32 : BitVec 6) (3 : BitVec 12)
    (B + 360) (B + 364) (B + 368) 90 91
    hsc2 hbase hover (by decide) (by decide) se3
    (cursor56_off 3 (3 : BitVec 12) se3 (by decide) scratchBase) hv59
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rfl) (by rfl)
  have b3 := b3raw
  let sc3 := sc2.set 59 ((bitLen >>> 32).truncate 8)
  have hsc3 : sc3.length = 64 := by
    simp [sc3, sc2, sc1, sc0, List.length_set, hscratch]
  have b4raw := bitlen_pair_at bitLen scratchBase sc3 (bitLen >>> 32) F21 hF21
    24 4 (24 : BitVec 6) (4 : BitVec 12)
    (B + 368) (B + 372) (B + 376) 92 93
    hsc3 hbase hover (by decide) (by decide) se4
    (cursor56_off 4 (4 : BitVec 12) se4 (by decide) scratchBase) hv60
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rfl) (by rfl)
  have b4 := b4raw
  let sc4 := sc3.set 60 ((bitLen >>> 24).truncate 8)
  have hsc4 : sc4.length = 64 := by
    simp [sc4, sc3, sc2, sc1, sc0, List.length_set, hscratch]
  have b5raw := bitlen_pair_at bitLen scratchBase sc4 (bitLen >>> 24) F21 hF21
    16 5 (16 : BitVec 6) (5 : BitVec 12)
    (B + 376) (B + 380) (B + 384) 94 95
    hsc4 hbase hover (by decide) (by decide) se5
    (cursor56_off 5 (5 : BitVec 12) se5 (by decide) scratchBase) hv61
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rfl) (by rfl)
  have b5 := b5raw
  let sc5 := sc4.set 61 ((bitLen >>> 16).truncate 8)
  have hsc5 : sc5.length = 64 := by
    simp [sc5, sc4, sc3, sc2, sc1, sc0, List.length_set, hscratch]
  have b6raw := bitlen_pair_at bitLen scratchBase sc5 (bitLen >>> 16) F21 hF21
    8 6 (8 : BitVec 6) (6 : BitVec 12)
    (B + 384) (B + 388) (B + 392) 96 97
    hsc5 hbase hover (by decide) (by decide) se6
    (cursor56_off 6 (6 : BitVec 12) se6 (by decide) scratchBase) hv62
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rfl) (by rfl)
  have b6 := b6raw
  let sc6 := sc5.set 62 ((bitLen >>> 8).truncate 8)
  have hsc6 : sc6.length = 64 := by
    simp [sc6, sc5, sc4, sc3, sc2, sc1, sc0, List.length_set, hscratch]
  have b7 := sha256Bitlen_byte7 bitLen scratchBase sc6 (bitLen >>> 8) F21 hF21
    hsc6 hbase hover hv63
  have hbe : sc6.set 63 (bitLen.truncate 8) = sha256BitlenBE scratch0 bitLen := by
    unfold sha256BitlenBE sc6 sc5 sc4 sc3 sc2 sc1 sc0
    rfl
  let c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) h0' b0'
  let c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c01 b1
  let c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c02 b2
  let c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c03 b3
  let c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c04 b4
  let c06 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c05 b5
  let c07 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c06 b6
  let c08 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c07 b7
  -- c08 fuel is nested sum = 16; post has sc6.set — rewrite to sha256BitlenBE
  exact cpsTripleWithin_mono_nSteps
    (by decide : ((((((((1 + 2) + 2) + 2) + 2) + 2) + 2) + 2) + 1) ≤ 16)
    (cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => by rw [hbe] at hq; exact hq) c08)

/-! ## Pad path ∘ bitlen write: B+196 → B+396 -/

/-- rem<56: `sha256PadPath_lt56_spec` ∘ `sha256Bitlen_write_spec`.
    Fuel `rem*7+33` (=17+16). B+196 → B+396 (final CSRS / squeeze entry). -/
theorem sha256PadThenBitlen_lt56
    (scratchBase inputCursor : Word) (bitLen : Word)
    (input scratch0 : List (BitVec 8))
    (rem : Nat)
    (v5 v6 v7 : Word)
    (F : Assertion) (hF : F.pcFree)
    (hsrcAlign : inputCursor.toNat % 8 = 0)
    (hdstAlign : scratchBase.toNat % 8 = 0)
    (hscratch : scratch0.length = 64)
    (hinp : rem ≤ input.length)
    (hrem : rem < 56)
    (hsrcOver : inputCursor.toNat + rem ≤ 2 ^ 64)
    (hover : scratchBase.toNat + 64 < 2 ^ 64)
    (hvalidS : ∀ i < rem, isValidByteAccess (inputCursor + BitVec.ofNat 64 i) = true)
    (hvalidD : ∀ i < rem, isValidByteAccess (scratchBase + BitVec.ofNat 64 i) = true)
    (hvalidPad : isValidByteAccess (scratchBase + BitVec.ofNat 64 rem) = true)
    (hv56 : isValidByteAccess (scratchBase + BitVec.ofNat 64 56) = true)
    (hv57 : isValidByteAccess (scratchBase + BitVec.ofNat 64 57) = true)
    (hv58 : isValidByteAccess (scratchBase + BitVec.ofNat 64 58) = true)
    (hv59 : isValidByteAccess (scratchBase + BitVec.ofNat 64 59) = true)
    (hv60 : isValidByteAccess (scratchBase + BitVec.ofNat 64 60) = true)
    (hv61 : isValidByteAccess (scratchBase + BitVec.ofNat 64 61) = true)
    (hv62 : isValidByteAccess (scratchBase + BitVec.ofNat 64 62) = true)
    (hv63 : isValidByteAccess (scratchBase + BitVec.ofNat 64 63) = true) :
    cpsTripleWithin (rem * 7 + 33) (B + 196) (B + 396) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase scratch0 **
        regOwn .x28 ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 8)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase
          (sha256BitlenBE (sha256PadScratch_lt56 input scratch0 rem) bitLen) **
        regOwn .x28 ** F) := by
  have hdstSpan : scratchBase.toNat + 64 ≤ 2 ^ 64 := by omega
  have hpad0 := sha256PadPath_lt56_spec scratchBase inputCursor input scratch0 rem
    v5 v6 v7 ((.x20 ↦ᵣ bitLen) ** F) (by pcf)
    hsrcAlign hdstAlign hscratch hinp hrem hsrcOver hdstSpan
    hvalidS hvalidD hvalidPad
  have hpad : cpsTripleWithin (rem * 7 + 17) (B + 196) (B + 332) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase scratch0 **
        regOwn .x28 ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ (56 : Word)) ** (.x6 ↦ᵣ (128 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadScratch_lt56 input scratch0 rem) **
        regOwn .x28 ** F) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hpad0
  have hmidLen := length_sha256PadScratch_lt56 input scratch0 rem hscratch
    (by omega) hinp
  have hbit0 := sha256Bitlen_write_spec bitLen scratchBase
    (sha256PadScratch_lt56 input scratch0 rem) (56 : Word) (128 : Word)
    ((.x9 ↦ᵣ inputCursor) ** (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
      (.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion inputCursor input ** regOwn .x28 ** F)
    (by pcf) hmidLen hdstAlign hover
    hv56 hv57 hv58 hv59 hv60 hv61 hv62 hv63
  have hbit : cpsTripleWithin 16 (B + 332) (B + 396) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ (56 : Word)) ** (.x6 ↦ᵣ (128 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadScratch_lt56 input scratch0 rem) **
        regOwn .x28 ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 8)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase
          (sha256BitlenBE (sha256PadScratch_lt56 input scratch0 rem) bitLen) **
        regOwn .x28 ** F) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hbit0
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hpad hbit
  exact cpsTripleWithin_mono_nSteps
    (by omega : (rem * 7 + 17) + 16 ≤ rem * 7 + 33) c

/-- rem≥56: `sha256PadPath_ge56_spec` ∘ `sha256Bitlen_write_spec`.
    Fuel `rem*7+44` (=28+16). B+196 → B+396 (final CSRS / squeeze entry). -/
theorem sha256PadThenBitlen_ge56
    (scratchBase inputCursor stateBase paramsBase : Word) (bitLen : Word)
    (input scratch0 state params : List (BitVec 8)) (payload : List Word)
    (rem : Nat)
    (v5 v6 v7 v10 : Word)
    (F : Assertion) (hF : F.pcFree)
    (hsrcAlign : inputCursor.toNat % 8 = 0)
    (hdstAlign : scratchBase.toNat % 8 = 0)
    (hscratch : scratch0.length = 64)
    (hstate : state.length = 32) (hpayload : payload.length = 4)
    (hinp : rem ≤ input.length)
    (hrem : 56 ≤ rem) (hrem64 : rem < 64)
    (hsrcOver : inputCursor.toNat + rem ≤ 2 ^ 64)
    (hover : scratchBase.toNat + 64 < 2 ^ 64)
    (hvalidS : ∀ i < rem, isValidByteAccess (inputCursor + BitVec.ofNat 64 i) = true)
    (hvalidD : ∀ i < rem, isValidByteAccess (scratchBase + BitVec.ofNat 64 i) = true)
    (hvalidPad : isValidByteAccess (scratchBase + BitVec.ofNat 64 rem) = true)
    (hv56 : isValidByteAccess (scratchBase + BitVec.ofNat 64 56) = true)
    (hv57 : isValidByteAccess (scratchBase + BitVec.ofNat 64 57) = true)
    (hv58 : isValidByteAccess (scratchBase + BitVec.ofNat 64 58) = true)
    (hv59 : isValidByteAccess (scratchBase + BitVec.ofNat 64 59) = true)
    (hv60 : isValidByteAccess (scratchBase + BitVec.ofNat 64 60) = true)
    (hv61 : isValidByteAccess (scratchBase + BitVec.ofNat 64 61) = true)
    (hv62 : isValidByteAccess (scratchBase + BitVec.ofNat 64 62) = true)
    (hv63 : isValidByteAccess (scratchBase + BitVec.ofNat 64 63) = true)
    (hsem : ∀ (R : Assertion) (s : MachineState),
      (((.x8 ↦ᵣ stateBase) **
        (.x10 ↦ᵣ (BitVec.ofNat 64 GuestAddrs.sha256_w_params)) **
        (.x21 ↦ᵣ scratchBase) ** bytesRegion paramsBase params **
        bytesRegion stateBase state **
        bytesRegion scratchBase (sha256PadScratch_lt56 input scratch0 rem)) ** R).holdsFor s →
      s.csrsValid 0x805 .x10 = true ∧
      s.csrsWrite 0x805 .x10 = (stateBase, payload)) :
    cpsTripleWithin (rem * 7 + 44) (B + 196) (B + 396) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) **
        (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase scratch0 **
        bytesRegion paramsBase params **
        bytesRegion stateBase state **
        regOwn .x28 ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) **
        (.x10 ↦ᵣ (BitVec.ofNat 64 GuestAddrs.sha256_w_params)) **
        (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 8)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase
          (sha256BitlenBE (sha256PadScratch_ge56 input scratch0 rem) bitLen) **
        bytesRegion paramsBase params **
        bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
        regOwn .x28 ** F) := by
  have hdstSpan : scratchBase.toNat + 64 ≤ 2 ^ 64 := by omega
  have hpad0 := sha256PadPath_ge56_spec scratchBase inputCursor stateBase paramsBase
    input scratch0 state params payload rem v5 v6 v7 v10
    ((.x20 ↦ᵣ bitLen) ** F) (by pcf)
    hsrcAlign hdstAlign hscratch hstate hpayload hinp hrem hrem64
    hsrcOver hdstSpan hvalidS hvalidD hvalidPad hsem
  have hpad : cpsTripleWithin (rem * 7 + 28) (B + 196) (B + 332) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) **
        (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase scratch0 **
        bytesRegion paramsBase params **
        bytesRegion stateBase state **
        regOwn .x28 ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) **
        (.x10 ↦ᵣ (BitVec.ofNat 64 GuestAddrs.sha256_w_params)) **
        (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ (56 : Word)) ** (.x6 ↦ᵣ (128 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadScratch_ge56 input scratch0 rem) **
        bytesRegion paramsBase params **
        bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
        regOwn .x28 ** F) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hpad0
  have hmidLen := length_sha256PadScratch_ge56 input scratch0 rem hscratch hrem64 hinp
  have hbit0 := sha256Bitlen_write_spec bitLen scratchBase
    (sha256PadScratch_ge56 input scratch0 rem) (56 : Word) (128 : Word)
    ((.x9 ↦ᵣ inputCursor) ** (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
      (.x8 ↦ᵣ stateBase) **
      (.x10 ↦ᵣ (BitVec.ofNat 64 GuestAddrs.sha256_w_params)) **
      (.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion inputCursor input **
      bytesRegion paramsBase params **
      bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
      regOwn .x28 ** F)
    (by pcf) hmidLen hdstAlign hover
    hv56 hv57 hv58 hv59 hv60 hv61 hv62 hv63
  have hbit : cpsTripleWithin 16 (B + 332) (B + 396) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) **
        (.x10 ↦ᵣ (BitVec.ofNat 64 GuestAddrs.sha256_w_params)) **
        (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ (56 : Word)) ** (.x6 ↦ᵣ (128 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase (sha256PadScratch_ge56 input scratch0 rem) **
        bytesRegion paramsBase params **
        bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
        regOwn .x28 ** F)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x8 ↦ᵣ stateBase) **
        (.x10 ↦ᵣ (BitVec.ofNat 64 GuestAddrs.sha256_w_params)) **
        (.x20 ↦ᵣ bitLen) **
        (.x5 ↦ᵣ (scratchBase + (56 : Word))) **
        (.x6 ↦ᵣ (bitLen >>> 8)) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion inputCursor input **
        bytesRegion scratchBase
          (sha256BitlenBE (sha256PadScratch_ge56 input scratch0 rem) bitLen) **
        bytesRegion paramsBase params **
        bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
        regOwn .x28 ** F) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hbit0
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hpad hbit
  exact cpsTripleWithin_mono_nSteps
    (by omega : (rem * 7 + 28) + 16 ≤ rem * 7 + 44) c

end EvmAsm.Codegen.Proofs
