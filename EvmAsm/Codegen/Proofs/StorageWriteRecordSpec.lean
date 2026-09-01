/-
  EvmAsm.Codegen.Proofs.StorageWriteRecordSpec

  **The `storage_write_record` machine triple — fail-closed arm (#11921).**

  WORK IN PROGRESS: segment A pilot.
-/

module

public import EvmAsm.Rv64.SyscallSpecs
public import EvmAsm.Rv64.ControlFlow
public import EvmAsm.Rv64.Tactics.RunBlock
public import EvmAsm.Evm64.CallingConvention
public import EvmAsm.Codegen.Programs.StorageWriteMap
meta import EvmAsm.Rv64.SyscallSpecs
meta import EvmAsm.Rv64.ControlFlow
meta import EvmAsm.Rv64.Tactics.RunBlock
meta import EvmAsm.Evm64.CallingConvention
meta import EvmAsm.Codegen.Programs.StorageWriteMap

@[expose] public section

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen

/-! ## Segment A — prologue, arena base, and the empty-map exit of the scan -/

/-- `storage_write_record` instructions 0..22 at a free `base`: the 13-slot
    prologue, `la t0, tx_storage_writes_count`, the four-instruction arena-base
    materialisation, `li t4, 0`, and the scan's `bgeu` — TAKEN, because the
    transaction's storage-write map is empty (`hcount`). -/
theorem storageWriteRecord_segA_body_spec
    (base sp ra a0 a6 countPtr v5 v6 v7 v13 v14 v15 v28 v29 v30 v31 : Word)
    (hla : base + (56 : Word) +
        (((laHi GuestAddrs.tx_storage_writes_count
            (GuestAddrs.storage_write_record + 56)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.tx_storage_writes_count
          (GuestAddrs.storage_write_record + 56)) = countPtr)
    (hbr : signExtend13 (brOff (GuestAddrs.storage_write_record + 284)
        (GuestAddrs.storage_write_record + 88)) = (196 : Word)) :
    cpsTripleWithin 23 base (base + (284 : Word))
      (CodeReq.ofProg base storageWriteRecord_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ a6) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       memOwn (sp - (112 : Word)) ** memOwn (sp - (104 : Word)) **
       memOwn (sp - (96 : Word)) ** memOwn (sp - (88 : Word)) **
       memOwn (sp - (80 : Word)) ** memOwn (sp - (72 : Word)) **
       memOwn (sp - (64 : Word)) ** memOwn (sp - (56 : Word)) **
       memOwn (sp - (48 : Word)) ** memOwn (sp - (40 : Word)) **
       memOwn (sp - (32 : Word)) ** memOwn (sp - (24 : Word)) **
       memOwn (sp - (16 : Word)) **
       (countPtr ↦ₘ (0 : Word)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp - (112 : Word))) **
       (.x10 ↦ᵣ a0) **
       (.x5 ↦ᵣ countPtr) ** (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ a6) **
       (.x28 ↦ᵣ (0xa2d57ec0 : Word)) ** (.x29 ↦ᵣ (0 : Word)) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       ((sp - (112 : Word)) ↦ₘ v5) ** ((sp - (104 : Word)) ↦ₘ v6) **
       ((sp - (96 : Word)) ↦ₘ v7) ** ((sp - (88 : Word)) ↦ₘ v28) **
       ((sp - (80 : Word)) ↦ₘ v29) ** ((sp - (72 : Word)) ↦ₘ v30) **
       ((sp - (64 : Word)) ↦ₘ v31) ** ((sp - (56 : Word)) ↦ₘ ra) **
       ((sp - (48 : Word)) ↦ₘ v13) ** ((sp - (40 : Word)) ↦ₘ v14) **
       ((sp - (32 : Word)) ↦ₘ v15) ** ((sp - (24 : Word)) ↦ₘ a6) **
       ((sp - (16 : Word)) ↦ₘ a0) **
       (countPtr ↦ₘ (0 : Word))) := by
  unfold storageWriteRecord_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 0: `addi sp, sp, -112`
  have P0 := addi_spec_gen_same_within .x2 sp (-112 : BitVec 12) base (by nofun)
  rw [show signExtend12 (-112 : BitVec 12) = (-112 : Word) from by decide,
      show sp + (-112 : Word) = sp - (112 : Word) from by bv_omega] at P0
  -- indices 1..13: spill t0,t1,t2,t3,t4,t5,t6,ra,a3,a4,a5,a6,a0
  have P1 := sd_spec_gen_own_within .x2 .x5 (sp - (112 : Word)) v5 (0 : BitVec 12)
    (base + (4 : Word))
  rw [show (sp - (112 : Word)) + signExtend12 (0 : BitVec 12) = sp - (112 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at P1
  have P2 := sd_spec_gen_own_within .x2 .x6 (sp - (112 : Word)) v6 (8 : BitVec 12)
    (base + (8 : Word))
  rw [show (sp - (112 : Word)) + signExtend12 (8 : BitVec 12) = sp - (104 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at P2
  have P3 := sd_spec_gen_own_within .x2 .x7 (sp - (112 : Word)) v7 (16 : BitVec 12)
    (base + (12 : Word))
  rw [show (sp - (112 : Word)) + signExtend12 (16 : BitVec 12) = sp - (96 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at P3
  have P4 := sd_spec_gen_own_within .x2 .x28 (sp - (112 : Word)) v28 (24 : BitVec 12)
    (base + (16 : Word))
  rw [show (sp - (112 : Word)) + signExtend12 (24 : BitVec 12) = sp - (88 : Word) from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]; bv_omega] at P4
  have P5 := sd_spec_gen_own_within .x2 .x29 (sp - (112 : Word)) v29 (32 : BitVec 12)
    (base + (20 : Word))
  rw [show (sp - (112 : Word)) + signExtend12 (32 : BitVec 12) = sp - (80 : Word) from by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]; bv_omega] at P5
  have P6 := sd_spec_gen_own_within .x2 .x30 (sp - (112 : Word)) v30 (40 : BitVec 12)
    (base + (24 : Word))
  rw [show (sp - (112 : Word)) + signExtend12 (40 : BitVec 12) = sp - (72 : Word) from by
    rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]; bv_omega] at P6
  have P7 := sd_spec_gen_own_within .x2 .x31 (sp - (112 : Word)) v31 (48 : BitVec 12)
    (base + (28 : Word))
  rw [show (sp - (112 : Word)) + signExtend12 (48 : BitVec 12) = sp - (64 : Word) from by
    rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide]; bv_omega] at P7
  have P8 := sd_spec_gen_own_within .x2 .x1 (sp - (112 : Word)) ra (56 : BitVec 12)
    (base + (32 : Word))
  rw [show (sp - (112 : Word)) + signExtend12 (56 : BitVec 12) = sp - (56 : Word) from by
    rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide]; bv_omega] at P8
  have P9 := sd_spec_gen_own_within .x2 .x13 (sp - (112 : Word)) v13 (64 : BitVec 12)
    (base + (36 : Word))
  rw [show (sp - (112 : Word)) + signExtend12 (64 : BitVec 12) = sp - (48 : Word) from by
    rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide]; bv_omega] at P9
  have P10 := sd_spec_gen_own_within .x2 .x14 (sp - (112 : Word)) v14 (72 : BitVec 12)
    (base + (40 : Word))
  rw [show (sp - (112 : Word)) + signExtend12 (72 : BitVec 12) = sp - (40 : Word) from by
    rw [show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide]; bv_omega] at P10
  have P11 := sd_spec_gen_own_within .x2 .x15 (sp - (112 : Word)) v15 (80 : BitVec 12)
    (base + (44 : Word))
  rw [show (sp - (112 : Word)) + signExtend12 (80 : BitVec 12) = sp - (32 : Word) from by
    rw [show signExtend12 (80 : BitVec 12) = (80 : Word) from by decide]; bv_omega] at P11
  have P12 := sd_spec_gen_own_within .x2 .x16 (sp - (112 : Word)) a6 (88 : BitVec 12)
    (base + (48 : Word))
  rw [show (sp - (112 : Word)) + signExtend12 (88 : BitVec 12) = sp - (24 : Word) from by
    rw [show signExtend12 (88 : BitVec 12) = (88 : Word) from by decide]; bv_omega] at P12
  have P13 := sd_spec_gen_own_within .x2 .x10 (sp - (112 : Word)) a0 (96 : BitVec 12)
    (base + (52 : Word))
  rw [show (sp - (112 : Word)) + signExtend12 (96 : BitVec 12) = sp - (16 : Word) from by
    rw [show signExtend12 (96 : BitVec 12) = (96 : Word) from by decide]; bv_omega] at P13
  -- indices 14, 15: `la t0, tx_storage_writes_count`
  have P14 := auipc_spec_gen_within .x5 v5
    (laHi GuestAddrs.tx_storage_writes_count (GuestAddrs.storage_write_record + 56))
    (base + (56 : Word)) (by nofun)
  have P15 := addi_spec_gen_same_within .x5
    ((base + (56 : Word)) +
      (((laHi GuestAddrs.tx_storage_writes_count
          (GuestAddrs.storage_write_record + 56)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.tx_storage_writes_count (GuestAddrs.storage_write_record + 56))
    (base + (60 : Word)) (by nofun)
  rw [hla] at P15
  -- index 16: `ld t1, 0(t0)` — the transaction-level entry count
  have P16 := ld_spec_gen_within .x6 .x5 countPtr v6 (0 : Word) (0 : BitVec 12)
    (base + (64 : Word)) (by nofun)
  rw [show countPtr + signExtend12 (0 : BitVec 12) = countPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at P16
  -- indices 17..20: materialise the TX_STORAGE_WRITES_AREA base into t3
  have P17 := lui_spec_gen_within .x28 v28 (20 : BitVec 20) (base + (68 : Word)) (by nofun)
  rw [show (((20 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64) = (81920 : Word) from by
    decide] at P17
  have P18 := addiw_spec_gen_same_within .x28 (81920 : Word) (1451 : BitVec 12)
    (base + (72 : Word)) (by nofun)
  rw [show ((((81920 : Word).truncate 32 + (signExtend12 (1451 : BitVec 12)).truncate 32 :
      BitVec 32)).signExtend 64) = (83371 : Word) from by decide] at P18
  have P19 := slli_spec_gen_same_within .x28 (83371 : Word) (15 : BitVec 6)
    (base + (76 : Word)) (by nofun)
  rw [show ((83371 : Word) <<< (15 : BitVec 6).toNat) = (2731900928 : Word) from by
    decide] at P19
  have P20 := addi_spec_gen_same_within .x28 (2731900928 : Word) (-320 : BitVec 12)
    (base + (80 : Word)) (by nofun)
  rw [show (2731900928 : Word) + signExtend12 (-320 : BitVec 12) = (0xa2d57ec0 : Word) from by
    decide] at P20
  -- index 21: `li t4, 0` — the scan cursor
  have P21 := li_spec_gen_within .x29 v29 (0 : Word) (base + (84 : Word)) (by nofun)
  -- index 22: `bgeu t4, t1, .Lswr_append` — TAKEN, the map is empty
  have PB := bgeu_spec_gen_within .x29 .x6
    (brOff (GuestAddrs.storage_write_record + 284) (GuestAddrs.storage_write_record + 88))
    (0 : Word) (0 : Word) (base + (88 : Word))
  rw [hbr, show base + (88 : Word) + (196 : Word) = base + (284 : Word) from by bv_omega]
    at PB
  have P22 : cpsTripleWithin 1 (base + (88 : Word)) (base + (284 : Word))
      (CodeReq.singleton (base + (88 : Word)) (.BGEU .x29 .x6
        (brOff (GuestAddrs.storage_write_record + 284)
          (GuestAddrs.storage_write_record + 88))))
      ((.x29 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)))
      ((.x29 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word))) :=
    cpsBranchWithin_takenStripPure2 PB (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact absurd h_pure.2 (by decide))
  runBlock P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20
    P21 P22

end EvmAsm.Codegen.Proofs
