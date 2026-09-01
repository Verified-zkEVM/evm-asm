/-
  EvmAsm.Codegen.Proofs.StorageWriteRecordSpec

  **The `storage_write_record` machine triple — fail-closed arm (#11921).**

  WORK IN PROGRESS: segment A pilot.
-/

module

public import EvmAsm.Rv64.SyscallSpecs
public import EvmAsm.Rv64.ControlFlow
public import EvmAsm.Rv64.Tactics.RunBlock
public import EvmAsm.Rv64.WP.Call
public import EvmAsm.Evm64.CallingConvention
public import EvmAsm.Codegen.Programs.StorageWriteMap
meta import EvmAsm.Rv64.SyscallSpecs
meta import EvmAsm.Rv64.ControlFlow
meta import EvmAsm.Rv64.Tactics.RunBlock
meta import EvmAsm.Rv64.WP.Call
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

/-! ## Segment B — the arena-capacity gate and the undo-journal call arguments -/

/-- `storage_write_record` instructions 71..76 (`base + 284 .. base + 304`):
    materialise the arena capacity 5588 into `t2`, take the capacity `bgeu`
    NOT taken (the map is empty, so `0 < 5588`), and load the three
    `storage_writes_undo_push` arguments — `a3 = 0` (the append index),
    `a4 = 1` (wasAbsent), `a5 = 0` (no payload). -/
theorem storageWriteRecord_segB_body_spec
    (base v7 v13 v14 v15 : Word) :
    cpsTripleWithin 6 (base + (284 : Word)) (base + (308 : Word))
      (CodeReq.ofProg base storageWriteRecord_prog)
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15))
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (5588 : Word)) **
       (.x13 ↦ᵣ (0 : Word)) ** (.x14 ↦ᵣ (1 : Word)) ** (.x15 ↦ᵣ (0 : Word))) := by
  unfold storageWriteRecord_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 71: `lui t2, 1`
  have Q0 := lui_spec_gen_within .x7 v7 (1 : BitVec 20) (base + (284 : Word)) (by nofun)
  rw [show (((1 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64) = (4096 : Word) from by
    decide] at Q0
  -- index 72: `addiw t2, t2, 1492` — the transaction arena capacity, 5588
  have Q1 := addiw_spec_gen_same_within .x7 (4096 : Word) (1492 : BitVec 12)
    (base + (288 : Word)) (by nofun)
  rw [show ((((4096 : Word).truncate 32 + (signExtend12 (1492 : BitVec 12)).truncate 32 :
      BitVec 32)).signExtend 64) = (5588 : Word) from by decide] at Q1
  -- index 73: `bgeu t1, t2, .Lswr_overflow` — NOT taken, `0 < 5588`
  have QB := bgeu_spec_gen_within .x6 .x7
    (brOff (GuestAddrs.storage_write_record + 492) (GuestAddrs.storage_write_record + 292))
    (0 : Word) (5588 : Word) (base + (292 : Word))
  have Q2 : cpsTripleWithin 1 (base + (292 : Word)) (base + (292 : Word) + 4)
      (CodeReq.singleton (base + (292 : Word)) (.BGEU .x6 .x7
        (brOff (GuestAddrs.storage_write_record + 492)
          (GuestAddrs.storage_write_record + 292))))
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (5588 : Word)))
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (5588 : Word))) :=
    cpsBranchWithin_ntakenStripPure2 QB (fun hp hQt => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQt
      exact absurd h_pure.2 (by decide))
  rw [show base + (292 : Word) + 4 = base + (296 : Word) from by bv_omega] at Q2
  -- index 74: `mv a3, t1` — the append index (0, the map is empty)
  have Q3 := mv_spec_gen_within .x13 .x6 (0 : Word) v13 (base + (296 : Word)) (by nofun)
  -- index 75: `li a4, 1` — wasAbsent
  have Q4 := li_spec_gen_within .x14 v14 (1 : Word) (base + (300 : Word)) (by nofun)
  -- index 76: `li a5, 0` — no payload on the append path
  have Q5 := li_spec_gen_within .x15 v15 (0 : Word) (base + (304 : Word)) (by nofun)
  runBlock Q0 Q1 Q2 Q3 Q4 Q5

/-! ## The callee — `storage_writes_undo_push`, journal-full arm -/

/-- `storage_writes_undo_push` at a free `ubase`, on the **journal-full** arm:
    the sole `bgeu` at index 13 is TAKEN (`hfull`), so the routine latches both
    sticky overflow flags, returns `a0 = 1`, and — crucially — stores NOTHING
    into the journal and does not advance `storage_writes_undo_count`.

    This is the fail-closed contract `RegionMap.lean:164` states in prose. The
    caller must reject on `a0 ≠ 0` rather than mutate without a rollback record;
    `storageWriteRecord_segC_body_spec` is the arm that does. -/
theorem storageWritesUndoPush_full_body_spec
    (ubase sp2 retA undoPtr txOvfPtr blkOvfPtr undoCount ovfTx ovfBlk
      w5 w6 w7 w10 w28 w29 w30 w31 : Word)
    (hlaCount : ubase + (32 : Word) +
        (((laHi GuestAddrs.storage_writes_undo_count
            (GuestAddrs.storage_writes_undo_push + 32)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.storage_writes_undo_count
          (GuestAddrs.storage_writes_undo_push + 32)) = undoPtr)
    (hlaTx : ubase + (192 : Word) +
        (((laHi GuestAddrs.tx_storage_writes_overflow
            (GuestAddrs.storage_writes_undo_push + 192)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.tx_storage_writes_overflow
          (GuestAddrs.storage_writes_undo_push + 192)) = txOvfPtr)
    (hlaBlk : ubase + (204 : Word) +
        (((laHi GuestAddrs.storage_writes_overflow
            (GuestAddrs.storage_writes_undo_push + 204)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.storage_writes_overflow
          (GuestAddrs.storage_writes_undo_push + 204)) = blkOvfPtr)
    (hbr : signExtend13 (brOff (GuestAddrs.storage_writes_undo_push + 188)
        (GuestAddrs.storage_writes_undo_push + 52)) = (136 : Word))
    (hfull : ¬ BitVec.ult undoCount (167652 : Word)) :
    cpsTripleWithin 30 ubase (retA &&& ~~~(1 : Word))
      (CodeReq.ofProg ubase storageWritesUndoPush_prog)
      ((.x1 ↦ᵣ retA) ** (.x2 ↦ᵣ sp2) ** (.x10 ↦ᵣ w10) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) **
       (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31) **
       memOwn (sp2 - (64 : Word)) ** memOwn (sp2 - (56 : Word)) **
       memOwn (sp2 - (48 : Word)) ** memOwn (sp2 - (40 : Word)) **
       memOwn (sp2 - (32 : Word)) ** memOwn (sp2 - (24 : Word)) **
       memOwn (sp2 - (16 : Word)) **
       (undoPtr ↦ₘ undoCount) ** (txOvfPtr ↦ₘ ovfTx) ** (blkOvfPtr ↦ₘ ovfBlk))
      ((.x1 ↦ᵣ retA) ** (.x2 ↦ᵣ sp2) ** (.x10 ↦ᵣ (1 : Word)) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) **
       (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31) **
       ((sp2 - (64 : Word)) ↦ₘ w5) ** ((sp2 - (56 : Word)) ↦ₘ w6) **
       ((sp2 - (48 : Word)) ↦ₘ w7) ** ((sp2 - (40 : Word)) ↦ₘ w28) **
       ((sp2 - (32 : Word)) ↦ₘ w29) ** ((sp2 - (24 : Word)) ↦ₘ w30) **
       ((sp2 - (16 : Word)) ↦ₘ w31) **
       (undoPtr ↦ₘ undoCount) ** (txOvfPtr ↦ₘ (1 : Word)) **
       (blkOvfPtr ↦ₘ (1 : Word))) := by
  unfold storageWritesUndoPush_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 0: `addi sp, sp, -64`
  have U0 := addi_spec_gen_same_within .x2 sp2 (-64 : BitVec 12) ubase (by nofun)
  rw [show signExtend12 (-64 : BitVec 12) = (-64 : Word) from by decide,
      show sp2 + (-64 : Word) = sp2 - (64 : Word) from by bv_omega] at U0
  -- indices 1..7: spill t0..t6
  have U1 := sd_spec_gen_own_within .x2 .x5 (sp2 - (64 : Word)) w5 (0 : BitVec 12)
    (ubase + (4 : Word))
  rw [show (sp2 - (64 : Word)) + signExtend12 (0 : BitVec 12) = sp2 - (64 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at U1
  have U2 := sd_spec_gen_own_within .x2 .x6 (sp2 - (64 : Word)) w6 (8 : BitVec 12)
    (ubase + (8 : Word))
  rw [show (sp2 - (64 : Word)) + signExtend12 (8 : BitVec 12) = sp2 - (56 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at U2
  have U3 := sd_spec_gen_own_within .x2 .x7 (sp2 - (64 : Word)) w7 (16 : BitVec 12)
    (ubase + (12 : Word))
  rw [show (sp2 - (64 : Word)) + signExtend12 (16 : BitVec 12) = sp2 - (48 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at U3
  have U4 := sd_spec_gen_own_within .x2 .x28 (sp2 - (64 : Word)) w28 (24 : BitVec 12)
    (ubase + (16 : Word))
  rw [show (sp2 - (64 : Word)) + signExtend12 (24 : BitVec 12) = sp2 - (40 : Word) from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]; bv_omega] at U4
  have U5 := sd_spec_gen_own_within .x2 .x29 (sp2 - (64 : Word)) w29 (32 : BitVec 12)
    (ubase + (20 : Word))
  rw [show (sp2 - (64 : Word)) + signExtend12 (32 : BitVec 12) = sp2 - (32 : Word) from by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]; bv_omega] at U5
  have U6 := sd_spec_gen_own_within .x2 .x30 (sp2 - (64 : Word)) w30 (40 : BitVec 12)
    (ubase + (24 : Word))
  rw [show (sp2 - (64 : Word)) + signExtend12 (40 : BitVec 12) = sp2 - (24 : Word) from by
    rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]; bv_omega] at U6
  have U7 := sd_spec_gen_own_within .x2 .x31 (sp2 - (64 : Word)) w31 (48 : BitVec 12)
    (ubase + (28 : Word))
  rw [show (sp2 - (64 : Word)) + signExtend12 (48 : BitVec 12) = sp2 - (16 : Word) from by
    rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide]; bv_omega] at U7
  -- indices 8, 9: `la t0, storage_writes_undo_count`
  have U8 := auipc_spec_gen_within .x5 w5
    (laHi GuestAddrs.storage_writes_undo_count (GuestAddrs.storage_writes_undo_push + 32))
    (ubase + (32 : Word)) (by nofun)
  have U9 := addi_spec_gen_same_within .x5
    ((ubase + (32 : Word)) +
      (((laHi GuestAddrs.storage_writes_undo_count
          (GuestAddrs.storage_writes_undo_push + 32)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.storage_writes_undo_count (GuestAddrs.storage_writes_undo_push + 32))
    (ubase + (36 : Word)) (by nofun)
  rw [hlaCount] at U9
  -- index 10: `ld t1, 0(t0)` — the journal cursor
  have U10 := ld_spec_gen_within .x6 .x5 undoPtr w6 undoCount (0 : BitVec 12)
    (ubase + (40 : Word)) (by nofun)
  rw [show undoPtr + signExtend12 (0 : BitVec 12) = undoPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at U10
  -- indices 11, 12: the journal capacity, 167652
  have U11 := lui_spec_gen_within .x7 w7 (41 : BitVec 20) (ubase + (44 : Word)) (by nofun)
  rw [show (((41 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64) = (167936 : Word) from by
    decide] at U11
  have U12 := addiw_spec_gen_same_within .x7 (167936 : Word) (-284 : BitVec 12)
    (ubase + (48 : Word)) (by nofun)
  rw [show ((((167936 : Word).truncate 32 + (signExtend12 (-284 : BitVec 12)).truncate 32 :
      BitVec 32)).signExtend 64) = (167652 : Word) from by decide] at U12
  -- index 13: `bgeu t1, t2, .Lswup_full` — TAKEN, the journal is full
  have UB := bgeu_spec_gen_within .x6 .x7
    (brOff (GuestAddrs.storage_writes_undo_push + 188)
      (GuestAddrs.storage_writes_undo_push + 52))
    undoCount (167652 : Word) (ubase + (52 : Word))
  rw [hbr, show ubase + (52 : Word) + (136 : Word) = ubase + (188 : Word) from by bv_omega]
    at UB
  have U13 : cpsTripleWithin 1 (ubase + (52 : Word)) (ubase + (188 : Word))
      (CodeReq.singleton (ubase + (52 : Word)) (.BGEU .x6 .x7
        (brOff (GuestAddrs.storage_writes_undo_push + 188)
          (GuestAddrs.storage_writes_undo_push + 52))))
      ((.x6 ↦ᵣ undoCount) ** (.x7 ↦ᵣ (167652 : Word)))
      ((.x6 ↦ᵣ undoCount) ** (.x7 ↦ᵣ (167652 : Word))) :=
    cpsBranchWithin_takenStripPure2 UB (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact hfull h_pure.2)
  -- index 47: `li a0, 1` — the failure return code
  have U14 := li_spec_gen_within .x10 w10 (1 : Word) (ubase + (188 : Word)) (by nofun)
  -- indices 48, 49: `la t3, tx_storage_writes_overflow`
  have U15 := auipc_spec_gen_within .x28 w28
    (laHi GuestAddrs.tx_storage_writes_overflow (GuestAddrs.storage_writes_undo_push + 192))
    (ubase + (192 : Word)) (by nofun)
  have U16 := addi_spec_gen_same_within .x28
    ((ubase + (192 : Word)) +
      (((laHi GuestAddrs.tx_storage_writes_overflow
          (GuestAddrs.storage_writes_undo_push + 192)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.tx_storage_writes_overflow (GuestAddrs.storage_writes_undo_push + 192))
    (ubase + (196 : Word)) (by nofun)
  rw [hlaTx] at U16
  -- index 50: latch the transaction-level sticky flag
  have U17 := sd_spec_gen_within .x28 .x10 txOvfPtr (1 : Word) ovfTx (0 : BitVec 12)
    (ubase + (200 : Word))
  rw [show txOvfPtr + signExtend12 (0 : BitVec 12) = txOvfPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at U17
  -- indices 51, 52: `la t3, storage_writes_overflow`
  have U18 := auipc_spec_gen_within .x28 txOvfPtr
    (laHi GuestAddrs.storage_writes_overflow (GuestAddrs.storage_writes_undo_push + 204))
    (ubase + (204 : Word)) (by nofun)
  have U19 := addi_spec_gen_same_within .x28
    ((ubase + (204 : Word)) +
      (((laHi GuestAddrs.storage_writes_overflow
          (GuestAddrs.storage_writes_undo_push + 204)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.storage_writes_overflow (GuestAddrs.storage_writes_undo_push + 204))
    (ubase + (208 : Word)) (by nofun)
  rw [hlaBlk] at U19
  -- index 53: latch the block-level sticky flag
  have U20 := sd_spec_gen_within .x28 .x10 blkOvfPtr (1 : Word) ovfBlk (0 : BitVec 12)
    (ubase + (212 : Word))
  rw [show blkOvfPtr + signExtend12 (0 : BitVec 12) = blkOvfPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at U20
  -- indices 54..60: reload t0..t6
  have U21 := ld_spec_gen_within .x5 .x2 (sp2 - (64 : Word)) undoPtr w5 (0 : BitVec 12)
    (ubase + (216 : Word)) (by nofun)
  rw [show (sp2 - (64 : Word)) + signExtend12 (0 : BitVec 12) = sp2 - (64 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at U21
  have U22 := ld_spec_gen_within .x6 .x2 (sp2 - (64 : Word)) undoCount w6 (8 : BitVec 12)
    (ubase + (220 : Word)) (by nofun)
  rw [show (sp2 - (64 : Word)) + signExtend12 (8 : BitVec 12) = sp2 - (56 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at U22
  have U23 := ld_spec_gen_within .x7 .x2 (sp2 - (64 : Word)) (167652 : Word) w7
    (16 : BitVec 12) (ubase + (224 : Word)) (by nofun)
  rw [show (sp2 - (64 : Word)) + signExtend12 (16 : BitVec 12) = sp2 - (48 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at U23
  have U24 := ld_spec_gen_within .x28 .x2 (sp2 - (64 : Word)) blkOvfPtr w28 (24 : BitVec 12)
    (ubase + (228 : Word)) (by nofun)
  rw [show (sp2 - (64 : Word)) + signExtend12 (24 : BitVec 12) = sp2 - (40 : Word) from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]; bv_omega] at U24
  have U25 := ld_spec_gen_within .x29 .x2 (sp2 - (64 : Word)) w29 w29 (32 : BitVec 12)
    (ubase + (232 : Word)) (by nofun)
  rw [show (sp2 - (64 : Word)) + signExtend12 (32 : BitVec 12) = sp2 - (32 : Word) from by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]; bv_omega] at U25
  have U26 := ld_spec_gen_within .x30 .x2 (sp2 - (64 : Word)) w30 w30 (40 : BitVec 12)
    (ubase + (236 : Word)) (by nofun)
  rw [show (sp2 - (64 : Word)) + signExtend12 (40 : BitVec 12) = sp2 - (24 : Word) from by
    rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]; bv_omega] at U26
  have U27 := ld_spec_gen_within .x31 .x2 (sp2 - (64 : Word)) w31 w31 (48 : BitVec 12)
    (ubase + (240 : Word)) (by nofun)
  rw [show (sp2 - (64 : Word)) + signExtend12 (48 : BitVec 12) = sp2 - (16 : Word) from by
    rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide]; bv_omega] at U27
  -- index 61: `addi sp, sp, 64`
  have U28 := addi_spec_gen_same_within .x2 (sp2 - (64 : Word)) (64 : BitVec 12)
    (ubase + (244 : Word)) (by nofun)
  rw [show (sp2 - (64 : Word)) + signExtend12 (64 : BitVec 12) = sp2 from by
    rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide]; bv_omega] at U28
  -- index 62: `ret`
  have U29 := EvmAsm.Evm64.ret_spec_within' (ubase + (248 : Word)) retA
  runBlock U0 U1 U2 U3 U4 U5 U6 U7 U8 U9 U10 U11 U12 U13 U14 U15 U16 U17 U18 U19 U20
    U21 U22 U23 U24 U25 U26 U27 U28 U29

end EvmAsm.Codegen.Proofs
