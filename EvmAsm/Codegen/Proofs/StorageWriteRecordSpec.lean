/-
  EvmAsm.Codegen.Proofs.StorageWriteRecordSpec

  **The `storage_write_record` machine triple — fail-closed arm (#11921).**

  `storage_write_record` (`Codegen/Programs/StorageWriteMap.lean`,
  `storageWriteRecord_prog`, 145 instructions at
  `GuestAddrs.storage_write_record`, image entry
  `GuestImageEntries.lean:395`) is the guest's `set_storage`
  (`state_tracker.py:489`): scan `TX_STORAGE_WRITES_AREA` for the
  `(address, slot)` pair, overwrite the value on a hit, append a fresh
  128-byte row with a captured pre-transaction baseline on a miss, drop
  the write and latch the sticky overflow flags when either the arena or
  the undo journal is full.

  ## ⭐ Why the `CodeReq` is a union, and why that is forced

  `Codegen.Proofs.AccountReadRecordSpec` could state its arm over
  `CodeReq.ofProg (GuestAddrs.account_read_record) accountReadRecord_prog`
  alone, because that routine's suppression gate reaches the epilogue
  without leaving its own bytes.  **`storage_write_record` has no such
  arm.** Every terminating path either

  * runs the scan at index 22 for `tx_storage_writes_count` iterations, or
  * reaches a `jal ra, storage_writes_undo_push` (index 65 on the hit arm,
    index 77 on the append arm),

  and the only path that avoids the call — `.Lswr_overflow` at index 123 —
  is reachable only when the count has already driven 5588 scan
  iterations.  So a whole-routine triple over this Program must range over
  the callee's bytes too, and `swrCR` is that union: the routine's own 145
  instructions at their linked `GuestAddrs` entry, plus
  `storageWritesUndoPush_prog` at its own.  (This is the `pdCr`/`bansfCR`
  shape; `scripts/proof-frontier.py`'s classifier resolves the union body
  and still sees `GuestAddrs.storage_write_record` as the anchor.)

  ## What this module proves

  `storageWriteRecordFailClosedFlat_spec`, an 83-step whole-routine triple
  entry → `ret` under two named gates:

  * the transaction's storage-write map is empty
    (`tx_storage_writes_count ↦ₘ 0`) — this is a transaction's FIRST
    storage write, so the scan's `bgeu` at index 22 is taken with zero
    iterations and no loop invariant is needed;
  * the undo journal is full (`hfull`), so `storage_writes_undo_push`
    refuses.

  Under those, the routine is **fail-closed**: both sticky flags latch to
  1, `tx_storage_writes_count` stays 0, `storage_writes_undo_count` is not
  advanced, and `sp` plus all thirteen prologue-saved registers come back
  intact.  Because `cpsTripleWithin` universally quantifies over a `pcFree`
  frame, the triple ALSO says — for free, since neither is named in the
  pre or the post — that nothing is written to `TX_STORAGE_WRITES_AREA` or
  to the undo-journal arena.  That is the spec-side content of the
  "⭐ **FAILS CLOSED** — latches overflow and rejects" claim that
  `Codegen/RegionMap.lean:164` currently makes only in prose.

  `storageWritesUndoPush_full_body_spec` is the callee's own whole-routine
  contract on the same arm — the first triple of any shape for
  `storage_writes_undo_push`, which the frontier census lists as `absent`.

  ## ⚠️ What is deliberately NOT proven

  The hit arm, the append arm's sixteen-dword row write, and the
  5588-iteration `.Lswr_overflow` arm.  Those need the scan's loop
  invariant (`measureTwoExitLoop_spec`, measure
  `tx_storage_writes_count − t4`) and the `storageWritesMapIs` vocabulary
  (`Stateless/State/WriteMapAssertions.lean:248`), and they are where the
  machine will be tied to the already-proven model
  `storageWriteUpsert` (`Stateless/State/StorageWriteUpsert.lean:142`,
  #12016).  The registry row is therefore `.conditional` with both gates
  named.

  ## Mechanics

  Same two pilot rules as `AccountReadRecordSpec`: present the code
  requirement as the `singleton`-union chain (`unfold` + `CodeReq.ofProg_cons`)
  before `runBlock`, and write every offset `(k : Word)`.  Segments compose
  with `seqFrame`; the call site uses `WP.cpsCallWithin` behind the
  `swr_callSite77` adapter, exactly as `bansf_callSite22_walk_init` does.
  The file is not `module`-ised because `CodeReq.ofProg_mem_at` and
  `CodeReq.Disjoint.ofProg_ranges` live in non-`module` `Rv64/SAsm` files —
  the same reason `BalAccountNonstorageFinalsSpec.lean` is not.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only
  (audited by the `#print axioms` at the end of this file).
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.WP.Call
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Codegen.Programs.StorageWriteMap

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

/-! ## Segment C — the caller's reject arm and the epilogue -/

/-- `storage_write_record` instruction 78 and 123..144 (`base + 312`, then
    `base + 492 .. base + 576`): the caller sees `a0 ≠ 0` from
    `storage_writes_undo_push`, takes the `bne` to `.Lswr_overflow`, latches
    both sticky flags a second time, restores all thirteen saved registers and
    `sp`, and returns.

    Nothing is written to `TX_STORAGE_WRITES_AREA` and
    `tx_storage_writes_count` is never even addressed on this arm — both facts
    come for free from the universally quantified `pcFree` frame, since neither
    appears in the pre or the post. -/
theorem storageWriteRecord_segC_body_spec
    (base sp ra a0 a6 link retVal txOvfPtr blkOvfPtr ovfTx ovfBlk
      v5 v6 v7 v13 v14 v15 v28 v29 v30 v31 u5 u6 u7 u13 u14 u15 u16 u28 u29 u30 u31 : Word)
    (hbr : signExtend13 (brOff (GuestAddrs.storage_write_record + 492)
        (GuestAddrs.storage_write_record + 312)) = (180 : Word))
    (hlaTx : base + (492 : Word) +
        (((laHi GuestAddrs.tx_storage_writes_overflow
            (GuestAddrs.storage_write_record + 492)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.tx_storage_writes_overflow
          (GuestAddrs.storage_write_record + 492)) = txOvfPtr)
    (hlaBlk : base + (508 : Word) +
        (((laHi GuestAddrs.storage_writes_overflow
            (GuestAddrs.storage_write_record + 508)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.storage_writes_overflow
          (GuestAddrs.storage_write_record + 508)) = blkOvfPtr)
    (hfail : retVal ≠ (0 : Word)) :
    cpsTripleWithin 23 (base + (312 : Word)) (ra &&& ~~~(1 : Word))
      (CodeReq.ofProg base storageWriteRecord_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ link) ** (.x2 ↦ᵣ (sp - (112 : Word))) **
       (.x10 ↦ᵣ retVal) **
       (.x5 ↦ᵣ u5) ** (.x6 ↦ᵣ u6) ** (.x7 ↦ᵣ u7) **
       (.x13 ↦ᵣ u13) ** (.x14 ↦ᵣ u14) ** (.x15 ↦ᵣ u15) ** (.x16 ↦ᵣ u16) **
       (.x28 ↦ᵣ u28) ** (.x29 ↦ᵣ u29) ** (.x30 ↦ᵣ u30) ** (.x31 ↦ᵣ u31) **
       ((sp - (112 : Word)) ↦ₘ v5) ** ((sp - (104 : Word)) ↦ₘ v6) **
       ((sp - (96 : Word)) ↦ₘ v7) ** ((sp - (88 : Word)) ↦ₘ v28) **
       ((sp - (80 : Word)) ↦ₘ v29) ** ((sp - (72 : Word)) ↦ₘ v30) **
       ((sp - (64 : Word)) ↦ₘ v31) ** ((sp - (56 : Word)) ↦ₘ ra) **
       ((sp - (48 : Word)) ↦ₘ v13) ** ((sp - (40 : Word)) ↦ₘ v14) **
       ((sp - (32 : Word)) ↦ₘ v15) ** ((sp - (24 : Word)) ↦ₘ a6) **
       ((sp - (16 : Word)) ↦ₘ a0) **
       (txOvfPtr ↦ₘ ovfTx) ** (blkOvfPtr ↦ₘ ovfBlk))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ a6) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       ((sp - (112 : Word)) ↦ₘ v5) ** ((sp - (104 : Word)) ↦ₘ v6) **
       ((sp - (96 : Word)) ↦ₘ v7) ** ((sp - (88 : Word)) ↦ₘ v28) **
       ((sp - (80 : Word)) ↦ₘ v29) ** ((sp - (72 : Word)) ↦ₘ v30) **
       ((sp - (64 : Word)) ↦ₘ v31) ** ((sp - (56 : Word)) ↦ₘ ra) **
       ((sp - (48 : Word)) ↦ₘ v13) ** ((sp - (40 : Word)) ↦ₘ v14) **
       ((sp - (32 : Word)) ↦ₘ v15) ** ((sp - (24 : Word)) ↦ₘ a6) **
       ((sp - (16 : Word)) ↦ₘ a0) **
       (txOvfPtr ↦ₘ (1 : Word)) ** (blkOvfPtr ↦ₘ (1 : Word))) := by
  unfold storageWriteRecord_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 78: `bne a0, zero, .Lswr_overflow` — TAKEN, the callee refused
  have RB := bne_spec_gen_within .x10 .x0
    (brOff (GuestAddrs.storage_write_record + 492) (GuestAddrs.storage_write_record + 312))
    retVal (0 : Word) (base + (312 : Word))
  rw [hbr, show base + (312 : Word) + (180 : Word) = base + (492 : Word) from by bv_omega]
    at RB
  have R0 : cpsTripleWithin 1 (base + (312 : Word)) (base + (492 : Word))
      (CodeReq.singleton (base + (312 : Word)) (.BNE .x10 .x0
        (brOff (GuestAddrs.storage_write_record + 492)
          (GuestAddrs.storage_write_record + 312))))
      ((.x10 ↦ᵣ retVal) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ retVal) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranchWithin_takenStripPure2 RB (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact hfail h_pure.2)
  -- indices 123, 124: `la t0, tx_storage_writes_overflow`
  have R1 := auipc_spec_gen_within .x5 u5
    (laHi GuestAddrs.tx_storage_writes_overflow (GuestAddrs.storage_write_record + 492))
    (base + (492 : Word)) (by nofun)
  have R2 := addi_spec_gen_same_within .x5
    ((base + (492 : Word)) +
      (((laHi GuestAddrs.tx_storage_writes_overflow
          (GuestAddrs.storage_write_record + 492)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.tx_storage_writes_overflow (GuestAddrs.storage_write_record + 492))
    (base + (496 : Word)) (by nofun)
  rw [hlaTx] at R2
  -- index 125: `li t1, 1`
  have R3 := li_spec_gen_within .x6 u6 (1 : Word) (base + (500 : Word)) (by nofun)
  -- index 126: latch the transaction-level sticky flag
  have R4 := sd_spec_gen_within .x5 .x6 txOvfPtr (1 : Word) ovfTx (0 : BitVec 12)
    (base + (504 : Word))
  rw [show txOvfPtr + signExtend12 (0 : BitVec 12) = txOvfPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at R4
  -- indices 127, 128: `la t0, storage_writes_overflow`
  have R5 := auipc_spec_gen_within .x5 txOvfPtr
    (laHi GuestAddrs.storage_writes_overflow (GuestAddrs.storage_write_record + 508))
    (base + (508 : Word)) (by nofun)
  have R6 := addi_spec_gen_same_within .x5
    ((base + (508 : Word)) +
      (((laHi GuestAddrs.storage_writes_overflow
          (GuestAddrs.storage_write_record + 508)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.storage_writes_overflow (GuestAddrs.storage_write_record + 508))
    (base + (512 : Word)) (by nofun)
  rw [hlaBlk] at R6
  -- index 129: latch the block-level sticky flag
  have R7 := sd_spec_gen_within .x5 .x6 blkOvfPtr (1 : Word) ovfBlk (0 : BitVec 12)
    (base + (516 : Word))
  rw [show blkOvfPtr + signExtend12 (0 : BitVec 12) = blkOvfPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at R7
  -- indices 130..142: reload t0..t6, ra, a3, a4, a5, a6, a0
  have R8 := ld_spec_gen_within .x5 .x2 (sp - (112 : Word)) blkOvfPtr v5 (0 : BitVec 12)
    (base + (520 : Word)) (by nofun)
  rw [show (sp - (112 : Word)) + signExtend12 (0 : BitVec 12) = sp - (112 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at R8
  have R9 := ld_spec_gen_within .x6 .x2 (sp - (112 : Word)) (1 : Word) v6 (8 : BitVec 12)
    (base + (524 : Word)) (by nofun)
  rw [show (sp - (112 : Word)) + signExtend12 (8 : BitVec 12) = sp - (104 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at R9
  have R10 := ld_spec_gen_within .x7 .x2 (sp - (112 : Word)) u7 v7 (16 : BitVec 12)
    (base + (528 : Word)) (by nofun)
  rw [show (sp - (112 : Word)) + signExtend12 (16 : BitVec 12) = sp - (96 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at R10
  have R11 := ld_spec_gen_within .x28 .x2 (sp - (112 : Word)) u28 v28 (24 : BitVec 12)
    (base + (532 : Word)) (by nofun)
  rw [show (sp - (112 : Word)) + signExtend12 (24 : BitVec 12) = sp - (88 : Word) from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]; bv_omega] at R11
  have R12 := ld_spec_gen_within .x29 .x2 (sp - (112 : Word)) u29 v29 (32 : BitVec 12)
    (base + (536 : Word)) (by nofun)
  rw [show (sp - (112 : Word)) + signExtend12 (32 : BitVec 12) = sp - (80 : Word) from by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]; bv_omega] at R12
  have R13 := ld_spec_gen_within .x30 .x2 (sp - (112 : Word)) u30 v30 (40 : BitVec 12)
    (base + (540 : Word)) (by nofun)
  rw [show (sp - (112 : Word)) + signExtend12 (40 : BitVec 12) = sp - (72 : Word) from by
    rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]; bv_omega] at R13
  have R14 := ld_spec_gen_within .x31 .x2 (sp - (112 : Word)) u31 v31 (48 : BitVec 12)
    (base + (544 : Word)) (by nofun)
  rw [show (sp - (112 : Word)) + signExtend12 (48 : BitVec 12) = sp - (64 : Word) from by
    rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide]; bv_omega] at R14
  have R15 := ld_spec_gen_within .x1 .x2 (sp - (112 : Word)) link ra (56 : BitVec 12)
    (base + (548 : Word)) (by nofun)
  rw [show (sp - (112 : Word)) + signExtend12 (56 : BitVec 12) = sp - (56 : Word) from by
    rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide]; bv_omega] at R15
  have R16 := ld_spec_gen_within .x13 .x2 (sp - (112 : Word)) u13 v13 (64 : BitVec 12)
    (base + (552 : Word)) (by nofun)
  rw [show (sp - (112 : Word)) + signExtend12 (64 : BitVec 12) = sp - (48 : Word) from by
    rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide]; bv_omega] at R16
  have R17 := ld_spec_gen_within .x14 .x2 (sp - (112 : Word)) u14 v14 (72 : BitVec 12)
    (base + (556 : Word)) (by nofun)
  rw [show (sp - (112 : Word)) + signExtend12 (72 : BitVec 12) = sp - (40 : Word) from by
    rw [show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide]; bv_omega] at R17
  have R18 := ld_spec_gen_within .x15 .x2 (sp - (112 : Word)) u15 v15 (80 : BitVec 12)
    (base + (560 : Word)) (by nofun)
  rw [show (sp - (112 : Word)) + signExtend12 (80 : BitVec 12) = sp - (32 : Word) from by
    rw [show signExtend12 (80 : BitVec 12) = (80 : Word) from by decide]; bv_omega] at R18
  have R19 := ld_spec_gen_within .x16 .x2 (sp - (112 : Word)) u16 a6 (88 : BitVec 12)
    (base + (564 : Word)) (by nofun)
  rw [show (sp - (112 : Word)) + signExtend12 (88 : BitVec 12) = sp - (24 : Word) from by
    rw [show signExtend12 (88 : BitVec 12) = (88 : Word) from by decide]; bv_omega] at R19
  have R20 := ld_spec_gen_within .x10 .x2 (sp - (112 : Word)) retVal a0 (96 : BitVec 12)
    (base + (568 : Word)) (by nofun)
  rw [show (sp - (112 : Word)) + signExtend12 (96 : BitVec 12) = sp - (16 : Word) from by
    rw [show signExtend12 (96 : BitVec 12) = (96 : Word) from by decide]; bv_omega] at R20
  -- index 143: `addi sp, sp, 112`
  have R21 := addi_spec_gen_same_within .x2 (sp - (112 : Word)) (112 : BitVec 12)
    (base + (572 : Word)) (by nofun)
  rw [show (sp - (112 : Word)) + signExtend12 (112 : BitVec 12) = sp from by
    rw [show signExtend12 (112 : BitVec 12) = (112 : Word) from by decide]; bv_omega] at R21
  -- index 144: `ret`
  have R22 := EvmAsm.Evm64.ret_spec_within' (base + (576 : Word)) ra
  runBlock R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20
    R21 R22

/-- `storage_writes_undo_push`'s journal-full arm on the linked layout: entry
    AND `CodeReq` are both at `GuestAddrs.storage_writes_undo_push`, which is
    the `GuestImageEntries.lean:399` pairing itself — a whole-routine claim in
    the `scripts/proof-frontier.py --shape` sense.  The three `la` round-trips
    and the `bgeu` displacement resolve by `decide` on the linked layout. -/
theorem storageWritesUndoPushFullFlat_spec
    (sp2 retA undoCount ovfTx ovfBlk w5 w6 w7 w10 w28 w29 w30 w31 : Word)
    (hfull : ¬ BitVec.ult undoCount (167652 : Word)) :
    cpsTripleWithin 30 (GuestAddrs.storage_writes_undo_push : Word)
      (retA &&& ~~~(1 : Word))
      (CodeReq.ofProg (GuestAddrs.storage_writes_undo_push : Word)
        storageWritesUndoPush_prog)
      ((.x1 ↦ᵣ retA) ** (.x2 ↦ᵣ sp2) ** (.x10 ↦ᵣ w10) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) **
       (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31) **
       memOwn (sp2 - (64 : Word)) ** memOwn (sp2 - (56 : Word)) **
       memOwn (sp2 - (48 : Word)) ** memOwn (sp2 - (40 : Word)) **
       memOwn (sp2 - (32 : Word)) ** memOwn (sp2 - (24 : Word)) **
       memOwn (sp2 - (16 : Word)) **
       ((GuestAddrs.storage_writes_undo_count : Word) ↦ₘ undoCount) **
       ((GuestAddrs.tx_storage_writes_overflow : Word) ↦ₘ ovfTx) **
       ((GuestAddrs.storage_writes_overflow : Word) ↦ₘ ovfBlk))
      ((.x1 ↦ᵣ retA) ** (.x2 ↦ᵣ sp2) ** (.x10 ↦ᵣ (1 : Word)) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) **
       (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31) **
       ((sp2 - (64 : Word)) ↦ₘ w5) ** ((sp2 - (56 : Word)) ↦ₘ w6) **
       ((sp2 - (48 : Word)) ↦ₘ w7) ** ((sp2 - (40 : Word)) ↦ₘ w28) **
       ((sp2 - (32 : Word)) ↦ₘ w29) ** ((sp2 - (24 : Word)) ↦ₘ w30) **
       ((sp2 - (16 : Word)) ↦ₘ w31) **
       ((GuestAddrs.storage_writes_undo_count : Word) ↦ₘ undoCount) **
       ((GuestAddrs.tx_storage_writes_overflow : Word) ↦ₘ (1 : Word)) **
       ((GuestAddrs.storage_writes_overflow : Word) ↦ₘ (1 : Word))) :=
  storageWritesUndoPush_full_body_spec (GuestAddrs.storage_writes_undo_push : Word)
    sp2 retA
    (GuestAddrs.storage_writes_undo_count : Word)
    (GuestAddrs.tx_storage_writes_overflow : Word)
    (GuestAddrs.storage_writes_overflow : Word)
    undoCount ovfTx ovfBlk w5 w6 w7 w10 w28 w29 w30 w31
    (by decide) (by decide) (by decide) (by decide) hfull

/-! ## The deployed (anchored) whole-routine contract -/

/-- The routine's linked entry. -/
abbrev SWR : Word := (GuestAddrs.storage_write_record : Word)

/-- Its one callee's linked entry. -/
abbrev SWUP : Word := (GuestAddrs.storage_writes_undo_push : Word)

/-- `storage_write_record`'s code requirement: its own 145 instructions at
    `GuestAddrs.storage_write_record`, plus the only routine it calls.

    The union is FORCED, not a convenience: `storage_write_record` has no arm
    that both terminates at `ret` and stays inside its own bytes.  The scan
    exits either into a `jal ra, storage_writes_undo_push` (both the hit and the
    append arm) or, after 5588 iterations, into `.Lswr_overflow`.  So a
    whole-routine triple must range over the callee's bytes too. -/
def swrCR : CodeReq :=
  (CodeReq.ofProg (GuestAddrs.storage_write_record : Word) storageWriteRecord_prog).union
    (CodeReq.ofProg (GuestAddrs.storage_writes_undo_push : Word) storageWritesUndoPush_prog)

theorem swr_disj_undoPush :
    (CodeReq.ofProg SWR storageWriteRecord_prog).Disjoint
      (CodeReq.ofProg SWUP storageWritesUndoPush_prog) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem swrProg_sub_swrCR :
    ∀ a i, CodeReq.ofProg SWR storageWriteRecord_prog a = some i → swrCR a = some i :=
  CodeReq.union_mono_left

/-- Call-site adapter for the `jal ra, storage_writes_undo_push` at instruction
    index 77 (`SWR + 308`) — the append arm's journal push. -/
theorem swr_callSite77 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n SWUP ((SWR + (308 : Word) + 4) &&& ~~~(1 : Word))
      (CodeReq.ofProg SWUP storageWritesUndoPush_prog)
      ((.x1 ↦ᵣ (SWR + (308 : Word) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (SWR + (308 : Word)) (SWR + (308 : Word) + 4) swrCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := SWR + (308 : Word)) (calleeEntry := SWUP) (vOld := vRa)
    (calleeCode := CodeReq.ofProg SWUP storageWritesUndoPush_prog)
    (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.storage_writes_undo_push (GuestAddrs.storage_write_record + 308))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at SWR (SWR + (308 : Word)) storageWriteRecord_prog 77 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right swr_disj_undoPush (fun _ _ h => h) a i h

/-- ⭐ **`storage_write_record`, whole routine, fail-closed arm.**

    Entry `GuestAddrs.storage_write_record`, exit `ra &&& ~~~1` — the caller's
    return address — over `swrCR`, which pairs the linked `GuestAddrs` entry
    with `storageWriteRecord_prog` exactly as `GuestImageEntries.lean:395` does.

    Two named gates select the arm:

    * `tx_storage_writes_count = 0` — the transaction's storage-write map is
      empty, i.e. this is the transaction's FIRST storage write.  The scan's
      `bgeu` at index 22 is then taken with zero iterations, so no loop
      invariant is needed and the routine goes straight to `.Lswr_append`.
    * `hfull : ¬ storage_writes_undo_count < 167652` — the undo journal is full,
      so `storage_writes_undo_push` refuses.

    Under both, the routine is **fail-closed**: it latches
    `tx_storage_writes_overflow` and `storage_writes_overflow` to 1, leaves
    `tx_storage_writes_count` at 0, leaves `storage_writes_undo_count`
    untouched, restores `sp` and every one of the thirteen registers the
    prologue saved, and returns.  Because `cpsTripleWithin` quantifies over an
    arbitrary `pcFree` frame, the triple ALSO says — for free — that nothing at
    all is written to `TX_STORAGE_WRITES_AREA` or to the undo journal arena,
    since neither is named in the pre or the post.  That is the content of the
    "FAILS CLOSED — latches overflow and rejects" claim that
    `Codegen/RegionMap.lean:164` makes in prose.

    ⚠️ NOT proven here: the hit arm, the append arm's 16-dword row write, and
    the 5588-iteration `.Lswr_overflow` arm.  Those need the scan loop
    invariant and the `storageWritesMapIs` vocabulary, and they are where the
    tie to `storageWriteUpsert` (`Stateless/State/StorageWriteUpsert.lean:142`)
    will be made. -/
theorem storageWriteRecordFailClosedFlat_spec
    (sp ra a0 a6 undoCount ovfTx ovfBlk v5 v6 v7 v13 v14 v15 v28 v29 v30 v31 : Word)
    (hfull : ¬ BitVec.ult undoCount (167652 : Word)) :
    cpsTripleWithin 83 (GuestAddrs.storage_write_record : Word) (ra &&& ~~~(1 : Word))
      swrCR
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ a6) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       memOwn (sp - (176 : Word)) ** memOwn (sp - (168 : Word)) **
       memOwn (sp - (160 : Word)) ** memOwn (sp - (152 : Word)) **
       memOwn (sp - (144 : Word)) ** memOwn (sp - (136 : Word)) **
       memOwn (sp - (128 : Word)) **
       memOwn (sp - (112 : Word)) ** memOwn (sp - (104 : Word)) **
       memOwn (sp - (96 : Word)) ** memOwn (sp - (88 : Word)) **
       memOwn (sp - (80 : Word)) ** memOwn (sp - (72 : Word)) **
       memOwn (sp - (64 : Word)) ** memOwn (sp - (56 : Word)) **
       memOwn (sp - (48 : Word)) ** memOwn (sp - (40 : Word)) **
       memOwn (sp - (32 : Word)) ** memOwn (sp - (24 : Word)) **
       memOwn (sp - (16 : Word)) **
       ((GuestAddrs.tx_storage_writes_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.storage_writes_undo_count : Word) ↦ₘ undoCount) **
       ((GuestAddrs.tx_storage_writes_overflow : Word) ↦ₘ ovfTx) **
       ((GuestAddrs.storage_writes_overflow : Word) ↦ₘ ovfBlk))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ a6) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       ((sp - (176 : Word)) ↦ₘ (GuestAddrs.tx_storage_writes_count : Word)) **
       ((sp - (168 : Word)) ↦ₘ (0 : Word)) **
       ((sp - (160 : Word)) ↦ₘ (5588 : Word)) **
       ((sp - (152 : Word)) ↦ₘ (0xa2d57ec0 : Word)) **
       ((sp - (144 : Word)) ↦ₘ (0 : Word)) **
       ((sp - (136 : Word)) ↦ₘ v30) ** ((sp - (128 : Word)) ↦ₘ v31) **
       ((sp - (112 : Word)) ↦ₘ v5) ** ((sp - (104 : Word)) ↦ₘ v6) **
       ((sp - (96 : Word)) ↦ₘ v7) ** ((sp - (88 : Word)) ↦ₘ v28) **
       ((sp - (80 : Word)) ↦ₘ v29) ** ((sp - (72 : Word)) ↦ₘ v30) **
       ((sp - (64 : Word)) ↦ₘ v31) ** ((sp - (56 : Word)) ↦ₘ ra) **
       ((sp - (48 : Word)) ↦ₘ v13) ** ((sp - (40 : Word)) ↦ₘ v14) **
       ((sp - (32 : Word)) ↦ₘ v15) ** ((sp - (24 : Word)) ↦ₘ a6) **
       ((sp - (16 : Word)) ↦ₘ a0) **
       ((GuestAddrs.tx_storage_writes_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.storage_writes_undo_count : Word) ↦ₘ undoCount) **
       ((GuestAddrs.tx_storage_writes_overflow : Word) ↦ₘ (1 : Word)) **
       ((GuestAddrs.storage_writes_overflow : Word) ↦ₘ (1 : Word))) := by
  -- segment A: prologue .. the empty-map `bgeu`
  have hA := cpsTripleWithin_extend_code swrProg_sub_swrCR
    (storageWriteRecord_segA_body_spec SWR sp ra a0 a6
      (GuestAddrs.tx_storage_writes_count : Word) v5 v6 v7 v13 v14 v15 v28 v29 v30 v31
      (by decide) (by decide))
  -- the callee's frame slots and the three globals it touches are not in
  -- segment A's footprint; carry them across it by the frame rule
  have hA := cpsTripleWithin_frameR
    (memOwn (sp - (176 : Word)) ** memOwn (sp - (168 : Word)) **
     memOwn (sp - (160 : Word)) ** memOwn (sp - (152 : Word)) **
     memOwn (sp - (144 : Word)) ** memOwn (sp - (136 : Word)) **
     memOwn (sp - (128 : Word)) **
     ((GuestAddrs.storage_writes_undo_count : Word) ↦ₘ undoCount) **
     ((GuestAddrs.tx_storage_writes_overflow : Word) ↦ₘ ovfTx) **
     ((GuestAddrs.storage_writes_overflow : Word) ↦ₘ ovfBlk))
    (by pcf) hA
  -- segment B: the capacity gate and the call arguments
  have hB := cpsTripleWithin_extend_code swrProg_sub_swrCR
    (storageWriteRecord_segB_body_spec SWR v7 v13 v14 v15)
  -- the callee, on its journal-full arm
  have hU := storageWritesUndoPush_full_body_spec SWUP (sp - (112 : Word))
    (SWR + (308 : Word) + 4)
    (GuestAddrs.storage_writes_undo_count : Word)
    (GuestAddrs.tx_storage_writes_overflow : Word)
    (GuestAddrs.storage_writes_overflow : Word)
    undoCount ovfTx ovfBlk
    (GuestAddrs.tx_storage_writes_count : Word) (0 : Word) (5588 : Word) a0
    (0xa2d57ec0 : Word) (0 : Word) v30 v31
    (by decide) (by decide) (by decide) (by decide) hfull
  rw [show (sp - (112 : Word)) - (64 : Word) = sp - (176 : Word) from by bv_omega,
      show (sp - (112 : Word)) - (56 : Word) = sp - (168 : Word) from by bv_omega,
      show (sp - (112 : Word)) - (48 : Word) = sp - (160 : Word) from by bv_omega,
      show (sp - (112 : Word)) - (40 : Word) = sp - (152 : Word) from by bv_omega,
      show (sp - (112 : Word)) - (32 : Word) = sp - (144 : Word) from by bv_omega,
      show (sp - (112 : Word)) - (24 : Word) = sp - (136 : Word) from by bv_omega,
      show (sp - (112 : Word)) - (16 : Word) = sp - (128 : Word) from by bv_omega] at hU
  have hCall := swr_callSite77 (n := 30) ra (by pcf) hU
  rw [show SWR + (308 : Word) + 4 = SWR + (312 : Word) from by bv_omega] at hCall
  -- segment C: the reject arm and the epilogue
  have hC := cpsTripleWithin_extend_code swrProg_sub_swrCR
    (storageWriteRecord_segC_body_spec SWR sp ra a0 a6 (SWR + (312 : Word)) (1 : Word)
      (GuestAddrs.tx_storage_writes_overflow : Word)
      (GuestAddrs.storage_writes_overflow : Word) (1 : Word) (1 : Word)
      v5 v6 v7 v13 v14 v15 v28 v29 v30 v31
      (GuestAddrs.tx_storage_writes_count : Word) (0 : Word) (5588 : Word)
      (0 : Word) (1 : Word) (0 : Word) a6 (0xa2d57ec0 : Word) (0 : Word) v30 v31
      (by decide) (by decide) (by decide) (by decide))
  seqFrame hA hB
  seqFrame hAhB hCall
  seqFrame hAhBhCall hC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hAhBhCallhC

/-! ## Non-vacuity

  Four checks, in the shape `docs/agents` asks for: a fully numeric instance
  (so a `True`-shaped or trivially satisfiable post could not have passed),
  a positive witness for each gate, a NEGATIVE control showing that each gate
  really excludes the inputs the routine is normally asked about, and a
  satisfiability check on the numeric precondition — `memOwn`/`↦ₘ` both
  *assert* `isValidDwordAccess`, so an unsatisfiable pre is a real risk rather
  than a formality. -/

/-- **Numeric instance.** `sp = 0x30000000`, an undo cursor of 200000 (past the
    167652 capacity), both sticky flags starting at 0, and the ten saved
    temporaries `1..7, 11..13`.  The post is fully concrete: the twenty spill
    slots hold their saved values in spill order (the callee's seven carrying
    the scan state the caller had live at the call — the count pointer, 0, the
    capacity 5588, the arena base 0xa2d57ec0, 0, and `t5`/`t6`), `sp` is back at
    `0x30000000`, `tx_storage_writes_count` still reads 0, the undo cursor is
    still 200000, and BOTH overflow flags now read 1. -/
example (ra a0 a6 : Word) :
    cpsTripleWithin 83 (GuestAddrs.storage_write_record : Word) (ra &&& ~~~(1 : Word))
      swrCR
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (0x30000000 : Word)) **
       (.x10 ↦ᵣ a0) **
       (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (2 : Word)) ** (.x7 ↦ᵣ (3 : Word)) **
       (.x13 ↦ᵣ (11 : Word)) ** (.x14 ↦ᵣ (12 : Word)) ** (.x15 ↦ᵣ (13 : Word)) **
       (.x16 ↦ᵣ a6) **
       (.x28 ↦ᵣ (4 : Word)) ** (.x29 ↦ᵣ (5 : Word)) ** (.x30 ↦ᵣ (6 : Word)) **
       (.x31 ↦ᵣ (7 : Word)) **
       memOwn (0x2fffff50 : Word) **
       memOwn (0x2fffff58 : Word) **
       memOwn (0x2fffff60 : Word) **
       memOwn (0x2fffff68 : Word) **
       memOwn (0x2fffff70 : Word) **
       memOwn (0x2fffff78 : Word) **
       memOwn (0x2fffff80 : Word) **
       memOwn (0x2fffff90 : Word) **
       memOwn (0x2fffff98 : Word) **
       memOwn (0x2fffffa0 : Word) **
       memOwn (0x2fffffa8 : Word) **
       memOwn (0x2fffffb0 : Word) **
       memOwn (0x2fffffb8 : Word) **
       memOwn (0x2fffffc0 : Word) **
       memOwn (0x2fffffc8 : Word) **
       memOwn (0x2fffffd0 : Word) **
       memOwn (0x2fffffd8 : Word) **
       memOwn (0x2fffffe0 : Word) **
       memOwn (0x2fffffe8 : Word) **
       memOwn (0x2ffffff0 : Word) **
       ((GuestAddrs.tx_storage_writes_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.storage_writes_undo_count : Word) ↦ₘ (200000 : Word)) **
       ((GuestAddrs.tx_storage_writes_overflow : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.storage_writes_overflow : Word) ↦ₘ (0 : Word)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (0x30000000 : Word)) **
       (.x10 ↦ᵣ a0) **
       (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (2 : Word)) ** (.x7 ↦ᵣ (3 : Word)) **
       (.x13 ↦ᵣ (11 : Word)) ** (.x14 ↦ᵣ (12 : Word)) ** (.x15 ↦ᵣ (13 : Word)) **
       (.x16 ↦ᵣ a6) **
       (.x28 ↦ᵣ (4 : Word)) ** (.x29 ↦ᵣ (5 : Word)) ** (.x30 ↦ᵣ (6 : Word)) **
       (.x31 ↦ᵣ (7 : Word)) **
       ((0x2fffff50 : Word) ↦ₘ (GuestAddrs.tx_storage_writes_count : Word)) **
       ((0x2fffff58 : Word) ↦ₘ (0 : Word)) **
       ((0x2fffff60 : Word) ↦ₘ (5588 : Word)) **
       ((0x2fffff68 : Word) ↦ₘ (0xa2d57ec0 : Word)) **
       ((0x2fffff70 : Word) ↦ₘ (0 : Word)) **
       ((0x2fffff78 : Word) ↦ₘ (6 : Word)) **
       ((0x2fffff80 : Word) ↦ₘ (7 : Word)) **
       ((0x2fffff90 : Word) ↦ₘ (1 : Word)) **
       ((0x2fffff98 : Word) ↦ₘ (2 : Word)) **
       ((0x2fffffa0 : Word) ↦ₘ (3 : Word)) **
       ((0x2fffffa8 : Word) ↦ₘ (4 : Word)) **
       ((0x2fffffb0 : Word) ↦ₘ (5 : Word)) **
       ((0x2fffffb8 : Word) ↦ₘ (6 : Word)) **
       ((0x2fffffc0 : Word) ↦ₘ (7 : Word)) **
       ((0x2fffffc8 : Word) ↦ₘ ra) **
       ((0x2fffffd0 : Word) ↦ₘ (11 : Word)) **
       ((0x2fffffd8 : Word) ↦ₘ (12 : Word)) **
       ((0x2fffffe0 : Word) ↦ₘ (13 : Word)) **
       ((0x2fffffe8 : Word) ↦ₘ a6) **
       ((0x2ffffff0 : Word) ↦ₘ a0) **
       ((GuestAddrs.tx_storage_writes_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.storage_writes_undo_count : Word) ↦ₘ (200000 : Word)) **
       ((GuestAddrs.tx_storage_writes_overflow : Word) ↦ₘ (1 : Word)) **
       ((GuestAddrs.storage_writes_overflow : Word) ↦ₘ (1 : Word))) := by
  have h := storageWriteRecordFailClosedFlat_spec (0x30000000 : Word) ra a0 a6
    (200000 : Word) 0 0 1 2 3 11 12 13 4 5 6 7 (by decide)
  rw [
      show (0x30000000 : Word) - (176 : Word) = (0x2fffff50 : Word) from by decide,
      show (0x30000000 : Word) - (168 : Word) = (0x2fffff58 : Word) from by decide,
      show (0x30000000 : Word) - (160 : Word) = (0x2fffff60 : Word) from by decide,
      show (0x30000000 : Word) - (152 : Word) = (0x2fffff68 : Word) from by decide,
      show (0x30000000 : Word) - (144 : Word) = (0x2fffff70 : Word) from by decide,
      show (0x30000000 : Word) - (136 : Word) = (0x2fffff78 : Word) from by decide,
      show (0x30000000 : Word) - (128 : Word) = (0x2fffff80 : Word) from by decide,
      show (0x30000000 : Word) - (112 : Word) = (0x2fffff90 : Word) from by decide,
      show (0x30000000 : Word) - (104 : Word) = (0x2fffff98 : Word) from by decide,
      show (0x30000000 : Word) - (96 : Word) = (0x2fffffa0 : Word) from by decide,
      show (0x30000000 : Word) - (88 : Word) = (0x2fffffa8 : Word) from by decide,
      show (0x30000000 : Word) - (80 : Word) = (0x2fffffb0 : Word) from by decide,
      show (0x30000000 : Word) - (72 : Word) = (0x2fffffb8 : Word) from by decide,
      show (0x30000000 : Word) - (64 : Word) = (0x2fffffc0 : Word) from by decide,
      show (0x30000000 : Word) - (56 : Word) = (0x2fffffc8 : Word) from by decide,
      show (0x30000000 : Word) - (48 : Word) = (0x2fffffd0 : Word) from by decide,
      show (0x30000000 : Word) - (40 : Word) = (0x2fffffd8 : Word) from by decide,
      show (0x30000000 : Word) - (32 : Word) = (0x2fffffe0 : Word) from by decide,
      show (0x30000000 : Word) - (24 : Word) = (0x2fffffe8 : Word) from by decide,
      show (0x30000000 : Word) - (16 : Word) = (0x2ffffff0 : Word) from by decide] at h
  exact h

/-- **Gate witnesses and negative controls.**

    1. `¬ 200000 <ᵤ 167652` inhabits `hfull` — a journal past capacity.
    2. `¬ ¬ 0 <ᵤ 167652` is provably FALSE, so the arm genuinely EXCLUDES the
       ordinary case of an empty undo journal rather than covering it silently.
       (`storage_writes_undo_push` then falls through to its append path at
       index 14 instead of branching to `+188`.)
    3. `0 <ᵤ 5588` and `¬ 0 <ᵤ 0`: with an empty transaction map the scan's
       `bgeu` at index 22 IS taken with zero iterations, and the capacity
       `bgeu` at index 73 is NOT — which is why this arm needs no loop
       invariant.  A non-empty map (`count = 1`) makes the first one FALSE, so
       the hit / append / 5588-iteration arms really are outside the triple.
    4. The two arms of the caller's `bne` at index 78 are distinct addresses,
       so "taken" is a real restriction. -/
example :
    (¬ BitVec.ult (200000 : Word) (167652 : Word))
    ∧ ¬ (¬ BitVec.ult (0 : Word) (167652 : Word))
    ∧ (¬ BitVec.ult (0 : Word) (0 : Word))
    ∧ ¬ (¬ BitVec.ult (0 : Word) (1 : Word))
    ∧ BitVec.ult (0 : Word) (5588 : Word)
    ∧ (GuestAddrs.storage_write_record + 316 ≠ GuestAddrs.storage_write_record + 492) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Satisfiability of the numeric instance's precondition.**  All twenty
    frame slots and all four globals are valid, 8-byte-aligned dword addresses,
    and the four globals are pairwise distinct and disjoint from the frame — so
    the separating conjunction is inhabitable and the numeric post above is not
    vacuously true. -/
example :
    isValidDwordAccess (0x2fffff50 : Word) = true ∧
    isValidDwordAccess (0x2fffff58 : Word) = true ∧
    isValidDwordAccess (0x2fffff60 : Word) = true ∧
    isValidDwordAccess (0x2fffff68 : Word) = true ∧
    isValidDwordAccess (0x2fffff70 : Word) = true ∧
    isValidDwordAccess (0x2fffff78 : Word) = true ∧
    isValidDwordAccess (0x2fffff80 : Word) = true ∧
    isValidDwordAccess (0x2fffff90 : Word) = true ∧
    isValidDwordAccess (0x2fffff98 : Word) = true ∧
    isValidDwordAccess (0x2fffffa0 : Word) = true ∧
    isValidDwordAccess (0x2fffffa8 : Word) = true ∧
    isValidDwordAccess (0x2fffffb0 : Word) = true ∧
    isValidDwordAccess (0x2fffffb8 : Word) = true ∧
    isValidDwordAccess (0x2fffffc0 : Word) = true ∧
    isValidDwordAccess (0x2fffffc8 : Word) = true ∧
    isValidDwordAccess (0x2fffffd0 : Word) = true ∧
    isValidDwordAccess (0x2fffffd8 : Word) = true ∧
    isValidDwordAccess (0x2fffffe0 : Word) = true ∧
    isValidDwordAccess (0x2fffffe8 : Word) = true ∧
    isValidDwordAccess (0x2ffffff0 : Word) = true ∧
    isValidDwordAccess (GuestAddrs.tx_storage_writes_count : Word) = true ∧
    isValidDwordAccess (GuestAddrs.storage_writes_undo_count : Word) = true ∧
    isValidDwordAccess (GuestAddrs.tx_storage_writes_overflow : Word) = true ∧
    isValidDwordAccess (GuestAddrs.storage_writes_overflow : Word) = true ∧
    (GuestAddrs.tx_storage_writes_count : Word) ≠ (GuestAddrs.storage_writes_undo_count : Word) ∧
    (GuestAddrs.tx_storage_writes_overflow : Word) ≠ (GuestAddrs.storage_writes_overflow : Word) ∧
    (GuestAddrs.tx_storage_writes_count : Word) ≠ (0x2fffff50 : Word) ∧
    (GuestAddrs.storage_writes_overflow : Word) ≠ (0x2ffffff0 : Word) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## Axiom audit — classical-only. -/

#print axioms storageWritesUndoPush_full_body_spec
#print axioms storageWritesUndoPushFullFlat_spec
#print axioms storageWriteRecordFailClosedFlat_spec

end EvmAsm.Codegen.Proofs
