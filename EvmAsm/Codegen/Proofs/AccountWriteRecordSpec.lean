/-
  EvmAsm.Codegen.Proofs.AccountWriteRecordSpec

  **The `account_write_record` machine triple — fail-closed arm (#11921).**

  `account_write_record` (`Codegen/Programs/AccountWriteMap.lean`,
  `accountWriteRecord_prog`, 144 instructions at
  `GuestAddrs.account_write_record`, image entry
  `GuestImageEntries.lean:401`) is the guest's `set_account`
  (`state_tracker.py:486`): scan `TX_ACCOUNT_WRITES_AREA` for the 20-byte
  big-endian address, overlay the masked fields on a hit, append a fresh
  128-byte row on a miss, drop the write and latch the sticky overflow
  flags when either the arena (`txAccountWritesCapacity` = 16384 rows) or
  the undo journal (`accountWritesUndoCapacity` = 163840 rows) is full.

  ## ⭐ Why the `CodeReq` is a union, and why that is forced

  `Codegen.Proofs.AccountReadRecordSpec` could state its arm over
  `CodeReq.ofProg (GuestAddrs.account_read_record) accountReadRecord_prog`
  alone, because that routine's suppression gate reaches the epilogue
  without leaving its own bytes.  **`account_write_record` has no such
  arm** — the same structural finding
  `Codegen.Proofs.StorageWriteRecordSpec` records for its storage twin.
  Every terminating path either

  * runs the scan at index 24 for `tx_account_writes_count` iterations, or
  * reaches a `jal ra, account_writes_undo_push` (index 40 on the hit arm,
    index 55 on the append arm),

  and the only path that avoids the call — `.Lawr_overflow` at index 127,
  entered by the arena-capacity `bgeu` at index 52 — is reachable only
  when the count has already driven 16384 scan iterations.  So a
  whole-routine triple over this Program must range over the callee's
  bytes too, and `awrCR` is that union: the routine's own 144
  instructions at their linked `GuestAddrs` entry, plus
  `accountWritesUndoPush_prog` at its own.  (This is the `pdCr`/`bansfCR`
  shape; `scripts/proof-frontier.py`'s classifier resolves the union body
  and still sees `GuestAddrs.account_write_record` as the anchor.)

  ## What this module proves

  `accountWriteRecordFailClosedFlat_spec`, a 77-step whole-routine triple
  entry → `ret` under two named gates:

  * the transaction's account-write map is empty
    (`tx_account_writes_count ↦ₘ 0`) — this is a transaction's FIRST
    account write, so the scan's `bgeu` at index 24 is taken with zero
    iterations and no loop invariant is needed;
  * the undo journal is full (`hfull`), so `account_writes_undo_push`
    refuses.

  Under those, the routine is **fail-closed**: both sticky flags latch to
  1, `tx_account_writes_count` stays 0, `account_writes_undo_count` is not
  advanced, and `sp` plus the eight registers the epilogue reloads
  (`t0`-`t6` and `ra`) come back intact.  Because `cpsTripleWithin`
  universally quantifies over a `pcFree` frame, the triple ALSO says — for
  free, since neither is named in the pre or the post — that nothing is
  written to `TX_ACCOUNT_WRITES_AREA` or to the account undo-journal
  arena.  That is the spec-side content of the
  "⭐ **FAILS CLOSED** — latches overflow and rejects" discipline the
  region table states only in prose.

  ⚠️ **The post is NOT a full callee-saves claim, and that is a finding.**
  `accountWriteRecord_prog`'s prologue spills `a0`-`a7` (indices 9..16,
  frame slots `+64 .. +120`) but its epilogue (indices 134..141) reloads
  only `t0`-`t6` and `ra`.  The spill slots are re-read as *argument*
  scratch across the call (indices 29, 65, 91, 94, 105, 111, 113, 117,
  121), never to restore the caller's values, and no arm of the routine
  reloads them — the success path at index 126 jumps to the very same
  index-134 epilogue.  So the post here honestly records `a0 = 1`
  (the callee's failure code), `a5 = 0` and `a6 = 1` (the arguments this
  arm materialised at indices 53/54), rather than the entry values.  The
  storage twin `storageWriteRecord_prog` DOES reload `a0`, so this is an
  asymmetry between the two writers, not a shared convention.  It is not a
  soundness defect — `a0`-`a7` are caller-saved under the RISC-V ABI — but
  it does contradict `AccountWriteMap.lean`'s docstring claim that "the
  argument registers it forwards are saved and restored", and therefore
  the claim that the routine is safe to call from a handler `preBody`
  holding live dispatcher state in caller-saved registers.

  `accountWritesUndoPushFullFlat_spec` is the callee's own whole-routine
  contract on the same arm — the first triple of any shape for
  `account_writes_undo_push`.

  ## ⚠️ What is deliberately NOT proven

  The hit arm, the append arm's fourteen-dword zero-fill plus the masked
  field overlay (indices 74..126), and the 16384-iteration
  `.Lawr_overflow` arm.  Those need the scan's loop invariant (measure
  `tx_account_writes_count − t4`) and the account write-map vocabulary,
  and they are where the machine will be tied to the already-proven model
  `accountWriteUpsert` (`Stateless/State/AccountWriteUpsert.lean`,
  #11938/#12016).  The registry row is therefore `.conditional` with both
  gates named.

  ## `Nodup`

  #11921 asks what became of the writer's uniqueness clause.  As on the
  storage side, it neither becomes a machine theorem here nor is assumed:
  it is simply not reachable from this arm.  Uniqueness is already a
  hypothesis-free model theorem (`accountWriteUpsert_rowsMap`, #11938).
  A fail-closed arm writes no row, so it makes no claim about the row
  sequence and never mentions `AccountWriteRowsMap`; that model theorem is
  consumed when the append arm is proved, not before.

  ## Mechanics

  Same two pilot rules as `StorageWriteRecordSpec`: present the code
  requirement as the `singleton`-union chain (`unfold` + `CodeReq.ofProg_cons`)
  before `runBlock`, and write every offset `(k : Word)`.  Segments compose
  with `seqFrame`; the call site uses `WP.cpsCallWithin` behind the
  `awr_callSite55` adapter.  The file is not `module`-ised because
  `CodeReq.ofProg_mem_at` and `CodeReq.Disjoint.ofProg_ranges` live in
  non-`module` `Rv64/SAsm` files — the same reason
  `StorageWriteRecordSpec.lean` is not.

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
import EvmAsm.Codegen.Programs.AccountWriteMap

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen

/-! ## Segment A — prologue, arena base, and the empty-map exit of the scan -/

/-- `account_write_record` instructions 0..24 at a free `base`: the 16-slot
    prologue, `la t0, tx_account_writes_count`, the three-instruction
    `TX_ACCOUNT_WRITES_AREA` materialisation, `li t4, 0`, and the scan's
    `bgeu` — TAKEN, because the transaction's account-write map is empty
    (`countPtr ↦ₘ 0`). -/
theorem accountWriteRecord_segA_body_spec
    (base sp ra countPtr v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17
      v28 v29 v30 v31 : Word)
    (hla : base + (68 : Word) +
        (((laHi GuestAddrs.tx_account_writes_count
            (GuestAddrs.account_write_record + 68)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.tx_account_writes_count
          (GuestAddrs.account_write_record + 68)) = countPtr)
    (hbr : signExtend13 (brOff (GuestAddrs.account_write_record + 204)
        (GuestAddrs.account_write_record + 96)) = (108 : Word)) :
    cpsTripleWithin 25 base (base + (204 : Word))
      (CodeReq.ofProg base accountWriteRecord_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
       (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       memOwn (sp - (128 : Word)) ** memOwn (sp - (120 : Word)) **
       memOwn (sp - (112 : Word)) ** memOwn (sp - (104 : Word)) **
       memOwn (sp - (96 : Word)) ** memOwn (sp - (88 : Word)) **
       memOwn (sp - (80 : Word)) ** memOwn (sp - (72 : Word)) **
       memOwn (sp - (64 : Word)) ** memOwn (sp - (56 : Word)) **
       memOwn (sp - (48 : Word)) ** memOwn (sp - (40 : Word)) **
       memOwn (sp - (32 : Word)) ** memOwn (sp - (24 : Word)) **
       memOwn (sp - (16 : Word)) ** memOwn (sp - (8 : Word)) **
       (countPtr ↦ₘ (0 : Word)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp - (128 : Word))) **
       (.x5 ↦ᵣ countPtr) ** (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
       (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) **
       (.x28 ↦ᵣ EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA) ** (.x29 ↦ᵣ (0 : Word)) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       ((sp - (128 : Word)) ↦ₘ v5) ** ((sp - (120 : Word)) ↦ₘ v6) **
       ((sp - (112 : Word)) ↦ₘ v7) ** ((sp - (104 : Word)) ↦ₘ v28) **
       ((sp - (96 : Word)) ↦ₘ v29) ** ((sp - (88 : Word)) ↦ₘ v30) **
       ((sp - (80 : Word)) ↦ₘ v31) ** ((sp - (72 : Word)) ↦ₘ ra) **
       ((sp - (64 : Word)) ↦ₘ v10) ** ((sp - (56 : Word)) ↦ₘ v11) **
       ((sp - (48 : Word)) ↦ₘ v12) ** ((sp - (40 : Word)) ↦ₘ v13) **
       ((sp - (32 : Word)) ↦ₘ v14) ** ((sp - (24 : Word)) ↦ₘ v15) **
       ((sp - (16 : Word)) ↦ₘ v16) ** ((sp - (8 : Word)) ↦ₘ v17) **
       (countPtr ↦ₘ (0 : Word))) := by
  unfold accountWriteRecord_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 0: `addi sp, sp, -128`
  have P0 := addi_spec_gen_same_within .x2 sp (-128 : BitVec 12) base (by nofun)
  rw [show signExtend12 (-128 : BitVec 12) = (-128 : Word) from by decide,
      show sp + (-128 : Word) = sp - (128 : Word) from by bv_omega] at P0
  -- indices 1..16: spill t0,t1,t2,t3,t4,t5,t6,ra,a0,a1,a2,a3,a4,a5,a6,a7
  have P1 := sd_spec_gen_own_within .x2 .x5 (sp - (128 : Word)) v5 (0 : BitVec 12)
    (base + (4 : Word))
  rw [show (sp - (128 : Word)) + signExtend12 (0 : BitVec 12) = sp - (128 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at P1
  have P2 := sd_spec_gen_own_within .x2 .x6 (sp - (128 : Word)) v6 (8 : BitVec 12)
    (base + (8 : Word))
  rw [show (sp - (128 : Word)) + signExtend12 (8 : BitVec 12) = sp - (120 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at P2
  have P3 := sd_spec_gen_own_within .x2 .x7 (sp - (128 : Word)) v7 (16 : BitVec 12)
    (base + (12 : Word))
  rw [show (sp - (128 : Word)) + signExtend12 (16 : BitVec 12) = sp - (112 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at P3
  have P4 := sd_spec_gen_own_within .x2 .x28 (sp - (128 : Word)) v28 (24 : BitVec 12)
    (base + (16 : Word))
  rw [show (sp - (128 : Word)) + signExtend12 (24 : BitVec 12) = sp - (104 : Word) from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]; bv_omega] at P4
  have P5 := sd_spec_gen_own_within .x2 .x29 (sp - (128 : Word)) v29 (32 : BitVec 12)
    (base + (20 : Word))
  rw [show (sp - (128 : Word)) + signExtend12 (32 : BitVec 12) = sp - (96 : Word) from by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]; bv_omega] at P5
  have P6 := sd_spec_gen_own_within .x2 .x30 (sp - (128 : Word)) v30 (40 : BitVec 12)
    (base + (24 : Word))
  rw [show (sp - (128 : Word)) + signExtend12 (40 : BitVec 12) = sp - (88 : Word) from by
    rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]; bv_omega] at P6
  have P7 := sd_spec_gen_own_within .x2 .x31 (sp - (128 : Word)) v31 (48 : BitVec 12)
    (base + (28 : Word))
  rw [show (sp - (128 : Word)) + signExtend12 (48 : BitVec 12) = sp - (80 : Word) from by
    rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide]; bv_omega] at P7
  have P8 := sd_spec_gen_own_within .x2 .x1 (sp - (128 : Word)) ra (56 : BitVec 12)
    (base + (32 : Word))
  rw [show (sp - (128 : Word)) + signExtend12 (56 : BitVec 12) = sp - (72 : Word) from by
    rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide]; bv_omega] at P8
  have P9 := sd_spec_gen_own_within .x2 .x10 (sp - (128 : Word)) v10 (64 : BitVec 12)
    (base + (36 : Word))
  rw [show (sp - (128 : Word)) + signExtend12 (64 : BitVec 12) = sp - (64 : Word) from by
    rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide]; bv_omega] at P9
  have P10 := sd_spec_gen_own_within .x2 .x11 (sp - (128 : Word)) v11 (72 : BitVec 12)
    (base + (40 : Word))
  rw [show (sp - (128 : Word)) + signExtend12 (72 : BitVec 12) = sp - (56 : Word) from by
    rw [show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide]; bv_omega] at P10
  have P11 := sd_spec_gen_own_within .x2 .x12 (sp - (128 : Word)) v12 (80 : BitVec 12)
    (base + (44 : Word))
  rw [show (sp - (128 : Word)) + signExtend12 (80 : BitVec 12) = sp - (48 : Word) from by
    rw [show signExtend12 (80 : BitVec 12) = (80 : Word) from by decide]; bv_omega] at P11
  have P12 := sd_spec_gen_own_within .x2 .x13 (sp - (128 : Word)) v13 (88 : BitVec 12)
    (base + (48 : Word))
  rw [show (sp - (128 : Word)) + signExtend12 (88 : BitVec 12) = sp - (40 : Word) from by
    rw [show signExtend12 (88 : BitVec 12) = (88 : Word) from by decide]; bv_omega] at P12
  have P13 := sd_spec_gen_own_within .x2 .x14 (sp - (128 : Word)) v14 (96 : BitVec 12)
    (base + (52 : Word))
  rw [show (sp - (128 : Word)) + signExtend12 (96 : BitVec 12) = sp - (32 : Word) from by
    rw [show signExtend12 (96 : BitVec 12) = (96 : Word) from by decide]; bv_omega] at P13
  have P14 := sd_spec_gen_own_within .x2 .x15 (sp - (128 : Word)) v15 (104 : BitVec 12)
    (base + (56 : Word))
  rw [show (sp - (128 : Word)) + signExtend12 (104 : BitVec 12) = sp - (24 : Word) from by
    rw [show signExtend12 (104 : BitVec 12) = (104 : Word) from by decide]; bv_omega] at P14
  have P15 := sd_spec_gen_own_within .x2 .x16 (sp - (128 : Word)) v16 (112 : BitVec 12)
    (base + (60 : Word))
  rw [show (sp - (128 : Word)) + signExtend12 (112 : BitVec 12) = sp - (16 : Word) from by
    rw [show signExtend12 (112 : BitVec 12) = (112 : Word) from by decide]; bv_omega] at P15
  have P16 := sd_spec_gen_own_within .x2 .x17 (sp - (128 : Word)) v17 (120 : BitVec 12)
    (base + (64 : Word))
  rw [show (sp - (128 : Word)) + signExtend12 (120 : BitVec 12) = sp - (8 : Word) from by
    rw [show signExtend12 (120 : BitVec 12) = (120 : Word) from by decide]; bv_omega] at P16
  -- indices 17, 18: `la t0, tx_account_writes_count`
  have P17 := auipc_spec_gen_within .x5 v5
    (laHi GuestAddrs.tx_account_writes_count (GuestAddrs.account_write_record + 68))
    (base + (68 : Word)) (by nofun)
  have P18 := addi_spec_gen_same_within .x5
    ((base + (68 : Word)) +
      (((laHi GuestAddrs.tx_account_writes_count
          (GuestAddrs.account_write_record + 68)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.tx_account_writes_count (GuestAddrs.account_write_record + 68))
    (base + (72 : Word)) (by nofun)
  rw [hla] at P18
  -- index 19: `ld t1, 0(t0)` — the transaction-level entry count
  have P19 := ld_spec_gen_within .x6 .x5 countPtr v6 (0 : Word) (0 : BitVec 12)
    (base + (76 : Word)) (by nofun)
  rw [show countPtr + signExtend12 (0 : BitVec 12) = countPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at P19
  -- indices 20..22: materialise the TX_ACCOUNT_WRITES_AREA base into t3
  have P20 := lui_spec_gen_within .x28 v28
    (((EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat >>> 12) >>> 12) : BitVec 20)
    (base + (80 : Word)) (by nofun)
  rw [show ((((((EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat >>> 12) >>> 12) : BitVec 20)
      ).zeroExtend 32 <<< 12).signExtend 64) = (782336 : Word) from by decide] at P20
  have P21 := addiw_spec_gen_same_within .x28 (782336 : Word)
    (((EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat >>> 12) % 4096) : BitVec 12)
    (base + (84 : Word)) (by nofun)
  rw [show ((((782336 : Word).truncate 32 +
      (signExtend12 (((EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat >>> 12) % 4096) :
        BitVec 12)).truncate 32 : BitVec 32)).signExtend 64) = (784256 : Word) from by
    decide] at P21
  have P22 := slli_spec_gen_same_within .x28 (784256 : Word) (12 : BitVec 6)
    (base + (88 : Word)) (by nofun)
  rw [show ((784256 : Word) <<< (12 : BitVec 6).toNat)
      = EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA from by decide] at P22
  -- index 23: `li t4, 0` — the scan cursor
  have P23 := li_spec_gen_within .x29 v29 (0 : Word) (base + (92 : Word)) (by nofun)
  -- index 24: `bgeu t4, t1, .Lawr_append` — TAKEN, the map is empty
  have PB := bgeu_spec_gen_within .x29 .x6
    (brOff (GuestAddrs.account_write_record + 204) (GuestAddrs.account_write_record + 96))
    (0 : Word) (0 : Word) (base + (96 : Word))
  rw [hbr, show base + (96 : Word) + (108 : Word) = base + (204 : Word) from by bv_omega]
    at PB
  have P24 : cpsTripleWithin 1 (base + (96 : Word)) (base + (204 : Word))
      (CodeReq.singleton (base + (96 : Word)) (.BGEU .x29 .x6
        (brOff (GuestAddrs.account_write_record + 204)
          (GuestAddrs.account_write_record + 96))))
      ((.x29 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)))
      ((.x29 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word))) :=
    cpsBranchWithin_takenStripPure2 PB (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact absurd h_pure.2 (by decide))
  runBlock P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20
    P21 P22 P23 P24

/-! ## Segment B — the arena-capacity gate and the undo-journal call arguments -/

/-- `account_write_record` instructions 51..54 (`base + 204 .. base + 216`):
    materialise the arena capacity `txAccountWritesCapacity` = 16384 into `t2`,
    take the capacity `bgeu` NOT taken (the map is empty, so `0 < 16384`), and
    load the two `account_writes_undo_push` arguments — `a5 = 0` (the append
    index) and `a6 = 1` (`wasAbsent`). -/
theorem accountWriteRecord_segB_body_spec
    (base v7 v15 v16 : Word) :
    cpsTripleWithin 4 (base + (204 : Word)) (base + (220 : Word))
      (CodeReq.ofProg base accountWriteRecord_prog)
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16))
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (16384 : Word)) **
       (.x15 ↦ᵣ (0 : Word)) ** (.x16 ↦ᵣ (1 : Word))) := by
  unfold accountWriteRecord_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 51: `lui t2, 4` — the transaction arena capacity, 16384 rows
  have Q0 := lui_spec_gen_within .x7 v7 (4 : BitVec 20) (base + (204 : Word)) (by nofun)
  rw [show (((4 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64) = (16384 : Word) from by
    decide] at Q0
  -- index 52: `bgeu t1, t2, .Lawr_overflow` — NOT taken, `0 < 16384`
  have QB := bgeu_spec_gen_within .x6 .x7
    (brOff (GuestAddrs.account_write_record + 508) (GuestAddrs.account_write_record + 208))
    (0 : Word) (16384 : Word) (base + (208 : Word))
  have Q1 : cpsTripleWithin 1 (base + (208 : Word)) (base + (208 : Word) + 4)
      (CodeReq.singleton (base + (208 : Word)) (.BGEU .x6 .x7
        (brOff (GuestAddrs.account_write_record + 508)
          (GuestAddrs.account_write_record + 208))))
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (16384 : Word)))
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (16384 : Word))) :=
    cpsBranchWithin_ntakenStripPure2 QB (fun hp hQt => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQt
      exact absurd h_pure.2 (by decide))
  rw [show base + (208 : Word) + 4 = base + (212 : Word) from by bv_omega] at Q1
  -- index 53: `mv a5, t1` — the append index (0, the map is empty)
  have Q2 := mv_spec_gen_within .x15 .x6 (0 : Word) v15 (base + (212 : Word)) (by nofun)
  -- index 54: `li a6, 1` — wasAbsent
  have Q3 := li_spec_gen_within .x16 v16 (1 : Word) (base + (216 : Word)) (by nofun)
  runBlock Q0 Q1 Q2 Q3

/-! ## The callee — `account_writes_undo_push`, journal-full arm -/

/-- `account_writes_undo_push` at a free `ubase`, on the **journal-full** arm:
    the sole capacity `bgeu` at index 12 is TAKEN (`hfull`), so the routine
    latches both sticky overflow flags, returns `a0 = 1`, and — crucially —
    stores NOTHING into the journal and does not advance
    `account_writes_undo_count`.

    That is the fail-closed contract the caller depends on: it must reject on
    `a0 ≠ 0` rather than mutate the map without a rollback record;
    `accountWriteRecord_segC_body_spec` is the arm that does. -/
theorem accountWritesUndoPush_full_body_spec
    (ubase sp2 retA undoPtr txOvfPtr blkOvfPtr undoCount ovfTx ovfBlk
      w5 w6 w7 w10 w28 w29 w30 w31 : Word)
    (hlaCount : ubase + (32 : Word) +
        (((laHi GuestAddrs.account_writes_undo_count
            (GuestAddrs.account_writes_undo_push + 32)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.account_writes_undo_count
          (GuestAddrs.account_writes_undo_push + 32)) = undoPtr)
    (hlaTx : ubase + (228 : Word) +
        (((laHi GuestAddrs.tx_account_writes_overflow
            (GuestAddrs.account_writes_undo_push + 228)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.tx_account_writes_overflow
          (GuestAddrs.account_writes_undo_push + 228)) = txOvfPtr)
    (hlaBlk : ubase + (240 : Word) +
        (((laHi GuestAddrs.account_writes_overflow
            (GuestAddrs.account_writes_undo_push + 240)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.account_writes_overflow
          (GuestAddrs.account_writes_undo_push + 240)) = blkOvfPtr)
    (hbr : signExtend13 (brOff (GuestAddrs.account_writes_undo_push + 224)
        (GuestAddrs.account_writes_undo_push + 48)) = (176 : Word))
    (hfull : ¬ BitVec.ult undoCount (163840 : Word)) :
    cpsTripleWithin 29 ubase (retA &&& ~~~(1 : Word))
      (CodeReq.ofProg ubase accountWritesUndoPush_prog)
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
  unfold accountWritesUndoPush_prog
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
  -- indices 8, 9: `la t0, account_writes_undo_count`
  have U8 := auipc_spec_gen_within .x5 w5
    (laHi GuestAddrs.account_writes_undo_count (GuestAddrs.account_writes_undo_push + 32))
    (ubase + (32 : Word)) (by nofun)
  have U9 := addi_spec_gen_same_within .x5
    ((ubase + (32 : Word)) +
      (((laHi GuestAddrs.account_writes_undo_count
          (GuestAddrs.account_writes_undo_push + 32)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.account_writes_undo_count (GuestAddrs.account_writes_undo_push + 32))
    (ubase + (36 : Word)) (by nofun)
  rw [hlaCount] at U9
  -- index 10: `ld t1, 0(t0)` — the journal cursor
  have U10 := ld_spec_gen_within .x6 .x5 undoPtr w6 undoCount (0 : BitVec 12)
    (ubase + (40 : Word)) (by nofun)
  rw [show undoPtr + signExtend12 (0 : BitVec 12) = undoPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at U10
  -- index 11: `lui t2, 40` — the journal capacity, accountWritesUndoCapacity = 163840
  have U11 := lui_spec_gen_within .x7 w7 (40 : BitVec 20) (ubase + (44 : Word)) (by nofun)
  rw [show (((40 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64) = (163840 : Word) from by
    decide] at U11
  -- index 12: `bgeu t1, t2, .Lawup_full` — TAKEN, the journal is full
  have UB := bgeu_spec_gen_within .x6 .x7
    (brOff (GuestAddrs.account_writes_undo_push + 224)
      (GuestAddrs.account_writes_undo_push + 48))
    undoCount (163840 : Word) (ubase + (48 : Word))
  rw [hbr, show ubase + (48 : Word) + (176 : Word) = ubase + (224 : Word) from by bv_omega]
    at UB
  have U12 : cpsTripleWithin 1 (ubase + (48 : Word)) (ubase + (224 : Word))
      (CodeReq.singleton (ubase + (48 : Word)) (.BGEU .x6 .x7
        (brOff (GuestAddrs.account_writes_undo_push + 224)
          (GuestAddrs.account_writes_undo_push + 48))))
      ((.x6 ↦ᵣ undoCount) ** (.x7 ↦ᵣ (163840 : Word)))
      ((.x6 ↦ᵣ undoCount) ** (.x7 ↦ᵣ (163840 : Word))) :=
    cpsBranchWithin_takenStripPure2 UB (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact hfull h_pure.2)
  -- index 56: `li a0, 1` — the failure return code
  have U13 := li_spec_gen_within .x10 w10 (1 : Word) (ubase + (224 : Word)) (by nofun)
  -- indices 57, 58: `la t3, tx_account_writes_overflow`
  have U14 := auipc_spec_gen_within .x28 w28
    (laHi GuestAddrs.tx_account_writes_overflow (GuestAddrs.account_writes_undo_push + 228))
    (ubase + (228 : Word)) (by nofun)
  have U15 := addi_spec_gen_same_within .x28
    ((ubase + (228 : Word)) +
      (((laHi GuestAddrs.tx_account_writes_overflow
          (GuestAddrs.account_writes_undo_push + 228)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.tx_account_writes_overflow (GuestAddrs.account_writes_undo_push + 228))
    (ubase + (232 : Word)) (by nofun)
  rw [hlaTx] at U15
  -- index 59: latch the transaction-level sticky flag
  have U16 := sd_spec_gen_within .x28 .x10 txOvfPtr (1 : Word) ovfTx (0 : BitVec 12)
    (ubase + (236 : Word))
  rw [show txOvfPtr + signExtend12 (0 : BitVec 12) = txOvfPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at U16
  -- indices 60, 61: `la t3, account_writes_overflow`
  have U17 := auipc_spec_gen_within .x28 txOvfPtr
    (laHi GuestAddrs.account_writes_overflow (GuestAddrs.account_writes_undo_push + 240))
    (ubase + (240 : Word)) (by nofun)
  have U18 := addi_spec_gen_same_within .x28
    ((ubase + (240 : Word)) +
      (((laHi GuestAddrs.account_writes_overflow
          (GuestAddrs.account_writes_undo_push + 240)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.account_writes_overflow (GuestAddrs.account_writes_undo_push + 240))
    (ubase + (244 : Word)) (by nofun)
  rw [hlaBlk] at U18
  -- index 62: latch the block-level sticky flag
  have U19 := sd_spec_gen_within .x28 .x10 blkOvfPtr (1 : Word) ovfBlk (0 : BitVec 12)
    (ubase + (248 : Word))
  rw [show blkOvfPtr + signExtend12 (0 : BitVec 12) = blkOvfPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at U19
  -- indices 63..69: reload t0..t6
  have U20 := ld_spec_gen_within .x5 .x2 (sp2 - (64 : Word)) undoPtr w5 (0 : BitVec 12)
    (ubase + (252 : Word)) (by nofun)
  rw [show (sp2 - (64 : Word)) + signExtend12 (0 : BitVec 12) = sp2 - (64 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at U20
  have U21 := ld_spec_gen_within .x6 .x2 (sp2 - (64 : Word)) undoCount w6 (8 : BitVec 12)
    (ubase + (256 : Word)) (by nofun)
  rw [show (sp2 - (64 : Word)) + signExtend12 (8 : BitVec 12) = sp2 - (56 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at U21
  have U22 := ld_spec_gen_within .x7 .x2 (sp2 - (64 : Word)) (163840 : Word) w7
    (16 : BitVec 12) (ubase + (260 : Word)) (by nofun)
  rw [show (sp2 - (64 : Word)) + signExtend12 (16 : BitVec 12) = sp2 - (48 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at U22
  have U23 := ld_spec_gen_within .x28 .x2 (sp2 - (64 : Word)) blkOvfPtr w28 (24 : BitVec 12)
    (ubase + (264 : Word)) (by nofun)
  rw [show (sp2 - (64 : Word)) + signExtend12 (24 : BitVec 12) = sp2 - (40 : Word) from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]; bv_omega] at U23
  have U24 := ld_spec_gen_within .x29 .x2 (sp2 - (64 : Word)) w29 w29 (32 : BitVec 12)
    (ubase + (268 : Word)) (by nofun)
  rw [show (sp2 - (64 : Word)) + signExtend12 (32 : BitVec 12) = sp2 - (32 : Word) from by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]; bv_omega] at U24
  have U25 := ld_spec_gen_within .x30 .x2 (sp2 - (64 : Word)) w30 w30 (40 : BitVec 12)
    (ubase + (272 : Word)) (by nofun)
  rw [show (sp2 - (64 : Word)) + signExtend12 (40 : BitVec 12) = sp2 - (24 : Word) from by
    rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]; bv_omega] at U25
  have U26 := ld_spec_gen_within .x31 .x2 (sp2 - (64 : Word)) w31 w31 (48 : BitVec 12)
    (ubase + (276 : Word)) (by nofun)
  rw [show (sp2 - (64 : Word)) + signExtend12 (48 : BitVec 12) = sp2 - (16 : Word) from by
    rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide]; bv_omega] at U26
  -- index 70: `addi sp, sp, 64`
  have U27 := addi_spec_gen_same_within .x2 (sp2 - (64 : Word)) (64 : BitVec 12)
    (ubase + (280 : Word)) (by nofun)
  rw [show (sp2 - (64 : Word)) + signExtend12 (64 : BitVec 12) = sp2 from by
    rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide]; bv_omega] at U27
  -- index 71: `ret`
  have U28 := EvmAsm.Evm64.ret_spec_within' (ubase + (284 : Word)) retA
  runBlock U0 U1 U2 U3 U4 U5 U6 U7 U8 U9 U10 U11 U12 U13 U14 U15 U16 U17 U18 U19 U20
    U21 U22 U23 U24 U25 U26 U27 U28

/-! ## Segment C — the caller's reject arm and the epilogue -/

/-- `account_write_record` instruction 56 and 127..143 (`base + 224`, then
    `base + 508 .. base + 572`): the caller sees `a0 ≠ 0` from
    `account_writes_undo_push`, takes the `bne` to `.Lawr_overflow`, latches
    both sticky flags a second time, restores `t0`-`t6`, `ra` and `sp`, and
    returns.

    ⚠️ The epilogue does NOT reload `a0`-`a7`: they are spilled by the
    prologue and re-read as argument scratch, never restored.  The post
    therefore carries the clobbered values through.

    Nothing is written to `TX_ACCOUNT_WRITES_AREA` and
    `tx_account_writes_count` is never even addressed on this arm — both facts
    come for free from the universally quantified `pcFree` frame, since neither
    appears in the pre or the post. -/
theorem accountWriteRecord_segC_body_spec
    (base sp ra link retVal txOvfPtr blkOvfPtr ovfTx ovfBlk
      v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31
      u5 u6 u7 u28 u29 u30 u31 : Word)
    (hbr : signExtend13 (brOff (GuestAddrs.account_write_record + 508)
        (GuestAddrs.account_write_record + 224)) = (284 : Word))
    (hlaTx : base + (508 : Word) +
        (((laHi GuestAddrs.tx_account_writes_overflow
            (GuestAddrs.account_write_record + 508)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.tx_account_writes_overflow
          (GuestAddrs.account_write_record + 508)) = txOvfPtr)
    (hlaBlk : base + (524 : Word) +
        (((laHi GuestAddrs.account_writes_overflow
            (GuestAddrs.account_write_record + 524)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.account_writes_overflow
          (GuestAddrs.account_write_record + 524)) = blkOvfPtr)
    (hfail : retVal ≠ (0 : Word)) :
    cpsTripleWithin 18 (base + (224 : Word)) (ra &&& ~~~(1 : Word))
      (CodeReq.ofProg base accountWriteRecord_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ link) ** (.x2 ↦ᵣ (sp - (128 : Word))) **
       (.x10 ↦ᵣ retVal) **
       (.x5 ↦ᵣ u5) ** (.x6 ↦ᵣ u6) ** (.x7 ↦ᵣ u7) **
       (.x28 ↦ᵣ u28) ** (.x29 ↦ᵣ u29) ** (.x30 ↦ᵣ u30) ** (.x31 ↦ᵣ u31) **
       ((sp - (128 : Word)) ↦ₘ v5) ** ((sp - (120 : Word)) ↦ₘ v6) **
       ((sp - (112 : Word)) ↦ₘ v7) ** ((sp - (104 : Word)) ↦ₘ v28) **
       ((sp - (96 : Word)) ↦ₘ v29) ** ((sp - (88 : Word)) ↦ₘ v30) **
       ((sp - (80 : Word)) ↦ₘ v31) ** ((sp - (72 : Word)) ↦ₘ ra) **
       ((sp - (64 : Word)) ↦ₘ v10) ** ((sp - (56 : Word)) ↦ₘ v11) **
       ((sp - (48 : Word)) ↦ₘ v12) ** ((sp - (40 : Word)) ↦ₘ v13) **
       ((sp - (32 : Word)) ↦ₘ v14) ** ((sp - (24 : Word)) ↦ₘ v15) **
       ((sp - (16 : Word)) ↦ₘ v16) ** ((sp - (8 : Word)) ↦ₘ v17) **
       (txOvfPtr ↦ₘ ovfTx) ** (blkOvfPtr ↦ₘ ovfBlk))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ retVal) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       ((sp - (128 : Word)) ↦ₘ v5) ** ((sp - (120 : Word)) ↦ₘ v6) **
       ((sp - (112 : Word)) ↦ₘ v7) ** ((sp - (104 : Word)) ↦ₘ v28) **
       ((sp - (96 : Word)) ↦ₘ v29) ** ((sp - (88 : Word)) ↦ₘ v30) **
       ((sp - (80 : Word)) ↦ₘ v31) ** ((sp - (72 : Word)) ↦ₘ ra) **
       ((sp - (64 : Word)) ↦ₘ v10) ** ((sp - (56 : Word)) ↦ₘ v11) **
       ((sp - (48 : Word)) ↦ₘ v12) ** ((sp - (40 : Word)) ↦ₘ v13) **
       ((sp - (32 : Word)) ↦ₘ v14) ** ((sp - (24 : Word)) ↦ₘ v15) **
       ((sp - (16 : Word)) ↦ₘ v16) ** ((sp - (8 : Word)) ↦ₘ v17) **
       (txOvfPtr ↦ₘ (1 : Word)) ** (blkOvfPtr ↦ₘ (1 : Word))) := by
  unfold accountWriteRecord_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 56: `bne a0, zero, .Lawr_overflow` — TAKEN, the callee refused
  have RB := bne_spec_gen_within .x10 .x0
    (brOff (GuestAddrs.account_write_record + 508) (GuestAddrs.account_write_record + 224))
    retVal (0 : Word) (base + (224 : Word))
  rw [hbr, show base + (224 : Word) + (284 : Word) = base + (508 : Word) from by bv_omega]
    at RB
  have R0 : cpsTripleWithin 1 (base + (224 : Word)) (base + (508 : Word))
      (CodeReq.singleton (base + (224 : Word)) (.BNE .x10 .x0
        (brOff (GuestAddrs.account_write_record + 508)
          (GuestAddrs.account_write_record + 224))))
      ((.x10 ↦ᵣ retVal) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ retVal) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranchWithin_takenStripPure2 RB (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact hfail h_pure.2)
  -- indices 127, 128: `la t0, tx_account_writes_overflow`
  have R1 := auipc_spec_gen_within .x5 u5
    (laHi GuestAddrs.tx_account_writes_overflow (GuestAddrs.account_write_record + 508))
    (base + (508 : Word)) (by nofun)
  have R2 := addi_spec_gen_same_within .x5
    ((base + (508 : Word)) +
      (((laHi GuestAddrs.tx_account_writes_overflow
          (GuestAddrs.account_write_record + 508)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.tx_account_writes_overflow (GuestAddrs.account_write_record + 508))
    (base + (512 : Word)) (by nofun)
  rw [hlaTx] at R2
  -- index 129: `li t1, 1`
  have R3 := li_spec_gen_within .x6 u6 (1 : Word) (base + (516 : Word)) (by nofun)
  -- index 130: latch the transaction-level sticky flag
  have R4 := sd_spec_gen_within .x5 .x6 txOvfPtr (1 : Word) ovfTx (0 : BitVec 12)
    (base + (520 : Word))
  rw [show txOvfPtr + signExtend12 (0 : BitVec 12) = txOvfPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at R4
  -- indices 131, 132: `la t0, account_writes_overflow`
  have R5 := auipc_spec_gen_within .x5 txOvfPtr
    (laHi GuestAddrs.account_writes_overflow (GuestAddrs.account_write_record + 524))
    (base + (524 : Word)) (by nofun)
  have R6 := addi_spec_gen_same_within .x5
    ((base + (524 : Word)) +
      (((laHi GuestAddrs.account_writes_overflow
          (GuestAddrs.account_write_record + 524)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.account_writes_overflow (GuestAddrs.account_write_record + 524))
    (base + (528 : Word)) (by nofun)
  rw [hlaBlk] at R6
  -- index 133: latch the block-level sticky flag
  have R7 := sd_spec_gen_within .x5 .x6 blkOvfPtr (1 : Word) ovfBlk (0 : BitVec 12)
    (base + (532 : Word))
  rw [show blkOvfPtr + signExtend12 (0 : BitVec 12) = blkOvfPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at R7
  -- indices 134..141: reload t0..t6 and ra (NOT a0..a7)
  have R8 := ld_spec_gen_within .x5 .x2 (sp - (128 : Word)) blkOvfPtr v5 (0 : BitVec 12)
    (base + (536 : Word)) (by nofun)
  rw [show (sp - (128 : Word)) + signExtend12 (0 : BitVec 12) = sp - (128 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at R8
  have R9 := ld_spec_gen_within .x6 .x2 (sp - (128 : Word)) (1 : Word) v6 (8 : BitVec 12)
    (base + (540 : Word)) (by nofun)
  rw [show (sp - (128 : Word)) + signExtend12 (8 : BitVec 12) = sp - (120 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at R9
  have R10 := ld_spec_gen_within .x7 .x2 (sp - (128 : Word)) u7 v7 (16 : BitVec 12)
    (base + (544 : Word)) (by nofun)
  rw [show (sp - (128 : Word)) + signExtend12 (16 : BitVec 12) = sp - (112 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at R10
  have R11 := ld_spec_gen_within .x28 .x2 (sp - (128 : Word)) u28 v28 (24 : BitVec 12)
    (base + (548 : Word)) (by nofun)
  rw [show (sp - (128 : Word)) + signExtend12 (24 : BitVec 12) = sp - (104 : Word) from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]; bv_omega] at R11
  have R12 := ld_spec_gen_within .x29 .x2 (sp - (128 : Word)) u29 v29 (32 : BitVec 12)
    (base + (552 : Word)) (by nofun)
  rw [show (sp - (128 : Word)) + signExtend12 (32 : BitVec 12) = sp - (96 : Word) from by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]; bv_omega] at R12
  have R13 := ld_spec_gen_within .x30 .x2 (sp - (128 : Word)) u30 v30 (40 : BitVec 12)
    (base + (556 : Word)) (by nofun)
  rw [show (sp - (128 : Word)) + signExtend12 (40 : BitVec 12) = sp - (88 : Word) from by
    rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]; bv_omega] at R13
  have R14 := ld_spec_gen_within .x31 .x2 (sp - (128 : Word)) u31 v31 (48 : BitVec 12)
    (base + (560 : Word)) (by nofun)
  rw [show (sp - (128 : Word)) + signExtend12 (48 : BitVec 12) = sp - (80 : Word) from by
    rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide]; bv_omega] at R14
  have R15 := ld_spec_gen_within .x1 .x2 (sp - (128 : Word)) link ra (56 : BitVec 12)
    (base + (564 : Word)) (by nofun)
  rw [show (sp - (128 : Word)) + signExtend12 (56 : BitVec 12) = sp - (72 : Word) from by
    rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide]; bv_omega] at R15
  -- index 142: `addi sp, sp, 128`
  have R16 := addi_spec_gen_same_within .x2 (sp - (128 : Word)) (128 : BitVec 12)
    (base + (568 : Word)) (by nofun)
  rw [show (sp - (128 : Word)) + signExtend12 (128 : BitVec 12) = sp from by
    rw [show signExtend12 (128 : BitVec 12) = (128 : Word) from by decide]; bv_omega] at R16
  -- index 143: `ret`
  have R17 := EvmAsm.Evm64.ret_spec_within' (base + (572 : Word)) ra
  runBlock R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17

/-- `account_writes_undo_push`'s journal-full arm on the linked layout: entry
    AND `CodeReq` are both at `GuestAddrs.account_writes_undo_push`, which is
    the `GuestImageEntries.lean:417` pairing itself — a whole-routine claim in
    the `scripts/proof-frontier.py --shape` sense.  The three `la` round-trips
    and the `bgeu` displacement resolve by `decide` on the linked layout. -/
theorem accountWritesUndoPushFullFlat_spec
    (sp2 retA undoCount ovfTx ovfBlk w5 w6 w7 w10 w28 w29 w30 w31 : Word)
    (hfull : ¬ BitVec.ult undoCount (163840 : Word)) :
    cpsTripleWithin 29 (GuestAddrs.account_writes_undo_push : Word)
      (retA &&& ~~~(1 : Word))
      (CodeReq.ofProg (GuestAddrs.account_writes_undo_push : Word)
        accountWritesUndoPush_prog)
      ((.x1 ↦ᵣ retA) ** (.x2 ↦ᵣ sp2) ** (.x10 ↦ᵣ w10) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) **
       (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31) **
       memOwn (sp2 - (64 : Word)) ** memOwn (sp2 - (56 : Word)) **
       memOwn (sp2 - (48 : Word)) ** memOwn (sp2 - (40 : Word)) **
       memOwn (sp2 - (32 : Word)) ** memOwn (sp2 - (24 : Word)) **
       memOwn (sp2 - (16 : Word)) **
       ((GuestAddrs.account_writes_undo_count : Word) ↦ₘ undoCount) **
       ((GuestAddrs.tx_account_writes_overflow : Word) ↦ₘ ovfTx) **
       ((GuestAddrs.account_writes_overflow : Word) ↦ₘ ovfBlk))
      ((.x1 ↦ᵣ retA) ** (.x2 ↦ᵣ sp2) ** (.x10 ↦ᵣ (1 : Word)) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) **
       (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31) **
       ((sp2 - (64 : Word)) ↦ₘ w5) ** ((sp2 - (56 : Word)) ↦ₘ w6) **
       ((sp2 - (48 : Word)) ↦ₘ w7) ** ((sp2 - (40 : Word)) ↦ₘ w28) **
       ((sp2 - (32 : Word)) ↦ₘ w29) ** ((sp2 - (24 : Word)) ↦ₘ w30) **
       ((sp2 - (16 : Word)) ↦ₘ w31) **
       ((GuestAddrs.account_writes_undo_count : Word) ↦ₘ undoCount) **
       ((GuestAddrs.tx_account_writes_overflow : Word) ↦ₘ (1 : Word)) **
       ((GuestAddrs.account_writes_overflow : Word) ↦ₘ (1 : Word))) :=
  accountWritesUndoPush_full_body_spec (GuestAddrs.account_writes_undo_push : Word)
    sp2 retA
    (GuestAddrs.account_writes_undo_count : Word)
    (GuestAddrs.tx_account_writes_overflow : Word)
    (GuestAddrs.account_writes_overflow : Word)
    undoCount ovfTx ovfBlk w5 w6 w7 w10 w28 w29 w30 w31
    (by decide) (by decide) (by decide) (by decide) hfull

/-! ## The deployed (anchored) whole-routine contract -/

/-- The routine's linked entry. -/
abbrev AWR : Word := (GuestAddrs.account_write_record : Word)

/-- Its one callee on this arm's linked entry. -/
abbrev AWUP : Word := (GuestAddrs.account_writes_undo_push : Word)

/-- `account_write_record`'s code requirement: its own 144 instructions at
    `GuestAddrs.account_write_record`, plus the routine it calls on both the
    hit and the append arm.

    The union is FORCED, not a convenience: `account_write_record` has no arm
    that both terminates at `ret` and stays inside its own bytes.  The scan
    exits either into a `jal ra, account_writes_undo_push` (index 40 on the hit
    arm, index 55 on the append arm) or, after `txAccountWritesCapacity` =
    16384 iterations, into `.Lawr_overflow`.  So a whole-routine triple must
    range over the callee's bytes too. -/
def awrCR : CodeReq :=
  (CodeReq.ofProg (GuestAddrs.account_write_record : Word) accountWriteRecord_prog).union
    (CodeReq.ofProg (GuestAddrs.account_writes_undo_push : Word) accountWritesUndoPush_prog)

theorem awr_disj_undoPush :
    (CodeReq.ofProg AWR accountWriteRecord_prog).Disjoint
      (CodeReq.ofProg AWUP accountWritesUndoPush_prog) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem awrProg_sub_awrCR :
    ∀ a i, CodeReq.ofProg AWR accountWriteRecord_prog a = some i → awrCR a = some i :=
  CodeReq.union_mono_left

/-- Call-site adapter for the `jal ra, account_writes_undo_push` at instruction
    index 55 (`AWR + 220`) — the append arm's journal push. -/
theorem awr_callSite55 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n AWUP ((AWR + (220 : Word) + 4) &&& ~~~(1 : Word))
      (CodeReq.ofProg AWUP accountWritesUndoPush_prog)
      ((.x1 ↦ᵣ (AWR + (220 : Word) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (AWR + (220 : Word)) (AWR + (220 : Word) + 4) awrCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := AWR + (220 : Word)) (calleeEntry := AWUP) (vOld := vRa)
    (calleeCode := CodeReq.ofProg AWUP accountWritesUndoPush_prog)
    (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.account_writes_undo_push (GuestAddrs.account_write_record + 220))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at AWR (AWR + (220 : Word)) accountWriteRecord_prog 55 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right awr_disj_undoPush (fun _ _ h => h) a i h

/-- ⭐ **`account_write_record`, whole routine, fail-closed arm.**

    Entry `GuestAddrs.account_write_record`, exit `ra &&& ~~~1` — the caller's
    return address — over `awrCR`, which pairs the linked `GuestAddrs` entry
    with `accountWriteRecord_prog` exactly as `GuestImageEntries.lean:401` does.

    Two named gates select the arm:

    * `tx_account_writes_count = 0` — the transaction's account-write map is
      empty, i.e. this is the transaction's FIRST account write.  The scan's
      `bgeu` at index 24 is then taken with zero iterations, so no loop
      invariant is needed and the routine goes straight to `.Lawr_append`.
    * `hfull : ¬ account_writes_undo_count < 163840` — the undo journal is full
      (`accountWritesUndoCapacity`), so `account_writes_undo_push` refuses.

    Under both, the routine is **fail-closed**: it latches
    `tx_account_writes_overflow` and `account_writes_overflow` to 1, leaves
    `tx_account_writes_count` at 0, leaves `account_writes_undo_count`
    untouched, restores `sp` together with `t0`-`t6` and `ra`, and returns.
    Because `cpsTripleWithin` quantifies over an arbitrary `pcFree` frame, the
    triple ALSO says — for free — that nothing at all is written to
    `TX_ACCOUNT_WRITES_AREA` or to the account undo-journal arena, since
    neither is named in the pre or the post.

    ⚠️ `a0`, `a5` and `a6` are CLOBBERED and the post says so: `a0 = 1` is the
    callee's failure code, `a5 = 0` and `a6 = 1` are the push arguments
    materialised at indices 53/54.  `a1`-`a4` and `a7` survive only because
    this arm never touches them.  The epilogue reloads no `a` register on any
    path, contrary to the routine's docstring.

    ⚠️ NOT proven here: the hit arm, the append arm's zero-fill and masked
    field overlay, and the 16384-iteration `.Lawr_overflow` arm.  Those need
    the scan loop invariant and the account write-map vocabulary, and they are
    where the tie to `accountWriteUpsert` will be made. -/
theorem accountWriteRecordFailClosedFlat_spec
    (sp ra undoCount ovfTx ovfBlk v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17
      v28 v29 v30 v31 : Word)
    (hfull : ¬ BitVec.ult undoCount (163840 : Word)) :
    cpsTripleWithin 77 (GuestAddrs.account_write_record : Word) (ra &&& ~~~(1 : Word))
      awrCR
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
       (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       memOwn (sp - (192 : Word)) ** memOwn (sp - (184 : Word)) **
       memOwn (sp - (176 : Word)) ** memOwn (sp - (168 : Word)) **
       memOwn (sp - (160 : Word)) ** memOwn (sp - (152 : Word)) **
       memOwn (sp - (144 : Word)) **
       memOwn (sp - (128 : Word)) ** memOwn (sp - (120 : Word)) **
       memOwn (sp - (112 : Word)) ** memOwn (sp - (104 : Word)) **
       memOwn (sp - (96 : Word)) ** memOwn (sp - (88 : Word)) **
       memOwn (sp - (80 : Word)) ** memOwn (sp - (72 : Word)) **
       memOwn (sp - (64 : Word)) ** memOwn (sp - (56 : Word)) **
       memOwn (sp - (48 : Word)) ** memOwn (sp - (40 : Word)) **
       memOwn (sp - (32 : Word)) ** memOwn (sp - (24 : Word)) **
       memOwn (sp - (16 : Word)) ** memOwn (sp - (8 : Word)) **
       ((GuestAddrs.tx_account_writes_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.account_writes_undo_count : Word) ↦ₘ undoCount) **
       ((GuestAddrs.tx_account_writes_overflow : Word) ↦ₘ ovfTx) **
       ((GuestAddrs.account_writes_overflow : Word) ↦ₘ ovfBlk))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
       (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ (0 : Word)) ** (.x16 ↦ᵣ (1 : Word)) **
       (.x17 ↦ᵣ v17) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       ((sp - (192 : Word)) ↦ₘ (GuestAddrs.tx_account_writes_count : Word)) **
       ((sp - (184 : Word)) ↦ₘ (0 : Word)) **
       ((sp - (176 : Word)) ↦ₘ (16384 : Word)) **
       ((sp - (168 : Word)) ↦ₘ EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA) **
       ((sp - (160 : Word)) ↦ₘ (0 : Word)) **
       ((sp - (152 : Word)) ↦ₘ v30) ** ((sp - (144 : Word)) ↦ₘ v31) **
       ((sp - (128 : Word)) ↦ₘ v5) ** ((sp - (120 : Word)) ↦ₘ v6) **
       ((sp - (112 : Word)) ↦ₘ v7) ** ((sp - (104 : Word)) ↦ₘ v28) **
       ((sp - (96 : Word)) ↦ₘ v29) ** ((sp - (88 : Word)) ↦ₘ v30) **
       ((sp - (80 : Word)) ↦ₘ v31) ** ((sp - (72 : Word)) ↦ₘ ra) **
       ((sp - (64 : Word)) ↦ₘ v10) ** ((sp - (56 : Word)) ↦ₘ v11) **
       ((sp - (48 : Word)) ↦ₘ v12) ** ((sp - (40 : Word)) ↦ₘ v13) **
       ((sp - (32 : Word)) ↦ₘ v14) ** ((sp - (24 : Word)) ↦ₘ v15) **
       ((sp - (16 : Word)) ↦ₘ v16) ** ((sp - (8 : Word)) ↦ₘ v17) **
       ((GuestAddrs.tx_account_writes_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.account_writes_undo_count : Word) ↦ₘ undoCount) **
       ((GuestAddrs.tx_account_writes_overflow : Word) ↦ₘ (1 : Word)) **
       ((GuestAddrs.account_writes_overflow : Word) ↦ₘ (1 : Word))) := by
  -- segment A: prologue .. the empty-map `bgeu`
  have hA := cpsTripleWithin_extend_code awrProg_sub_awrCR
    (accountWriteRecord_segA_body_spec AWR sp ra
      (GuestAddrs.tx_account_writes_count : Word) v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17
      v28 v29 v30 v31
      (by decide) (by decide))
  -- the callee's frame slots and the three globals it touches are not in
  -- segment A's footprint; carry them across it by the frame rule
  have hA := cpsTripleWithin_frameR
    (memOwn (sp - (192 : Word)) ** memOwn (sp - (184 : Word)) **
     memOwn (sp - (176 : Word)) ** memOwn (sp - (168 : Word)) **
     memOwn (sp - (160 : Word)) ** memOwn (sp - (152 : Word)) **
     memOwn (sp - (144 : Word)) **
     ((GuestAddrs.account_writes_undo_count : Word) ↦ₘ undoCount) **
     ((GuestAddrs.tx_account_writes_overflow : Word) ↦ₘ ovfTx) **
     ((GuestAddrs.account_writes_overflow : Word) ↦ₘ ovfBlk))
    (by pcf) hA
  -- segment B: the capacity gate and the call arguments
  have hB := cpsTripleWithin_extend_code awrProg_sub_awrCR
    (accountWriteRecord_segB_body_spec AWR v7 v15 v16)
  -- the callee, on its journal-full arm
  have hU := accountWritesUndoPush_full_body_spec AWUP (sp - (128 : Word))
    (AWR + (220 : Word) + 4)
    (GuestAddrs.account_writes_undo_count : Word)
    (GuestAddrs.tx_account_writes_overflow : Word)
    (GuestAddrs.account_writes_overflow : Word)
    undoCount ovfTx ovfBlk
    (GuestAddrs.tx_account_writes_count : Word) (0 : Word) (16384 : Word) v10
    EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA (0 : Word) v30 v31
    (by decide) (by decide) (by decide) (by decide) hfull
  rw [show (sp - (128 : Word)) - (64 : Word) = sp - (192 : Word) from by bv_omega,
      show (sp - (128 : Word)) - (56 : Word) = sp - (184 : Word) from by bv_omega,
      show (sp - (128 : Word)) - (48 : Word) = sp - (176 : Word) from by bv_omega,
      show (sp - (128 : Word)) - (40 : Word) = sp - (168 : Word) from by bv_omega,
      show (sp - (128 : Word)) - (32 : Word) = sp - (160 : Word) from by bv_omega,
      show (sp - (128 : Word)) - (24 : Word) = sp - (152 : Word) from by bv_omega,
      show (sp - (128 : Word)) - (16 : Word) = sp - (144 : Word) from by bv_omega] at hU
  have hCall := awr_callSite55 (n := 29) ra (by pcf) hU
  rw [show AWR + (220 : Word) + 4 = AWR + (224 : Word) from by bv_omega] at hCall
  -- segment C: the reject arm and the epilogue
  have hC := cpsTripleWithin_extend_code awrProg_sub_awrCR
    (accountWriteRecord_segC_body_spec AWR sp ra (AWR + (224 : Word)) (1 : Word)
      (GuestAddrs.tx_account_writes_overflow : Word)
      (GuestAddrs.account_writes_overflow : Word) (1 : Word) (1 : Word)
      v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31
      (GuestAddrs.tx_account_writes_count : Word) (0 : Word) (16384 : Word)
      EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA (0 : Word) v30 v31
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
    163840 capacity), both sticky flags starting at 0, and the eleven saved
    temporaries `1..7, 11..14`.  The post is fully concrete: the twenty-three
    spill slots hold their saved values in spill order (the callee's seven
    carrying the scan state the caller had live at the call — the count
    pointer, 0, the capacity 16384, the arena base
    `TX_ACCOUNT_WRITES_AREA`, 0, and `t5`/`t6`), `sp` is back at
    `0x30000000`, `tx_account_writes_count` still reads 0, the undo cursor is
    still 200000, and BOTH overflow flags now read 1.  `a0`/`a5`/`a6` come back
    as 1/0/1, NOT as their entry values — the clobber, stated. -/
example (ra : Word) :
    cpsTripleWithin 77 (GuestAddrs.account_write_record : Word) (ra &&& ~~~(1 : Word))
      awrCR
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (0x30000000 : Word)) **
       (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (2 : Word)) ** (.x7 ↦ᵣ (3 : Word)) **
       (.x10 ↦ᵣ (20 : Word)) ** (.x11 ↦ᵣ (21 : Word)) ** (.x12 ↦ᵣ (22 : Word)) **
       (.x13 ↦ᵣ (23 : Word)) ** (.x14 ↦ᵣ (24 : Word)) ** (.x15 ↦ᵣ (25 : Word)) **
       (.x16 ↦ᵣ (26 : Word)) ** (.x17 ↦ᵣ (27 : Word)) **
       (.x28 ↦ᵣ (4 : Word)) ** (.x29 ↦ᵣ (5 : Word)) ** (.x30 ↦ᵣ (6 : Word)) **
       (.x31 ↦ᵣ (7 : Word)) **
       memOwn (0x2fffff40 : Word) **
       memOwn (0x2fffff48 : Word) **
       memOwn (0x2fffff50 : Word) **
       memOwn (0x2fffff58 : Word) **
       memOwn (0x2fffff60 : Word) **
       memOwn (0x2fffff68 : Word) **
       memOwn (0x2fffff70 : Word) **
       memOwn (0x2fffff80 : Word) **
       memOwn (0x2fffff88 : Word) **
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
       memOwn (0x2ffffff8 : Word) **
       ((GuestAddrs.tx_account_writes_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.account_writes_undo_count : Word) ↦ₘ (200000 : Word)) **
       ((GuestAddrs.tx_account_writes_overflow : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.account_writes_overflow : Word) ↦ₘ (0 : Word)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (0x30000000 : Word)) **
       (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (2 : Word)) ** (.x7 ↦ᵣ (3 : Word)) **
       (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ (21 : Word)) ** (.x12 ↦ᵣ (22 : Word)) **
       (.x13 ↦ᵣ (23 : Word)) ** (.x14 ↦ᵣ (24 : Word)) ** (.x15 ↦ᵣ (0 : Word)) **
       (.x16 ↦ᵣ (1 : Word)) ** (.x17 ↦ᵣ (27 : Word)) **
       (.x28 ↦ᵣ (4 : Word)) ** (.x29 ↦ᵣ (5 : Word)) ** (.x30 ↦ᵣ (6 : Word)) **
       (.x31 ↦ᵣ (7 : Word)) **
       ((0x2fffff40 : Word) ↦ₘ (GuestAddrs.tx_account_writes_count : Word)) **
       ((0x2fffff48 : Word) ↦ₘ (0 : Word)) **
       ((0x2fffff50 : Word) ↦ₘ (16384 : Word)) **
       ((0x2fffff58 : Word) ↦ₘ EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA) **
       ((0x2fffff60 : Word) ↦ₘ (0 : Word)) **
       ((0x2fffff68 : Word) ↦ₘ (6 : Word)) **
       ((0x2fffff70 : Word) ↦ₘ (7 : Word)) **
       ((0x2fffff80 : Word) ↦ₘ (1 : Word)) **
       ((0x2fffff88 : Word) ↦ₘ (2 : Word)) **
       ((0x2fffff90 : Word) ↦ₘ (3 : Word)) **
       ((0x2fffff98 : Word) ↦ₘ (4 : Word)) **
       ((0x2fffffa0 : Word) ↦ₘ (5 : Word)) **
       ((0x2fffffa8 : Word) ↦ₘ (6 : Word)) **
       ((0x2fffffb0 : Word) ↦ₘ (7 : Word)) **
       ((0x2fffffb8 : Word) ↦ₘ ra) **
       ((0x2fffffc0 : Word) ↦ₘ (20 : Word)) **
       ((0x2fffffc8 : Word) ↦ₘ (21 : Word)) **
       ((0x2fffffd0 : Word) ↦ₘ (22 : Word)) **
       ((0x2fffffd8 : Word) ↦ₘ (23 : Word)) **
       ((0x2fffffe0 : Word) ↦ₘ (24 : Word)) **
       ((0x2fffffe8 : Word) ↦ₘ (25 : Word)) **
       ((0x2ffffff0 : Word) ↦ₘ (26 : Word)) **
       ((0x2ffffff8 : Word) ↦ₘ (27 : Word)) **
       ((GuestAddrs.tx_account_writes_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.account_writes_undo_count : Word) ↦ₘ (200000 : Word)) **
       ((GuestAddrs.tx_account_writes_overflow : Word) ↦ₘ (1 : Word)) **
       ((GuestAddrs.account_writes_overflow : Word) ↦ₘ (1 : Word))) := by
  have h := accountWriteRecordFailClosedFlat_spec (0x30000000 : Word) ra
    (200000 : Word) 0 0 1 2 3 20 21 22 23 24 25 26 27 4 5 6 7 (by decide)
  rw [
      show (0x30000000 : Word) - (192 : Word) = (0x2fffff40 : Word) from by decide,
      show (0x30000000 : Word) - (184 : Word) = (0x2fffff48 : Word) from by decide,
      show (0x30000000 : Word) - (176 : Word) = (0x2fffff50 : Word) from by decide,
      show (0x30000000 : Word) - (168 : Word) = (0x2fffff58 : Word) from by decide,
      show (0x30000000 : Word) - (160 : Word) = (0x2fffff60 : Word) from by decide,
      show (0x30000000 : Word) - (152 : Word) = (0x2fffff68 : Word) from by decide,
      show (0x30000000 : Word) - (144 : Word) = (0x2fffff70 : Word) from by decide,
      show (0x30000000 : Word) - (128 : Word) = (0x2fffff80 : Word) from by decide,
      show (0x30000000 : Word) - (120 : Word) = (0x2fffff88 : Word) from by decide,
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
      show (0x30000000 : Word) - (16 : Word) = (0x2ffffff0 : Word) from by decide,
      show (0x30000000 : Word) - (8 : Word) = (0x2ffffff8 : Word) from by decide] at h
  exact h

/-- **Gate witnesses and negative controls.**

    1. `¬ 200000 <ᵤ 163840` inhabits `hfull` — a journal past
       `accountWritesUndoCapacity`.
    2. `¬ ¬ 0 <ᵤ 163840` is provably FALSE, so the arm genuinely EXCLUDES the
       ordinary case of an empty undo journal rather than covering it silently.
       (`account_writes_undo_push` then falls through to its append path at
       index 13 instead of branching to `+224`.)
    3. `0 <ᵤ 16384` and `¬ 0 <ᵤ 0`: with an empty transaction map the scan's
       `bgeu` at index 24 IS taken with zero iterations, and the capacity
       `bgeu` at index 52 is NOT — which is why this arm needs no loop
       invariant.  A non-empty map (`count = 1`) makes the first one FALSE, so
       the hit / append / 16384-iteration arms really are outside the triple.
    4. The two arms of the caller's `bne` at index 56 are distinct addresses,
       so "taken" is a real restriction. -/
example :
    (¬ BitVec.ult (200000 : Word) (163840 : Word))
    ∧ ¬ (¬ BitVec.ult (0 : Word) (163840 : Word))
    ∧ (¬ BitVec.ult (0 : Word) (0 : Word))
    ∧ ¬ (¬ BitVec.ult (0 : Word) (1 : Word))
    ∧ BitVec.ult (0 : Word) (16384 : Word)
    ∧ (GuestAddrs.account_write_record + 228 ≠ GuestAddrs.account_write_record + 508) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Satisfiability of the numeric instance's precondition.**  All twenty-three
    frame slots and all four globals are valid, 8-byte-aligned dword addresses,
    and the four globals are pairwise distinct and disjoint from the frame — so
    the separating conjunction is inhabitable and the numeric post above is not
    vacuously true. -/
example :
    isValidDwordAccess (0x2fffff40 : Word) = true ∧
    isValidDwordAccess (0x2fffff48 : Word) = true ∧
    isValidDwordAccess (0x2fffff50 : Word) = true ∧
    isValidDwordAccess (0x2fffff58 : Word) = true ∧
    isValidDwordAccess (0x2fffff60 : Word) = true ∧
    isValidDwordAccess (0x2fffff68 : Word) = true ∧
    isValidDwordAccess (0x2fffff70 : Word) = true ∧
    isValidDwordAccess (0x2fffff80 : Word) = true ∧
    isValidDwordAccess (0x2fffff88 : Word) = true ∧
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
    isValidDwordAccess (0x2ffffff8 : Word) = true ∧
    isValidDwordAccess (GuestAddrs.tx_account_writes_count : Word) = true ∧
    isValidDwordAccess (GuestAddrs.account_writes_undo_count : Word) = true ∧
    isValidDwordAccess (GuestAddrs.tx_account_writes_overflow : Word) = true ∧
    isValidDwordAccess (GuestAddrs.account_writes_overflow : Word) = true ∧
    (GuestAddrs.tx_account_writes_count : Word)
      ≠ (GuestAddrs.account_writes_undo_count : Word) ∧
    (GuestAddrs.tx_account_writes_overflow : Word)
      ≠ (GuestAddrs.account_writes_overflow : Word) ∧
    (GuestAddrs.tx_account_writes_count : Word) ≠ (0x2fffff40 : Word) ∧
    (GuestAddrs.account_writes_overflow : Word) ≠ (0x2ffffff8 : Word) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   by decide, by decide, by decide⟩

/-! ## Axiom audit — classical-only. -/

#print axioms accountWritesUndoPush_full_body_spec
#print axioms accountWritesUndoPushFullFlat_spec
#print axioms accountWriteRecordFailClosedFlat_spec

end EvmAsm.Codegen.Proofs
