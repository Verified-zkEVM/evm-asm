/-
  EvmAsm.Codegen.Proofs.WriteSetsRestoreFrameSpec

  **The `write_sets_restore_frame` machine triple — nothing-to-undo arm (#12127).**

  `write_sets_restore_frame` (`Codegen/Programs/StorageWriteMap.lean`,
  `writeSetsRestoreFrame_prog`, 81 instructions at
  `GuestAddrs.write_sets_restore_frame` = `0x80021198`, image entry
  `GuestImageEntries.lean:400`) is the storage-write half of a call-frame
  revert: it takes the frame's undo-journal mark in `a0` and replays
  `STORAGE_WRITES_UNDO_AREA` backwards down to that mark — writing back the
  previous value of each overwrite, decrementing `tx_storage_writes_count`
  for each append, re-materialising a displaced 128-byte row for the
  `wasAbsent = 2` records — and then resets the cursor to the mark.

  ## What this module proves

  `writeSetsRestoreFrameEmptyFlat_spec`, a 31-step whole-routine triple
  entry → `ret` under one named gate:

  * `hnone : ¬ (a0 <ᵤ storage_writes_undo_count)` — the caller's mark is at
    or above the current journal cursor, i.e. **the frame journalled
    nothing**, so the `bgeu a0, t1` at instruction index 18 (`base + 72`) is
    TAKEN and the replay loop runs zero iterations.

  Under that gate the routine is a pure cursor reset: `storage_writes_undo_count`
  ends holding `a0`, `sp` and all seven prologue-saved temporaries come back
  intact, and `a0`/`ra` are untouched.  Because `cpsTripleWithin` universally
  quantifies over a `pcFree` frame, the triple ALSO says — for free, since
  none of them is named in the pre or the post — that **nothing** is written
  to `TX_STORAGE_WRITES_AREA`, to `tx_storage_writes_count`, or to the
  undo-journal arena itself.  That is the spec-side content of the
  "a frame that wrote nothing is restored by a cursor reset alone" claim the
  routine's docstring currently makes only in prose, and it is the reason a
  nested frame's revert cannot corrupt its parent's write map.

  ## Why the `CodeReq` is `ofProg` alone, and not a union

  Unlike `storage_write_record` (see `StorageWriteRecordSpec.lean`, whose
  `swrCR` is a FORCED union because every terminating path leaves the
  routine's own bytes), `write_sets_restore_frame` is **call-free**: its
  Program contains no `JAL x1` at all — every jump is a local `JAL x0` and
  the only `JALR` is the `x0`-linked `ret`.  So the code requirement is
  exactly `CodeReq.ofProg (GuestAddrs.write_sets_restore_frame)
  writeSetsRestoreFrame_prog`, the `GuestImageEntries.lean:400` pairing
  itself — entry AND `CodeReq` are both at the anchor.

  ## ⚠️ What is deliberately NOT proven

  The replay loop (indices 19..68): the `wasAbsent = 0` value write-back, the
  `wasAbsent = 1` count decrement, and the `wasAbsent = 2` 128-byte row copy
  at indices 55..62.  Those need the journal's record invariant and the
  `storageWritesMapIs` vocabulary
  (`Stateless/State/WriteMapAssertions.lean`), and they are where the machine
  will be tied to the already-proven model `storageWriteUpsert`
  (`Stateless/State/StorageWriteUpsert.lean:142`).  The registry row is
  therefore `.conditional` with the gate named.

  ## Mechanics

  Same idiom as `StorageWriteRecordSpec`: present the code requirement as the
  `singleton`-union chain (`unfold` + `CodeReq.ofProg_cons`) before
  `runBlock`, and write every offset `(k : Word)`.  The two `la
  storage_writes_undo_count` round-trips (indices 8/9 and 69/70) and the
  `bgeu` displacement resolve by `decide` on the linked layout.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only
  (audited by the `#print axioms` at the end of this file).
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Codegen.Programs.StorageWriteMap

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen

/-! ## Frame-offset arithmetic, hoisted out of the proof

  ⚠️ **Measured, not stylistic.**  `bv_omega` expands to
  `simp only [bitvec_to_nat] at * <;> omega`, and the `at *` walks the whole
  local context.  Inside the body proof below that context carries
  `hlaCount0`/`hlaCount1`/`hbr` — hypotheses whose `laHi`/`laLo`/`brOff`
  applications `omega` then tries to evaluate.  With them in scope the very
  first `sd` frame-offset rewrite costs ~254 s on its own; with them cleared
  it costs milliseconds.  So every offset identity the body proof needs is
  proved HERE, at file scope, where the context is one or two `Word`s. -/

/-- `(sp − 64) + off = sp − (64 − off)` for a spill slot at `off` bytes into a
    64-byte frame, with the 12-bit immediate's sign extension discharged by the
    caller (`hi`) and the complement by `hk`. -/
private theorem wsrf_slot (sp2 : Word) (i : BitVec 12) (d k : Word)
    (hi : signExtend12 i = d) (hk : d + k = (64 : Word)) :
    (sp2 - (64 : Word)) + signExtend12 i = sp2 - k := by
  subst hi; bv_omega

/-- The prologue's `addi sp, sp, -64`. -/
private theorem wsrf_push (sp2 : Word) :
    sp2 + signExtend12 (-64 : BitVec 12) = sp2 - (64 : Word) := by
  rw [show signExtend12 (-64 : BitVec 12) = (-64 : Word) from by decide]; bv_omega

/-- The epilogue's `addi sp, sp, 64`. -/
private theorem wsrf_pop (sp2 : Word) :
    (sp2 - (64 : Word)) + signExtend12 (64 : BitVec 12) = sp2 := by
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide]; bv_omega

/-- The taken `bgeu` at instruction index 18 (`base + 72`) lands at
    `base + 276`, instruction index 69. -/
private theorem wsrf_brTarget (base : Word) :
    base + (72 : Word) + (204 : Word) = base + (276 : Word) := by bv_omega

/-! ## The nothing-to-undo arm at a free `base` -/

/-- `write_sets_restore_frame` at a free `base`, on the **nothing-to-undo**
    arm: indices 0..18 (the 7-slot prologue, `la t0,
    storage_writes_undo_count`, `ld t1`, the two arena-base immediate
    materialisations into `t3`/`t6`, and the `bgeu a0, t1` — TAKEN, because
    the caller's mark is at or above the cursor) followed by indices 69..80
    at `base + 276` (re-`la` the cursor, store the mark into it, reload the
    seven temporaries, pop the frame, `ret`).

    The journal arena is never addressed and `tx_storage_writes_count` is
    never even materialised on this arm — both facts come for free from the
    universally quantified `pcFree` frame, since neither appears in the pre
    or the post. -/
theorem writeSetsRestoreFrame_empty_body_spec
    (base sp2 retA undoPtr undoCount a0
      w5 w6 w7 w28 w29 w30 w31 : Word)
    (hlaCount0 : base + (32 : Word) +
        (((laHi GuestAddrs.storage_writes_undo_count
            (GuestAddrs.write_sets_restore_frame + 32)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.storage_writes_undo_count
          (GuestAddrs.write_sets_restore_frame + 32)) = undoPtr)
    (hlaCount1 : base + (276 : Word) +
        (((laHi GuestAddrs.storage_writes_undo_count
            (GuestAddrs.write_sets_restore_frame + 276)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.storage_writes_undo_count
          (GuestAddrs.write_sets_restore_frame + 276)) = undoPtr)
    (hbr : signExtend13 (brOff (GuestAddrs.write_sets_restore_frame + 276)
        (GuestAddrs.write_sets_restore_frame + 72)) = (204 : Word))
    (hnone : ¬ BitVec.ult a0 undoCount) :
    cpsTripleWithin 31 base (retA &&& ~~~(1 : Word))
      (CodeReq.ofProg base writeSetsRestoreFrame_prog)
      ((.x1 ↦ᵣ retA) ** (.x2 ↦ᵣ sp2) ** (.x10 ↦ᵣ a0) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) **
       (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31) **
       memOwn (sp2 - (64 : Word)) ** memOwn (sp2 - (56 : Word)) **
       memOwn (sp2 - (48 : Word)) ** memOwn (sp2 - (40 : Word)) **
       memOwn (sp2 - (32 : Word)) ** memOwn (sp2 - (24 : Word)) **
       memOwn (sp2 - (16 : Word)) **
       (undoPtr ↦ₘ undoCount))
      ((.x1 ↦ᵣ retA) ** (.x2 ↦ᵣ sp2) ** (.x10 ↦ᵣ a0) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) **
       (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31) **
       ((sp2 - (64 : Word)) ↦ₘ w5) ** ((sp2 - (56 : Word)) ↦ₘ w6) **
       ((sp2 - (48 : Word)) ↦ₘ w7) ** ((sp2 - (40 : Word)) ↦ₘ w28) **
       ((sp2 - (32 : Word)) ↦ₘ w29) ** ((sp2 - (24 : Word)) ↦ₘ w30) **
       ((sp2 - (16 : Word)) ↦ₘ w31) **
       (undoPtr ↦ₘ a0)) := by
  -- ⚠️ The `unfold` + `CodeReq.ofProg_cons` expansion is deliberately deferred
  -- to just before `runBlock`.  `bv_omega` runs `simp only [bitvec_to_nat] at *`,
  -- which walks the GOAL as well as the context; with the 81-instruction
  -- `CodeReq.singleton` union chain already in the goal, the very first frame
  -- offset rewrite below costs ~127 s on its own (measured).  Keeping the code
  -- requirement folded while the address arithmetic is discharged brings the
  -- whole declaration back under the default heartbeat budget.
  -- index 0: `addi sp, sp, -64`
  have R0 := addi_spec_gen_same_within .x2 sp2 (-64 : BitVec 12) base (by nofun)
  rw [wsrf_push sp2] at R0
  -- indices 1..7: spill t0..t6
  have R1 := sd_spec_gen_own_within .x2 .x5 (sp2 - (64 : Word)) w5 (0 : BitVec 12)
    (base + (4 : Word))
  rw [show (sp2 - (64 : Word)) + signExtend12 (0 : BitVec 12) = sp2 - (64 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at R1
  have R2 := sd_spec_gen_own_within .x2 .x6 (sp2 - (64 : Word)) w6 (8 : BitVec 12)
    (base + (8 : Word))
  rw [wsrf_slot sp2 (8 : BitVec 12) (8 : Word) (56 : Word) (by decide) (by decide)] at R2
  have R3 := sd_spec_gen_own_within .x2 .x7 (sp2 - (64 : Word)) w7 (16 : BitVec 12)
    (base + (12 : Word))
  rw [wsrf_slot sp2 (16 : BitVec 12) (16 : Word) (48 : Word) (by decide) (by decide)] at R3
  have R4 := sd_spec_gen_own_within .x2 .x28 (sp2 - (64 : Word)) w28 (24 : BitVec 12)
    (base + (16 : Word))
  rw [wsrf_slot sp2 (24 : BitVec 12) (24 : Word) (40 : Word) (by decide) (by decide)] at R4
  have R5 := sd_spec_gen_own_within .x2 .x29 (sp2 - (64 : Word)) w29 (32 : BitVec 12)
    (base + (20 : Word))
  rw [wsrf_slot sp2 (32 : BitVec 12) (32 : Word) (32 : Word) (by decide) (by decide)] at R5
  have R6 := sd_spec_gen_own_within .x2 .x30 (sp2 - (64 : Word)) w30 (40 : BitVec 12)
    (base + (24 : Word))
  rw [wsrf_slot sp2 (40 : BitVec 12) (40 : Word) (24 : Word) (by decide) (by decide)] at R6
  have R7 := sd_spec_gen_own_within .x2 .x31 (sp2 - (64 : Word)) w31 (48 : BitVec 12)
    (base + (28 : Word))
  rw [wsrf_slot sp2 (48 : BitVec 12) (48 : Word) (16 : Word) (by decide) (by decide)] at R7
  -- indices 8, 9: `la t0, storage_writes_undo_count`
  have R8 := auipc_spec_gen_within .x5 w5
    (laHi GuestAddrs.storage_writes_undo_count (GuestAddrs.write_sets_restore_frame + 32))
    (base + (32 : Word)) (by nofun)
  have R9 := addi_spec_gen_same_within .x5
    ((base + (32 : Word)) +
      (((laHi GuestAddrs.storage_writes_undo_count
          (GuestAddrs.write_sets_restore_frame + 32)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.storage_writes_undo_count (GuestAddrs.write_sets_restore_frame + 32))
    (base + (36 : Word)) (by nofun)
  rw [hlaCount0] at R9
  -- index 10: `ld t1, 0(t0)` — the journal cursor
  have R10 := ld_spec_gen_within .x6 .x5 undoPtr w6 undoCount (0 : BitVec 12)
    (base + (40 : Word)) (by nofun)
  rw [show undoPtr + signExtend12 (0 : BitVec 12) = undoPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at R10
  -- indices 11..13: the journal base `STORAGE_WRITES_UNDO_AREA` = 0xBBBCD000 into t3
  have R11 := lui_spec_gen_within .x28 w28 storageWritesUndoLuiImm
    (base + (44 : Word)) (by nofun)
  rw [show ((storageWritesUndoLuiImm.zeroExtend 32 <<< 12).signExtend 64)
      = (770048 : Word) from by decide] at R11
  have R12 := addiw_spec_gen_same_within .x28 (770048 : Word) storageWritesUndoAddiwImm
    (base + (48 : Word)) (by nofun)
  rw [show ((((770048 : Word).truncate 32 +
      (signExtend12 storageWritesUndoAddiwImm).truncate 32 : BitVec 32)).signExtend 64)
      = (768973 : Word) from by decide] at R12
  have R13 := slli_spec_gen_same_within .x28 (768973 : Word) (12 : BitVec 6)
    (base + (52 : Word)) (by nofun)
  rw [show ((768973 : Word) <<< (12 : BitVec 6).toNat) = EvmAsm.Stateless.STORAGE_WRITES_UNDO_AREA from by
    decide] at R13
  -- indices 14..17: the transaction write-map base `TX_STORAGE_WRITES_AREA` into t6
  have R14 := lui_spec_gen_within .x31 w31 (20 : BitVec 20) (base + (56 : Word)) (by nofun)
  rw [show (((20 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64) = (81920 : Word) from by
    decide] at R14
  have R15 := addiw_spec_gen_same_within .x31 (81920 : Word) (1451 : BitVec 12)
    (base + (60 : Word)) (by nofun)
  rw [show ((((81920 : Word).truncate 32 + (signExtend12 (1451 : BitVec 12)).truncate 32 :
      BitVec 32)).signExtend 64) = (83371 : Word) from by decide] at R15
  have R16 := slli_spec_gen_same_within .x31 (83371 : Word) (15 : BitVec 6)
    (base + (64 : Word)) (by nofun)
  rw [show ((83371 : Word) <<< (15 : BitVec 6).toNat) = (0xA2D58000 : Word) from by
    decide] at R16
  have R17 := addi_spec_gen_same_within .x31 (0xA2D58000 : Word) (-320 : BitVec 12)
    (base + (68 : Word)) (by nofun)
  rw [show (0xA2D58000 : Word) + signExtend12 (-320 : BitVec 12) = EvmAsm.Stateless.TX_STORAGE_WRITES_AREA from by
    decide] at R17
  -- index 18: `bgeu a0, t1, .Lwsrf_done` — TAKEN, the frame journalled nothing
  have RB := bgeu_spec_gen_within .x10 .x6
    (brOff (GuestAddrs.write_sets_restore_frame + 276)
      (GuestAddrs.write_sets_restore_frame + 72))
    a0 undoCount (base + (72 : Word))
  rw [hbr, wsrf_brTarget base] at RB
  have R18 : cpsTripleWithin 1 (base + (72 : Word)) (base + (276 : Word))
      (CodeReq.singleton (base + (72 : Word)) (.BGEU .x10 .x6
        (brOff (GuestAddrs.write_sets_restore_frame + 276)
          (GuestAddrs.write_sets_restore_frame + 72))))
      ((.x10 ↦ᵣ a0) ** (.x6 ↦ᵣ undoCount))
      ((.x10 ↦ᵣ a0) ** (.x6 ↦ᵣ undoCount)) :=
    cpsBranchWithin_takenStripPure2 RB (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact hnone h_pure.2)
  -- indices 69, 70: `la t0, storage_writes_undo_count`, second site
  have R19 := auipc_spec_gen_within .x5 undoPtr
    (laHi GuestAddrs.storage_writes_undo_count (GuestAddrs.write_sets_restore_frame + 276))
    (base + (276 : Word)) (by nofun)
  have R20 := addi_spec_gen_same_within .x5
    ((base + (276 : Word)) +
      (((laHi GuestAddrs.storage_writes_undo_count
          (GuestAddrs.write_sets_restore_frame + 276)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.storage_writes_undo_count (GuestAddrs.write_sets_restore_frame + 276))
    (base + (280 : Word)) (by nofun)
  rw [hlaCount1] at R20
  -- index 71: `sd a0, 0(t0)` — the cursor is reset to the caller's mark
  have R21 := sd_spec_gen_within .x5 .x10 undoPtr a0 undoCount (0 : BitVec 12)
    (base + (284 : Word))
  rw [show undoPtr + signExtend12 (0 : BitVec 12) = undoPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at R21
  -- indices 72..78: reload t0..t6
  have R22 := ld_spec_gen_within .x5 .x2 (sp2 - (64 : Word)) undoPtr w5 (0 : BitVec 12)
    (base + (288 : Word)) (by nofun)
  rw [show (sp2 - (64 : Word)) + signExtend12 (0 : BitVec 12) = sp2 - (64 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at R22
  have R23 := ld_spec_gen_within .x6 .x2 (sp2 - (64 : Word)) undoCount w6 (8 : BitVec 12)
    (base + (292 : Word)) (by nofun)
  rw [wsrf_slot sp2 (8 : BitVec 12) (8 : Word) (56 : Word) (by decide) (by decide)] at R23
  have R24 := ld_spec_gen_within .x7 .x2 (sp2 - (64 : Word)) w7 w7 (16 : BitVec 12)
    (base + (296 : Word)) (by nofun)
  rw [wsrf_slot sp2 (16 : BitVec 12) (16 : Word) (48 : Word) (by decide) (by decide)] at R24
  have R25 := ld_spec_gen_within .x28 .x2 (sp2 - (64 : Word)) EvmAsm.Stateless.STORAGE_WRITES_UNDO_AREA w28
    (24 : BitVec 12) (base + (300 : Word)) (by nofun)
  rw [wsrf_slot sp2 (24 : BitVec 12) (24 : Word) (40 : Word) (by decide) (by decide)] at R25
  have R26 := ld_spec_gen_within .x29 .x2 (sp2 - (64 : Word)) w29 w29 (32 : BitVec 12)
    (base + (304 : Word)) (by nofun)
  rw [wsrf_slot sp2 (32 : BitVec 12) (32 : Word) (32 : Word) (by decide) (by decide)] at R26
  have R27 := ld_spec_gen_within .x30 .x2 (sp2 - (64 : Word)) w30 w30 (40 : BitVec 12)
    (base + (308 : Word)) (by nofun)
  rw [wsrf_slot sp2 (40 : BitVec 12) (40 : Word) (24 : Word) (by decide) (by decide)] at R27
  have R28 := ld_spec_gen_within .x31 .x2 (sp2 - (64 : Word)) EvmAsm.Stateless.TX_STORAGE_WRITES_AREA w31
    (48 : BitVec 12) (base + (312 : Word)) (by nofun)
  rw [wsrf_slot sp2 (48 : BitVec 12) (48 : Word) (16 : Word) (by decide) (by decide)] at R28
  -- index 79: `addi sp, sp, 64`
  have R29 := addi_spec_gen_same_within .x2 (sp2 - (64 : Word)) (64 : BitVec 12)
    (base + (316 : Word)) (by nofun)
  rw [wsrf_pop sp2] at R29
  -- index 80: `ret`
  have R30 := EvmAsm.Evm64.ret_spec_within' (base + (320 : Word)) retA
  unfold writeSetsRestoreFrame_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  runBlock R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20
    R21 R22 R23 R24 R25 R26 R27 R28 R29 R30

/-! ## The deployed (anchored) whole-routine contract -/

/-- `write_sets_restore_frame`'s nothing-to-undo arm on the linked layout:
    entry AND `CodeReq` are both at `GuestAddrs.write_sets_restore_frame`,
    which is the `GuestImageEntries.lean:400` pairing itself — a
    whole-routine claim in the `scripts/proof-frontier.py --shape` sense.
    The two `la` round-trips and the `bgeu` displacement resolve by `decide`
    on the linked layout. -/
theorem writeSetsRestoreFrameEmptyFlat_spec
    (sp2 retA undoCount a0 w5 w6 w7 w28 w29 w30 w31 : Word)
    (hnone : ¬ BitVec.ult a0 undoCount) :
    cpsTripleWithin 31 (GuestAddrs.write_sets_restore_frame : Word)
      (retA &&& ~~~(1 : Word))
      (CodeReq.ofProg (GuestAddrs.write_sets_restore_frame : Word)
        writeSetsRestoreFrame_prog)
      ((.x1 ↦ᵣ retA) ** (.x2 ↦ᵣ sp2) ** (.x10 ↦ᵣ a0) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) **
       (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31) **
       memOwn (sp2 - (64 : Word)) ** memOwn (sp2 - (56 : Word)) **
       memOwn (sp2 - (48 : Word)) ** memOwn (sp2 - (40 : Word)) **
       memOwn (sp2 - (32 : Word)) ** memOwn (sp2 - (24 : Word)) **
       memOwn (sp2 - (16 : Word)) **
       ((GuestAddrs.storage_writes_undo_count : Word) ↦ₘ undoCount))
      ((.x1 ↦ᵣ retA) ** (.x2 ↦ᵣ sp2) ** (.x10 ↦ᵣ a0) **
       (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) **
       (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31) **
       ((sp2 - (64 : Word)) ↦ₘ w5) ** ((sp2 - (56 : Word)) ↦ₘ w6) **
       ((sp2 - (48 : Word)) ↦ₘ w7) ** ((sp2 - (40 : Word)) ↦ₘ w28) **
       ((sp2 - (32 : Word)) ↦ₘ w29) ** ((sp2 - (24 : Word)) ↦ₘ w30) **
       ((sp2 - (16 : Word)) ↦ₘ w31) **
       ((GuestAddrs.storage_writes_undo_count : Word) ↦ₘ a0)) :=
  writeSetsRestoreFrame_empty_body_spec
    (GuestAddrs.write_sets_restore_frame : Word) sp2 retA
    (GuestAddrs.storage_writes_undo_count : Word)
    undoCount a0 w5 w6 w7 w28 w29 w30 w31
    (by decide) (by decide) (by decide) hnone

/-! ## Non-vacuity

  Three checks, in the shape `docs/agents` asks for: a fully numeric
  instance (so a `True`-shaped or trivially satisfiable post could not have
  passed), a positive witness for the gate together with a NEGATIVE control
  showing that the gate really excludes the inputs the routine is normally
  asked about, and a satisfiability check on the numeric precondition —
  `memOwn`/`↦ₘ` both *assert* `isValidDwordAccess`, so an unsatisfiable pre
  is a real risk rather than a formality. -/

/-- **Numeric instance.** `sp = 0x30000000`, a journal cursor of 0 (an empty
    journal), a mark of 0, and the seven saved temporaries `1..7`.  The post
    is fully concrete: the seven spill slots hold their saved values in
    spill order, `sp` is back at `0x30000000`, and
    `storage_writes_undo_count` reads the mark, 0. -/
theorem wsrfEmpty_numeric_instance (ra : Word) :
    cpsTripleWithin 31 (GuestAddrs.write_sets_restore_frame : Word)
      (ra &&& ~~~(1 : Word))
      (CodeReq.ofProg (GuestAddrs.write_sets_restore_frame : Word)
        writeSetsRestoreFrame_prog)
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (0x30000000 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (2 : Word)) ** (.x7 ↦ᵣ (3 : Word)) **
       (.x28 ↦ᵣ (4 : Word)) ** (.x29 ↦ᵣ (5 : Word)) ** (.x30 ↦ᵣ (6 : Word)) **
       (.x31 ↦ᵣ (7 : Word)) **
       memOwn (0x2fffffc0 : Word) ** memOwn (0x2fffffc8 : Word) **
       memOwn (0x2fffffd0 : Word) ** memOwn (0x2fffffd8 : Word) **
       memOwn (0x2fffffe0 : Word) ** memOwn (0x2fffffe8 : Word) **
       memOwn (0x2ffffff0 : Word) **
       ((GuestAddrs.storage_writes_undo_count : Word) ↦ₘ (0 : Word)))
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (0x30000000 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (2 : Word)) ** (.x7 ↦ᵣ (3 : Word)) **
       (.x28 ↦ᵣ (4 : Word)) ** (.x29 ↦ᵣ (5 : Word)) ** (.x30 ↦ᵣ (6 : Word)) **
       (.x31 ↦ᵣ (7 : Word)) **
       ((0x2fffffc0 : Word) ↦ₘ (1 : Word)) ** ((0x2fffffc8 : Word) ↦ₘ (2 : Word)) **
       ((0x2fffffd0 : Word) ↦ₘ (3 : Word)) ** ((0x2fffffd8 : Word) ↦ₘ (4 : Word)) **
       ((0x2fffffe0 : Word) ↦ₘ (5 : Word)) ** ((0x2fffffe8 : Word) ↦ₘ (6 : Word)) **
       ((0x2ffffff0 : Word) ↦ₘ (7 : Word)) **
       ((GuestAddrs.storage_writes_undo_count : Word) ↦ₘ (0 : Word))) :=
  writeSetsRestoreFrameEmptyFlat_spec (0x30000000 : Word) ra (0 : Word) (0 : Word)
    (1 : Word) (2 : Word) (3 : Word) (4 : Word) (5 : Word) (6 : Word) (7 : Word)
    (by decide)

/-- **Positive witness and NEGATIVE controls for the gate.**

    1. `¬ (0 <ᵤ 0)`: an empty journal with a zero mark IS inside the arm, so
       the numeric instance above is not vacuous.
    2. `¬ ¬ (0 <ᵤ 1)`: a mark of 0 against a cursor of 1 — one journalled
       record — is provably OUTSIDE the arm.  This is the negative control
       that matters: it is exactly the ordinary case the routine exists to
       serve, so the gate is a genuine restriction and not framing.  On that
       input the `bgeu` at index 18 falls through into the replay loop at
       index 19, which this module does not claim.
    3. The two arms of the `bgeu` at index 18 land at distinct addresses
       (`base + 76` versus `base + 276`), so "taken" is a real choice. -/
theorem wsrfEmpty_gate_reachable :
    (¬ BitVec.ult (0 : Word) (0 : Word))
    ∧ ¬ (¬ BitVec.ult (0 : Word) (1 : Word))
    ∧ ¬ (¬ BitVec.ult (5 : Word) (200000 : Word))
    ∧ (GuestAddrs.write_sets_restore_frame + 76
        ≠ GuestAddrs.write_sets_restore_frame + 276) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **Satisfiability of the numeric instance's precondition.**  All seven
    frame slots and the one global are valid, 8-byte-aligned dword
    addresses, and the global is disjoint from the frame — so the separating
    conjunction is inhabitable and the numeric post above is not vacuously
    true. -/
theorem wsrfEmpty_precondition_satisfiable :
    isValidDwordAccess (0x2fffffc0 : Word) = true ∧
    isValidDwordAccess (0x2fffffc8 : Word) = true ∧
    isValidDwordAccess (0x2fffffd0 : Word) = true ∧
    isValidDwordAccess (0x2fffffd8 : Word) = true ∧
    isValidDwordAccess (0x2fffffe0 : Word) = true ∧
    isValidDwordAccess (0x2fffffe8 : Word) = true ∧
    isValidDwordAccess (0x2ffffff0 : Word) = true ∧
    isValidDwordAccess (GuestAddrs.storage_writes_undo_count : Word) = true ∧
    (GuestAddrs.storage_writes_undo_count : Word) ≠ (0x2fffffc0 : Word) ∧
    (GuestAddrs.storage_writes_undo_count : Word) ≠ (0x2ffffff0 : Word) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   by decide, by decide, by decide⟩

/-! ## Axiom audit — classical-only. -/

#print axioms writeSetsRestoreFrame_empty_body_spec
#print axioms writeSetsRestoreFrameEmptyFlat_spec
#print axioms wsrfEmpty_numeric_instance
#print axioms wsrfEmpty_gate_reachable
#print axioms wsrfEmpty_precondition_satisfiable

end EvmAsm.Codegen.Proofs
