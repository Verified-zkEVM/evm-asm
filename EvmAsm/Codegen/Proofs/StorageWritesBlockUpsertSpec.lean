/-
  EvmAsm.Codegen.Proofs.StorageWritesBlockUpsertSpec

  **The `storage_writes_block_upsert` machine triple — first-row append
  arm (#11921).**

  `storage_writes_block_upsert` (`Codegen/Programs/StorageWriteMap.lean`,
  `storageWritesBlockUpsert_prog`, 105 instructions at
  `GuestAddrs.storage_writes_block_upsert`, image entry
  `Codegen/Proofs/GuestImageEntries.lean:396`) is the block-level half of the
  storage write merge, factored out of `storage_write_record` so the promotion
  boundary reads as one loop over one operation.  Its ABI:

      a0 = rowAddress ptr (32 B)   a1 = slotKey ptr (32 B)
      a2 = value ptr (32 B)        a3 = baseline ptr (32 B), or 0

  and its 128-byte row is `+0` rowAddress, `+32` slotKey, `+64` value,
  `+96` baseline (zero-filled when `a3 = 0` — the APPEND-only rule that keeps
  a pre-block baseline alive across later overwrites; dropping it made
  zero-clears of nonzero parents look unchanged, the 7251 multi-block
  residual).

  ## ⭐ Why the `CodeReq` here is a SINGLE `ofProg`, and the writers' is not

  `Codegen/Proofs/StorageWriteRecordSpec.lean` and
  `Codegen/Proofs/AccountWriteRecordSpec.lean` both had to state their arms
  over a two-program UNION `CodeReq`, because neither of those routines has an
  arm that terminates at `ret` without either leaving its own bytes through a
  `jal ra, …undo_push` or first running a capacity-sized scan.

  **This routine is different, and the difference is checked rather than
  assumed.**  `storageWritesBlockUpsert_prog` contains no `jal ra, …` at all:
  every `JAL` in it is a `JAL .x0` internal jump, and the only
  register-indirect transfer is the closing `jalr x0, 0(ra)`.  It is a LEAF —
  the block-level upsert pushes no undo record, which is exactly why it could
  be factored out of `storage_write_record` in the first place.  So the
  whole-routine triple below is stated over the plain
  `CodeReq.ofProg (GuestAddrs.storage_writes_block_upsert : Word)
  storageWritesBlockUpsert_prog` — entry AND code requirement anchored at the
  same `GuestImageEntries` pairing, no callee contract needed, no union.

  ## What this module proves

  `storageWritesBlockUpsertAppendFlat_spec`, a 63-step whole-routine triple
  entry → `ret` under two named gates:

  * `storage_writes_count ↦ₘ 0` — the block's storage-write map is EMPTY, so
    the scan's `bgeu t4, t1` at instruction index 16 is taken with ZERO
    iterations and no loop invariant is needed;
  * `a3 = 0` — a null baseline pointer, so the `beq a3, x0` at index 67
    selects `.Lswbu_base_zero` (the four-dword zero fill at `+96 .. +120`)
    rather than the baseline copy.

  Under those, this is a **fully FUNCTIONAL arm, not a fail-closed one** — the
  first genuinely value-producing whole-routine triple in the #11921 write-map
  family.  The post says the routine

  * writes row 0 at `STORAGE_WRITES_AREA`: the caller's four rowAddress dwords
    at `+0 .. +24`, four slotKey dwords at `+32 .. +56`, four value dwords at
    `+64 .. +88`, and four ZERO dwords at `+96 .. +120`;
  * bumps `storage_writes_count` from 0 to 1;
  * restores `sp` and ALL seven callee-spilled temporaries `t0`-`t6`, and
    leaves `a0`-`a3` and `ra` untouched.

  Because `cpsTripleWithin` universally quantifies over a `pcFree` frame, the
  triple ALSO says — for free, since they are not named in the pre or the
  post — that nothing outside those seventeen dwords is written: no other
  arena row, no overflow flag, no undo journal.

  ⚠️ **Register discipline, read from the epilogue rather than a docstring.**
  #13182 records that `account_write_record`'s prologue spills `a0`-`a7` and
  no arm restores them, contradicting its docstring.  This routine does NOT
  have that asymmetry: indices 96..102 reload exactly the seven registers
  indices 1..7 spilled (`t0`-`t6`), the frame is popped at 103, and `a0`-`a3`
  are read-only argument pointers that are never written at all.  The post
  below states full restoration because the code actually does it.

  ## ⚠️ What is deliberately NOT proven

  The HIT arm (indices 17..45 — the eight-comparison row match and the
  `.Lswbu_hit` overlay), the baseline-COPY arm (indices 68..75, taken when
  `a3 ≠ 0`), and the `.Lswbu_overflow` arm at index 92, which latches
  `storage_writes_overflow` and is reachable only once the count has already
  driven `blockStorageWritesCapacity` = 66666 scan iterations.  Those need the
  scan's loop invariant (measure `storage_writes_count − t4`) and the storage
  write-map row vocabulary.  The registry row is therefore `.conditional` with
  both gates named.

  ## `Nodup`

  #11921 asks what became of the writer's uniqueness clause.  Here it is
  neither proven nor assumed, and the reason is sharper than on the two
  fail-closed arms: on an EMPTY map the appended row is the ONLY row, so
  distinctness of the row sequence is degenerate — a one-element list is
  `Nodup` for free and the triple never needs to say so.  Uniqueness becomes a
  real obligation exactly when the scan can find a prior match, i.e. on the
  hit arm, which is outside this triple.  The model-side statement
  (`storageWriteUpsert_nodup`) is already hypothesis-free and is consumed when
  that arm is proved, not before.

  ## Mechanics

  Same pilot rules as `AccountWriteRecordSpec`: present the code requirement
  as the `singleton`-union chain (`unfold` + `CodeReq.ofProg_cons`) before
  `runBlock`, and write every offset `(k : Word)`.  Five segments compose with
  `seqFrame`.  There is no call-site adapter — the routine is a leaf.  The
  arena base the code materialises with a bare `LUI 162 / ADDIW 1333 /
  SLLI 12 / ADDI -1600` chain is carried through this proof SYMBOLICALLY:
  the intermediate is written `STORAGE_WRITES_AREA + 1600`, never as a bare
  in-range literal (`scripts/check-layout-literals.sh`, GH #12586).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only
  (audited by the `#print axioms` at the end of this file).
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.WP.Call
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Codegen.Programs.StorageWriteMap

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen

/-! ## Segment A — prologue, arena base, and the empty-map exit of the scan -/

/-- `storage_writes_block_upsert` instructions 0..16 at a free `base`: the
    seven-slot prologue (`t0`-`t6`), `la t0, storage_writes_count`, the
    four-instruction `STORAGE_WRITES_AREA` materialisation into `t3`,
    `li t4, 0`, and the scan's `bgeu` — TAKEN, because the block's
    storage-write map is empty (`countPtr ↦ₘ 0`).

    The arena chain is `lui 162 / addiw 1333 / slli 12 / addi -1600`; its
    post-shift intermediate is `STORAGE_WRITES_AREA + 1600`, written
    symbolically here so no bare in-range layout literal appears. -/
theorem storageWritesBlockUpsert_segA_body_spec
    (base sp ra countPtr v5 v6 v7 v28 v29 v30 v31 : Word)
    (hla : base + (32 : Word) +
        (((laHi GuestAddrs.storage_writes_count
            (GuestAddrs.storage_writes_block_upsert + 32)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.storage_writes_count
          (GuestAddrs.storage_writes_block_upsert + 32)) = countPtr)
    (hbr : signExtend13 (brOff (GuestAddrs.storage_writes_block_upsert + 184)
        (GuestAddrs.storage_writes_block_upsert + 64)) = (120 : Word)) :
    cpsTripleWithin 17 base (base + (184 : Word))
      (CodeReq.ofProg base storageWritesBlockUpsert_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       memOwn (sp - (64 : Word)) ** memOwn (sp - (56 : Word)) **
       memOwn (sp - (48 : Word)) ** memOwn (sp - (40 : Word)) **
       memOwn (sp - (32 : Word)) ** memOwn (sp - (24 : Word)) **
       memOwn (sp - (16 : Word)) **
       (countPtr ↦ₘ (0 : Word)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp - (64 : Word))) **
       (.x5 ↦ᵣ countPtr) ** (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ EvmAsm.Stateless.STORAGE_WRITES_AREA) ** (.x29 ↦ᵣ (0 : Word)) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       ((sp - (64 : Word)) ↦ₘ v5) ** ((sp - (56 : Word)) ↦ₘ v6) **
       ((sp - (48 : Word)) ↦ₘ v7) ** ((sp - (40 : Word)) ↦ₘ v28) **
       ((sp - (32 : Word)) ↦ₘ v29) ** ((sp - (24 : Word)) ↦ₘ v30) **
       ((sp - (16 : Word)) ↦ₘ v31) **
       (countPtr ↦ₘ (0 : Word))) := by
  unfold storageWritesBlockUpsert_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 0: `addi sp, sp, -64`
  have P0 := addi_spec_gen_same_within .x2 sp (-64 : BitVec 12) base (by nofun)
  rw [show signExtend12 (-64 : BitVec 12) = (-64 : Word) from by decide,
      show sp + (-64 : Word) = sp - (64 : Word) from by bv_omega] at P0
  -- indices 1..7: spill t0,t1,t2,t3,t4,t5,t6
  have P1 := sd_spec_gen_own_within .x2 .x5 (sp - (64 : Word)) v5 (0 : BitVec 12)
    (base + (4 : Word))
  rw [show (sp - (64 : Word)) + signExtend12 (0 : BitVec 12) = sp - (64 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at P1
  have P2 := sd_spec_gen_own_within .x2 .x6 (sp - (64 : Word)) v6 (8 : BitVec 12)
    (base + (8 : Word))
  rw [show (sp - (64 : Word)) + signExtend12 (8 : BitVec 12) = sp - (56 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at P2
  have P3 := sd_spec_gen_own_within .x2 .x7 (sp - (64 : Word)) v7 (16 : BitVec 12)
    (base + (12 : Word))
  rw [show (sp - (64 : Word)) + signExtend12 (16 : BitVec 12) = sp - (48 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at P3
  have P4 := sd_spec_gen_own_within .x2 .x28 (sp - (64 : Word)) v28 (24 : BitVec 12)
    (base + (16 : Word))
  rw [show (sp - (64 : Word)) + signExtend12 (24 : BitVec 12) = sp - (40 : Word) from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]; bv_omega] at P4
  have P5 := sd_spec_gen_own_within .x2 .x29 (sp - (64 : Word)) v29 (32 : BitVec 12)
    (base + (20 : Word))
  rw [show (sp - (64 : Word)) + signExtend12 (32 : BitVec 12) = sp - (32 : Word) from by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]; bv_omega] at P5
  have P6 := sd_spec_gen_own_within .x2 .x30 (sp - (64 : Word)) v30 (40 : BitVec 12)
    (base + (24 : Word))
  rw [show (sp - (64 : Word)) + signExtend12 (40 : BitVec 12) = sp - (24 : Word) from by
    rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]; bv_omega] at P6
  have P7 := sd_spec_gen_own_within .x2 .x31 (sp - (64 : Word)) v31 (48 : BitVec 12)
    (base + (28 : Word))
  rw [show (sp - (64 : Word)) + signExtend12 (48 : BitVec 12) = sp - (16 : Word) from by
    rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide]; bv_omega] at P7
  -- indices 8, 9: `la t0, storage_writes_count`
  have P8 := auipc_spec_gen_within .x5 v5
    (laHi GuestAddrs.storage_writes_count
      (GuestAddrs.storage_writes_block_upsert + 32))
    (base + (32 : Word)) (by nofun)
  have P9 := addi_spec_gen_same_within .x5
    ((base + (32 : Word)) +
      (((laHi GuestAddrs.storage_writes_count
          (GuestAddrs.storage_writes_block_upsert + 32)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.storage_writes_count
      (GuestAddrs.storage_writes_block_upsert + 32))
    (base + (36 : Word)) (by nofun)
  rw [hla] at P9
  -- index 10: `ld t1, 0(t0)` — the block-level row count
  have P10 := ld_spec_gen_within .x6 .x5 countPtr v6 (0 : Word) (0 : BitVec 12)
    (base + (40 : Word)) (by nofun)
  rw [show countPtr + signExtend12 (0 : BitVec 12) = countPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at P10
  -- indices 11..14: materialise STORAGE_WRITES_AREA into t3
  have P11 := lui_spec_gen_within .x28 v28 (162 : BitVec 20) (base + (44 : Word)) (by nofun)
  rw [show (((162 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64) = (663552 : Word) from by
    decide] at P11
  have P12 := addiw_spec_gen_same_within .x28 (663552 : Word) (1333 : BitVec 12)
    (base + (48 : Word)) (by nofun)
  rw [show ((((663552 : Word).truncate 32 +
      (signExtend12 (1333 : BitVec 12)).truncate 32 : BitVec 32)).signExtend 64)
      = (664885 : Word) from by decide] at P12
  have P13 := slli_spec_gen_same_within .x28 (664885 : Word) (12 : BitVec 6)
    (base + (52 : Word)) (by nofun)
  rw [show ((664885 : Word) <<< (12 : BitVec 6).toNat)
      = EvmAsm.Stateless.STORAGE_WRITES_AREA + (1600 : Word) from by decide] at P13
  have P14 := addi_spec_gen_same_within .x28
    (EvmAsm.Stateless.STORAGE_WRITES_AREA + (1600 : Word)) (-1600 : BitVec 12)
    (base + (56 : Word)) (by nofun)
  rw [show EvmAsm.Stateless.STORAGE_WRITES_AREA + (1600 : Word) +
      signExtend12 (-1600 : BitVec 12) = EvmAsm.Stateless.STORAGE_WRITES_AREA from by
    decide] at P14
  -- index 15: `li t4, 0` — the scan cursor
  have P15 := li_spec_gen_within .x29 v29 (0 : Word) (base + (60 : Word)) (by nofun)
  -- index 16: `bgeu t4, t1, .Lswbu_append` — TAKEN, the block map is empty
  have PB := bgeu_spec_gen_within .x29 .x6
    (brOff (GuestAddrs.storage_writes_block_upsert + 184)
      (GuestAddrs.storage_writes_block_upsert + 64))
    (0 : Word) (0 : Word) (base + (64 : Word))
  rw [hbr, show base + (64 : Word) + (120 : Word) = base + (184 : Word) from by bv_omega]
    at PB
  have P16 : cpsTripleWithin 1 (base + (64 : Word)) (base + (184 : Word))
      (CodeReq.singleton (base + (64 : Word)) (.BGEU .x29 .x6
        (brOff (GuestAddrs.storage_writes_block_upsert + 184)
          (GuestAddrs.storage_writes_block_upsert + 64))))
      ((.x29 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)))
      ((.x29 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word))) :=
    cpsBranchWithin_takenStripPure2 PB (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact absurd h_pure.2 (by decide))
  runBlock P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16

/-! ## Segment B — the arena-capacity gate -/

/-- `storage_writes_block_upsert` instructions 46..48
    (`base + 184 .. base + 196`): materialise `blockStorageWritesCapacity` =
    66666 into `t2` with `lui 16 / addiw 1130`, and take the capacity
    `bgeu t1, t2` NOT taken — the map is empty, so `0 < 66666` and the append
    proceeds instead of latching `storage_writes_overflow`. -/
theorem storageWritesBlockUpsert_segB_body_spec (base u7 : Word) :
    cpsTripleWithin 3 (base + (184 : Word)) (base + (196 : Word))
      (CodeReq.ofProg base storageWritesBlockUpsert_prog)
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ u7))
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (66666 : Word))) := by
  unfold storageWritesBlockUpsert_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 46: `lui t2, 16`
  have Q0 := lui_spec_gen_within .x7 u7 (16 : BitVec 20) (base + (184 : Word)) (by nofun)
  rw [show (((16 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64) = (65536 : Word) from by
    decide] at Q0
  -- index 47: `addiw t2, t2, 1130` — blockStorageWritesCapacity
  have Q1 := addiw_spec_gen_same_within .x7 (65536 : Word) (1130 : BitVec 12)
    (base + (188 : Word)) (by nofun)
  rw [show ((((65536 : Word).truncate 32 +
      (signExtend12 (1130 : BitVec 12)).truncate 32 : BitVec 32)).signExtend 64)
      = (66666 : Word) from by decide] at Q1
  -- index 48: `bgeu t1, t2, .Lswbu_overflow` — NOT taken, `0 < 66666`
  have QB := bgeu_spec_gen_within .x6 .x7
    (brOff (GuestAddrs.storage_writes_block_upsert + 368)
      (GuestAddrs.storage_writes_block_upsert + 192))
    (0 : Word) (66666 : Word) (base + (192 : Word))
  have Q2 : cpsTripleWithin 1 (base + (192 : Word)) (base + (192 : Word) + 4)
      (CodeReq.singleton (base + (192 : Word)) (.BGEU .x6 .x7
        (brOff (GuestAddrs.storage_writes_block_upsert + 368)
          (GuestAddrs.storage_writes_block_upsert + 192))))
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (66666 : Word)))
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (66666 : Word))) :=
    cpsBranchWithin_ntakenStripPure2 QB (fun hp hQt => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQt
      exact absurd h_pure.2 (by decide))
  rw [show base + (192 : Word) + 4 = base + (196 : Word) from by bv_omega] at Q2
  runBlock Q0 Q1 Q2

/-! ## Segment C — row base, the eight key dwords, and the null-baseline test -/

/-- `storage_writes_block_upsert` instructions 49..67
    (`base + 196 .. base + 308`): compute the append row base
    `t5 = t3 + (t1 << 7)` — with `t1 = 0` this is `STORAGE_WRITES_AREA`
    itself, row 0 — then copy the caller's four rowAddress dwords from `a0`
    into `+0 .. +24` and four slotKey dwords from `a1` into `+32 .. +56`, and
    take `beq a3, x0` TAKEN because the baseline pointer is null. -/
theorem storageWritesBlockUpsert_segC_body_spec
    (base keyPtr slotPtr u7 u30 k0 k1 k2 k3 s0 s1 s2 s3
      r0 r1 r2 r3 r4 r5 r6 r7 : Word) :
    cpsTripleWithin 19 (base + (196 : Word)) (base + (308 : Word))
      (CodeReq.ofProg base storageWritesBlockUpsert_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ u7) **
       (.x10 ↦ᵣ keyPtr) ** (.x11 ↦ᵣ slotPtr) ** (.x13 ↦ᵣ (0 : Word)) **
       (.x28 ↦ᵣ EvmAsm.Stateless.STORAGE_WRITES_AREA) ** (.x30 ↦ᵣ u30) **
       (keyPtr ↦ₘ k0) ** ((keyPtr + (8 : Word)) ↦ₘ k1) **
       ((keyPtr + (16 : Word)) ↦ₘ k2) ** ((keyPtr + (24 : Word)) ↦ₘ k3) **
       (slotPtr ↦ₘ s0) ** ((slotPtr + (8 : Word)) ↦ₘ s1) **
       ((slotPtr + (16 : Word)) ↦ₘ s2) ** ((slotPtr + (24 : Word)) ↦ₘ s3) **
       (EvmAsm.Stateless.STORAGE_WRITES_AREA ↦ₘ r0) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (8 : Word)) ↦ₘ r1) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (16 : Word)) ↦ₘ r2) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (24 : Word)) ↦ₘ r3) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (32 : Word)) ↦ₘ r4) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (40 : Word)) ↦ₘ r5) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (48 : Word)) ↦ₘ r6) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (56 : Word)) ↦ₘ r7))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ s3) **
       (.x10 ↦ᵣ keyPtr) ** (.x11 ↦ᵣ slotPtr) ** (.x13 ↦ᵣ (0 : Word)) **
       (.x28 ↦ᵣ EvmAsm.Stateless.STORAGE_WRITES_AREA) **
       (.x30 ↦ᵣ EvmAsm.Stateless.STORAGE_WRITES_AREA) **
       (keyPtr ↦ₘ k0) ** ((keyPtr + (8 : Word)) ↦ₘ k1) **
       ((keyPtr + (16 : Word)) ↦ₘ k2) ** ((keyPtr + (24 : Word)) ↦ₘ k3) **
       (slotPtr ↦ₘ s0) ** ((slotPtr + (8 : Word)) ↦ₘ s1) **
       ((slotPtr + (16 : Word)) ↦ₘ s2) ** ((slotPtr + (24 : Word)) ↦ₘ s3) **
       (EvmAsm.Stateless.STORAGE_WRITES_AREA ↦ₘ k0) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (8 : Word)) ↦ₘ k1) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (16 : Word)) ↦ₘ k2) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (24 : Word)) ↦ₘ k3) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (32 : Word)) ↦ₘ s0) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (40 : Word)) ↦ₘ s1) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (48 : Word)) ↦ₘ s2) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (56 : Word)) ↦ₘ s3)) := by
  unfold storageWritesBlockUpsert_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 49: `slli t5, t1, 7` — row stride 128, and `t1 = 0`
  have R0 := slli_spec_gen_within .x30 .x6 u30 (0 : Word) (7 : BitVec 6)
    (base + (196 : Word)) (by nofun)
  rw [show ((0 : Word) <<< (7 : BitVec 6).toNat) = (0 : Word) from by decide] at R0
  -- index 50: `add t5, t3, t5` — the append row base, row 0
  have R1 := add_spec_gen_rd_eq_rs2_within .x30 .x28
    EvmAsm.Stateless.STORAGE_WRITES_AREA (0 : Word) (base + (200 : Word)) (by nofun)
  rw [show EvmAsm.Stateless.STORAGE_WRITES_AREA + (0 : Word)
      = EvmAsm.Stateless.STORAGE_WRITES_AREA from BitVec.add_zero _] at R1
  -- indices 51..58: rowAddress, four dwords from a0 into +0 .. +24
  have R2 := ld_spec_gen_within .x7 .x10 keyPtr u7 k0 (0 : BitVec 12)
    (base + (204 : Word)) (by nofun)
  rw [show keyPtr + signExtend12 (0 : BitVec 12) = keyPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at R2
  have R3 := sd_spec_gen_within .x30 .x7 EvmAsm.Stateless.STORAGE_WRITES_AREA k0 r0
    (0 : BitVec 12) (base + (208 : Word))
  rw [show EvmAsm.Stateless.STORAGE_WRITES_AREA + signExtend12 (0 : BitVec 12)
      = EvmAsm.Stateless.STORAGE_WRITES_AREA from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at R3
  have R4 := ld_spec_gen_within .x7 .x10 keyPtr k0 k1 (8 : BitVec 12)
    (base + (212 : Word)) (by nofun)
  rw [show keyPtr + signExtend12 (8 : BitVec 12) = keyPtr + (8 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]] at R4
  have R5 := sd_spec_gen_within .x30 .x7 EvmAsm.Stateless.STORAGE_WRITES_AREA k1 r1
    (8 : BitVec 12) (base + (216 : Word))
  rw [show EvmAsm.Stateless.STORAGE_WRITES_AREA + signExtend12 (8 : BitVec 12)
      = EvmAsm.Stateless.STORAGE_WRITES_AREA + (8 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]] at R5
  have R6 := ld_spec_gen_within .x7 .x10 keyPtr k1 k2 (16 : BitVec 12)
    (base + (220 : Word)) (by nofun)
  rw [show keyPtr + signExtend12 (16 : BitVec 12) = keyPtr + (16 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]] at R6
  have R7 := sd_spec_gen_within .x30 .x7 EvmAsm.Stateless.STORAGE_WRITES_AREA k2 r2
    (16 : BitVec 12) (base + (224 : Word))
  rw [show EvmAsm.Stateless.STORAGE_WRITES_AREA + signExtend12 (16 : BitVec 12)
      = EvmAsm.Stateless.STORAGE_WRITES_AREA + (16 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]] at R7
  have R8 := ld_spec_gen_within .x7 .x10 keyPtr k2 k3 (24 : BitVec 12)
    (base + (228 : Word)) (by nofun)
  rw [show keyPtr + signExtend12 (24 : BitVec 12) = keyPtr + (24 : Word) from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]] at R8
  have R9 := sd_spec_gen_within .x30 .x7 EvmAsm.Stateless.STORAGE_WRITES_AREA k3 r3
    (24 : BitVec 12) (base + (232 : Word))
  rw [show EvmAsm.Stateless.STORAGE_WRITES_AREA + signExtend12 (24 : BitVec 12)
      = EvmAsm.Stateless.STORAGE_WRITES_AREA + (24 : Word) from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]] at R9
  -- indices 59..66: slotKey, four dwords from a1 into +32 .. +56
  have R10 := ld_spec_gen_within .x7 .x11 slotPtr k3 s0 (0 : BitVec 12)
    (base + (236 : Word)) (by nofun)
  rw [show slotPtr + signExtend12 (0 : BitVec 12) = slotPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at R10
  have R11 := sd_spec_gen_within .x30 .x7 EvmAsm.Stateless.STORAGE_WRITES_AREA s0 r4
    (32 : BitVec 12) (base + (240 : Word))
  rw [show EvmAsm.Stateless.STORAGE_WRITES_AREA + signExtend12 (32 : BitVec 12)
      = EvmAsm.Stateless.STORAGE_WRITES_AREA + (32 : Word) from by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]] at R11
  have R12 := ld_spec_gen_within .x7 .x11 slotPtr s0 s1 (8 : BitVec 12)
    (base + (244 : Word)) (by nofun)
  rw [show slotPtr + signExtend12 (8 : BitVec 12) = slotPtr + (8 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]] at R12
  have R13 := sd_spec_gen_within .x30 .x7 EvmAsm.Stateless.STORAGE_WRITES_AREA s1 r5
    (40 : BitVec 12) (base + (248 : Word))
  rw [show EvmAsm.Stateless.STORAGE_WRITES_AREA + signExtend12 (40 : BitVec 12)
      = EvmAsm.Stateless.STORAGE_WRITES_AREA + (40 : Word) from by
    rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]] at R13
  have R14 := ld_spec_gen_within .x7 .x11 slotPtr s1 s2 (16 : BitVec 12)
    (base + (252 : Word)) (by nofun)
  rw [show slotPtr + signExtend12 (16 : BitVec 12) = slotPtr + (16 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]] at R14
  have R15 := sd_spec_gen_within .x30 .x7 EvmAsm.Stateless.STORAGE_WRITES_AREA s2 r6
    (48 : BitVec 12) (base + (256 : Word))
  rw [show EvmAsm.Stateless.STORAGE_WRITES_AREA + signExtend12 (48 : BitVec 12)
      = EvmAsm.Stateless.STORAGE_WRITES_AREA + (48 : Word) from by
    rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide]] at R15
  have R16 := ld_spec_gen_within .x7 .x11 slotPtr s2 s3 (24 : BitVec 12)
    (base + (260 : Word)) (by nofun)
  rw [show slotPtr + signExtend12 (24 : BitVec 12) = slotPtr + (24 : Word) from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]] at R16
  have R17 := sd_spec_gen_within .x30 .x7 EvmAsm.Stateless.STORAGE_WRITES_AREA s3 r7
    (56 : BitVec 12) (base + (264 : Word))
  rw [show EvmAsm.Stateless.STORAGE_WRITES_AREA + signExtend12 (56 : BitVec 12)
      = EvmAsm.Stateless.STORAGE_WRITES_AREA + (56 : Word) from by
    rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide]] at R17
  -- index 67: `beq a3, x0, .Lswbu_base_zero` — TAKEN, the baseline is null
  have RB := beq_spec_gen_within .x13 .x0 (40 : BitVec 13) (0 : Word) (0 : Word)
    (base + (268 : Word))
  rw [show signExtend13 (40 : BitVec 13) = (40 : Word) from by decide,
      show base + (268 : Word) + (40 : Word) = base + (308 : Word) from by bv_omega] at RB
  have R18 : cpsTripleWithin 1 (base + (268 : Word)) (base + (308 : Word))
      (CodeReq.singleton (base + (268 : Word)) (.BEQ .x13 .x0 (40 : BitVec 13)))
      ((.x13 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x13 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranchWithin_takenStripPure2 RB (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact absurd h_pure.2 (by decide))
  runBlock R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18

/-! ## Segment D — the zero baseline, the count bump, and the value dwords -/

/-- `storage_writes_block_upsert` instructions 77..91
    (`base + 308 .. base + 384`): `.Lswbu_base_zero` writes four ZERO dwords
    into `+96 .. +120`, the row count goes 0 → 1 and is stored back, the
    caller's four value dwords are copied from `a2` into `+64 .. +88`, and the
    unconditional `j` at index 91 reaches the epilogue.

    ⭐ The `+96` baseline slot is APPEND-only by design: it records the value
    at the start of the interval this row represents, so
    `execution_map_state_changes` can compare `+64` against `+96` and decide
    whether the MPT actually changes.  Zero-filling it on a null baseline —
    rather than leaving it — is what makes a zero-clear of a nonzero parent
    visible. -/
theorem storageWritesBlockUpsert_segD_body_spec
    (base countPtr valPtr w7 n0 n1 n2 n3 b0 b1 b2 b3 c0 c1 c2 c3 : Word) :
    cpsTripleWithin 15 (base + (308 : Word)) (base + (384 : Word))
      (CodeReq.ofProg base storageWritesBlockUpsert_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ countPtr) ** (.x6 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ w7) ** (.x12 ↦ᵣ valPtr) **
       (.x30 ↦ᵣ EvmAsm.Stateless.STORAGE_WRITES_AREA) **
       (countPtr ↦ₘ (0 : Word)) **
       (valPtr ↦ₘ n0) ** ((valPtr + (8 : Word)) ↦ₘ n1) **
       ((valPtr + (16 : Word)) ↦ₘ n2) ** ((valPtr + (24 : Word)) ↦ₘ n3) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (64 : Word)) ↦ₘ c0) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (72 : Word)) ↦ₘ c1) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (80 : Word)) ↦ₘ c2) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (88 : Word)) ↦ₘ c3) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (96 : Word)) ↦ₘ b0) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (104 : Word)) ↦ₘ b1) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (112 : Word)) ↦ₘ b2) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (120 : Word)) ↦ₘ b3))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ countPtr) ** (.x6 ↦ᵣ (1 : Word)) **
       (.x7 ↦ᵣ n3) ** (.x12 ↦ᵣ valPtr) **
       (.x30 ↦ᵣ EvmAsm.Stateless.STORAGE_WRITES_AREA) **
       (countPtr ↦ₘ (1 : Word)) **
       (valPtr ↦ₘ n0) ** ((valPtr + (8 : Word)) ↦ₘ n1) **
       ((valPtr + (16 : Word)) ↦ₘ n2) ** ((valPtr + (24 : Word)) ↦ₘ n3) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (64 : Word)) ↦ₘ n0) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (72 : Word)) ↦ₘ n1) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (80 : Word)) ↦ₘ n2) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (88 : Word)) ↦ₘ n3) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (96 : Word)) ↦ₘ (0 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (104 : Word)) ↦ₘ (0 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (112 : Word)) ↦ₘ (0 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (120 : Word)) ↦ₘ (0 : Word))) := by
  unfold storageWritesBlockUpsert_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- indices 77..80: `.Lswbu_base_zero` — four zero dwords at +96 .. +120
  have S0 := sd_x0_spec_gen_within .x30 EvmAsm.Stateless.STORAGE_WRITES_AREA b0
    (96 : BitVec 12) (base + (308 : Word))
  rw [show EvmAsm.Stateless.STORAGE_WRITES_AREA + signExtend12 (96 : BitVec 12)
      = EvmAsm.Stateless.STORAGE_WRITES_AREA + (96 : Word) from by
    rw [show signExtend12 (96 : BitVec 12) = (96 : Word) from by decide]] at S0
  have S1 := sd_x0_spec_gen_within .x30 EvmAsm.Stateless.STORAGE_WRITES_AREA b1
    (104 : BitVec 12) (base + (312 : Word))
  rw [show EvmAsm.Stateless.STORAGE_WRITES_AREA + signExtend12 (104 : BitVec 12)
      = EvmAsm.Stateless.STORAGE_WRITES_AREA + (104 : Word) from by
    rw [show signExtend12 (104 : BitVec 12) = (104 : Word) from by decide]] at S1
  have S2 := sd_x0_spec_gen_within .x30 EvmAsm.Stateless.STORAGE_WRITES_AREA b2
    (112 : BitVec 12) (base + (316 : Word))
  rw [show EvmAsm.Stateless.STORAGE_WRITES_AREA + signExtend12 (112 : BitVec 12)
      = EvmAsm.Stateless.STORAGE_WRITES_AREA + (112 : Word) from by
    rw [show signExtend12 (112 : BitVec 12) = (112 : Word) from by decide]] at S2
  have S3 := sd_x0_spec_gen_within .x30 EvmAsm.Stateless.STORAGE_WRITES_AREA b3
    (120 : BitVec 12) (base + (320 : Word))
  rw [show EvmAsm.Stateless.STORAGE_WRITES_AREA + signExtend12 (120 : BitVec 12)
      = EvmAsm.Stateless.STORAGE_WRITES_AREA + (120 : Word) from by
    rw [show signExtend12 (120 : BitVec 12) = (120 : Word) from by decide]] at S3
  -- index 81: `addi t1, t1, 1` — the row count, 0 → 1
  have S4 := addi_spec_gen_same_within .x6 (0 : Word) (1 : BitVec 12)
    (base + (324 : Word)) (by nofun)
  rw [show (0 : Word) + signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at S4
  -- index 82: `sd t1, 0(t0)` — store it back
  have S5 := sd_spec_gen_within .x5 .x6 countPtr (1 : Word) (0 : Word) (0 : BitVec 12)
    (base + (328 : Word))
  rw [show countPtr + signExtend12 (0 : BitVec 12) = countPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at S5
  -- indices 83..90: value, four dwords from a2 into +64 .. +88
  have S6 := ld_spec_gen_within .x7 .x12 valPtr w7 n0 (0 : BitVec 12)
    (base + (332 : Word)) (by nofun)
  rw [show valPtr + signExtend12 (0 : BitVec 12) = valPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at S6
  have S7 := sd_spec_gen_within .x30 .x7 EvmAsm.Stateless.STORAGE_WRITES_AREA n0 c0
    (64 : BitVec 12) (base + (336 : Word))
  rw [show EvmAsm.Stateless.STORAGE_WRITES_AREA + signExtend12 (64 : BitVec 12)
      = EvmAsm.Stateless.STORAGE_WRITES_AREA + (64 : Word) from by
    rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide]] at S7
  have S8 := ld_spec_gen_within .x7 .x12 valPtr n0 n1 (8 : BitVec 12)
    (base + (340 : Word)) (by nofun)
  rw [show valPtr + signExtend12 (8 : BitVec 12) = valPtr + (8 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]] at S8
  have S9 := sd_spec_gen_within .x30 .x7 EvmAsm.Stateless.STORAGE_WRITES_AREA n1 c1
    (72 : BitVec 12) (base + (344 : Word))
  rw [show EvmAsm.Stateless.STORAGE_WRITES_AREA + signExtend12 (72 : BitVec 12)
      = EvmAsm.Stateless.STORAGE_WRITES_AREA + (72 : Word) from by
    rw [show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide]] at S9
  have S10 := ld_spec_gen_within .x7 .x12 valPtr n1 n2 (16 : BitVec 12)
    (base + (348 : Word)) (by nofun)
  rw [show valPtr + signExtend12 (16 : BitVec 12) = valPtr + (16 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]] at S10
  have S11 := sd_spec_gen_within .x30 .x7 EvmAsm.Stateless.STORAGE_WRITES_AREA n2 c2
    (80 : BitVec 12) (base + (352 : Word))
  rw [show EvmAsm.Stateless.STORAGE_WRITES_AREA + signExtend12 (80 : BitVec 12)
      = EvmAsm.Stateless.STORAGE_WRITES_AREA + (80 : Word) from by
    rw [show signExtend12 (80 : BitVec 12) = (80 : Word) from by decide]] at S11
  have S12 := ld_spec_gen_within .x7 .x12 valPtr n2 n3 (24 : BitVec 12)
    (base + (356 : Word)) (by nofun)
  rw [show valPtr + signExtend12 (24 : BitVec 12) = valPtr + (24 : Word) from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]] at S12
  have S13 := sd_spec_gen_within .x30 .x7 EvmAsm.Stateless.STORAGE_WRITES_AREA n3 c3
    (88 : BitVec 12) (base + (360 : Word))
  rw [show EvmAsm.Stateless.STORAGE_WRITES_AREA + signExtend12 (88 : BitVec 12)
      = EvmAsm.Stateless.STORAGE_WRITES_AREA + (88 : Word) from by
    rw [show signExtend12 (88 : BitVec 12) = (88 : Word) from by decide]] at S13
  -- index 91: `j` to the epilogue
  have S14 := jal_x0_spec_gen_within (20 : BitVec 21) (base + (364 : Word))
  rw [show signExtend21 (20 : BitVec 21) = (20 : Word) from by decide,
      show base + (364 : Word) + (20 : Word) = base + (384 : Word) from by bv_omega] at S14
  runBlock S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14

/-! ## Segment E — the epilogue -/

/-- `storage_writes_block_upsert` instructions 96..104
    (`base + 384 .. base + 416`): reload `t0`-`t6` from the frame, pop the
    64-byte frame, and `ret`.

    Unlike `account_write_record` (#13182), this epilogue reloads EXACTLY the
    seven registers the prologue spilled, so the whole-routine post below is
    an honest full-restoration claim.  `a0`-`a3` never appear here because the
    routine never writes them. -/
theorem storageWritesBlockUpsert_segE_body_spec
    (base sp ra v5 v6 v7 v28 v29 v30 v31 y5 y6 y7 y28 y29 y30 y31 : Word) :
    cpsTripleWithin 9 (base + (384 : Word)) (ra &&& ~~~(1 : Word))
      (CodeReq.ofProg base storageWritesBlockUpsert_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp - (64 : Word))) **
       (.x5 ↦ᵣ y5) ** (.x6 ↦ᵣ y6) ** (.x7 ↦ᵣ y7) **
       (.x28 ↦ᵣ y28) ** (.x29 ↦ᵣ y29) ** (.x30 ↦ᵣ y30) ** (.x31 ↦ᵣ y31) **
       ((sp - (64 : Word)) ↦ₘ v5) ** ((sp - (56 : Word)) ↦ₘ v6) **
       ((sp - (48 : Word)) ↦ₘ v7) ** ((sp - (40 : Word)) ↦ₘ v28) **
       ((sp - (32 : Word)) ↦ₘ v29) ** ((sp - (24 : Word)) ↦ₘ v30) **
       ((sp - (16 : Word)) ↦ₘ v31))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       ((sp - (64 : Word)) ↦ₘ v5) ** ((sp - (56 : Word)) ↦ₘ v6) **
       ((sp - (48 : Word)) ↦ₘ v7) ** ((sp - (40 : Word)) ↦ₘ v28) **
       ((sp - (32 : Word)) ↦ₘ v29) ** ((sp - (24 : Word)) ↦ₘ v30) **
       ((sp - (16 : Word)) ↦ₘ v31)) := by
  unfold storageWritesBlockUpsert_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  have T0 := ld_spec_gen_within .x5 .x2 (sp - (64 : Word)) y5 v5 (0 : BitVec 12)
    (base + (384 : Word)) (by nofun)
  rw [show (sp - (64 : Word)) + signExtend12 (0 : BitVec 12) = sp - (64 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at T0
  have T1 := ld_spec_gen_within .x6 .x2 (sp - (64 : Word)) y6 v6 (8 : BitVec 12)
    (base + (388 : Word)) (by nofun)
  rw [show (sp - (64 : Word)) + signExtend12 (8 : BitVec 12) = sp - (56 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at T1
  have T2 := ld_spec_gen_within .x7 .x2 (sp - (64 : Word)) y7 v7 (16 : BitVec 12)
    (base + (392 : Word)) (by nofun)
  rw [show (sp - (64 : Word)) + signExtend12 (16 : BitVec 12) = sp - (48 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at T2
  have T3 := ld_spec_gen_within .x28 .x2 (sp - (64 : Word)) y28 v28 (24 : BitVec 12)
    (base + (396 : Word)) (by nofun)
  rw [show (sp - (64 : Word)) + signExtend12 (24 : BitVec 12) = sp - (40 : Word) from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]; bv_omega] at T3
  have T4 := ld_spec_gen_within .x29 .x2 (sp - (64 : Word)) y29 v29 (32 : BitVec 12)
    (base + (400 : Word)) (by nofun)
  rw [show (sp - (64 : Word)) + signExtend12 (32 : BitVec 12) = sp - (32 : Word) from by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]; bv_omega] at T4
  have T5 := ld_spec_gen_within .x30 .x2 (sp - (64 : Word)) y30 v30 (40 : BitVec 12)
    (base + (404 : Word)) (by nofun)
  rw [show (sp - (64 : Word)) + signExtend12 (40 : BitVec 12) = sp - (24 : Word) from by
    rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]; bv_omega] at T5
  have T6 := ld_spec_gen_within .x31 .x2 (sp - (64 : Word)) y31 v31 (48 : BitVec 12)
    (base + (408 : Word)) (by nofun)
  rw [show (sp - (64 : Word)) + signExtend12 (48 : BitVec 12) = sp - (16 : Word) from by
    rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide]; bv_omega] at T6
  -- index 103: `addi sp, sp, 64`
  have T7 := addi_spec_gen_same_within .x2 (sp - (64 : Word)) (64 : BitVec 12)
    (base + (412 : Word)) (by nofun)
  rw [show (sp - (64 : Word)) + signExtend12 (64 : BitVec 12) = sp from by
    rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide]; bv_omega] at T7
  -- index 104: `ret`
  have T8 := EvmAsm.Evm64.ret_spec_within' (base + (416 : Word)) ra
  runBlock T0 T1 T2 T3 T4 T5 T6 T7 T8

/-! ## The deployed (anchored) whole-routine contract -/

/-- ⭐ **`storage_writes_block_upsert`, whole routine, first-row append arm.**

    Entry `GuestAddrs.storage_writes_block_upsert`, exit `ra &&& ~~~1` — the
    caller's return address — over
    `CodeReq.ofProg (GuestAddrs.storage_writes_block_upsert : Word)
    storageWritesBlockUpsert_prog`, which IS the
    `Codegen/Proofs/GuestImageEntries.lean:396` pairing.  Entry and code
    requirement are anchored at the same address, so this grades
    `whole-routine` under `scripts/proof-frontier.py`'s `shape_of_theorem`.

    ⭐ **A single `ofProg`, not a union — and that is checked.**  Both #11921
    WRITERS proved so far needed a two-program union because neither has a
    terminating arm that stays inside its own bytes.  This routine is a LEAF:
    `storageWritesBlockUpsert_prog` contains no `jal ra, …`, only `JAL .x0`
    internal jumps and the closing `jalr x0, 0(ra)` — the block-level upsert
    pushes no undo record.  No callee contract is needed and none is assumed.

    Two named gates select the arm:

    * `storage_writes_count = 0` — the block's storage-write map is empty, so
      the scan's `bgeu` at index 16 is taken with zero iterations;
    * `a3 = 0` — a null baseline pointer, so the `beq a3, x0` at index 67
      selects `.Lswbu_base_zero`.

    ⭐ Unlike the two fail-closed writer arms, this is a **fully FUNCTIONAL**
    triple.  The post says row 0 at `STORAGE_WRITES_AREA` receives the
    caller's four rowAddress dwords at `+0 .. +24`, four slotKey dwords at
    `+32 .. +56`, four value dwords at `+64 .. +88`, and four ZEROES at
    `+96 .. +120`; `storage_writes_count` goes 0 → 1; and `sp`, `ra`, `a0`-`a3`
    and all seven spilled temporaries `t0`-`t6` come back intact.  Because
    `cpsTripleWithin` quantifies over an arbitrary `pcFree` frame, the triple
    ALSO says — for free — that nothing outside those seventeen dwords is
    written: no other arena row, no overflow flag, no undo journal.

    ⚠️ NOT proven here: the hit arm (indices 17..45), the baseline-COPY arm
    (indices 68..75, `a3 ≠ 0`), and `.Lswbu_overflow` at index 92, which is
    reachable only after `blockStorageWritesCapacity` = 66666 scan iterations.
    Those need the scan's loop invariant, and they are where the tie to
    `storageWriteUpsert` will be made. -/
theorem storageWritesBlockUpsertAppendFlat_spec
    (sp ra keyPtr slotPtr valPtr
      v5 v6 v7 v28 v29 v30 v31
      k0 k1 k2 k3 s0 s1 s2 s3 n0 n1 n2 n3
      r0 r1 r2 r3 r4 r5 r6 r7 c0 c1 c2 c3 b0 b1 b2 b3 : Word) :
    cpsTripleWithin 63 (GuestAddrs.storage_writes_block_upsert : Word)
      (ra &&& ~~~(1 : Word))
      (CodeReq.ofProg (GuestAddrs.storage_writes_block_upsert : Word)
        storageWritesBlockUpsert_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ keyPtr) ** (.x11 ↦ᵣ slotPtr) ** (.x12 ↦ᵣ valPtr) **
       (.x13 ↦ᵣ (0 : Word)) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       memOwn (sp - (64 : Word)) ** memOwn (sp - (56 : Word)) **
       memOwn (sp - (48 : Word)) ** memOwn (sp - (40 : Word)) **
       memOwn (sp - (32 : Word)) ** memOwn (sp - (24 : Word)) **
       memOwn (sp - (16 : Word)) **
       ((GuestAddrs.storage_writes_count : Word) ↦ₘ (0 : Word)) **
       (keyPtr ↦ₘ k0) ** ((keyPtr + (8 : Word)) ↦ₘ k1) **
       ((keyPtr + (16 : Word)) ↦ₘ k2) ** ((keyPtr + (24 : Word)) ↦ₘ k3) **
       (slotPtr ↦ₘ s0) ** ((slotPtr + (8 : Word)) ↦ₘ s1) **
       ((slotPtr + (16 : Word)) ↦ₘ s2) ** ((slotPtr + (24 : Word)) ↦ₘ s3) **
       (valPtr ↦ₘ n0) ** ((valPtr + (8 : Word)) ↦ₘ n1) **
       ((valPtr + (16 : Word)) ↦ₘ n2) ** ((valPtr + (24 : Word)) ↦ₘ n3) **
       (EvmAsm.Stateless.STORAGE_WRITES_AREA ↦ₘ r0) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (8 : Word)) ↦ₘ r1) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (16 : Word)) ↦ₘ r2) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (24 : Word)) ↦ₘ r3) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (32 : Word)) ↦ₘ r4) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (40 : Word)) ↦ₘ r5) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (48 : Word)) ↦ₘ r6) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (56 : Word)) ↦ₘ r7) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (64 : Word)) ↦ₘ c0) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (72 : Word)) ↦ₘ c1) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (80 : Word)) ↦ₘ c2) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (88 : Word)) ↦ₘ c3) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (96 : Word)) ↦ₘ b0) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (104 : Word)) ↦ₘ b1) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (112 : Word)) ↦ₘ b2) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (120 : Word)) ↦ₘ b3))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ keyPtr) ** (.x11 ↦ᵣ slotPtr) ** (.x12 ↦ᵣ valPtr) **
       (.x13 ↦ᵣ (0 : Word)) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       ((sp - (64 : Word)) ↦ₘ v5) ** ((sp - (56 : Word)) ↦ₘ v6) **
       ((sp - (48 : Word)) ↦ₘ v7) ** ((sp - (40 : Word)) ↦ₘ v28) **
       ((sp - (32 : Word)) ↦ₘ v29) ** ((sp - (24 : Word)) ↦ₘ v30) **
       ((sp - (16 : Word)) ↦ₘ v31) **
       ((GuestAddrs.storage_writes_count : Word) ↦ₘ (1 : Word)) **
       (keyPtr ↦ₘ k0) ** ((keyPtr + (8 : Word)) ↦ₘ k1) **
       ((keyPtr + (16 : Word)) ↦ₘ k2) ** ((keyPtr + (24 : Word)) ↦ₘ k3) **
       (slotPtr ↦ₘ s0) ** ((slotPtr + (8 : Word)) ↦ₘ s1) **
       ((slotPtr + (16 : Word)) ↦ₘ s2) ** ((slotPtr + (24 : Word)) ↦ₘ s3) **
       (valPtr ↦ₘ n0) ** ((valPtr + (8 : Word)) ↦ₘ n1) **
       ((valPtr + (16 : Word)) ↦ₘ n2) ** ((valPtr + (24 : Word)) ↦ₘ n3) **
       (EvmAsm.Stateless.STORAGE_WRITES_AREA ↦ₘ k0) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (8 : Word)) ↦ₘ k1) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (16 : Word)) ↦ₘ k2) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (24 : Word)) ↦ₘ k3) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (32 : Word)) ↦ₘ s0) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (40 : Word)) ↦ₘ s1) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (48 : Word)) ↦ₘ s2) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (56 : Word)) ↦ₘ s3) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (64 : Word)) ↦ₘ n0) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (72 : Word)) ↦ₘ n1) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (80 : Word)) ↦ₘ n2) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (88 : Word)) ↦ₘ n3) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (96 : Word)) ↦ₘ (0 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (104 : Word)) ↦ₘ (0 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (112 : Word)) ↦ₘ (0 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (120 : Word)) ↦ₘ (0 : Word))) := by
  -- segment A: prologue .. the empty-map `bgeu`
  have hA := storageWritesBlockUpsert_segA_body_spec
    (GuestAddrs.storage_writes_block_upsert : Word) sp ra
    (GuestAddrs.storage_writes_count : Word) v5 v6 v7 v28 v29 v30 v31
    (by decide) (by decide)
  -- everything segments C..E touch that segment A does not
  have hA := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ keyPtr) ** (.x11 ↦ᵣ slotPtr) ** (.x12 ↦ᵣ valPtr) **
     (.x13 ↦ᵣ (0 : Word)) **
     (keyPtr ↦ₘ k0) ** ((keyPtr + (8 : Word)) ↦ₘ k1) **
     ((keyPtr + (16 : Word)) ↦ₘ k2) ** ((keyPtr + (24 : Word)) ↦ₘ k3) **
     (slotPtr ↦ₘ s0) ** ((slotPtr + (8 : Word)) ↦ₘ s1) **
     ((slotPtr + (16 : Word)) ↦ₘ s2) ** ((slotPtr + (24 : Word)) ↦ₘ s3) **
     (valPtr ↦ₘ n0) ** ((valPtr + (8 : Word)) ↦ₘ n1) **
     ((valPtr + (16 : Word)) ↦ₘ n2) ** ((valPtr + (24 : Word)) ↦ₘ n3) **
     (EvmAsm.Stateless.STORAGE_WRITES_AREA ↦ₘ r0) **
     ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (8 : Word)) ↦ₘ r1) **
     ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (16 : Word)) ↦ₘ r2) **
     ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (24 : Word)) ↦ₘ r3) **
     ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (32 : Word)) ↦ₘ r4) **
     ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (40 : Word)) ↦ₘ r5) **
     ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (48 : Word)) ↦ₘ r6) **
     ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (56 : Word)) ↦ₘ r7) **
     ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (64 : Word)) ↦ₘ c0) **
     ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (72 : Word)) ↦ₘ c1) **
     ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (80 : Word)) ↦ₘ c2) **
     ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (88 : Word)) ↦ₘ c3) **
     ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (96 : Word)) ↦ₘ b0) **
     ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (104 : Word)) ↦ₘ b1) **
     ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (112 : Word)) ↦ₘ b2) **
     ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (120 : Word)) ↦ₘ b3))
    (by pcf) hA
  -- segment B: the capacity gate
  have hB := storageWritesBlockUpsert_segB_body_spec
    (GuestAddrs.storage_writes_block_upsert : Word) v7
  -- segment C: the row base and the eight key dwords
  have hC := storageWritesBlockUpsert_segC_body_spec
    (GuestAddrs.storage_writes_block_upsert : Word) keyPtr slotPtr
    (66666 : Word) v30 k0 k1 k2 k3 s0 s1 s2 s3 r0 r1 r2 r3 r4 r5 r6 r7
  -- segment D: the zero baseline, the count bump, and the value dwords
  have hD := storageWritesBlockUpsert_segD_body_spec
    (GuestAddrs.storage_writes_block_upsert : Word)
    (GuestAddrs.storage_writes_count : Word) valPtr s3 n0 n1 n2 n3 b0 b1 b2 b3
    c0 c1 c2 c3
  -- segment E: the epilogue
  have hE := storageWritesBlockUpsert_segE_body_spec
    (GuestAddrs.storage_writes_block_upsert : Word) sp ra
    v5 v6 v7 v28 v29 v30 v31
    (GuestAddrs.storage_writes_count : Word) (1 : Word) n3
    EvmAsm.Stateless.STORAGE_WRITES_AREA (0 : Word)
    EvmAsm.Stateless.STORAGE_WRITES_AREA v31
  seqFrame hA hB
  seqFrame hAhB hC
  seqFrame hAhBhC hD
  seqFrame hAhBhChD hE
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hAhBhChDhE

/-! ## Non-vacuity

  Three checks, in the shape `docs/agents` asks for: a fully numeric instance
  (so a `True`-shaped or trivially satisfiable post could not have passed), a
  positive witness for each gate together with a NEGATIVE control showing the
  gate really excludes the inputs the routine is normally asked about, and a
  satisfiability check on the numeric precondition — `memOwn`/`↦ₘ` both
  *assert* `isValidDwordAccess`, so an unsatisfiable pre is a real risk rather
  than a formality. -/

/-- **Numeric instance.**  `sp = 0x30000000`, the three source pointers at
    three distinct 32-byte-aligned cells of the stack region below it, a null
    baseline, temps `1..7`, and concrete 32-byte payloads
    `k = 101..104`, `s = 201..204`, `v = 301..304`.  The post is fully
    concrete: row 0 reads back `101..104` at `+0 .. +24`, `201..204` at
    `+32 .. +56`, `301..304` at `+64 .. +88`, ZERO at `+96 .. +120`;
    `storage_writes_count` reads 1; and every one of `t0`-`t6`, `sp`, `ra`
    and `a0`-`a3` is back at its entry value.

    The pre-image values `r0..r7`, `c0..c3` and `b0..b3` are left universally
    quantified on purpose: the arm OVERWRITES all sixteen row dwords, so the
    post must not depend on what was there — which is exactly what a
    quantified pre-image and a concrete post-image assert together. -/
example (ra r0 r1 r2 r3 r4 r5 r6 r7 c0 c1 c2 c3 b0 b1 b2 b3 : Word) :
    cpsTripleWithin 63 (GuestAddrs.storage_writes_block_upsert : Word)
      (ra &&& ~~~(1 : Word))
      (CodeReq.ofProg (GuestAddrs.storage_writes_block_upsert : Word)
        storageWritesBlockUpsert_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (0x30000000 : Word)) **
       (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (2 : Word)) ** (.x7 ↦ᵣ (3 : Word)) **
       (.x10 ↦ᵣ (0x2fffff00 : Word)) ** (.x11 ↦ᵣ (0x2fffff20 : Word)) **
       (.x12 ↦ᵣ (0x2fffff40 : Word)) ** (.x13 ↦ᵣ (0 : Word)) **
       (.x28 ↦ᵣ (4 : Word)) ** (.x29 ↦ᵣ (5 : Word)) ** (.x30 ↦ᵣ (6 : Word)) **
       (.x31 ↦ᵣ (7 : Word)) **
       memOwn (0x2fffffc0 : Word) ** memOwn (0x2fffffc8 : Word) **
       memOwn (0x2fffffd0 : Word) ** memOwn (0x2fffffd8 : Word) **
       memOwn (0x2fffffe0 : Word) ** memOwn (0x2fffffe8 : Word) **
       memOwn (0x2ffffff0 : Word) **
       ((GuestAddrs.storage_writes_count : Word) ↦ₘ (0 : Word)) **
       ((0x2fffff00 : Word) ↦ₘ (101 : Word)) **
       ((0x2fffff08 : Word) ↦ₘ (102 : Word)) **
       ((0x2fffff10 : Word) ↦ₘ (103 : Word)) **
       ((0x2fffff18 : Word) ↦ₘ (104 : Word)) **
       ((0x2fffff20 : Word) ↦ₘ (201 : Word)) **
       ((0x2fffff28 : Word) ↦ₘ (202 : Word)) **
       ((0x2fffff30 : Word) ↦ₘ (203 : Word)) **
       ((0x2fffff38 : Word) ↦ₘ (204 : Word)) **
       ((0x2fffff40 : Word) ↦ₘ (301 : Word)) **
       ((0x2fffff48 : Word) ↦ₘ (302 : Word)) **
       ((0x2fffff50 : Word) ↦ₘ (303 : Word)) **
       ((0x2fffff58 : Word) ↦ₘ (304 : Word)) **
       (EvmAsm.Stateless.STORAGE_WRITES_AREA ↦ₘ r0) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (8 : Word)) ↦ₘ r1) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (16 : Word)) ↦ₘ r2) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (24 : Word)) ↦ₘ r3) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (32 : Word)) ↦ₘ r4) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (40 : Word)) ↦ₘ r5) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (48 : Word)) ↦ₘ r6) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (56 : Word)) ↦ₘ r7) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (64 : Word)) ↦ₘ c0) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (72 : Word)) ↦ₘ c1) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (80 : Word)) ↦ₘ c2) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (88 : Word)) ↦ₘ c3) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (96 : Word)) ↦ₘ b0) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (104 : Word)) ↦ₘ b1) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (112 : Word)) ↦ₘ b2) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (120 : Word)) ↦ₘ b3))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (0x30000000 : Word)) **
       (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (2 : Word)) ** (.x7 ↦ᵣ (3 : Word)) **
       (.x10 ↦ᵣ (0x2fffff00 : Word)) ** (.x11 ↦ᵣ (0x2fffff20 : Word)) **
       (.x12 ↦ᵣ (0x2fffff40 : Word)) ** (.x13 ↦ᵣ (0 : Word)) **
       (.x28 ↦ᵣ (4 : Word)) ** (.x29 ↦ᵣ (5 : Word)) ** (.x30 ↦ᵣ (6 : Word)) **
       (.x31 ↦ᵣ (7 : Word)) **
       ((0x2fffffc0 : Word) ↦ₘ (1 : Word)) **
       ((0x2fffffc8 : Word) ↦ₘ (2 : Word)) **
       ((0x2fffffd0 : Word) ↦ₘ (3 : Word)) **
       ((0x2fffffd8 : Word) ↦ₘ (4 : Word)) **
       ((0x2fffffe0 : Word) ↦ₘ (5 : Word)) **
       ((0x2fffffe8 : Word) ↦ₘ (6 : Word)) **
       ((0x2ffffff0 : Word) ↦ₘ (7 : Word)) **
       ((GuestAddrs.storage_writes_count : Word) ↦ₘ (1 : Word)) **
       ((0x2fffff00 : Word) ↦ₘ (101 : Word)) **
       ((0x2fffff08 : Word) ↦ₘ (102 : Word)) **
       ((0x2fffff10 : Word) ↦ₘ (103 : Word)) **
       ((0x2fffff18 : Word) ↦ₘ (104 : Word)) **
       ((0x2fffff20 : Word) ↦ₘ (201 : Word)) **
       ((0x2fffff28 : Word) ↦ₘ (202 : Word)) **
       ((0x2fffff30 : Word) ↦ₘ (203 : Word)) **
       ((0x2fffff38 : Word) ↦ₘ (204 : Word)) **
       ((0x2fffff40 : Word) ↦ₘ (301 : Word)) **
       ((0x2fffff48 : Word) ↦ₘ (302 : Word)) **
       ((0x2fffff50 : Word) ↦ₘ (303 : Word)) **
       ((0x2fffff58 : Word) ↦ₘ (304 : Word)) **
       (EvmAsm.Stateless.STORAGE_WRITES_AREA ↦ₘ (101 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (8 : Word)) ↦ₘ (102 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (16 : Word)) ↦ₘ (103 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (24 : Word)) ↦ₘ (104 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (32 : Word)) ↦ₘ (201 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (40 : Word)) ↦ₘ (202 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (48 : Word)) ↦ₘ (203 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (56 : Word)) ↦ₘ (204 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (64 : Word)) ↦ₘ (301 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (72 : Word)) ↦ₘ (302 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (80 : Word)) ↦ₘ (303 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (88 : Word)) ↦ₘ (304 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (96 : Word)) ↦ₘ (0 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (104 : Word)) ↦ₘ (0 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (112 : Word)) ↦ₘ (0 : Word)) **
       ((EvmAsm.Stateless.STORAGE_WRITES_AREA + (120 : Word)) ↦ₘ (0 : Word))) := by
  have h := storageWritesBlockUpsertAppendFlat_spec (0x30000000 : Word) ra
    (0x2fffff00 : Word) (0x2fffff20 : Word) (0x2fffff40 : Word)
    1 2 3 4 5 6 7
    101 102 103 104 201 202 203 204 301 302 303 304
    r0 r1 r2 r3 r4 r5 r6 r7 c0 c1 c2 c3 b0 b1 b2 b3
  rw [show (0x30000000 : Word) - (64 : Word) = (0x2fffffc0 : Word) from by decide,
      show (0x30000000 : Word) - (56 : Word) = (0x2fffffc8 : Word) from by decide,
      show (0x30000000 : Word) - (48 : Word) = (0x2fffffd0 : Word) from by decide,
      show (0x30000000 : Word) - (40 : Word) = (0x2fffffd8 : Word) from by decide,
      show (0x30000000 : Word) - (32 : Word) = (0x2fffffe0 : Word) from by decide,
      show (0x30000000 : Word) - (24 : Word) = (0x2fffffe8 : Word) from by decide,
      show (0x30000000 : Word) - (16 : Word) = (0x2ffffff0 : Word) from by decide,
      show (0x2fffff00 : Word) + (8 : Word) = (0x2fffff08 : Word) from by decide,
      show (0x2fffff00 : Word) + (16 : Word) = (0x2fffff10 : Word) from by decide,
      show (0x2fffff00 : Word) + (24 : Word) = (0x2fffff18 : Word) from by decide,
      show (0x2fffff20 : Word) + (8 : Word) = (0x2fffff28 : Word) from by decide,
      show (0x2fffff20 : Word) + (16 : Word) = (0x2fffff30 : Word) from by decide,
      show (0x2fffff20 : Word) + (24 : Word) = (0x2fffff38 : Word) from by decide,
      show (0x2fffff40 : Word) + (8 : Word) = (0x2fffff48 : Word) from by decide,
      show (0x2fffff40 : Word) + (16 : Word) = (0x2fffff50 : Word) from by decide,
      show (0x2fffff40 : Word) + (24 : Word) = (0x2fffff58 : Word) from by decide] at h
  exact h

/-- **Gate witnesses and negative controls.**

    1. `¬ 0 <ᵤ 0` inhabits the empty-map gate: the scan's `bgeu t4, t1` at
       index 16 IS taken with zero iterations, which is why this arm needs no
       loop invariant.
    2. `¬ ¬ (0 <ᵤ 1)` is provably FALSE — a map holding even ONE row makes the
       index-16 `bgeu` fall through into the scan body, so the hit arm is
       genuinely OUTSIDE this triple rather than silently covered.
    3. `0 <ᵤ 66666` witnesses the capacity `bgeu` at index 48 NOT being taken,
       and `¬ 66666 <ᵤ 66666` is its boundary: a full arena really does reach
       `.Lswbu_overflow`, which this triple does not claim.
    4. The null-baseline gate is a real selection: `.Lswbu_base_zero` (index
       77, `+308`) and the baseline-copy arm (index 68, `+272`) are distinct
       addresses, so `a3 = 0` excludes the copy arm rather than covering it.
    5. `blockStorageWritesCapacity` really is 66666, i.e. the `lui 16 /
       addiw 1130` pair this proof steps through is the capacity the Program
       intends. -/
example :
    (¬ BitVec.ult (0 : Word) (0 : Word))
    ∧ ¬ (¬ BitVec.ult (0 : Word) (1 : Word))
    ∧ BitVec.ult (0 : Word) (66666 : Word)
    ∧ (¬ BitVec.ult (66666 : Word) (66666 : Word))
    ∧ (GuestAddrs.storage_writes_block_upsert + 308
        ≠ GuestAddrs.storage_writes_block_upsert + 272)
    ∧ (GuestAddrs.storage_writes_block_upsert + 184
        ≠ GuestAddrs.storage_writes_block_upsert + 68)
    ∧ blockStorageWritesCapacity = 66666 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Satisfiability of the numeric instance's precondition.**  All seven
    frame slots, the twelve source dwords, the sixteen row dwords and the
    count global are valid, 8-byte-aligned dword addresses; the three source
    32-byte blocks, the frame and the row are pairwise disjoint; and the count
    global is distinct from all of them.  `memOwn`/`↦ₘ` both assert validity,
    so without this the separating conjunction could be uninhabitable and the
    numeric post above vacuous. -/
example :
    isValidDwordAccess (0x2fffffc0 : Word) = true ∧
    isValidDwordAccess (0x2ffffff0 : Word) = true ∧
    isValidDwordAccess (0x2fffff00 : Word) = true ∧
    isValidDwordAccess (0x2fffff18 : Word) = true ∧
    isValidDwordAccess (0x2fffff20 : Word) = true ∧
    isValidDwordAccess (0x2fffff38 : Word) = true ∧
    isValidDwordAccess (0x2fffff40 : Word) = true ∧
    isValidDwordAccess (0x2fffff58 : Word) = true ∧
    isValidDwordAccess EvmAsm.Stateless.STORAGE_WRITES_AREA = true ∧
    isValidDwordAccess (EvmAsm.Stateless.STORAGE_WRITES_AREA + (120 : Word)) = true ∧
    isValidDwordAccess (GuestAddrs.storage_writes_count : Word) = true ∧
    ((0x2fffff18 : Word) < (0x2fffff20 : Word)) ∧
    ((0x2fffff38 : Word) < (0x2fffff40 : Word)) ∧
    ((0x2fffff58 : Word) < (0x2fffffc0 : Word)) ∧
    (GuestAddrs.storage_writes_count : Word) ≠ EvmAsm.Stateless.STORAGE_WRITES_AREA ∧
    (GuestAddrs.storage_writes_count : Word) ≠ (0x2fffff00 : Word) ∧
    (GuestAddrs.storage_writes_count : Word) ≠ (0x2fffffc0 : Word) ∧
    EvmAsm.Stateless.STORAGE_WRITES_AREA ≠ (0x2fffff00 : Word) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   by decide, by decide, by decide, by decide⟩

/-! ## Axiom audit — classical-only. -/

#print axioms storageWritesBlockUpsertAppendFlat_spec

end EvmAsm.Codegen.Proofs
