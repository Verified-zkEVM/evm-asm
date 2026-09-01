/-
  EvmAsm.Codegen.Proofs.StorageWritesBlockLatestValueSpec

  **The `storage_writes_block_latest_value` machine triple — the
  count-exceeds-capacity refusal arm (#11654).**

  `storage_writes_block_latest_value`
  (`Codegen/Programs/CommittedStorageLookup.lean`,
  `storageWritesBlockLatestValue_prog`, 82 instructions = 328 bytes at
  `GuestAddrs.storage_writes_block_latest_value` = `0x800205b8`, image entry
  `Codegen/Proofs/GuestImageEntries.lean:391`) is **tier 2 of SLOAD's storage
  read path**: the bounded reader for the canonical block-level
  `storage_writes` map (`BlockState.storage_writes`, `state_tracker.py:74`).

  ## ⭐ Why this routine, and not `h_SLOAD` (#11654's stated target)

  #11654 asks for SLOAD to be re-proved against `StorageWriteMap`.  Measured on
  this branch, **the handler itself is not statable**: `h_SLOAD`
  (`Codegen/Programs/Storage.lean:412`) is an `OpcodeHandlerSpec` whose
  `preBody` and `tail` are raw `String`s with `body := []`, there is no
  `h_SLOAD`-shaped `Program`, no `GuestImageEntries` pairing, and
  `scripts/asm-fixtures/MANIFEST.tsv` carries 0 of its rows for any `h_*`
  handler.  `cpsTripleWithin` ranges over a `CodeReq` built from a `Program`,
  so no whole-handler SLOAD triple can be written today.  The two read-path
  snippets spliced into it — `storageTxMapFindAsm "sload_live" …`
  (`Storage.lean:463`) and `storagePrestateResolveAsm "sload" …`
  (`Storage.lean:465`) — are label-prefix-parameterised `String`s with no
  symbol boundary at all, and `storageTxMapFindAsm` additionally contains `la`
  and a branch to the dispatcher-owned `.exit_outofgas`, so they are worse
  placed for a triple than an ordinary `String` routine.

  What IS Program-valued, guest-anchored and unrowed is the **tier-2 read
  routine SLOAD delegates to**.  `storagePrestateResolveAsm`'s own docstring
  spells the funnel out: tier 1 the transaction write map, **tier 2
  `storage_writes_block_latest_value`, which reads the canonical
  execution-specs `BlockState.storage_writes` map**, tier 3 the header-state
  witness, else zero.  Skipping tier 2 would return the pre-block value
  wherever an earlier transaction in the block already wrote the slot, which
  is exactly why the routine exists.  This module states the first machine
  triple over it.

  ⚠️ **Granularity, stated plainly.**  This is a triple over
  `storage_writes_block_latest_value`, **not** over SLOAD.  It does not claim
  that the SLOAD opcode returns the right value, and the `SLOAD` registry row
  is left at `.execSpec` for that reason.  What it does claim is a
  whole-routine contract for one arm of one named tier of SLOAD's read path.

  ## What this module proves

  `storageWritesBlockLatestValueCapacityRefusalFlat_spec`, a **14-step**
  whole-routine triple entry → `ret` under one named gate:

  * `BitVec.ult cap cnt` — the caller's `a4` (map capacity) is strictly less
    than its `a3` (map row count), i.e. the count the caller reports exceeds
    the capacity it reports.

  Under that gate the `bltu a4, a3` at instruction index 5 (`base + 20`) is
  TAKEN to `base + 296` (index 74), the routine answers `a0 = 2` — the
  documented "count exceeds capacity" status — jumps the two other status
  arms (`.JAL .x0 4` at index 75 is a pure fallthrough-length jump that skips
  nothing but exists in the emitted form), reloads `ra`, `s0`, `s1` and `s2`,
  pops the 32-byte frame and returns.

  ⭐ Because `cpsTripleWithin` universally quantifies over a `pcFree` frame,
  and **no map arena, no scratch buffer and no out pointer is named in the pre
  or the post**, the triple ALSO says — for free — that on this arm the
  routine writes nothing outside its own stack frame and does not read the
  canonical map at all.  That is the substance of "fail closed": a caller that
  mis-reports its counts gets a refusal, not a partial scan of an
  over-long map.

  ## ⭐ A single `ofProg`, not a union — and that is checked

  `Codegen/Proofs/StorageWriteRecordSpec.lean` and
  `Codegen/Proofs/AccountWriteRecordSpec.lean` both had to state their arms
  over a two-program UNION `CodeReq`, because neither writer has an arm that
  terminates at `ret` without leaving its own bytes through a
  `jal ra, …undo_push`.  This routine is a LEAF, and the check is the same one
  `AccountWritesLookupCurrentSpec` runs: `storageWritesBlockLatestValue_prog`
  contains no `jal ra, …` at all — every `JAL` in it is a `JAL .x0` internal
  jump, and the only register-indirect transfer is the closing
  `jalr x0, 0(ra)`.  So the triple is stated over the plain
  `CodeReq.ofProg (GuestAddrs.storage_writes_block_latest_value : Word)
  storageWritesBlockLatestValue_prog`, which IS the `GuestImageEntries.lean:391`
  pairing.  Entry and code requirement are anchored at the same address, so
  this grades `whole-routine` under `scripts/proof-frontier.py`'s
  `shape_of_theorem`.

  ## ⚠️ Registers: `s0`/`s1`/`s2` ARE restored, and that was read off the
  epilogue

  #13182's rule applies: docstrings are not evidence about register
  restoration.  The prologue at indices 0..4 saves `ra`, `s0`, `s1`, `s2`
  (`x1`, `x8`, `x9`, `x18`) into a 32-byte frame and the epilogue at indices
  76..79 reloads exactly those four; the post below says so.  `a0` (`x10`) is
  the return value and comes back `2`.  `a3`/`a4` (`x13`/`x14`) are read and
  not written, and the post carries them unchanged.  Every other register the
  routine uses — `t0`-`t4`, `s0`'s aliases, `a1`, `a2`, `a5`-`a7` — is touched
  only past the taken branch, on arms this triple does not enter, so none of
  them is named and the frame rule carries them.

  ## ⚠️ What is deliberately NOT proven

  Everything from index 6 onward: the 20-byte recipient normalisation loop
  (indices 15..21), the 32-byte big-endian slot-key reversal loop (indices
  25..31), the 128-byte row scan (indices 33..73), and the two functional
  answers `a0 = 1` (found, value copied from row offset 64) and `a0 = 0`
  (no match).  Those need two byte-copy loop invariants plus an outer scan
  invariant with measure `cnt − t0`, and that is where the machine gets tied
  to the already-proven model (`storageRowLookup` / `SloadReadPath`,
  `Stateless/State/StorageReadPath.lean`; `storageWriteUpsert_rowsMap`,
  `Stateless/State/StorageWriteUpsert.lean`).  The registry row is therefore
  `.conditional` with the one gate named.

  ## `Nodup`

  As on `accountWritesLookupCurrentAbsentFlat_spec`, no uniqueness obligation
  arises: this is a READER, it never constructs a row sequence, and on the
  refusal arm it does not inspect a single row, so "the first matching row is
  the right one" is not a claim being made in either direction.

  ## Mechanics

  Same pilot rules as `AccountWritesLookupCurrentSpec`: present the code
  requirement as the `singleton`-union chain (`unfold` +
  `CodeReq.ofProg_cons`) before `runBlock`, and write every offset
  `(k : Word)`.  Segments compose with `seqFrame`.  There is no call-site
  adapter — the routine is a leaf.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only
  (audited by the `#print axioms` at the end of this file).
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.WP.Call
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Codegen.Programs.CommittedStorageLookup

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen

/-! ## Segment A — the four-slot prologue and the capacity `bltu`, TAKEN -/

/-- `storage_writes_block_latest_value` instructions 0..5 at a free `base`:
    the 32-byte prologue saving `ra`, `s0`, `s1`, `s2`, then
    `bltu a4, a3, .Lswblv_overflow` — TAKEN, because the caller's reported
    capacity (`a4`, `x14`) is strictly below its reported row count (`a3`,
    `x13`).

    `hbr` pins the emitted branch displacement: the reloc-rendered
    `brOff (sym + 296) (sym + 20)` really is `+276`, so the taken edge lands
    on index 74 (`base + 296`), the `li a0, 2` status arm.  It is discharged
    by `decide` at the call site rather than assumed. -/
theorem storageWritesBlockLatestValue_segA_body_spec
    (base sp ra cnt cap v8 v9 v18 : Word)
    (hlt : BitVec.ult cap cnt)
    (hbr : signExtend13 (brOff (GuestAddrs.storage_writes_block_latest_value + 296)
        (GuestAddrs.storage_writes_block_latest_value + 20)) = (276 : Word)) :
    cpsTripleWithin 6 base (base + (296 : Word))
      (CodeReq.ofProg base storageWritesBlockLatestValue_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
       (.x13 ↦ᵣ cnt) ** (.x14 ↦ᵣ cap) **
       memOwn (sp - (32 : Word)) ** memOwn (sp - (24 : Word)) **
       memOwn (sp - (16 : Word)) ** memOwn (sp - (8 : Word)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp - (32 : Word))) **
       (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
       (.x13 ↦ᵣ cnt) ** (.x14 ↦ᵣ cap) **
       ((sp - (32 : Word)) ↦ₘ ra) ** ((sp - (24 : Word)) ↦ₘ v8) **
       ((sp - (16 : Word)) ↦ₘ v9) ** ((sp - (8 : Word)) ↦ₘ v18)) := by
  unfold storageWritesBlockLatestValue_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 0: `addi sp, sp, -32`
  have P0 := addi_spec_gen_same_within .x2 sp (-32 : BitVec 12) base (by nofun)
  rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide,
      show sp + (-32 : Word) = sp - (32 : Word) from by bv_omega] at P0
  -- index 1: `sd ra, 0(sp)`
  have P1 := sd_spec_gen_own_within .x2 .x1 (sp - (32 : Word)) ra (0 : BitVec 12)
    (base + (4 : Word))
  rw [show (sp - (32 : Word)) + signExtend12 (0 : BitVec 12) = sp - (32 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at P1
  -- index 2: `sd s0, 8(sp)`
  have P2 := sd_spec_gen_own_within .x2 .x8 (sp - (32 : Word)) v8 (8 : BitVec 12)
    (base + (8 : Word))
  rw [show (sp - (32 : Word)) + signExtend12 (8 : BitVec 12) = sp - (24 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at P2
  -- index 3: `sd s1, 16(sp)`
  have P3 := sd_spec_gen_own_within .x2 .x9 (sp - (32 : Word)) v9 (16 : BitVec 12)
    (base + (12 : Word))
  rw [show (sp - (32 : Word)) + signExtend12 (16 : BitVec 12) = sp - (16 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at P3
  -- index 4: `sd s2, 24(sp)`
  have P4 := sd_spec_gen_own_within .x2 .x18 (sp - (32 : Word)) v18 (24 : BitVec 12)
    (base + (16 : Word))
  rw [show (sp - (32 : Word)) + signExtend12 (24 : BitVec 12) = sp - (8 : Word) from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]; bv_omega] at P4
  -- index 5: `bltu a4, a3, +276` — TAKEN, the reported count exceeds capacity
  have PB := bltu_spec_gen_within .x14 .x13
    (brOff (GuestAddrs.storage_writes_block_latest_value + 296)
      (GuestAddrs.storage_writes_block_latest_value + 20))
    cap cnt (base + (20 : Word))
  rw [hbr, show base + (20 : Word) + (276 : Word) = base + (296 : Word) from by bv_omega]
    at PB
  have P5 : cpsTripleWithin 1 (base + (20 : Word)) (base + (296 : Word))
      (CodeReq.singleton (base + (20 : Word)) (.BLTU .x14 .x13
        (brOff (GuestAddrs.storage_writes_block_latest_value + 296)
          (GuestAddrs.storage_writes_block_latest_value + 20))))
      ((.x14 ↦ᵣ cap) ** (.x13 ↦ᵣ cnt))
      ((.x14 ↦ᵣ cap) ** (.x13 ↦ᵣ cnt)) :=
    cpsBranchWithin_takenStripPure2 PB (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact absurd hlt h_pure.2)
  runBlock P0 P1 P2 P3 P4 P5

/-! ## Segment B — the `a0 = 2` status arm and the epilogue -/

/-- `storage_writes_block_latest_value` instructions 74..81
    (`base + 296 .. base + 324`): `li a0, 2` (the "count exceeds capacity"
    status), the `j +4` that separates it from the other two status arms,
    then reload `ra`, `s0`, `s1`, `s2`, pop the 32-byte frame and `ret`.

    ⚠️ Read off the epilogue, not off a docstring (#13182): the prologue saved
    exactly `ra`/`s0`/`s1`/`s2` and this reloads exactly those four, so all
    are restored.  `a0` is the answer and is NOT restored — it is the point. -/
theorem storageWritesBlockLatestValue_segB_body_spec
    (base sp ra link w8 w9 w10 w18 v8 v9 v18 : Word) :
    cpsTripleWithin 8 (base + (296 : Word)) (ra &&& ~~~(1 : Word))
      (CodeReq.ofProg base storageWritesBlockLatestValue_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ link) ** (.x2 ↦ᵣ (sp - (32 : Word))) **
       (.x8 ↦ᵣ w8) ** (.x9 ↦ᵣ w9) ** (.x10 ↦ᵣ w10) ** (.x18 ↦ᵣ w18) **
       ((sp - (32 : Word)) ↦ₘ ra) ** ((sp - (24 : Word)) ↦ₘ v8) **
       ((sp - (16 : Word)) ↦ₘ v9) ** ((sp - (8 : Word)) ↦ₘ v18))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ (2 : Word)) ** (.x18 ↦ᵣ v18) **
       ((sp - (32 : Word)) ↦ₘ ra) ** ((sp - (24 : Word)) ↦ₘ v8) **
       ((sp - (16 : Word)) ↦ₘ v9) ** ((sp - (8 : Word)) ↦ₘ v18)) := by
  unfold storageWritesBlockLatestValue_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 74: `li a0, 2` — status 2, "count exceeds capacity"
  have R0 := li_spec_gen_within .x10 w10 (2 : Word) (base + (296 : Word)) (by nofun)
  -- index 75: `j +4` — the arm separator; a one-instruction fallthrough
  have R1 := jal_x0_spec_gen_within (4 : BitVec 21) (base + (300 : Word))
  rw [show signExtend21 (4 : BitVec 21) = (4 : Word) from by decide,
      show base + (300 : Word) + (4 : Word) = base + (304 : Word) from by bv_omega] at R1
  -- index 76: `ld ra, 0(sp)`
  have R2 := ld_spec_gen_within .x1 .x2 (sp - (32 : Word)) link ra (0 : BitVec 12)
    (base + (304 : Word)) (by nofun)
  rw [show (sp - (32 : Word)) + signExtend12 (0 : BitVec 12) = sp - (32 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at R2
  -- index 77: `ld s0, 8(sp)`
  have R3 := ld_spec_gen_within .x8 .x2 (sp - (32 : Word)) w8 v8 (8 : BitVec 12)
    (base + (308 : Word)) (by nofun)
  rw [show (sp - (32 : Word)) + signExtend12 (8 : BitVec 12) = sp - (24 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at R3
  -- index 78: `ld s1, 16(sp)`
  have R4 := ld_spec_gen_within .x9 .x2 (sp - (32 : Word)) w9 v9 (16 : BitVec 12)
    (base + (312 : Word)) (by nofun)
  rw [show (sp - (32 : Word)) + signExtend12 (16 : BitVec 12) = sp - (16 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at R4
  -- index 79: `ld s2, 24(sp)`
  have R5 := ld_spec_gen_within .x18 .x2 (sp - (32 : Word)) w18 v18 (24 : BitVec 12)
    (base + (316 : Word)) (by nofun)
  rw [show (sp - (32 : Word)) + signExtend12 (24 : BitVec 12) = sp - (8 : Word) from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]; bv_omega] at R5
  -- index 80: `addi sp, sp, 32`
  have R6 := addi_spec_gen_same_within .x2 (sp - (32 : Word)) (32 : BitVec 12)
    (base + (320 : Word)) (by nofun)
  rw [show (sp - (32 : Word)) + signExtend12 (32 : BitVec 12) = sp from by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]; bv_omega] at R6
  -- index 81: `ret`
  have R7 := EvmAsm.Evm64.ret_spec_within' (base + (324 : Word)) ra
  runBlock R0 R1 R2 R3 R4 R5 R6 R7

/-! ## The deployed (anchored) whole-routine contract -/

/-- ⭐ **`storage_writes_block_latest_value`, whole routine, the
    count-exceeds-capacity refusal arm.**

    Entry `GuestAddrs.storage_writes_block_latest_value`, exit `ra &&& ~~~1` —
    the caller's return address — over
    `CodeReq.ofProg (GuestAddrs.storage_writes_block_latest_value : Word)
    storageWritesBlockLatestValue_prog`, which IS the
    `Codegen/Proofs/GuestImageEntries.lean:391` pairing.  Entry and code
    requirement are anchored at the same address, so this grades
    `whole-routine` under `scripts/proof-frontier.py`'s `shape_of_theorem`.

    ⭐ A single `ofProg`, not a union: the routine is a LEAF
    (`storageWritesBlockLatestValue_prog` has no `jal ra, …`, only `JAL .x0`
    internal jumps and the closing `jalr x0, 0(ra)`), so no callee contract is
    needed and none is assumed.

    One named gate selects the arm:

    * `BitVec.ult cap cnt` — the caller's `a4` (map capacity) is strictly
      below its `a3` (map row count), so the `bltu a4, a3` at index 5 is
      taken.

    Under it the routine answers `a0 = 2` — the documented "count exceeds
    capacity" status — restores `ra`, `s0`, `s1`, `s2` and `sp`, and returns.
    `a3`/`a4` come back unchanged.

    ⭐ Because `cpsTripleWithin` quantifies over an arbitrary `pcFree` frame
    and NO map arena, scratch buffer or out pointer is named in the pre or the
    post, the triple ALSO says — for free — that on this arm the routine
    writes nothing outside its own 32-byte frame and does not read the
    canonical `storage_writes` map at all.  That is the substance of the
    fail-closed refusal: a mis-reported count yields a status, not a partial
    scan past the end of the map.

    ⚠️ Granularity: this is `storage_writes_block_latest_value`'s contract, not
    SLOAD's.  See the module header — `h_SLOAD` has no `Program` and no
    whole-handler triple is statable.  This routine is tier 2 of the read
    funnel `h_SLOAD` runs (`storagePrestateResolveAsm`,
    `Codegen/Programs/Storage.lean:327`).

    ⚠️ NOT proven here: everything from index 6 on — the 20-byte recipient
    normalisation loop, the 32-byte big-endian key reversal, the 128-byte row
    scan, and the `a0 = 1` (found) and `a0 = 0` (no match) answers.  Those
    need two byte-copy loop invariants and a scan invariant with measure
    `cnt − t0`, and they are where the machine gets tied to the already-proven
    `storageRowLookup` model. -/
theorem storageWritesBlockLatestValueCapacityRefusalFlat_spec
    (sp ra cnt cap v8 v9 v10 v18 : Word)
    (hlt : BitVec.ult cap cnt) :
    cpsTripleWithin 14 (GuestAddrs.storage_writes_block_latest_value : Word)
      (ra &&& ~~~(1 : Word))
      (CodeReq.ofProg (GuestAddrs.storage_writes_block_latest_value : Word)
        storageWritesBlockLatestValue_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
       (.x13 ↦ᵣ cnt) ** (.x14 ↦ᵣ cap) **
       memOwn (sp - (32 : Word)) ** memOwn (sp - (24 : Word)) **
       memOwn (sp - (16 : Word)) ** memOwn (sp - (8 : Word)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ (2 : Word)) ** (.x18 ↦ᵣ v18) **
       (.x13 ↦ᵣ cnt) ** (.x14 ↦ᵣ cap) **
       ((sp - (32 : Word)) ↦ₘ ra) ** ((sp - (24 : Word)) ↦ₘ v8) **
       ((sp - (16 : Word)) ↦ₘ v9) ** ((sp - (8 : Word)) ↦ₘ v18)) := by
  -- segment A: the four-slot prologue and the taken capacity `bltu`
  have hA := storageWritesBlockLatestValue_segA_body_spec
    (GuestAddrs.storage_writes_block_latest_value : Word) sp ra cnt cap v8 v9 v18
    hlt (by decide)
  -- `a0` is not in segment A's footprint; carry it across by the frame rule
  have hA := cpsTripleWithin_frameR (.x10 ↦ᵣ v10) (by pcf) hA
  -- segment B: the `a0 = 2` status arm and the epilogue
  have hB := storageWritesBlockLatestValue_segB_body_spec
    (GuestAddrs.storage_writes_block_latest_value : Word) sp ra ra v8 v9 v10 v18
    v8 v9 v18
  -- `a3`/`a4` are read-only and untouched past the branch; frame them across B
  have hB := cpsTripleWithin_frameR
    ((.x13 ↦ᵣ cnt) ** (.x14 ↦ᵣ cap)) (by pcf) hB
  seqFrame hA hB
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hAhB

/-! ## Non-vacuity

  Three checks, in the shape `docs/agents` asks for: a fully numeric instance
  (so a `True`-shaped or trivially satisfiable post could not have passed), a
  positive witness for the gate together with a NEGATIVE control showing the
  gate really excludes the inputs the routine is normally asked about, and a
  satisfiability check on the numeric precondition — `memOwn`/`↦ₘ` both
  *assert* `isValidDwordAccess`, so an unsatisfiable pre is a real risk rather
  than a formality. -/

/-- **Numeric instance.**  `sp = 0x30000000`, `a3 = 1` row claimed against
    `a4 = 0` capacity, callee-saves `9`/`10`/`11`, `a0 = 20` on entry.  The
    post is fully concrete: `a0` reads back `2` (the refusal status, NOT its
    entry value `20`), `s0`/`s1`/`s2` are back at `9`/`10`/`11`, `sp` is back
    at `0x30000000`, and the four frame slots hold `ra`, `9`, `10`, `11`.

    ⭐ NAMED rather than an anonymous `example`, and registered as its own
    witness abbrev in `Progress/Routines.lean`, so this control is INSIDE the
    axiom gate (#12857) rather than mentioned only in the row's prose. -/
theorem swblvCapacityRefusal_numeric_instance (ra : Word) :
    cpsTripleWithin 14 (GuestAddrs.storage_writes_block_latest_value : Word)
      (ra &&& ~~~(1 : Word))
      (CodeReq.ofProg (GuestAddrs.storage_writes_block_latest_value : Word)
        storageWritesBlockLatestValue_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (0x30000000 : Word)) **
       (.x8 ↦ᵣ (9 : Word)) ** (.x9 ↦ᵣ (10 : Word)) ** (.x10 ↦ᵣ (20 : Word)) **
       (.x18 ↦ᵣ (11 : Word)) **
       (.x13 ↦ᵣ (1 : Word)) ** (.x14 ↦ᵣ (0 : Word)) **
       memOwn (0x2fffffe0 : Word) ** memOwn (0x2fffffe8 : Word) **
       memOwn (0x2ffffff0 : Word) ** memOwn (0x2ffffff8 : Word))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (0x30000000 : Word)) **
       (.x8 ↦ᵣ (9 : Word)) ** (.x9 ↦ᵣ (10 : Word)) ** (.x10 ↦ᵣ (2 : Word)) **
       (.x18 ↦ᵣ (11 : Word)) **
       (.x13 ↦ᵣ (1 : Word)) ** (.x14 ↦ᵣ (0 : Word)) **
       ((0x2fffffe0 : Word) ↦ₘ ra) ** ((0x2fffffe8 : Word) ↦ₘ (9 : Word)) **
       ((0x2ffffff0 : Word) ↦ₘ (10 : Word)) **
       ((0x2ffffff8 : Word) ↦ₘ (11 : Word))) := by
  have h := storageWritesBlockLatestValueCapacityRefusalFlat_spec
    (0x30000000 : Word) ra 1 0 9 10 20 11 (by decide)
  rw [show (0x30000000 : Word) - (32 : Word) = (0x2fffffe0 : Word) from by decide,
      show (0x30000000 : Word) - (24 : Word) = (0x2fffffe8 : Word) from by decide,
      show (0x30000000 : Word) - (16 : Word) = (0x2ffffff0 : Word) from by decide,
      show (0x30000000 : Word) - (8 : Word) = (0x2ffffff8 : Word) from by decide] at h
  exact h

/-- **Gate witness and negative control.**

    1. `BitVec.ult 0 1` inhabits the gate: a caller reporting one row against
       a zero capacity really does take the `bltu a4, a3` at index 5, so this
       arm is reachable and the triple is not vacuous.
    2. ⛔ `BitVec.ult 16384 0` is provably FALSE — and `16384` is not an
       arbitrary number, it is the capacity the routine's own focused ABI
       probe passes (`ziskStorageWritesBlockLookupPrologue`, `li a4, 16384`).
       So the well-formed call the guest actually makes FALLS THROUGH into the
       scan rather than being silently covered by this triple: the refusal arm
       genuinely excludes the normal case.  The same control fires for a full
       map (`¬ BitVec.ult 16384 16384` — capacity equal to count is NOT a
       refusal), which is why the gate is strict `<` and not `≤`.
    3. The three status arms live at three DISTINCT addresses
       (`+ 288` for `a0 = 0`, `+ 296` for `a0 = 2` — this one — and the
       in-scan `a0 = 1` at `+ 280`), so "the refusal arm" is a real selection
       among arms and not the routine's only exit.

    ⭐ NAMED and registered as a witness abbrev, so the control is inside the
    axiom gate (#12857). -/
theorem swblvCapacityRefusal_gate_reachable :
    BitVec.ult (0 : Word) (1 : Word)
    ∧ ¬ BitVec.ult (16384 : Word) (0 : Word)
    ∧ ¬ BitVec.ult (16384 : Word) (16384 : Word)
    ∧ (GuestAddrs.storage_writes_block_latest_value + 296
        ≠ GuestAddrs.storage_writes_block_latest_value + 288)
    ∧ (GuestAddrs.storage_writes_block_latest_value + 296
        ≠ GuestAddrs.storage_writes_block_latest_value + 280)
    ∧ (GuestAddrs.storage_writes_block_latest_value + 288
        ≠ GuestAddrs.storage_writes_block_latest_value + 280) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Satisfiability of the numeric instance's precondition.**  All four frame
    slots are valid, 8-byte-aligned, pairwise distinct dword addresses, so the
    separating conjunction is inhabitable and the numeric post above is not
    vacuously true.  The routine's `Program` length is also pinned here
    (`82 * 4 = 328`), the `prog.length * 4 == hi − lo` cross-check that keeps
    the `CodeReq.ofProg` extent honest against
    `scripts/asm-fixtures/symbol-addresses.tsv`.

    ⭐ NAMED and registered as a witness abbrev, so the control is inside the
    axiom gate (#12857). -/
theorem swblvCapacityRefusal_precondition_satisfiable :
    isValidDwordAccess (0x2fffffe0 : Word) = true ∧
    isValidDwordAccess (0x2fffffe8 : Word) = true ∧
    isValidDwordAccess (0x2ffffff0 : Word) = true ∧
    isValidDwordAccess (0x2ffffff8 : Word) = true ∧
    (0x2fffffe0 : Word) ≠ (0x2fffffe8 : Word) ∧
    (0x2ffffff0 : Word) ≠ (0x2ffffff8 : Word) ∧
    storageWritesBlockLatestValue_prog.length * 4 = 328 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## Axiom audit — classical-only. -/

#print axioms storageWritesBlockLatestValueCapacityRefusalFlat_spec
#print axioms swblvCapacityRefusal_numeric_instance
#print axioms swblvCapacityRefusal_gate_reachable
#print axioms swblvCapacityRefusal_precondition_satisfiable

end EvmAsm.Codegen.Proofs
