/-
  EvmAsm.Codegen.Proofs.AccountWritesLookupCurrentSpec

  **The `account_writes_lookup_current` machine triple — both-tiers-empty
  arm (#11921).**

  `account_writes_lookup_current` (`Codegen/Programs/AccountWriteMap.lean`,
  `accountWritesLookupCurrent_prog`, 99 instructions at
  `GuestAddrs.account_writes_lookup_current`, image entry
  `Codegen/Proofs/GuestImageEntries.lean:409`) is the reader half of the
  account write-map family: it answers the current execution-code/status
  question for a 20-byte address by scanning the TRANSACTION tier
  (`TX_ACCOUNT_WRITES_AREA`, `tx_account_writes_count` rows) and then, on a
  miss, the BLOCK tier (`ACCOUNT_WRITES_AREA`, `account_writes_count` rows),
  returning `a0 = 0` absent / `1` live code with `a1`/`a2` = pointer/length /
  `2` present-but-empty / `3` present-but-deleted.

  ## ⭐ Why the `CodeReq` here is a SINGLE `ofProg`, and the writers' is not

  `Codegen/Proofs/StorageWriteRecordSpec.lean` and
  `Codegen/Proofs/AccountWriteRecordSpec.lean` both had to state their arms
  over a two-program UNION `CodeReq`, because neither writer has an arm that
  terminates at `ret` without either leaving its own bytes through a
  `jal ra, …undo_push` or first running a capacity-sized scan.

  **This routine is different, and the difference is checked rather than
  assumed.**  `accountWritesLookupCurrent_prog` contains no `jal ra, …` at
  all: every `JAL` in it is a `JAL .x0` internal jump, and the only
  register-indirect transfer is the closing `jalr x0, 0(ra)`.  It is a leaf.
  So the whole-routine triple below is stated over the plain
  `CodeReq.ofProg (GuestAddrs.account_writes_lookup_current : Word)
  accountWritesLookupCurrent_prog` — entry AND code requirement anchored at
  the same `GuestImageEntries` pairing, no callee contract needed, no union.

  ## What this module proves

  `accountWritesLookupCurrentAbsentFlat_spec`, a 27-step whole-routine triple
  entry → `ret` under two named gates:

  * `tx_account_writes_count ↦ₘ 0` — the transaction tier is empty, so the
    scan's `bgeu t3, t1` at instruction index 11 is taken with ZERO
    iterations;
  * `account_writes_count ↦ₘ 0` — the block tier is empty likewise, so the
    second scan's `bgeu t3, t1` at index 51 is taken with ZERO iterations.

  Under those, the routine takes the `.Lawlc_absent` triple at indices 92..94
  and answers **absent**: `a0 = 0`, `a1 = 0`, `a2 = 0`.  It restores `ra`,
  `s0` and `sp`.  Because `cpsTripleWithin` universally quantifies over a
  `pcFree` frame, the triple ALSO says — for free, since neither arena is
  named in the pre or the post — that the routine writes NOTHING anywhere: it
  is a pure reader, and on this arm it does not even read the arenas.

  Unlike the two writers, this is not a *fail-closed* arm but a genuine
  FUNCTIONAL one: `a0 = 0` is the answer the model gives for an address with
  no row in either tier, not a refusal.

  ⚠️ **`t0`-`t3` are clobbered and the post says so.**  The prologue
  (indices 0..2) saves only `ra` and `s0`; `t0`/`t1`/`t2`/`t3` (`x5`, `x6`,
  `x7`, `x28`) are scratch and come back holding the block-tier count
  pointer, `0`, `ACCOUNT_WRITES_AREA` and `0`.  That is correct under the
  RISC-V ABI (they are caller-saved) but it is a real part of the contract, so
  it is written into the post rather than framed away.  `t4`-`t6`
  (`x29`-`x31`) are touched only inside the two scan bodies, which this arm
  skips, so they are not named at all and the frame rule carries them.

  ## ⚠️ What is deliberately NOT proven

  Every arm that reaches a row: the transaction-tier hit (indices 12..43),
  the block-tier hit (indices 52..83), and the three non-zero answers
  `a0 = 1` / `2` / `3` at indices 82, 84 and 88.  Those need the
  `DualReadByteScan` 20-byte address comparison invariant, an outer loop
  invariant over each tier (measure `count − t3`), and the account
  write-map row vocabulary — and that is where the machine gets tied to the
  already-proven model (`Stateless/State/AccountWriteUpsert.lean`,
  #11938/#12016).  The registry row is therefore `.conditional` with both
  gates named.

  ## `Nodup`

  #11921 asks what became of the writers' uniqueness clause.  Here it does not
  arise at all, and for a different reason than on the two fail-closed writer
  arms: this is a READER, so it never constructs a row sequence and has no
  uniqueness obligation to discharge in either direction.  Uniqueness of the
  underlying map is already a hypothesis-free model theorem
  (`accountWriteUpsert_rowsMap`, #11938); a reader consumes it, and would only
  need to on a HIT arm — where "the first matching row is the right one"
  becomes a claim.  On the both-tiers-empty arm there is no matching row, so
  the question is vacuous and nothing is assumed.

  ## Mechanics

  Same pilot rules as `AccountWriteRecordSpec`: present the code requirement
  as the `singleton`-union chain (`unfold` + `CodeReq.ofProg_cons`) before
  `runBlock`, and write every offset `(k : Word)`.  Segments compose with
  `seqFrame`.  There is no call-site adapter — the routine is a leaf.  The
  file is not `module`-ised, for the same reason `AccountWriteRecordSpec.lean`
  is not.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only
  (audited by the `#print axioms` at the end of this file).
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.WP.Call
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Codegen.Programs.AccountWriteMap

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen

/-! ## Segment A — prologue, transaction-tier base, and the empty-tier exit -/

/-- `account_writes_lookup_current` instructions 0..11 at a free `base`: the
    two-slot prologue (`ra`, `s0`), `mv s0, a0` (the caller's address
    pointer), `la t0, tx_account_writes_count`, the three-instruction
    `TX_ACCOUNT_WRITES_AREA` materialisation into `t2`, `li t3, 0`, and the
    transaction-tier scan's `bgeu` — TAKEN, because that tier is empty
    (`txCountPtr ↦ₘ 0`). -/
theorem accountWritesLookupCurrent_segA_body_spec
    (base sp ra txCountPtr v5 v6 v7 v8 v10 v28 : Word)
    (hla : base + (16 : Word) +
        (((laHi GuestAddrs.tx_account_writes_count
            (GuestAddrs.account_writes_lookup_current + 16)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.tx_account_writes_count
          (GuestAddrs.account_writes_lookup_current + 16)) = txCountPtr)
    (hbr : signExtend13 (brOff (GuestAddrs.account_writes_lookup_current + 176)
        (GuestAddrs.account_writes_lookup_current + 44)) = (132 : Word)) :
    cpsTripleWithin 12 base (base + (176 : Word))
      (CodeReq.ofProg base accountWritesLookupCurrent_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x8 ↦ᵣ v8) **
       (.x10 ↦ᵣ v10) ** (.x28 ↦ᵣ v28) **
       memOwn (sp - (24 : Word)) ** memOwn (sp - (16 : Word)) **
       (txCountPtr ↦ₘ (0 : Word)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp - (24 : Word))) **
       (.x5 ↦ᵣ txCountPtr) ** (.x6 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA) ** (.x8 ↦ᵣ v10) **
       (.x10 ↦ᵣ v10) ** (.x28 ↦ᵣ (0 : Word)) **
       ((sp - (24 : Word)) ↦ₘ ra) ** ((sp - (16 : Word)) ↦ₘ v8) **
       (txCountPtr ↦ₘ (0 : Word))) := by
  unfold accountWritesLookupCurrent_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 0: `addi sp, sp, -24`
  have P0 := addi_spec_gen_same_within .x2 sp (-24 : BitVec 12) base (by nofun)
  rw [show signExtend12 (-24 : BitVec 12) = (-24 : Word) from by decide,
      show sp + (-24 : Word) = sp - (24 : Word) from by bv_omega] at P0
  -- index 1: `sd ra, 0(sp)`
  have P1 := sd_spec_gen_own_within .x2 .x1 (sp - (24 : Word)) ra (0 : BitVec 12)
    (base + (4 : Word))
  rw [show (sp - (24 : Word)) + signExtend12 (0 : BitVec 12) = sp - (24 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at P1
  -- index 2: `sd s0, 8(sp)`
  have P2 := sd_spec_gen_own_within .x2 .x8 (sp - (24 : Word)) v8 (8 : BitVec 12)
    (base + (8 : Word))
  rw [show (sp - (24 : Word)) + signExtend12 (8 : BitVec 12) = sp - (16 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at P2
  -- index 3: `mv s0, a0` — the 20-byte address pointer the caller passed
  have P3 := mv_spec_gen_within .x8 .x10 v10 v8 (base + (12 : Word)) (by nofun)
  -- indices 4, 5: `la t0, tx_account_writes_count`
  have P4 := auipc_spec_gen_within .x5 v5
    (laHi GuestAddrs.tx_account_writes_count
      (GuestAddrs.account_writes_lookup_current + 16))
    (base + (16 : Word)) (by nofun)
  have P5 := addi_spec_gen_same_within .x5
    ((base + (16 : Word)) +
      (((laHi GuestAddrs.tx_account_writes_count
          (GuestAddrs.account_writes_lookup_current + 16)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.tx_account_writes_count
      (GuestAddrs.account_writes_lookup_current + 16))
    (base + (20 : Word)) (by nofun)
  rw [hla] at P5
  -- index 6: `ld t1, 0(t0)` — the transaction-tier row count
  have P6 := ld_spec_gen_within .x6 .x5 txCountPtr v6 (0 : Word) (0 : BitVec 12)
    (base + (24 : Word)) (by nofun)
  rw [show txCountPtr + signExtend12 (0 : BitVec 12) = txCountPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at P6
  -- indices 7..9: materialise TX_ACCOUNT_WRITES_AREA into t2
  have P7 := lui_spec_gen_within .x7 v7
    (((EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat >>> 12) >>> 12) : BitVec 20)
    (base + (28 : Word)) (by nofun)
  rw [show ((((((EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat >>> 12) >>> 12) : BitVec 20)
      ).zeroExtend 32 <<< 12).signExtend 64) = (782336 : Word) from by decide] at P7
  have P8 := addiw_spec_gen_same_within .x7 (782336 : Word)
    (((EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat >>> 12) % 4096) : BitVec 12)
    (base + (32 : Word)) (by nofun)
  rw [show ((((782336 : Word).truncate 32 +
      (signExtend12 (((EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat >>> 12) % 4096) :
        BitVec 12)).truncate 32 : BitVec 32)).signExtend 64) = (784256 : Word) from by
    decide] at P8
  have P9 := slli_spec_gen_same_within .x7 (784256 : Word) (12 : BitVec 6)
    (base + (36 : Word)) (by nofun)
  rw [show ((784256 : Word) <<< (12 : BitVec 6).toNat)
      = EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA from by decide] at P9
  -- index 10: `li t3, 0` — the transaction-tier scan cursor
  have P10 := li_spec_gen_within .x28 v28 (0 : Word) (base + (40 : Word)) (by nofun)
  -- index 11: `bgeu t3, t1, .Lawlc_block` — TAKEN, the transaction tier is empty
  have PB := bgeu_spec_gen_within .x28 .x6
    (brOff (GuestAddrs.account_writes_lookup_current + 176)
      (GuestAddrs.account_writes_lookup_current + 44))
    (0 : Word) (0 : Word) (base + (44 : Word))
  rw [hbr, show base + (44 : Word) + (132 : Word) = base + (176 : Word) from by bv_omega]
    at PB
  have P11 : cpsTripleWithin 1 (base + (44 : Word)) (base + (176 : Word))
      (CodeReq.singleton (base + (44 : Word)) (.BGEU .x28 .x6
        (brOff (GuestAddrs.account_writes_lookup_current + 176)
          (GuestAddrs.account_writes_lookup_current + 44))))
      ((.x28 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)))
      ((.x28 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word))) :=
    cpsBranchWithin_takenStripPure2 PB (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact absurd h_pure.2 (by decide))
  runBlock P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11

/-! ## Segment B — the block tier, and its empty-tier exit -/

/-- `account_writes_lookup_current` instructions 44..51
    (`base + 176 .. base + 368`): `la t0, account_writes_count`, load the
    block-tier row count, materialise `ACCOUNT_WRITES_AREA` into `t2`,
    `li t3, 0`, and take the block-tier scan's `bgeu` — TAKEN, because the
    block tier is empty too (`blkCountPtr ↦ₘ 0`).

    ⭐ The three-instruction base materialisation here is the #12600 fix: the
    trio used to build `0xBDB80000`, the PRE-`e799e986c` block-tier arena, so
    every phase-2 lookup scanned dead zero-filled memory.  The `SLLI`-of-a-
    small-positive encoding this proof steps through is exactly the corrected
    one, derived from the `ACCOUNT_WRITES_AREA` layout constant. -/
theorem accountWritesLookupCurrent_segB_body_spec
    (base blkCountPtr u5 u6 u7 u28 : Word)
    (hla : base + (176 : Word) +
        (((laHi GuestAddrs.account_writes_count
            (GuestAddrs.account_writes_lookup_current + 176)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.account_writes_count
          (GuestAddrs.account_writes_lookup_current + 176)) = blkCountPtr)
    (hbr : signExtend13 (brOff (GuestAddrs.account_writes_lookup_current + 368)
        (GuestAddrs.account_writes_lookup_current + 204)) = (164 : Word)) :
    cpsTripleWithin 8 (base + (176 : Word)) (base + (368 : Word))
      (CodeReq.ofProg base accountWritesLookupCurrent_prog)
      ((.x5 ↦ᵣ u5) ** (.x6 ↦ᵣ u6) ** (.x7 ↦ᵣ u7) ** (.x28 ↦ᵣ u28) **
       (blkCountPtr ↦ₘ (0 : Word)))
      ((.x5 ↦ᵣ blkCountPtr) ** (.x6 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ EvmAsm.Stateless.ACCOUNT_WRITES_AREA) ** (.x28 ↦ᵣ (0 : Word)) **
       (blkCountPtr ↦ₘ (0 : Word))) := by
  unfold accountWritesLookupCurrent_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- indices 44, 45: `la t0, account_writes_count`
  have Q0 := auipc_spec_gen_within .x5 u5
    (laHi GuestAddrs.account_writes_count
      (GuestAddrs.account_writes_lookup_current + 176))
    (base + (176 : Word)) (by nofun)
  have Q1 := addi_spec_gen_same_within .x5
    ((base + (176 : Word)) +
      (((laHi GuestAddrs.account_writes_count
          (GuestAddrs.account_writes_lookup_current + 176)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.account_writes_count
      (GuestAddrs.account_writes_lookup_current + 176))
    (base + (180 : Word)) (by nofun)
  rw [hla] at Q1
  -- index 46: `ld t1, 0(t0)` — the block-tier row count
  have Q2 := ld_spec_gen_within .x6 .x5 blkCountPtr u6 (0 : Word) (0 : BitVec 12)
    (base + (184 : Word)) (by nofun)
  rw [show blkCountPtr + signExtend12 (0 : BitVec 12) = blkCountPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at Q2
  -- indices 47..49: materialise ACCOUNT_WRITES_AREA into t2
  have Q3 := lui_spec_gen_within .x7 u7
    (((EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat >>> 12) >>> 12) : BitVec 20)
    (base + (188 : Word)) (by nofun)
  rw [show ((((((EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat >>> 12) >>> 12) : BitVec 20)
      ).zeroExtend 32 <<< 12).signExtend 64) = (774144 : Word) from by decide] at Q3
  have Q4 := addiw_spec_gen_same_within .x7 (774144 : Word)
    (((EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat >>> 12) % 4096) : BitVec 12)
    (base + (192 : Word)) (by nofun)
  rw [show ((((774144 : Word).truncate 32 +
      (signExtend12 (((EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat >>> 12) % 4096) :
        BitVec 12)).truncate 32 : BitVec 32)).signExtend 64) = (775522 : Word) from by
    decide] at Q4
  have Q5 := slli_spec_gen_same_within .x7 (775522 : Word) (12 : BitVec 6)
    (base + (196 : Word)) (by nofun)
  rw [show ((775522 : Word) <<< (12 : BitVec 6).toNat)
      = EvmAsm.Stateless.ACCOUNT_WRITES_AREA from by decide] at Q5
  -- index 50: `li t3, 0` — the block-tier scan cursor
  have Q6 := li_spec_gen_within .x28 u28 (0 : Word) (base + (200 : Word)) (by nofun)
  -- index 51: `bgeu t3, t1, .Lawlc_absent` — TAKEN, the block tier is empty
  have QB := bgeu_spec_gen_within .x28 .x6
    (brOff (GuestAddrs.account_writes_lookup_current + 368)
      (GuestAddrs.account_writes_lookup_current + 204))
    (0 : Word) (0 : Word) (base + (204 : Word))
  rw [hbr, show base + (204 : Word) + (164 : Word) = base + (368 : Word) from by bv_omega]
    at QB
  have Q7 : cpsTripleWithin 1 (base + (204 : Word)) (base + (368 : Word))
      (CodeReq.singleton (base + (204 : Word)) (.BGEU .x28 .x6
        (brOff (GuestAddrs.account_writes_lookup_current + 368)
          (GuestAddrs.account_writes_lookup_current + 204))))
      ((.x28 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)))
      ((.x28 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word))) :=
    cpsBranchWithin_takenStripPure2 QB (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact absurd h_pure.2 (by decide))
  runBlock Q0 Q1 Q2 Q3 Q4 Q5 Q6 Q7

/-! ## Segment C — the `.Lawlc_absent` answer and the epilogue -/

/-- `account_writes_lookup_current` instructions 92..98
    (`base + 368 .. base + 392`): the absent triple `a0 = 0`, `a1 = 0`,
    `a2 = 0`, then reload `ra` and `s0`, pop the 24-byte frame, and `ret`.

    Unlike the two write-map writers, this epilogue DOES restore everything it
    saved: the prologue saved exactly `ra` and `s0` and this reloads exactly
    those two.  `t0`-`t3` are not saved and not restored — they are
    caller-saved scratch, and the post below carries their clobbered values
    rather than framing them away. -/
theorem accountWritesLookupCurrent_segC_body_spec
    (base sp ra link v8 w8 w10 w11 w12 : Word) :
    cpsTripleWithin 7 (base + (368 : Word)) (ra &&& ~~~(1 : Word))
      (CodeReq.ofProg base accountWritesLookupCurrent_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ link) ** (.x2 ↦ᵣ (sp - (24 : Word))) **
       (.x8 ↦ᵣ w8) ** (.x10 ↦ᵣ w10) ** (.x11 ↦ᵣ w11) ** (.x12 ↦ᵣ w12) **
       ((sp - (24 : Word)) ↦ₘ ra) ** ((sp - (16 : Word)) ↦ₘ v8))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x8 ↦ᵣ v8) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
       (.x12 ↦ᵣ (0 : Word)) **
       ((sp - (24 : Word)) ↦ₘ ra) ** ((sp - (16 : Word)) ↦ₘ v8)) := by
  unfold accountWritesLookupCurrent_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- indices 92..94: `li a0, 0` / `li a1, 0` / `li a2, 0` — the absent answer
  have R0 := li_spec_gen_within .x10 w10 (0 : Word) (base + (368 : Word)) (by nofun)
  have R1 := li_spec_gen_within .x11 w11 (0 : Word) (base + (372 : Word)) (by nofun)
  have R2 := li_spec_gen_within .x12 w12 (0 : Word) (base + (376 : Word)) (by nofun)
  -- index 95: `ld ra, 0(sp)`
  have R3 := ld_spec_gen_within .x1 .x2 (sp - (24 : Word)) link ra (0 : BitVec 12)
    (base + (380 : Word)) (by nofun)
  rw [show (sp - (24 : Word)) + signExtend12 (0 : BitVec 12) = sp - (24 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at R3
  -- index 96: `ld s0, 8(sp)`
  have R4 := ld_spec_gen_within .x8 .x2 (sp - (24 : Word)) w8 v8 (8 : BitVec 12)
    (base + (384 : Word)) (by nofun)
  rw [show (sp - (24 : Word)) + signExtend12 (8 : BitVec 12) = sp - (16 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at R4
  -- index 97: `addi sp, sp, 24`
  have R5 := addi_spec_gen_same_within .x2 (sp - (24 : Word)) (24 : BitVec 12)
    (base + (388 : Word)) (by nofun)
  rw [show (sp - (24 : Word)) + signExtend12 (24 : BitVec 12) = sp from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]; bv_omega] at R5
  -- index 98: `ret`
  have R6 := EvmAsm.Evm64.ret_spec_within' (base + (392 : Word)) ra
  runBlock R0 R1 R2 R3 R4 R5 R6

/-! ## The deployed (anchored) whole-routine contract -/

/-- ⭐ **`account_writes_lookup_current`, whole routine, both-tiers-empty arm.**

    Entry `GuestAddrs.account_writes_lookup_current`, exit `ra &&& ~~~1` — the
    caller's return address — over
    `CodeReq.ofProg (GuestAddrs.account_writes_lookup_current : Word)
    accountWritesLookupCurrent_prog`, which IS the
    `Codegen/Proofs/GuestImageEntries.lean:409` pairing.  Entry and code
    requirement are anchored at the same address, so this grades
    `whole-routine` under `scripts/proof-frontier.py`'s `shape_of_theorem`.

    ⭐ **A single `ofProg`, not a union — and that is checked.**  The two
    write-map WRITERS needed a two-program union because neither has a
    terminating arm that stays inside its own bytes.  This routine is a LEAF:
    `accountWritesLookupCurrent_prog` contains no `jal ra, …`, only `JAL .x0`
    internal jumps and the closing `jalr x0, 0(ra)`.  No callee contract is
    needed and none is assumed.

    Two named gates select the arm:

    * `tx_account_writes_count = 0` — the transaction tier is empty, so the
      scan's `bgeu` at index 11 is taken with zero iterations;
    * `account_writes_count = 0` — the block tier is empty, so the second
      scan's `bgeu` at index 51 is taken with zero iterations.

    Under both, the routine answers **absent**: `a0 = 0`, `a1 = 0`, `a2 = 0`
    (the `.Lawlc_absent` triple at indices 92..94), restores `ra`, `s0` and
    `sp`, and returns.  Because `cpsTripleWithin` quantifies over an arbitrary
    `pcFree` frame, the triple ALSO says — for free — that the routine writes
    nothing at all and does not even touch `TX_ACCOUNT_WRITES_AREA` or
    `ACCOUNT_WRITES_AREA`, since neither arena is named in the pre or the post.

    ⚠️ `t0`-`t3` (`x5`, `x6`, `x7`, `x28`) are CLOBBERED and the post says so:
    they come back holding the block-tier count pointer, `0`,
    `ACCOUNT_WRITES_AREA` and `0`.  They are caller-saved, so this is correct,
    but it is stated rather than framed.  `t4`-`t6` are touched only inside
    the scan bodies this arm skips, so they are not named at all.

    ⚠️ NOT proven here: both hit arms (indices 12..43 and 52..83) and the
    three non-zero answers `a0 = 1` / `2` / `3`.  Those need the 20-byte
    address comparison invariant and a per-tier loop invariant, and they are
    where the tie to the account write-map model will be made. -/
theorem accountWritesLookupCurrentAbsentFlat_spec
    (sp ra v5 v6 v7 v8 v10 v11 v12 v28 : Word) :
    cpsTripleWithin 27 (GuestAddrs.account_writes_lookup_current : Word)
      (ra &&& ~~~(1 : Word))
      (CodeReq.ofProg (GuestAddrs.account_writes_lookup_current : Word)
        accountWritesLookupCurrent_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x8 ↦ᵣ v8) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x28 ↦ᵣ v28) **
       memOwn (sp - (24 : Word)) ** memOwn (sp - (16 : Word)) **
       ((GuestAddrs.tx_account_writes_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.account_writes_count : Word) ↦ₘ (0 : Word)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x5 ↦ᵣ (GuestAddrs.account_writes_count : Word)) ** (.x6 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ EvmAsm.Stateless.ACCOUNT_WRITES_AREA) ** (.x8 ↦ᵣ v8) **
       (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
       (.x28 ↦ᵣ (0 : Word)) **
       ((sp - (24 : Word)) ↦ₘ ra) ** ((sp - (16 : Word)) ↦ₘ v8) **
       ((GuestAddrs.tx_account_writes_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.account_writes_count : Word) ↦ₘ (0 : Word))) := by
  -- segment A: prologue .. the transaction-tier `bgeu`
  have hA := accountWritesLookupCurrent_segA_body_spec
    (GuestAddrs.account_writes_lookup_current : Word) sp ra
    (GuestAddrs.tx_account_writes_count : Word) v5 v6 v7 v8 v10 v28
    (by decide) (by decide)
  -- the block-tier count and the two argument registers segment C writes are
  -- not in segment A's footprint; carry them across it by the frame rule
  have hA := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     ((GuestAddrs.account_writes_count : Word) ↦ₘ (0 : Word)))
    (by pcf) hA
  -- segment B: the block tier and its `bgeu`
  have hB := accountWritesLookupCurrent_segB_body_spec
    (GuestAddrs.account_writes_lookup_current : Word)
    (GuestAddrs.account_writes_count : Word)
    (GuestAddrs.tx_account_writes_count : Word) (0 : Word)
    EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA (0 : Word)
    (by decide) (by decide)
  -- segment C: the absent answer and the epilogue
  have hC := accountWritesLookupCurrent_segC_body_spec
    (GuestAddrs.account_writes_lookup_current : Word) sp ra ra v8 v10 v10 v11 v12
  seqFrame hA hB
  seqFrame hAhB hC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hAhBhC

/-! ## Non-vacuity

  Three checks, in the shape `docs/agents` asks for: a fully numeric instance
  (so a `True`-shaped or trivially satisfiable post could not have passed), a
  positive witness for each gate together with a NEGATIVE control showing the
  gate really excludes the inputs the routine is normally asked about, and a
  satisfiability check on the numeric precondition — `memOwn`/`↦ₘ` both
  *assert* `isValidDwordAccess`, so an unsatisfiable pre is a real risk rather
  than a formality. -/

/-- **Numeric instance.**  `sp = 0x30000000`, both tier counts 0, temps
    `1..4` and argument registers `20..22`, `s0 = 9`.  The post is fully
    concrete: `a0`/`a1`/`a2` all read back 0 (the absent answer, NOT their
    entry values `20`/`21`/`22`), `s0` is back at 9, `sp` is back at
    `0x30000000`, the two frame slots hold `ra` and 9, and `t0`-`t3` carry
    their clobbered values — the block-tier count pointer, 0,
    `ACCOUNT_WRITES_AREA`, 0. -/
example (ra : Word) :
    cpsTripleWithin 27 (GuestAddrs.account_writes_lookup_current : Word)
      (ra &&& ~~~(1 : Word))
      (CodeReq.ofProg (GuestAddrs.account_writes_lookup_current : Word)
        accountWritesLookupCurrent_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (0x30000000 : Word)) **
       (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (2 : Word)) ** (.x7 ↦ᵣ (3 : Word)) **
       (.x8 ↦ᵣ (9 : Word)) **
       (.x10 ↦ᵣ (20 : Word)) ** (.x11 ↦ᵣ (21 : Word)) ** (.x12 ↦ᵣ (22 : Word)) **
       (.x28 ↦ᵣ (4 : Word)) **
       memOwn (0x2fffffe8 : Word) ** memOwn (0x2ffffff0 : Word) **
       ((GuestAddrs.tx_account_writes_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.account_writes_count : Word) ↦ₘ (0 : Word)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (0x30000000 : Word)) **
       (.x5 ↦ᵣ (GuestAddrs.account_writes_count : Word)) ** (.x6 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ EvmAsm.Stateless.ACCOUNT_WRITES_AREA) ** (.x8 ↦ᵣ (9 : Word)) **
       (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
       (.x28 ↦ᵣ (0 : Word)) **
       ((0x2fffffe8 : Word) ↦ₘ ra) ** ((0x2ffffff0 : Word) ↦ₘ (9 : Word)) **
       ((GuestAddrs.tx_account_writes_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.account_writes_count : Word) ↦ₘ (0 : Word))) := by
  have h := accountWritesLookupCurrentAbsentFlat_spec (0x30000000 : Word) ra
    1 2 3 9 20 21 22 4
  rw [show (0x30000000 : Word) - (24 : Word) = (0x2fffffe8 : Word) from by decide,
      show (0x30000000 : Word) - (16 : Word) = (0x2ffffff0 : Word) from by decide] at h
  exact h

/-- **Gate witnesses and negative controls.**

    1. `¬ 0 <ᵤ 0` inhabits both gates: with an empty tier the `bgeu t3, t1` at
       index 11 (and again at index 51) IS taken with zero iterations, which
       is why this arm needs no loop invariant.
    2. `¬ ¬ (0 <ᵤ 1)` is provably FALSE — so a tier holding even ONE row makes
       the corresponding `bgeu` fall through into the scan body, and the hit
       arms really are OUTSIDE this triple rather than silently covered.  The
       same control fires for the transaction tier (index 11) and the block
       tier (index 51), which is why BOTH counts must be gated: an empty
       transaction tier alone does not reach `.Lawlc_absent`.
    3. The `.Lawlc_absent` label and the three non-zero answers live at four
       DISTINCT addresses, so "the absent triple" is a real selection among
       arms and not the routine's only exit. -/
example :
    (¬ BitVec.ult (0 : Word) (0 : Word))
    ∧ ¬ (¬ BitVec.ult (0 : Word) (1 : Word))
    ∧ (GuestAddrs.account_writes_lookup_current + 368
        ≠ GuestAddrs.account_writes_lookup_current + 328)
    ∧ (GuestAddrs.account_writes_lookup_current + 368
        ≠ GuestAddrs.account_writes_lookup_current + 336)
    ∧ (GuestAddrs.account_writes_lookup_current + 368
        ≠ GuestAddrs.account_writes_lookup_current + 352)
    ∧ (GuestAddrs.account_writes_lookup_current + 176
        ≠ GuestAddrs.account_writes_lookup_current + 48) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Satisfiability of the numeric instance's precondition.**  Both frame
    slots and both tier counters are valid, 8-byte-aligned dword addresses,
    and the two counters are distinct from each other and from the frame — so
    the separating conjunction is inhabitable and the numeric post above is
    not vacuously true.  The two arena bases are also distinct, which is the
    #12600 property this proof depends on: if the block-tier trio still built
    `0xBDB80000` the two tiers would alias. -/
example :
    isValidDwordAccess (0x2fffffe8 : Word) = true ∧
    isValidDwordAccess (0x2ffffff0 : Word) = true ∧
    isValidDwordAccess (GuestAddrs.tx_account_writes_count : Word) = true ∧
    isValidDwordAccess (GuestAddrs.account_writes_count : Word) = true ∧
    (GuestAddrs.tx_account_writes_count : Word)
      ≠ (GuestAddrs.account_writes_count : Word) ∧
    (GuestAddrs.tx_account_writes_count : Word) ≠ (0x2fffffe8 : Word) ∧
    (GuestAddrs.account_writes_count : Word) ≠ (0x2ffffff0 : Word) ∧
    EvmAsm.Stateless.ACCOUNT_WRITES_AREA
      ≠ EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   by decide⟩

/-! ## Axiom audit — classical-only. -/

#print axioms accountWritesLookupCurrentAbsentFlat_spec

end EvmAsm.Codegen.Proofs
