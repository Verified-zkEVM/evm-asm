/-
  EvmAsm.Codegen.Proofs.AccountWritesLatestBalanceSpec

  **The `account_writes_latest_balance` machine triple — both-tiers-empty
  arm (#11921).**

  `account_writes_latest_balance` (`Codegen/Programs/AccountWriteMap.lean`,
  `accountWritesLatestBalance_prog`, 80 instructions at
  `GuestAddrs.account_writes_latest_balance`, image entry
  `Codegen/Proofs/GuestImageEntries.lean`) answers "what is this account's
  balance as of now" over the two account-write tiers: log the read through
  `account_read_record`, then scan the TRANSACTION tier
  (`TX_ACCOUNT_WRITES_AREA`, `tx_account_writes_count` rows) for the 20-byte
  address, then the BLOCK tier (`ACCOUNT_WRITES_AREA`,
  `account_writes_count` rows).  A row wins only if its field mask carries
  BALANCE (`andi t0, t0, 1` on `+112`); on a win the four balance dwords at
  `+32 .. +56` are copied to the caller's `a1` out-pointer and `a0 = 1`,
  otherwise `a0 = 0`.

  ## ⭐ Why the `CodeReq` IS a union here, unlike the two leaves

  `Codegen/Proofs/AccountWritesLookupCurrentSpec.lean` and
  `Codegen/Proofs/StorageWritesBlockUpsertSpec.lean` could each state their
  arm over a single `CodeReq.ofProg`, because those two routines are leaves.
  **This one is not, and the reason is stronger than for the two writers:**
  `account_write_record`'s calls sit on particular arms, so "no arm both
  returns and stays inside" took an argument.  Here the
  `jal ra, account_read_record` at instruction index 7 (`AWLB + 28`) is
  **unconditional and above every branch in the routine** — every path
  through `account_writes_latest_balance` leaves its own bytes, immediately.
  So `awlbCR` unions the routine's 80 instructions at their linked
  `GuestAddrs` entry with `accountReadRecord_prog` at its own.

  ⭐ **The callee contract is REUSED, not re-proved.**
  `accountReadRecordSuppressedFlat_spec` (`Codegen/Proofs/AccountReadRecordSpec.lean`)
  already states `account_read_record`'s suppressed arm as a whole-routine
  triple at `GuestAddrs.account_read_record`, and it lines up with this call
  site exactly: it preserves `ra`, `sp`, `a0` and `t0`-`t6`, so the caller's
  scan state and out-pointer survive the call by the frame rule.  This module
  adds no second copy of it (`scripts/check-duplicate-decls.py` stays at its
  pinned 9).

  ## What this module proves

  `accountWritesLatestBalanceAbsentFlat_spec`, a 51-step whole-routine triple
  entry → `ret` under three named gates:

  * `runtime_tx_account_read_suppress ≠ 0` — the callee's own gate, inherited
    verbatim; read logging is suppressed, so `account_read_record` returns
    without touching the read log;
  * `tx_account_writes_count ↦ₘ 0` — the transaction tier is empty, so the
    scan's `bgeu t3, t1` at index 15 is taken with ZERO iterations;
  * `account_writes_count ↦ₘ 0` — the block tier is empty likewise, so the
    second scan's `bgeu` at index 43 is taken with ZERO iterations.

  Under those the routine answers **no balance override**: `a0 = 0` (index
  74), the caller's `a1` out-buffer is NOT written, and `ra`, `s0`, `s1` and
  `sp` come back intact.  Because `cpsTripleWithin` universally quantifies
  over a `pcFree` frame, the triple ALSO says — for free, since neither arena
  nor the out-buffer is named in the pre or the post — that the routine writes
  nothing at all on this arm.  "The out-pointer is left alone when no tier
  claims the account" is the load-bearing half of that: a caller may keep its
  own value there.

  ⚠️ **Register discipline, read from the epilogue rather than a docstring**
  (#13182 is why).  Indices 75..77 reload exactly the `ra`/`s0`/`s1` triple
  indices 1..3 spilled, and index 78 pops the 32-byte frame.  `t0`-`t3` are
  neither saved nor restored — they are caller-saved scratch, and the post
  states their clobbered values (`t0` = the block-tier count pointer, `t1` = 0,
  `t2` = `ACCOUNT_WRITES_AREA`, `t3` = 0) rather than framing them away.
  `t4`-`t6` are preserved: the callee's contract restores them and the scan
  bodies that would clobber them are skipped.

  ## ⚠️ What is deliberately NOT proven

  Both hit arms (indices 16..35 and 44..63) and the balance-copy tail at
  indices 64..73, which is where the four dwords at `+32 .. +56` reach the
  caller's out-pointer and `a0` becomes 1.  Those need the 20-byte
  address-comparison invariant and a per-tier loop invariant (measure
  `count − t3`), and they are where the machine gets tied to the account
  write-map model.  Also not proven: `account_read_record`'s unsuppressed arm
  — this triple inherits the callee's gate rather than discharging it.  The
  registry row is therefore `.conditional` with all three gates named.

  ## `Nodup`

  As in `AccountWritesLookupCurrentSpec`, uniqueness does not arise: this is a
  READER, so it constructs no row sequence.  Uniqueness would be a CONSUMED
  fact on a hit arm ("the first matching row is the right one"), and on the
  both-tiers-empty arm there is no matching row, so the question is vacuous
  and nothing is assumed.  The hypothesis-free model theorem
  `accountWriteUpsert_rowsMap` (#11938) is consumed when a hit arm is proved.

  ## Mechanics

  Same pilot rules as `AccountWriteRecordSpec`: present the code requirement
  as the `singleton`-union chain (`unfold` + `CodeReq.ofProg_cons`) before
  `runBlock`, write every offset `(k : Word)`, compose segments with
  `seqFrame`, and put the single call site behind the `awlb_callSite7`
  adapter over `WP.cpsCallWithin`.  The file is not `module`-ised because
  `CodeReq.ofProg_mem_at` and `CodeReq.Disjoint.ofProg_ranges` live in
  non-`module` `Rv64/SAsm` files.

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
import EvmAsm.Codegen.Proofs.AccountReadRecordSpec

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen

/-! ## Segment A — prologue and the call arguments -/

/-- `account_writes_latest_balance` instructions 0..6 at a free `base`: the
    three-slot prologue (`ra`, `s0`, `s1`), `mv s0, a0` / `mv s1, a1` — the
    address pointer and the balance out-pointer — and `mv a0, s0`, which
    re-materialises the address pointer as the `account_read_record`
    argument. -/
theorem accountWritesLatestBalance_segA_body_spec
    (base sp ra v8 v9 v10 v11 : Word) :
    cpsTripleWithin 7 base (base + (28 : Word))
      (CodeReq.ofProg base accountWritesLatestBalance_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       memOwn (sp - (32 : Word)) ** memOwn (sp - (24 : Word)) **
       memOwn (sp - (16 : Word)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp - (32 : Word))) **
       (.x8 ↦ᵣ v10) ** (.x9 ↦ᵣ v11) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       ((sp - (32 : Word)) ↦ₘ ra) ** ((sp - (24 : Word)) ↦ₘ v8) **
       ((sp - (16 : Word)) ↦ₘ v9)) := by
  unfold accountWritesLatestBalance_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 0: `addi sp, sp, -32`
  have P0 := addi_spec_gen_same_within .x2 sp (-32 : BitVec 12) base (by nofun)
  rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide,
      show sp + (-32 : Word) = sp - (32 : Word) from by bv_omega] at P0
  -- indices 1..3: spill ra, s0, s1
  have P1 := sd_spec_gen_own_within .x2 .x1 (sp - (32 : Word)) ra (0 : BitVec 12)
    (base + (4 : Word))
  rw [show (sp - (32 : Word)) + signExtend12 (0 : BitVec 12) = sp - (32 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at P1
  have P2 := sd_spec_gen_own_within .x2 .x8 (sp - (32 : Word)) v8 (8 : BitVec 12)
    (base + (8 : Word))
  rw [show (sp - (32 : Word)) + signExtend12 (8 : BitVec 12) = sp - (24 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at P2
  have P3 := sd_spec_gen_own_within .x2 .x9 (sp - (32 : Word)) v9 (16 : BitVec 12)
    (base + (12 : Word))
  rw [show (sp - (32 : Word)) + signExtend12 (16 : BitVec 12) = sp - (16 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at P3
  -- index 4: `mv s0, a0` — the 20-byte address pointer
  have P4 := mv_spec_gen_within .x8 .x10 v10 v8 (base + (16 : Word)) (by nofun)
  -- index 5: `mv s1, a1` — the balance out-pointer
  have P5 := mv_spec_gen_within .x9 .x11 v11 v9 (base + (20 : Word)) (by nofun)
  -- index 6: `mv a0, s0` — the `account_read_record` argument
  have P6 := mv_spec_gen_within .x10 .x8 v10 v10 (base + (24 : Word)) (by nofun)
  runBlock P0 P1 P2 P3 P4 P5 P6

/-! ## Segment B — the transaction tier and its empty-tier exit -/

/-- `account_writes_latest_balance` instructions 8..15
    (`base + 32 .. base + 144`): `la t0, tx_account_writes_count`, load the
    transaction-tier row count, materialise `TX_ACCOUNT_WRITES_AREA` into
    `t2`, `li t3, 0`, and take the scan's `bgeu` — TAKEN, the tier is
    empty. -/
theorem accountWritesLatestBalance_segB_body_spec
    (base txCountPtr u5 u6 u7 u28 : Word)
    (hla : base + (32 : Word) +
        (((laHi GuestAddrs.tx_account_writes_count
            (GuestAddrs.account_writes_latest_balance + 32)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.tx_account_writes_count
          (GuestAddrs.account_writes_latest_balance + 32)) = txCountPtr)
    (hbr : signExtend13 (brOff (GuestAddrs.account_writes_latest_balance + 144)
        (GuestAddrs.account_writes_latest_balance + 60)) = (84 : Word)) :
    cpsTripleWithin 8 (base + (32 : Word)) (base + (144 : Word))
      (CodeReq.ofProg base accountWritesLatestBalance_prog)
      ((.x5 ↦ᵣ u5) ** (.x6 ↦ᵣ u6) ** (.x7 ↦ᵣ u7) ** (.x28 ↦ᵣ u28) **
       (txCountPtr ↦ₘ (0 : Word)))
      ((.x5 ↦ᵣ txCountPtr) ** (.x6 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA) ** (.x28 ↦ᵣ (0 : Word)) **
       (txCountPtr ↦ₘ (0 : Word))) := by
  unfold accountWritesLatestBalance_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  have Q0 := auipc_spec_gen_within .x5 u5
    (laHi GuestAddrs.tx_account_writes_count
      (GuestAddrs.account_writes_latest_balance + 32))
    (base + (32 : Word)) (by nofun)
  have Q1 := addi_spec_gen_same_within .x5
    ((base + (32 : Word)) +
      (((laHi GuestAddrs.tx_account_writes_count
          (GuestAddrs.account_writes_latest_balance + 32)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.tx_account_writes_count
      (GuestAddrs.account_writes_latest_balance + 32))
    (base + (36 : Word)) (by nofun)
  rw [hla] at Q1
  have Q2 := ld_spec_gen_within .x6 .x5 txCountPtr u6 (0 : Word) (0 : BitVec 12)
    (base + (40 : Word)) (by nofun)
  rw [show txCountPtr + signExtend12 (0 : BitVec 12) = txCountPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at Q2
  have Q3 := lui_spec_gen_within .x7 u7
    (((EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat >>> 12) >>> 12) : BitVec 20)
    (base + (44 : Word)) (by nofun)
  rw [show ((((((EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat >>> 12) >>> 12) : BitVec 20)
      ).zeroExtend 32 <<< 12).signExtend 64) = (782336 : Word) from by decide] at Q3
  have Q4 := addiw_spec_gen_same_within .x7 (782336 : Word)
    (((EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat >>> 12) % 4096) : BitVec 12)
    (base + (48 : Word)) (by nofun)
  rw [show ((((782336 : Word).truncate 32 +
      (signExtend12 (((EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat >>> 12) % 4096) :
        BitVec 12)).truncate 32 : BitVec 32)).signExtend 64) = (784256 : Word) from by
    decide] at Q4
  have Q5 := slli_spec_gen_same_within .x7 (784256 : Word) (12 : BitVec 6)
    (base + (52 : Word)) (by nofun)
  rw [show ((784256 : Word) <<< (12 : BitVec 6).toNat)
      = EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA from by decide] at Q5
  have Q6 := li_spec_gen_within .x28 u28 (0 : Word) (base + (56 : Word)) (by nofun)
  have QB := bgeu_spec_gen_within .x28 .x6
    (brOff (GuestAddrs.account_writes_latest_balance + 144)
      (GuestAddrs.account_writes_latest_balance + 60))
    (0 : Word) (0 : Word) (base + (60 : Word))
  rw [hbr, show base + (60 : Word) + (84 : Word) = base + (144 : Word) from by bv_omega]
    at QB
  have Q7 : cpsTripleWithin 1 (base + (60 : Word)) (base + (144 : Word))
      (CodeReq.singleton (base + (60 : Word)) (.BGEU .x28 .x6
        (brOff (GuestAddrs.account_writes_latest_balance + 144)
          (GuestAddrs.account_writes_latest_balance + 60))))
      ((.x28 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)))
      ((.x28 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word))) :=
    cpsBranchWithin_takenStripPure2 QB (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact absurd h_pure.2 (by decide))
  runBlock Q0 Q1 Q2 Q3 Q4 Q5 Q6 Q7

/-! ## Segment C — the block tier and its empty-tier exit -/

/-- `account_writes_latest_balance` instructions 36..43
    (`base + 144 .. base + 296`): the same eight-instruction shape against
    `account_writes_count` and `ACCOUNT_WRITES_AREA`, `bgeu` again TAKEN.

    ⭐ The base materialisation here is the #12600 fix: the trio used to build
    `0xBDB80000`, the PRE-`e799e986c` block-tier arena, so every phase-2
    balance lookup scanned dead zero-filled memory.  This proof steps through
    the corrected encoding, derived from the `ACCOUNT_WRITES_AREA` layout
    constant. -/
theorem accountWritesLatestBalance_segC_body_spec
    (base blkCountPtr w5 w6 w7 w28 : Word)
    (hla : base + (144 : Word) +
        (((laHi GuestAddrs.account_writes_count
            (GuestAddrs.account_writes_latest_balance + 144)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.account_writes_count
          (GuestAddrs.account_writes_latest_balance + 144)) = blkCountPtr)
    (hbr : signExtend13 (brOff (GuestAddrs.account_writes_latest_balance + 296)
        (GuestAddrs.account_writes_latest_balance + 172)) = (124 : Word)) :
    cpsTripleWithin 8 (base + (144 : Word)) (base + (296 : Word))
      (CodeReq.ofProg base accountWritesLatestBalance_prog)
      ((.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) **
       (blkCountPtr ↦ₘ (0 : Word)))
      ((.x5 ↦ᵣ blkCountPtr) ** (.x6 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ EvmAsm.Stateless.ACCOUNT_WRITES_AREA) ** (.x28 ↦ᵣ (0 : Word)) **
       (blkCountPtr ↦ₘ (0 : Word))) := by
  unfold accountWritesLatestBalance_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  have S0 := auipc_spec_gen_within .x5 w5
    (laHi GuestAddrs.account_writes_count
      (GuestAddrs.account_writes_latest_balance + 144))
    (base + (144 : Word)) (by nofun)
  have S1 := addi_spec_gen_same_within .x5
    ((base + (144 : Word)) +
      (((laHi GuestAddrs.account_writes_count
          (GuestAddrs.account_writes_latest_balance + 144)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.account_writes_count
      (GuestAddrs.account_writes_latest_balance + 144))
    (base + (148 : Word)) (by nofun)
  rw [hla] at S1
  have S2 := ld_spec_gen_within .x6 .x5 blkCountPtr w6 (0 : Word) (0 : BitVec 12)
    (base + (152 : Word)) (by nofun)
  rw [show blkCountPtr + signExtend12 (0 : BitVec 12) = blkCountPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at S2
  have S3 := lui_spec_gen_within .x7 w7
    (((EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat >>> 12) >>> 12) : BitVec 20)
    (base + (156 : Word)) (by nofun)
  rw [show ((((((EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat >>> 12) >>> 12) : BitVec 20)
      ).zeroExtend 32 <<< 12).signExtend 64) = (774144 : Word) from by decide] at S3
  have S4 := addiw_spec_gen_same_within .x7 (774144 : Word)
    (((EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat >>> 12) % 4096) : BitVec 12)
    (base + (160 : Word)) (by nofun)
  rw [show ((((774144 : Word).truncate 32 +
      (signExtend12 (((EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat >>> 12) % 4096) :
        BitVec 12)).truncate 32 : BitVec 32)).signExtend 64) = (775522 : Word) from by
    decide] at S4
  have S5 := slli_spec_gen_same_within .x7 (775522 : Word) (12 : BitVec 6)
    (base + (164 : Word)) (by nofun)
  rw [show ((775522 : Word) <<< (12 : BitVec 6).toNat)
      = EvmAsm.Stateless.ACCOUNT_WRITES_AREA from by decide] at S5
  have S6 := li_spec_gen_within .x28 w28 (0 : Word) (base + (168 : Word)) (by nofun)
  have SB := bgeu_spec_gen_within .x28 .x6
    (brOff (GuestAddrs.account_writes_latest_balance + 296)
      (GuestAddrs.account_writes_latest_balance + 172))
    (0 : Word) (0 : Word) (base + (172 : Word))
  rw [hbr, show base + (172 : Word) + (124 : Word) = base + (296 : Word) from by bv_omega]
    at SB
  have S7 : cpsTripleWithin 1 (base + (172 : Word)) (base + (296 : Word))
      (CodeReq.singleton (base + (172 : Word)) (.BGEU .x28 .x6
        (brOff (GuestAddrs.account_writes_latest_balance + 296)
          (GuestAddrs.account_writes_latest_balance + 172))))
      ((.x28 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)))
      ((.x28 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word))) :=
    cpsBranchWithin_takenStripPure2 SB (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact absurd h_pure.2 (by decide))
  runBlock S0 S1 S2 S3 S4 S5 S6 S7

/-! ## Segment D — the "no override" answer and the epilogue -/

/-- `account_writes_latest_balance` instructions 74..79
    (`base + 296 .. base + 316`): `li a0, 0` — no tier claims this account's
    balance — then reload `ra`, `s0`, `s1`, pop the 32-byte frame, and `ret`.

    ⭐ The out-pointer `a1` is NOT written on this arm, and that is the
    load-bearing part: a caller may leave its own value in the out-buffer and
    read `a0 = 0` as "unchanged".  The triple says so by NOT naming the buffer
    anywhere, which the universally quantified `pcFree` frame turns into a
    no-write guarantee. -/
theorem accountWritesLatestBalance_segD_body_spec
    (base sp ra link v8 v9 y8 y9 y10 : Word) :
    cpsTripleWithin 6 (base + (296 : Word)) (ra &&& ~~~(1 : Word))
      (CodeReq.ofProg base accountWritesLatestBalance_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ link) ** (.x2 ↦ᵣ (sp - (32 : Word))) **
       (.x8 ↦ᵣ y8) ** (.x9 ↦ᵣ y9) ** (.x10 ↦ᵣ y10) **
       ((sp - (32 : Word)) ↦ₘ ra) ** ((sp - (24 : Word)) ↦ₘ v8) **
       ((sp - (16 : Word)) ↦ₘ v9))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ (0 : Word)) **
       ((sp - (32 : Word)) ↦ₘ ra) ** ((sp - (24 : Word)) ↦ₘ v8) **
       ((sp - (16 : Word)) ↦ₘ v9)) := by
  unfold accountWritesLatestBalance_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 74: `li a0, 0` — no balance override
  have T0 := li_spec_gen_within .x10 y10 (0 : Word) (base + (296 : Word)) (by nofun)
  -- indices 75..77: reload ra, s0, s1
  have T1 := ld_spec_gen_within .x1 .x2 (sp - (32 : Word)) link ra (0 : BitVec 12)
    (base + (300 : Word)) (by nofun)
  rw [show (sp - (32 : Word)) + signExtend12 (0 : BitVec 12) = sp - (32 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at T1
  have T2 := ld_spec_gen_within .x8 .x2 (sp - (32 : Word)) y8 v8 (8 : BitVec 12)
    (base + (304 : Word)) (by nofun)
  rw [show (sp - (32 : Word)) + signExtend12 (8 : BitVec 12) = sp - (24 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at T2
  have T3 := ld_spec_gen_within .x9 .x2 (sp - (32 : Word)) y9 v9 (16 : BitVec 12)
    (base + (308 : Word)) (by nofun)
  rw [show (sp - (32 : Word)) + signExtend12 (16 : BitVec 12) = sp - (16 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at T3
  -- index 78: `addi sp, sp, 32`
  have T4 := addi_spec_gen_same_within .x2 (sp - (32 : Word)) (32 : BitVec 12)
    (base + (312 : Word)) (by nofun)
  rw [show (sp - (32 : Word)) + signExtend12 (32 : BitVec 12) = sp from by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]; bv_omega] at T4
  -- index 79: `ret`
  have T5 := EvmAsm.Evm64.ret_spec_within' (base + (316 : Word)) ra
  runBlock T0 T1 T2 T3 T4 T5

/-! ## The deployed (anchored) whole-routine contract -/

/-- The routine's linked entry. -/
abbrev AWLB : Word := (GuestAddrs.account_writes_latest_balance : Word)

/-- Its one callee, on its linked entry. -/
abbrev ARR : Word := (GuestAddrs.account_read_record : Word)

/-- `account_writes_latest_balance`'s code requirement: its own 80
    instructions at `GuestAddrs.account_writes_latest_balance`, plus the
    routine it calls.

    The union is FORCED, and more plainly than for the two write-map writers:
    the `jal ra, account_read_record` at instruction index 7 is UNCONDITIONAL
    and sits above every branch, so EVERY path through this routine leaves its
    own bytes. -/
def awlbCR : CodeReq :=
  (CodeReq.ofProg (GuestAddrs.account_writes_latest_balance : Word)
      accountWritesLatestBalance_prog).union
    (CodeReq.ofProg (GuestAddrs.account_read_record : Word) accountReadRecord_prog)

theorem awlb_disj_readRecord :
    (CodeReq.ofProg AWLB accountWritesLatestBalance_prog).Disjoint
      (CodeReq.ofProg ARR accountReadRecord_prog) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem awlbProg_sub_awlbCR :
    ∀ a i, CodeReq.ofProg AWLB accountWritesLatestBalance_prog a = some i →
      awlbCR a = some i :=
  CodeReq.union_mono_left

/-- Call-site adapter for the `jal ra, account_read_record` at instruction
    index 7 (`AWLB + 28`) — the unconditional read-log call. -/
theorem awlb_callSite7 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n ARR ((AWLB + (28 : Word) + 4) &&& ~~~(1 : Word))
      (CodeReq.ofProg ARR accountReadRecord_prog)
      ((.x1 ↦ᵣ (AWLB + (28 : Word) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (AWLB + (28 : Word)) (AWLB + (28 : Word) + 4) awlbCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := AWLB + (28 : Word)) (calleeEntry := ARR) (vOld := vRa)
    (calleeCode := CodeReq.ofProg ARR accountReadRecord_prog)
    (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.account_read_record
      (GuestAddrs.account_writes_latest_balance + 28))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at AWLB (AWLB + (28 : Word)) accountWritesLatestBalance_prog 7 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right awlb_disj_readRecord (fun _ _ h => h) a i h

/-- ⭐ **`account_writes_latest_balance`, whole routine, both-tiers-empty arm.**

    Entry `GuestAddrs.account_writes_latest_balance`, exit `ra &&& ~~~1` — the
    caller's return address — over `awlbCR`, which pairs the linked
    `GuestAddrs` entry with `accountWritesLatestBalance_prog` exactly as
    `GuestImageEntries` does, unioned with the one routine it calls.

    ⭐ **The union is forced by an UNCONDITIONAL call.** Unlike
    `account_write_record`, where "no arm both returns and stays inside" took
    an argument about which arms reach which `jal`, here the
    `jal ra, account_read_record` at index 7 sits above every branch: every
    path leaves the routine's own bytes immediately.  And unlike the two
    #11921 leaves (`account_writes_lookup_current`,
    `storage_writes_block_upsert`), a single `CodeReq.ofProg` cannot state
    anything at all here.

    ⭐ **The callee contract is reused, not re-proved:**
    `accountReadRecordSuppressedFlat_spec`, already landed, whose suppressed
    arm preserves `ra`, `sp`, `a0` and `t0`-`t6` — exactly what this caller
    needs to survive the call.

    Three named gates select the arm:

    * `hsuppress : runtime_tx_account_read_suppress ≠ 0` — the callee's own
      gate, inherited verbatim rather than discharged;
    * `tx_account_writes_count = 0` — the transaction tier is empty, so the
      scan's `bgeu` at index 15 is taken with zero iterations;
    * `account_writes_count = 0` — the block tier is empty, so the second
      scan's `bgeu` at index 43 is taken with zero iterations.

    Under those the routine answers **no balance override**: `a0 = 0`, and the
    caller's `a1` out-buffer is left ALONE — which the triple states by not
    naming it, the `pcFree` frame turning that silence into a no-write
    guarantee over the whole routine.  `ra`, `s0`, `s1` and `sp` come back
    intact, as do `t4`-`t6` (the callee restores them and the scan bodies are
    skipped).

    ⚠️ `t0`-`t3` are CLOBBERED and the post says so: the block-tier count
    pointer, `0`, `ACCOUNT_WRITES_AREA` and `0`.  They are caller-saved, and —
    unlike #13182's finding about `account_write_record` — this matches what
    the epilogue actually does: indices 75..77 reload exactly the `ra`/`s0`/`s1`
    triple indices 1..3 spilled.

    ⚠️ NOT proven: both hit arms (indices 16..35 and 44..63), the balance-copy
    tail at indices 64..73, and `account_read_record`'s unsuppressed arm. -/
theorem accountWritesLatestBalanceAbsentFlat_spec
    (sp ra suppressVal v5 v6 v7 v8 v9 v10 v11 v28 v29 v30 v31 : Word)
    (hsuppress : suppressVal ≠ (0 : Word)) :
    cpsTripleWithin 51 (GuestAddrs.account_writes_latest_balance : Word)
      (ra &&& ~~~(1 : Word))
      awlbCR
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       memOwn (sp - (96 : Word)) ** memOwn (sp - (88 : Word)) **
       memOwn (sp - (80 : Word)) ** memOwn (sp - (72 : Word)) **
       memOwn (sp - (64 : Word)) ** memOwn (sp - (56 : Word)) **
       memOwn (sp - (48 : Word)) **
       memOwn (sp - (32 : Word)) ** memOwn (sp - (24 : Word)) **
       memOwn (sp - (16 : Word)) **
       ((GuestAddrs.runtime_tx_account_read_suppress : Word) ↦ₘ suppressVal) **
       ((GuestAddrs.tx_account_writes_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.account_writes_count : Word) ↦ₘ (0 : Word)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x5 ↦ᵣ (GuestAddrs.account_writes_count : Word)) ** (.x6 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ EvmAsm.Stateless.ACCOUNT_WRITES_AREA) **
       (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) **
       (.x28 ↦ᵣ (0 : Word)) **
       (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       ((sp - (96 : Word)) ↦ₘ v5) ** ((sp - (88 : Word)) ↦ₘ v6) **
       ((sp - (80 : Word)) ↦ₘ v7) ** ((sp - (72 : Word)) ↦ₘ v28) **
       ((sp - (64 : Word)) ↦ₘ v29) ** ((sp - (56 : Word)) ↦ₘ v30) **
       ((sp - (48 : Word)) ↦ₘ v31) **
       ((sp - (32 : Word)) ↦ₘ ra) ** ((sp - (24 : Word)) ↦ₘ v8) **
       ((sp - (16 : Word)) ↦ₘ v9) **
       ((GuestAddrs.runtime_tx_account_read_suppress : Word) ↦ₘ suppressVal) **
       ((GuestAddrs.tx_account_writes_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.account_writes_count : Word) ↦ₘ (0 : Word))) := by
  -- segment A: prologue and the call arguments
  have hA := cpsTripleWithin_extend_code awlbProg_sub_awlbCR
    (accountWritesLatestBalance_segA_body_spec AWLB sp ra v8 v9 v10 v11)
  -- everything the callee and segments B..D touch that segment A does not
  have hA := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
     memOwn (sp - (96 : Word)) ** memOwn (sp - (88 : Word)) **
     memOwn (sp - (80 : Word)) ** memOwn (sp - (72 : Word)) **
     memOwn (sp - (64 : Word)) ** memOwn (sp - (56 : Word)) **
     memOwn (sp - (48 : Word)) **
     ((GuestAddrs.runtime_tx_account_read_suppress : Word) ↦ₘ suppressVal) **
     ((GuestAddrs.tx_account_writes_count : Word) ↦ₘ (0 : Word)) **
     ((GuestAddrs.account_writes_count : Word) ↦ₘ (0 : Word)))
    (by pcf) hA
  -- the callee, on its already-proven suppressed arm, permuted so that the
  -- link register leads (`WP.cpsCallWithin`'s shape)
  have hU0 := accountReadRecordSuppressedFlat_spec (sp - (32 : Word))
    (AWLB + (28 : Word) + 4) v10 suppressVal v5 v6 v7 v28 v29 v30 v31 hsuppress
  rw [show (sp - (32 : Word)) - (64 : Word) = sp - (96 : Word) from by bv_omega,
      show (sp - (32 : Word)) - (56 : Word) = sp - (88 : Word) from by bv_omega,
      show (sp - (32 : Word)) - (48 : Word) = sp - (80 : Word) from by bv_omega,
      show (sp - (32 : Word)) - (40 : Word) = sp - (72 : Word) from by bv_omega,
      show (sp - (32 : Word)) - (32 : Word) = sp - (64 : Word) from by bv_omega,
      show (sp - (32 : Word)) - (24 : Word) = sp - (56 : Word) from by bv_omega,
      show (sp - (32 : Word)) - (16 : Word) = sp - (48 : Word) from by bv_omega] at hU0
  have hU : cpsTripleWithin 21 ARR ((AWLB + (28 : Word) + 4) &&& ~~~(1 : Word))
      (CodeReq.ofProg ARR accountReadRecord_prog)
      ((.x1 ↦ᵣ (AWLB + (28 : Word) + 4)) **
       ((.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (sp - (32 : Word))) ** (.x10 ↦ᵣ v10) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        memOwn (sp - (96 : Word)) ** memOwn (sp - (88 : Word)) **
        memOwn (sp - (80 : Word)) ** memOwn (sp - (72 : Word)) **
        memOwn (sp - (64 : Word)) ** memOwn (sp - (56 : Word)) **
        memOwn (sp - (48 : Word)) **
        ((GuestAddrs.runtime_tx_account_read_suppress : Word) ↦ₘ suppressVal)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (AWLB + (28 : Word) + 4)) **
       (.x2 ↦ᵣ (sp - (32 : Word))) ** (.x10 ↦ᵣ v10) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       ((sp - (96 : Word)) ↦ₘ v5) ** ((sp - (88 : Word)) ↦ₘ v6) **
       ((sp - (80 : Word)) ↦ₘ v7) ** ((sp - (72 : Word)) ↦ₘ v28) **
       ((sp - (64 : Word)) ↦ₘ v29) ** ((sp - (56 : Word)) ↦ₘ v30) **
       ((sp - (48 : Word)) ↦ₘ v31) **
       ((GuestAddrs.runtime_tx_account_read_suppress : Word) ↦ₘ suppressVal)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hU0
  have hCall := awlb_callSite7 (n := 21) ra (by pcf) hU
  rw [show AWLB + (28 : Word) + 4 = AWLB + (32 : Word) from by bv_omega] at hCall
  -- segment B: the transaction tier
  have hB := cpsTripleWithin_extend_code awlbProg_sub_awlbCR
    (accountWritesLatestBalance_segB_body_spec AWLB
      (GuestAddrs.tx_account_writes_count : Word) v5 v6 v7 v28
      (by decide) (by decide))
  -- segment C: the block tier
  have hC := cpsTripleWithin_extend_code awlbProg_sub_awlbCR
    (accountWritesLatestBalance_segC_body_spec AWLB
      (GuestAddrs.account_writes_count : Word)
      (GuestAddrs.tx_account_writes_count : Word) (0 : Word)
      EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA (0 : Word)
      (by decide) (by decide))
  -- segment D: the "no override" answer and the epilogue
  have hD := cpsTripleWithin_extend_code awlbProg_sub_awlbCR
    (accountWritesLatestBalance_segD_body_spec AWLB sp ra (AWLB + (32 : Word))
      v8 v9 v10 v11 v10)
  seqFrame hA hCall
  seqFrame hAhCall hB
  seqFrame hAhCallhB hC
  seqFrame hAhCallhBhC hD
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hAhCallhBhChD

/-! ## Non-vacuity

  Three checks, in the shape `docs/agents` asks for: a fully numeric instance
  (so a `True`-shaped or trivially satisfiable post could not have passed),
  positive witnesses and NEGATIVE controls for the gates, and a
  satisfiability check on the numeric precondition — `memOwn`/`↦ₘ` both
  *assert* `isValidDwordAccess`, so an unsatisfiable pre is a real risk rather
  than a formality. -/

/-- **Numeric instance.**  `sp = 0x30000000`, suppression flag `1`, both tier
    counts 0, temps `1..7`, `s0 = 8`, `s1 = 9` (the out-pointer the routine
    does not write), argument registers `20`/`21`.  The post is fully
    concrete: `a0` reads back 0 rather than its entry value 20, `s0`/`s1` are
    back at 8/9, `sp` at `0x30000000`, the callee's seven spill slots at
    `0x2fffffa0 .. 0x2fffffd0` hold `1..7` in spill order and the caller's
    three at `0x2fffffe0 .. 0x2ffffff0` hold `ra`, 8 and 9. -/
example (ra : Word) :
    cpsTripleWithin 51 (GuestAddrs.account_writes_latest_balance : Word)
      (ra &&& ~~~(1 : Word))
      awlbCR
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (0x30000000 : Word)) **
       (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (2 : Word)) ** (.x7 ↦ᵣ (3 : Word)) **
       (.x8 ↦ᵣ (8 : Word)) ** (.x9 ↦ᵣ (9 : Word)) **
       (.x10 ↦ᵣ (20 : Word)) ** (.x11 ↦ᵣ (21 : Word)) **
       (.x28 ↦ᵣ (4 : Word)) ** (.x29 ↦ᵣ (5 : Word)) ** (.x30 ↦ᵣ (6 : Word)) **
       (.x31 ↦ᵣ (7 : Word)) **
       memOwn (0x2fffffa0 : Word) ** memOwn (0x2fffffa8 : Word) **
       memOwn (0x2fffffb0 : Word) ** memOwn (0x2fffffb8 : Word) **
       memOwn (0x2fffffc0 : Word) ** memOwn (0x2fffffc8 : Word) **
       memOwn (0x2fffffd0 : Word) **
       memOwn (0x2fffffe0 : Word) ** memOwn (0x2fffffe8 : Word) **
       memOwn (0x2ffffff0 : Word) **
       ((GuestAddrs.runtime_tx_account_read_suppress : Word) ↦ₘ (1 : Word)) **
       ((GuestAddrs.tx_account_writes_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.account_writes_count : Word) ↦ₘ (0 : Word)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (0x30000000 : Word)) **
       (.x5 ↦ᵣ (GuestAddrs.account_writes_count : Word)) ** (.x6 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ EvmAsm.Stateless.ACCOUNT_WRITES_AREA) **
       (.x8 ↦ᵣ (8 : Word)) ** (.x9 ↦ᵣ (9 : Word)) **
       (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (21 : Word)) **
       (.x28 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ (5 : Word)) ** (.x30 ↦ᵣ (6 : Word)) **
       (.x31 ↦ᵣ (7 : Word)) **
       ((0x2fffffa0 : Word) ↦ₘ (1 : Word)) ** ((0x2fffffa8 : Word) ↦ₘ (2 : Word)) **
       ((0x2fffffb0 : Word) ↦ₘ (3 : Word)) ** ((0x2fffffb8 : Word) ↦ₘ (4 : Word)) **
       ((0x2fffffc0 : Word) ↦ₘ (5 : Word)) ** ((0x2fffffc8 : Word) ↦ₘ (6 : Word)) **
       ((0x2fffffd0 : Word) ↦ₘ (7 : Word)) **
       ((0x2fffffe0 : Word) ↦ₘ ra) ** ((0x2fffffe8 : Word) ↦ₘ (8 : Word)) **
       ((0x2ffffff0 : Word) ↦ₘ (9 : Word)) **
       ((GuestAddrs.runtime_tx_account_read_suppress : Word) ↦ₘ (1 : Word)) **
       ((GuestAddrs.tx_account_writes_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.account_writes_count : Word) ↦ₘ (0 : Word))) := by
  have h := accountWritesLatestBalanceAbsentFlat_spec (0x30000000 : Word) ra
    1 1 2 3 8 9 20 21 4 5 6 7 (by decide)
  rw [show (0x30000000 : Word) - (96 : Word) = (0x2fffffa0 : Word) from by decide,
      show (0x30000000 : Word) - (88 : Word) = (0x2fffffa8 : Word) from by decide,
      show (0x30000000 : Word) - (80 : Word) = (0x2fffffb0 : Word) from by decide,
      show (0x30000000 : Word) - (72 : Word) = (0x2fffffb8 : Word) from by decide,
      show (0x30000000 : Word) - (64 : Word) = (0x2fffffc0 : Word) from by decide,
      show (0x30000000 : Word) - (56 : Word) = (0x2fffffc8 : Word) from by decide,
      show (0x30000000 : Word) - (48 : Word) = (0x2fffffd0 : Word) from by decide,
      show (0x30000000 : Word) - (32 : Word) = (0x2fffffe0 : Word) from by decide,
      show (0x30000000 : Word) - (24 : Word) = (0x2fffffe8 : Word) from by decide,
      show (0x30000000 : Word) - (16 : Word) = (0x2ffffff0 : Word) from by decide]
    at h
  exact h

/-- **Gate witnesses and negative controls.**

    1. `(1 : Word) ≠ 0` inhabits `hsuppress`, the callee's gate.
    2. `¬ ((0 : Word) ≠ 0)` is provably FALSE, so a ZERO suppression flag —
       i.e. read logging ENABLED, the ordinary case — is genuinely EXCLUDED
       from this triple rather than silently covered.  That is the arm of
       `account_read_record` this proof does not claim.
    3. `¬ 0 <ᵤ 0` inhabits both tier gates: with an empty tier the
       `bgeu t3, t1` at index 15 (and again at 43) IS taken with zero
       iterations.
    4. `¬ ¬ (0 <ᵤ 1)` is provably FALSE, so a tier holding even ONE row falls
       through into the scan body and the hit arms are outside the triple.
       The control fires for both tiers, which is why both counts are gated.
    5. The `.Lawlb_none` answer (index 74, `+296`) and the balance-copy tail
       (index 64, `+256`) are distinct addresses, so `a0 = 0` is a real
       selection among arms.
    6. The union `CodeReq` is not degenerate: the caller's entry and the
       callee's entry are distinct addresses. -/
example :
    ((1 : Word) ≠ (0 : Word))
    ∧ ¬ ((0 : Word) ≠ (0 : Word))
    ∧ (¬ BitVec.ult (0 : Word) (0 : Word))
    ∧ ¬ (¬ BitVec.ult (0 : Word) (1 : Word))
    ∧ (GuestAddrs.account_writes_latest_balance + 296
        ≠ GuestAddrs.account_writes_latest_balance + 256)
    ∧ (GuestAddrs.account_writes_latest_balance ≠ GuestAddrs.account_read_record) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Satisfiability of the numeric instance's precondition.**  All ten frame
    slots — the callee's seven and the caller's three — and all three globals
    are valid, 8-byte-aligned dword addresses; the callee's frame sits strictly
    below the caller's, so the two do not alias; and the three globals are
    pairwise distinct and disjoint from the frame. -/
example :
    isValidDwordAccess (0x2fffffa0 : Word) = true ∧
    isValidDwordAccess (0x2fffffa8 : Word) = true ∧
    isValidDwordAccess (0x2fffffb0 : Word) = true ∧
    isValidDwordAccess (0x2fffffb8 : Word) = true ∧
    isValidDwordAccess (0x2fffffc0 : Word) = true ∧
    isValidDwordAccess (0x2fffffc8 : Word) = true ∧
    isValidDwordAccess (0x2fffffd0 : Word) = true ∧
    isValidDwordAccess (0x2fffffe0 : Word) = true ∧
    isValidDwordAccess (0x2fffffe8 : Word) = true ∧
    isValidDwordAccess (0x2ffffff0 : Word) = true ∧
    isValidDwordAccess (GuestAddrs.runtime_tx_account_read_suppress : Word) = true ∧
    isValidDwordAccess (GuestAddrs.tx_account_writes_count : Word) = true ∧
    isValidDwordAccess (GuestAddrs.account_writes_count : Word) = true ∧
    ((0x2fffffd0 : Word) < (0x2fffffe0 : Word)) ∧
    (GuestAddrs.runtime_tx_account_read_suppress : Word)
      ≠ (GuestAddrs.tx_account_writes_count : Word) ∧
    (GuestAddrs.tx_account_writes_count : Word)
      ≠ (GuestAddrs.account_writes_count : Word) ∧
    (GuestAddrs.account_writes_count : Word) ≠ (0x2fffffa0 : Word) ∧
    (GuestAddrs.runtime_tx_account_read_suppress : Word) ≠ (0x2ffffff0 : Word) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   by decide, by decide, by decide, by decide⟩

/-! ## Axiom audit — classical-only. -/

#print axioms accountWritesLatestBalanceAbsentFlat_spec

end EvmAsm.Codegen.Proofs
