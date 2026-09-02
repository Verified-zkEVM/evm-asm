/-
  EvmAsm.Codegen.Proofs.BalBuilderEnsureAccountSpec

  **The `bal_builder_ensure_account` machine triple — intern-into-an-empty-table
  arm (#11921).**

  `bal_builder_ensure_account` (`Codegen/Programs/BlockAccessListBuilder.lean`,
  `balBuilderEnsureAccount_prog`, 67 instructions at
  `GuestAddrs.bal_builder_ensure_account`, image entry in
  `Codegen/Proofs/GuestImageEntries.lean`) is the BAL builder's **only**
  account-table writer: given a canonical BE20 address in `a0`, it bytewise
  compares that key against each of the `bal_builder_account_count` existing
  24-byte-stride rows, returning the row index on a hit; on a miss it appends
  the key and returns the new index; at capacity (140000 rows) it latches
  `bal_builder_overflow` and returns `-1`.

  ## Why this routine, and why first

  It is the **keystone callee of three of the six** `jal ra` targets of
  `account_writes_emit_builder_tx` (#11921's last unrowed routine):
  `bal_builder_append_balance` (index 5), `bal_builder_append_nonce` (index 5)
  and `bal_builder_append_code` (index 6) each open with an UNCONDITIONAL
  `jal ra, bal_builder_ensure_account` sitting above every branch, then
  immediately branch on its `a0`.  So none of those three can be stated over a
  single `CodeReq.ofProg` — and none of them can be stated at all until this
  routine has a contract.

  ⭐ And unlike its three callers, this routine **is a leaf**: it contains no
  `jal ra` at all (`balBuilderEnsureAccount_relocs` carries two `la`s and one
  more `la`, no cross-`jal`).  So its `CodeReq` is a single `CodeReq.ofProg` —
  the `AccountWritesLookupCurrentSpec` / `StorageWritesBlockUpsertSpec` shape,
  not the union shape #13176/#13179/#13186 needed.

  ## What this module proves

  `balBuilderEnsureAccountAppendEmptyFlat_spec`, a **179-step whole-routine
  triple** entry → `ret` under one named gate:

  * `bal_builder_account_count ↦ₘ 0` — the account table is empty.

  Under it the routine **interns the address at row 0**: the 20 key bytes are
  copied from the caller's buffer into `bal_builder_accounts`, the count cell
  goes `0 → 1`, and `a0 = 0` — the stable table index.  This is a
  value-producing arm, not a fail-closed one; it is the second such in the
  #11921 wave (after `storageWritesBlockUpsertAppendFlat_spec`).

  ⭐ **Why the empty-table arm is the only one reachable in a bounded trace.**
  The scan's guard at index 14 is `bgeu s3, s2` with `s3 = 0`, so it is taken
  — skipping the comparison loop entirely — **iff** the count is zero.  Any
  other arm runs the 20-byte comparison loop once per existing row, and the
  capacity arm at index 54 additionally needs the count to reach 140000, which
  means 140000 scan iterations first.  The empty-table arm is therefore not the
  interesting arm, only the reachable one — the same honesty as #13176/#13179.

  ## The copy loop is real, and it is `countdownLoop_spec`

  Unlike every other #11921 row so far, this arm does **not** skip its loop:
  indices 42..48 are a genuine twenty-iteration bytewise copy
  (`beq t0, x0, exit` top guard; `lbu`/`sb`/two cursor bumps/`addi t0, t0, -1`;
  `jal x0` back-edge).  It is discharged by `Rv64/SAsm/AbiFrameLoop.lean`'s
  `countdownLoop_spec` over the invariant "the first `20 − n` key bytes are
  already in the row", which is why the step count is `20 * (6 + 1) + 1 = 141`
  of the 179.  The per-iteration body triple
  (`balBuilderEnsureAccount_copyBody_spec`) follows `hesrCopyBody`
  (`Codegen/Programs/HeaderFieldsSpecBlocksTail.lean`) — the same
  `bytesRegion_lbu_within` / `bytesRegion_sb_within` / `copyIntoRegion` idiom.

  ⚠️ Note the cursor roles are the reverse of `hesrCopyBody`'s: here `t1`
  (`x6`) is the **destination** row cursor and `t2` (`x7`) the **source** key
  cursor, read off the Program rather than the docstring.

  ## ⚠️ Register discipline, read from the epilogue (#13182 is why)

  Indices 59..64 reload exactly the six `s`-registers indices 1..6 spilled
  (`s0`,`s1`,`s2`,`s3`,`s4`,`s5` = `x8`,`x9`,`x18`,`x19`,`x20`,`x21`), index 65
  pops the 48-byte frame and index 66 is `ret`.  **`ra` is neither spilled nor
  reloaded** — this is a leaf, and the frame has no `ra` slot at all, so `ra`
  survives because nothing writes it.  `t0`-`t2` (`x5`,`x6`,`x7`) and `x28` are
  caller-saved scratch: the post states their clobbered values rather than
  framing them away.

  ## ⚠️ What is deliberately NOT proven

  The hit arm (indices 15..31 — the per-row 20-byte comparison loop and its
  early-mismatch break), the append-at-a-nonzero-index arm, and the capacity
  arm at index 54 that latches `bal_builder_overflow`.  Those need the scan
  loop's own invariant (measure `count − s3`) plus the table-uniqueness
  vocabulary, and they are where the machine gets tied to the interning model.
  The registry row is therefore `.conditional` with the empty-table gate named.

  ## Mechanics

  Same pilot rules as `AccountWritesLatestBalanceSpec`: present the code
  requirement as the `singleton`-union chain (`unfold` + `CodeReq.ofProg_cons`)
  before `runBlock`, write every offset `(k : Word)`, and compose segments with
  `seqFrame`.  The file is not `module`-ised because `CodeReq.ofProg_mem_at`
  lives in a non-`module` `Rv64/SAsm` file.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only
  (audited by the `#print axioms` at the end of this file).
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.SAsm.AbiFrameLoop
import EvmAsm.Rv64.SAsm.CtrlSpecs
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Evm64.Terminating.ReturnWindowLoopSpec
import EvmAsm.Codegen.Programs.BlockAccessListBuilder

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen

/-- The routine's linked entry. -/
abbrev BBEA : Word := (GuestAddrs.bal_builder_ensure_account : Word)

/-- `bal_builder_ensure_account`'s code requirement.  A single
    `CodeReq.ofProg` — the routine is a LEAF, so unlike #13176/#13179/#13186
    no union is needed. -/
def bbeaCR : CodeReq :=
  CodeReq.ofProg BBEA balBuilderEnsureAccount_prog

/-! ## Segment A — prologue, the two `la`s, and the empty-table guard -/

/-- `bal_builder_ensure_account` instructions 0..14 (`base .. base + 128`):
    push the 48-byte frame, spill the six `s`-registers, `mv s0, a0` (the BE20
    key pointer), `la s1, bal_builder_account_count` + load the count into
    `s2`, `li s3, 0`, `la s4, bal_builder_accounts`, and take the scan guard
    `bgeu s3, s2` — TAKEN, because the table is empty, so the comparison loop
    runs zero times. -/
theorem balBuilderEnsureAccount_segA_body_spec
    (base sp addrPtr countPtr accountsBase v8 v9 v18 v19 v20 v21 : Word)
    (hlaCount : base + (32 : Word) +
        (((laHi GuestAddrs.bal_builder_account_count
            (GuestAddrs.bal_builder_ensure_account + 32)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.bal_builder_account_count
          (GuestAddrs.bal_builder_ensure_account + 32)) = countPtr)
    (hlaAcc : base + (48 : Word) +
        (((laHi GuestAddrs.bal_builder_accounts
            (GuestAddrs.bal_builder_ensure_account + 48)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.bal_builder_accounts
          (GuestAddrs.bal_builder_ensure_account + 48)) = accountsBase)
    (hbr : signExtend13 (brOff (GuestAddrs.bal_builder_ensure_account + 128)
        (GuestAddrs.bal_builder_ensure_account + 56)) = (72 : Word)) :
    cpsTripleWithin 15 base (base + (128 : Word))
      (CodeReq.ofProg base balBuilderEnsureAccount_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ sp) **
       (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ addrPtr) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
       memOwn (sp - (48 : Word)) ** memOwn (sp - (40 : Word)) **
       memOwn (sp - (32 : Word)) ** memOwn (sp - (24 : Word)) **
       memOwn (sp - (16 : Word)) ** memOwn (sp - (8 : Word)) **
       (countPtr ↦ₘ (0 : Word)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (sp - (48 : Word))) **
       (.x8 ↦ᵣ addrPtr) ** (.x9 ↦ᵣ countPtr) ** (.x10 ↦ᵣ addrPtr) **
       (.x18 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ (0 : Word)) **
       (.x20 ↦ᵣ accountsBase) ** (.x21 ↦ᵣ v21) **
       ((sp - (48 : Word)) ↦ₘ v8) ** ((sp - (40 : Word)) ↦ₘ v9) **
       ((sp - (32 : Word)) ↦ₘ v18) ** ((sp - (24 : Word)) ↦ₘ v19) **
       ((sp - (16 : Word)) ↦ₘ v20) ** ((sp - (8 : Word)) ↦ₘ v21) **
       (countPtr ↦ₘ (0 : Word))) := by
  unfold balBuilderEnsureAccount_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 0: `addi sp, sp, -48`
  have P0 := addi_spec_gen_same_within .x2 sp (-48 : BitVec 12) base (by nofun)
  rw [show signExtend12 (-48 : BitVec 12) = (-48 : Word) from by decide,
      show sp + (-48 : Word) = sp - (48 : Word) from by bv_omega] at P0
  -- indices 1..6: spill s0, s1, s2, s3, s4, s5
  have P1 := sd_spec_gen_own_within .x2 .x8 (sp - (48 : Word)) v8 (0 : BitVec 12)
    (base + (4 : Word))
  rw [show (sp - (48 : Word)) + signExtend12 (0 : BitVec 12) = sp - (48 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at P1
  have P2 := sd_spec_gen_own_within .x2 .x9 (sp - (48 : Word)) v9 (8 : BitVec 12)
    (base + (8 : Word))
  rw [show (sp - (48 : Word)) + signExtend12 (8 : BitVec 12) = sp - (40 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at P2
  have P3 := sd_spec_gen_own_within .x2 .x18 (sp - (48 : Word)) v18 (16 : BitVec 12)
    (base + (12 : Word))
  rw [show (sp - (48 : Word)) + signExtend12 (16 : BitVec 12) = sp - (32 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at P3
  have P4 := sd_spec_gen_own_within .x2 .x19 (sp - (48 : Word)) v19 (24 : BitVec 12)
    (base + (16 : Word))
  rw [show (sp - (48 : Word)) + signExtend12 (24 : BitVec 12) = sp - (24 : Word) from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]; bv_omega] at P4
  have P5 := sd_spec_gen_own_within .x2 .x20 (sp - (48 : Word)) v20 (32 : BitVec 12)
    (base + (20 : Word))
  rw [show (sp - (48 : Word)) + signExtend12 (32 : BitVec 12) = sp - (16 : Word) from by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]; bv_omega] at P5
  have P6 := sd_spec_gen_own_within .x2 .x21 (sp - (48 : Word)) v21 (40 : BitVec 12)
    (base + (24 : Word))
  rw [show (sp - (48 : Word)) + signExtend12 (40 : BitVec 12) = sp - (8 : Word) from by
    rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]; bv_omega] at P6
  -- index 7: `mv s0, a0` — the BE20 key pointer
  have P7 := mv_spec_gen_within .x8 .x10 addrPtr v8 (base + (28 : Word)) (by nofun)
  -- indices 8..9: `la s1, bal_builder_account_count`
  have P8 := auipc_spec_gen_within .x9 v9
    (laHi GuestAddrs.bal_builder_account_count
      (GuestAddrs.bal_builder_ensure_account + 32))
    (base + (32 : Word)) (by nofun)
  have P9 := addi_spec_gen_same_within .x9
    ((base + (32 : Word)) +
      (((laHi GuestAddrs.bal_builder_account_count
          (GuestAddrs.bal_builder_ensure_account + 32)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.bal_builder_account_count
      (GuestAddrs.bal_builder_ensure_account + 32))
    (base + (36 : Word)) (by nofun)
  rw [hlaCount] at P9
  -- index 10: `ld s2, 0(s1)` — the row count, zero on this arm
  have P10 := ld_spec_gen_within .x18 .x9 countPtr v18 (0 : Word) (0 : BitVec 12)
    (base + (40 : Word)) (by nofun)
  rw [show countPtr + signExtend12 (0 : BitVec 12) = countPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at P10
  -- index 11: `li s3, 0` — the scan cursor
  have P11 := li_spec_gen_within .x19 v19 (0 : Word) (base + (44 : Word)) (by nofun)
  -- indices 12..13: `la s4, bal_builder_accounts`
  have P12 := auipc_spec_gen_within .x20 v20
    (laHi GuestAddrs.bal_builder_accounts
      (GuestAddrs.bal_builder_ensure_account + 48))
    (base + (48 : Word)) (by nofun)
  have P13 := addi_spec_gen_same_within .x20
    ((base + (48 : Word)) +
      (((laHi GuestAddrs.bal_builder_accounts
          (GuestAddrs.bal_builder_ensure_account + 48)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.bal_builder_accounts
      (GuestAddrs.bal_builder_ensure_account + 48))
    (base + (52 : Word)) (by nofun)
  rw [hlaAcc] at P13
  -- index 14: `bgeu s3, s2` — TAKEN, the table is empty
  have PB := bgeu_spec_gen_within .x19 .x18
    (brOff (GuestAddrs.bal_builder_ensure_account + 128)
      (GuestAddrs.bal_builder_ensure_account + 56))
    (0 : Word) (0 : Word) (base + (56 : Word))
  rw [hbr, show base + (56 : Word) + (72 : Word) = base + (128 : Word) from by bv_omega] at PB
  have P14 : cpsTripleWithin 1 (base + (56 : Word)) (base + (128 : Word))
      (CodeReq.singleton (base + (56 : Word)) (.BGEU .x19 .x18
        (brOff (GuestAddrs.bal_builder_ensure_account + 128)
          (GuestAddrs.bal_builder_ensure_account + 56))))
      ((.x19 ↦ᵣ (0 : Word)) ** (.x18 ↦ᵣ (0 : Word)))
      ((.x19 ↦ᵣ (0 : Word)) ** (.x18 ↦ᵣ (0 : Word))) :=
    cpsBranchWithin_takenStripPure2 PB (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact absurd h_pure.2 (by decide))
  runBlock P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14

/-! ## Segment B — the capacity check and the row-0 cursor setup -/

/-- `bal_builder_ensure_account` instructions 32..41 (`base + 128 ..
    base + 168`): materialise the 140000-row capacity into `t0`, take the
    `bgeu s2, t0` capacity branch — NOT taken, because the count is zero —
    then compute the row address `s5 = s4 + 24 * s2 = accountsBase`, and set up
    the copy loop's three registers: `t0 = 20` (the countdown), `t1 = s5` (the
    DESTINATION cursor) and `t2 = s0` (the SOURCE key cursor). -/
theorem balBuilderEnsureAccount_segB_body_spec
    (base addrPtr accountsBase w5 w6 w7 w21 : Word)
    (hbr : signExtend13 (brOff (GuestAddrs.bal_builder_ensure_account + 216)
        (GuestAddrs.bal_builder_ensure_account + 136)) = (80 : Word)) :
    cpsTripleWithin 10 (base + (128 : Word)) (base + (168 : Word))
      (CodeReq.ofProg base balBuilderEnsureAccount_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) **
       (.x8 ↦ᵣ addrPtr) ** (.x18 ↦ᵣ (0 : Word)) **
       (.x20 ↦ᵣ accountsBase) ** (.x21 ↦ᵣ w21))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (20 : Word)) ** (.x6 ↦ᵣ accountsBase) **
       (.x7 ↦ᵣ addrPtr) **
       (.x8 ↦ᵣ addrPtr) ** (.x18 ↦ᵣ (0 : Word)) **
       (.x20 ↦ᵣ accountsBase) ** (.x21 ↦ᵣ accountsBase)) := by
  unfold balBuilderEnsureAccount_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- indices 32..33: `li t0, 140000` as `lui` + `addiw`
  have Q0 := lui_spec_gen_within .x5 w5 (34 : BitVec 20) (base + (128 : Word)) (by nofun)
  rw [show ((((34 : BitVec 20)).zeroExtend 32 <<< 12).signExtend 64) = (139264 : Word) from by
    decide] at Q0
  have Q1 := addiw_spec_gen_same_within .x5 (139264 : Word) (736 : BitVec 12)
    (base + (132 : Word)) (by nofun)
  rw [show ((((139264 : Word).truncate 32 +
      (signExtend12 (736 : BitVec 12)).truncate 32 : BitVec 32)).signExtend 64)
      = (140000 : Word) from by decide] at Q1
  -- index 34: `bgeu s2, t0` — NOT taken, the table is far below capacity
  have QB := bgeu_spec_gen_within .x18 .x5
    (brOff (GuestAddrs.bal_builder_ensure_account + 216)
      (GuestAddrs.bal_builder_ensure_account + 136))
    (0 : Word) (140000 : Word) (base + (136 : Word))
  rw [hbr, show base + (136 : Word) + (4 : Word) = base + (140 : Word) from by bv_omega] at QB
  have Q2 : cpsTripleWithin 1 (base + (136 : Word)) (base + (140 : Word))
      (CodeReq.singleton (base + (136 : Word)) (.BGEU .x18 .x5
        (brOff (GuestAddrs.bal_builder_ensure_account + 216)
          (GuestAddrs.bal_builder_ensure_account + 136))))
      ((.x18 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (140000 : Word)))
      ((.x18 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (140000 : Word))) :=
    cpsBranchWithin_ntakenStripPure2 QB (fun hp hQt => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQt
      exact h_pure.2 (by decide))
  -- indices 35..38: `s5 = s4 + 24 * s2`, all zero here
  have Q3 := slli_spec_gen_within .x21 .x18 w21 (0 : Word) (1 : BitVec 6)
    (base + (140 : Word)) (by nofun)
  rw [show ((0 : Word) <<< (1 : BitVec 6).toNat) = (0 : Word) from by decide] at Q3
  have Q4 := add_spec_gen_rd_eq_rs1_within .x21 .x18 (0 : Word) (0 : Word)
    (base + (144 : Word)) (by nofun)
  rw [show (0 : Word) + (0 : Word) = (0 : Word) from by decide] at Q4
  have Q5 := slli_spec_gen_same_within .x21 (0 : Word) (3 : BitVec 6)
    (base + (148 : Word)) (by nofun)
  rw [show ((0 : Word) <<< (3 : BitVec 6).toNat) = (0 : Word) from by decide] at Q5
  have Q6 := add_spec_gen_rd_eq_rs2_within .x21 .x20 accountsBase (0 : Word)
    (base + (152 : Word)) (by nofun)
  rw [show accountsBase + (0 : Word) = accountsBase from by bv_omega] at Q6
  -- index 39: `li t0, 20` — the byte countdown
  have Q7 := li_spec_gen_within .x5 (140000 : Word) (20 : Word)
    (base + (156 : Word)) (by nofun)
  -- index 40: `mv t1, s5` — the DESTINATION cursor
  have Q8 := mv_spec_gen_within .x6 .x21 accountsBase w6 (base + (160 : Word)) (by nofun)
  -- index 41: `mv t2, s0` — the SOURCE key cursor
  have Q9 := mv_spec_gen_within .x7 .x8 addrPtr w7 (base + (164 : Word)) (by nofun)
  runBlock Q0 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9

end EvmAsm.Codegen.Proofs
