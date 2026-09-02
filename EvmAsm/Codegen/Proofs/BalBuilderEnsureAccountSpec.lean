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
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

/-- Local `PCFree` instance for `bytesRegion` (there is no global one — only
    section-scoped ones in the RLP files).  Without it `runBlock`/`seqFrame`'s
    `buildPcFreeProof` cannot discharge a frame containing the key or row
    region and silently leaves the frame metavariable unassigned. -/
local instance instPCFreeBytesRegion (b : Word) (bs : List (BitVec 8)) :
    Assertion.PCFree (bytesRegion b bs) := ⟨bytesRegion_pcFree b bs⟩

local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj
    | pcFree)

/-- Word decrement of a successor counter. -/
private theorem bbea_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- Pointer advance by 1 byte. -/
private theorem bbea_advance (b : Word) (m : Nat) :
    (b + BitVec.ofNat 64 m) + signExtend12 (1 : BitVec 12) = b + BitVec.ofNat 64 (m + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega

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

/-! ## Segment C — the twenty-iteration key copy

  Indices 42..48 are a genuine loop, not a skipped one:

  ```
  42:  beq  t0, x0, +28        -- exit to index 49 when the countdown drains
  43:  lbu  x28, 0(t2)         -- SOURCE byte (t2 = the caller's key cursor)
  44:  sb   0(t1), x28         -- DESTINATION byte (t1 = the row cursor)
  45:  addi t1, t1, 1
  46:  addi t2, t2, 1
  47:  addi t0, t0, -1
  48:  jal  x0, -24            -- back-edge to 42
  ```

  ⚠️ The cursor roles are the REVERSE of `hesrCopyBody`'s: `t1` writes and
  `t2` reads.  Read off the Program, not the sibling proof. -/

/-- The copy-loop invariant after `i` of the twenty key bytes have landed in
    the row: the two cursors sit `i` bytes in, `x28` holds whatever the last
    `lbu` left there, and the row region carries the first `i` key bytes. -/
def bbeaCopyInv (addrPtr accountsBase : Word)
    (srcBytes dstBytes : List (BitVec 8)) (i : Nat) : Assertion :=
  ((.x6 : Reg) ↦ᵣ (accountsBase + BitVec.ofNat 64 i)) **
  ((.x7 : Reg) ↦ᵣ (addrPtr + BitVec.ofNat 64 i)) ** regOwn .x28 **
  bytesRegion addrPtr srcBytes **
  bytesRegion accountsBase (copyIntoRegion dstBytes srcBytes 0 0 i)

theorem bbeaCopyInv_pcFree (addrPtr accountsBase : Word)
    (srcBytes dstBytes : List (BitVec 8)) (i : Nat) :
    (bbeaCopyInv addrPtr accountsBase srcBytes dstBytes i).pcFree := by
  unfold bbeaCopyInv; pcFreeR

/-- One iteration of the key copy (indices 43..48, `base + 172 → base + 168`):
    read key byte `i`, store it into row byte `i`, bump both cursors,
    decrement the countdown, and take the back-edge. -/
theorem balBuilderEnsureAccount_copyBody_spec
    (base addrPtr accountsBase : Word) (srcBytes dstBytes : List (BitVec 8))
    (i m : Nat)
    (h_src_align : addrPtr.toNat % 8 = 0)
    (h_dst_align : accountsBase.toNat % 8 = 0)
    (h_src_lt : i < srcBytes.length)
    (h_dst_lt : i < dstBytes.length)
    (h_src_over : addrPtr.toNat + srcBytes.length < 2 ^ 64)
    (h_dst_over : accountsBase.toNat + dstBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (addrPtr + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dstBytes.length →
      isValidByteAccess (accountsBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 6 (base + (172 : Word)) (base + (168 : Word))
      (CodeReq.ofProg base balBuilderEnsureAccount_prog)
      (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bbeaCopyInv addrPtr accountsBase srcBytes dstBytes i)
      (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 m) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bbeaCopyInv addrPtr accountsBase srcBytes dstBytes (i + 1)) := by
  unfold bbeaCopyInv
  have htrunc : ((srcBytes[i]'h_src_lt).zeroExtend 64).truncate 8 = (srcBytes[i]'h_src_lt) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have := (srcBytes[i]'h_src_lt).isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hgetd : srcBytes.getD i 0 = (srcBytes[i]'h_src_lt) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h_src_lt]
    simp
  have hstep : copyIntoRegion dstBytes srcBytes 0 0 (i + 1)
      = (copyIntoRegion dstBytes srcBytes 0 0 i).set i (srcBytes[i]'h_src_lt) := by
    simp only [copyIntoRegion, Nat.zero_add, hgetd]
  -- Peel `regOwn .x28` to a concrete entry value, quantified.
  suffices key : ∀ v28 : Word,
      cpsTripleWithin 6 (base + (172 : Word)) (base + (168 : Word))
        (CodeReq.ofProg base balBuilderEnsureAccount_prog)
        ((((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x6 : Reg) ↦ᵣ (accountsBase + BitVec.ofNat 64 i)) **
          ((.x7 : Reg) ↦ᵣ (addrPtr + BitVec.ofNat 64 i)) **
          bytesRegion addrPtr srcBytes **
          bytesRegion accountsBase (copyIntoRegion dstBytes srcBytes 0 0 i)) **
         ((.x28 : Reg) ↦ᵣ v28))
        (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 m) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         ((.x6 : Reg) ↦ᵣ (accountsBase + BitVec.ofNat 64 (i + 1))) **
         ((.x7 : Reg) ↦ᵣ (addrPtr + BitVec.ofNat 64 (i + 1))) ** regOwn .x28 **
         bytesRegion addrPtr srcBytes **
         bytesRegion accountsBase (copyIntoRegion dstBytes srcBytes 0 0 (i + 1))) by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => by
      xperm_chunked hq) (cpsTripleWithin_of_forall_regIs_to_regOwn key)
  intro v28
  -- With `x28` concrete, the six instructions run straight through; weaken the
  -- copied byte back to `regOwn` afterwards.
  suffices hbody : cpsTripleWithin 6 (base + (172 : Word)) (base + (168 : Word))
      (CodeReq.ofProg base balBuilderEnsureAccount_prog)
      (((.x7 : Reg) ↦ᵣ (addrPtr + BitVec.ofNat 64 i)) ** ((.x28 : Reg) ↦ᵣ v28) **
       bytesRegion addrPtr srcBytes **
       ((.x6 : Reg) ↦ᵣ (accountsBase + BitVec.ofNat 64 i)) **
       bytesRegion accountsBase (copyIntoRegion dstBytes srcBytes 0 0 i) **
       ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (((.x7 : Reg) ↦ᵣ (addrPtr + BitVec.ofNat 64 (i + 1))) **
       ((.x28 : Reg) ↦ᵣ ((srcBytes[i]'h_src_lt).zeroExtend 64)) **
       bytesRegion addrPtr srcBytes **
       ((.x6 : Reg) ↦ᵣ (accountsBase + BitVec.ofNat 64 (i + 1))) **
       bytesRegion accountsBase (copyIntoRegion dstBytes srcBytes 0 0 (i + 1)) **
       ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 m) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun sState hq => ?_) hbody
    have hq2 : (((.x28 : Reg) ↦ᵣ ((srcBytes[i]'h_src_lt).zeroExtend 64)) **
        ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 m) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x6 : Reg) ↦ᵣ (accountsBase + BitVec.ofNat 64 (i + 1))) **
        ((.x7 : Reg) ↦ᵣ (addrPtr + BitVec.ofNat 64 (i + 1))) **
        bytesRegion addrPtr srcBytes **
        bytesRegion accountsBase (copyIntoRegion dstBytes srcBytes 0 0 (i + 1))) sState := by
      xperm_chunked hq
    have hq3 := sepConj_mono_left (regIs_implies_regOwn .x28) _ hq2
    xperm_chunked hq3
  -- The five straight-line steps 43..47, then the back-edge composed by hand
  -- (`runBlock` reconciles a forward exit only; index 48 jumps BACKWARD).
  have hstraight : cpsTripleWithin 5 (base + (172 : Word)) (base + (192 : Word))
      (CodeReq.ofProg base balBuilderEnsureAccount_prog)
      (((.x7 : Reg) ↦ᵣ (addrPtr + BitVec.ofNat 64 i)) ** ((.x28 : Reg) ↦ᵣ v28) **
       bytesRegion addrPtr srcBytes **
       ((.x6 : Reg) ↦ᵣ (accountsBase + BitVec.ofNat 64 i)) **
       bytesRegion accountsBase (copyIntoRegion dstBytes srcBytes 0 0 i) **
       ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (m + 1)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (((.x7 : Reg) ↦ᵣ (addrPtr + BitVec.ofNat 64 (i + 1))) **
       ((.x28 : Reg) ↦ᵣ ((srcBytes[i]'h_src_lt).zeroExtend 64)) **
       bytesRegion addrPtr srcBytes **
       ((.x6 : Reg) ↦ᵣ (accountsBase + BitVec.ofNat 64 (i + 1))) **
       bytesRegion accountsBase (copyIntoRegion dstBytes srcBytes 0 0 (i + 1)) **
       ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 m) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) := by
    unfold balBuilderEnsureAccount_prog
    simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
    -- index 43: `lbu x28, 0(t2)` — the key byte
    have C0 := bytesRegion_lbu_within .x28 .x7 addrPtr v28 (base + (172 : Word))
      srcBytes i (by nofun) h_src_align h_src_lt (by omega) (h_src_valid i h_src_lt)
    -- index 44: `sb 0(t1), x28` — the row byte
    have C1 := bytesRegion_sb_within .x6 .x28 accountsBase ((srcBytes[i]'h_src_lt).zeroExtend 64)
      (base + (176 : Word)) (copyIntoRegion dstBytes srcBytes 0 0 i) i h_dst_align
      (by rw [copyIntoRegion_length]; omega) (by omega)
      (h_dst_valid i h_dst_lt)
    rw [htrunc, ← hstep] at C1
    -- index 45: `addi t1, t1, 1` — bump the row cursor
    have C2 := addi_spec_gen_same_within .x6
      (accountsBase + BitVec.ofNat 64 i) (1 : BitVec 12) (base + (180 : Word)) (by nofun)
    rw [bbea_advance accountsBase i] at C2
    -- index 46: `addi t2, t2, 1` — bump the key cursor
    have C3 := addi_spec_gen_same_within .x7
      (addrPtr + BitVec.ofNat 64 i) (1 : BitVec 12) (base + (184 : Word)) (by nofun)
    rw [bbea_advance addrPtr i] at C3
    -- index 47: `addi t0, t0, -1` — drain the countdown
    have C4 := addi_spec_gen_same_within .x5 (BitVec.ofNat 64 (m + 1)) (-1 : BitVec 12)
      (base + (188 : Word)) (by nofun)
    rw [bbea_succ_dec m] at C4
    runBlock C0 C1 C2 C3 C4
  -- index 48: `jal x0, -24` — the back-edge to the loop header
  have hjmem : ∀ a i',
      CodeReq.singleton (base + (192 : Word)) (.JAL .x0 (-24 : BitVec 21)) a = some i' →
      CodeReq.ofProg base balBuilderEnsureAccount_prog a = some i' :=
    CodeReq.ofProg_mem_at base (base + (192 : Word)) balBuilderEnsureAccount_prog 48
      (.JAL .x0 (-24 : BitVec 21)) (by bv_omega) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  have C5 := jal0_spec_pcFree (-24 : BitVec 21) (base + (192 : Word))
    (P := ((.x7 : Reg) ↦ᵣ (addrPtr + BitVec.ofNat 64 (i + 1))) **
      ((.x28 : Reg) ↦ᵣ ((srcBytes[i]'h_src_lt).zeroExtend 64)) **
      bytesRegion addrPtr srcBytes **
      ((.x6 : Reg) ↦ᵣ (accountsBase + BitVec.ofNat 64 (i + 1))) **
      bytesRegion accountsBase (copyIntoRegion dstBytes srcBytes 0 0 (i + 1)) **
      ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 m) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) (by pcFreeR)
  rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide,
      show base + (192 : Word) + (-24 : Word) = base + (168 : Word) from by bv_omega] at C5
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hstraight
    (cpsTripleWithin_extend_code hjmem C5)

/-- **The copy-loop closure** (indices 42..48, `base + 168 → base + 196`):
    `countdownLoop_spec` over `bbeaCopyInv`, twenty iterations of six steps
    each plus the final guard test. -/
theorem balBuilderEnsureAccount_copyLoop_spec
    (base addrPtr accountsBase : Word) (srcBytes dstBytes : List (BitVec 8))
    (h_src_align : addrPtr.toNat % 8 = 0)
    (h_dst_align : accountsBase.toNat % 8 = 0)
    (h_src_len : srcBytes.length = 20)
    (h_dst_len : 20 ≤ dstBytes.length)
    (h_src_over : addrPtr.toNat + srcBytes.length < 2 ^ 64)
    (h_dst_over : accountsBase.toNat + dstBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (addrPtr + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dstBytes.length →
      isValidByteAccess (accountsBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 141 (base + (168 : Word)) (base + (196 : Word))
      (CodeReq.ofProg base balBuilderEnsureAccount_prog)
      (((.x5 : Reg) ↦ᵣ (20 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bbeaCopyInv addrPtr accountsBase srcBytes dstBytes 0)
      (((.x5 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bbeaCopyInv addrPtr accountsBase srcBytes dstBytes 20) := by
  have hguard : ∀ a i,
      CodeReq.singleton (base + (168 : Word)) (.BEQ .x5 .x0 (28 : BitVec 13)) a = some i →
      CodeReq.ofProg base balBuilderEnsureAccount_prog a = some i :=
    CodeReq.ofProg_mem_at base (base + (168 : Word)) balBuilderEnsureAccount_prog 42
      (.BEQ .x5 .x0 (28 : BitVec 13)) (by bv_omega) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  have hloop := countdownLoop_spec
    (cr := CodeReq.ofProg base balBuilderEnsureAccount_prog)
    (hdr := base + (168 : Word)) (exitAddr := base + (196 : Word)) (ctr := .x5)
    (exitOff := (28 : BitVec 13)) (bodyStep := 6) (N := 20)
    (inv := fun n => bbeaCopyInv addrPtr accountsBase srcBytes dstBytes (20 - n))
    (by nofun) (by omega)
    (by rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega)
    (fun n => bbeaCopyInv_pcFree _ _ _ _ _)
    hguard
    (fun n hn => by
      have hidx : 20 - n = (20 - (n + 1)) + 1 := by omega
      rw [show base + (168 : Word) + 4 = base + (172 : Word) from by bv_omega, hidx]
      exact balBuilderEnsureAccount_copyBody_spec base addrPtr accountsBase srcBytes dstBytes
        (20 - (n + 1)) n h_src_align h_dst_align (by omega) (by omega)
        h_src_over h_dst_over h_src_valid h_dst_valid)
  simpa using hloop

/-! ## Segment D — commit the new row and answer with its index -/

/-- `bal_builder_ensure_account` instructions 49..53 (`base + 196 ..
    base + 236`): `addi t0, s2, 1` (the new count), store it back through
    `s1`, `mv s3, s2` and `mv a0, s3` — the interned index, `0` here — then
    `j` past the overflow arm to the epilogue.

    ⭐ The count store is the routine's ONLY write outside the row itself, and
    it is what makes the interning stable: the next call sees a nonzero count
    and takes the comparison path. -/
theorem balBuilderEnsureAccount_segD_body_spec
    (base countPtr y5 y10 y19 : Word) :
    cpsTripleWithin 5 (base + (196 : Word)) (base + (236 : Word))
      (CodeReq.ofProg base balBuilderEnsureAccount_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ y5) ** (.x9 ↦ᵣ countPtr) **
       (.x10 ↦ᵣ y10) ** (.x18 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ y19) **
       (countPtr ↦ₘ (0 : Word)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x9 ↦ᵣ countPtr) **
       (.x10 ↦ᵣ (0 : Word)) ** (.x18 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ (0 : Word)) **
       (countPtr ↦ₘ (1 : Word))) := by
  unfold balBuilderEnsureAccount_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 49: `addi t0, s2, 1`
  have D0 := addi_spec_gen_within .x5 .x18 y5 (0 : Word) (1 : BitVec 12)
    (base + (196 : Word)) (by nofun)
  rw [show (0 : Word) + signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at D0
  -- index 50: `sd t0, 0(s1)` — the count cell goes 0 → 1
  have D1 := sd_spec_gen_within .x9 .x5 countPtr (1 : Word) (0 : Word) (0 : BitVec 12)
    (base + (200 : Word))
  rw [show countPtr + signExtend12 (0 : BitVec 12) = countPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at D1
  -- index 51: `mv s3, s2` — the interned index
  have D2 := mv_spec_gen_within .x19 .x18 (0 : Word) y19 (base + (204 : Word)) (by nofun)
  -- index 52: `mv a0, s3` — the result register
  have D3 := mv_spec_gen_within .x10 .x19 (0 : Word) y10 (base + (208 : Word)) (by nofun)
  -- index 53: `j` past the overflow arm
  have D4 := jal0_spec_pcFree (24 : BitVec 21) (base + (212 : Word))
    (P := (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x9 ↦ᵣ countPtr) **
      (.x10 ↦ᵣ (0 : Word)) ** (.x18 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ (0 : Word)) **
      (countPtr ↦ₘ (1 : Word))) (by pcFree)
  rw [show signExtend21 (24 : BitVec 21) = (24 : Word) from by decide,
      show base + (212 : Word) + (24 : Word) = base + (236 : Word) from by bv_omega] at D4
  runBlock D0 D1 D2 D3 D4

/-! ## Segment E — the epilogue -/

/-- `bal_builder_ensure_account` instructions 59..66 (`base + 236 .. ret`):
    reload the six `s`-registers from the frame, pop the 48-byte frame, and
    `ret`.

    ⚠️ Read from the Program, not a docstring (#13182 is why the distinction
    matters): the epilogue reloads EXACTLY the six registers indices 1..6
    spilled and nothing else.  There is **no `ra` slot** — this routine is a
    leaf, so `ra` survives simply because nothing writes it. -/
theorem balBuilderEnsureAccount_segE_body_spec
    (base sp ra v8 v9 v18 v19 v20 v21 z8 z9 z18 z19 z20 z21 : Word) :
    cpsTripleWithin 8 (base + (236 : Word)) (ra &&& ~~~(1 : Word))
      (CodeReq.ofProg base balBuilderEnsureAccount_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp - (48 : Word))) **
       (.x8 ↦ᵣ z8) ** (.x9 ↦ᵣ z9) ** (.x18 ↦ᵣ z18) ** (.x19 ↦ᵣ z19) **
       (.x20 ↦ᵣ z20) ** (.x21 ↦ᵣ z21) **
       ((sp - (48 : Word)) ↦ₘ v8) ** ((sp - (40 : Word)) ↦ₘ v9) **
       ((sp - (32 : Word)) ↦ₘ v18) ** ((sp - (24 : Word)) ↦ₘ v19) **
       ((sp - (16 : Word)) ↦ₘ v20) ** ((sp - (8 : Word)) ↦ₘ v21))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
       (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
       ((sp - (48 : Word)) ↦ₘ v8) ** ((sp - (40 : Word)) ↦ₘ v9) **
       ((sp - (32 : Word)) ↦ₘ v18) ** ((sp - (24 : Word)) ↦ₘ v19) **
       ((sp - (16 : Word)) ↦ₘ v20) ** ((sp - (8 : Word)) ↦ₘ v21)) := by
  unfold balBuilderEnsureAccount_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  have E0 := ld_spec_gen_within .x8 .x2 (sp - (48 : Word)) z8 v8 (0 : BitVec 12)
    (base + (236 : Word)) (by nofun)
  rw [show (sp - (48 : Word)) + signExtend12 (0 : BitVec 12) = sp - (48 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at E0
  have E1 := ld_spec_gen_within .x9 .x2 (sp - (48 : Word)) z9 v9 (8 : BitVec 12)
    (base + (240 : Word)) (by nofun)
  rw [show (sp - (48 : Word)) + signExtend12 (8 : BitVec 12) = sp - (40 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at E1
  have E2 := ld_spec_gen_within .x18 .x2 (sp - (48 : Word)) z18 v18 (16 : BitVec 12)
    (base + (244 : Word)) (by nofun)
  rw [show (sp - (48 : Word)) + signExtend12 (16 : BitVec 12) = sp - (32 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at E2
  have E3 := ld_spec_gen_within .x19 .x2 (sp - (48 : Word)) z19 v19 (24 : BitVec 12)
    (base + (248 : Word)) (by nofun)
  rw [show (sp - (48 : Word)) + signExtend12 (24 : BitVec 12) = sp - (24 : Word) from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]; bv_omega] at E3
  have E4 := ld_spec_gen_within .x20 .x2 (sp - (48 : Word)) z20 v20 (32 : BitVec 12)
    (base + (252 : Word)) (by nofun)
  rw [show (sp - (48 : Word)) + signExtend12 (32 : BitVec 12) = sp - (16 : Word) from by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]; bv_omega] at E4
  have E5 := ld_spec_gen_within .x21 .x2 (sp - (48 : Word)) z21 v21 (40 : BitVec 12)
    (base + (256 : Word)) (by nofun)
  rw [show (sp - (48 : Word)) + signExtend12 (40 : BitVec 12) = sp - (8 : Word) from by
    rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]; bv_omega] at E5
  have E6 := addi_spec_gen_same_within .x2 (sp - (48 : Word)) (48 : BitVec 12)
    (base + (260 : Word)) (by nofun)
  rw [show (sp - (48 : Word)) + signExtend12 (48 : BitVec 12) = sp from by
    rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide]; bv_omega] at E6
  have E7 := EvmAsm.Evm64.ret_spec_within' (base + (264 : Word)) ra
  runBlock E0 E1 E2 E3 E4 E5 E6 E7

/-! ## The deployed (anchored) whole-routine contract -/

/-- The account table's base, on its linked `.bss` address. -/
abbrev BBACC : Word := (GuestAddrs.bal_builder_accounts : Word)

/-- The row-count cell, on its linked `.bss` address. -/
abbrev BBCNT : Word := (GuestAddrs.bal_builder_account_count : Word)

theorem bbeaProg_sub_bbeaCR :
    ∀ a i, CodeReq.ofProg BBEA balBuilderEnsureAccount_prog a = some i → bbeaCR a = some i :=
  fun _ _ h => h

/-- ⭐ **`bal_builder_ensure_account`, whole routine, intern-into-an-empty-table
    arm.**

    Entry `GuestAddrs.bal_builder_ensure_account`, exit `ra &&& ~~~1` — the
    caller's return address — over `bbeaCR`, which pairs the linked
    `GuestAddrs` entry with `balBuilderEnsureAccount_prog` exactly as
    `GuestImageEntries` does.

    ⭐ **A single `CodeReq.ofProg`, because the routine is a LEAF.** #13176,
    #13179 and #13186 each needed a two-program union; this one does not, and
    that is the property that makes it usable as a callee contract by the
    three `bal_builder_append_*` routines whose unconditional
    `jal ra, bal_builder_ensure_account` currently blocks them.

    One named gate selects the arm:

    * `bal_builder_account_count ↦ₘ 0` — the table is empty, so the scan
      guard `bgeu s3, s2` at index 14 is taken with ZERO iterations and the
      140000-row capacity branch at index 34 falls through.

    Under it the routine **interns the key at row 0**: the caller's twenty
    address bytes are copied into `bal_builder_accounts`
    (`copyIntoRegion rowBytes keyBytes 0 0 20`), the count cell goes `0 → 1`,
    and `a0 = 0` — the stable table index the three appenders then use.  Both
    facts are stated over honest regions rather than framed away.

    ⚠️ **Register discipline read from the Program, not the docstring**
    (#13182).  `s0`-`s5` and `sp` come back at their entry values because
    indices 59..64 reload exactly the six slots indices 1..6 spilled.  `ra` is
    NOT spilled — the frame has no `ra` slot, this being a leaf — and survives
    only because nothing writes it; the post says so by returning `.x1 ↦ᵣ ra`.
    `t0`-`t2` are clobbered and the post states their values (`t0 = 1`, the
    two cursors one past the copied key); `x28` is left as `regOwn`.

    ⚠️ NOT proven: the hit arm, the append-at-a-nonzero-index arm, and the
    capacity/overflow arm at index 54.  The registry row is `.conditional`
    with the empty-table gate named. -/
theorem balBuilderEnsureAccountAppendEmptyFlat_spec
    (sp ra addrPtr v5 v6 v7 v8 v9 v18 v19 v20 v21 v28 : Word)
    (keyBytes rowBytes : List (BitVec 8))
    (h_key_align : addrPtr.toNat % 8 = 0)
    (h_key_len : keyBytes.length = 20)
    (h_row_len : 20 ≤ rowBytes.length)
    (h_key_over : addrPtr.toNat + keyBytes.length < 2 ^ 64)
    (h_row_over : BBACC.toNat + rowBytes.length < 2 ^ 64)
    (h_key_valid : ∀ k, k < keyBytes.length →
      isValidByteAccess (addrPtr + BitVec.ofNat 64 k) = true)
    (h_row_valid : ∀ k, k < rowBytes.length →
      isValidByteAccess (BBACC + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 179 BBEA (ra &&& ~~~(1 : Word)) bbeaCR
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ addrPtr) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
       (.x28 ↦ᵣ v28) **
       memOwn (sp - (48 : Word)) ** memOwn (sp - (40 : Word)) **
       memOwn (sp - (32 : Word)) ** memOwn (sp - (24 : Word)) **
       memOwn (sp - (16 : Word)) ** memOwn (sp - (8 : Word)) **
       (BBCNT ↦ₘ (0 : Word)) **
       bytesRegion addrPtr keyBytes ** bytesRegion BBACC rowBytes)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (BBACC + BitVec.ofNat 64 20)) **
       (.x7 ↦ᵣ (addrPtr + BitVec.ofNat 64 20)) **
       (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ (0 : Word)) **
       (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
       regOwn .x28 **
       ((sp - (48 : Word)) ↦ₘ v8) ** ((sp - (40 : Word)) ↦ₘ v9) **
       ((sp - (32 : Word)) ↦ₘ v18) ** ((sp - (24 : Word)) ↦ₘ v19) **
       ((sp - (16 : Word)) ↦ₘ v20) ** ((sp - (8 : Word)) ↦ₘ v21) **
       (BBCNT ↦ₘ (1 : Word)) **
       bytesRegion addrPtr keyBytes **
       bytesRegion BBACC (copyIntoRegion rowBytes keyBytes 0 0 20)) := by
  -- segment A: prologue, the two `la`s, the empty-table guard
  have hA := cpsTripleWithin_extend_code bbeaProg_sub_bbeaCR
    (balBuilderEnsureAccount_segA_body_spec BBEA sp addrPtr BBCNT BBACC
      v8 v9 v18 v19 v20 v21 (by decide +kernel) (by decide +kernel) (by decide +kernel))
  have hA := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
     bytesRegion addrPtr keyBytes ** bytesRegion BBACC rowBytes)
    (by pcFree) hA
  -- segment B: the capacity check and the row-0 cursor setup
  have hB := cpsTripleWithin_extend_code bbeaProg_sub_bbeaCR
    (balBuilderEnsureAccount_segB_body_spec BBEA addrPtr BBACC v5 v6 v7 v21
      (by decide +kernel))
  -- segment C: the twenty-iteration key copy
  have hC0 := balBuilderEnsureAccount_copyLoop_spec BBEA addrPtr BBACC keyBytes rowBytes
    h_key_align (by decide +kernel) h_key_len h_row_len h_key_over h_row_over
    h_key_valid h_row_valid
  simp only [bbeaCopyInv,
    show BBACC + BitVec.ofNat 64 0 = BBACC from by bv_omega,
    show addrPtr + BitVec.ofNat 64 0 = addrPtr from by bv_omega,
    show copyIntoRegion rowBytes keyBytes 0 0 0 = rowBytes from rfl] at hC0
  have hC := cpsTripleWithin_extend_code bbeaProg_sub_bbeaCR
    (cpsTripleWithin_weaken
      (P' := ((.x5 : Reg) ↦ᵣ (20 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x6 : Reg) ↦ᵣ BBACC) ** ((.x7 : Reg) ↦ᵣ addrPtr) ** ((.x28 : Reg) ↦ᵣ v28) **
        bytesRegion addrPtr keyBytes ** bytesRegion BBACC rowBytes)
      (fun _ hp => by
        have hp2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x28))))) _ hp
        xperm_chunked hp2)
      (fun _ hq => hq) hC0)
  -- segment D: commit the row count and the interned index
  have hD := cpsTripleWithin_extend_code bbeaProg_sub_bbeaCR
    (balBuilderEnsureAccount_segD_body_spec BBEA BBCNT (0 : Word) addrPtr (0 : Word))
  -- segment E: the epilogue
  have hE := cpsTripleWithin_extend_code bbeaProg_sub_bbeaCR
    (balBuilderEnsureAccount_segE_body_spec BBEA sp ra v8 v9 v18 v19 v20 v21
      addrPtr BBCNT (0 : Word) (0 : Word) BBACC BBACC)
  seqFrame hA hB
  seqFrame hAhB hC
  seqFrame hAhBhC hD
  seqFrame hAhBhChD hE
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hAhBhChDhE

/-! ## Axiom audit — classical-only. -/

#print axioms balBuilderEnsureAccountAppendEmptyFlat_spec

end EvmAsm.Codegen.Proofs
