/-
  EvmAsm.Codegen.Proofs.AccountReadRecordSpec

  **The `account_read_record` machine triple — suppressed arm (#12222).**

  `account_read_record` (`EvmAsm/Codegen/Programs/AccountReadLog.lean`,
  `accountReadRecord_prog`, 73 instructions at
  `GuestAddrs.account_read_record`) is the producer for the guest's
  `account_reads` container — the read half of the BAL surface and the
  sibling of `account_write_record`.  In-degree 10: ten emitted contracts
  reach it through an uncontracted `jal`.

  ## What this module proves, and what it deliberately does not

  The routine's FIRST decision is the suppression gate: instructions 8..11
  materialise `runtime_tx_account_read_suppress`, load it, and `bne` to the
  epilogue when it is non-zero.  The triple below covers exactly that arm —
  the **21-step suppressed path** `0..11 ;; 64..72`:

      prologue (sp -= 64, spill t0/t1/t2/t3/t4/t5/t6)
        ;; la t0, runtime_tx_account_read_suppress ; ld t1, 0(t0)
        ;; bne t1, zero, .Lret          -- TAKEN (this arm's gate)
        ;; epilogue (reload the seven temps, sp += 64, ret)

  and its postcondition is the **no-op** claim that the calling convention
  in `AccountReadLog.lean` advertises: `sp` is restored, all seven caller-
  invisible temporaries `t0`-`t6` hold their entry values again, `a0` (the
  20-byte address pointer) is untouched, and the suppression cell itself is
  unchanged.  Because `cpsTripleWithin` universally quantifies over a
  `pcFree` frame `R`, everything NOT named in the pre/post is preserved
  verbatim — so this triple also states, for free, that the suppressed arm
  writes **nothing** to `tx_account_reads_count`,
  `tx_account_reads_overflow`, or the `TX_ACCOUNT_READS_AREA` arena.  That
  is the spec-side content of the gate: a suppressed read is not recorded,
  so it cannot appear in `account_reads` and therefore cannot reach
  `add_touched_account` (`block_access_lists.py:696`).

  The remaining three arms — overflow (`count >= 16384`), dedup hit, and
  append — run the fixed-stride scan (indices 12..63, an outer entry walk
  with a nested 20-byte byte-compare loop) and need a loop invariant plus
  the `accountReadRowsFrom` vocabulary; they are NOT proven here.  The
  registry row is therefore `.conditional` with the gate named, per
  `EvmAsm/Progress/Routines.lean`'s tier reading.

  ## Mechanics (the two pilot rules of `Proofs/FlatBlockPilotSpec.lean`)

  1. The code requirement is presented as the `singleton`-union chain
     (`unfold` + `CodeReq.ofProg_cons`) before `runBlock`, otherwise
     `runBlock` delta-unfolds the literal-list `def` and silently leaves
     metavariables.
  2. Every address offset is written `(k : Word)`, never bare `k`.

  The `la` round-trip and the `bne` displacement round-trip are named
  hypotheses on the position-independent `*_body_spec` and discharged by
  `decide` on the linked layout in the anchored `*Flat_spec`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only
  (audited by the `#print axioms` at the end of this file).
-/

module

public import EvmAsm.Rv64.SyscallSpecs
public import EvmAsm.Rv64.ControlFlow
public import EvmAsm.Rv64.Tactics.RunBlock
public import EvmAsm.Evm64.CallingConvention
public import EvmAsm.Codegen.Programs.AccountReadLog
meta import EvmAsm.Rv64.SyscallSpecs
meta import EvmAsm.Rv64.ControlFlow
meta import EvmAsm.Rv64.Tactics.RunBlock
meta import EvmAsm.Evm64.CallingConvention
meta import EvmAsm.Codegen.Programs.AccountReadLog

@[expose] public section

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen

/-! ## The suppressed arm at a free `base` -/

/-- `account_read_record`'s suppressed arm at a free `base`, with the `la`
    round-trip and the `bne` displacement named.

    `hsuppress` is the arm's gate: the transaction-level
    `runtime_tx_account_read_suppress` cell is non-zero (system-transaction
    reads).  Under it the routine is a no-op on every caller-visible
    register and records nothing. -/
theorem accountReadRecord_suppressed_body_spec
    (base sp ra a0 suppressPtr suppressVal v5 v6 v7 v28 v29 v30 v31 : Word)
    (hla : base + (32 : Word) +
        (((laHi GuestAddrs.runtime_tx_account_read_suppress
            (GuestAddrs.account_read_record + 32)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.runtime_tx_account_read_suppress
          (GuestAddrs.account_read_record + 32)) = suppressPtr)
    (hbr : signExtend13 (brOff (GuestAddrs.account_read_record + 256)
        (GuestAddrs.account_read_record + 44)) = (212 : Word))
    (hsuppress : suppressVal ≠ (0 : Word)) :
    cpsTripleWithin 21 base (ra &&& ~~~1)
      (CodeReq.ofProg base accountReadRecord_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       memOwn (sp - (64 : Word)) ** memOwn (sp - (56 : Word)) **
       memOwn (sp - (48 : Word)) ** memOwn (sp - (40 : Word)) **
       memOwn (sp - (32 : Word)) ** memOwn (sp - (24 : Word)) **
       memOwn (sp - (16 : Word)) **
       (suppressPtr ↦ₘ suppressVal))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       ((sp - (64 : Word)) ↦ₘ v5) ** ((sp - (56 : Word)) ↦ₘ v6) **
       ((sp - (48 : Word)) ↦ₘ v7) ** ((sp - (40 : Word)) ↦ₘ v28) **
       ((sp - (32 : Word)) ↦ₘ v29) ** ((sp - (24 : Word)) ↦ₘ v30) **
       ((sp - (16 : Word)) ↦ₘ v31) **
       (suppressPtr ↦ₘ suppressVal)) := by
  -- Pilot rule 1: present the code requirement as the `singleton`-union chain.
  unfold accountReadRecord_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 0: `addi sp, sp, -64`
  have P0 := addi_spec_gen_same_within .x2 sp (-64 : BitVec 12) base (by nofun)
  rw [show signExtend12 (-64 : BitVec 12) = (-64 : Word) from by decide,
      show sp + (-64 : Word) = sp - (64 : Word) from by bv_omega] at P0
  -- indices 1..7: spill `t0`-`t6`
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
  -- indices 8, 9: `la t0, runtime_tx_account_read_suppress`
  have P8 := auipc_spec_gen_within .x5 v5
    (laHi GuestAddrs.runtime_tx_account_read_suppress
      (GuestAddrs.account_read_record + 32))
    (base + (32 : Word)) (by nofun)
  have P9 := addi_spec_gen_same_within .x5
    ((base + (32 : Word)) +
      (((laHi GuestAddrs.runtime_tx_account_read_suppress
          (GuestAddrs.account_read_record + 32)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.runtime_tx_account_read_suppress
      (GuestAddrs.account_read_record + 32))
    (base + (36 : Word)) (by nofun)
  rw [hla] at P9
  -- index 10: `ld t1, 0(t0)` — the suppression flag
  have P10 := ld_spec_gen_within .x6 .x5 suppressPtr v6 suppressVal (0 : BitVec 12)
    (base + (40 : Word)) (by nofun)
  rw [show suppressPtr + signExtend12 (0 : BitVec 12) = suppressPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at P10
  -- index 11: `bne t1, zero, .Lret` — TAKEN, because `suppressVal ≠ 0`
  have PB := bne_spec_gen_within .x6 .x0
    (brOff (GuestAddrs.account_read_record + 256) (GuestAddrs.account_read_record + 44))
    suppressVal (0 : Word) (base + (44 : Word))
  rw [hbr, show base + (44 : Word) + (212 : Word) = base + (256 : Word) from by bv_omega]
    at PB
  have P11 : cpsTripleWithin 1 (base + (44 : Word)) (base + (256 : Word))
      (CodeReq.singleton (base + (44 : Word)) (.BNE .x6 .x0
        (brOff (GuestAddrs.account_read_record + 256)
          (GuestAddrs.account_read_record + 44))))
      ((.x6 ↦ᵣ suppressVal) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ suppressVal) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranchWithin_takenStripPure2 PB (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact hsuppress h_pure.2)
  -- indices 64..70: reload `t0`-`t6`
  have E0 := ld_spec_gen_within .x5 .x2 (sp - (64 : Word)) suppressPtr v5 (0 : BitVec 12)
    (base + (256 : Word)) (by nofun)
  rw [show (sp - (64 : Word)) + signExtend12 (0 : BitVec 12) = sp - (64 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at E0
  have E1 := ld_spec_gen_within .x6 .x2 (sp - (64 : Word)) suppressVal v6 (8 : BitVec 12)
    (base + (260 : Word)) (by nofun)
  rw [show (sp - (64 : Word)) + signExtend12 (8 : BitVec 12) = sp - (56 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at E1
  have E2 := ld_spec_gen_within .x7 .x2 (sp - (64 : Word)) v7 v7 (16 : BitVec 12)
    (base + (264 : Word)) (by nofun)
  rw [show (sp - (64 : Word)) + signExtend12 (16 : BitVec 12) = sp - (48 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at E2
  have E3 := ld_spec_gen_within .x28 .x2 (sp - (64 : Word)) v28 v28 (24 : BitVec 12)
    (base + (268 : Word)) (by nofun)
  rw [show (sp - (64 : Word)) + signExtend12 (24 : BitVec 12) = sp - (40 : Word) from by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]; bv_omega] at E3
  have E4 := ld_spec_gen_within .x29 .x2 (sp - (64 : Word)) v29 v29 (32 : BitVec 12)
    (base + (272 : Word)) (by nofun)
  rw [show (sp - (64 : Word)) + signExtend12 (32 : BitVec 12) = sp - (32 : Word) from by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]; bv_omega] at E4
  have E5 := ld_spec_gen_within .x30 .x2 (sp - (64 : Word)) v30 v30 (40 : BitVec 12)
    (base + (276 : Word)) (by nofun)
  rw [show (sp - (64 : Word)) + signExtend12 (40 : BitVec 12) = sp - (24 : Word) from by
    rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]; bv_omega] at E5
  have E6 := ld_spec_gen_within .x31 .x2 (sp - (64 : Word)) v31 v31 (48 : BitVec 12)
    (base + (280 : Word)) (by nofun)
  rw [show (sp - (64 : Word)) + signExtend12 (48 : BitVec 12) = sp - (16 : Word) from by
    rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide]; bv_omega] at E6
  -- index 71: `addi sp, sp, 64`
  have E7 := addi_spec_gen_same_within .x2 (sp - (64 : Word)) (64 : BitVec 12)
    (base + (284 : Word)) (by nofun)
  rw [show (sp - (64 : Word)) + signExtend12 (64 : BitVec 12) = sp from by
    rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide]; bv_omega] at E7
  -- index 72: `ret`
  have E8 := EvmAsm.Evm64.ret_spec_within' (base + (288 : Word)) ra
  runBlock P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 E0 E1 E2 E3 E4 E5 E6 E7 E8

/-! ## The deployed (anchored) contract

  Entry AND `CodeReq` are both at `GuestAddrs.account_read_record`, which is
  the `GuestImageEntries.lean` pairing itself
  (`(GuestAddrs.account_read_record, accountReadRecord_prog)`), so this is a
  `whole-routine` claim in the `scripts/proof-frontier.py --shape` sense —
  not a structured-Spec caller union. -/

/-- `account_read_record`'s suppressed arm on the linked layout: the `la`
    resolves to `GuestAddrs.runtime_tx_account_read_suppress` and the `bne`
    displacement to `+212` (= `(ARR+256) - (ARR+44)`), both by `decide`. -/
theorem accountReadRecordSuppressedFlat_spec
    (sp ra a0 suppressVal v5 v6 v7 v28 v29 v30 v31 : Word)
    (hsuppress : suppressVal ≠ (0 : Word)) :
    cpsTripleWithin 21 (GuestAddrs.account_read_record : Word) (ra &&& ~~~1)
      (CodeReq.ofProg (GuestAddrs.account_read_record : Word) accountReadRecord_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       memOwn (sp - (64 : Word)) ** memOwn (sp - (56 : Word)) **
       memOwn (sp - (48 : Word)) ** memOwn (sp - (40 : Word)) **
       memOwn (sp - (32 : Word)) ** memOwn (sp - (24 : Word)) **
       memOwn (sp - (16 : Word)) **
       ((GuestAddrs.runtime_tx_account_read_suppress : Word) ↦ₘ suppressVal))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
       ((sp - (64 : Word)) ↦ₘ v5) ** ((sp - (56 : Word)) ↦ₘ v6) **
       ((sp - (48 : Word)) ↦ₘ v7) ** ((sp - (40 : Word)) ↦ₘ v28) **
       ((sp - (32 : Word)) ↦ₘ v29) ** ((sp - (24 : Word)) ↦ₘ v30) **
       ((sp - (16 : Word)) ↦ₘ v31) **
       ((GuestAddrs.runtime_tx_account_read_suppress : Word) ↦ₘ suppressVal)) :=
  accountReadRecord_suppressed_body_spec (GuestAddrs.account_read_record : Word)
    sp ra a0 (GuestAddrs.runtime_tx_account_read_suppress : Word) suppressVal
    v5 v6 v7 v28 v29 v30 v31 (by decide) (by decide) hsuppress

/-! ## Non-vacuity

  Three checks, in the shape `docs/agents` asks for: a fully numeric
  instance (so a `True`-shaped or trivially-satisfiable post could not have
  passed), a positive witness for the gate, and a NEGATIVE control showing
  the gate really excludes inputs the symbol could otherwise be asked
  about. -/

/-- **Numeric instance.**  `sp = 0x30000000`, suppression flag `1`, the seven
    temps `1..7`: the post is fully concrete — the seven spill slots at
    `0x2fffffc0 .. 0x2ffffff0` hold `1..7` in spill order, `sp` is back to
    `0x30000000`, and the flag cell still reads `1`. -/
example (ra a0 : Word) :
    cpsTripleWithin 21 (GuestAddrs.account_read_record : Word) (ra &&& ~~~1)
      (CodeReq.ofProg (GuestAddrs.account_read_record : Word) accountReadRecord_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (0x30000000 : Word)) **
       (.x10 ↦ᵣ a0) **
       (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (2 : Word)) ** (.x7 ↦ᵣ (3 : Word)) **
       (.x28 ↦ᵣ (4 : Word)) ** (.x29 ↦ᵣ (5 : Word)) ** (.x30 ↦ᵣ (6 : Word)) **
       (.x31 ↦ᵣ (7 : Word)) **
       memOwn (0x2fffffc0 : Word) ** memOwn (0x2fffffc8 : Word) **
       memOwn (0x2fffffd0 : Word) ** memOwn (0x2fffffd8 : Word) **
       memOwn (0x2fffffe0 : Word) ** memOwn (0x2fffffe8 : Word) **
       memOwn (0x2ffffff0 : Word) **
       ((GuestAddrs.runtime_tx_account_read_suppress : Word) ↦ₘ (1 : Word)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (0x30000000 : Word)) **
       (.x10 ↦ᵣ a0) **
       (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (2 : Word)) ** (.x7 ↦ᵣ (3 : Word)) **
       (.x28 ↦ᵣ (4 : Word)) ** (.x29 ↦ᵣ (5 : Word)) ** (.x30 ↦ᵣ (6 : Word)) **
       (.x31 ↦ᵣ (7 : Word)) **
       ((0x2fffffc0 : Word) ↦ₘ (1 : Word)) ** ((0x2fffffc8 : Word) ↦ₘ (2 : Word)) **
       ((0x2fffffd0 : Word) ↦ₘ (3 : Word)) ** ((0x2fffffd8 : Word) ↦ₘ (4 : Word)) **
       ((0x2fffffe0 : Word) ↦ₘ (5 : Word)) ** ((0x2fffffe8 : Word) ↦ₘ (6 : Word)) **
       ((0x2ffffff0 : Word) ↦ₘ (7 : Word)) **
       ((GuestAddrs.runtime_tx_account_read_suppress : Word) ↦ₘ (1 : Word))) := by
  have h := accountReadRecordSuppressedFlat_spec (0x30000000 : Word) ra a0 1 1 2 3 4 5 6 7
    (by decide)
  rw [show (0x30000000 : Word) - (64 : Word) = (0x2fffffc0 : Word) from by decide,
      show (0x30000000 : Word) - (56 : Word) = (0x2fffffc8 : Word) from by decide,
      show (0x30000000 : Word) - (48 : Word) = (0x2fffffd0 : Word) from by decide,
      show (0x30000000 : Word) - (40 : Word) = (0x2fffffd8 : Word) from by decide,
      show (0x30000000 : Word) - (32 : Word) = (0x2fffffe0 : Word) from by decide,
      show (0x30000000 : Word) - (24 : Word) = (0x2fffffe8 : Word) from by decide,
      show (0x30000000 : Word) - (16 : Word) = (0x2ffffff0 : Word) from by decide] at h
  exact h

/-- **Gate witness and negative control.**  `1 ≠ 0` inhabits the gate, and
    `0 ≠ 0` is provably FALSE — so the suppressed arm genuinely excludes the
    ordinary (recording) inputs rather than covering them silently.  The
    excluded arms are the overflow / dedup-hit / append paths at instruction
    indices 12..63, which is where the `bne` at index 11 falls through. -/
example : ((1 : Word) ≠ (0 : Word)) ∧ ¬ ((0 : Word) ≠ (0 : Word)) ∧
    (GuestAddrs.account_read_record + 48 ≠ GuestAddrs.account_read_record + 256) :=
  ⟨by decide, by decide, by decide⟩

/-- **Satisfiability of the numeric instance's precondition.**  A numeric post
    is worthless if no machine state can enter the triple, and `memOwn`/`↦ₘ`
    both *assert* `isValidDwordAccess`, so this is a real risk rather than a
    formality.  All eight cells the instance names — the seven spill slots and
    the suppression flag — are valid, 8-byte-aligned dword addresses in a live
    zone, and the flag is distinct from every slot, so the separating
    conjunction is inhabitable. -/
example :
    isValidDwordAccess (0x2fffffc0 : Word) = true ∧
    isValidDwordAccess (0x2fffffc8 : Word) = true ∧
    isValidDwordAccess (0x2fffffd0 : Word) = true ∧
    isValidDwordAccess (0x2fffffd8 : Word) = true ∧
    isValidDwordAccess (0x2fffffe0 : Word) = true ∧
    isValidDwordAccess (0x2fffffe8 : Word) = true ∧
    isValidDwordAccess (0x2ffffff0 : Word) = true ∧
    isValidDwordAccess (GuestAddrs.runtime_tx_account_read_suppress : Word) = true ∧
    (GuestAddrs.runtime_tx_account_read_suppress : Word) ≠ (0x2fffffc0 : Word) ∧
    (GuestAddrs.runtime_tx_account_read_suppress : Word) ≠ (0x2ffffff0 : Word) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   by decide, by decide, by decide⟩

/-! ## Axiom audit — classical-only. -/

#print axioms accountReadRecord_suppressed_body_spec
#print axioms accountReadRecordSuppressedFlat_spec

end EvmAsm.Codegen.Proofs
