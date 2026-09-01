/-
  EvmAsm.Codegen.Proofs.FlatBlockPilotSpec

  **The flat-block contract pilot (#12245, under #12244).**

  `scripts/shape-census.py` reports 588 emitted `Function` defs with zero
  conditional branches, and the generator question was whether a
  machine-level contract for such a routine — entry at the `GuestAddrs`
  anchor, exit at `ret`, registers/memory per the symbolic store — is
  derivable by symbolic execution alone (no invariant, no termination
  measure) and therefore worth mechanizing.

  This module answers it with worked contracts for the routines in the
  DEPLOYED image (`EvmAsm/Codegen/Proofs/GuestImageEntries.lean` is the
  authority) that genuinely have that shape and carried no prior spec of
  any kind.  Two contract shapes appear, both loop-free, both
  invariant-free, both stating the FULL register/memory effect:

  * **return-shaped** — exit `ra &&& ~~~1` (`wcidx_record_ptr`,
    `write_sets_discard_tx`, `read_sets_discard_tx`);
  * **tail-transfer-shaped** — the routine's last instruction is a
    `j <callee>`, so the exit pc is the *callee's entry*
    (`secf_square_mod_p`, `secf_square_mod_n`,
    `derive_withdrawal_requests`, `derive_consolidation_requests`,
    `derive_builder_deposit_requests`, `derive_builder_exit_requests`).
    A tail-transfer contract needs no callee spec: it states exactly the
    argument shuffle the wrapper performs and then hands control over,
    which is precisely the fact a caller must compose with the callee's
    own triple.  It is the honest whole-routine claim for a wrapper, and
    it is the fact whose absence let `derive_withdrawal_requests` /
    `derive_consolidation_requests` be mis-annotated as leaves (#11578).

  ## Layering (why each contract comes in two pieces)

  Each routine gets a `*_body_spec` over a free `base`, carrying the
  `la`/`jal` relocation round-trip as a NAMED linking hypothesis, plus an
  anchored `*Flat_spec` that instantiates `base := GuestAddrs.<sym>` and
  discharges that hypothesis by `decide` on the concrete linked layout.
  Only the anchored `*Flat_spec` is a `whole-routine` claim in the
  `scripts/proof-frontier.py --shape` sense: entry AND `CodeReq` both at
  `GuestAddrs.<sym>`.

  The split is a design choice, NOT a technical necessity — proving the
  anchored form directly also works.  It is kept because the position-
  independent `*_body_spec` is the reusable half (a second link layout only
  needs a fresh `by decide`), and because it keeps the relocation arithmetic
  in one named hypothesis instead of inline in a whole-routine statement.

  ## Two mechanical rules the proofs all obey (the non-obvious part)

  1. **Reshape the code requirement before `runBlock`.**  `runBlock`
     delta-unfolds `CodeReq.ofProg` whenever its program argument is an
     opaque literal-list `def` — it only special-cases the
     layout-parameterised `<sym>_prog_of guestLayout` shape — and its own
     code-membership step then cannot see the singleton chain, so it silently
     leaves unassigned metavariables (the goal is reported as an
     unsynthesized placeholder at every preceding `have`, with `runBlock`
     itself tracing success).  `unfold <sym>_prog` followed by
     `rw [CodeReq.ofProg_cons, …, CodeReq.ofProg_nil]` presents the
     requirement as the `singleton`-union chain and the tactic works.
  2. **Write every address offset as `(k : Word)`, never bare `k`.**  In
     `base + 12` the `binop%` elaborator coerces the `Nat` literal
     (`base + ↑12`), which is a different term from the `BitVec` literal the
     instruction specs produce, so `seqFrame` cannot match the chained
     postcondition.

  Anti-vacuity (#11906): each contract is followed by a concrete `example`
  that instantiates it and reads a fully numeric post, so a `True`-shaped or
  trivially satisfiable statement could not have passed.
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Codegen.Programs.WitnessCodeLookup
import EvmAsm.Codegen.Programs.StorageWriteMap
import EvmAsm.Codegen.Programs.ReadSetsPromote
import EvmAsm.Codegen.Programs.Secp256k1Field
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.SystemCallStaging
import EvmAsm.Codegen.Programs.BalSerializer
import EvmAsm.Codegen.Programs.MptDeleteWalkDb

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen

/-- `jal x0, off` with a frame: the library's `jal_x0_spec_gen_within` has
    `empAssertion` pre/post (a pure control transfer), which `runBlock` cannot
    chain because `empAssertion` is not an atom of the surrounding state.  This
    is the same triple with the surviving state `P` carried through — the form
    the tail-transfer contracts below need. -/
private theorem jal_x0_frame_within (P : Assertion) (hP : P.pcFree)
    (offset : BitVec 21) (addr : Word) :
    cpsTripleWithin 1 addr (addr + signExtend21 offset)
      (CodeReq.singleton addr (.JAL .x0 offset)) P P := by
  have h := cpsTripleWithin_frameL P hP (jal_x0_spec_gen_within offset addr)
  exact (sepConj_emp_right' P) ▸ h

/-! ## 1. `wcidx_record_ptr` — `i ↦ &wcidx_records[i]`

  Seven instructions: `i << 5`, `i << 4`, `add` (so `t0 = 48 * i`),
  `la a0, wcidx_records`, `add a0, a0, t0`, `ret`.  `48` is not a shift, so
  the emitter spells the multiply as the shift pair; the contract states
  the exact shift sum the machine computes and
  `wcidxRecordPtr_stride` converts it to `48 * i`.

  In-degree 3 (`scripts/proof-frontier.py`): the code-witness index's
  comparator/swap/sift-down callers all address records through it.  Its
  `widx_*` twin has `widx_record_ptr_spec`
  (`EvmAsm/Codegen/Proofs/MptWitnessIndexSpec.lean`), which is
  `structured-only` — over a re-declared parametric program at a free
  base, not the deployed `wcidxRecordPtr_prog` at its anchor. -/

/-- The record stride the routine computes: `(i <<< 5) + (i <<< 4) = 48 * i`
    for every `i` — no wrap side condition, both sides wrap alike. -/
theorem wcidxRecordPtr_stride (i : Word) :
    (i <<< (5 : Nat)) + (i <<< (4 : Nat)) = 48 * i := by
  bv_omega

/-- `wcidx_record_ptr` at a free `base`, with the `la` round-trip named.
    `a0 := recs + 48 * a0_in`; `t0`/`t1` end holding the partial shifts;
    memory untouched; return through `ra`. -/
theorem wcidxRecordPtr_body_spec (base recs i ra v5 v6 : Word)
    (hla : base + (12 : Word) +
        (((laHi GuestAddrs.wcidx_records (GuestAddrs.wcidx_record_ptr + 12)).zeroExtend 32
          <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.wcidx_records (GuestAddrs.wcidx_record_ptr + 12))
      = recs) :
    cpsTripleWithin 7 base (ra &&& ~~~1)
      (CodeReq.ofProg base wcidxRecordPtr_prog)
      ((.x10 ↦ᵣ i) ** (.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
      ((.x10 ↦ᵣ (recs + ((i <<< (5 : Nat)) + (i <<< (4 : Nat))))) **
       (.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ ((i <<< (5 : Nat)) + (i <<< (4 : Nat)))) **
       (.x6 ↦ᵣ (i <<< (4 : Nat)))) := by
  -- Rule 1 of the module header: present the code requirement as the
  -- `singleton`-union chain before `runBlock`.
  unfold wcidxRecordPtr_prog
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil]
  have S0 := slli_spec_gen_within .x5 .x10 v5 i (5 : BitVec 6) base (by nofun)
  have S1 := slli_spec_gen_within .x6 .x10 v6 i (4 : BitVec 6) (base + (4 : Word)) (by nofun)
  rw [show ((5 : BitVec 6).toNat) = 5 from by decide] at S0
  rw [show ((4 : BitVec 6).toNat) = 4 from by decide] at S1
  have A0 := add_spec_gen_rd_eq_rs1_within .x5 .x6 (i <<< (5 : Nat)) (i <<< (4 : Nat))
    (base + (8 : Word)) (by nofun)
  have AU := auipc_spec_gen_within .x10 i
    (laHi GuestAddrs.wcidx_records (GuestAddrs.wcidx_record_ptr + 12))
    (base + (12 : Word)) (by nofun)
  have AD := addi_spec_gen_same_within .x10
    ((base + (12 : Word)) +
      (((laHi GuestAddrs.wcidx_records (GuestAddrs.wcidx_record_ptr + 12)).zeroExtend 32
        <<< 12).signExtend 64))
    (laLo GuestAddrs.wcidx_records (GuestAddrs.wcidx_record_ptr + 12))
    (base + (16 : Word)) (by nofun)
  rw [hla] at AD
  have A1 := add_spec_gen_rd_eq_rs1_within .x10 .x5 recs
    ((i <<< (5 : Nat)) + (i <<< (4 : Nat))) (base + (20 : Word)) (by nofun)
  have R := EvmAsm.Evm64.ret_spec_within' (base + (24 : Word)) ra
  runBlock S0 S1 A0 AU AD A1 R

/-- `wcidx_record_ptr` deployed contract, anchored at the guest image entry:
    the `la` resolves to `GuestAddrs.wcidx_records` on the linked layout. -/
theorem wcidxRecordPtrFlat_spec (i ra v5 v6 : Word) :
    cpsTripleWithin 7 (GuestAddrs.wcidx_record_ptr : Word) (ra &&& ~~~1)
      (CodeReq.ofProg (GuestAddrs.wcidx_record_ptr : Word) wcidxRecordPtr_prog)
      ((.x10 ↦ᵣ i) ** (.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
      ((.x10 ↦ᵣ ((GuestAddrs.wcidx_records : Word) +
          ((i <<< (5 : Nat)) + (i <<< (4 : Nat))))) **
       (.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ ((i <<< (5 : Nat)) + (i <<< (4 : Nat)))) **
       (.x6 ↦ᵣ (i <<< (4 : Nat)))) :=
  wcidxRecordPtr_body_spec (GuestAddrs.wcidx_record_ptr : Word)
    (GuestAddrs.wcidx_records : Word) i ra v5 v6 (by decide)

/-- **Anti-vacuity witness** (#11906) for `wcidxRecordPtrFlat_spec`: instantiated
    at `a0 = 3` the post is fully concrete — `a0 = 0xa34071a0`
    (`wcidx_records + 144`), `t0 = 144`, `t1 = 48`.  A `True`-shaped or
    trivially-satisfiable post could not produce these numerals. -/
example (ra : Word) :
    cpsTripleWithin 7 (GuestAddrs.wcidx_record_ptr : Word) (ra &&& ~~~1)
      (CodeReq.ofProg (GuestAddrs.wcidx_record_ptr : Word) wcidxRecordPtr_prog)
      ((.x10 ↦ᵣ (3 : Word)) ** (.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0xa34071a0 : Word)) ** (.x1 ↦ᵣ ra) **
       (.x5 ↦ᵣ (144 : Word)) ** (.x6 ↦ᵣ (48 : Word))) := by
  have h := wcidxRecordPtrFlat_spec 3 ra 0 0
  rw [show (GuestAddrs.wcidx_records : Word) +
        (((3 : Word) <<< (5 : Nat)) + ((3 : Word) <<< (4 : Nat))) = (0xa34071a0 : Word)
      from by decide,
    show ((3 : Word) <<< (5 : Nat)) + ((3 : Word) <<< (4 : Nat)) = (144 : Word) from by decide,
    show ((3 : Word) <<< (4 : Nat)) = (48 : Word) from by decide] at h
  exact h

/-! ## 2. `write_sets_discard_tx` — zero the three tx-level write cursors

  Three `la`/`sd zero` pairs and a `ret`.  Discards a failed transaction's
  storage writes (the reads are deliberately kept — see
  `EvmAsm/Codegen/Programs/ReadSetsPromote.lean`). -/

/-- `write_sets_discard_tx` at a free `base`, with the three `la`
    round-trips named.  All three cursors become `0`; `t0` is left holding
    the third cursor's address; nothing else changes. -/
theorem writeSetsDiscardTx_body_spec (base c0 c1 c2 ra v5 m0 m1 m2 : Word)
    (hla0 : base +
        (((laHi GuestAddrs.tx_storage_writes_count
            (GuestAddrs.write_sets_discard_tx + 0)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.tx_storage_writes_count
          (GuestAddrs.write_sets_discard_tx + 0)) = c0)
    (hla1 : base + (12 : Word) +
        (((laHi GuestAddrs.tx_storage_writes_overflow
            (GuestAddrs.write_sets_discard_tx + 12)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.tx_storage_writes_overflow
          (GuestAddrs.write_sets_discard_tx + 12)) = c1)
    (hla2 : base + (24 : Word) +
        (((laHi GuestAddrs.storage_writes_undo_count
            (GuestAddrs.write_sets_discard_tx + 24)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.storage_writes_undo_count
          (GuestAddrs.write_sets_discard_tx + 24)) = c2) :
    cpsTripleWithin 10 base (ra &&& ~~~1)
      (CodeReq.ofProg base writeSetsDiscardTx_prog)
      ((.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ v5) ** (c0 ↦ₘ m0) ** (c1 ↦ₘ m1) ** (c2 ↦ₘ m2))
      ((.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ c2) **
       (c0 ↦ₘ (0 : Word)) ** (c1 ↦ₘ (0 : Word)) ** (c2 ↦ₘ (0 : Word))) := by
  -- Rule 1 of the module header: present the code requirement as the
  -- `singleton`-union chain before `runBlock`.
  unfold writeSetsDiscardTx_prog
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil]
  have AU0 := auipc_spec_gen_within .x5 v5
    (laHi GuestAddrs.tx_storage_writes_count (GuestAddrs.write_sets_discard_tx + 0))
    base (by nofun)
  have AD0 := addi_spec_gen_same_within .x5
    ((base) +
      (((laHi GuestAddrs.tx_storage_writes_count
          (GuestAddrs.write_sets_discard_tx + 0)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.tx_storage_writes_count (GuestAddrs.write_sets_discard_tx + 0))
    (base + (4 : Word)) (by nofun)
  rw [hla0] at AD0
  have SD0 := sd_x0_spec_gen_within .x5 c0 m0 (0 : BitVec 12) (base + (8 : Word))
  rw [show c0 + signExtend12 (0 : BitVec 12) = c0 from by
    rw [signExtend12_0]; exact BitVec.add_zero c0] at SD0
  have AU1 := auipc_spec_gen_within .x5 c0
    (laHi GuestAddrs.tx_storage_writes_overflow (GuestAddrs.write_sets_discard_tx + 12))
    (base + (12 : Word)) (by nofun)
  have AD1 := addi_spec_gen_same_within .x5
    ((base + (12 : Word)) +
      (((laHi GuestAddrs.tx_storage_writes_overflow
          (GuestAddrs.write_sets_discard_tx + 12)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.tx_storage_writes_overflow (GuestAddrs.write_sets_discard_tx + 12))
    (base + (16 : Word)) (by nofun)
  rw [hla1] at AD1
  have SD1 := sd_x0_spec_gen_within .x5 c1 m1 (0 : BitVec 12) (base + (20 : Word))
  rw [show c1 + signExtend12 (0 : BitVec 12) = c1 from by
    rw [signExtend12_0]; exact BitVec.add_zero c1] at SD1
  have AU2 := auipc_spec_gen_within .x5 c1
    (laHi GuestAddrs.storage_writes_undo_count (GuestAddrs.write_sets_discard_tx + 24))
    (base + (24 : Word)) (by nofun)
  have AD2 := addi_spec_gen_same_within .x5
    ((base + (24 : Word)) +
      (((laHi GuestAddrs.storage_writes_undo_count
          (GuestAddrs.write_sets_discard_tx + 24)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.storage_writes_undo_count (GuestAddrs.write_sets_discard_tx + 24))
    (base + (28 : Word)) (by nofun)
  rw [hla2] at AD2
  have SD2 := sd_x0_spec_gen_within .x5 c2 m2 (0 : BitVec 12) (base + (32 : Word))
  rw [show c2 + signExtend12 (0 : BitVec 12) = c2 from by
    rw [signExtend12_0]; exact BitVec.add_zero c2] at SD2
  have R := EvmAsm.Evm64.ret_spec_within' (base + (36 : Word)) ra
  runBlock AU0 AD0 SD0 AU1 AD1 SD1 AU2 AD2 SD2 R

/-- `write_sets_discard_tx` deployed contract, anchored at the guest image
    entry, with the three cursor addresses resolved to their data symbols. -/
theorem writeSetsDiscardTxFlat_spec (ra v5 m0 m1 m2 : Word) :
    cpsTripleWithin 10 (GuestAddrs.write_sets_discard_tx : Word) (ra &&& ~~~1)
      (CodeReq.ofProg (GuestAddrs.write_sets_discard_tx : Word) writeSetsDiscardTx_prog)
      ((.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ v5) **
       ((GuestAddrs.tx_storage_writes_count : Word) ↦ₘ m0) **
       ((GuestAddrs.tx_storage_writes_overflow : Word) ↦ₘ m1) **
       ((GuestAddrs.storage_writes_undo_count : Word) ↦ₘ m2))
      ((.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ (GuestAddrs.storage_writes_undo_count : Word)) **
       ((GuestAddrs.tx_storage_writes_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.tx_storage_writes_overflow : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.storage_writes_undo_count : Word) ↦ₘ (0 : Word))) :=
  writeSetsDiscardTx_body_spec (GuestAddrs.write_sets_discard_tx : Word)
    (GuestAddrs.tx_storage_writes_count : Word)
    (GuestAddrs.tx_storage_writes_overflow : Word)
    (GuestAddrs.storage_writes_undo_count : Word)
    ra v5 m0 m1 m2 (by decide) (by decide) (by decide)

/-- **Anti-vacuity witness** for `writeSetsDiscardTxFlat_spec`: three cells
    holding `7` end holding `0`, at three pairwise DISTINCT guest addresses,
    and `t0` ends at a specific one of them.  So the post is three independent
    value changes, not one aliased or vacuous claim. -/
example (ra : Word) :
    cpsTripleWithin 10 (GuestAddrs.write_sets_discard_tx : Word) (ra &&& ~~~1)
      (CodeReq.ofProg (GuestAddrs.write_sets_discard_tx : Word) writeSetsDiscardTx_prog)
      ((.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ (0 : Word)) **
       ((GuestAddrs.tx_storage_writes_count : Word) ↦ₘ (7 : Word)) **
       ((GuestAddrs.tx_storage_writes_overflow : Word) ↦ₘ (7 : Word)) **
       ((GuestAddrs.storage_writes_undo_count : Word) ↦ₘ (7 : Word)))
      ((.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ (GuestAddrs.storage_writes_undo_count : Word)) **
       ((GuestAddrs.tx_storage_writes_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.tx_storage_writes_overflow : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.storage_writes_undo_count : Word) ↦ₘ (0 : Word))) := by
  exact writeSetsDiscardTxFlat_spec ra 0 7 7 7

/-! ## 3. `read_sets_discard_tx` — zero the three tx-level read cursors

  Byte-for-byte the same shape as §2 over the read cursors.  Kept as a
  separate contract (not a shared lemma) deliberately: the pair is the
  pilot's measurement of how much a second instance of an already-worked
  shape costs. -/

/-- `read_sets_discard_tx` at a free `base`, with the three `la`
    round-trips named. -/
theorem readSetsDiscardTx_body_spec (base c0 c1 c2 ra v5 m0 m1 m2 : Word)
    (hla0 : base +
        (((laHi GuestAddrs.tx_storage_reads_count
            (GuestAddrs.read_sets_discard_tx + 0)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.tx_storage_reads_count
          (GuestAddrs.read_sets_discard_tx + 0)) = c0)
    (hla1 : base + (12 : Word) +
        (((laHi GuestAddrs.tx_account_reads_count
            (GuestAddrs.read_sets_discard_tx + 12)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.tx_account_reads_count
          (GuestAddrs.read_sets_discard_tx + 12)) = c1)
    (hla2 : base + (24 : Word) +
        (((laHi GuestAddrs.tx_code_reads_count
            (GuestAddrs.read_sets_discard_tx + 24)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.tx_code_reads_count
          (GuestAddrs.read_sets_discard_tx + 24)) = c2) :
    cpsTripleWithin 10 base (ra &&& ~~~1)
      (CodeReq.ofProg base readSetsDiscardTx_prog)
      ((.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ v5) ** (c0 ↦ₘ m0) ** (c1 ↦ₘ m1) ** (c2 ↦ₘ m2))
      ((.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ c2) **
       (c0 ↦ₘ (0 : Word)) ** (c1 ↦ₘ (0 : Word)) ** (c2 ↦ₘ (0 : Word))) := by
  -- Rule 1 of the module header: present the code requirement as the
  -- `singleton`-union chain before `runBlock`.
  unfold readSetsDiscardTx_prog
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil]
  have AU0 := auipc_spec_gen_within .x5 v5
    (laHi GuestAddrs.tx_storage_reads_count (GuestAddrs.read_sets_discard_tx + 0))
    base (by nofun)
  have AD0 := addi_spec_gen_same_within .x5
    ((base) +
      (((laHi GuestAddrs.tx_storage_reads_count
          (GuestAddrs.read_sets_discard_tx + 0)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.tx_storage_reads_count (GuestAddrs.read_sets_discard_tx + 0))
    (base + (4 : Word)) (by nofun)
  rw [hla0] at AD0
  have SD0 := sd_x0_spec_gen_within .x5 c0 m0 (0 : BitVec 12) (base + (8 : Word))
  rw [show c0 + signExtend12 (0 : BitVec 12) = c0 from by
    rw [signExtend12_0]; exact BitVec.add_zero c0] at SD0
  have AU1 := auipc_spec_gen_within .x5 c0
    (laHi GuestAddrs.tx_account_reads_count (GuestAddrs.read_sets_discard_tx + 12))
    (base + (12 : Word)) (by nofun)
  have AD1 := addi_spec_gen_same_within .x5
    ((base + (12 : Word)) +
      (((laHi GuestAddrs.tx_account_reads_count
          (GuestAddrs.read_sets_discard_tx + 12)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.tx_account_reads_count (GuestAddrs.read_sets_discard_tx + 12))
    (base + (16 : Word)) (by nofun)
  rw [hla1] at AD1
  have SD1 := sd_x0_spec_gen_within .x5 c1 m1 (0 : BitVec 12) (base + (20 : Word))
  rw [show c1 + signExtend12 (0 : BitVec 12) = c1 from by
    rw [signExtend12_0]; exact BitVec.add_zero c1] at SD1
  have AU2 := auipc_spec_gen_within .x5 c1
    (laHi GuestAddrs.tx_code_reads_count (GuestAddrs.read_sets_discard_tx + 24))
    (base + (24 : Word)) (by nofun)
  have AD2 := addi_spec_gen_same_within .x5
    ((base + (24 : Word)) +
      (((laHi GuestAddrs.tx_code_reads_count
          (GuestAddrs.read_sets_discard_tx + 24)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.tx_code_reads_count (GuestAddrs.read_sets_discard_tx + 24))
    (base + (28 : Word)) (by nofun)
  rw [hla2] at AD2
  have SD2 := sd_x0_spec_gen_within .x5 c2 m2 (0 : BitVec 12) (base + (32 : Word))
  rw [show c2 + signExtend12 (0 : BitVec 12) = c2 from by
    rw [signExtend12_0]; exact BitVec.add_zero c2] at SD2
  have R := EvmAsm.Evm64.ret_spec_within' (base + (36 : Word)) ra
  runBlock AU0 AD0 SD0 AU1 AD1 SD1 AU2 AD2 SD2 R

/-- `read_sets_discard_tx` deployed contract, anchored at the guest image
    entry, with the three cursor addresses resolved to their data symbols. -/
theorem readSetsDiscardTxFlat_spec (ra v5 m0 m1 m2 : Word) :
    cpsTripleWithin 10 (GuestAddrs.read_sets_discard_tx : Word) (ra &&& ~~~1)
      (CodeReq.ofProg (GuestAddrs.read_sets_discard_tx : Word) readSetsDiscardTx_prog)
      ((.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ v5) **
       ((GuestAddrs.tx_storage_reads_count : Word) ↦ₘ m0) **
       ((GuestAddrs.tx_account_reads_count : Word) ↦ₘ m1) **
       ((GuestAddrs.tx_code_reads_count : Word) ↦ₘ m2))
      ((.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ (GuestAddrs.tx_code_reads_count : Word)) **
       ((GuestAddrs.tx_storage_reads_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.tx_account_reads_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.tx_code_reads_count : Word) ↦ₘ (0 : Word))) :=
  readSetsDiscardTx_body_spec (GuestAddrs.read_sets_discard_tx : Word)
    (GuestAddrs.tx_storage_reads_count : Word)
    (GuestAddrs.tx_account_reads_count : Word)
    (GuestAddrs.tx_code_reads_count : Word)
    ra v5 m0 m1 m2 (by decide) (by decide) (by decide)

/-- **Anti-vacuity witness** for `readSetsDiscardTxFlat_spec`: same shape as §2,
    over three DIFFERENT concrete addresses — so neither contract's post is
    satisfiable by the other's. -/
example (ra : Word) :
    cpsTripleWithin 10 (GuestAddrs.read_sets_discard_tx : Word) (ra &&& ~~~1)
      (CodeReq.ofProg (GuestAddrs.read_sets_discard_tx : Word) readSetsDiscardTx_prog)
      ((.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ (0 : Word)) **
       ((GuestAddrs.tx_storage_reads_count : Word) ↦ₘ (7 : Word)) **
       ((GuestAddrs.tx_account_reads_count : Word) ↦ₘ (7 : Word)) **
       ((GuestAddrs.tx_code_reads_count : Word) ↦ₘ (7 : Word)))
      ((.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ (GuestAddrs.tx_code_reads_count : Word)) **
       ((GuestAddrs.tx_storage_reads_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.tx_account_reads_count : Word) ↦ₘ (0 : Word)) **
       ((GuestAddrs.tx_code_reads_count : Word) ↦ₘ (0 : Word))) :=
  readSetsDiscardTxFlat_spec ra 0 7 7 7

/-- The three read cursors are pairwise distinct and disjoint from the three
    write cursors of §2 — the two contracts touch six different cells. -/
example : (GuestAddrs.tx_storage_reads_count ≠ GuestAddrs.tx_account_reads_count) ∧
    (GuestAddrs.tx_account_reads_count ≠ GuestAddrs.tx_code_reads_count) ∧
    (GuestAddrs.tx_storage_reads_count ≠ GuestAddrs.tx_storage_writes_count) :=
  ⟨by decide, by decide, by decide⟩

/-! ## 4. `secf_square_mod_p` — the squaring wrapper (tail transfer)

  Two instructions: `mv a1, a0 ; j secf_mul_mod_p`.  The contract says
  exactly that: `a1` becomes `a0` and control arrives at
  `secf_mul_mod_p`'s entry with `a0` unchanged and memory untouched.  No
  callee spec is needed or used, so this contract is available today; a
  caller composes it with whatever `secf_mul_mod_p` triple exists. -/

/-- `secf_square_mod_p` at a free `base`, with the `jal` displacement
    round-trip named. -/
theorem secfSquareModP_body_spec (base tgt a v11 : Word)
    (hjal : base + (4 : Word) +
        signExtend21 (jalOff GuestAddrs.secf_mul_mod_p (GuestAddrs.secf_square_mod_p + 4))
      = tgt) :
    cpsTripleWithin 2 base tgt
      (CodeReq.ofProg base secfSquareModP_prog)
      ((.x10 ↦ᵣ a) ** (.x11 ↦ᵣ v11))
      ((.x10 ↦ᵣ a) ** (.x11 ↦ᵣ a)) := by
  -- Rule 1 of the module header: present the code requirement as the
  -- `singleton`-union chain before `runBlock`.
  unfold secfSquareModP_prog
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil]
  have M := mv_spec_gen_within .x11 .x10 a v11 base (by nofun)
  have J := jal_x0_frame_within ((.x10 ↦ᵣ a) ** (.x11 ↦ᵣ a))
    Assertion.PCFree.proof
    (jalOff GuestAddrs.secf_mul_mod_p (GuestAddrs.secf_square_mod_p + 4)) (base + (4 : Word))
  rw [hjal] at J
  runBlock M J

/-- `secf_square_mod_p` deployed contract, anchored at the guest image entry:
    the tail `j` lands exactly on `GuestAddrs.secf_mul_mod_p`. -/
theorem secfSquareModPFlat_spec (a v11 : Word) :
    cpsTripleWithin 2 (GuestAddrs.secf_square_mod_p : Word)
      (GuestAddrs.secf_mul_mod_p : Word)
      (CodeReq.ofProg (GuestAddrs.secf_square_mod_p : Word) secfSquareModP_prog)
      ((.x10 ↦ᵣ a) ** (.x11 ↦ᵣ v11))
      ((.x10 ↦ᵣ a) ** (.x11 ↦ᵣ a)) :=
  secfSquareModP_body_spec (GuestAddrs.secf_square_mod_p : Word)
    (GuestAddrs.secf_mul_mod_p : Word) a v11 (by decide)

/-- **Anti-vacuity witness** for `secfSquareModPFlat_spec`: at `a0 = 5` the post
    pins `a1 = 5` (overwriting the incoming `a1 = 9`) and the exit pc is the
    specific OTHER routine's entry `GuestAddrs.secf_mul_mod_p`, neither the
    fallthrough `entry+8` nor the routine's own entry. -/
example :
    cpsTripleWithin 2 (GuestAddrs.secf_square_mod_p : Word)
      (GuestAddrs.secf_mul_mod_p : Word)
      (CodeReq.ofProg (GuestAddrs.secf_square_mod_p : Word) secfSquareModP_prog)
      ((.x10 ↦ᵣ (5 : Word)) ** (.x11 ↦ᵣ (9 : Word)))
      ((.x10 ↦ᵣ (5 : Word)) ** (.x11 ↦ᵣ (5 : Word))) := by
  exact secfSquareModPFlat_spec 5 9

example : GuestAddrs.secf_mul_mod_p ≠ GuestAddrs.secf_square_mod_p ∧
    GuestAddrs.secf_mul_mod_p ≠ GuestAddrs.secf_square_mod_p + 8 :=
  ⟨by decide, by decide⟩

/-! ## 5. `secf_square_mod_n` — the same wrapper over the scalar field -/

/-- `secf_square_mod_n` at a free `base`, with the `jal` displacement
    round-trip named. -/
theorem secfSquareModN_body_spec (base tgt a v11 : Word)
    (hjal : base + (4 : Word) +
        signExtend21 (jalOff GuestAddrs.secf_mul_mod_n (GuestAddrs.secf_square_mod_n + 4))
      = tgt) :
    cpsTripleWithin 2 base tgt
      (CodeReq.ofProg base secfSquareModN_prog)
      ((.x10 ↦ᵣ a) ** (.x11 ↦ᵣ v11))
      ((.x10 ↦ᵣ a) ** (.x11 ↦ᵣ a)) := by
  -- Rule 1 of the module header: present the code requirement as the
  -- `singleton`-union chain before `runBlock`.
  unfold secfSquareModN_prog
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil]
  have M := mv_spec_gen_within .x11 .x10 a v11 base (by nofun)
  have J := jal_x0_frame_within ((.x10 ↦ᵣ a) ** (.x11 ↦ᵣ a))
    Assertion.PCFree.proof
    (jalOff GuestAddrs.secf_mul_mod_n (GuestAddrs.secf_square_mod_n + 4)) (base + (4 : Word))
  rw [hjal] at J
  runBlock M J

/-- `secf_square_mod_n` deployed contract, anchored at the guest image entry. -/
theorem secfSquareModNFlat_spec (a v11 : Word) :
    cpsTripleWithin 2 (GuestAddrs.secf_square_mod_n : Word)
      (GuestAddrs.secf_mul_mod_n : Word)
      (CodeReq.ofProg (GuestAddrs.secf_square_mod_n : Word) secfSquareModN_prog)
      ((.x10 ↦ᵣ a) ** (.x11 ↦ᵣ v11))
      ((.x10 ↦ᵣ a) ** (.x11 ↦ᵣ a)) :=
  secfSquareModN_body_spec (GuestAddrs.secf_square_mod_n : Word)
    (GuestAddrs.secf_mul_mod_n : Word) a v11 (by decide)

/-- **Anti-vacuity witness** for `secfSquareModNFlat_spec`: the same shuffle but
    exiting at `GuestAddrs.secf_mul_mod_n` — a DIFFERENT callee from §4, so
    neither contract could be satisfied by the other's exit. -/
example :
    cpsTripleWithin 2 (GuestAddrs.secf_square_mod_n : Word)
      (GuestAddrs.secf_mul_mod_n : Word)
      (CodeReq.ofProg (GuestAddrs.secf_square_mod_n : Word) secfSquareModN_prog)
      ((.x10 ↦ᵣ (5 : Word)) ** (.x11 ↦ᵣ (9 : Word)))
      ((.x10 ↦ᵣ (5 : Word)) ** (.x11 ↦ᵣ (5 : Word))) := by
  exact secfSquareModNFlat_spec 5 9

example : GuestAddrs.secf_mul_mod_n ≠ GuestAddrs.secf_mul_mod_p := by decide

/-! ## 6-7. `derive_withdrawal_requests` / `derive_consolidation_requests`

  Seven instructions: shift `a0..a3` up into `a1..a4`, materialize the
  predeploy address into `a0`, tail-jump to `stage_system_call`.  These are
  the two routines `docs/leaf-routine-targets.md` annotated as leaves and
  #11578 corrected: they are NOT leaves, they are the argument-shuffling
  front half of `stage_system_call`.  The contract states the shuffle
  exactly and stops at the transfer, which is the honest whole-routine
  claim and is what a caller needs in order to apply a
  `stage_system_call` triple. -/

/-- `derive_withdrawal_requests` at a free `base`, with the `la` and `jal`
    round-trips named: `a4:=a3, a3:=a2, a2:=a1, a1:=a0, a0:=&predeploy`,
    then transfer. -/
theorem deriveWithdrawalRequests_body_spec
    (base addr tgt a0 a1 a2 a3 v14 : Word)
    (hla : base + (16 : Word) +
        (((laHi GuestAddrs.withdrawal_request_predeploy_addr
            (GuestAddrs.derive_withdrawal_requests + 16)).zeroExtend 32
              <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.withdrawal_request_predeploy_addr
          (GuestAddrs.derive_withdrawal_requests + 16)) = addr)
    (hjal : base + (24 : Word) +
        signExtend21 (jalOff GuestAddrs.stage_system_call
          (GuestAddrs.derive_withdrawal_requests + 24)) = tgt) :
    cpsTripleWithin 7 base tgt
      (CodeReq.ofProg base deriveWithdrawalRequests_prog)
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) ** (.x14 ↦ᵣ v14))
      ((.x10 ↦ᵣ addr) ** (.x11 ↦ᵣ a0) ** (.x12 ↦ᵣ a1) ** (.x13 ↦ᵣ a2) **
       (.x14 ↦ᵣ a3)) := by
  -- Rule 1 of the module header: present the code requirement as the
  -- `singleton`-union chain before `runBlock`.
  unfold deriveWithdrawalRequests_prog
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil]
  have M0 := mv_spec_gen_within .x14 .x13 a3 v14 base (by nofun)
  have M1 := mv_spec_gen_within .x13 .x12 a2 a3 (base + (4 : Word)) (by nofun)
  have M2 := mv_spec_gen_within .x12 .x11 a1 a2 (base + (8 : Word)) (by nofun)
  have M3 := mv_spec_gen_within .x11 .x10 a0 a1 (base + (12 : Word)) (by nofun)
  have AU := auipc_spec_gen_within .x10 a0
    (laHi GuestAddrs.withdrawal_request_predeploy_addr
      (GuestAddrs.derive_withdrawal_requests + 16)) (base + (16 : Word)) (by nofun)
  have AD := addi_spec_gen_same_within .x10
    ((base + (16 : Word)) +
      (((laHi GuestAddrs.withdrawal_request_predeploy_addr
          (GuestAddrs.derive_withdrawal_requests + 16)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.withdrawal_request_predeploy_addr
      (GuestAddrs.derive_withdrawal_requests + 16)) (base + (20 : Word)) (by nofun)
  rw [hla] at AD
  have J := jal_x0_frame_within
    ((.x10 ↦ᵣ addr) ** (.x11 ↦ᵣ a0) ** (.x12 ↦ᵣ a1) ** (.x13 ↦ᵣ a2) ** (.x14 ↦ᵣ a3))
    Assertion.PCFree.proof
    (jalOff GuestAddrs.stage_system_call (GuestAddrs.derive_withdrawal_requests + 24))
    (base + (24 : Word))
  rw [hjal] at J
  runBlock M0 M1 M2 M3 AU AD J

/-- `derive_withdrawal_requests` deployed contract, anchored at the guest
    image entry. -/
theorem deriveWithdrawalRequestsFlat_spec (a0 a1 a2 a3 v14 : Word) :
    cpsTripleWithin 7 (GuestAddrs.derive_withdrawal_requests : Word)
      (GuestAddrs.stage_system_call : Word)
      (CodeReq.ofProg (GuestAddrs.derive_withdrawal_requests : Word)
        deriveWithdrawalRequests_prog)
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) ** (.x14 ↦ᵣ v14))
      ((.x10 ↦ᵣ (GuestAddrs.withdrawal_request_predeploy_addr : Word)) **
       (.x11 ↦ᵣ a0) ** (.x12 ↦ᵣ a1) ** (.x13 ↦ᵣ a2) ** (.x14 ↦ᵣ a3)) :=
  deriveWithdrawalRequests_body_spec (GuestAddrs.derive_withdrawal_requests : Word)
    (GuestAddrs.withdrawal_request_predeploy_addr : Word)
    (GuestAddrs.stage_system_call : Word) a0 a1 a2 a3 v14 (by decide) (by decide)

/-- `derive_consolidation_requests` at a free `base` — the same shuffle with
    the consolidation predeploy address. -/
theorem deriveConsolidationRequests_body_spec
    (base addr tgt a0 a1 a2 a3 v14 : Word)
    (hla : base + (16 : Word) +
        (((laHi GuestAddrs.consolidation_request_predeploy_addr
            (GuestAddrs.derive_consolidation_requests + 16)).zeroExtend 32
              <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.consolidation_request_predeploy_addr
          (GuestAddrs.derive_consolidation_requests + 16)) = addr)
    (hjal : base + (24 : Word) +
        signExtend21 (jalOff GuestAddrs.stage_system_call
          (GuestAddrs.derive_consolidation_requests + 24)) = tgt) :
    cpsTripleWithin 7 base tgt
      (CodeReq.ofProg base deriveConsolidationRequests_prog)
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) ** (.x14 ↦ᵣ v14))
      ((.x10 ↦ᵣ addr) ** (.x11 ↦ᵣ a0) ** (.x12 ↦ᵣ a1) ** (.x13 ↦ᵣ a2) **
       (.x14 ↦ᵣ a3)) := by
  -- Rule 1 of the module header: present the code requirement as the
  -- `singleton`-union chain before `runBlock`.
  unfold deriveConsolidationRequests_prog
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil]
  have M0 := mv_spec_gen_within .x14 .x13 a3 v14 base (by nofun)
  have M1 := mv_spec_gen_within .x13 .x12 a2 a3 (base + (4 : Word)) (by nofun)
  have M2 := mv_spec_gen_within .x12 .x11 a1 a2 (base + (8 : Word)) (by nofun)
  have M3 := mv_spec_gen_within .x11 .x10 a0 a1 (base + (12 : Word)) (by nofun)
  have AU := auipc_spec_gen_within .x10 a0
    (laHi GuestAddrs.consolidation_request_predeploy_addr
      (GuestAddrs.derive_consolidation_requests + 16)) (base + (16 : Word)) (by nofun)
  have AD := addi_spec_gen_same_within .x10
    ((base + (16 : Word)) +
      (((laHi GuestAddrs.consolidation_request_predeploy_addr
          (GuestAddrs.derive_consolidation_requests + 16)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.consolidation_request_predeploy_addr
      (GuestAddrs.derive_consolidation_requests + 16)) (base + (20 : Word)) (by nofun)
  rw [hla] at AD
  have J := jal_x0_frame_within
    ((.x10 ↦ᵣ addr) ** (.x11 ↦ᵣ a0) ** (.x12 ↦ᵣ a1) ** (.x13 ↦ᵣ a2) ** (.x14 ↦ᵣ a3))
    Assertion.PCFree.proof
    (jalOff GuestAddrs.stage_system_call (GuestAddrs.derive_consolidation_requests + 24))
    (base + (24 : Word))
  rw [hjal] at J
  runBlock M0 M1 M2 M3 AU AD J

/-- `derive_consolidation_requests` deployed contract, anchored at the guest
    image entry. -/
theorem deriveConsolidationRequestsFlat_spec (a0 a1 a2 a3 v14 : Word) :
    cpsTripleWithin 7 (GuestAddrs.derive_consolidation_requests : Word)
      (GuestAddrs.stage_system_call : Word)
      (CodeReq.ofProg (GuestAddrs.derive_consolidation_requests : Word)
        deriveConsolidationRequests_prog)
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) ** (.x14 ↦ᵣ v14))
      ((.x10 ↦ᵣ (GuestAddrs.consolidation_request_predeploy_addr : Word)) **
       (.x11 ↦ᵣ a0) ** (.x12 ↦ᵣ a1) ** (.x13 ↦ᵣ a2) ** (.x14 ↦ᵣ a3)) :=
  deriveConsolidationRequests_body_spec (GuestAddrs.derive_consolidation_requests : Word)
    (GuestAddrs.consolidation_request_predeploy_addr : Word)
    (GuestAddrs.stage_system_call : Word) a0 a1 a2 a3 v14 (by decide) (by decide)

/-- **Anti-vacuity witness** for §7: at `a0..a3 = 1,2,3,4` the post names the
    withdrawal predeploy through `GuestAddrs.withdrawal_request_predeploy_addr`,
    leaves `a1..a4 = 1,2,3,4`, and exits at `GuestAddrs.stage_system_call`. -/
example :
    cpsTripleWithin 7 (GuestAddrs.derive_withdrawal_requests : Word)
      (GuestAddrs.stage_system_call : Word)
      (CodeReq.ofProg (GuestAddrs.derive_withdrawal_requests : Word)
        deriveWithdrawalRequests_prog)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** (.x12 ↦ᵣ (3 : Word)) **
       (.x13 ↦ᵣ (4 : Word)) ** (.x14 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (GuestAddrs.withdrawal_request_predeploy_addr : Word)) **
       (.x11 ↦ᵣ (1 : Word)) ** (.x12 ↦ᵣ (2 : Word)) **
       (.x13 ↦ᵣ (3 : Word)) ** (.x14 ↦ᵣ (4 : Word))) := by
  exact deriveWithdrawalRequestsFlat_spec 1 2 3 4 0

/-- **Anti-vacuity witness** for §8: the same shuffle but with the consolidation
    predeploy address named by `GuestAddrs.consolidation_request_predeploy_addr`. -/
example :
    cpsTripleWithin 7 (GuestAddrs.derive_consolidation_requests : Word)
      (GuestAddrs.stage_system_call : Word)
      (CodeReq.ofProg (GuestAddrs.derive_consolidation_requests : Word)
        deriveConsolidationRequests_prog)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** (.x12 ↦ᵣ (3 : Word)) **
       (.x13 ↦ᵣ (4 : Word)) ** (.x14 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (GuestAddrs.consolidation_request_predeploy_addr : Word)) **
       (.x11 ↦ᵣ (1 : Word)) ** (.x12 ↦ᵣ (2 : Word)) **
       (.x13 ↦ᵣ (3 : Word)) ** (.x14 ↦ᵣ (4 : Word))) := by
  exact deriveConsolidationRequestsFlat_spec 1 2 3 4 0

/-- The two routines materialize DIFFERENT predeploy addresses into `a0` and both
    land on the same `stage_system_call` entry — so neither post is satisfiable by
    the other's, and the shared exit is a real address, not a fallthrough. -/
example : GuestAddrs.withdrawal_request_predeploy_addr ≠
      GuestAddrs.consolidation_request_predeploy_addr ∧
    GuestAddrs.stage_system_call ≠ GuestAddrs.derive_withdrawal_requests + 28 ∧
    GuestAddrs.stage_system_call ≠ GuestAddrs.derive_consolidation_requests + 28 :=
  ⟨by decide, by decide, by decide⟩

/-! ## 8-9. `derive_builder_deposit_requests` / `derive_builder_exit_requests`

  The EIP-8282 builder deposit/exit adapters (#12318 callee-composition
  lane).  Byte-for-byte the same seven-instruction shape as §6-7 — shift
  `a0..a3` up into `a1..a4`, materialize the contract address into `a0`,
  tail-jump to `stage_system_call` — with a different address constant,
  so the same tail-transfer contract is the honest whole-routine claim.

  **Extent, from the linked image and not from prose.**
  `scripts/asm-fixtures/symbol-addresses.tsv` places
  `derive_builder_deposit_requests` at `0x8005369c`,
  `derive_builder_exit_requests` at `0x800536b8` and `stage_system_call`
  at `0x800536d4`: 28 bytes each, which is `prog.length * 4` for the
  `#guard`ed `prog.length = 7` in
  `Codegen/Programs/SystemCallStaging.lean`.  Both
  `(GuestAddrs.<sym>, <sym>_prog)` pairs are in `GuestImageEntries`, so
  the `CodeReq` below is the deployed code and not a detached listing.

  ⚠️ **`scripts/callee-composition-queue.py` grades both at in-degree
  `0 / 0`, and that must not be read as dead code.**  Both are called by
  `block_state_root` — `jal ra, derive_builder_deposit_requests` in the
  `.Lc1_bd_call` arm of `blockStateRootFunction`
  (`Codegen/Programs/BlockVerdictStateRoot.lean`), and the builder-exit
  arm below it.  That caller is linked (`0x80013830` in
  `scripts/asm-fixtures/symbol-addresses.tsv`) but is still emitted as
  assembly TEXT: it has no `Program`, no `GuestAddrs` constant and no
  `scripts/asm-fixtures/*.s` entry, so BOTH of the queue's graphs — the
  image graph and the fixture graph — miss the edge.  The `0 / 0` here is
  the absence of a converted caller, not the absence of a caller.

  As in §6-7 the contract composes NOTHING from `stage_system_call`: it
  stops at the transfer, so it inherits none of that routine's
  `.conditional` gate. -/

/-- `derive_builder_deposit_requests` at a free `base`, with the `la` and
    `jal` round-trips named: `a4:=a3, a3:=a2, a2:=a1, a1:=a0,
    a0:=&builder_deposit_contract_addr`, then transfer. -/
theorem deriveBuilderDepositRequests_body_spec
    (base addr tgt a0 a1 a2 a3 v14 : Word)
    (hla : base + (16 : Word) +
        (((laHi GuestAddrs.builder_deposit_contract_addr
            (GuestAddrs.derive_builder_deposit_requests + 16)).zeroExtend 32
              <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.builder_deposit_contract_addr
          (GuestAddrs.derive_builder_deposit_requests + 16)) = addr)
    (hjal : base + (24 : Word) +
        signExtend21 (jalOff GuestAddrs.stage_system_call
          (GuestAddrs.derive_builder_deposit_requests + 24)) = tgt) :
    cpsTripleWithin 7 base tgt
      (CodeReq.ofProg base deriveBuilderDepositRequests_prog)
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) ** (.x14 ↦ᵣ v14))
      ((.x10 ↦ᵣ addr) ** (.x11 ↦ᵣ a0) ** (.x12 ↦ᵣ a1) ** (.x13 ↦ᵣ a2) **
       (.x14 ↦ᵣ a3)) := by
  -- Rule 1 of the module header: present the code requirement as the
  -- `singleton`-union chain before `runBlock`.
  unfold deriveBuilderDepositRequests_prog
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil]
  have M0 := mv_spec_gen_within .x14 .x13 a3 v14 base (by nofun)
  have M1 := mv_spec_gen_within .x13 .x12 a2 a3 (base + (4 : Word)) (by nofun)
  have M2 := mv_spec_gen_within .x12 .x11 a1 a2 (base + (8 : Word)) (by nofun)
  have M3 := mv_spec_gen_within .x11 .x10 a0 a1 (base + (12 : Word)) (by nofun)
  have AU := auipc_spec_gen_within .x10 a0
    (laHi GuestAddrs.builder_deposit_contract_addr
      (GuestAddrs.derive_builder_deposit_requests + 16)) (base + (16 : Word)) (by nofun)
  have AD := addi_spec_gen_same_within .x10
    ((base + (16 : Word)) +
      (((laHi GuestAddrs.builder_deposit_contract_addr
          (GuestAddrs.derive_builder_deposit_requests + 16)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.builder_deposit_contract_addr
      (GuestAddrs.derive_builder_deposit_requests + 16)) (base + (20 : Word)) (by nofun)
  rw [hla] at AD
  have J := jal_x0_frame_within
    ((.x10 ↦ᵣ addr) ** (.x11 ↦ᵣ a0) ** (.x12 ↦ᵣ a1) ** (.x13 ↦ᵣ a2) ** (.x14 ↦ᵣ a3))
    Assertion.PCFree.proof
    (jalOff GuestAddrs.stage_system_call (GuestAddrs.derive_builder_deposit_requests + 24))
    (base + (24 : Word))
  rw [hjal] at J
  runBlock M0 M1 M2 M3 AU AD J

/-- `derive_builder_deposit_requests` deployed contract, anchored at the
    guest image entry. -/
theorem deriveBuilderDepositRequestsFlat_spec (a0 a1 a2 a3 v14 : Word) :
    cpsTripleWithin 7 (GuestAddrs.derive_builder_deposit_requests : Word)
      (GuestAddrs.stage_system_call : Word)
      (CodeReq.ofProg (GuestAddrs.derive_builder_deposit_requests : Word)
        deriveBuilderDepositRequests_prog)
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) ** (.x14 ↦ᵣ v14))
      ((.x10 ↦ᵣ (GuestAddrs.builder_deposit_contract_addr : Word)) **
       (.x11 ↦ᵣ a0) ** (.x12 ↦ᵣ a1) ** (.x13 ↦ᵣ a2) ** (.x14 ↦ᵣ a3)) :=
  deriveBuilderDepositRequests_body_spec
    (GuestAddrs.derive_builder_deposit_requests : Word)
    (GuestAddrs.builder_deposit_contract_addr : Word)
    (GuestAddrs.stage_system_call : Word) a0 a1 a2 a3 v14 (by decide) (by decide)

/-- `derive_builder_exit_requests` at a free `base` — the same shuffle with
    the builder EXIT contract address. -/
theorem deriveBuilderExitRequests_body_spec
    (base addr tgt a0 a1 a2 a3 v14 : Word)
    (hla : base + (16 : Word) +
        (((laHi GuestAddrs.builder_exit_contract_addr
            (GuestAddrs.derive_builder_exit_requests + 16)).zeroExtend 32
              <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.builder_exit_contract_addr
          (GuestAddrs.derive_builder_exit_requests + 16)) = addr)
    (hjal : base + (24 : Word) +
        signExtend21 (jalOff GuestAddrs.stage_system_call
          (GuestAddrs.derive_builder_exit_requests + 24)) = tgt) :
    cpsTripleWithin 7 base tgt
      (CodeReq.ofProg base deriveBuilderExitRequests_prog)
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) ** (.x14 ↦ᵣ v14))
      ((.x10 ↦ᵣ addr) ** (.x11 ↦ᵣ a0) ** (.x12 ↦ᵣ a1) ** (.x13 ↦ᵣ a2) **
       (.x14 ↦ᵣ a3)) := by
  -- Rule 1 of the module header: present the code requirement as the
  -- `singleton`-union chain before `runBlock`.
  unfold deriveBuilderExitRequests_prog
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil]
  have M0 := mv_spec_gen_within .x14 .x13 a3 v14 base (by nofun)
  have M1 := mv_spec_gen_within .x13 .x12 a2 a3 (base + (4 : Word)) (by nofun)
  have M2 := mv_spec_gen_within .x12 .x11 a1 a2 (base + (8 : Word)) (by nofun)
  have M3 := mv_spec_gen_within .x11 .x10 a0 a1 (base + (12 : Word)) (by nofun)
  have AU := auipc_spec_gen_within .x10 a0
    (laHi GuestAddrs.builder_exit_contract_addr
      (GuestAddrs.derive_builder_exit_requests + 16)) (base + (16 : Word)) (by nofun)
  have AD := addi_spec_gen_same_within .x10
    ((base + (16 : Word)) +
      (((laHi GuestAddrs.builder_exit_contract_addr
          (GuestAddrs.derive_builder_exit_requests + 16)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.builder_exit_contract_addr
      (GuestAddrs.derive_builder_exit_requests + 16)) (base + (20 : Word)) (by nofun)
  rw [hla] at AD
  have J := jal_x0_frame_within
    ((.x10 ↦ᵣ addr) ** (.x11 ↦ᵣ a0) ** (.x12 ↦ᵣ a1) ** (.x13 ↦ᵣ a2) ** (.x14 ↦ᵣ a3))
    Assertion.PCFree.proof
    (jalOff GuestAddrs.stage_system_call (GuestAddrs.derive_builder_exit_requests + 24))
    (base + (24 : Word))
  rw [hjal] at J
  runBlock M0 M1 M2 M3 AU AD J

/-- `derive_builder_exit_requests` deployed contract, anchored at the guest
    image entry. -/
theorem deriveBuilderExitRequestsFlat_spec (a0 a1 a2 a3 v14 : Word) :
    cpsTripleWithin 7 (GuestAddrs.derive_builder_exit_requests : Word)
      (GuestAddrs.stage_system_call : Word)
      (CodeReq.ofProg (GuestAddrs.derive_builder_exit_requests : Word)
        deriveBuilderExitRequests_prog)
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) ** (.x14 ↦ᵣ v14))
      ((.x10 ↦ᵣ (GuestAddrs.builder_exit_contract_addr : Word)) **
       (.x11 ↦ᵣ a0) ** (.x12 ↦ᵣ a1) ** (.x13 ↦ᵣ a2) ** (.x14 ↦ᵣ a3)) :=
  deriveBuilderExitRequests_body_spec
    (GuestAddrs.derive_builder_exit_requests : Word)
    (GuestAddrs.builder_exit_contract_addr : Word)
    (GuestAddrs.stage_system_call : Word) a0 a1 a2 a3 v14 (by decide) (by decide)

/-- **Anti-vacuity witness** for §8: at `a0..a3 = 1,2,3,4` the post names the
    builder deposit contract through `GuestAddrs.builder_deposit_contract_addr`,
    leaves `a1..a4 = 1,2,3,4`, and exits at `GuestAddrs.stage_system_call`.
    NAMED (not an anonymous `example`) so `Progress/Routines.lean` can witness
    it and `check-nonvacuity-witnessed.py` sees the row's evidence inside the
    axiom gate rather than in prose. -/
theorem deriveBuilderDepositRequests_sample_reachable :
    cpsTripleWithin 7 (GuestAddrs.derive_builder_deposit_requests : Word)
      (GuestAddrs.stage_system_call : Word)
      (CodeReq.ofProg (GuestAddrs.derive_builder_deposit_requests : Word)
        deriveBuilderDepositRequests_prog)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** (.x12 ↦ᵣ (3 : Word)) **
       (.x13 ↦ᵣ (4 : Word)) ** (.x14 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (GuestAddrs.builder_deposit_contract_addr : Word)) **
       (.x11 ↦ᵣ (1 : Word)) ** (.x12 ↦ᵣ (2 : Word)) **
       (.x13 ↦ᵣ (3 : Word)) ** (.x14 ↦ᵣ (4 : Word))) := by
  exact deriveBuilderDepositRequestsFlat_spec 1 2 3 4 0

/-- **Anti-vacuity witness** for §9: the same shuffle with the builder EXIT
    contract address named by `GuestAddrs.builder_exit_contract_addr`. -/
theorem deriveBuilderExitRequests_sample_reachable :
    cpsTripleWithin 7 (GuestAddrs.derive_builder_exit_requests : Word)
      (GuestAddrs.stage_system_call : Word)
      (CodeReq.ofProg (GuestAddrs.derive_builder_exit_requests : Word)
        deriveBuilderExitRequests_prog)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** (.x12 ↦ᵣ (3 : Word)) **
       (.x13 ↦ᵣ (4 : Word)) ** (.x14 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (GuestAddrs.builder_exit_contract_addr : Word)) **
       (.x11 ↦ᵣ (1 : Word)) ** (.x12 ↦ᵣ (2 : Word)) **
       (.x13 ↦ᵣ (3 : Word)) ** (.x14 ↦ᵣ (4 : Word))) := by
  exact deriveBuilderExitRequestsFlat_spec 1 2 3 4 0

/-- **Negative control** for §8-9.  All FOUR request adapters materialize
    PAIRWISE DISTINCT addresses into `a0` and land on the same
    `stage_system_call` entry, so no one of the four posts is satisfiable by
    any other's — a contract that had silently proved the wrong constant, or
    that had been stated over the wrong sibling's `_prog`, could not have
    passed.

    ⚠️ The §6-7 control also asserted that the exit is not the routine's
    fallthrough `<sym> + 28`.  That conjunct holds for the deposit adapter
    (whose `j` skips OVER the exit adapter) but is **provably false** for
    `derive_builder_exit_requests`: it is laid out immediately before
    `stage_system_call`, so its tail jump targets exactly its own
    fallthrough address.  The fact is recorded here as the equality it is
    rather than dropped, because it is the one place a reader could
    mistake a fallthrough for a proven transfer — for that row it is the
    address-distinctness conjuncts above, not the exit address, that
    carry the control. -/
theorem deriveBuilderRequests_addr_control :
    GuestAddrs.builder_deposit_contract_addr ≠ GuestAddrs.builder_exit_contract_addr ∧
    GuestAddrs.builder_deposit_contract_addr ≠
      GuestAddrs.withdrawal_request_predeploy_addr ∧
    GuestAddrs.builder_deposit_contract_addr ≠
      GuestAddrs.consolidation_request_predeploy_addr ∧
    GuestAddrs.builder_exit_contract_addr ≠
      GuestAddrs.withdrawal_request_predeploy_addr ∧
    GuestAddrs.builder_exit_contract_addr ≠
      GuestAddrs.consolidation_request_predeploy_addr ∧
    GuestAddrs.stage_system_call ≠ GuestAddrs.derive_builder_deposit_requests + 28 ∧
    GuestAddrs.derive_builder_deposit_requests + 28 = GuestAddrs.derive_builder_exit_requests ∧
    GuestAddrs.stage_system_call = GuestAddrs.derive_builder_exit_requests + 28 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Negative control, hypothesis side.**  The linking hypotheses of the
    `*_body_spec`s are not vacuously satisfiable: at the DEPLOYED base each is
    discharged by `decide` above, but the SAME `hla` is provably FALSE when the
    base is moved off the linked layout — here `base := GuestAddrs.`
    `derive_builder_deposit_requests + 4`, one instruction along.  So
    `deriveBuilderDepositRequests_body_spec` genuinely constrains `base`, and
    an implementation of it that ignored the relocation round-trip would be
    unsound. -/
theorem deriveBuilderDepositRequests_hla_false_off_base :
    ¬ ((GuestAddrs.derive_builder_deposit_requests : Word) + (4 : Word) + (16 : Word) +
        (((laHi GuestAddrs.builder_deposit_contract_addr
            (GuestAddrs.derive_builder_deposit_requests + 16)).zeroExtend 32
              <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.builder_deposit_contract_addr
          (GuestAddrs.derive_builder_deposit_requests + 16))
      = (GuestAddrs.builder_deposit_contract_addr : Word)) := by decide

/-! ## 10. `bal_serializer_u64_to_field` — widen a u64 into a 32-byte LE field

  Six instructions, **no relocation of any kind**: four `sd zero` to clear
  the 32-byte field, one `sd a1` to lay the u64 into the least-significant
  limb, and `ret`.  It is the purest instance of the shape #12245 asks
  about — the `*_body_spec` below carries NO linking hypothesis, so the
  anchored form is a bare instantiation with nothing to `decide`.

  **Extent, from the linked image and not from prose.**
  `scripts/asm-fixtures/symbol-addresses.tsv` places
  `bal_serializer_u64_to_field` at `0x800241c0` and the next `.text`
  symbol `bal_serializer_measure_reads` at `0x800241d8`: 24 bytes, which
  is `prog.length * 4` for the `#guard`ed `prog.length = 6` in
  `Codegen/Programs/BalSerializer.lean`.  The pair
  `(GuestAddrs.bal_serializer_u64_to_field, balSerializerU64ToField_prog)`
  is in `guestImageEntries`, so the `CodeReq` is the deployed code.

  ⚠️ **The first and the fifth store are to the SAME address.**  `sd zero,
  0(a0)` clears limb 0 and `sd a1, 0(a0)` immediately overwrites it, so
  the strongest post for that cell is `a1`, not `0` — the contract states
  the final value and the intermediate `0` never appears.  A contract
  written from the instruction list without tracking the aliasing would
  claim all four limbs zero, and the u64 would vanish.

  In-degree is real: `bal_serializer_emit_storage`, `emit_balance` and
  `emit_nonce` (×4 call sites) all widen through this routine
  (`Codegen/Programs/BalSerializerTail.lean`).  The LE limb order the post
  states is the one that docstring's bug history turns on. -/

/-- `bal_serializer_u64_to_field` at a free `base`.  No relocation, hence no
    linking hypothesis: the four 8-byte limbs at `a0`, `a0+8`, `a0+16`,
    `a0+24` end holding `a1, 0, 0, 0` — little-endian, least-significant
    limb first — with every register unchanged and return through `ra`. -/
theorem balSerializerU64ToField_body_spec
    (base a0 a1 ra m0 m1 m2 m3 : Word) :
    cpsTripleWithin 6 base (ra &&& ~~~1)
      (CodeReq.ofProg base balSerializerU64ToField_prog)
      ((.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) **
       (a0 ↦ₘ m0) ** ((a0 + (8 : Word)) ↦ₘ m1) **
       ((a0 + (16 : Word)) ↦ₘ m2) ** ((a0 + (24 : Word)) ↦ₘ m3))
      ((.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) **
       (a0 ↦ₘ a1) ** ((a0 + (8 : Word)) ↦ₘ (0 : Word)) **
       ((a0 + (16 : Word)) ↦ₘ (0 : Word)) **
       ((a0 + (24 : Word)) ↦ₘ (0 : Word))) := by
  -- Rule 1 of the module header: present the code requirement as the
  -- `singleton`-union chain before `runBlock`.
  unfold balSerializerU64ToField_prog
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil]
  have Z0 := sd_x0_spec_gen_within .x10 a0 m0 (0 : BitVec 12) base
  rw [show a0 + signExtend12 (0 : BitVec 12) = a0 from by
    rw [signExtend12_0]; exact BitVec.add_zero a0] at Z0
  have Z1 := sd_x0_spec_gen_within .x10 a0 m1 (8 : BitVec 12) (base + (4 : Word))
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at Z1
  have Z2 := sd_x0_spec_gen_within .x10 a0 m2 (16 : BitVec 12) (base + (8 : Word))
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at Z2
  have Z3 := sd_x0_spec_gen_within .x10 a0 m3 (24 : BitVec 12) (base + (12 : Word))
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at Z3
  -- The aliasing step: limb 0 currently holds the `0` written by `Z0`.
  have S := sd_spec_gen_within .x10 .x11 a0 a1 (0 : Word) (0 : BitVec 12)
    (base + (16 : Word))
  rw [show a0 + signExtend12 (0 : BitVec 12) = a0 from by
    rw [signExtend12_0]; exact BitVec.add_zero a0] at S
  have R := EvmAsm.Evm64.ret_spec_within' (base + (20 : Word)) ra
  runBlock Z0 Z1 Z2 Z3 S R

/-- `bal_serializer_u64_to_field` deployed contract, anchored at the guest
    image entry.  There is no relocation to discharge, so this is the
    `*_body_spec` at `base := GuestAddrs.bal_serializer_u64_to_field` and
    nothing else. -/
theorem balSerializerU64ToFieldFlat_spec (a0 a1 ra m0 m1 m2 m3 : Word) :
    cpsTripleWithin 6 (GuestAddrs.bal_serializer_u64_to_field : Word) (ra &&& ~~~1)
      (CodeReq.ofProg (GuestAddrs.bal_serializer_u64_to_field : Word)
        balSerializerU64ToField_prog)
      ((.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) **
       (a0 ↦ₘ m0) ** ((a0 + (8 : Word)) ↦ₘ m1) **
       ((a0 + (16 : Word)) ↦ₘ m2) ** ((a0 + (24 : Word)) ↦ₘ m3))
      ((.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) **
       (a0 ↦ₘ a1) ** ((a0 + (8 : Word)) ↦ₘ (0 : Word)) **
       ((a0 + (16 : Word)) ↦ₘ (0 : Word)) **
       ((a0 + (24 : Word)) ↦ₘ (0 : Word))) :=
  balSerializerU64ToField_body_spec
    (GuestAddrs.bal_serializer_u64_to_field : Word) a0 a1 ra m0 m1 m2 m3

/-- **Anti-vacuity witness** for §10.  At `a1 = 0x0102030405060708` into a
    field whose four limbs all start at `0xffffffffffffffff`, the post is
    fully numeric: limb 0 carries the u64 and limbs 1-3 are cleared.  The
    starting value is chosen NON-zero on purpose — with `m0..m3 = 0` the
    four clearing stores would be indistinguishable from no-ops, and the
    post would hold of a routine that did nothing to limbs 1-3.

    NAMED (not an anonymous `example`) so `Progress/Routines.lean` can cite
    it and `check-nonvacuity-witnessed.py` sees the row's evidence inside
    the axiom gate rather than in prose. -/
theorem balSerializerU64ToField_sample_reachable (ra : Word) :
    cpsTripleWithin 6 (GuestAddrs.bal_serializer_u64_to_field : Word) (ra &&& ~~~1)
      (CodeReq.ofProg (GuestAddrs.bal_serializer_u64_to_field : Word)
        balSerializerU64ToField_prog)
      ((.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ (0xa2d00000 : Word)) **
       (.x11 ↦ᵣ (0x0102030405060708 : Word)) **
       ((0xa2d00000 : Word) ↦ₘ (0xffffffffffffffff : Word)) **
       ((0xa2d00008 : Word) ↦ₘ (0xffffffffffffffff : Word)) **
       ((0xa2d00010 : Word) ↦ₘ (0xffffffffffffffff : Word)) **
       ((0xa2d00018 : Word) ↦ₘ (0xffffffffffffffff : Word)))
      ((.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ (0xa2d00000 : Word)) **
       (.x11 ↦ᵣ (0x0102030405060708 : Word)) **
       ((0xa2d00000 : Word) ↦ₘ (0x0102030405060708 : Word)) **
       ((0xa2d00008 : Word) ↦ₘ (0 : Word)) **
       ((0xa2d00010 : Word) ↦ₘ (0 : Word)) **
       ((0xa2d00018 : Word) ↦ₘ (0 : Word))) := by
  have h := balSerializerU64ToFieldFlat_spec (0xa2d00000 : Word)
    (0x0102030405060708 : Word) ra
    (0xffffffffffffffff : Word) (0xffffffffffffffff : Word)
    (0xffffffffffffffff : Word) (0xffffffffffffffff : Word)
  rw [show (0xa2d00000 : Word) + (8 : Word) = (0xa2d00008 : Word) from by decide,
    show (0xa2d00000 : Word) + (16 : Word) = (0xa2d00010 : Word) from by decide,
    show (0xa2d00000 : Word) + (24 : Word) = (0xa2d00018 : Word) from by decide] at h
  exact h

/-- **Negative control** for §10, on the aliasing that the contract turns on.
    The five stores hit only FOUR distinct addresses: `0(a0)` is written
    twice.  Recorded as the two facts it is — the four limb addresses are
    pairwise distinct offsets, and the fifth store's address is provably
    EQUAL to the first store's — because a contract that had missed the
    aliasing would put `0` in limb 0 and still typecheck.  The `= 0`
    conjunct is what makes limb 0's post `a1` rather than `0`. -/
theorem balSerializerU64ToField_alias_control :
    ((8 : Word) ≠ (0 : Word)) ∧ ((16 : Word) ≠ (0 : Word)) ∧
    ((24 : Word) ≠ (0 : Word)) ∧ ((16 : Word) ≠ (8 : Word)) ∧
    ((24 : Word) ≠ (8 : Word)) ∧ ((24 : Word) ≠ (16 : Word)) ∧
    signExtend12 (0 : BitVec 12) = (0 : Word) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## 11. `mpt_delete_walk_db` — the one-instruction tail transfer

  The whole routine is `j mpt_set_record_walk_db`: delete and set share an
  ABI and a stack layout, so the delete entry point is a pure rename of
  the set walker.  One instruction, no branch, no `ret`, nothing written.

  **Extent, from the linked image and not from prose.**
  `scripts/asm-fixtures/symbol-addresses.tsv` places `mpt_delete_walk_db`
  at `0x800073fc` and the next `.text` symbol `mpt_extension_extract` at
  `0x80007400`: 4 bytes, which is `prog.length * 4` for the `#guard`ed
  `(mptDeleteWalkDb_prog_of .zero).length = 1` in
  `Codegen/Programs/MptDeleteWalkDbProg.lean`.  The pair
  `(GuestAddrs.mpt_delete_walk_db, mptDeleteWalkDb_prog)` is in
  `guestImageEntries`.

  This is the routine whose one-instruction body was graded **loop-bearing**
  by the shape dump before #12790 — a single instruction cannot contain a
  loop, and it was that witness which exposed the missing extent conjunct
  in the back-edge test.  Rowing it closes the loop on its own bug report.

  Because nothing is written and no register is touched, the strongest post
  is the precondition itself for an ARBITRARY `pcFree` frame — the contract
  is parametric in `P`.  As in §6-9 it composes nothing from the callee: it
  stops at the transfer, and inherits none of `mpt_set_record_walk_db`'s
  own status. -/

/-- `mpt_delete_walk_db` at a free `base`, with the `jal` round-trip named:
    control moves to `tgt` and NOTHING else changes, for any `pcFree` `P`. -/
theorem mptDeleteWalkDb_body_spec (base tgt : Word) (P : Assertion) (hP : P.pcFree)
    (hjal : base +
        signExtend21 (jalOff GuestAddrs.mpt_set_record_walk_db
          (GuestAddrs.mpt_delete_walk_db + 0)) = tgt) :
    cpsTripleWithin 1 base tgt
      (CodeReq.ofProg base mptDeleteWalkDb_prog) P P := by
  unfold mptDeleteWalkDb_prog mptDeleteWalkDb_prog_of
  rw [CodeReq.ofProg_singleton]
  have J := jal_x0_frame_within P hP
    (jalOff guestLayout.mpt_set_record_walk_db (guestLayout.mpt_delete_walk_db + 0)) base
  rw [show (guestLayout.mpt_set_record_walk_db) = GuestAddrs.mpt_set_record_walk_db from rfl,
    show (guestLayout.mpt_delete_walk_db) = GuestAddrs.mpt_delete_walk_db from rfl] at J
  rw [hjal] at J
  exact J

/-- `mpt_delete_walk_db` deployed contract, anchored at the guest image entry:
    the tail jump lands exactly on `GuestAddrs.mpt_set_record_walk_db`, and the
    seven-argument walk ABI (`a0..a6`) plus `ra` arrives there untouched. -/
theorem mptDeleteWalkDbFlat_spec (ra a0 a1 a2 a3 a4 a5 a6 : Word) :
    cpsTripleWithin 1 (GuestAddrs.mpt_delete_walk_db : Word)
      (GuestAddrs.mpt_set_record_walk_db : Word)
      (CodeReq.ofProg (GuestAddrs.mpt_delete_walk_db : Word) mptDeleteWalkDb_prog)
      ((.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
       (.x13 ↦ᵣ a3) ** (.x14 ↦ᵣ a4) ** (.x15 ↦ᵣ a5) ** (.x16 ↦ᵣ a6))
      ((.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
       (.x13 ↦ᵣ a3) ** (.x14 ↦ᵣ a4) ** (.x15 ↦ᵣ a5) ** (.x16 ↦ᵣ a6)) :=
  mptDeleteWalkDb_body_spec (GuestAddrs.mpt_delete_walk_db : Word)
    (GuestAddrs.mpt_set_record_walk_db : Word) _ Assertion.PCFree.proof (by decide)

/-- **Anti-vacuity witness** for §11: at eight distinct concrete argument
    values the pre and post are fully numeric and the exit pc is the named
    `GuestAddrs.mpt_set_record_walk_db`.  NAMED so `Progress/Routines.lean`
    can cite it inside the axiom gate. -/
theorem mptDeleteWalkDb_sample_reachable :
    cpsTripleWithin 1 (GuestAddrs.mpt_delete_walk_db : Word)
      (GuestAddrs.mpt_set_record_walk_db : Word)
      (CodeReq.ofProg (GuestAddrs.mpt_delete_walk_db : Word) mptDeleteWalkDb_prog)
      ((.x1 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (2 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
       (.x12 ↦ᵣ (4 : Word)) ** (.x13 ↦ᵣ (5 : Word)) ** (.x14 ↦ᵣ (6 : Word)) **
       (.x15 ↦ᵣ (7 : Word)) ** (.x16 ↦ᵣ (8 : Word)))
      ((.x1 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (2 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
       (.x12 ↦ᵣ (4 : Word)) ** (.x13 ↦ᵣ (5 : Word)) ** (.x14 ↦ᵣ (6 : Word)) **
       (.x15 ↦ᵣ (7 : Word)) ** (.x16 ↦ᵣ (8 : Word))) :=
  mptDeleteWalkDbFlat_spec 1 2 3 4 5 6 7 8

/-- **Negative control** for §11, on both halves of the transfer claim.

    The exit address is the callee and NOT the routine's own fallthrough:
    `mpt_delete_walk_db + 4` is `mpt_extension_extract`, a different
    routine, and the jump goes backwards to `mpt_set_record_walk_db` at a
    LOWER address — which is exactly why the pre-#12790 shape dump graded
    this one-instruction body as containing a loop.  The strict inequality
    below is that back-edge, recorded as the fact it is.

    Hypothesis side: the SAME `hjal` is provably FALSE one instruction off
    the linked base, so `mptDeleteWalkDb_body_spec` genuinely constrains
    `base` and did not prove a transfer that holds everywhere. -/
theorem mptDeleteWalkDb_transfer_control :
    GuestAddrs.mpt_set_record_walk_db ≠ GuestAddrs.mpt_delete_walk_db + 4 ∧
    GuestAddrs.mpt_set_record_walk_db < GuestAddrs.mpt_delete_walk_db ∧
    ¬ ((GuestAddrs.mpt_delete_walk_db : Word) + (4 : Word) +
        signExtend21 (jalOff GuestAddrs.mpt_set_record_walk_db
          (GuestAddrs.mpt_delete_walk_db + 0))
      = (GuestAddrs.mpt_set_record_walk_db : Word)) :=
  ⟨by decide, by decide, by decide⟩

/-! ## Axiom audit — every contract is classical-only. -/

#print axioms wcidxRecordPtrFlat_spec
#print axioms writeSetsDiscardTxFlat_spec
#print axioms readSetsDiscardTxFlat_spec
#print axioms secfSquareModPFlat_spec
#print axioms secfSquareModNFlat_spec
#print axioms deriveWithdrawalRequestsFlat_spec
#print axioms deriveConsolidationRequestsFlat_spec
#print axioms deriveBuilderDepositRequestsFlat_spec
#print axioms deriveBuilderExitRequestsFlat_spec
#print axioms balSerializerU64ToFieldFlat_spec
#print axioms mptDeleteWalkDbFlat_spec

end EvmAsm.Codegen.Proofs
