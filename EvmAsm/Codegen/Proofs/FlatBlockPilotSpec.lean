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
    (`secf_square_mod_p`, `secf_square_mod_n`, `rlp_walk_next_nested`,
    `derive_withdrawal_requests`, `derive_consolidation_requests`).
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
    holding `7` end holding `0`, at three concrete and pairwise DISTINCT guest
    addresses, and `t0` ends at a specific one of them.  So the post is three
    independent value changes, not one aliased or vacuous claim. -/
example (ra : Word) :
    cpsTripleWithin 10 (GuestAddrs.write_sets_discard_tx : Word) (ra &&& ~~~1)
      (CodeReq.ofProg (GuestAddrs.write_sets_discard_tx : Word) writeSetsDiscardTx_prog)
      ((.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ (0 : Word)) **
       ((0xb9ccba78 : Word) ↦ₘ (7 : Word)) **
       ((0xb9ccba80 : Word) ↦ₘ (7 : Word)) **
       ((0xb9ccba88 : Word) ↦ₘ (7 : Word)))
      ((.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ (0xb9ccba88 : Word)) **
       ((0xb9ccba78 : Word) ↦ₘ (0 : Word)) **
       ((0xb9ccba80 : Word) ↦ₘ (0 : Word)) **
       ((0xb9ccba88 : Word) ↦ₘ (0 : Word))) := by
  have h := writeSetsDiscardTxFlat_spec ra 0 7 7 7
  rw [show (GuestAddrs.tx_storage_writes_count : Word) = (0xb9ccba78 : Word) from by decide,
    show (GuestAddrs.tx_storage_writes_overflow : Word) = (0xb9ccba80 : Word) from by decide,
    show (GuestAddrs.storage_writes_undo_count : Word) = (0xb9ccba88 : Word) from by decide] at h
  exact h

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
    concrete address `0x8001f2d8` — a specific OTHER routine's entry, neither
    the fallthrough `entry+8` nor the routine's own entry. -/
example :
    cpsTripleWithin 2 (GuestAddrs.secf_square_mod_p : Word) (0x8001f2d8 : Word)
      (CodeReq.ofProg (GuestAddrs.secf_square_mod_p : Word) secfSquareModP_prog)
      ((.x10 ↦ᵣ (5 : Word)) ** (.x11 ↦ᵣ (9 : Word)))
      ((.x10 ↦ᵣ (5 : Word)) ** (.x11 ↦ᵣ (5 : Word))) := by
  have h := secfSquareModPFlat_spec 5 9
  rw [show (GuestAddrs.secf_mul_mod_p : Word) = (0x8001f2d8 : Word) from by decide] at h
  exact h

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
    exiting at the concrete `0x8001f5b8` — a DIFFERENT callee from §4, so neither
    contract could be satisfied by the other's exit. -/
example :
    cpsTripleWithin 2 (GuestAddrs.secf_square_mod_n : Word) (0x8001f5b8 : Word)
      (CodeReq.ofProg (GuestAddrs.secf_square_mod_n : Word) secfSquareModN_prog)
      ((.x10 ↦ᵣ (5 : Word)) ** (.x11 ↦ᵣ (9 : Word)))
      ((.x10 ↦ᵣ (5 : Word)) ** (.x11 ↦ᵣ (5 : Word))) := by
  have h := secfSquareModNFlat_spec 5 9
  rw [show (GuestAddrs.secf_mul_mod_n : Word) = (0x8001f5b8 : Word) from by decide] at h
  exact h

example : GuestAddrs.secf_mul_mod_n ≠ GuestAddrs.secf_mul_mod_p := by decide

/-! ## 6. `rlp_walk_next_nested` — a pure alias (one instruction)

  A single `j rlp_walk_next_shared`.  The contract pins the transfer target
  and that the ABI registers survive it untouched — the whole content of
  the routine. -/

/-- `rlp_walk_next_nested` at a free `base`: one jump, no state change. -/
theorem rlpWalkNextNested_body_spec (base tgt ra a0 a1 a2 : Word)
    (hjal : base +
        signExtend21 (jalOff GuestAddrs.rlp_walk_next_shared
          (GuestAddrs.rlp_walk_next_nested + 0)) = tgt) :
    cpsTripleWithin 1 base tgt
      (CodeReq.ofProg base rlpWalkNextNested_prog)
      ((.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2))
      ((.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2)) := by
  -- Rule 1 of the module header: present the code requirement as the
  -- `singleton`-union chain before `runBlock`.
  unfold rlpWalkNextNested_prog
  rw [CodeReq.ofProg_cons,
    CodeReq.ofProg_nil]
  have J := jal_x0_frame_within
    ((.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2))
    Assertion.PCFree.proof
    (jalOff GuestAddrs.rlp_walk_next_shared (GuestAddrs.rlp_walk_next_nested + 0)) base
  rw [hjal] at J
  runBlock J

/-- `rlp_walk_next_nested` deployed contract, anchored at the guest image
    entry: it is exactly `rlp_walk_next_shared` reached with the ABI
    registers intact. -/
theorem rlpWalkNextNestedFlat_spec (ra a0 a1 a2 : Word) :
    cpsTripleWithin 1 (GuestAddrs.rlp_walk_next_nested : Word)
      (GuestAddrs.rlp_walk_next_shared : Word)
      (CodeReq.ofProg (GuestAddrs.rlp_walk_next_nested : Word) rlpWalkNextNested_prog)
      ((.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2))
      ((.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2)) :=
  rlpWalkNextNested_body_spec (GuestAddrs.rlp_walk_next_nested : Word)
    (GuestAddrs.rlp_walk_next_shared : Word) ra a0 a1 a2 (by decide)

/-- **Anti-vacuity witness** for `rlpWalkNextNestedFlat_spec`: the ABI registers
    keep their concrete incoming values `1, 2, 3` across a transfer to the
    concrete pc `0x8000524c`. -/
example :
    cpsTripleWithin 1 (GuestAddrs.rlp_walk_next_nested : Word) (0x8000524c : Word)
      (CodeReq.ofProg (GuestAddrs.rlp_walk_next_nested : Word) rlpWalkNextNested_prog)
      ((.x1 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ (2 : Word)) **
       (.x12 ↦ᵣ (3 : Word)))
      ((.x1 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ (2 : Word)) **
       (.x12 ↦ᵣ (3 : Word))) := by
  have h := rlpWalkNextNestedFlat_spec 0 1 2 3
  rw [show (GuestAddrs.rlp_walk_next_shared : Word) = (0x8000524c : Word) from by decide] at h
  exact h

/-- The alias's target is the very next instruction address, i.e. the `j` is a
    real 4-byte forward transfer out of a 1-instruction routine. -/
example : GuestAddrs.rlp_walk_next_shared = GuestAddrs.rlp_walk_next_nested + 4 := by decide

/-! ## 7-8. `derive_withdrawal_requests` / `derive_consolidation_requests`

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

/-- **Anti-vacuity witness** for §7: at `a0..a3 = 1,2,3,4` the post is fully
    concrete — `a0 = 0xa0b00d88` (the withdrawal predeploy address),
    `a1..a4 = 1,2,3,4` — with the exit at the concrete `0x80053224`. -/
example :
    cpsTripleWithin 7 (GuestAddrs.derive_withdrawal_requests : Word) (0x80053224 : Word)
      (CodeReq.ofProg (GuestAddrs.derive_withdrawal_requests : Word)
        deriveWithdrawalRequests_prog)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** (.x12 ↦ᵣ (3 : Word)) **
       (.x13 ↦ᵣ (4 : Word)) ** (.x14 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0xa0b00d88 : Word)) ** (.x11 ↦ᵣ (1 : Word)) ** (.x12 ↦ᵣ (2 : Word)) **
       (.x13 ↦ᵣ (3 : Word)) ** (.x14 ↦ᵣ (4 : Word))) := by
  have h := deriveWithdrawalRequestsFlat_spec 1 2 3 4 0
  rw [show (GuestAddrs.withdrawal_request_predeploy_addr : Word) = (0xa0b00d88 : Word)
      from by decide,
    show (GuestAddrs.stage_system_call : Word) = (0x80053224 : Word) from by decide] at h
  exact h

/-- **Anti-vacuity witness** for §8: the same shuffle but `a0 = 0xa0b00da0` (the
    consolidation predeploy address). -/
example :
    cpsTripleWithin 7 (GuestAddrs.derive_consolidation_requests : Word) (0x80053224 : Word)
      (CodeReq.ofProg (GuestAddrs.derive_consolidation_requests : Word)
        deriveConsolidationRequests_prog)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** (.x12 ↦ᵣ (3 : Word)) **
       (.x13 ↦ᵣ (4 : Word)) ** (.x14 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0xa0b00da0 : Word)) ** (.x11 ↦ᵣ (1 : Word)) ** (.x12 ↦ᵣ (2 : Word)) **
       (.x13 ↦ᵣ (3 : Word)) ** (.x14 ↦ᵣ (4 : Word))) := by
  have h := deriveConsolidationRequestsFlat_spec 1 2 3 4 0
  rw [show (GuestAddrs.consolidation_request_predeploy_addr : Word) = (0xa0b00da0 : Word)
      from by decide,
    show (GuestAddrs.stage_system_call : Word) = (0x80053224 : Word) from by decide] at h
  exact h

/-- The two routines materialize DIFFERENT predeploy addresses into `a0` and both
    land on the same `stage_system_call` entry — so neither post is satisfiable by
    the other's, and the shared exit is a real address, not a fallthrough. -/
example : GuestAddrs.withdrawal_request_predeploy_addr ≠
      GuestAddrs.consolidation_request_predeploy_addr ∧
    GuestAddrs.stage_system_call ≠ GuestAddrs.derive_withdrawal_requests + 28 ∧
    GuestAddrs.stage_system_call ≠ GuestAddrs.derive_consolidation_requests + 28 :=
  ⟨by decide, by decide, by decide⟩

/-! ## Axiom audit — every contract is classical-only. -/

#print axioms wcidxRecordPtrFlat_spec
#print axioms writeSetsDiscardTxFlat_spec
#print axioms readSetsDiscardTxFlat_spec
#print axioms secfSquareModPFlat_spec
#print axioms secfSquareModNFlat_spec
#print axioms rlpWalkNextNestedFlat_spec
#print axioms deriveWithdrawalRequestsFlat_spec
#print axioms deriveConsolidationRequestsFlat_spec

end EvmAsm.Codegen.Proofs
