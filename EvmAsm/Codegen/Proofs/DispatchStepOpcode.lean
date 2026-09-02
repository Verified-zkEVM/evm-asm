/-
  EvmAsm.Codegen.Proofs.DispatchStepOpcode

  **The opcode half of the dispatch step** (GH #13173, obligation 4): the
  `opcode_handlers` table load and the indirect `jalr` whose target is a
  LOADED value, as a machine triple at its linked address.

  ## What #13224 left

  `Proofs/DispatchStepGas.lean` proved indices 6..10 of
  `dispatchLoopBody_prog` — the M30 gas debit and its out-of-gas exit.  The
  residue is the fetch, the two `.data` table loads and the dispatch:

      idx 11  (+44)   auipc x6, %pcrel_hi(opcode_handlers)
      idx 12  (+48)   addi  x6, x6, %pcrel_lo(...)
      idx 13  (+52)   add   x6, x6, x5          -- x5 = op * 8
      idx 14  (+56)   ld    x7, 0(x6)           -- x7 := handlers[op]
      idx 15  (+60)   jalr  x1, 0(x7)           -- EXIT PC IS A LOADED VALUE

  ## A computed exit PC needs no new rule

  `cpsTripleWithin n entry exit cr P Q` takes `exit : Word` as a *term*, so an
  exit that is a function of the state is expressible as soon as the value is
  named in the precondition.  `jalr_spec_within` already exposes it:
  its exit is `(v1 + signExtend12 offset) &&& ~~~1` where `v1` is `rs1`'s
  value, a parameter.  So the dispatch step is stated by making the loaded
  handler address a parameter of the family and letting the exit mention it —
  `dispatchStep_opcode_within` below is `cpsTripleWithin 5` with exit
  `entries[op]`.  There is no new CPS rule to build and none was built.

  ## The `execBlock` → CPS bridge was already built, and it does not fit here

  `Proofs/OpcodeTables.lean` proves the same table load on the SAsm
  `execBlock`/`Region` engine (`exec_table_load`).  A general bridge from that
  engine into this one **already exists** and was not the cost anyone expected:
  `SAsm/BlockSound.lean`'s `execBlock_sound`, its PC-threaded sibling
  `SAsm/GlobalData.lean`'s `execBlockAt_sound` (which is the one that can step
  an `AUIPC` — `blockOk` rejects `AUIPC`, `blockOkAt` accepts it), and the
  atom-granularity `SAsm/BlockAtBridge.lean`'s `blockAt_flat_spec` all turn an
  `execBlock` run into a `cpsTripleWithin`.

  ⛔ **They cannot be used on this block, for a reason of register scope, not
  of engine mismatch.**  Their register currency is `regFileIs` /
  `regAtoms rf exposedRegs`, and `SAsm/RegFile.lean`'s `exposedRegs` is
  `[x5..x7, x28..x31, x10..x17]` — fifteen registers, containing neither `x1`
  nor `x20`.  The dispatch body writes `x1` (the `jalr`'s link register) and
  reads `x20` (the environment pointer for the gas debit), so no
  `execBlock`-side statement can even *mention* the two registers that make
  this block a dispatch.  `regs_not_exposed_here` states that as a theorem.
  The route taken below is therefore the `↦ᵣ`-atom one, instruction by
  instruction, which has no such restriction.

  What DOES port from `OpcodeTables` is its *table image*, `tableBytes`.
  `tableRegion_dword_at` below is that bridge: a `bytesRegion` pinned to
  `tableBytes entries` splits into the `op`-th dword atom and a frame, so the
  two files agree on what "the table is at this address" means while each
  engine reads it its own way.  It is four lines, because
  `bytesRegion_dword_at` (the dependency) and `tableBytes_slice`
  (`OpcodeTables`) already exist and meet exactly.

  ⚠️ What does **not** exist, in either engine, is a Lean statement that the
  shipped image's `.data` at `opcode_handlers` HOLDS `opcodeHandlerEntries`.
  `guestScratch` (`Proofs/GuestImage.lean`) owns the `.data` tile as
  `anyBytes` — havoc'd contents — and `scripts/check-opcode-tables.sh` checks
  the ELF bytes offline.  So the table's *contents* enter both this file and
  `OpcodeTables` as a hypothesis, and the `.data` counterpart of
  `guestImageCodeReq` is the missing piece.  See
  `opcode_table_contents_not_scratch_determined`, which states that gap as a
  theorem.

  ## Non-vacuity

  `dispatchStep_opcode_instance` instantiates the family at the real
  `opcodeHandlerEntries` mirror for ADD (`0x01`) under a concrete resolver,
  and separately witnesses that the table's indexed cell is an addressable
  aligned dword.  `dispatchStep_opcode_premises_refutable` is the negative
  control: three hypotheses each provably FALSE at a concrete point.
-/
import EvmAsm.Codegen.Proofs.DispatchStepGas
import EvmAsm.Codegen.Proofs.OpcodeTables
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.MemRegion

namespace EvmAsm.Codegen.DispatchStepOpcode

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.DispatchStepGas
open EvmAsm.Codegen.Proofs.OpcodeTables

/-- The `opcode_handlers` table base, as a machine word.  Read from
    `GuestAddrs`, never spelled. -/
abbrev HT : Word := BitVec.ofNat 64 GuestAddrs.opcode_handlers

/-- The `opcode_gas_costs` table base, as a machine word. -/
abbrev GT : Word := BitVec.ofNat 64 GuestAddrs.opcode_gas_costs

/-! ### Layout cross-checks, derived from the symbol table

    The two tables are 256 dwords each and adjacent; both facts come out of
    `GuestAddrs`, not out of prose, and both are what makes an `op`-indexed
    `↦ₘ` atom inside the `opcode_handlers` tile an addressable dword. -/

/-- `opcode_gas_costs` is exactly `8 * 256` bytes below `opcode_handlers`, and
    both are dword-aligned.  `8 * 256` is `tableBytes`' length at 256 entries,
    so this is the `prog.length * 4`-style extent cross-check for a table. -/
theorem opcode_tables_adjacent :
    GuestAddrs.opcode_handlers - GuestAddrs.opcode_gas_costs = 8 * 256
    ∧ GuestAddrs.opcode_gas_costs % 8 = 0
    ∧ GuestAddrs.opcode_handlers % 8 = 0 := by decide

/-- **Why the ready-made `execBlock` → CPS bridge cannot carry this block.**

    `execBlock_sound` / `execBlockAt_sound` / `blockAt_flat_spec` all state
    their register side as `regFileIs rf` or `regAtoms rf exposedRegs`, and
    `regFileIs rf = regAtoms rf exposedRegs` (`SAsm/FnFlat.lean`).  So a triple
    obtained through any of them constrains exactly `exposedRegs` and nothing
    else.  The dispatch body's link register `x1` and environment pointer
    `x20` are not in that list, so the bridge is not merely inconvenient here —
    it is not expressive enough, and no amount of framing recovers `x1`.

    This is why `dispatchStep_opcode_within` below is built from the
    `↦ᵣ`-atom one-step specs instead, and why doing so is not a missed reuse.
    Third conjunct: the exposed set is nonempty at the registers this block
    *does* share with it, so the point is scope, not a broken predicate. -/
theorem regs_not_exposed_here :
    Reg.isExposed .x1 = false ∧ Reg.isExposed .x20 = false
    ∧ Reg.isExposed .x5 = true ∧ Reg.isExposed .x6 = true
    ∧ Reg.isExposed .x7 = true := by decide

/-! ### The bridge: `OpcodeTables`' table image, as a CPS separation atom -/

/-- **`execBlock`-side table image ↦ CPS-side indexed dword atom.**

    `OpcodeTables.tableBytes entries` is the little-endian dword image of a
    `List Word` table.  On the SAsm engine it is consumed through
    `tableAt`/`Region.dwordAt`; here the same image pins a `bytesRegion`, and
    this lemma reads the `op`-th cell out of it as the `↦ₘ` atom that
    `ld_spec_gen_within` wants, framing the rest of the table.

    This is the whole of the `execBlock` → CPS bridge for a table load: the
    engines share the *image* (`tableBytes`), not the load lemma. -/
theorem tableRegion_dword_at (tableBase : Word) (entries : List Word) (op : Nat)
    (hop : op < entries.length) :
    ∃ front rest : Assertion, front.pcFree ∧ rest.pcFree ∧
      bytesRegion tableBase (tableBytes entries)
        = (front ** (((tableBase + BitVec.ofNat 64 (8 * op)) ↦ₘ entries[op])
            ** rest)) := by
  have hlen : 8 * op < (tableBytes entries).length := by
    rw [length_tableBytes]; omega
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegion_dword_at tableBase (tableBytes entries) op hlen
  exact ⟨front, rest, hf, hr, by
    rw [heq, tableBytes_slice entries op hop, packBytes_dwordBytes]⟩

/-- `bytesRegion` over a table image is `pcFree` — needed to frame the table
    across the neighbouring register steps. -/
theorem tableRegion_pcFree (tableBase : Word) (entries : List Word) :
    (bytesRegion tableBase (tableBytes entries)).pcFree :=
  bytesRegion_pcFree _ _

/-! ### The `la` immediates, reconciled between the two spellings

    `dispatchLoopBody_prog` carries `Codegen.laHi`/`Codegen.laLo` (Nat symbol,
    Nat pc — the assembler's view); `la_materialize_within` is stated over
    `Rv64.laHi`/`Rv64.laLo` (Word pc, Word target — the psABI arithmetic that
    `la_resolve` proves).  These three `decide`s are the reconciliation, and
    they read both addresses out of `GuestAddrs`. -/

private theorem hi_handlers :
    Codegen.laHi GuestAddrs.opcode_handlers (GuestAddrs.dispatch_loop_body + 44)
      = Rv64.laHi (B + 44) HT := by decide

private theorem lo_handlers :
    Codegen.laLo GuestAddrs.opcode_handlers (GuestAddrs.dispatch_loop_body + 44)
      = Rv64.laLo (B + 44) HT := by decide

private theorem range_handlers : laInRange (B + 44) HT := by decide

set_option maxRecDepth 8000

/-- **The dispatch step's opcode half** (#13173, obligation 4): indices 11..15
    of the shipped dispatcher loop body, at their linked addresses.

    With the scaled opcode `8 * op` in `x5` (put there by index 1's
    `slli x5, x5, 3`, and untouched by the gas debit) and the
    `opcode_handlers` table pinned at its linked base, the five instructions
    materialize the table address, index it, load the handler, and jump to it.

    ⭐ **The exit PC is a loaded value, and that needs no new rule.**
    `cpsTripleWithin`'s exit is a `Word`-valued *term*, and
    `jalr_spec_within`'s is already `(v1 + signExtend12 offset) &&& ~~~1` over
    `rs1`'s value.  Naming the loaded handler `entries[op]` in the
    precondition is therefore enough to name it in the exit: this family is
    **indexed by the opcode**, one triple per `op`, each with its own exit.
    `halign` is the standard `jalr` alignment side-condition (`Fn.jalr_ret_spec`
    carries the same one); every entry of the shipped table is a 4-aligned
    label address, so it is discharged by `decide` at any concrete table.

    `x1` is left holding `B + 64` — which is `GuestAddrs.dispatch_resume`, the
    loop's own resume label (`dispatchLoopBody_abuts_dispatchResume`), so the
    handler's `ret` comes back into the loop.  That is stated, not remarked:
    see `dispatch_ra_is_resume`.

    The table's CONTENTS are a hypothesis (`entries`), not a fact about the
    shipped image — see `dispatchStep_opcode_data_gap`. -/
theorem dispatchStep_opcode_within (op : Nat) (entries : List Word)
    (hop : op < entries.length)
    (halign : (entries[op] &&& ~~~(1 : Word)) = entries[op])
    (old1 old6 old7 : Word) :
    cpsTripleWithin 5 (B + 44) entries[op] dlbCode
      ((((.x6 : Reg) ↦ᵣ old6) ** ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * op))
          ** ((.x7 : Reg) ↦ᵣ old7) ** ((.x1 : Reg) ↦ᵣ old1))
        ** bytesRegion HT (tableBytes entries))
      ((((.x6 : Reg) ↦ᵣ (HT + BitVec.ofNat 64 (8 * op)))
          ** ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * op))
          ** ((.x7 : Reg) ↦ᵣ entries[op]) ** ((.x1 : Reg) ↦ᵣ (B + 64)))
        ** bytesRegion HT (tableBytes entries)) := by
  obtain ⟨front, rest, hf, hr, heq⟩ := tableRegion_dword_at HT entries op hop
  -- idx 11,12 (+44,+48): la x6, opcode_handlers.
  have hla := la_materialize_within (cr := dlbCode) .x6 old6 (B + 44) HT
    (by decide) range_handlers
    (by rw [← hi_handlers]; code_mem)
    (by rw [← lo_handlers]; code_mem)
  rw [show (B + 44 : Word) + 8 = B + 52 from by decide] at hla
  have hlaF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * op)) ** ((.x7 : Reg) ↦ᵣ old7)
      ** ((.x1 : Reg) ↦ᵣ old1) ** front
      ** (((HT + BitVec.ofNat 64 (8 * op)) ↦ₘ entries[op]) ** rest))
    (by repeat' first
        | assumption
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) hla
  -- idx 13 (+52): add x6, x6, x5.
  have hadd := add_spec_gen_rd_eq_rs1_within .x6 .x5 HT
    (BitVec.ofNat 64 (8 * op)) (B + 52) (by decide)
  rw [show (B + 52 : Word) + 4 = B + 56 from by decide] at hadd
  have haddF := liftCode (cr' := dlbCode)
    (cpsTripleWithin_frameR
      (((.x7 : Reg) ↦ᵣ old7) ** ((.x1 : Reg) ↦ᵣ old1) ** front
        ** (((HT + BitVec.ofNat 64 (8 * op)) ↦ₘ entries[op]) ** rest))
      (by repeat' first
        | assumption
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) hadd) (by code_mem)
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hlaF haddF
  -- idx 14 (+56): ld x7, 0(x6) — the handler-table read.
  have hld := ld_spec_gen_within .x7 .x6 (HT + BitVec.ofNat 64 (8 * op)) old7
    entries[op] (0 : BitVec 12) (B + 56) (by decide)
  rw [show (HT + BitVec.ofNat 64 (8 * op)) + signExtend12 (0 : BitVec 12)
        = HT + BitVec.ofNat 64 (8 * op) from by
        show _ + (0 : Word) = _; bv_omega,
      show (B + 56 : Word) + 4 = B + 60 from by decide] at hld
  have hldF := liftCode (cr' := dlbCode)
    (cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * op)) ** ((.x1 : Reg) ↦ᵣ old1)
        ** front ** rest)
      (by repeat' first
        | assumption
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) hld) (by code_mem)
  have h13 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    h12 hldF
  -- idx 15 (+60): jalr x1, 0(x7) — the exit PC is the loaded value.
  have hjalr := jalr_spec_within .x1 .x7 entries[op] old1 (0 : BitVec 12)
    (B + 60) (by decide)
  rw [show entries[op] + signExtend12 (0 : BitVec 12) = entries[op] from by
        show _ + (0 : Word) = _; bv_omega,
      halign, show (B + 60 : Word) + 4 = B + 64 from by decide] at hjalr
  have hjalrF := liftCode (cr' := dlbCode)
    (cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * op))
        ** ((.x6 : Reg) ↦ᵣ (HT + BitVec.ofNat 64 (8 * op)))
        ** front ** (((HT + BitVec.ofNat 64 (8 * op)) ↦ₘ entries[op]) ** rest))
      (by repeat' first
        | assumption
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) hjalr) (by code_mem)
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    h13 hjalrF
  rw [heq]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-- **The same statement inside the whole-image `CodeReq`**, through
    `dispatchLoopBody_block_sub` — the #13178 anchor, spent a second time. -/
theorem dispatchStep_opcode_image (op : Nat) (entries : List Word)
    (hop : op < entries.length)
    (halign : (entries[op] &&& ~~~(1 : Word)) = entries[op])
    (old1 old6 old7 : Word) :
    cpsTripleWithin 5 (B + 44) entries[op] guestImageCodeReq
      ((((.x6 : Reg) ↦ᵣ old6) ** ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * op))
          ** ((.x7 : Reg) ↦ᵣ old7) ** ((.x1 : Reg) ↦ᵣ old1))
        ** bytesRegion HT (tableBytes entries))
      ((((.x6 : Reg) ↦ᵣ (HT + BitVec.ofNat 64 (8 * op)))
          ** ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * op))
          ** ((.x7 : Reg) ↦ᵣ entries[op]) ** ((.x1 : Reg) ↦ᵣ (B + 64)))
        ** bytesRegion HT (tableBytes entries)) :=
  cpsTripleWithin_extend_code dispatchLoopBody_block_sub
    (dispatchStep_opcode_within op entries hop halign old1 old6 old7)

/-- **The link register the dispatch leaves behind is the loop's own resume
    label.**  `B + 64` is `4 * 16` past the body's entry, which
    `dispatchLoopBody_abuts_dispatchResume` already pins to
    `GuestAddrs.dispatch_resume`.  So the `jalr x1` above is a CALL back into
    the loop, not a tail jump: the handler's `ret` re-enters at
    `.dispatch_resume`.  Stated, rather than remarked. -/
theorem dispatch_ra_is_resume :
    (B + 64 : Word) = BitVec.ofNat 64 GuestAddrs.dispatch_resume := by decide

/-! ### The `.data` gap this triple cannot close -/

/-- **The shipped image does not pin the table's contents, and that is a
    theorem, not an opinion.**

    `guestScratch` (`Proofs/GuestImage.lean`) owns the writable `.data` tile —
    which is where `opcode_handlers` lives — as `regionScratch`, i.e.
    `anyBytes`: ownership with contents FORGOTTEN.  The third conjunct is the
    havoc weakening that makes that so, and the first two exhibit two distinct
    table images of equal length, so a heap satisfying the `.data` tile's
    `anyBytes` may hold either.  No `↦ₘ` atom about `HT` follows from
    `guestScratch`, and therefore `dispatchStep_opcode_within`'s
    `bytesRegion HT (tableBytes entries)` premise cannot be discharged from the
    image assertion as it stands — it must come from a `.data` counterpart of
    `guestImageCodeReq`, which does not exist.

    ⛔ This is the honest boundary of obligation 4's opcode half: the control
    flow is proven for every opcode, and *which* handler each opcode reaches is
    still parameterized by the caller's table.  `scripts/check-opcode-tables.sh`
    checks the shipped bytes offline; nothing in Lean does. -/
theorem opcode_table_contents_not_scratch_determined :
    tableBytes [(0 : Word)] ≠ tableBytes [(1 : Word)]
    ∧ (tableBytes [(0 : Word)]).length = (tableBytes [(1 : Word)]).length
    ∧ (∀ (bs : List (BitVec 8)) (h : PartialState),
        bytesRegion HT bs h → anyBytes HT bs.length h) :=
  ⟨by decide, by decide, fun bs h hb => bytesRegion_anyBytes HT bs h hb⟩

/-! ### Non-vacuity -/

/-- A concrete, non-degenerate handler-address resolver: distinct 4-aligned
    addresses derived from the label text.  It is NOT the linker's resolver —
    no such resolver exists in Lean (that is
    `opcode_table_contents_not_scratch_determined`) — but it is a legitimate
    one, and it makes the instance below a statement about 256 different
    handler entries rather than about one repeated address. -/
def demoResolver : String → Word :=
  fun s => BitVec.ofNat 64 (GuestAddrs.dispatch_resume + 4 * s.length)

/-- **Satisfiable instance.**  The whole family, instantiated at the real
    `opcodeHandlerEntries` mirror of the SHIPPED `callFrameGuestRegistry` for
    opcode `0x01` (ADD), under `demoResolver`.  The remaining conjuncts
    witness that none of the premises is vacuous at that point: the table is
    256 entries, the indexed cell is an addressable aligned dword, and the
    entry really is 2-aligned so the `jalr` exit is the loaded value itself. -/
theorem dispatchStep_opcode_instance :
    (∀ old1 old6 old7 : Word,
      cpsTripleWithin 5 (B + 44)
        ((opcodeHandlerEntries demoResolver)[0x01]'(by simp))
        guestImageCodeReq
        ((((.x6 : Reg) ↦ᵣ old6) ** ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * 0x01))
            ** ((.x7 : Reg) ↦ᵣ old7) ** ((.x1 : Reg) ↦ᵣ old1))
          ** bytesRegion HT (tableBytes (opcodeHandlerEntries demoResolver)))
        ((((.x6 : Reg) ↦ᵣ (HT + BitVec.ofNat 64 (8 * 0x01)))
            ** ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * 0x01))
            ** ((.x7 : Reg) ↦ᵣ ((opcodeHandlerEntries demoResolver)[0x01]'(by simp)))
            ** ((.x1 : Reg) ↦ᵣ (B + 64)))
          ** bytesRegion HT (tableBytes (opcodeHandlerEntries demoResolver))))
    ∧ (opcodeHandlerEntries demoResolver).length = 256
    ∧ isValidDwordAccess (HT + BitVec.ofNat 64 (8 * 0x01)) = true
    ∧ (((opcodeHandlerEntries demoResolver)[0x01]'(by simp)) &&& ~~~(1 : Word))
        = ((opcodeHandlerEntries demoResolver)[0x01]'(by simp)) := by
  refine ⟨fun old1 old6 old7 => dispatchStep_opcode_image 0x01 _ (by simp) ?_
      old1 old6 old7, by simp, by decide, ?_⟩ <;>
    · simp only [opcodeHandlerEntries, opcodeHandlerLabels]
      decide

set_option maxRecDepth 40000 in
/-- **Negative control.**  Three hypotheses of the family above, each provably
    FALSE at a concrete point.

    1. **The `la` is at +44, not +40.**  The code premise really pins an index:
       one instruction earlier `dlbCode` answers with the gas debit's `sd`, so
       an off-by-one anchoring of this triple would be UNSUPPORTED, not merely
       weaker (`cpsTripleWithin_needs_entry_code`).
    2. **The `jalr` alignment premise discriminates.**  At an ODD handler
       address the exit is not the loaded value — `jalr` clears bit 0 — so
       `halign` is doing work and is not decoration.
    3. **The index premise is not free.**  A 256-entry table does not admit
       `op = 256`, so `hop` is what stops the family from claiming a 257th
       opcode. -/
theorem dispatchStep_opcode_premises_refutable :
    dlbCode (B + 40) ≠ some (.AUIPC .x6
        (Codegen.laHi GuestAddrs.opcode_handlers
          (GuestAddrs.dispatch_loop_body + 44)))
    ∧ ¬ (((3 : Word) &&& ~~~(1 : Word)) = (3 : Word))
    ∧ ¬ (256 < (opcodeHandlerEntries demoResolver).length) := by
  refine ⟨by decide, by decide, ?_⟩
  rw [length_opcodeHandlerEntries]
  omega

end EvmAsm.Codegen.DispatchStepOpcode
