/-
  EvmAsm.Codegen.Proofs.DispatchStepOpcode

  **The opcode half of the dispatch step, and with it the whole dispatch
  step** (GH #13173, obligation 4): the opcode fetch, both `.data` table
  loads, and the indirect `jalr` whose target is a LOADED value — as machine
  triples at their linked addresses.

  ## What #13224 left

  `Proofs/DispatchStepGas.lean` proved indices 6..10 of
  `dispatchLoopBody_prog` — the M30 gas debit and its out-of-gas exit.  The
  residue was everything on either side of it:

      idx  0  (+0)    lbu   x5, 0(x10)          -- x5 := code[pc], THE OPCODE
      idx  1  (+4)    slli  x5, x5, 3
      idx  2  (+8)    auipc x6, %pcrel_hi(opcode_gas_costs)
      idx  3  (+12)   addi  x6, x6, %pcrel_lo(...)
      idx  4  (+16)   add   x6, x6, x5
      idx  5  (+20)   ld    x6, 0(x6)           -- x6 := gasCosts[op]
      ... idx 6..10: the gas debit, #13224 ...
      idx 11  (+44)   auipc x6, %pcrel_hi(opcode_handlers)
      idx 12  (+48)   addi  x6, x6, %pcrel_lo(...)
      idx 13  (+52)   add   x6, x6, x5          -- x5 = op * 8, still
      idx 14  (+56)   ld    x7, 0(x6)           -- x7 := handlers[op]
      idx 15  (+60)   jalr  x1, 0(x7)           -- EXIT PC IS A LOADED VALUE

  Three theorems: `dispatchStep_fetch_within` (0..5),
  `dispatchStep_opcode_within` (11..15), and `dispatchStep_body_within`, which
  composes those two around #13224's branch into a **`cpsBranchWithin 16` over
  the whole sixteen-instruction body**, indexed by the fetched opcode.  `op` is
  `code[i]` — a projection of the code region, not a parameter — so the body
  theorem is one statement covering all 256 opcodes.

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
import EvmAsm.Codegen.Proofs.GuestDataImage
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

/-! ### The other half of the opcode work: fetch and the gas-cost table load

    Indices 0..5, the mirror image of 11..15 with a byte fetch in front of it:

        idx 0  (+0)   lbu   x5, 0(x10)              -- x5 := code[pc]
        idx 1  (+4)   slli  x5, x5, 3               -- x5 := op * 8
        idx 2  (+8)   auipc x6, %pcrel_hi(opcode_gas_costs)
        idx 3  (+12)  addi  x6, x6, %pcrel_lo(...)
        idx 4  (+16)  add   x6, x6, x5
        idx 5  (+20)  ld    x6, 0(x6)               -- x6 := gasCosts[op]

    Exit `+24` is exactly `dispatchStep_gasDebit_within`'s entry, and `x6` is
    exactly the `cost` that lemma left free. -/

private theorem hi_gascosts :
    Codegen.laHi GuestAddrs.opcode_gas_costs (GuestAddrs.dispatch_loop_body + 8)
      = Rv64.laHi (B + 8) GT := by decide

private theorem lo_gascosts :
    Codegen.laLo GuestAddrs.opcode_gas_costs (GuestAddrs.dispatch_loop_body + 8)
      = Rv64.laLo (B + 8) GT := by decide

private theorem range_gascosts : laInRange (B + 8) GT := by decide

/-- A zero-extended byte is the `Word` of its numeral — the step that turns
    `bytesRegion_lbu_within`'s `code[i].zeroExtend 64` into the `op`-indexed
    form the rest of the block wants. -/
private theorem byte_zeroExtend (b : BitVec 8) :
    b.zeroExtend 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq; simp

/-- **Fetch plus the gas-cost table load** (#13173, obligation 4): indices 0..5
    of the shipped dispatcher loop body.

    The opcode is `code[i]`, read out of the EVM bytecode region the loop's
    `x10` points into — so `op` is not a free parameter here, it is the byte
    the machine actually fetched.  Everything downstream is indexed by it:
    `x5` leaves holding `8 * op` (and survives the gas debit untouched, which
    is what lets `dispatchStep_opcode_within` reuse it eleven instructions
    later), and `x6` leaves holding `gasCosts[op]` — precisely the `cost` that
    `dispatchStep_gasDebit_within` takes as a free register.

    The exit `B + 24` is that lemma's entry, so these two compose with no
    interface to invent. -/
theorem dispatchStep_fetch_within (codeBase : Word) (code : List (BitVec 8))
    (i : Nat) (gasCosts : List Word) (old5 old6 : Word)
    (hi : i < code.length)
    (hbase : codeBase.toNat % 8 = 0)
    (hover : codeBase.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (codeBase + BitVec.ofNat 64 i) = true)
    (hop : (code[i]'hi).toNat < gasCosts.length) :
    cpsTripleWithin 6 B (B + 24) dlbCode
      (((((.x10 : Reg) ↦ᵣ (codeBase + BitVec.ofNat 64 i)) ** ((.x5 : Reg) ↦ᵣ old5)
          ** ((.x6 : Reg) ↦ᵣ old6)) ** bytesRegion codeBase code)
        ** bytesRegion GT (tableBytes gasCosts))
      (((((.x10 : Reg) ↦ᵣ (codeBase + BitVec.ofNat 64 i))
          ** ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * (code[i]'hi).toNat))
          ** ((.x6 : Reg) ↦ᵣ (gasCosts[(code[i]'hi).toNat]'hop)))
          ** bytesRegion codeBase code)
        ** bytesRegion GT (tableBytes gasCosts)) := by
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    tableRegion_dword_at GT gasCosts (code[i]'hi).toNat hop
  -- idx 0 (+0): lbu x5, 0(x10) — the opcode byte, out of the code region.
  have hlbu := bytesRegion_lbu_within .x5 .x10 codeBase old5 B code i
    (by decide) hbase hi hover hvalid
  rw [byte_zeroExtend] at hlbu
  have hlbuC := liftCode (cr' := dlbCode)
    (cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ old6) ** bytesRegion GT (tableBytes gasCosts))
      (by repeat' first
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) hlbu) (by code_mem)
  -- idx 1 (+4): slli x5, x5, 3.
  have hslli := slli_spec_gen_same_within .x5
    (BitVec.ofNat 64 (code[i]'hi).toNat) (3 : BitVec 6) (B + 4) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 from by decide,
      ofNat_shiftLeft_three (code[i]'hi).toNat,
      show (code[i]'hi).toNat * 8 = 8 * (code[i]'hi).toNat from by omega,
      show (B + 4 : Word) + 4 = B + 8 from by decide] at hslli
  have hslliC := liftCode (cr' := dlbCode)
    (cpsTripleWithin_frameR
      ((((.x10 : Reg) ↦ᵣ (codeBase + BitVec.ofNat 64 i)) ** ((.x6 : Reg) ↦ᵣ old6))
        ** bytesRegion codeBase code ** bytesRegion GT (tableBytes gasCosts))
      (by repeat' first
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) hslli) (by code_mem)
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hlbuC hslliC
  rw [heq] at h01
  -- idx 2,3 (+8,+12): la x6, opcode_gas_costs.
  have hla := la_materialize_within (cr := dlbCode) .x6 old6 (B + 8) GT
    (by decide) range_gascosts
    (by rw [← hi_gascosts]; code_mem)
    (by rw [← lo_gascosts]; code_mem)
  rw [show (B + 8 : Word) + 8 = B + 16 from by decide] at hla
  have hlaF := cpsTripleWithin_frameR
    ((((.x10 : Reg) ↦ᵣ (codeBase + BitVec.ofNat 64 i))
        ** ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * (code[i]'hi).toNat)))
      ** bytesRegion codeBase code
      ** front ** ((GT + BitVec.ofNat 64 (8 * (code[i]'hi).toNat))
          ↦ₘ (gasCosts[(code[i]'hi).toNat]'hop)) ** rest)
    (by repeat' first
      | assumption
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | apply pcFree_sepConj) hla
  -- idx 4 (+16): add x6, x6, x5.
  have hadd := add_spec_gen_rd_eq_rs1_within .x6 .x5 GT
    (BitVec.ofNat 64 (8 * (code[i]'hi).toNat)) (B + 16) (by decide)
  rw [show (B + 16 : Word) + 4 = B + 20 from by decide] at hadd
  have haddF := liftCode (cr' := dlbCode)
    (cpsTripleWithin_frameR
      ((((.x10 : Reg) ↦ᵣ (codeBase + BitVec.ofNat 64 i)))
        ** bytesRegion codeBase code
        ** front ** ((GT + BitVec.ofNat 64 (8 * (code[i]'hi).toNat))
            ↦ₘ (gasCosts[(code[i]'hi).toNat]'hop)) ** rest)
      (by repeat' first
        | assumption
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) hadd) (by code_mem)
  -- idx 5 (+20): ld x6, 0(x6) — the gas-cost table read.
  have hld := ld_spec_gen_same_within .x6
    (GT + BitVec.ofNat 64 (8 * (code[i]'hi).toNat))
    (gasCosts[(code[i]'hi).toNat]'hop) (0 : BitVec 12) (B + 20) (by decide)
  rw [show (GT + BitVec.ofNat 64 (8 * (code[i]'hi).toNat))
          + signExtend12 (0 : BitVec 12)
        = GT + BitVec.ofNat 64 (8 * (code[i]'hi).toNat) from by
        show _ + (0 : Word) = _; bv_omega,
      show (B + 20 : Word) + 4 = B + 24 from by decide] at hld
  have hldF := liftCode (cr' := dlbCode)
    (cpsTripleWithin_frameR
      ((((.x10 : Reg) ↦ᵣ (codeBase + BitVec.ofNat 64 i))
          ** ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * (code[i]'hi).toNat)))
        ** bytesRegion codeBase code ** front ** rest)
      (by repeat' first
        | assumption
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) hld) (by code_mem)
  have h234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hlaF haddF
  have h2345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    h234 hldF
  rw [heq]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 h2345)

/-! ### The whole sixteen-instruction body, indexed by the fetched opcode -/

/-- Sequence a triple onto the **taken** exit of a branch, with a permutation
    slot on the join.  The dependency has `_with_perm_` only for the
    fall-through side; this is that lemma conjugated by `cpsBranchWithin_swap`,
    exactly as `DispatchStepGas.seq_taken_same_cr` derives the perm-free
    version. -/
theorem seq_taken_perm_same_cr {n1 n2 : Nat} {entry mid target exit_f : Word}
    {cr : CodeReq} {P Q_t1 Q_f1 R Q_t2 : Assertion}
    (h1 : cpsBranchWithin n1 entry cr P mid Q_t1 exit_f Q_f1)
    (hperm : ∀ h, Q_t1 h → R h)
    (h2 : cpsTripleWithin n2 mid target cr R Q_t2) :
    cpsBranchWithin (n1 + n2) entry cr P target Q_t2 exit_f Q_f1 :=
  cpsBranchWithin_swap
    (cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
      (cpsBranchWithin_swap h1) hperm h2 (fun _ hp => hp))

set_option maxRecDepth 20000 in
/-- **One whole dispatch step of the shipped loop body, indexed by the opcode
    it fetched** (#13173, obligation 4, complete).

    All sixteen instructions of `dispatchLoopBody_prog`, from its linked entry
    `.dispatch_loop_body` to one of two exits:

    * **dispatch** — `handlers[op]`, a LOADED value, with `x1` holding
      `.dispatch_resume` so the handler returns into the loop, and
      `env+568` debited by `gasCosts[op]`;
    * **out of gas** — the linked `GuestAddrs.exit_outofgas`, with the gas cell
      UNCHANGED.

    `op` is `code[i]`, the byte the machine fetched through `x10`; it is not a
    parameter of the statement but a projection of the code region, so this is
    one theorem covering **all 256 opcodes** — the handler each reaches, and
    the gas each is charged, are read out of the two tables by index.

    Composed from `dispatchStep_fetch_within` (0..5),
    `DispatchStepGas.dispatchStep_gasDebit_within` (6..10, #13224) and
    `dispatchStep_opcode_within` (11..15); the step bound 16 is `6 + 5 + 5`,
    and no execution runs both halves of the relaxed `bltu` pair inside the
    middle factor.

    ⚠️ The two tables' CONTENTS are premises, not facts about the shipped
    image — `opcode_table_contents_not_scratch_determined`.  What is proven
    unconditionally is the *control flow and the indexing*: whatever the
    tables hold, this loop body charges the `op`-th gas entry and jumps to the
    `op`-th handler. -/
theorem dispatchStep_body_within (codeBase : Word) (code : List (BitVec 8))
    (i : Nat) (gasCosts handlers : List Word)
    (gp gas old1 old5 old6 old7 : Word)
    (hi : i < code.length)
    (hbase : codeBase.toNat % 8 = 0)
    (hover : codeBase.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (codeBase + BitVec.ofNat 64 i) = true)
    (hgc : (code[i]'hi).toNat < gasCosts.length)
    (hh : (code[i]'hi).toNat < handlers.length)
    (halign : ((handlers[(code[i]'hi).toNat]'hh) &&& ~~~(1 : Word))
      = handlers[(code[i]'hi).toNat]'hh) :
    cpsBranchWithin 16 B dlbCode
      (((.x1 : Reg) ↦ᵣ old1) ** ((.x5 : Reg) ↦ᵣ old5) ** ((.x6 : Reg) ↦ᵣ old6)
        ** ((.x7 : Reg) ↦ᵣ old7)
        ** ((.x10 : Reg) ↦ᵣ (codeBase + BitVec.ofNat 64 i))
        ** ((.x20 : Reg) ↦ᵣ gp) ** ((gp + 568) ↦ₘ gas)
        ** bytesRegion codeBase code ** bytesRegion GT (tableBytes gasCosts)
        ** bytesRegion HT (tableBytes handlers))
      (handlers[(code[i]'hi).toNat]'hh)
        (((.x1 : Reg) ↦ᵣ (B + 64))
          ** ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * (code[i]'hi).toNat))
          ** ((.x6 : Reg) ↦ᵣ (HT + BitVec.ofNat 64 (8 * (code[i]'hi).toNat)))
          ** ((.x7 : Reg) ↦ᵣ (handlers[(code[i]'hi).toNat]'hh))
          ** ((.x10 : Reg) ↦ᵣ (codeBase + BitVec.ofNat 64 i))
          ** ((.x20 : Reg) ↦ᵣ gp)
          ** ((gp + 568) ↦ₘ (gas - (gasCosts[(code[i]'hi).toNat]'hgc)))
          ** ⌜¬ BitVec.ult gas (gasCosts[(code[i]'hi).toNat]'hgc)⌝
          ** bytesRegion codeBase code ** bytesRegion GT (tableBytes gasCosts)
          ** bytesRegion HT (tableBytes handlers))
      (BitVec.ofNat 64 GuestAddrs.exit_outofgas)
        (((.x1 : Reg) ↦ᵣ old1)
          ** ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * (code[i]'hi).toNat))
          ** ((.x6 : Reg) ↦ᵣ (gasCosts[(code[i]'hi).toNat]'hgc))
          ** ((.x7 : Reg) ↦ᵣ gas)
          ** ((.x10 : Reg) ↦ᵣ (codeBase + BitVec.ofNat 64 i))
          ** ((.x20 : Reg) ↦ᵣ gp) ** ((gp + 568) ↦ₘ gas)
          ** ⌜BitVec.ult gas (gasCosts[(code[i]'hi).toNat]'hgc)⌝
          ** bytesRegion codeBase code ** bytesRegion GT (tableBytes gasCosts)
          ** bytesRegion HT (tableBytes handlers)) := by
  -- 0..5: fetch and the gas-cost table load.
  have hfetch := dispatchStep_fetch_within codeBase code i gasCosts old5 old6
    hi hbase hover hvalid hgc
  have hfetchF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ old1) ** ((.x7 : Reg) ↦ᵣ old7) ** ((.x20 : Reg) ↦ᵣ gp)
      ** ((gp + 568) ↦ₘ gas) ** bytesRegion HT (tableBytes handlers))
    (by repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | apply pcFree_sepConj) hfetch
  -- 6..10: the gas debit (#13224).
  have hgasF := cpsBranchWithin_frameR
    (((.x1 : Reg) ↦ᵣ old1)
      ** ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * (code[i]'hi).toNat))
      ** ((.x10 : Reg) ↦ᵣ (codeBase + BitVec.ofNat 64 i))
      ** bytesRegion codeBase code ** bytesRegion GT (tableBytes gasCosts)
      ** bytesRegion HT (tableBytes handlers))
    (by repeat' first
      | exact pcFree_regIs
      | exact bytesRegion_pcFree _ _
      | apply pcFree_sepConj)
    (dispatchStep_gasDebit_within gp (gasCosts[(code[i]'hi).toNat]'hgc) gas old7)
  have h010 := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hfetchF hgasF
  -- 11..15: the handler-table load and the indirect jump.
  have hopF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (codeBase + BitVec.ofNat 64 i))
      ** bytesRegion codeBase code ** ((.x20 : Reg) ↦ᵣ gp)
      ** ((gp + 568) ↦ₘ (gas - (gasCosts[(code[i]'hi).toNat]'hgc)))
      ** ⌜¬ BitVec.ult gas (gasCosts[(code[i]'hi).toNat]'hgc)⌝
      ** bytesRegion GT (tableBytes gasCosts))
    (by repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _
      | apply pcFree_sepConj)
    (dispatchStep_opcode_within (code[i]'hi).toNat handlers hh halign old1
      (gasCosts[(code[i]'hi).toNat]'hgc)
      (gas - (gasCosts[(code[i]'hi).toNat]'hgc)))
  exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) (fun _ hq => by xperm_hyp hq)
    (seq_taken_perm_same_cr h010 (fun _ hp => by xperm_hyp hp) hopF)

/-- **The whole dispatch step inside the image `CodeReq`.** -/
theorem dispatchStep_body_image (codeBase : Word) (code : List (BitVec 8))
    (i : Nat) (gasCosts handlers : List Word)
    (gp gas old1 old5 old6 old7 : Word)
    (hi : i < code.length)
    (hbase : codeBase.toNat % 8 = 0)
    (hover : codeBase.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (codeBase + BitVec.ofNat 64 i) = true)
    (hgc : (code[i]'hi).toNat < gasCosts.length)
    (hh : (code[i]'hi).toNat < handlers.length)
    (halign : ((handlers[(code[i]'hi).toNat]'hh) &&& ~~~(1 : Word))
      = handlers[(code[i]'hi).toNat]'hh) :
    cpsBranchWithin 16 B guestImageCodeReq
      (((.x1 : Reg) ↦ᵣ old1) ** ((.x5 : Reg) ↦ᵣ old5) ** ((.x6 : Reg) ↦ᵣ old6)
        ** ((.x7 : Reg) ↦ᵣ old7)
        ** ((.x10 : Reg) ↦ᵣ (codeBase + BitVec.ofNat 64 i))
        ** ((.x20 : Reg) ↦ᵣ gp) ** ((gp + 568) ↦ₘ gas)
        ** bytesRegion codeBase code ** bytesRegion GT (tableBytes gasCosts)
        ** bytesRegion HT (tableBytes handlers))
      (handlers[(code[i]'hi).toNat]'hh)
        (((.x1 : Reg) ↦ᵣ (B + 64))
          ** ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * (code[i]'hi).toNat))
          ** ((.x6 : Reg) ↦ᵣ (HT + BitVec.ofNat 64 (8 * (code[i]'hi).toNat)))
          ** ((.x7 : Reg) ↦ᵣ (handlers[(code[i]'hi).toNat]'hh))
          ** ((.x10 : Reg) ↦ᵣ (codeBase + BitVec.ofNat 64 i))
          ** ((.x20 : Reg) ↦ᵣ gp)
          ** ((gp + 568) ↦ₘ (gas - (gasCosts[(code[i]'hi).toNat]'hgc)))
          ** ⌜¬ BitVec.ult gas (gasCosts[(code[i]'hi).toNat]'hgc)⌝
          ** bytesRegion codeBase code ** bytesRegion GT (tableBytes gasCosts)
          ** bytesRegion HT (tableBytes handlers))
      (BitVec.ofNat 64 GuestAddrs.exit_outofgas)
        (((.x1 : Reg) ↦ᵣ old1)
          ** ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * (code[i]'hi).toNat))
          ** ((.x6 : Reg) ↦ᵣ (gasCosts[(code[i]'hi).toNat]'hgc))
          ** ((.x7 : Reg) ↦ᵣ gas)
          ** ((.x10 : Reg) ↦ᵣ (codeBase + BitVec.ofNat 64 i))
          ** ((.x20 : Reg) ↦ᵣ gp) ** ((gp + 568) ↦ₘ gas)
          ** ⌜BitVec.ult gas (gasCosts[(code[i]'hi).toNat]'hgc)⌝
          ** bytesRegion codeBase code ** bytesRegion GT (tableBytes gasCosts)
          ** bytesRegion HT (tableBytes handlers)) :=
  cpsBranchWithin_extend_code dispatchLoopBody_block_sub
    (dispatchStep_body_within codeBase code i gasCosts handlers gp gas
      old1 old5 old6 old7 hi hbase hover hvalid hgc hh halign)

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

/-- A concrete EVM-code region for the whole-body witness: one byte, `0x01`
    (ADD), at a dword-aligned address inside the model's RAM zone. -/
def demoCodeBase : Word := BitVec.ofNat 64 0xa0c00000

/-- The one-byte code region read by `dispatchStep_body_premises_satisfiable`. -/
def demoCode : List (BitVec 8) := [(0x01 : BitVec 8)]

/-- **The whole-body theorem's premise bundle is simultaneously satisfiable.**

    All seven side conditions of `dispatchStep_body_within` hold at one
    concrete point — an aligned, in-range, one-byte code region whose byte is
    `0x01`, and the two 256-entry table mirrors.  So the hypothesis family is
    not contradictory, and the whole-body triple is not vacuously true for want
    of an instantiation.  (The conclusion is exhibited separately, at the
    opcode half, by `dispatchStep_opcode_instance`: writing the sixteen-
    instruction conclusion out again would restate it, not check it.) -/
theorem dispatchStep_body_premises_satisfiable :
    0 < demoCode.length
    ∧ demoCodeBase.toNat % 8 = 0
    ∧ demoCodeBase.toNat + 0 < 2 ^ 64
    ∧ isValidByteAccess (demoCodeBase + BitVec.ofNat 64 0) = true
    ∧ (demoCode[0]'(by decide)).toNat < opcodeGasCostEntries.length
    ∧ (demoCode[0]'(by decide)).toNat
        < (opcodeHandlerEntries demoResolver).length
    ∧ ((((opcodeHandlerEntries demoResolver)[(demoCode[0]'(by decide)).toNat]'(by
            simp [demoCode])) &&& ~~~(1 : Word))
        = ((opcodeHandlerEntries demoResolver)[(demoCode[0]'(by decide)).toNat]'(by
            simp [demoCode]))) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · rw [length_opcodeGasCostEntries]; decide
  · rw [length_opcodeHandlerEntries]; decide
  · simp only [demoCode, opcodeHandlerEntries, opcodeHandlerLabels]
    decide

/-- **Negative control for the whole-body premises.**  Two of the region
    side-conditions above, each provably FALSE at a concrete point: a
    misaligned code base, and a code pointer in the gap between the model's
    legacy zone and its RAM zone.  Neither is decoration —
    `bytesRegion_lbu_within` is unusable without both. -/
theorem dispatchStep_body_premises_refutable :
    ¬ ((demoCodeBase + 1).toNat % 8 = 0)
    ∧ isValidByteAccess (BitVec.ofNat 64 0x90000000) = false := by decide

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

/-! ### The shipped instantiation (GH #13229)

    Everything above is parametric in `gasCosts`/`handlers`: `dispatchStep_body_
    image` proves the control flow and the indexing for whatever the two tables
    hold, because until #13229 nothing in Lean could say what they DO hold —
    `opcode_table_contents_not_scratch_determined` is that gap as a theorem.

    `Proofs/GuestDataImage.lean` closes it.  `.data` is PROGBITS, so the loader
    copies its bytes in before `_start` exactly as it does `.text`; the two
    dispatch tables are pinned at their linked bases and `guestScratch` now
    carries them instead of havoc.  So the family can be instantiated at the
    SHIPPED tables, and three of its seven side conditions disappear:

    * `hgc` / `hh` — the index bounds become unconditional.  A fetched byte is
      a `BitVec 8`, both shipped tables are exactly 256 long, so there is
      nothing left to assume;
    * `halign` — discharged by `shippedHandlerTable_jalr_stable`, which is
      proved over the RESOLVER'S RANGE (the 157 generated rows plus the `0`
      default) rather than by enumerating 256 opcodes.

    What remains (`hi`, `hbase`, `hover`, `hvalid`) is about the CODE region
    the machine is fetching from, not about the tables — a different obligation
    entirely, and not one #13229 claimed.

    The two table `bytesRegion`s are still in the pre, and must be: separation
    logic requires owning a region to read it.  The change is that they are no
    longer arbitrary.  They are spelled `guestDataImage` here, which is that
    pair definitionally (`guestDataImage_tables`), so the entry assertion
    supplies them rather than the caller inventing them. -/

open Proofs.GuestDataImage in
/-- A fetched opcode always indexes the shipped gas table: it is a `BitVec 8`
    and the table is 256 long. -/
theorem shippedGas_index (b : BitVec 8) : b.toNat < shippedGasCostTable.length := by
  have hlen : shippedGasCostTable.length = 256 := by simp
  have hb : b.toNat < 2 ^ 8 := b.isLt
  omega

open Proofs.GuestDataImage in
/-- The same for the shipped handler table. -/
theorem shippedHandler_index (b : BitVec 8) :
    b.toNat < shippedHandlerTable.length := by
  have hlen : shippedHandlerTable.length = 256 := by simp
  have hb : b.toNat < 2 ^ 8 := b.isLt
  omega

open Proofs.GuestDataImage in
/-- **The dispatch step over the tables the image actually ships.**

    Same sixteen instructions, same two exits, same `guestImageCodeReq` — but
    the gas charged and the handler reached are now read out of
    `guestDataImage`, the pinned `.data` bundle, instead of out of two
    universally quantified lists.  For every one of the 256 opcodes, *this*
    opcode charges *this* gas and reaches *this* handler in the shipped
    guest. -/
theorem dispatchStep_body_shipped (codeBase : Word) (code : List (BitVec 8))
    (i : Nat) (gp gas old1 old5 old6 old7 : Word)
    (hi : i < code.length)
    (hbase : codeBase.toNat % 8 = 0)
    (hover : codeBase.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (codeBase + BitVec.ofNat 64 i) = true) :
    cpsBranchWithin 16 B guestImageCodeReq
      (((.x1 : Reg) ↦ᵣ old1) ** ((.x5 : Reg) ↦ᵣ old5) ** ((.x6 : Reg) ↦ᵣ old6)
        ** ((.x7 : Reg) ↦ᵣ old7)
        ** ((.x10 : Reg) ↦ᵣ (codeBase + BitVec.ofNat 64 i))
        ** ((.x20 : Reg) ↦ᵣ gp) ** ((gp + 568) ↦ₘ gas)
        ** bytesRegion codeBase code ** guestDataImage)
      (shippedHandlerTable[(code[i]'hi).toNat]'(shippedHandler_index _))
        (((.x1 : Reg) ↦ᵣ (B + 64))
          ** ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * (code[i]'hi).toNat))
          ** ((.x6 : Reg) ↦ᵣ (HT + BitVec.ofNat 64 (8 * (code[i]'hi).toNat)))
          ** ((.x7 : Reg) ↦ᵣ
              (shippedHandlerTable[(code[i]'hi).toNat]'(shippedHandler_index _)))
          ** ((.x10 : Reg) ↦ᵣ (codeBase + BitVec.ofNat 64 i))
          ** ((.x20 : Reg) ↦ᵣ gp)
          ** ((gp + 568) ↦ₘ
              (gas - (shippedGasCostTable[(code[i]'hi).toNat]'(shippedGas_index _))))
          ** ⌜¬ BitVec.ult gas
              (shippedGasCostTable[(code[i]'hi).toNat]'(shippedGas_index _))⌝
          ** bytesRegion codeBase code ** guestDataImage)
      (BitVec.ofNat 64 GuestAddrs.exit_outofgas)
        (((.x1 : Reg) ↦ᵣ old1)
          ** ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * (code[i]'hi).toNat))
          ** ((.x6 : Reg) ↦ᵣ
              (shippedGasCostTable[(code[i]'hi).toNat]'(shippedGas_index _)))
          ** ((.x7 : Reg) ↦ᵣ gas)
          ** ((.x10 : Reg) ↦ᵣ (codeBase + BitVec.ofNat 64 i))
          ** ((.x20 : Reg) ↦ᵣ gp) ** ((gp + 568) ↦ₘ gas)
          ** ⌜BitVec.ult gas
              (shippedGasCostTable[(code[i]'hi).toNat]'(shippedGas_index _))⌝
          ** bytesRegion codeBase code ** guestDataImage) :=
  dispatchStep_body_image codeBase code i shippedGasCostTable shippedHandlerTable
    gp gas old1 old5 old6 old7 hi hbase hover hvalid
    (shippedGas_index _) (shippedHandler_index _)
    (shippedHandlerTable_jalr_stable _ (by
      have hb : (code[i]'hi).toNat < 2 ^ 8 := BitVec.isLt _
      omega))

open Proofs.GuestDataImage in
set_option maxRecDepth 100000 in
/-- **Satisfiable instance for the shipped family**, and the reason it is worth
    stating separately from `dispatchStep_body_instance`.

    That earlier instance had to be built over `demoResolver`, because no Lean
    term named the linker's choice.  This one is about the image: `ADD` charges
    3 and reaches `h_ADD`, `STOP` reaches `h_STOP`, and the two are DIFFERENT
    addresses — so `dispatchStep_body_shipped` is a statement about 256
    distinct destinations, not one address repeated. -/
theorem dispatchStep_body_shipped_instance :
    shippedGasCostTable[0x01]! = 3
    ∧ shippedHandlerTable[0x01]! = BitVec.ofNat 64 GuestAddrs.h_ADD
    ∧ shippedHandlerTable[0x00]! = BitVec.ofNat 64 GuestAddrs.h_STOP
    ∧ shippedHandlerTable[0x00]! ≠ shippedHandlerTable[0x01]! := by
  refine ⟨by decide, by decide, by decide, by decide⟩

open Proofs.GuestDataImage in
set_option maxRecDepth 100000 in
/-- **Negative control: the parametric family really did not determine the
    image.**

    `demoResolver` is a legitimate resolver — it makes every premise of
    `dispatchStep_body_within` / `dispatchStep_body_image` true — and the table
    it produces is provably NOT the one the guest ships.  So the older family
    was satisfied by at least two different `.data` images, which is exactly
    what `opcode_table_contents_not_scratch_determined` says and exactly what
    `dispatchStep_body_shipped` removes.

    Second conjunct: the shipped gas table is not degenerate at the opcode the
    instance above uses (`ADD` is not free), so that instance is not reading a
    zeroed region. -/
theorem dispatchStep_body_shipped_controls :
    opcodeHandlerEntries demoResolver ≠ shippedHandlerTable
    ∧ ¬ (shippedGasCostTable[0x01]! = 0) := by
  refine ⟨by decide, by decide⟩

end EvmAsm.Codegen.DispatchStepOpcode
