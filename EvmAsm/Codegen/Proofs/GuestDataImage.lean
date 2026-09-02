/-
  EvmAsm.Codegen.Proofs.GuestDataImage

  **The `.data` counterpart of `guestImageCodeReq`** (GH #13229): what the
  shipped image's writable data section HOLDS at the two dispatch tables, as a
  separation-logic assertion the dispatch triple can consume.

  ## The gap this closes

  `guestImageCodeReq` (`Proofs/GuestImage.lean`) pins `.text` — every linked
  `_prog` at its `GuestAddrs` entry.  Nothing pinned `.data`: `guestScratch`
  owned the whole tile as `regionScratch = anyBytes`, ownership with contents
  FORGOTTEN, and `DispatchStepOpcode.opcode_table_contents_not_scratch_determined`
  states that as a theorem rather than as prose.  So #13228's whole-dispatch-step
  triple took `bytesRegion GT (tableBytes gasCosts)` and
  `bytesRegion HT (tableBytes handlers)` as *premises*: it proved the control
  flow and the indexing for all 256 opcodes, but not *which* handler an opcode
  reaches.

  ## The design decision, and why this shape

  `.data` is part of the LOADED image exactly as `.text` is — the ELF's PROGBITS
  are copied in before `_start`.  Modelling it as havoc was not conservative, it
  was unfaithful in the direction that makes the dispatch step unprovable.  So
  the counterpart of `guestImageCodeReq` is not a new kind of object: it is the
  same move `.text` already makes, applied to the bytes the loader writes.

  Two consequences follow, and both are deliberate:

  * **Only what Lean can name is pinned.**  `.data` also holds `sha256_w_iv`,
    the secp/secf constants, `secc_point_tmp` (which the guest WRITES), and
    ~260 other symbols.  Pinning the whole tile would be wrong.  This file pins
    the two dispatch tables and leaves the rest havoc'd, and the split is a
    definition, not a lemma — `anyBytes` cannot be strengthened into
    `bytesRegion` after the fact (that is what
    `opcode_table_contents_not_scratch_determined` says).

  * **Row identity is an ELF symbol**, as it is for `guestImageEntries`.  The
    gas table's contents are emitter-derived (`opcodeGasCostEntries`, numbers
    `staticGasCost` already produces); the handler table's are LINK-derived, so
    they arrive through `GuestHandlerAddrs.handlerAddrRows` — generated from
    `symbol-addresses.tsv`, citing `GuestAddrs.h_*` by name.

  ## Which side of the stride line this falls on (#13011 / #13014)

  The interior-slice hazard needs a region whose size is **not** a multiple of
  the access stride: keccak's 20-byte region under an 8-byte stride is hard
  because `8 ∤ 20`, and a 20-byte `bytesRegion` under a dword split silently
  asserts the next 4 bytes.  A dword-indexed table is on the free side of that
  line, and `dataTables_stride_divides` is that claim as a theorem: the carve
  offset is `8 ∣ dataTablesOffset`, each table is `8 * 256` bytes so
  `8 ∣ tableSizeBytes`, and — measured from `GuestAddrs` and `RegionMap`, not
  from prose — the pair sits at the very TOP of `.data`, so there is no trailing
  tile to mis-size either (`dataTables_layout`).  Every split used below is
  therefore an `anyBytes_add` / `bytesRegion_append` at a dword boundary, and no
  assertion reaches a byte outside a table.

  ## What is pinned, and what is still a premise

  `guestDataScratch` replaces `regionScratch RegionMap.dataRegion` inside
  `guestScratch`/`guestResidue`.  `guestDataScratch_weakens` is the discharge
  obligation for that swap: the pinned bundle ENTAILS the havoc'd tile it
  replaces, so every consumer that only needed ownership is unaffected, and the
  swap strictly strengthens the entry assertion.  `guestDataScratch_satWithin`
  re-establishes the `.63` satisfiability witness at the new definition.
-/

import EvmAsm.Codegen.GuestHandlerAddrs
import EvmAsm.Codegen.Proofs.OpcodeTables
import EvmAsm.Codegen.RegionMap
import EvmAsm.Rv64.MemSat
import EvmAsm.Rv64.SAsm.PhaseSplit

namespace EvmAsm.Codegen.Proofs.GuestDataImage

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs.OpcodeTables

/-! ## 1. The shipped resolver

    `opcode_handlers` is emitted as 256 `.dword <label>` entries, so its
    contents are the LINKER's choice.  `opcodeHandlerEntries` is parameterised
    by `addrOf : String → Word` precisely because of that; this is the shipped
    instance, backed by the generated projection of `symbol-addresses.tsv`. -/

/-- The link-time handler-label resolver, from the generated row table.
    An unknown label resolves to `0`, which is not a handler address —
    `guestDataImage_controls` is the negative control, and
    `scripts/check-opcode-tables.sh` is what catches a missing row against the
    ELF. -/
def guestHandlerAddr (s : String) : Word :=
  BitVec.ofNat 64 ((GuestHandlerAddrs.handlerAddrRows.lookup s).getD 0)

/-- The `opcode_gas_costs` table as shipped: emitter-derived numbers. -/
abbrev shippedGasCostTable : List Word := opcodeGasCostEntries

/-- The `opcode_handlers` table as shipped: the emitter's label list resolved
    through the link-time address map. -/
abbrev shippedHandlerTable : List Word := opcodeHandlerEntries guestHandlerAddr

/-! ## 2. Layout, derived from `GuestAddrs` + `RegionMap` -/

/-- Base of the gas-cost table, as a machine word (read from `GuestAddrs`). -/
abbrev gasTableBase : Word := BitVec.ofNat 64 GuestAddrs.opcode_gas_costs

/-- Base of the handler table, as a machine word. -/
abbrev handlerTableBase : Word := BitVec.ofNat 64 GuestAddrs.opcode_handlers

/-- Base of the `.data` tile, as a machine word. -/
abbrev dataTileBase : Word := BitVec.ofNat 64 RegionMap.dataRegion.base

/-- Byte offset of the table pair inside `.data`, DERIVED from the two pinned
    addresses rather than written down. -/
abbrev dataTablesOffset : Nat :=
  GuestAddrs.opcode_gas_costs - RegionMap.dataRegion.base

/-- One table's byte extent: 256 dwords. -/
abbrev tableSizeBytes : Nat := 8 * 256

/-- **The layout, measured.**  The two tables are adjacent, dword-aligned, and
    together occupy exactly the TOP of the `.data` tile — there is no trailing
    havoc'd fragment to mis-size.  Every conjunct is read out of `GuestAddrs`
    and `RegionMap`; the `prog.length * 4`-style cross-check for a table is the
    third conjunct (`8 * 256` is `tableBytes`' length at 256 entries). -/
theorem dataTables_layout :
    RegionMap.dataRegion.base + dataTablesOffset = GuestAddrs.opcode_gas_costs
    ∧ GuestAddrs.opcode_gas_costs + tableSizeBytes = GuestAddrs.opcode_handlers
    ∧ GuestAddrs.opcode_handlers + tableSizeBytes
        = RegionMap.dataRegion.base + RegionMap.dataRegion.size := by decide

/-- **Which side of the #13011 / #13014 stride line a dword table falls on.**

    The interior-slice hazard is a region whose size is not a multiple of the
    access stride (`8 ∤ 20` for keccak's twenty bytes).  Here the stride divides
    everything in sight: the carve offset, each table's extent, and the
    `tableBytes` images themselves.  So the carve is free — no `bytesRegion`
    below asserts anything about a byte it does not own, and no split lands
    mid-dword. -/
theorem dataTables_stride_divides :
    8 ∣ dataTablesOffset
    ∧ 8 ∣ tableSizeBytes
    ∧ (tableBytes shippedGasCostTable).length = tableSizeBytes
    ∧ (tableBytes shippedHandlerTable).length = tableSizeBytes := by
  refine ⟨by decide, by decide, ?_, ?_⟩ <;> simp

/-! ## 3. The `.data` image assertion -/

/-- **The `.data` counterpart of `guestImageCodeReq`**: the two dispatch tables
    at their linked bases, holding the bytes the image ships.  Two rows, each
    keyed by an ELF symbol, exactly as `guestImageEntries`' rows are. -/
def guestDataImage : Assertion :=
  bytesRegion gasTableBase (tableBytes shippedGasCostTable) **
  bytesRegion handlerTableBase (tableBytes shippedHandlerTable)

/-- The `.data` tile as the guest owns it at entry: the unpinned prefix, then
    the two pinned tables.  This is what replaces
    `regionScratch RegionMap.dataRegion` inside `guestScratch`. -/
def guestDataScratch : Assertion :=
  anyBytes dataTileBase dataTablesOffset ** guestDataImage

/-- The havoc'd `.data` tile, split at the two dword-aligned table boundaries.
    Pure `anyBytes` on both sides — this is the shape the PINNED bundle
    weakens onto. -/
theorem anyBytes_data_split :
    anyBytes dataTileBase RegionMap.dataRegion.size
      = (anyBytes dataTileBase dataTablesOffset
          ** (anyBytes gasTableBase tableSizeBytes
              ** anyBytes handlerTableBase tableSizeBytes)) := by
  rw [show RegionMap.dataRegion.size
        = dataTablesOffset + (tableSizeBytes + tableSizeBytes) from by decide,
    anyBytes_add dataTileBase dataTablesOffset _ (by decide),
    show dataTileBase + BitVec.ofNat 64 dataTablesOffset = gasTableBase from by
      decide,
    anyBytes_add gasTableBase tableSizeBytes _ (by decide),
    show gasTableBase + BitVec.ofNat 64 tableSizeBytes = handlerTableBase from by
      decide]

private theorem bytesRegion_anyBytes_len {base : Word} {bs : List (BitVec 8)}
    {n : Nat} (hn : bs.length = n) :
    ∀ h, bytesRegion base bs h → anyBytes base n h := by
  intro h hb
  rw [← hn]
  exact bytesRegion_anyBytes base bs h hb

/-- **The swap is a strengthening.**  Whatever needed the old havoc'd `.data`
    tile still has it: the pinned bundle entails
    `regionScratch RegionMap.dataRegion` (spelled here as its `anyBytes`
    definition, since `regionScratch` lives one layer up).

    This is the discharge obligation for redefining `guestScratch`: no consumer
    that only wanted OWNERSHIP of `.data` can be broken by the swap, and the
    entry assertion strictly gains information. -/
theorem guestDataScratch_weakens :
    ∀ h, guestDataScratch h → anyBytes dataTileBase RegionMap.dataRegion.size h := by
  intro h hh
  rw [anyBytes_data_split]
  refine sepConj_mono (fun _ hx => hx) ?_ h hh
  exact sepConj_mono
    (bytesRegion_anyBytes_len (by simp))
    (bytesRegion_anyBytes_len (by simp))

/-! ## 4. Satisfiability at the new definition

    `guestScratch_sat` (`.63`) exhibits a heap for the entry bundle.  Pinning
    two tiles changes the witness for those tiles from "all zeroes" to "the
    shipped bytes", and nothing else: the footprints and bounds are the same,
    because `satWithin_bytesRegion`'s obligation depends only on the LENGTH. -/

/-- A `bytesRegion` inside the model's RAM zone is satisfiable within its own
    extent.  `satWithin_ramAny` below is the `anyBytes` case of the same
    argument, and `GuestImage.satWithin_ramRegion` is now a wrapper for it
    rather than a second copy. -/
theorem satWithin_ramBytes (b : Nat) (bs : List (BitVec 8))
    (hb : 0xa0000000 ≤ b) (he : b + bs.length ≤ 0xc0000000)
    (halign : b % 8 = 0) (hn : bs.length % 8 = 0) :
    (bytesRegion (BitVec.ofNat 64 b) bs).SatWithin b (b + bs.length) := by
  have hbase : (BitVec.ofNat 64 b).toNat = b := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hcount : 8 * ((bs.length + 7) / 8) = bs.length := by omega
  have h := satWithin_bytesRegion (BitVec.ofNat 64 b) bs (fun k hk => by
    have hlt : (BitVec.ofNat 64 b).toNat + 8 * k < 2 ^ 64 := by omega
    apply isValidDwordAccess_of_toNat
    · rw [toNat_add_ofNat_of_le hlt, hbase]; omega
    · rw [toNat_add_ofNat_of_le hlt, hbase]; right; right; omega)
  rw [hbase, hcount] at h
  exact h

/-- The `anyBytes` case: a havoc'd RAM range is satisfiable within its extent.
    Kept here so `GuestImage.satWithin_ramRegion` has one definition, not two
    copies of the same zone argument. -/
theorem satWithin_ramAny (b n : Nat)
    (hb : 0xa0000000 ≤ b) (he : b + n ≤ 0xc0000000)
    (halign : b % 8 = 0) (hn : n % 8 = 0) :
    (anyBytes (BitVec.ofNat 64 b) n).SatWithin b (b + n) := by
  have h := satWithin_ramBytes b (List.replicate n (0 : BitVec 8)) hb
    (by simpa using he) halign (by simpa using hn)
  obtain ⟨hp, hsat, hw⟩ := h
  exact ⟨hp, ⟨List.replicate n 0, List.length_replicate, hsat⟩, by simpa using hw⟩

/-- The entry witness for the pinned `.data` tile, at the same bounds the
    havoc'd tile had. -/
theorem guestDataScratch_satWithin :
    guestDataScratch.SatWithin RegionMap.dataRegion.base
      (RegionMap.dataRegion.base + RegionMap.dataRegion.size) := by
  have hgas : (tableBytes shippedGasCostTable).length = tableSizeBytes := by simp
  have hhnd : (tableBytes shippedHandlerTable).length = tableSizeBytes := by simp
  have s1 : (anyBytes dataTileBase dataTablesOffset).SatWithin
      RegionMap.dataRegion.base GuestAddrs.opcode_gas_costs :=
    (satWithin_ramAny RegionMap.dataRegion.base dataTablesOffset
      (by decide) (by decide) (by decide) (by decide)).congr_bounds rfl (by decide)
  have s2 : (bytesRegion gasTableBase (tableBytes shippedGasCostTable)).SatWithin
      GuestAddrs.opcode_gas_costs GuestAddrs.opcode_handlers := by
    have h := satWithin_ramBytes GuestAddrs.opcode_gas_costs
      (tableBytes shippedGasCostTable) (by decide) (by rw [hgas]; decide)
      (by decide) (by rw [hgas]; decide)
    exact h.congr_bounds rfl (by rw [hgas]; decide)
  have s3 : (bytesRegion handlerTableBase (tableBytes shippedHandlerTable)).SatWithin
      GuestAddrs.opcode_handlers
      (RegionMap.dataRegion.base + RegionMap.dataRegion.size) := by
    have h := satWithin_ramBytes GuestAddrs.opcode_handlers
      (tableBytes shippedHandlerTable) (by decide) (by rw [hhnd]; decide)
      (by decide) (by rw [hhnd]; decide)
    exact h.congr_bounds rfl (by rw [hhnd]; decide)
  exact s1.sepConj (s2.sepConj s3 (by decide) (by decide))
    (by decide) (by decide)

/-! ## 5. Reading a table entry out of the image -/

/-- **The extraction the dispatch triple wants.**  `guestDataImage` splits into
    the gas table alongside a frame, and into the handler table alongside a
    frame — the two `bytesRegion` premises of
    `DispatchStepOpcode.dispatchStep_body_within`, now supplied by the image
    rather than assumed by the caller. -/
theorem guestDataImage_tables :
    guestDataImage
      = (bytesRegion gasTableBase (tableBytes shippedGasCostTable)
          ** bytesRegion handlerTableBase (tableBytes shippedHandlerTable)) :=
  rfl

theorem guestDataImage_pcFree : guestDataImage.pcFree :=
  pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _)

theorem guestDataScratch_pcFree : guestDataScratch.pcFree :=
  pcFree_sepConj (pcFree_anyBytes _ _) guestDataImage_pcFree

/-! ## 6. The handler table's entries are jump-able

    `jalr` clears bit 0 of its target, so `dispatchStep_opcode_within` carries
    an alignment side-condition on the loaded handler address.  It holds for
    every entry of the shipped table, and NOT by enumerating 256 opcodes: the
    resolver's range is `{0} ∪ {row values}`, and every row value is a 4-aligned
    `.text` address. -/

private theorem lookup_getD_mem {α β : Type} [BEq α] (a : α) (d : β) :
    ∀ l : List (α × β),
      (l.lookup a).getD d = d ∨ ∃ p ∈ l, (l.lookup a).getD d = p.2 := by
  intro l
  induction l with
  | nil => exact Or.inl rfl
  | cons p ps ih =>
    obtain ⟨k, b⟩ := p
    by_cases hk : a == k
    · exact Or.inr ⟨(k, b), List.mem_cons_self, by simp [List.lookup, hk]⟩
    · rcases ih with h | ⟨q, hq, hqe⟩
      · exact Or.inl (by simp [List.lookup, hk, h])
      · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, by simp [List.lookup, hk, hqe]⟩

set_option maxRecDepth 40000 in
/-- Every row of the generated resolver names a 4-aligned `.text` address well
    inside the 64-bit word.  157 rows, kernel-checked. -/
theorem handlerAddrRows_aligned :
    ∀ p ∈ GuestHandlerAddrs.handlerAddrRows, p.2 % 4 = 0 ∧ p.2 < 2 ^ 64 := by
  decide

private theorem ofNat_and_not_one_of_even {n : Nat} (hn : n % 2 = 0) :
    (BitVec.ofNat 64 n &&& ~~~(1 : Word)) = BitVec.ofNat 64 n := by
  have hz : (BitVec.ofNat 64 n).getLsbD 0 = false := by
    rw [BitVec.getLsbD_ofNat]; simp [Nat.testBit_zero, hn]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not]
  by_cases h0 : i = 0
  · subst h0; rw [hz]; simp
  · simp [h0, hi]

/-- **Every address the shipped resolver can return is a legal `jalr` target.**
    Covers all 256 table cells without enumerating them: the resolver's range is
    the row values plus the `0` default, and both are even. -/
theorem guestHandlerAddr_jalr_stable (s : String) :
    (guestHandlerAddr s &&& ~~~(1 : Word)) = guestHandlerAddr s := by
  unfold guestHandlerAddr
  rcases lookup_getD_mem s 0 GuestHandlerAddrs.handlerAddrRows with h | ⟨p, hp, he⟩
  · rw [h]; exact ofNat_and_not_one_of_even (by decide)
  · rw [he]
    exact ofNat_and_not_one_of_even (by
      have := (handlerAddrRows_aligned p hp).1
      omega)

/-- The same fact, in the form `dispatchStep_body_within`'s `halign` premise
    wants it: at any index of the shipped handler table. -/
theorem shippedHandlerTable_jalr_stable (op : Nat) (hop : op < 256) :
    ((shippedHandlerTable[op]'(by simp [hop])) &&& ~~~(1 : Word))
      = shippedHandlerTable[op]'(by simp [hop]) := by
  rw [opcodeHandlerEntries_get guestHandlerAddr op hop]
  exact guestHandlerAddr_jalr_stable _

/-! ## 7. Non-vacuity, and the negative control -/

/-- **Satisfiable instance.**  The resolver really resolves: `h_ADD` maps to the
    `GuestAddrs` pin the linker produced, and the two tables have the length the
    image ships. -/
theorem guestDataImage_instance :
    guestHandlerAddr "h_ADD" = BitVec.ofNat 64 GuestAddrs.h_ADD
    ∧ guestHandlerAddr "h_invalid" = BitVec.ofNat 64 GuestAddrs.h_invalid
    ∧ shippedGasCostTable.length = 256
    ∧ shippedHandlerTable.length = 256 := by
  refine ⟨by decide, by decide, by simp, by simp⟩

/-- **Negative control, three ways.**

    1. The resolver DISCRIMINATES: an unknown label is not a handler address.
       Without a row, `opcodeHandlerEntries guestHandlerAddr` would quietly hold
       `0` at that opcode — which is why `scripts/check-opcode-tables.sh`
       compares against the ELF and why a missing row is a gate failure, not a
       silent weakening.
    2. The alignment premise is not decoration: at an ODD address `jalr` does
       NOT return the loaded value, so `guestHandlerAddr_jalr_stable` is doing
       work.
    3. The stride claim is not vacuous: the hazard shape it rules out
       (`8 ∤ 20`, keccak's region) is exhibited as a FALSE divisibility beside
       the true one. -/
theorem guestDataImage_controls :
    guestHandlerAddr "h_not_a_handler" ≠ BitVec.ofNat 64 GuestAddrs.h_ADD
    ∧ ¬ (((3 : Word) &&& ~~~(1 : Word)) = (3 : Word))
    ∧ ¬ (8 ∣ 20) ∧ 8 ∣ tableSizeBytes := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## 8. The residue-preservation obligation the pin CREATES

    §3's `guestDataScratch_weakens` discharges the swap on the PRE side, and
    that is the whole story for `guestScratch`: strengthening a precondition
    can only help a consumer that merely wanted ownership.  `guestResidue` is
    a POST, and `GuestImage.guestScratch_eq_window_residue` is an EQUALITY, so
    the same substitution on the residue side is a genuine NEW obligation for
    `.64`: **the guest must not clobber either table by halt.**

    This section does not discharge that obligation — `dataTables_residue_gap`
    says exactly why it cannot be discharged here — but it does three things
    prose could not:

    * `bytesRegion_mem_dword` makes a pinned table's dword contents READABLE
      off any heap satisfying the pin.  That is what "clobbered" has to mean
      at the assertion layer, and it is the general form of
      `HashBridgeKeccakEnvelope`'s private three-dword `mem_dword2_of_bytesRegion`.
    * `guestDataScratch_strictly_stronger` proves the obligation is REAL: an
      all-zero `.data` heap satisfies the havoc'd tile the residue used to
      carry, and does NOT satisfy the pinned one.  The residue side gained a
      proof burden, not a docstring.
    * `dataTables_residue_gap` states where the remaining gap sits, as a claim
      about what does and does not follow rather than as a remark. -/

section ResiduePreservation

-- Instantiating `bytesRegion_mem_dword` at `tableBytes <a 256-entry table>`
-- makes the elaborator reduce `List.length` through a 256-way `flatMap`, and
-- `guestDataScratch_strictly_stronger` additionally reduces a `getElem` at a
-- concrete index; neither survives the default 512 frames.  Measured, not
-- guessed: 8000 still fails, 40000 carries everything but the strictness
-- proof, which carries its own `set_option` below.
set_option maxRecDepth 40000

/-! The four heap-lookup helpers below are general separation-logic facts, not
    `.data` facts.  They live here rather than in `EvmAsm/Rv64/SepLogic.lean`
    because that module is a GENERATED shim over `riscv-zkvm`
    (`scripts/gen-rv64-shims.py`, `--check`-gated), so it cannot host new
    lemmas.  `HashBridgeKeccakEnvelope` needed the same reasoning and kept a
    private three-dword special case; if a third caller appears, these are what
    it should reuse. -/

/-- Left-biased union: a dword the LEFT heap owns survives the merge. -/
theorem mem_union_left {h₁ h₂ : PartialState} {a v : Word}
    (hv : h₁.mem a = some v) : (h₁.union h₂).mem a = some v := by
  show (match h₁.mem a with | some x => some x | none => h₂.mem a) = some v
  rw [hv]

/-- Left-biased union: a dword the RIGHT heap owns also survives, because
    disjointness makes the left heap's slot empty. -/
theorem mem_union_right {h₁ h₂ : PartialState} {a v : Word}
    (hd : h₁.Disjoint h₂) (hv : h₂.mem a = some v) :
    (h₁.union h₂).mem a = some v := by
  rcases hd.2.1 a with hn | hn
  · show (match h₁.mem a with | some x => some x | none => h₂.mem a) = some v
    rw [hn]; exact hv
  · rw [hn] at hv; exact absurd hv (by simp)

/-- Read a determined dword through the LEFT conjunct of a `**`. -/
theorem mem_of_sepConj_left {P Q : Assertion} {h : PartialState} {a v : Word}
    (hpq : (P ** Q) h) (hP : ∀ h', P h' → h'.mem a = some v) :
    h.mem a = some v := by
  obtain ⟨h₁, h₂, -, rfl, hp, -⟩ := hpq
  exact mem_union_left (hP h₁ hp)

/-- Read a determined dword through the RIGHT conjunct of a `**`. -/
theorem mem_of_sepConj_right {P Q : Assertion} {h : PartialState} {a v : Word}
    (hpq : (P ** Q) h) (hQ : ∀ h', Q h' → h'.mem a = some v) :
    h.mem a = some v := by
  obtain ⟨h₁, h₂, hd, rfl, -, hq⟩ := hpq
  exact mem_union_right hd (hQ h₂ hq)

/-- **A pinned region's dword contents are DETERMINED.**  Every atom of
    `bytesRegion` is exact ownership (`memIs a v h` means
    `h = singletonMem a v`), so at every dword index the heap holds exactly
    the packed slice — no `∃`, no frame to hide in.  This is what makes
    "the table still holds the shipped bytes" a checkable statement about a
    halt heap. -/
theorem bytesRegion_mem_dword {base : Word} {bs : List (BitVec 8)} {dw : Nat}
    (hdw : 8 * dw < bs.length) {h : PartialState} (hb : bytesRegion base bs h) :
    h.mem (base + BitVec.ofNat 64 (8 * dw))
      = some (packBytes ((bs.drop (8 * dw)).take 8)) := by
  obtain ⟨front, rest, -, -, heq⟩ := bytesRegion_dword_at base bs dw hdw
  rw [heq] at hb
  refine mem_of_sepConj_right hb (fun h' hh => ?_)
  refine mem_of_sepConj_left hh (fun h'' hh' => ?_)
  obtain ⟨rfl, -⟩ := hh'
  simp [PartialState.singletonMem]

/-- The gas table's `i`-th dword, read off any heap satisfying the pin. -/
theorem guestDataImage_mem_gas_dword {i : Nat} (hi : i < 256)
    {h : PartialState}
    (hd : guestDataImage h) :
    h.mem (gasTableBase + BitVec.ofNat 64 (8 * i))
      = some (shippedGasCostTable[i]'(by
          simp only [length_opcodeGasCostEntries]; exact hi)) := by
  unfold guestDataImage at hd
  obtain ⟨h₁, h₂, -, rfl, hg, -⟩ := hd
  have hbound : 8 * i < (tableBytes shippedGasCostTable).length := by
    simp only [length_tableBytes, length_opcodeGasCostEntries]; omega
  have hcell := bytesRegion_mem_dword (base := gasTableBase)
    (bs := tableBytes shippedGasCostTable) (dw := i) (h := h₁) hbound hg
  rw [tableBytes_slice shippedGasCostTable i
      (by simp only [length_opcodeGasCostEntries]; exact hi),
    packBytes_dwordBytes] at hcell
  exact mem_union_left hcell

/-- The handler table's `i`-th dword, read off any heap satisfying the pin. -/
theorem guestDataImage_mem_handler_dword {i : Nat} (hi : i < 256)
    {h : PartialState}
    (hd : guestDataImage h) :
    h.mem (handlerTableBase + BitVec.ofNat 64 (8 * i))
      = some (shippedHandlerTable[i]'(by
          simp only [length_opcodeHandlerEntries]; exact hi)) := by
  unfold guestDataImage at hd
  obtain ⟨h₁, h₂, hdj, rfl, -, hn⟩ := hd
  have hbound : 8 * i < (tableBytes shippedHandlerTable).length := by
    simp only [length_tableBytes, length_opcodeHandlerEntries]; omega
  have hcell := bytesRegion_mem_dword (base := handlerTableBase)
    (bs := tableBytes shippedHandlerTable) (dw := i) (h := h₂) hbound hn
  rw [tableBytes_slice shippedHandlerTable i
      (by simp only [length_opcodeHandlerEntries]; exact hi),
    packBytes_dwordBytes] at hcell
  exact mem_union_right hdj hcell

/-- The `.data` tile's dword index of `opcode_gas_costs[1]`, derived from the
    two pinned addresses rather than written down: the gas table starts at
    `dataTablesOffset` bytes into the tile, and ADD is opcode `1`. -/
private abbrev gasDword1Index : Nat := dataTablesOffset / 8 + 1

/-- ADD's static gas cost is `3`, so dword `1` of `opcode_gas_costs` is NOT
    zero — the discriminator the strictness proof below turns on.  Stated
    separately so a re-tiering of ADD breaks *this*, with a reason, rather
    than the strictness proof's last `rw`. -/
theorem gas_dword1_ne_zero :
    (shippedGasCostTable[1]'(by simp only [length_opcodeGasCostEntries]; omega))
      ≠ (0 : Word) := by
  simp only [shippedGasCostTable, opcodeGasCostEntries, List.getElem_map,
    List.getElem_range]
  decide

set_option maxRecDepth 200000 in
/-- **The pin is a STRICT strengthening, so the residue obligation is real.**

    A heap holding all zeroes across `.data` satisfies the havoc'd tile that
    `guestScratch`/`guestResidue` used to carry, and does NOT satisfy the
    pinned one: dword `1` of `opcode_gas_costs` is ADD's static cost `3`, not
    `0`.  So `guestDataScratch` genuinely rules out halt heaps that the old
    `regionScratch RegionMap.dataRegion` admitted, and `guestDataScratch_weakens`
    (§3) is one-directional on purpose.

    ⛔ Read together with `guestDataScratch_weakens` this is the whole shape of
    GH #13229's cost: free on the PRE, a new proof burden on the POST. -/
theorem guestDataScratch_strictly_stronger :
    ∃ h, anyBytes dataTileBase RegionMap.dataRegion.size h
      ∧ ¬ guestDataScratch h := by
  have hlen : (List.replicate RegionMap.dataRegion.size (0 : BitVec 8)).length
      = RegionMap.dataRegion.size := List.length_replicate
  obtain ⟨h, hz, -⟩ := satWithin_ramBytes RegionMap.dataRegion.base
    (List.replicate RegionMap.dataRegion.size (0 : BitVec 8))
    (by decide) (by rw [hlen]; decide) (by decide) (by rw [hlen]; decide)
  refine ⟨h, ⟨_, hlen, hz⟩, fun hpin => ?_⟩
  -- the zero heap's dword at `opcode_gas_costs + 8`
  have hzero := bytesRegion_mem_dword
    (bs := List.replicate RegionMap.dataRegion.size (0 : BitVec 8))
    (dw := gasDword1Index) (by rw [hlen]; decide) hz
  -- the pinned tile's dword at the same address
  have hpinned := mem_of_sepConj_right hpin
    (fun h' hh => guestDataImage_mem_gas_dword (i := 1) (by decide) hh)
  rw [show (BitVec.ofNat 64 RegionMap.dataRegion.base
        + BitVec.ofNat 64 (8 * gasDword1Index))
      = gasTableBase + BitVec.ofNat 64 (8 * 1) from by decide] at hzero
  rw [hpinned] at hzero
  -- the two readings of the same dword, spelled at the same type
  have hsame : (shippedGasCostTable[1]'(by
        simp only [length_opcodeGasCostEntries]; omega))
      = packBytes (List.take 8 (List.drop (8 * gasDword1Index)
          (List.replicate RegionMap.dataRegion.size (0 : BitVec 8)))) :=
    Option.some.inj hzero
  have hzeroval : packBytes (List.take 8 (List.drop (8 * gasDword1Index)
      (List.replicate RegionMap.dataRegion.size (0 : BitVec 8)))) = 0 := by
    simp only [List.drop_replicate, List.take_replicate]
    decide
  exact gas_dword1_ne_zero (hsame.trans hzeroval)

/-- **Where the gap is, and what is on each side of it.**

    1. The residue now DETERMINES the tables: any halt heap satisfying
       `guestDataImage` holds `shippedHandlerTable[i]` at
       `opcode_handlers + 8i`.  So the obligation has a statement, not just a
       name.
    2. It is not free: `guestDataScratch_strictly_stronger` exhibits a heap
       that satisfies the old havoc'd tile and fails the pinned one.
    3. And it is not derivable from ownership: the havoc weakening is
       one-directional, which is
       `DispatchStepOpcode.opcode_table_contents_not_scratch_determined` in
       the `.data` tile's own vocabulary.

    ⛔ **What is missing** is the run-level fact — that the guest's stores never
    reach `[opcode_gas_costs, .data_end)` — and it cannot be proved at this
    layer, because `.64` (`TopComposition.runStatelessGuestSound_of_phases`)
    still takes its six phase Props as HYPOTHESES: there is no whole-program
    write map to quantify over.  The offline evidence is
    `scripts/check-data-table-residue.sh`, which re-derives from the LINKED
    image (not from the emitter source, and not from this docstring) that
    exactly two instructions in `.text` materialise an address in the range,
    that both feed an `ld`, and that no store's statically resolvable base
    lands in it.  That gate bounds the risk; it is not a proof, and this
    theorem does not pretend otherwise. -/
theorem dataTables_residue_gap :
    (∀ (i : Nat) (hi : i < 256), ∀ h, guestDataImage h →
        h.mem (handlerTableBase + BitVec.ofNat 64 (8 * i))
          = some (shippedHandlerTable[i]'(by
              simp only [length_opcodeHandlerEntries]; exact hi)))
    ∧ (∃ h, anyBytes dataTileBase RegionMap.dataRegion.size h
        ∧ ¬ guestDataScratch h)
    ∧ (∀ h, guestDataScratch h →
        anyBytes dataTileBase RegionMap.dataRegion.size h) :=
  ⟨fun _ hi _ hd => guestDataImage_mem_handler_dword hi hd,
   guestDataScratch_strictly_stronger,
   guestDataScratch_weakens⟩

end ResiduePreservation

end EvmAsm.Codegen.Proofs.GuestDataImage
