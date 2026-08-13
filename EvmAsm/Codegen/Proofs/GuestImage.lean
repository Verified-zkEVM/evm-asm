/-
  EvmAsm.Codegen.Proofs.GuestImage

  The structural half of bead evm-asm-4ch8f.63: the two artifacts the
  top-level theorem (bead .64) instantiates `runStatelessGuestSound` with,
  composed from the wave-.9 conversions and the RegionMap:

  * `guestImageCodeReq` — the guest image's code requirement: the
    `CodeReq.unionAll` of `CodeReq.ofProg` at every LINKED converted
    function's `GuestAddrs` entry (`guestImageEntries`, GENERATED).
    `guestImage_block_sub` lifts any per-function triple into the image
    via `cpsTripleWithin_extend_code`/`cpsHaltTripleWithin_extend_code`,
    with the whole-image disjointness discharged by the ONE kernel-checked
    extent check `guestImageEntries_extentsOk` — no per-block case split.
    COVERAGE: the entries cover only part of `.text`; the authoritative
    gap accounting is `scripts/guest_image_coverage.py` (child beads under
    .63 track the uncovered ranges — `.64` needs the FULL image).

  * `guestFraming : GuestFraming` — the scratch/residue bundle: the `**`
    of `anyBytes` havoc over the eight writable (`zone = .ram`) regions of
    `RegionMap.guestRegionMap` (`guestScratch_matches_regionMap` pins the
    memory bundle to the map, so a region-map change breaks the build here),
    plus ownership of the registers written at the halt boundary: `x5` is
    written by the guest body and by `sp1`, while `x17` (the linux93 syscall
    selector) and `x10` (the linux93 result) are written by `linux93`.  The
    `scratch_sat` non-vacuity witness is built from the `Rv64.MemSat`
    footprint combinators and three disjoint register atoms.

  This file lives Codegen-side because both artifacts need Codegen
  (`GuestAddrs`, the `_prog`s, `RegionMap`) and Codegen is a pure layering
  sink — `Stateless/EntrySpec.lean` stays Codegen-free.
-/

import EvmAsm.Rv64.CodeReqExtents
import EvmAsm.Rv64.MemSat
import EvmAsm.Codegen.Proofs.GuestImageEntries
import EvmAsm.Codegen.RegionMap
import EvmAsm.Codegen.RegionMapLinkPins
import EvmAsm.Stateless.EntrySpec

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm (anyBytes)
open EvmAsm.Stateless

/-! ## 1. The guest-image `CodeReq` -/

/-- The guest image's code requirement: every linked converted `_prog`
    pinned at its `GuestAddrs` entry (see `guestImageEntries`).

    ⛔ **Do not instantiate a phase theorem at `guestImageCodeReq` while that
    phase's entry is unpinned.** `cpsTripleWithin_needs_entry_code`
    (`TopComposition.lean`) makes an unpinned entry **unsatisfiable**: a phase
    stated here whose `entry` has `cr entry = none` (and meets the lemma's other
    conditions) is **FALSE**, not merely weak — vacuous for its consumer rather
    than incomplete. Instantiation waits on full-image coverage (or an explicit
    argument that the phase falls outside the lemma).

    **Live extent**: `.text` is `[RegionMap.textRegion.base, guestTextEnd)`, whose
    size is `RegionMapLinkPins.textSizeBytes` — cite those SYMBOLS, not their
    values, since a link-layout regen moves them. For the covered byte count and
    percentage read the generated `docs/4ch8f-guest-image-coverage.md` (§1
    Summary), produced by `scripts/guest_image_coverage.py`. The largest remaining
    gap is the unconverted `_start` shell at the base of `.text` — the inherited
    whole-image clobber residual (#12166). The coverage *floor* constant is a
    gate, not the extent.

    This block previously quoted the extent inline — start address, end address,
    decimal size and the hex value of `textSizeBytes` — and every one of those
    literals had gone stale by 220 bytes, directly under a caveat reading
    "measure; do not copy older prose". A warning does not keep a figure fresh;
    `scripts/check-obligation-claims.sh` class D now checks any prose citing
    `textSizeBytes` against the constant itself. The stale digits are deliberately
    NOT reproduced here: that gate is value-exact and has no historical-example
    escape hatch, by design — an escape hatch on a value check is a hole in it. -/
def guestImageCodeReq : CodeReq := CodeReq.ofEntries guestImageEntries

/-- End of the guest `.text` (by name, so layout regens flow through). -/
def guestTextEnd : Nat := RegionMap.textRegion.base + RegionMap.textSizeBytes

set_option maxRecDepth 8000 in
/-- The ONE kernel-checked disjointness fact for the whole image: the
    entries' byte extents are ascending and non-overlapping inside
    `.text = [0x80000000, guestTextEnd)`. -/
theorem guestImageEntries_extentsOk :
    CodeReq.extentsOkFrom RegionMap.textRegion.base guestTextEnd
      guestImageEntries = true := by decide

/-- Any linked function's `ofProg` block is subsumed by the image
    `CodeReq` — the monotonicity witness for
    `cpsTripleWithin_extend_code` / `cpsHaltTripleWithin_extend_code`. -/
theorem guestImage_block_sub :
    ∀ e ∈ guestImageEntries, ∀ a i,
      CodeReq.ofProg (BitVec.ofNat 64 e.1) e.2 a = some i →
      guestImageCodeReq a = some i :=
  CodeReq.ofProg_sub_ofEntries_of_extentsOk guestImageEntries_extentsOk
    (by decide)

/-! ## 2. The `GuestFraming` bundle -/

/-- Havoc ownership of one region of the map. -/
def regionScratch (r : RegionMap.GuestRegion) : Assertion :=
  anyBytes (BitVec.ofNat 64 r.base) r.size

/-- The guest's working-state ownership at entry: the **eight** writable
    (`zone = .ram`) regions of the emitted-reality map, ascending —
    `zisk_system ** OUTPUT ** guest_stack ** state_tracker_live **
    .data ** .bss ** .state_gas_diag ** .sszscratch`.  (The `.bss` tile
    contains the `call_frame_arena`; `CallFramePhase.phaseDView` is a
    sub-tile split of it via `anyBytes_add`, so phase-view consumers frame
    out of this same resource.)

    ⚠️ The count in this docstring and in the two below said *eight*, *eight*
    and *six* while the bundle held **seven** tiles (GH #11186). It is eight
    now because `.state_gas_diag` was declared; do not read a matching number
    as evidence that anyone checked it — `guestScratch_matches_regionMap`
    below is what checks it, and it is the only statement here that can fail. -/
def guestScratch : Assertion :=
  regionScratch RegionMap.ziskSystemRegion **
  regionScratch RegionMap.outputRegion **
  regionScratch RegionMap.guestStackRegion **
  regionScratch RegionMap.stateTrackerLiveRegion **
  regionScratch RegionMap.dataRegion **
  regionScratch RegionMap.bssRegion **
  regionScratch RegionMap.stateGasDiagRegion **
  regionScratch RegionMap.sszScratchRegion

/-- Drift pin: the eight tiles of `guestScratch` are EXACTLY the writable
    regions of `guestRegionMap`, in map order.  Adding/renaming a `.ram`
    region breaks this `decide`, forcing the bundle to follow.

    GH #11186 is the worked example: declaring `.state_gas_diag` in
    `RegionMap` broke this `decide` on its own branch, one layer above the
    disjointness and zone-fit theorems that both still passed. Those answer
    *is it disjoint and does it fit*; this one answers *is the writable set
    the one the scratch bundle claims* — a different obligation, and the
    reason a bot must not extend this list: an enumeration that exists to
    catch silent extensions cannot be silently extended. -/
theorem guestScratch_matches_regionMap :
    (RegionMap.guestRegionMap.filter
        fun r => r.zone matches RegionMap.RegionZone.ram).map (·.name)
      = [RegionMap.ziskSystemRegion.name, RegionMap.outputRegion.name,
         RegionMap.guestStackRegion.name,
         RegionMap.stateTrackerLiveRegion.name,
         RegionMap.dataRegion.name, RegionMap.bssRegion.name,
         RegionMap.stateGasDiagRegion.name,
         RegionMap.sszScratchRegion.name] := by
  decide

/-! ### The `scratch_sat` witness

    An explicit heap satisfying `guestInputAssertion input ** guestScratch`
    for every admissible input: the input's dwords live in the model's
    legacy/input zones (`[0x40000008, 0x78000008)` at worst — exactly why
    `MAX_INPUT_BYTES = 0x37FFFFF8`), the eight scratch tiles in the RAM zone
    `[0xa0000000, 0xc0000000)`; all footprints ascend, so the `MemSat`
    combinators chain them. -/

private theorem satWithin_ramRegion (b n : Nat)
    (hb : 0xa0000000 ≤ b) (he : b + n ≤ 0xc0000000)
    (halign : b % 8 = 0) (hn : n % 8 = 0) :
    (anyBytes (BitVec.ofNat 64 b) n).SatWithin b (b + n) := by
  have hbase : (BitVec.ofNat 64 b).toNat = b := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hcount : 8 * ((n + 7) / 8) = n := by omega
  have h := satWithin_anyBytes (BitVec.ofNat 64 b) n (fun k hk => by
    have hlt : (BitVec.ofNat 64 b).toNat + 8 * k < 2 ^ 64 := by omega
    apply isValidDwordAccess_of_toNat
    · rw [toNat_add_ofNat_of_le hlt, hbase]; omega
    · rw [toNat_add_ofNat_of_le hlt, hbase]; right; right; omega)
  rw [hbase, hcount] at h
  exact h

private theorem satWithin_inputLen (input : SpecRef.Bytes) :
    (bytesRegion (INPUT_ADDR + INPUT_LEN_OFFSET)
        (u64LEBytes input.length)).SatWithin 0x40000008 0x40000010 := by
  have h := satWithin_bytesRegion (INPUT_ADDR + INPUT_LEN_OFFSET)
    (u64LEBytes input.length) (fun k hk => by
      rw [u64LEBytes_length] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      decide)
  rw [u64LEBytes_length] at h
  exact h.congr_bounds (by decide) (by decide)

private theorem satWithin_inputBody (input : SpecRef.Bytes)
    (hlen : input.length ≤ MAX_INPUT_BYTES) :
    (bytesRegion (INPUT_ADDR + INPUT_BODY_OFFSET) input).SatWithin
      0x40000010 (0x40000010 + 8 * ((input.length + 7) / 8)) := by
  have hmax : MAX_INPUT_BYTES = 0x37FFFFF8 := rfl
  have hbase : (INPUT_ADDR + INPUT_BODY_OFFSET).toNat = 0x40000010 := by
    decide
  have h := satWithin_bytesRegion (INPUT_ADDR + INPUT_BODY_OFFSET) input
    (fun k hk => by
      have hlt : (INPUT_ADDR + INPUT_BODY_OFFSET).toNat + 8 * k < 2 ^ 64 := by
        rw [hbase]; omega
      apply isValidDwordAccess_of_toNat
      · rw [toNat_add_ofNat_of_le hlt, hbase]; omega
      · rw [toNat_add_ofNat_of_le hlt, hbase]; left
        constructor
        · omega
        · -- last dword: `8·k ≤ 8·(⌈len/8⌉ − 1) ≤ len − 1` rounded to the
          -- dword below; the MAX bound puts it at `MEM_END` exactly.
          omega)
  rw [hbase] at h
  exact h

theorem guestScratch_sat : ∀ input : SpecRef.Bytes,
    input.length ≤ MAX_INPUT_BYTES →
    ∃ h, (guestInputAssertion input ** guestScratch) h := by
  intro input hlen
  have hmax : MAX_INPUT_BYTES = 0x37FFFFF8 := rfl
  -- the input record: `[0x40000008, 0x40000010 + 8·⌈len/8⌉)`
  have hin : (guestInputAssertion input).SatWithin
      0x40000008 (0x40000010 + 8 * ((input.length + 7) / 8)) :=
    (satWithin_inputLen input).sepConj (satWithin_inputBody input hlen)
      (by omega) (by omega)
  -- The eight RAM tiles, ascending. Numbering is t1..t4, t6..t8 plus t7b:
  -- there is no t5, and the gap is historical rather than meaningful. Count
  -- the `have`s, not the names (GH #11186).
  have t1 : (regionScratch RegionMap.ziskSystemRegion).SatWithin
      0xa0000000 0xa0010000 :=
    satWithin_ramRegion 0xa0000000 0x10000 (by omega) (by omega)
      (by omega) (by omega)
  have t2 : (regionScratch RegionMap.outputRegion).SatWithin
      0xa0010000 0xa0020000 :=
    satWithin_ramRegion 0xa0010000 0x10000 (by omega) (by omega)
      (by omega) (by omega)
  have t3 : (regionScratch RegionMap.guestStackRegion).SatWithin
      0xa0020000 0xa0050000 :=
    satWithin_ramRegion 0xa0020000 0x30000 (by omega) (by omega)
      (by omega) (by omega)
  have t4 : (regionScratch RegionMap.stateTrackerLiveRegion).SatWithin
      0xa0830000 0xa0a30000 :=
    satWithin_ramRegion 0xa0830000 0x200000 (by omega) (by omega)
      (by omega) (by omega)
  -- Link pins are `abbrev` from RegionMapLinkPins (#11230). Use `decide` (not
  -- omega) so inequalities reduce through abbrevs; no hand-typed end/size hex.
  have t6 : (regionScratch RegionMap.dataRegion).SatWithin
      0xa0b00000 (0xa0b00000 + RegionMap.dataSizeBytes) := by
    dsimp [regionScratch, RegionMap.dataRegion, RegionMap.dataSizeBytes,
      RegionMapLinkPins.dataSizeBytes]
    apply satWithin_ramRegion <;> decide
  have t7 : (regionScratch RegionMap.bssRegion).SatWithin
      0xa0b70000 (0xa0b70000 + RegionMap.bssSizeBytes) := by
    dsimp [regionScratch, RegionMap.bssRegion, RegionMap.bssSizeBytes,
      RegionMapLinkPins.bssSizeBytes]
    apply satWithin_ramRegion <;> decide
  have t7' : (regionScratch RegionMap.bssRegion).SatWithin
      (0xa0b00000 + RegionMap.dataSizeBytes) (0xa0b70000 + RegionMap.bssSizeBytes) :=
    t7.mono (by decide) (le_refl _)
  -- GH #11186: `.state_gas_diag` is linker-placed immediately after `.bss`, so
  -- its base IS `t7`'s upper bound, and this join needs no `mono` widening —
  -- but ONLY because the base is DERIVED as `0xa0b70000 + bssSizeBytes` and the
  -- two bounds are therefore the SAME TERM. While it was an independent pin the
  -- join typechecked only because the two `abbrev`s reduced to the same numeral;
  -- when `bssSizeBytes` moved, that coincidence ended and CI failed here with an
  -- application type mismatch.
  --
  -- `t8.mono` below is a DIFFERENT case and stays: `.state_gas_diag` ends well
  -- below `.sszscratch`'s base, so that hop crosses a genuine gap and must be
  -- widened. Pins are `abbrev`, hence `decide` not `omega`; alignment holds
  -- structurally (`.balign 8` in its emitter).
  have t7b : (regionScratch RegionMap.stateGasDiagRegion).SatWithin
      (0xa0b70000 + RegionMap.bssSizeBytes)
      (0xa0b70000 + RegionMap.bssSizeBytes + RegionMap.stateGasDiagSizeBytes) := by
    dsimp [regionScratch, RegionMap.stateGasDiagRegion,
      RegionMap.stateGasDiagBase, RegionMap.stateGasDiagSizeBytes,
      RegionMap.bssSizeBytes, RegionMapLinkPins.bssSizeBytes,
      RegionMapLinkPins.stateGasDiagSizeBytes]
    apply satWithin_ramRegion <;> decide
  have t8 : (regionScratch RegionMap.sszScratchRegion).SatWithin
      0xbf980000 0xc0000000 :=
    satWithin_ramRegion 0xbf980000 0x680000 (by decide) (by decide)
      (by decide) (by decide)
  have hs : guestScratch.SatWithin 0xa0000000 0xc0000000 :=
    t1.sepConj
      (t2.sepConj
        (t3.sepConj
          ((t4.mono (by decide) (by decide)).sepConj
            (t6.sepConj
              (t7'.sepConj
                (t7b.sepConj
                  (t8.mono (by decide) (le_refl _))
                  (by decide) (by decide))
                (by decide) (by decide))
              (by decide) (by decide))
            (by decide) (by decide))
          (by decide) (by decide))
        (by decide) (by decide))
      (by decide) (by decide)
  -- the input footprint tops out at 0x78000008 ≤ 0xa0000000
  have hall := (hin.mono (le_refl _) (show
      0x40000010 + 8 * ((input.length + 7) / 8) ≤ 0xa0000000 by omega)).sepConj
    hs (by omega) (by omega)
  exact hall.sat

/-! ### Register ownership at the guest boundary

    `guestImageCodeReq` does not yet include the unconverted `_start` shell
    (`0x80000000..0x80001948`, 6472 B per `scripts/guest_image_coverage.py`);
    the linked-image coverage therefore cannot certify a whole-image clobber
    set.  The boundary ABI is nevertheless explicit in `Layout.lean`: the
    `sp1` stub writes `x5`, while the `linux93` stub writes `x17` and `x10`.
    The framing bundle owns `x5`, `x10` and `x17`: `x5` is written by the
    guest body and by `sp1`, while `x17` and `x10` are written by `linux93`.
    The verified clean-halt predicate constrains only `x5`, so the syscall
    selector is still a load-bearing owned register at this boundary.  The
    remaining `_start` clobber accounting is the inherited
    `.64`/#12166 residual, not silently discharged here. -/

private def RegFree (P : Assertion) (r : Reg) : Prop :=
  ∀ h, P h → h.regs r = none

private theorem bytesRegionAux_regFree (r : Reg) :
    ∀ (n : Nat) (base : Word) (bs : List (BitVec 8)),
      RegFree (bytesRegionAux base n bs) r := by
  intro n
  induction n with
  | zero => intro base bs h hh; rw [hh]; rfl
  | succ m ih =>
    intro base bs h hh
    obtain ⟨h1, h2, _, hunion, hp1, hp2⟩ := hh
    have e1 : h1.regs r = none := by rw [hp1.1]; rfl
    have e2 : h2.regs r = none := ih (base + 8) (bs.drop 8) h2 hp2
    rw [← hunion]
    simp [PartialState.union, e1, e2]

private theorem bytesRegion_regFree (r : Reg) (base : Word)
    (bs : List (BitVec 8)) : RegFree (bytesRegion base bs) r :=
  bytesRegionAux_regFree r _ base bs

private theorem anyBytes_regFree (r : Reg) (base : Word) (n : Nat) :
    RegFree (anyBytes base n) r := by
  rintro h ⟨bs, _, hb⟩
  exact bytesRegion_regFree r base bs h hb

private theorem sepConj_regFree {P Q : Assertion} {r : Reg}
    (hP : RegFree P r) (hQ : RegFree Q r) : RegFree (P ** Q) r := by
  rintro h ⟨h1, h2, _, hunion, hp1, hp2⟩
  rw [← hunion]
  simp [PartialState.union, hP h1 hp1, hQ h2 hp2]

private theorem guestInput_regFree (input : SpecRef.Bytes) (r : Reg) :
    RegFree (guestInputAssertion input) r := by
  unfold guestInputAssertion
  exact sepConj_regFree (bytesRegion_regFree _ _ _)
    (bytesRegion_regFree _ _ _)

private theorem guestScratch_regFree (r : Reg) : RegFree guestScratch r := by
  unfold guestScratch regionScratch
  exact sepConj_regFree (anyBytes_regFree _ _ _)
    (sepConj_regFree (anyBytes_regFree _ _ _)
      (sepConj_regFree (anyBytes_regFree _ _ _)
        (sepConj_regFree (anyBytes_regFree _ _ _)
          (sepConj_regFree (anyBytes_regFree _ _ _)
            (sepConj_regFree (anyBytes_regFree _ _ _)
              (sepConj_regFree (anyBytes_regFree _ _ _)
                (anyBytes_regFree _ _ _)))))))

private theorem singletonReg_disjoint_regFree {P : Assertion} {r : Reg}
    {v : Word} {h : PartialState} (hfree : RegFree P r) (hp : P h) :
    (PartialState.singletonReg r v).Disjoint h := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r'
  by_cases hrr : r' = r
  · exact Or.inr (hrr ▸ hfree h hp)
  · exact Or.inl (by simp [PartialState.singletonReg, hrr])

private theorem singletonReg_disjoint_singletonReg {r1 r2 : Reg}
    {v1 v2 : Word} (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint
      (PartialState.singletonReg r2 v2) := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r
  by_cases hr : r = r1
  · exact Or.inr (by simp [PartialState.singletonReg, hr, hne])
  · exact Or.inl (by simp [PartialState.singletonReg, hr])

private theorem singletonReg_disjoint_union {h1 h2 h3 : PartialState}
    (hd12 : h1.Disjoint h2) (hd13 : h1.Disjoint h3) :
    h1.Disjoint (h2.union h3) := by
  obtain ⟨hr12, hm12, hc12, hpc12, hpv12, hpi12, hib12⟩ := hd12
  obtain ⟨hr13, hm13, hc13, hpc13, hpv13, hpi13, hib13⟩ := hd13
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    rcases hr12 r with h1none | h2none
    · exact Or.inl h1none
    · rcases hr13 r with h1none | h3none
      · exact Or.inl h1none
      · exact Or.inr (by simp [PartialState.union, h2none, h3none])
  · intro a
    rcases hm12 a with h1none | h2none
    · exact Or.inl h1none
    · rcases hm13 a with h1none | h3none
      · exact Or.inl h1none
      · exact Or.inr (by simp [PartialState.union, h2none, h3none])
  · intro a
    rcases hc12 a with h1none | h2none
    · exact Or.inl h1none
    · rcases hc13 a with h1none | h3none
      · exact Or.inl h1none
      · exact Or.inr (by simp [PartialState.union, h2none, h3none])
  · rcases hpc12 with h1none | h2none
    · exact Or.inl h1none
    · rcases hpc13 with h1none | h3none
      · exact Or.inl h1none
      · exact Or.inr (by simp [PartialState.union, h2none, h3none])
  · rcases hpv12 with h1none | h2none
    · exact Or.inl h1none
    · rcases hpv13 with h1none | h3none
      · exact Or.inl h1none
      · exact Or.inr (by simp [PartialState.union, h2none, h3none])
  · rcases hpi12 with h1none | h2none
    · exact Or.inl h1none
    · rcases hpi13 with h1none | h3none
      · exact Or.inl h1none
      · exact Or.inr (by simp [PartialState.union, h2none, h3none])
  · rcases hib12 with h1none | h2none
    · exact Or.inl h1none
    · rcases hib13 with h1none | h3none
      · exact Or.inl h1none
      · exact Or.inr (by simp [PartialState.union, h2none, h3none])

private theorem guestScratch_with_registers_sat : ∀ input : SpecRef.Bytes,
    input.length ≤ MAX_INPUT_BYTES →
    ∃ h, (guestInputAssertion input **
      (regOwn .x5 ** (regOwn .x10 ** (regOwn .x17 ** guestScratch)))) h := by
  intro input hlen
  obtain ⟨h, hp⟩ := guestScratch_sat input hlen
  obtain ⟨hi, hm, hdim, huim, hip, hmp⟩ := hp
  let h5 := PartialState.singletonReg .x5 (0 : Word)
  let h10 := PartialState.singletonReg .x10 (0 : Word)
  let h17 := PartialState.singletonReg .x17 (0 : Word)
  have hd5i : h5.Disjoint hi :=
    singletonReg_disjoint_regFree
      (guestInput_regFree input .x5) hip
  have hd10i : h10.Disjoint hi :=
    singletonReg_disjoint_regFree
      (guestInput_regFree input .x10) hip
  have hd17i : h17.Disjoint hi :=
    singletonReg_disjoint_regFree
      (guestInput_regFree input .x17) hip
  have hd5m : h5.Disjoint hm :=
    singletonReg_disjoint_regFree (guestScratch_regFree .x5) hmp
  have hd10m : h10.Disjoint hm :=
    singletonReg_disjoint_regFree (guestScratch_regFree .x10) hmp
  have hd17m : h17.Disjoint hm :=
    singletonReg_disjoint_regFree (guestScratch_regFree .x17) hmp
  have hd510 : h5.Disjoint h10 := by
    exact singletonReg_disjoint_singletonReg (by decide)
  have hd517 : h5.Disjoint h17 := by
    exact singletonReg_disjoint_singletonReg (by decide)
  have hd1017 : h10.Disjoint h17 := by
    exact singletonReg_disjoint_singletonReg (by decide)
  have hd10_17m : h10.Disjoint (h17.union hm) :=
    singletonReg_disjoint_union hd1017 hd10m
  have hd5_17m : h5.Disjoint (h17.union hm) :=
    singletonReg_disjoint_union hd517 hd5m
  have hd5_10_17m : h5.Disjoint (h10.union (h17.union hm)) :=
    singletonReg_disjoint_union hd510 hd5_17m
  have hdim17m : hi.Disjoint (h17.union hm) :=
    singletonReg_disjoint_union hd17i.symm hdim
  have hdim10_17m : hi.Disjoint (h10.union (h17.union hm)) :=
    singletonReg_disjoint_union hd10i.symm hdim17m
  have hdim51017 : hi.Disjoint (h5.union (h10.union (h17.union hm))) :=
    singletonReg_disjoint_union hd5i.symm hdim10_17m
  refine ⟨hi.union (h5.union (h10.union (h17.union hm))), ?_⟩
  refine ⟨hi, h5.union (h10.union (h17.union hm)), hdim51017, rfl, hip, ?_⟩
  refine ⟨h5, h10.union (h17.union hm), hd5_10_17m, rfl, ?_, ?_⟩
  · exact ⟨0, rfl⟩
  · refine ⟨h10, h17.union hm, hd10_17m, rfl, ⟨0, rfl⟩, ?_⟩
    exact ⟨h17, hm, hd17m, rfl, ⟨0, rfl⟩, hmp⟩

/-! ### The residue: `guestScratch` minus the observation window

    The top Props place the OUTPUT claim in STRICT separation with the
    residue (`guestOutputSound execute input ** fr.residue`), and
    `guestOutputSound` itself owns the `OUTPUT_CLAIM_BYTES`-byte window's
    dwords (the pinned length that closes the #9734 ∃-out vacuity hole —
    "the observation window is deliberately NOT allowed to hide in
    `residue`", EntrySpec.lean). So the residue must NOT re-own the
    window: it carves the first `OUTPUT_CLAIM_BYTES` bytes out of the
    OUTPUT tile and keeps only the tail, so that
    `guestOutputSound ** guestResidue` re-tiles the OUTPUT region
    exactly. (Found in the #9785 review: `residue := guestScratch`
    over-owned the window and made the `.64` post unsatisfiable.)

    NOTE (`runStatelessGuestFaithful`): the faithful Prop's window is the
    full input-dependent `serialize_stateless_output` byte string, wider
    than `OUTPUT_CLAIM_BYTES` and not constant across inputs, so THIS
    residue serves the soundness Prop only — the faithful follow-up
    needs its own carve (it is a stated `.64` v1 non-goal). -/

/-- The OUTPUT region above the observation window: havoc ownership of
    `[OUTPUT_ADDR + OUTPUT_CLAIM_BYTES, OUTPUT_ADDR + size)`. -/
def outputTailScratch : Assertion :=
  anyBytes
    (BitVec.ofNat 64 RegionMap.outputRegion.base +
      BitVec.ofNat 64 OUTPUT_CLAIM_BYTES)
    (RegionMap.outputRegion.size - OUTPUT_CLAIM_BYTES)

/-- Carve the OUTPUT entry tile at the (dword-aligned) claim boundary:
    entry tile = observation window ++ tail. `.64` uses this to convert
    `guestScratch`'s OUTPUT ownership into
    `anyBytes OUTPUT_ADDR OUTPUT_CLAIM_BYTES ** outputTailScratch`, hand
    the window to `guestOutputSound`, and drop the tail into the
    residue. -/
theorem regionScratch_output_carve :
    regionScratch RegionMap.outputRegion =
      (anyBytes (BitVec.ofNat 64 RegionMap.outputRegion.base)
          OUTPUT_CLAIM_BYTES **
        outputTailScratch) := by
  show anyBytes (BitVec.ofNat 64 RegionMap.outputRegion.base)
      RegionMap.outputRegion.size = _
  rw [show RegionMap.outputRegion.size
        = OUTPUT_CLAIM_BYTES +
            (RegionMap.outputRegion.size - OUTPUT_CLAIM_BYTES) from by decide]
  exact EvmAsm.Rv64.SAsm.anyBytes_add _ _ _ (by decide)

/-- The halt-state residue: the **eight**-region havoc with the observation
    window carved out of the OUTPUT tile.

    ⚠️ This is the FOURTH place the tile list is written out by hand, after
    `guestScratch`, `guestScratch_matches_regionMap` and `guestScratch_sat`'s
    `t`-chain. GH #11186: only the second of those is a `decide` that names the
    omission; this one fails as `unsolved goals` on the retiling identity below,
    which is loud but does not say *which* tile is missing. If you add a `.ram`
    region, expect to edit all four. -/
def guestResidue : Assertion :=
  regionScratch RegionMap.ziskSystemRegion **
  outputTailScratch **
  regionScratch RegionMap.guestStackRegion **
  regionScratch RegionMap.stateTrackerLiveRegion **
  regionScratch RegionMap.dataRegion **
  regionScratch RegionMap.bssRegion **
  regionScratch RegionMap.stateGasDiagRegion **
  regionScratch RegionMap.sszScratchRegion

/-- **The retiling identity `.64` consumes**: the entry scratch is
    exactly the observation window alongside the residue, so the halt
    post `guestOutputSound ** guestResidue` accounts for precisely the
    entry-owned work regions (window ownership moves from the havoc'd
    entry tile into `guestOutputSound`'s pinned-length `bytesRegion`). -/
theorem guestScratch_eq_window_residue :
    guestScratch =
      (anyBytes (BitVec.ofNat 64 RegionMap.outputRegion.base)
          OUTPUT_CLAIM_BYTES **
        guestResidue) := by
  unfold guestScratch guestResidue
  rw [regionScratch_output_carve, sepConj_assoc',
    ← sepConj_assoc' (regionScratch RegionMap.ziskSystemRegion),
    sepConj_comm' (regionScratch RegionMap.ziskSystemRegion),
    sepConj_assoc']

/-- **The `.63` framing bundle**: `scratch` = the eight-region havoc (the
    guest owns the FULL OUTPUT region at entry), `residue` = the same
    havoc minus the observation window (which `guestOutputSound` owns in
    the post — see the carve note above), with the non-vacuity
    witness. -/
def guestFraming : GuestFraming where
  scratch := regOwn .x5 ** (regOwn .x10 ** (regOwn .x17 ** guestScratch))
  residue := regOwn .x5 ** (regOwn .x10 ** (regOwn .x17 ** guestResidue))
  scratch_sat := guestScratch_with_registers_sat

end EvmAsm.Codegen
