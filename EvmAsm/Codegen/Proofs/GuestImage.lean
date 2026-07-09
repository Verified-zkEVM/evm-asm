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
    of `anyBytes` havoc over the six writable (`zone = .ram`) regions of
    `RegionMap.guestRegionMap` (`guestScratch_matches_regionMap` pins the
    bundle to the map, so a region-map change breaks the build here), with
    the `scratch_sat` non-vacuity witness built from the `Rv64.MemSat`
    footprint combinators.

  This file lives Codegen-side because both artifacts need Codegen
  (`GuestAddrs`, the `_prog`s, `RegionMap`) and Codegen is a pure layering
  sink — `Stateless/EntrySpec.lean` stays Codegen-free.
-/

import EvmAsm.Rv64.CodeReqExtents
import EvmAsm.Rv64.MemSat
import EvmAsm.Codegen.Proofs.GuestImageEntries
import EvmAsm.Codegen.RegionMap
import EvmAsm.Stateless.EntrySpec

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm (anyBytes)
open EvmAsm.Stateless

/-! ## 1. The guest-image `CodeReq` -/

/-- The guest image's code requirement: every linked converted `_prog`
    pinned at its `GuestAddrs` entry (see `guestImageEntries`). -/
def guestImageCodeReq : CodeReq := CodeReq.ofEntries guestImageEntries

/-- End of the guest `.text` (by name, so layout regens flow through). -/
def guestTextEnd : Nat := RegionMap.textRegion.base + RegionMap.textSizeBytes

set_option maxRecDepth 100000 in
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

/-- The guest's working-state ownership at entry: the six writable
    (`zone = .ram`) regions of the emitted-reality map, ascending —
    `zisk_system ** OUTPUT ** guest_stack ** state_tracker_live **
    .data ** .sszscratch`.  (The `.data` tile contains the
    `call_frame_arena`; `CallFramePhase.phaseDView` is a sub-tile split
    of it via `anyBytes_add`, so phase-view consumers frame out of this
    same resource.) -/
def guestScratch : Assertion :=
  regionScratch RegionMap.ziskSystemRegion **
  regionScratch RegionMap.outputRegion **
  regionScratch RegionMap.guestStackRegion **
  regionScratch RegionMap.stateTrackerLiveRegion **
  regionScratch RegionMap.dataRegion **
  regionScratch RegionMap.sszScratchRegion

/-- Drift pin: the six tiles of `guestScratch` are EXACTLY the writable
    regions of `guestRegionMap`, in map order.  Adding/renaming a `.ram`
    region breaks this `decide`, forcing the bundle to follow. -/
theorem guestScratch_matches_regionMap :
    (RegionMap.guestRegionMap.filter
        fun r => r.zone matches RegionMap.RegionZone.ram).map (·.name)
      = [RegionMap.ziskSystemRegion.name, RegionMap.outputRegion.name,
         RegionMap.guestStackRegion.name,
         RegionMap.stateTrackerLiveRegion.name,
         RegionMap.dataRegion.name, RegionMap.sszScratchRegion.name] := by
  decide

/-! ### The `scratch_sat` witness

    An explicit heap satisfying `guestInputAssertion input ** guestScratch`
    for every admissible input: the input's dwords live in the model's
    legacy/input zones (`[0x40000008, 0x78000008)` at worst — exactly why
    `MAX_INPUT_BYTES = 0x37FFFFF8`), the six scratch tiles in the RAM zone
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
  -- the six RAM tiles, ascending
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
      0xa0630000 0xa0830000 :=
    satWithin_ramRegion 0xa0630000 0x200000 (by omega) (by omega)
      (by omega) (by omega)
  have t5 : (regionScratch RegionMap.dataRegion).SatWithin
      0xa3000000 0xbc5a26d0 :=
    satWithin_ramRegion 0xa3000000 0x195a26d0 (by omega) (by omega)
      (by omega) (by omega)
  have t6 : (regionScratch RegionMap.sszScratchRegion).SatWithin
      0xbf500000 0xbfb80000 :=
    satWithin_ramRegion 0xbf500000 0x680000 (by omega) (by omega)
      (by omega) (by omega)
  have hs : guestScratch.SatWithin 0xa0000000 0xbfb80000 :=
    t1.sepConj
      (t2.sepConj
        (t3.sepConj
          ((t4.mono (by omega) (by omega)).sepConj
            (t5.sepConj (t6.mono (by omega) (le_refl _))
              (by omega) (by omega))
            (by omega) (by omega))
          (by omega) (by omega))
        (by omega) (by omega))
      (by omega) (by omega)
  -- the input footprint tops out at 0x78000008 ≤ 0xa0000000
  have hall := (hin.mono (le_refl _) (show
      0x40000010 + 8 * ((input.length + 7) / 8) ≤ 0xa0000000 by omega)).sepConj
    hs (by omega) (by omega)
  exact hall.sat

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

/-- The halt-state residue: the six-region havoc with the observation
    window carved out of the OUTPUT tile. -/
def guestResidue : Assertion :=
  regionScratch RegionMap.ziskSystemRegion **
  outputTailScratch **
  regionScratch RegionMap.guestStackRegion **
  regionScratch RegionMap.stateTrackerLiveRegion **
  regionScratch RegionMap.dataRegion **
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

/-- **The `.63` framing bundle**: `scratch` = the six-region havoc (the
    guest owns the FULL OUTPUT region at entry), `residue` = the same
    havoc minus the observation window (which `guestOutputSound` owns in
    the post — see the carve note above), with the non-vacuity
    witness. -/
def guestFraming : GuestFraming where
  scratch := guestScratch
  residue := guestResidue
  scratch_sat := guestScratch_sat

end EvmAsm.Codegen
