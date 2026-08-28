/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakEnvelope

  Witnesses for the keccak **envelope seam** (GH #13014).

  `zkvm_keccak256_spec_within` demands its input as one *exactly-sized*
  `bytesRegion inputBase input`.  Two facts make that unobtainable for a caller
  that hashes an interior slice of a buffer it already owns:

  1. No carving lemma applies when the slice length is not a multiple of 8.
     `bytesRegion_append` needs `8 ∣ xs.length`, `bytesRegion_split` needs
     `n % 8 = 0`, `bytesRegion_window_focus` needs both cut points aligned; and
     `bytesRegion_window_focus_any` deliberately hands back the **dword
     envelope** (`windowDwordLen off 20 = 24`), not the 20-byte slice.

  2. A sub-dword-length region pins the trailing bytes to zero.
     `bytesRegion base bs = bytesRegionAux base ((bs.length + 7) / 8) bs`
     (`Rv64/MemRegion.lean`), so 20 bytes own three dwords and the third is
     `base + 16 ↦ₘ packBytes (bs.drop 16)` over a four-element list, which
     `packBytes` zero-pads through `getByteAt`.  So `bytesRegion addr addr20`
     *asserts that the four buffer bytes following the address are `0x00`* — a
     content claim about the physical cell, not resource framing.

  `zkvm_keccak256_spec_within_envelope` (in `HashBridgeKeccakTop`) removes the
  assumption: its input region need only be **at least** `136*N + rem` bytes
  long, and the digest depends on the first `136*N + rem` bytes alone
  (`keccakBodyDigest_congr` / `keccakBodyDigest_append`).

  This file carries the evidence that the fix is real and not vacuous:

  * `envelope_region_sat` — a satisfiable instance: a genuine heap for the
    24-byte envelope of a 20-byte address whose four trailing bytes are the
    **nonzero** `0xc0 0x01 0x02 0x03` (an RLP list header, what actually
    follows the address inside a BAL `AccountChanges` item).
  * `exactRegion_false_on_nonzero_tail` — the **negative control**: on that very
    heap the exactly-sized `bytesRegion base addr20` is FALSE, because it pins
    the shared dword to a different value.  Re-introducing the zero-padding
    assumption would make this theorem unprovable.
  * `envelope_digest_ignores_tail` — the digest is unchanged by that nonzero
    tail.
  * `addrSlice_envelope_focus` / `balAccountPath_keccak_call_available` — the
    consumer's obstruction is gone: the dword envelope that
    `bytesRegion_window_focus_any` hands back from the caller's arena is
    exactly the seam's input resource, and the resulting keccak call site
    carries **no** hypothesis about the bytes following the address.
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakTop
import EvmAsm.Rv64.MemSat
import EvmAsm.Rv64.SAsm.BytesRegionWindow

-- ⚠️ Deliberately off (same reason as `NodeDbAppendSpec`): keccak's scratch
-- base `Zk3` is `private` in `HashBridgeKeccakTop`, and a bare occurrence would
-- otherwise be auto-bound as a fresh universally quantified `Word`, silently
-- turning a claim about the scratch arena into a claim about an arbitrary one.
set_option autoImplicit false

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

open private Zk3 B keccakCr from EvmAsm.Codegen.Proofs.HashBridgeKeccakTop

/-! ## §1  Non-vacuity: a heap with a **nonzero** trailing tail

    The base is an ordinary aligned RAM address in the first valid dword zone
    (`0x20 … 0x78000000`); it is not a layout constant and names nothing. -/

/-- Aligned base for the witness heaps. -/
private abbrev envBase : Word := BitVec.ofNat 64 0x1000

/-- A 20-byte account address. -/
def bacpAddr20 : List (BitVec 8) :=
  [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa,
   0xbb, 0xcc, 0xdd, 0xee, 0xff, 0x01, 0x02, 0x03, 0x04, 0x05]

/-- The four buffer bytes that follow the address inside the caller's RLP
    buffer.  In a well-formed `AccountChanges` these are the head of
    `storage_changes` — a list header, so `≥ 0xc0`.  **Nonzero**: this is the
    data the old, exactly-sized seam wrongly required to be `0x00`. -/
def bacpTail4 : List (BitVec 8) := [0xc0, 0x01, 0x02, 0x03]

theorem bacpAddr20_length : bacpAddr20.length = 20 := by decide

theorem bacpTail4_length : bacpTail4.length = 4 := by decide

/-- Both regions own exactly three dwords: `⌈20/8⌉ = ⌈24/8⌉ = 3`. -/
theorem bacp_dword_counts :
    (bacpAddr20.length + 7) / 8 = 3 ∧
      ((bacpAddr20 ++ bacpTail4).length + 7) / 8 = 3 := by decide

/-- The shared third dword is pinned to **different** values by the two
    regions: the envelope carries the real buffer bytes, the exactly-sized
    region zero-pads them.  This is the content of #13014, kernel-checked. -/
theorem bacp_dword2_differs :
    packBytes ((((bacpAddr20 ++ bacpTail4).drop 8).drop 8).take 8)
      ≠ packBytes (((bacpAddr20.drop 8).drop 8).take 8) := by decide

/-- Read the third dword cell off any heap satisfying a three-dword region at
    `envBase`.  Every atom of `bytesRegion` is exact ownership (`memIs a v h`
    means `h = singletonMem a v`), so the cell's value is determined. -/
private theorem mem_dword2_of_bytesRegion (bs : List (BitVec 8))
    (hn : (bs.length + 7) / 8 = 3) (h : PartialState)
    (hp : bytesRegion envBase bs h) :
    h.mem (envBase + 8 + 8) = some (packBytes (((bs.drop 8).drop 8).take 8)) := by
  have hp' : ((envBase ↦ₘ packBytes (bs.take 8)) **
      ((envBase + 8) ↦ₘ packBytes ((bs.drop 8).take 8)) **
      ((envBase + 8 + 8) ↦ₘ packBytes (((bs.drop 8).drop 8).take 8)) **
      empAssertion) h := by
    unfold bytesRegion at hp
    rw [hn] at hp
    exact hp
  obtain ⟨h1, h2, -, rfl, hp1, hp2⟩ := hp'
  obtain ⟨h3, h4, -, rfl, hp3, hp4⟩ := hp2
  obtain ⟨h5, h6, -, rfl, hp5, hp6⟩ := hp4
  obtain ⟨rfl, -⟩ := hp1
  obtain ⟨rfl, -⟩ := hp3
  obtain ⟨rfl, -⟩ := hp5
  subst hp6
  simp [PartialState.union, PartialState.singletonMem, PartialState.empty,
    show ((envBase + 8 + 8 : Word) == envBase) = false from by decide,
    show ((envBase + 8 + 8 : Word) == envBase + 8) = false from by decide]

/-- **Satisfiable instance.**  The envelope region — 20 address bytes plus a
    nonzero four-byte tail — is satisfied by a real heap. -/
theorem envelope_region_sat :
    ∃ h, bytesRegion envBase (bacpAddr20 ++ bacpTail4) h :=
  (satWithin_bytesRegion envBase (bacpAddr20 ++ bacpTail4)
    (by
      intro k hk
      rw [show ((bacpAddr20 ++ bacpTail4).length + 7) / 8 = 3 from by decide] at hk
      interval_cases k <;> decide)).sat

/-- **Negative control.**  On a heap satisfying the envelope with a *nonzero*
    trailing tail, the exactly-sized 20-byte region is FALSE: it would pin the
    shared third dword to the zero-padded value.  So the old seam's input
    resource genuinely cannot be produced there — and any accidental
    re-introduction of the zero-padding assumption would break this proof. -/
theorem exactRegion_false_on_nonzero_tail (h : PartialState)
    (henv : bytesRegion envBase (bacpAddr20 ++ bacpTail4) h) :
    ¬ bytesRegion envBase bacpAddr20 h := by
  intro hex
  have h1 := mem_dword2_of_bytesRegion _ (by decide) h henv
  have h2 := mem_dword2_of_bytesRegion _ (by decide) h hex
  rw [h1] at h2
  exact bacp_dword2_differs (Option.some.inj h2)

/-- The old seam's length hypothesis fails on exactly this data (`24 ≠ 20`),
    while the new seam's fits (`20 ≤ 24`). -/
theorem envelope_fit_but_not_exact :
    (bacpAddr20 ++ bacpTail4).length ≠ keccakAbsorbStep * 0 + 20 ∧
      keccakAbsorbStep * 0 + 20 ≤ (bacpAddr20 ++ bacpTail4).length := by
  decide

/-- The nonzero tail does not reach the digest. -/
theorem envelope_digest_ignores_tail :
    keccakBodyDigest (bacpAddr20 ++ bacpTail4) 0 20
      = keccakBodyDigest bacpAddr20 0 20 :=
  keccakBodyDigest_append bacpAddr20 bacpTail4 0 20 (by decide)

/-! ## §2  The consumer's obstruction is gone

    `bal_account_path` hashes the 20-byte address **in place**, inside the
    caller's RLP buffer (`.SUB .x10 .x10 .x12` at instruction index 12: cursor
    minus field length is the address start).  Its arena resource is
    `bytesRegion arenaBase ws`; the address sits at some offset `off` in it. -/

private theorem wstart_of_aligned (off : Nat) (h8 : off % 8 = 0) :
    windowDwordStart off = off := by
  unfold windowDwordStart; omega

private theorem wlen20_of_aligned (off : Nat) (h8 : off % 8 = 0) :
    windowDwordLen off 20 = 24 := by
  unfold windowDwordLen; omega

/-- The caller's arena carves into (dword envelope of the address slice) ⋆ rest
    with **no** hypothesis about the bytes following the address — only the
    alignment of the slice start and the arena's length. -/
theorem addrSlice_envelope_focus (arenaBase : Word) (ws : List (BitVec 8))
    (off : Nat) (h8 : off % 8 = 0) (hfit : off + 24 ≤ ws.length) :
    bytesRegion arenaBase ws
      = (bytesRegion (arenaBase + BitVec.ofNat 64 off) ((ws.drop off).take 24)
          ** windowRestAny arenaBase ws off 20) := by
  have hend : windowDwordEnd off 20 ≤ ws.length := by
    unfold windowDwordEnd windowDwordStart windowDwordLen; omega
  have hfoc := bytesRegion_window_focus_any arenaBase ws off 20 hend
  unfold bytesRegionWindow at hfoc
  rw [wstart_of_aligned off h8, wlen20_of_aligned off h8] at hfoc
  exact hfoc

/-- …and the digest of that envelope is the digest of the 20 address bytes. -/
theorem addrSlice_digest_envelope (ws : List (BitVec 8)) (off : Nat) :
    keccakBodyDigest ((ws.drop off).take 24) 0 20
      = keccakBodyDigest ((ws.drop off).take 20) 0 20 := by
  refine keccakBodyDigest_congr _ _ 0 20 ?_
  simp only [show keccakAbsorbStep * 0 + 20 = 20 from by decide,
    List.take_take]
  norm_num

/-- **The obstruction is gone.**  A `bal_account_path`-shaped call site: the
    keccak input resource is the dword envelope of the in-place 20-byte address
    slice, and the only hypothesis about the caller's buffer is `hslice`, a
    *length* fact.  Nothing here says the four bytes after the address are
    `0x00` — the claim the exactly-sized seam forced and no real BAL caller
    could discharge.

    (This is a call-site availability witness, not `bal_account_path`'s own
    registry triple; that belongs to the #12318 lane.) -/
theorem balAccountPath_keccak_call_available
    (sp0 ret : Word) (arenaBase : Word) (off : Nat) (outputBase : Word)
    (ws out0 os : List (BitVec 8))
    (v8 v9 v18 v20 v28 v29 : Word) (A : Assertion) (hA : A.pcFree)
    (halign_ret : (ret &&& ~~~(1 : Word)) = ret)
    (hslice : off + 24 ≤ ws.length)
    (hout0 : out0.length = 32)
    (hos : os.length = 200)
    (halign_zk : Zk3.toNat % 8 = 0)
    (hover : Zk3.toNat + 200 < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor (arenaBase + BitVec.ofNat 64 off) 0).toNat % 8 = 0)
    (hovers : ∀ n, n < 20 → Zk3.toNat + (20 - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < 20 →
      (keccakAbsorbCursor (arenaBase + BitVec.ofNat 64 off) 0).toNat
        + (20 - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < 20 →
      isValidByteAccess (Zk3 + BitVec.ofNat 64 (20 - (n + 1))) = true)
    (hvalidi : ∀ n, n < 20 →
      isValidByteAccess
        (keccakAbsorbCursor (arenaBase + BitVec.ofNat 64 off) 0
          + BitVec.ofNat 64 (20 - (n + 1))) = true)
    (hvalidRem : isValidByteAccess (Zk3 + BitVec.ofNat 64 20) = true)
    (hvalid135 : isValidByteAccess (Zk3 + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr (Zk3 + BitVec.ofNat 64 j) = true) :
    let addrEnv := (ws.drop off).take 24
    let inputBase := arenaBase + BitVec.ofNat 64 off
    let vals := keccakEntryVals v8 v9 v18 v20
    let lenW := BitVec.ofNat 64 (keccakAbsorbStep * 0 + 20)
    let newSp := sp0 + signExtend12 ((-32 : BitVec 12))
    cpsTripleWithin (5 + keccakBodyFuel 0 20 + 6) B ret keccakCr
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals **
        frameSlotsOwn keccakFrame newSp **
        keccakCallerPre inputBase lenW outputBase v28 v29 os addrEnv out0 A)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals **
        frameSlotsSaved keccakFrame newSp vals **
        keccakCallerPost inputBase outputBase addrEnv 0 20 A) := by
  intro addrEnv inputBase vals lenW newSp
  have hfit : keccakAbsorbStep * 0 + 20 ≤ addrEnv.length := by
    simp only [addrEnv, List.length_take, List.length_drop, keccakAbsorbStep]
    omega
  exact zkvm_keccak256_spec_within_envelope sp0 ret inputBase outputBase
    addrEnv 0 20 out0 v8 v9 v18 v20 v28 v29 os A hA halign_ret hfit
    (by decide) hout0 hos halign_zk hover (by decide) (by decide) hb8i
    hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem

end EvmAsm.Codegen.Proofs
