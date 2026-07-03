/-
  EvmAsm.Rv64.SAsm.PhaseSplit

  Temporal (phase) re-partition of a shared byte arena — the generic half of
  the `call_frame_arena` phase-ownership model (bead `evm-asm-4ch8f.6`, the
  deferred hard half; the union inventory it instantiates is
  `EvmAsm/Codegen/RegionMap.lean`, the instantiation itself
  `EvmAsm/Codegen/CallFramePhase.lean`).

  ## The model

  A byte range that two execution phases use for different purposes is ONE
  separation-logic resource, never two:

  * `anyBytes base n` — ownership of the `n` bytes at `base` with
    **unspecified contents** (the contents are existentially quantified).
  * A *phase view* of the range is a tiling of that resource into
    sub-ranges (`anyTilesAt`); `anyBytes_sum_eq_anyTilesAt` proves the whole
    resource and any dword-tiling of it are THE SAME assertion.
  * A phase transition is therefore just: weaken each concrete buffer to its
    havoc form (`bytesRegion_anyBytes`), then re-associate through the tiling
    equality.  Contents are FORGOTTEN at every transition **by
    construction** — a later phase provably cannot depend on what an earlier
    phase left in the shared bytes, because the only fact that crosses the
    boundary is `anyBytes` (ownership + length, nothing else).
  * On the consuming side, `cpsTripleWithin_anyBytes_pre` is the proof
    obligation that discipline imposes: a routine framed against a havoc'd
    range must be verified **for every possible contents** of that range.

  Together these make the prose "phase-liveness" argument of
  `docs/call-frame-memory-layout.md` §5 a checkable ownership discipline:
  the seven Phase-H arenas and the Phase-D frame array can share bytes
  soundly because at any point in the composed proof exactly one tiling of
  the arena resource exists, and re-tiling havocs the contents.
-/

import EvmAsm.Rv64.SAsm.HandleWiden

namespace EvmAsm.Rv64
namespace SAsm

-- ============================================================================
-- Havoc'd byte-range ownership
-- ============================================================================

/-- Ownership of the `n` bytes at `base` with unspecified contents. -/
def anyBytes (base : Word) (n : Nat) : Assertion :=
  fun h => ∃ bs : List (BitVec 8), bs.length = n ∧ bytesRegion base bs h

theorem pcFree_anyBytes (base : Word) (n : Nat) : (anyBytes base n).pcFree := by
  rintro h ⟨bs, _, hb⟩
  exact bytesRegion_pcFree base bs h hb

/-- **The havoc weakening**: concrete contents are forgotten.  This is the
    only way a buffer's ownership crosses a phase boundary. -/
theorem bytesRegion_anyBytes (base : Word) (bs : List (BitVec 8))
    (h : PartialState) (hb : bytesRegion base bs h) :
    anyBytes base bs.length h :=
  ⟨bs, rfl, hb⟩

@[simp] theorem anyBytes_zero (base : Word) : anyBytes base 0 = empAssertion := by
  funext h
  apply propext
  constructor
  · rintro ⟨bs, hlen, hb⟩
    rw [List.eq_nil_of_length_eq_zero hlen] at hb
    simpa using hb
  · intro h0
    exact ⟨[], rfl, by simpa using h0⟩

/-- Push a `+ ofNat` past a `+ ofNat` (addition modulo `2^64`, no side
    conditions). -/
theorem add_ofNat_ofNat (b : Word) (m k : Nat) :
    (b + BitVec.ofNat 64 m) + BitVec.ofNat 64 k = b + BitVec.ofNat 64 (m + k) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  conv_rhs => rw [Nat.add_mod]

/-- **Split/join a havoc'd range at a dword boundary**: the `m + k` bytes at
    `base` are exactly the `m` bytes at `base` alongside the `k` bytes at
    `base + m` (both havoc'd), provided the split point is dword-aligned. -/
theorem anyBytes_add (base : Word) (m k : Nat) (h8 : 8 ∣ m) :
    anyBytes base (m + k)
      = (anyBytes base m ** anyBytes (base + BitVec.ofNat 64 m) k) := by
  funext h
  apply propext
  constructor
  · rintro ⟨bs, hlen, hb⟩
    have htk : (bs.take m).length = m := by
      rw [List.length_take]
      omega
    have hdr : (bs.drop m).length = k := by
      rw [List.length_drop]
      omega
    rw [show bs = bs.take m ++ bs.drop m from (List.take_append_drop m bs).symm,
      bytesRegion_append base _ _ (by rw [htk]; exact h8), htk] at hb
    exact sepConj_mono_left (fun h' hx => ⟨bs.take m, htk, hx⟩) h
      (sepConj_mono_right (fun h' hx => ⟨bs.drop m, hdr, hx⟩) h hb)
  · rintro ⟨h1, h2, hd, hu, ⟨bs1, hl1, hb1⟩, ⟨bs2, hl2, hb2⟩⟩
    refine ⟨bs1 ++ bs2, by rw [List.length_append]; omega, ?_⟩
    rw [bytesRegion_append base bs1 bs2 (by rw [hl1]; exact h8), hl1]
    exact ⟨h1, h2, hd, hu, hb1, hb2⟩

-- ============================================================================
-- Contiguous havoc'd tilings
-- ============================================================================

/-- Havoc'd tiles of the given sizes laid out contiguously from `base + off`,
    with the running offset accumulated as a `Nat` sum — so the `j`-th tile's
    assertion is literally `anyBytes (base + ofNat offⱼ) sizeⱼ` with `offⱼ`
    a closed arithmetic term (matching e.g. the audited offsets of
    `RegionMap.dataUnionChildren`). -/
def anyTilesAt (base : Word) (off : Nat) : List Nat → Assertion
  | [] => empAssertion
  | n :: ns => anyBytes (base + BitVec.ofNat 64 off) n ** anyTilesAt base (off + n) ns

theorem pcFree_anyTilesAt (base : Word) (off : Nat) (segs : List Nat) :
    (anyTilesAt base off segs).pcFree := by
  induction segs generalizing off with
  | nil => exact pcFree_emp
  | cons n ns ih => exact pcFree_sepConj (pcFree_anyBytes _ _) (ih _)

/-- **The tiling equality**: a havoc'd range IS the separating conjunction of
    any contiguous dword-aligned tiling of it.  Rewrite left-to-right to enter
    a phase (hand each tile to its owner); right-to-left to leave it (collect
    the tiles back into the arena resource).  Contents do not appear on either
    side — crossing this equality havocs everything. -/
theorem anyBytes_sum_eq_anyTilesAt (base : Word) (off : Nat) (segs : List Nat)
    (h8 : ∀ s ∈ segs, 8 ∣ s) :
    anyBytes (base + BitVec.ofNat 64 off) segs.sum = anyTilesAt base off segs := by
  induction segs generalizing off with
  | nil => exact anyBytes_zero _
  | cons n ns ih =>
      rw [List.sum_cons, anyBytes_add _ n ns.sum (h8 n (List.mem_cons_self ..)),
        add_ofNat_ofNat,
        ih (off + n) (fun s hs => h8 s (List.mem_cons_of_mem _ hs))]
      rfl

/-- The tiling equality at the range's own base (`off = 0`). -/
theorem anyBytes_eq_anyTiles (base : Word) (segs : List Nat)
    (h8 : ∀ s ∈ segs, 8 ∣ s) :
    anyBytes base segs.sum = anyTilesAt base 0 segs := by
  have h0 : base + BitVec.ofNat 64 0 = base := by
    rw [show BitVec.ofNat 64 0 = (0 : Word) from rfl]
    simp
  rw [← anyBytes_sum_eq_anyTilesAt base 0 segs h8, h0]

-- ============================================================================
-- The proof obligation havoc imposes on consumers
-- ============================================================================

/-- **A routine framed against a havoc'd range must be verified for every
    possible contents.**  This is the checkable form of "Phase D cannot
    assume anything Phase H left in the shared bytes": to prove a triple
    whose precondition owns `anyBytes b len`, exhibit the triple for every
    concrete contents `bs` of that length. -/
theorem cpsTripleWithin_anyBytes_pre {n : Nat} {entry exit_ : Word}
    {cr : CodeReq} {P Q : Assertion} {b : Word} {len : Nat}
    (h : ∀ bs : List (BitVec 8), bs.length = len →
      cpsTripleWithin n entry exit_ cr (P ** bytesRegion b bs) Q) :
    cpsTripleWithin n entry exit_ cr (P ** anyBytes b len) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu,
    ⟨h11, h12, hd', hu', hP, ⟨bs, hlen, hbs⟩⟩, hR2⟩ := hPR
  exact h bs hlen R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu, ⟨h11, h12, hd', hu', hP, hbs⟩, hR2⟩ hpc

/-- Demo of the obligation in action: an `LBU` from a havoc'd range admits
    only an **existential** result — the strongest provable postcondition
    says "some byte", never a particular value.  A hypothetical Phase-D
    routine trying to read back what Phase H stored is exactly this triple,
    and this is all it can ever prove. -/
example (rd rs1 : Reg) (regionBase vOld base : Word) (n : Nat)
    (hrd : rd ≠ .x0) (hn : 0 < n)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + 0 < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.LBU rd rs1 0))
      (((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 0)) ** (rd ↦ᵣ vOld))
        ** anyBytes regionBase n)
      (fun h => ∃ b : BitVec 8,
        ((((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 0))
          ** (rd ↦ᵣ (b.zeroExtend 64))) ** anyBytes regionBase n) h)) := by
  apply cpsTripleWithin_anyBytes_pre
  intro bs hlen
  have hi : 0 < bs.length := by omega
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) ?_
    (bytesRegion_lbu_within rd rs1 regionBase vOld base bs 0 hrd halign hi
      hover hvalid)
  intro h' hp
  refine ⟨bs[0]'hi, ?_⟩
  have hp' : (((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 0))
      ** (rd ↦ᵣ ((bs[0]'hi).zeroExtend 64))) ** bytesRegion regionBase bs) h' := by
    xperm_hyp hp
  exact sepConj_mono_right
    (fun h'' hx => hlen ▸ bytesRegion_anyBytes regionBase bs h'' hx) h' hp'

end SAsm
end EvmAsm.Rv64
