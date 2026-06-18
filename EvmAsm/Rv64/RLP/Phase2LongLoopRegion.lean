/-
  EvmAsm.Rv64.RLP.Phase2LongLoopRegion

  EL.3 Phase 2 (long form) — the big-endian length-read loop over a multi-dword
  `bytesRegion`, the region-based analog of the single-dword stack in
  `Phase2LongIter` / `Phase2LongLoopBody` / `Phase2LongLoopGeneral`.

  The body program is unchanged (`rlp_phase2_long_iter_prog` /
  `rlp_phase2_long_loop_body_prog`); only the memory model differs:
  `(dwordAddr ↦ₘ wordVal)` (one dword) → `bytesRegion regionBase bs` (many
  dwords), so the `k` length bytes may cross dword boundaries — the read the
  single-`dwordAddr` `hwin` constraint could not express. Each iteration loads
  `bs[off]` via the cross-dword `bytesRegion_lbu_within`; the pointer is
  `regionBase + ofNat off`.

  Result register `x11` accumulates `rlpLoopAccRegion bs len off n`, which from
  `len = 0` decodes to the pure-spec `Nat.fromBytesBE` of the read bytes.
-/

import EvmAsm.Rv64.RLP.Phase2LongLoopGeneral
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.Tactics.ExtractPure
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.AddrNorm (se12_0 se12_1 bv6_toNat_8)

/-- `bytesRegion` is PC-free — lets the `pcFree` tactic discharge frame
    side-conditions for frames containing the region. -/
instance (regionBase : Word) (bs : List (BitVec 8)) :
    Assertion.PCFree (bytesRegion regionBase bs) :=
  ⟨bytesRegion_pcFree _ _⟩

-- ============================================================================
-- Region accumulator and byte list (mirror rlpLoopAcc / rlpLoopByteList,
-- reading `bs.getD off 0` instead of `extractByte wordVal (byteOffset ptr)`)
-- ============================================================================

/-- `x11` after `n` iterations starting from `(len, off)`: each step shifts left
    a byte and adds `bs[off]`, advancing `off`. -/
def rlpLoopAccRegion (bs : List Byte) : Word → Nat → Nat → Word
  | len, _,   0       => len
  | len, off, (k + 1) =>
      rlpLoopAccRegion bs ((len <<< 8) + (bs.getD off 0).zeroExtend 64) (off + 1) k

theorem rlpLoopAccRegion_zero (bs : List Byte) (len : Word) (off : Nat) :
    rlpLoopAccRegion bs len off 0 = len := rfl

theorem rlpLoopAccRegion_succ (bs : List Byte) (len : Word) (off k : Nat) :
    rlpLoopAccRegion bs len off (k + 1)
      = rlpLoopAccRegion bs ((len <<< 8) + (bs.getD off 0).zeroExtend 64) (off + 1) k := rfl

/-- The `n` bytes read from `off`, most-significant (first read) first. -/
def rlpRegionByteList (bs : List Byte) : Nat → Nat → List Byte
  | _,   0       => []
  | off, (k + 1) => (bs.getD off 0) :: rlpRegionByteList bs (off + 1) k

theorem rlpRegionByteList_length (bs : List Byte) (off n : Nat) :
    (rlpRegionByteList bs off n).length = n := by
  induction n generalizing off with
  | zero => rfl
  | succ k ih => simp [rlpRegionByteList, ih]

/-- In range, the read byte list is the corresponding slice of `bs`. -/
theorem rlpRegionByteList_eq_slice (bs : List Byte) (off n : Nat)
    (h : off + n ≤ bs.length) :
    rlpRegionByteList bs off n = (bs.drop off).take n := by
  induction n generalizing off with
  | zero => simp [rlpRegionByteList]
  | succ k ih =>
    have hoff : off < bs.length := by omega
    rw [rlpRegionByteList, ih (off + 1) (by omega), List.drop_eq_getElem_cons hoff,
        List.take_succ_cons]
    congr 1
    exact (List.getElem_eq_getD (0 : Byte)).symm

/-- Mod-form accumulator invariant (mirror `rlpLoopAcc_toNat`). -/
theorem rlpLoopAccRegion_toNat (bs : List Byte) (n : Nat) (len : Word) (off : Nat) :
    (rlpLoopAccRegion bs len off n).toNat
      = (len.toNat * 256 ^ n
          + Nat.fromBytesBE (rlpRegionByteList bs off n)) % 2 ^ 64 := by
  induction n generalizing len off with
  | zero =>
    simp only [rlpLoopAccRegion, rlpRegionByteList, Nat.fromBytesBE, pow_zero, Nat.mul_one,
      Nat.add_zero]
    exact (Nat.mod_eq_of_lt len.isLt).symm
  | succ k ih =>
    rw [rlpLoopAccRegion, ih,
        show rlpRegionByteList bs off (k + 1)
          = (bs.getD off 0) :: rlpRegionByteList bs (off + 1) k from rfl,
        show Nat.fromBytesBE ((bs.getD off 0) :: rlpRegionByteList bs (off + 1) k)
          = (bs.getD off 0).toNat * 256 ^ (rlpRegionByteList bs (off + 1) k).length
            + Nat.fromBytesBE (rlpRegionByteList bs (off + 1) k) from rfl,
        rlpRegionByteList_length]
    have hlen' :
        ((len <<< 8) + (bs.getD off 0).zeroExtend 64).toNat
          ≡ len.toNat * 256 + (bs.getD off 0).toNat [MOD 2 ^ 64] := by
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
        Nat.shiftLeft_eq, show (2 : Nat) ^ 8 = 256 from rfl]
      calc (len.toNat * 256 % 2 ^ 64 + (bs.getD off 0).toNat % 2 ^ 64) % 2 ^ 64
          ≡ len.toNat * 256 % 2 ^ 64 + (bs.getD off 0).toNat % 2 ^ 64 [MOD 2 ^ 64] :=
            Nat.mod_modEq _ _
        _ ≡ len.toNat * 256 + (bs.getD off 0).toNat [MOD 2 ^ 64] :=
            Nat.ModEq.add (Nat.mod_modEq _ _) (Nat.mod_modEq _ _)
    have h1 := (hlen'.mul_right (256 ^ k)).add_right
      (Nat.fromBytesBE (rlpRegionByteList bs (off + 1) k))
    have h2 : (len.toNat * 256 + (bs.getD off 0).toNat) * 256 ^ k
            + Nat.fromBytesBE (rlpRegionByteList bs (off + 1) k)
          = len.toNat * 256 ^ (k + 1)
            + ((bs.getD off 0).toNat * 256 ^ k
              + Nat.fromBytesBE (rlpRegionByteList bs (off + 1) k)) := by ring
    rw [h2] at h1
    exact h1

/-- From `len = 0`, the accumulator decodes to the pure big-endian value of the
    bytes read; in range, those are `(bs.drop off).take n`. -/
theorem rlpLoopAccRegion_zero_eq_fromBytesBE (bs : List Byte) (off n : Nat)
    (h : off + n ≤ bs.length) :
    rlpLoopAccRegion bs 0 off n
      = BitVec.ofNat 64 (Nat.fromBytesBE ((bs.drop off).take n)) := by
  apply BitVec.eq_of_toNat_eq
  rw [rlpLoopAccRegion_toNat, BitVec.toNat_ofNat,
    show ((0 : Word).toNat) = 0 from rfl, Nat.zero_mul, Nat.zero_add,
    rlpRegionByteList_eq_slice bs off n h]

-- ============================================================================
-- One iteration over the region (reuse the single-dword iter via a dword bridge)
-- ============================================================================

/-- One iteration of the long-form length loop, reading `bs[off]` from the
    multi-dword region. Region analog of `rlp_phase2_long_iter_spec_within`,
    proved by extracting the dword containing byte `off` from `bytesRegion` and
    reusing the single-dword iteration spec. -/
theorem rlp_phase2_long_region_iter_spec_within
    (bs : List Byte) (regionBase len cnt v12Old : Word) (off : Nat) (base : Word)
    (halign : regionBase.toNat % 8 = 0) (hoff : off < bs.length)
    (hover : regionBase.toNat + off < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    cpsTripleWithin 5 base (base + 20)
      (CodeReq.ofProg base rlp_phase2_long_iter_prog)
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 off)) ** (.x14 ↦ᵣ cnt) **
       (.x12 ↦ᵣ v12Old) ** bytesRegion regionBase bs)
      ((.x11 ↦ᵣ ((len <<< 8) + (bs.getD off 0).zeroExtend 64)) **
       (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 off) + 1)) **
       (.x14 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) **
       (.x12 ↦ᵣ (bs.getD off 0).zeroExtend 64) ** bytesRegion regionBase bs) := by
  have hq : 8 * (off / 8) < bs.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ := bytesRegion_dword_at regionBase bs (off / 8) hq
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (off / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (off / 8))).take 8) with hwv
  have halign' : alignToDword (regionBase + BitVec.ofNat 64 off) = dwordAddr :=
    alignToDword_add_ofNat_of_aligned halign hover
  have hbyte : extractByte wordVal (byteOffset (regionBase + BitVec.ofNat 64 off))
      = bs[off]'hoff := by
    rw [byteOffset_add_ofNat_of_aligned halign hover, hwv,
        extractByte_packBytes _ _ (by omega)
          (by rw [List.length_take, List.length_drop]; omega),
        List.getElem_take, List.getElem_drop]
    congr 1; omega
  have iter := rlp_phase2_long_iter_spec_within len (regionBase + BitVec.ofNat 64 off) cnt
    v12Old wordVal dwordAddr base halign' hvalid
  simp only [rlp_phase2_long_iter_post_unfold] at iter
  rw [hbyte, show (bs[off]'hoff : Byte) = bs.getD off 0 from
        List.getElem_eq_getD (0 : Byte)] at iter
  rw [heq]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hr) iter)

-- ============================================================================
-- Loop body with back-branch (mirror rlp_phase2_long_loop_body_spec_within)
-- ============================================================================

/-- Bundled post for either exit of the region loop body. -/
@[irreducible]
def rlp_phase2_long_region_body_post
    (bs : List Byte) (regionBase len : Word) (off : Nat) (cnt : Word) (P : Prop) : Assertion :=
  (.x11 ↦ᵣ ((len <<< 8) + (bs.getD off 0).zeroExtend 64)) **
    (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 off) + 1)) **
    (.x14 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) **
    (.x12 ↦ᵣ (bs.getD off 0).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion regionBase bs ** ⌜P⌝

theorem rlp_phase2_long_region_body_post_unfold
    (bs : List Byte) (regionBase len : Word) (off : Nat) (cnt : Word) (P : Prop) :
    rlp_phase2_long_region_body_post bs regionBase len off cnt P =
    ((.x11 ↦ᵣ ((len <<< 8) + (bs.getD off 0).zeroExtend 64)) **
     (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 off) + 1)) **
     (.x14 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) **
     (.x12 ↦ᵣ (bs.getD off 0).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion regionBase bs ** ⌜P⌝) := by
  delta rlp_phase2_long_region_body_post; rfl

theorem rlp_phase2_long_region_body_post_pure
    {bs : List Byte} {regionBase len : Word} {off : Nat} {cnt : Word} {P : Prop} :
    ∀ hp, rlp_phase2_long_region_body_post bs regionBase len off cnt P hp → P := by
  intro hp hpost
  simp only [rlp_phase2_long_region_body_post_unfold] at hpost
  open EvmAsm.Rv64.Tactics in extract_pure hpost
  exact hpost.1

/-- One pass through the region length-loop body, as a `cpsBranchWithin`. -/
theorem rlp_phase2_long_region_body_spec_within
    (bs : List Byte) (regionBase len cnt v12Old : Word) (off : Nat)
    (base : Word) (back : BitVec 13)
    (halign : regionBase.toNat % 8 = 0) (hoff : off < bs.length)
    (hover : regionBase.toNat + off < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    let cnt' := cnt + signExtend12 (-1 : BitVec 12)
    cpsBranchWithin 6 base (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 off)) ** (.x14 ↦ᵣ cnt) **
       (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs)
      ((base + 20) + signExtend13 back)
        (rlp_phase2_long_region_body_post bs regionBase len off cnt (cnt' ≠ 0))
      (base + 24)
        (rlp_phase2_long_region_body_post bs regionBase len off cnt (cnt' = 0)) := by
  have hcr_eq : CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back) =
      (CodeReq.ofProg base rlp_phase2_long_iter_prog).union
      ((CodeReq.singleton (base + 20) (.BNE .x14 .x0 back)).union CodeReq.empty) := by
    funext a
    have e2 : (base + 4 + 4 : Word) = base + 8 := by bv_omega
    have e3 : (base + 8 + 4 : Word) = base + 12 := by bv_omega
    have e4 : (base + 12 + 4 : Word) = base + 16 := by bv_omega
    have e5 : (base + 16 + 4 : Word) = base + 20 := by bv_omega
    simp only [rlp_phase2_long_loop_body_prog, rlp_phase2_long_iter_prog,
      CodeReq.ofProg_cons, CodeReq.ofProg_nil, CodeReq.union, CodeReq.empty,
      e2, e3, e4, e5, CodeReq.singleton]
    simp only [beq_iff_eq]
    by_cases h0 : a = base
    · simp [h0]
    by_cases h1 : a = base + 4#64
    · simp [h1]
    by_cases h2 : a = base + 8#64
    · simp [h2]
    by_cases h3 : a = base + 12#64
    · simp [h3]
    by_cases h4 : a = base + 16#64
    · simp [h4]
    by_cases h5 : a = base + 20#64
    · simp [h5]
    simp [h0, h1, h2, h3, h4]
  rw [hcr_eq]
  simp only [rlp_phase2_long_region_body_post_unfold]
  have iter := rlp_phase2_long_region_iter_spec_within bs regionBase len cnt v12Old off base
    halign hoff hover hvalid
  set byteZext := (bs.getD off 0).zeroExtend 64 with hbz
  set cnt' := cnt + signExtend12 (-1 : BitVec 12) with hcnt'
  set ptr := regionBase + BitVec.ofNat 64 off with hptr
  have iter' : cpsTripleWithin 5 base (base + 20)
      (CodeReq.ofProg base rlp_phase2_long_iter_prog)
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ cnt) **
       (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs)
      ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) ** (.x13 ↦ᵣ (ptr + 1)) ** (.x14 ↦ᵣ cnt') **
       (.x12 ↦ᵣ byteZext) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) iter)
  have bne_raw := bne_spec_gen_within .x14 .x0 back cnt' (0 : Word) (base + 20)
  have bne_framed : cpsBranchWithin 1 (base + 20)
      (CodeReq.singleton (base + 20) (.BNE .x14 .x0 back))
      ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) ** (.x13 ↦ᵣ (ptr + 1)) ** (.x14 ↦ᵣ cnt') **
       (.x12 ↦ᵣ byteZext) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs)
      ((base + 20) + signExtend13 back)
        ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) ** (.x13 ↦ᵣ (ptr + 1)) ** (.x14 ↦ᵣ cnt') **
         (.x12 ↦ᵣ byteZext) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs ** ⌜cnt' ≠ 0⌝)
      (base + 24)
        ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) ** (.x13 ↦ᵣ (ptr + 1)) ** (.x14 ↦ᵣ cnt') **
         (.x12 ↦ᵣ byteZext) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs ** ⌜cnt' = 0⌝) := by
    have h_eq_20_4 : (base + 20 : Word) + 4 = base + 24 := by bv_omega
    rw [h_eq_20_4] at bne_raw
    exact cpsBranchWithin_weaken
      (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsBranchWithin_frameR
        ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) ** (.x13 ↦ᵣ (ptr + 1)) ** (.x12 ↦ᵣ byteZext) **
         bytesRegion regionBase bs) (by pcFree) bne_raw)
  have hd_iter_bne : (CodeReq.ofProg base rlp_phase2_long_iter_prog).Disjoint
      ((CodeReq.singleton (base + 20) (.BNE .x14 .x0 back)).union CodeReq.empty) := by
    refine CodeReq.Disjoint.union_right ?_ (CodeReq.Disjoint.empty_right _)
    apply CodeReq.Disjoint.ofProg_singleton
    apply CodeReq.ofProg_none_range
    intro k hk
    simp only [rlp_phase2_long_iter_prog, List.length_cons, List.length_nil] at hk
    interval_cases k <;> bv_omega
  have bne_ext : cpsBranchWithin 1 (base + 20)
      ((CodeReq.singleton (base + 20) (.BNE .x14 .x0 back)).union CodeReq.empty) _ _ _ _ _ :=
    cpsBranchWithin_extend_code
      (fun a _ hcr => by
        show (CodeReq.singleton (base + 20) (.BNE .x14 .x0 back)).union CodeReq.empty a = _
        simp only [CodeReq.union, hcr])
      bne_framed
  exact cpsTripleWithin_seq_cpsBranchWithin hd_iter_bne iter' bne_ext

-- ============================================================================
-- General n-iteration region closure (induction)
-- ============================================================================

/-- Region length-read loop closure for `k + 1 ∈ [1,8]` iterations, general
    accumulator `len`. Region analog of `rlp_phase2_long_loop_succ_spec_within`;
    `hwin` bundles in-range + validity for each of the `k + 1` length bytes. -/
theorem rlp_phase2_long_loop_region_succ_spec_within (k : Nat) (hk : k + 1 ≤ 8)
    (regionBase len : Word) (off : Nat) (v12Old : Word) (bs : List Byte)
    (base : Word) (back : BitVec 13)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < k + 1 →
        off + i < bs.length
        ∧ isValidByteAccess (regionBase + BitVec.ofNat 64 (off + i)) = true)
    (hback : (base + 20) + signExtend13 back = base) :
    cpsTripleWithin (6 * (k + 1)) base (base + 24)
      (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 off)) **
       (.x14 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion regionBase bs)
      ((.x11 ↦ᵣ rlpLoopAccRegion bs len off (k + 1)) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (off + (k + 1)))) ** (.x14 ↦ᵣ (0 : Word)) **
       (.x12 ↦ᵣ (bs.getD (off + k) 0).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion regionBase bs) := by
  induction k generalizing len off v12Old with
  | zero =>
    obtain ⟨hoff, hvalid0⟩ := by have h := hwin 0 (by omega); rwa [Nat.add_zero] at h
    have hover0 : regionBase.toNat + off < 2 ^ 64 := by omega
    have body := rlp_phase2_long_region_body_spec_within bs regionBase len
      (BitVec.ofNat 64 (0 + 1)) v12Old off base back halign hoff hover0 hvalid0
    rw [word_ofNat_succ_dec 0] at body
    have h_absurd : ∀ hp,
        rlp_phase2_long_region_body_post bs regionBase len off (BitVec.ofNat 64 (0 + 1))
          ((BitVec.ofNat 64 0 : Word) ≠ 0) hp → False :=
      fun hp hpost => (rlp_phase2_long_region_body_post_pure hp hpost) (by decide)
    have tri := cpsBranchWithin_ntakenPath body h_absurd
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_) tri
    simp only [rlp_phase2_long_region_body_post_unfold] at hp
    rw [show (regionBase + BitVec.ofNat 64 off) + 1
          = regionBase + BitVec.ofNat 64 (off + (0 + 1)) from by
        rw [word_ofNat_add_one off]; bv_omega] at hp
    rw [rlpLoopAccRegion_succ, rlpLoopAccRegion_zero, show off + 0 = off from rfl]
    open EvmAsm.Rv64.Tactics in xperm_pure hp
  | succ k ih =>
    obtain ⟨hoff, hvalid0⟩ := by have h := hwin 0 (by omega); rwa [Nat.add_zero] at h
    have hover0 : regionBase.toNat + off < 2 ^ 64 := by omega
    have body := rlp_phase2_long_region_body_spec_within bs regionBase len
      (BitVec.ofNat 64 (k + 1 + 1)) v12Old off base back halign hoff hover0 hvalid0
    rw [word_ofNat_succ_dec (k + 1)] at body
    have hne : BitVec.ofNat 64 (k + 1) ≠ (0 : Word) := word_ofNat_succ_ne_zero k (by omega)
    have h_absurd : ∀ hp,
        rlp_phase2_long_region_body_post bs regionBase len off (BitVec.ofNat 64 (k + 1 + 1))
          ((BitVec.ofNat 64 (k + 1) : Word) = 0) hp → False :=
      fun hp hpost => absurd (rlp_phase2_long_region_body_post_pure hp hpost) hne
    have tri1 := cpsBranchWithin_takenPath body h_absurd
    rw [hback] at tri1
    have tri1' : cpsTripleWithin 6 base base
        (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
        ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 off)) **
         (.x14 ↦ᵣ BitVec.ofNat 64 (k + 1 + 1)) ** (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion regionBase bs)
        ((.x11 ↦ᵣ ((len <<< 8) + (bs.getD off 0).zeroExtend 64)) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (off + 1))) **
         (.x14 ↦ᵣ BitVec.ofNat 64 (k + 1)) **
         (.x12 ↦ᵣ (bs.getD off 0).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion regionBase bs) :=
      cpsTripleWithin_weaken (fun _ hp => hp)
        (fun h hp => by
          simp only [rlp_phase2_long_region_body_post_unfold] at hp
          rw [word_ofNat_succ_dec (k + 1),
              show (regionBase + BitVec.ofNat 64 off) + 1
                = regionBase + BitVec.ofNat 64 (off + 1) from by
                rw [word_ofNat_add_one off]; bv_omega] at hp
          open EvmAsm.Rv64.Tactics in xperm_pure hp)
        tri1
    have hwin' : ∀ i, i < k + 1 →
        (off + 1) + i < bs.length
        ∧ isValidByteAccess (regionBase + BitVec.ofNat 64 ((off + 1) + i)) = true := by
      intro i hi
      have h := hwin (i + 1) (by omega)
      rwa [show off + (i + 1) = (off + 1) + i from by omega] at h
    have ihspec := ih (by omega) ((len <<< 8) + (bs.getD off 0).zeroExtend 64) (off + 1)
      ((bs.getD off 0).zeroExtend 64) hwin'
    have composed :=
      cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) tri1' ihspec
    rw [show (6 * (k + 1 + 1)) = 6 + 6 * (k + 1) from by ring,
        rlpLoopAccRegion_succ bs len off (k + 1),
        show off + (k + 1 + 1) = (off + 1) + (k + 1) from by omega,
        show off + (k + 1) = (off + 1) + k from by omega]
    exact composed

/-- Region length-read closure with accumulator started at `0`, stated against
    the pure spec `Nat.fromBytesBE` of the `n` length bytes read from the region. -/
theorem rlp_phase2_long_loop_region_n_spec_within (n : Nat) (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (regionBase v12Old : Word) (off : Nat) (bs : List Byte) (base : Word) (back : BitVec 13)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < n →
        off + i < bs.length
        ∧ isValidByteAccess (regionBase + BitVec.ofNat 64 (off + i)) = true)
    (hback : (base + 20) + signExtend13 back = base) :
    cpsTripleWithin (6 * n) base (base + 24)
      (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 off)) **
       (.x14 ↦ᵣ BitVec.ofNat 64 n) ** (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion regionBase bs)
      ((.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((bs.drop off).take n))) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (off + n))) ** (.x14 ↦ᵣ (0 : Word)) **
       (.x12 ↦ᵣ (bs.getD (off + (n - 1)) 0).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion regionBase bs) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hlen : off + (k + 1) ≤ bs.length := by have := (hwin k (by omega)).1; omega
  have core := rlp_phase2_long_loop_region_succ_spec_within k hn8 regionBase 0 off v12Old bs
    base back halign hover hwin hback
  rw [show (k + 1 - 1) = k from rfl]
  rw [rlpLoopAccRegion_zero_eq_fromBytesBE bs off (k + 1) hlen] at core
  exact core

-- Sanity: the parametric closure instantiated at `n = 2` (a 2-byte length field).
example : (6 * 2) = 12 := rfl

end EvmAsm.Rv64.RLP
