/-
  EvmAsm.Rv64.RLP.SingleByteListLoop

  EL.3 — the first RV64 RLP *list*-decode loop: a back-branch loop that
  traverses a payload of single-byte items (each byte `< 0x80` is its own
  RLP item) reading from a multi-dword `bytesRegion`, advancing a pointer
  and decrementing a counter:

      LBU  x12, x13, 0        ; byte = mem[x13]   (read; x12 discarded)
      ADDI x13, x13, 1        ; ptr += 1
      ADDI x14, x14, -1       ; counter -= 1
      BNE  x14, x0, back      ; if counter != 0, loop back

  Unlike the Phase-2 *length* loop (`Phase2LongLoopGeneral`), this loop:
    * reads from the multi-dword `bytesRegion` via `bytesRegion_lbu_within`
      (keyed by the *absolute* byte index `i`, so the induction keeps
      `regionBase`/`bs` fixed and re-indexes the per-iteration hypotheses,
      rather than shifting a single iteration-invariant `dwordAddr ↦ₘ`), and
    * accumulates nothing — the decoder is zero-copy; a single-byte item
      materializes no structure, it just consumes one byte.

  Scope (assume-precondition): the loop does *not* validate `< 0x80` in-line
  (no fail-exit); a precondition `∀ b ∈ bs, b.toNat < 0x80` assumes it — the
  same hypothesis the pure spec `decodeItems_singleByte_run` needs. The bridge
  theorem packages the operational spec with that pure decode result. In-line
  validation (the 3-exit fail path) is a follow-up.
-/

import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.RLP.Phase2LongLoopGeneral
import EvmAsm.EL.RLP.ListDecode
import EvmAsm.Rv64.Tactics.ExtractPure
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.AddrNorm (se12_1)

/-- `bytesRegion` is PC-free — lets the `pcFree` tactic discharge frame
    side-conditions involving the region. -/
instance (regionBase : Word) (bs : List (BitVec 8)) :
    Assertion.PCFree (bytesRegion regionBase bs) :=
  ⟨bytesRegion_pcFree _ _⟩

-- ============================================================================
-- One iteration (no back-branch): LBU + ptr advance + counter decrement
-- ============================================================================

/-- Three-instruction iteration body: read the byte, advance the pointer,
    decrement the counter. -/
def sbll_iter_prog : Program :=
  [.LBU .x12 .x13 0, .ADDI .x13 .x13 1, .ADDI .x14 .x14 (-1)]

example : sbll_iter_prog.length = 3 := rfl

/-- Split `ofProg base sbll_iter_prog` into three singleton CodeReqs plus an
    `empty` tail. -/
private theorem sbll_iter_code_split {base : Word} :
    CodeReq.ofProg base sbll_iter_prog =
    (CodeReq.singleton base (.LBU .x12 .x13 0)).union
    ((CodeReq.singleton (base + 4) (.ADDI .x13 .x13 1)).union
    ((CodeReq.singleton (base + 8) (.ADDI .x14 .x14 (-1))).union
     CodeReq.empty)) := by
  have e2 : (base + 4 + 4 : Word) = base + 8 := by bv_omega
  simp only [sbll_iter_prog, CodeReq.ofProg_cons, CodeReq.ofProg_nil, e2]

/-- `cpsTripleWithin` spec for one iteration: reads byte `i` of the region
    into `x12`, advances `x13` to index `i+1`, decrements `x14`. -/
theorem sbll_iter_spec_within
    (regionBase v12Old cnt base : Word) (bs : List (BitVec 8)) (i : Nat)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 3 base (base + 12)
      (CodeReq.ofProg base sbll_iter_prog)
      ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) **
       (.x14 ↦ᵣ cnt) ** bytesRegion regionBase bs)
      ((.x12 ↦ᵣ ((bs[i]'hi).zeroExtend 64)) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) **
       (.x14 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) **
       bytesRegion regionBase bs) := by
  rw [sbll_iter_code_split]
  have h01 : (base : Word) ≠ base + 4 := by bv_omega
  have h02 : (base : Word) ≠ base + 8 := by bv_omega
  have h12 : (base + 4 : Word) ≠ base + 8 := by bv_omega
  -- Step 1: LBU x12, x13, 0 — reads byte i from the region.
  have lbu_raw := bytesRegion_lbu_within .x12 .x13 regionBase v12Old base bs i
    (by decide) halign hi hover hvalid
  set byteZext := (bs[i]'hi).zeroExtend 64 with hbz
  have s1 : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU .x12 .x13 0))
      ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) **
       (.x14 ↦ᵣ cnt) ** bytesRegion regionBase bs)
      ((.x12 ↦ᵣ byteZext) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) **
       (.x14 ↦ᵣ cnt) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR (.x14 ↦ᵣ cnt) (by pcFree) lbu_raw)
  -- Step 2: ADDI x13, x13, 1 — advance the pointer to index i+1.
  have addi_ptr_raw := addi_spec_gen_same_within .x13 (regionBase + BitVec.ofNat 64 i)
    1 (base + 4) (by nofun)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega, se12_1,
      show (regionBase + BitVec.ofNat 64 i) + 1 = regionBase + BitVec.ofNat 64 (i + 1) from by
        rw [word_ofNat_add_one i]; bv_omega] at addi_ptr_raw
  have s2 : cpsTripleWithin 1 (base + 4) (base + 8)
      (CodeReq.singleton (base + 4) (.ADDI .x13 .x13 1))
      ((.x12 ↦ᵣ byteZext) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) **
       (.x14 ↦ᵣ cnt) ** bytesRegion regionBase bs)
      ((.x12 ↦ᵣ byteZext) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) **
       (.x14 ↦ᵣ cnt) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x12 ↦ᵣ byteZext) ** (.x14 ↦ᵣ cnt) ** bytesRegion regionBase bs)
        (by pcFree) addi_ptr_raw)
  -- Step 3: ADDI x14, x14, -1 — decrement the counter.
  have addi_cnt_raw := addi_spec_gen_same_within .x14 cnt (-1) (base + 8) (by nofun)
  rw [show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at addi_cnt_raw
  have s3 : cpsTripleWithin 1 (base + 8) (base + 12)
      (CodeReq.singleton (base + 8) (.ADDI .x14 .x14 (-1)))
      ((.x12 ↦ᵣ byteZext) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) **
       (.x14 ↦ᵣ cnt) ** bytesRegion regionBase bs)
      ((.x12 ↦ᵣ byteZext) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) **
       (.x14 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x12 ↦ᵣ byteZext) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) **
         bytesRegion regionBase bs)
        (by pcFree) addi_cnt_raw)
  -- Chain the three steps.
  have hd2 : CodeReq.Disjoint
      (CodeReq.singleton (base + 4) (.ADDI .x13 .x13 1))
      ((CodeReq.singleton (base + 8) (.ADDI .x14 .x14 (-1))).union CodeReq.empty) :=
    CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h12)
      (CodeReq.Disjoint.empty_right _)
  have hd1 : CodeReq.Disjoint
      (CodeReq.singleton base (.LBU .x12 .x13 0))
      ((CodeReq.singleton (base + 4) (.ADDI .x13 .x13 1)).union
        ((CodeReq.singleton (base + 8) (.ADDI .x14 .x14 (-1))).union CodeReq.empty)) :=
    CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h01)
      (CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h02)
        (CodeReq.Disjoint.empty_right _))
  have s3_ext : cpsTripleWithin 1 (base + 8) (base + 12)
      ((CodeReq.singleton (base + 8) (.ADDI .x14 .x14 (-1))).union CodeReq.empty) _ _ :=
    cpsTripleWithin_extend_code
      (fun a _ hcr => by
        show (CodeReq.singleton (base + 8) (.ADDI .x14 .x14 (-1))).union CodeReq.empty a = _
        simp only [CodeReq.union, hcr])
      s3
  have t23 := cpsTripleWithin_seq hd2 s2 s3_ext
  exact cpsTripleWithin_seq hd1 s1 t23

-- ============================================================================
-- Full loop body (with back-branch): a 2-exit cpsBranchWithin
-- ============================================================================

/-- Four-instruction loop body: one iteration followed by `BNE x14, x0, back`. -/
def sbll_body_prog (back : BitVec 13) : Program :=
  [.LBU .x12 .x13 0, .ADDI .x13 .x13 1, .ADDI .x14 .x14 (-1), .BNE .x14 .x0 back]

example (back : BitVec 13) : (sbll_body_prog back).length = 4 := rfl

/-- Bundled post for either exit of the loop body: registers updated as per one
    iteration, plus a caller-supplied pure dispatch fact `P`. -/
@[irreducible]
def sbll_body_post (regionBase byteZext nextPtr cnt' : Word)
    (bs : List (BitVec 8)) (P : Prop) : Assertion :=
  (.x12 ↦ᵣ byteZext) ** (.x13 ↦ᵣ nextPtr) ** (.x14 ↦ᵣ cnt') **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs ** ⌜P⌝

theorem sbll_body_post_unfold (regionBase byteZext nextPtr cnt' : Word)
    (bs : List (BitVec 8)) (P : Prop) :
    sbll_body_post regionBase byteZext nextPtr cnt' bs P =
    ((.x12 ↦ᵣ byteZext) ** (.x13 ↦ᵣ nextPtr) ** (.x14 ↦ᵣ cnt') **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs ** ⌜P⌝) := by
  delta sbll_body_post; rfl

/-- Extract the pure proposition `P` carried by the loop-body post. -/
theorem sbll_body_post_pure {regionBase byteZext nextPtr cnt' : Word}
    {bs : List (BitVec 8)} {P : Prop} :
    ∀ hp, sbll_body_post regionBase byteZext nextPtr cnt' bs P hp → P := by
  intro hp hpost
  simp only [sbll_body_post_unfold] at hpost
  open EvmAsm.Rv64.Tactics in extract_pure hpost
  exact hpost.1

/-- Step-bounded spec for one pass through the loop body, reading byte `i`.
    Composes `sbll_iter_spec_within` with `bne_spec_gen_within` at `base + 12`. -/
theorem sbll_body_spec_within
    (regionBase v12Old cnt base : Word) (back : BitVec 13)
    (bs : List (BitVec 8)) (i : Nat)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true) :
    let byteZext := (bs[i]'hi).zeroExtend 64
    let cnt'     := cnt + signExtend12 (-1 : BitVec 12)
    cpsBranchWithin 4 base (CodeReq.ofProg base (sbll_body_prog back))
      ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) **
       (.x14 ↦ᵣ cnt) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs)
      ((base + 12) + signExtend13 back)
        (sbll_body_post regionBase byteZext
          (regionBase + BitVec.ofNat 64 (i + 1)) cnt' bs (cnt' ≠ 0))
      (base + 16)
        (sbll_body_post regionBase byteZext
          (regionBase + BitVec.ofNat 64 (i + 1)) cnt' bs (cnt' = 0)) := by
  -- The body `ofProg` splits as `ofProg base iter_prog ∪ (BNE singleton ∪ empty)`.
  have hcr_eq : CodeReq.ofProg base (sbll_body_prog back) =
      (CodeReq.ofProg base sbll_iter_prog).union
      ((CodeReq.singleton (base + 12) (.BNE .x14 .x0 back)).union CodeReq.empty) := by
    funext a
    have e2 : (base + 4 + 4 : Word) = base + 8 := by bv_omega
    have e3 : (base + 8 + 4 : Word) = base + 12 := by bv_omega
    simp only [sbll_body_prog, sbll_iter_prog, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
      CodeReq.union, CodeReq.empty, e2, e3, CodeReq.singleton]
    simp only [beq_iff_eq]
    by_cases h0 : a = base
    · simp [h0]
    by_cases h1 : a = base + 4#64
    · simp [h1]
    by_cases h2 : a = base + 8#64
    · simp [h2]
    by_cases h3 : a = base + 12#64
    · simp [h3]
    simp [h0, h1, h2, h3]
  rw [hcr_eq]
  simp only [sbll_body_post_unfold]
  set byteZext := (bs[i]'hi).zeroExtend 64 with hbz
  set cnt' := cnt + signExtend12 (-1 : BitVec 12) with hcnt
  -- Iteration triple (3 instr, base → base+12), framed with (.x0 ↦ᵣ 0).
  have iter := sbll_iter_spec_within regionBase v12Old cnt base bs i halign hi hover hvalid
  have iter' : cpsTripleWithin 3 base (base + 12)
      (CodeReq.ofProg base sbll_iter_prog)
      ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) **
       (.x14 ↦ᵣ cnt) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs)
      ((.x14 ↦ᵣ cnt') ** (.x0 ↦ᵣ (0 : Word)) **
       (.x12 ↦ᵣ byteZext) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) **
       bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) iter)
  -- BNE x14, x0, back at (base + 12).
  have bne_raw := bne_spec_gen_within .x14 .x0 back cnt' (0 : Word) (base + 12)
  have bne_framed : cpsBranchWithin 1 (base + 12)
      (CodeReq.singleton (base + 12) (.BNE .x14 .x0 back))
      ((.x14 ↦ᵣ cnt') ** (.x0 ↦ᵣ (0 : Word)) **
       (.x12 ↦ᵣ byteZext) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) **
       bytesRegion regionBase bs)
      ((base + 12) + signExtend13 back)
        ((.x12 ↦ᵣ byteZext) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) **
         (.x14 ↦ᵣ cnt') ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs ** ⌜cnt' ≠ 0⌝)
      (base + 16)
        ((.x12 ↦ᵣ byteZext) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) **
         (.x14 ↦ᵣ cnt') ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs ** ⌜cnt' = 0⌝) := by
    have h_eq_12_4 : (base + 12 : Word) + 4 = base + 16 := by bv_omega
    rw [h_eq_12_4] at bne_raw
    exact cpsBranchWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsBranchWithin_frameR
        ((.x12 ↦ᵣ byteZext) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) **
         bytesRegion regionBase bs) (by pcFree) bne_raw)
  -- Disjointness between iter CR and the BNE-singleton-union-empty CR.
  have hd_iter_bne : (CodeReq.ofProg base sbll_iter_prog).Disjoint
      ((CodeReq.singleton (base + 12) (.BNE .x14 .x0 back)).union CodeReq.empty) := by
    refine CodeReq.Disjoint.union_right ?_ (CodeReq.Disjoint.empty_right _)
    apply CodeReq.Disjoint.ofProg_singleton
    apply CodeReq.ofProg_none_range
    intro k hk
    simp only [sbll_iter_prog, List.length_cons, List.length_nil] at hk
    interval_cases k <;> bv_omega
  have bne_ext : cpsBranchWithin 1 (base + 12)
      ((CodeReq.singleton (base + 12) (.BNE .x14 .x0 back)).union CodeReq.empty)
      _ _ _ _ _ :=
    cpsBranchWithin_extend_code
      (fun a _ hcr => by
        show (CodeReq.singleton (base + 12) (.BNE .x14 .x0 back)).union CodeReq.empty a = _
        simp only [CodeReq.union, hcr])
      bne_framed
  exact cpsTripleWithin_seq_cpsBranchWithin hd_iter_bne iter' bne_ext

-- ============================================================================
-- n-iteration closure (operational cpsTriple, by remaining-count induction)
-- ============================================================================

/-- Loop closure for `k + 1` iterations starting at absolute index `start`.

    Proved by induction on `k` generalizing `start` (and the discarded `x12`
    value): the region `bytesRegion regionBase bs` and the alignment stay
    fixed; only the index and per-iteration validity hypotheses are re-indexed.
    Counter `k + 1` ⇒ exactly `k + 1` iterations; reads indices
    `start … start + k`. -/
theorem sbll_loop_succ_spec_within (k start : Nat)
    (regionBase v12Old base : Word) (back : BitVec 13) (bs : List (BitVec 8))
    (halign : regionBase.toNat % 8 = 0) (hk_len : start + k < bs.length)
    (hover : regionBase.toNat + (start + k) < 2 ^ 64)
    (hwin : ∀ j, j < k + 1 →
        isValidByteAccess (regionBase + BitVec.ofNat 64 (start + j)) = true)
    (hback : (base + 12) + signExtend13 back = base) :
    cpsTripleWithin (4 * (k + 1)) base (base + 16)
      (CodeReq.ofProg base (sbll_body_prog back))
      ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 start)) **
       (.x14 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion regionBase bs)
      ((.x12 ↦ᵣ ((bs[start + k]'(by omega)).zeroExtend 64)) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (start + (k + 1)))) **
       (.x14 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion regionBase bs) := by
  induction k generalizing start v12Old with
  | zero =>
    have hvalid0 := hwin 0 (by omega)
    rw [show start + 0 = start from rfl] at hvalid0
    have body := sbll_body_spec_within regionBase v12Old (1 : Word) base back bs start
      halign (by omega) (by omega) hvalid0
    rw [cnt_dec_1] at body
    set byteZext := (bs[start]'(by omega : start < bs.length)).zeroExtend 64 with hbz
    have h_absurd : ∀ hp,
        sbll_body_post regionBase byteZext (regionBase + BitVec.ofNat 64 (start + 1))
          (0 : Word) bs ((0 : Word) ≠ 0) hp → False :=
      fun hp hpost => sbll_body_post_pure hp hpost rfl
    have tri := cpsBranchWithin_ntakenPath body h_absurd
    -- `4 * (0 + 1) = 4`, `start + 0 = start`, `start + (0 + 1) = start + 1` all hold
    -- definitionally, so the goal unifies with `tri` after weakening the post.
    exact cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [sbll_body_post_unfold] at hp
        open EvmAsm.Rv64.Tactics in xperm_pure hp)
      tri
  | succ k ih =>
    have hvalid0 := hwin 0 (by omega)
    rw [show start + 0 = start from rfl] at hvalid0
    have body := sbll_body_spec_within regionBase v12Old (BitVec.ofNat 64 (k + 1 + 1))
      base back bs start halign (by omega) (by omega) hvalid0
    rw [word_ofNat_succ_dec (k + 1)] at body
    set byteZext := (bs[start]'(by omega : start < bs.length)).zeroExtend 64 with hbz
    have hne : BitVec.ofNat 64 (k + 1) ≠ (0 : Word) :=
      word_ofNat_succ_ne_zero k (by omega)
    have h_absurd : ∀ hp,
        sbll_body_post regionBase byteZext (regionBase + BitVec.ofNat 64 (start + 1))
          (BitVec.ofNat 64 (k + 1)) bs ((BitVec.ofNat 64 (k + 1) : Word) = 0) hp → False :=
      fun hp hpost => absurd (sbll_body_post_pure hp hpost) hne
    have tri1 := cpsBranchWithin_takenPath body h_absurd
    rw [hback] at tri1
    have tri1' : cpsTripleWithin 4 base base
        (CodeReq.ofProg base (sbll_body_prog back))
        ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 start)) **
         (.x14 ↦ᵣ BitVec.ofNat 64 (k + 1 + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion regionBase bs)
        ((.x12 ↦ᵣ byteZext) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (start + 1))) **
         (.x14 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion regionBase bs) :=
      cpsTripleWithin_weaken
        (fun _ hp => hp)
        (fun _ hp => by
          simp only [sbll_body_post_unfold] at hp
          open EvmAsm.Rv64.Tactics in xperm_pure hp)
        tri1
    have hwin' : ∀ j, j < k + 1 →
        isValidByteAccess (regionBase + BitVec.ofNat 64 ((start + 1) + j)) = true := by
      intro j hj
      have h := hwin (j + 1) (by omega)
      rwa [show start + (j + 1) = (start + 1) + j from by omega] at h
    have ihspec := ih (start + 1) byteZext (by omega) (by omega) hwin'
    have composed :=
      cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) tri1' ihspec
    rw [show (4 * (k + 1 + 1)) = 4 + 4 * (k + 1) from by ring]
    simp only [show start + (k + 1) = (start + 1) + k from by omega,
               show start + (k + 1 + 1) = (start + 1) + (k + 1) from by omega]
    exact composed

/-- General `n ≥ 1` loop closure, entry counter `n`, reading region bytes
    `0 … n-1`. Pointer advances to index `n`, counter zeroes. -/
theorem sbll_loop_n_spec_within (n : Nat) (hn1 : 1 ≤ n)
    (regionBase v12Old base : Word) (back : BitVec 13) (bs : List (BitVec 8))
    (halign : regionBase.toNat % 8 = 0) (hn_len : n ≤ bs.length)
    (hover : regionBase.toNat + n < 2 ^ 64)
    (hwin : ∀ i, i < n → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hback : (base + 12) + signExtend13 back = base) :
    cpsTripleWithin (4 * n) base (base + 16)
      (CodeReq.ofProg base (sbll_body_prog back))
      ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ regionBase) **
       (.x14 ↦ᵣ BitVec.ofNat 64 n) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion regionBase bs)
      ((.x12 ↦ᵣ ((bs[n - 1]'(by omega)).zeroExtend 64)) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 n)) **
       (.x14 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion regionBase bs) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have core := sbll_loop_succ_spec_within k 0 regionBase v12Old base back bs
    halign (by omega) (by omega)
    (by intro j hj; rw [Nat.zero_add]; exact hwin j hj) hback
  -- Normalize `0 + _` and `regionBase + ofNat 0`; `k + 1 - 1 = k` holds definitionally.
  simp only [Nat.zero_add] at core
  rw [show regionBase + BitVec.ofNat 64 0 = regionBase from by simp] at core
  exact core

-- ============================================================================
-- Bridge to the pure spec `decodeItems_singleByte_run`
-- ============================================================================

/-- **Single-byte-item list-decode bridge.** Given a region `bytesRegion
    regionBase bs` whose every byte is `< 0x80`, the loop runs in
    `4 * bs.length` steps — advancing the pointer by `bs.length` and zeroing
    the counter — *and* the pure decoder turns the payload into `bs.length`
    single-byte items consuming the whole list.

    The decoder is zero-copy, so the operational half materializes no item
    structure; the right conjunct is `decodeItems_singleByte_run` at the
    canonical depth `2 * bs.length`. The two halves are tied by the *shared*
    precondition `hsingle` (which a future in-line-validation PR will discharge
    operationally rather than assume) and the *matching* consumed length
    `bs.length` (loop advances `x13` by `bs.length`; pure decoder leaves `[]`). -/
theorem sbll_loop_bridge (n : Nat) (hn1 : 1 ≤ n)
    (regionBase v12Old base : Word) (back : BitVec 13) (bs : List (BitVec 8))
    (halign : regionBase.toNat % 8 = 0) (hn_len : n = bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hsingle : ∀ b ∈ bs, b.toNat < 0x80)
    (hback : (base + 12) + signExtend13 back = base) :
    cpsTripleWithin (4 * bs.length) base (base + 16)
      (CodeReq.ofProg base (sbll_body_prog back))
      ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ regionBase) **
       (.x14 ↦ᵣ BitVec.ofNat 64 bs.length) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion regionBase bs)
      ((.x12 ↦ᵣ ((bs[bs.length - 1]'(by omega)).zeroExtend 64)) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 bs.length)) **
       (.x14 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion regionBase bs)
    ∧ decodeItems (2 * bs.length) bs
        = some (bs.map (fun b => RLPItem.bytes [b]), []) := by
  subst hn_len
  refine ⟨sbll_loop_n_spec_within bs.length hn1 regionBase v12Old base back bs
    halign (le_refl _) hover hwin hback, ?_⟩
  exact decodeItems_singleByte_run bs (2 * bs.length) hsingle (le_refl _)

/-- Cross-dword cross-check: a 10-byte all-`< 0x80` payload spanning two dwords.
    Decodes to 10 single-byte items in `4 * 10 = 40` steps; the loop reads
    byte 9 (second dword) — a cross-dword traversal the single-`dwordAddr`
    length loop could not express. -/
example (base regionBase v12Old : Word) (back : BitVec 13) (bs : List (BitVec 8))
    (hlen : bs.length = 10) (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + 10 < 2 ^ 64)
    (hwin : ∀ i, i < 10 → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hsingle : ∀ b ∈ bs, b.toNat < 0x80)
    (hback : (base + 12) + signExtend13 back = base) :
    cpsTripleWithin 40 base (base + 16)
      (CodeReq.ofProg base (sbll_body_prog back))
      ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ regionBase) **
       (.x14 ↦ᵣ BitVec.ofNat 64 10) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion regionBase bs)
      ((.x12 ↦ᵣ ((bs[9]'(by omega)).zeroExtend 64)) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 10)) **
       (.x14 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion regionBase bs)
    ∧ decodeItems 20 bs = some (bs.map (fun b => RLPItem.bytes [b]), []) := by
  have h := sbll_loop_bridge 10 (by omega) regionBase v12Old base back bs
    halign hlen.symm (by omega) (by rw [hlen]; exact hwin) hsingle hback
  simp only [hlen] at h
  exact h

end EvmAsm.Rv64.RLP
