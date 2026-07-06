/-
  EvmAsm.Rv64.RLP.SingleByteListLoopValidated

  EL.3 — the single-byte-item RLP list-decode loop with **in-machine `< 0x80`
  validation**. Where `SingleByteListLoop.lean` *assumes* every payload byte
  `< 0x80` (the `hsingle` precondition), this loop *proves* it: it ORs every byte
  into an accumulator (`x11`) as it scans, then a single post-loop bit-7 check
  (`ANDI x15, x11, 0x80; BNE x15, x0, fail`) decides success vs. fail. The
  success branch *derives* `∀ b ∈ bs, b.toNat < 0x80`, so the bridge to the pure
  `decodeItems_singleByte_run` no longer assumes it.

  Design: accumulate-then-check (not per-iteration early-exit). The loop stays a
  `cpsTripleWithin` closure (an OR accumulator, exactly like the Phase-2 length
  loop's shift+add accumulator); a single 2-exit branch follows. This drops
  `hsingle` without any new branch-composition infrastructure. `OR` never
  overflows, so — unlike the length loop — there is no `n ≤ 8` bound.
-/

import EvmAsm.Rv64.RLP.SingleByteListLoop

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.AddrNorm (se12_1)

-- ============================================================================
-- Pure OR-accumulator + the bit-7 key lemma
-- ============================================================================

/-- The loop's accumulator: OR each byte (zero-extended to 64 bits) into `acc`. -/
def orAccList (acc : Word) (l : List (BitVec 8)) : Word :=
  l.foldl (fun a b => a ||| b.zeroExtend 64) acc

@[simp] theorem orAccList_nil (acc : Word) : orAccList acc [] = acc := rfl

theorem orAccList_cons (acc : Word) (b : BitVec 8) (l : List (BitVec 8)) :
    orAccList acc (b :: l) = orAccList (acc ||| b.zeroExtend 64) l := rfl

/-- If `(x ||| y) &&& m = 0` then the left disjunct is masked to zero. -/
theorem and_left_of_or_and_eq_zero {x y m : Word} (h : (x ||| y) &&& m = 0) :
    x &&& m = 0 := by
  ext i
  have hi := congrArg (fun z => z.getLsbD i) h
  simp at hi
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases m.getLsbD i <;> simp_all

/-- If `(x ||| y) &&& m = 0` then the right disjunct is masked to zero. -/
theorem and_right_of_or_and_eq_zero {x y m : Word} (h : (x ||| y) &&& m = 0) :
    y &&& m = 0 := by
  ext i
  have hi := congrArg (fun z => z.getLsbD i) h
  simp at hi
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases m.getLsbD i <;> simp_all

/-- Bit-7 leaf: a byte whose bit 7 is masked off (by `0x80`) is `< 0x80`. -/
theorem byte_zext_and_0x80_eq_zero_imp_lt {b : BitVec 8}
    (h : (b.zeroExtend 64) &&& (0x80 : Word) = 0) : b.toNat < 0x80 := by
  -- Bit 7 of `b` is clear (the only set bit of `0x80` is bit 7).
  have h7 : b.getLsbD 7 = false := by
    have hi := congrArg (fun z => z.getLsbD 7) h
    simpa [BitVec.getLsbD_and, BitVec.getLsbD_zero, BitVec.getLsbD_setWidth,
           show ((0x80 : Word).getLsbD 7 = true) from by decide] using hi
  -- For an 8-bit vector, bit 7 is the MSB; MSB clear ⇒ `2 * toNat < 2^8`.
  have hmsb : b.msb = false := by rw [BitVec.msb_eq_getLsbD_last]; simpa using h7
  have h2 := (BitVec.msb_eq_false_iff_two_mul_lt).mp hmsb
  omega

/-- The fold preserves the bit-7-clear invariant downward to its seed. -/
theorem orAccList_and_zero_imp_acc {l : List (BitVec 8)} :
    ∀ acc : Word, (orAccList acc l) &&& (0x80 : Word) = 0 → acc &&& (0x80 : Word) = 0 := by
  induction l with
  | nil => intro acc h; simpa [orAccList] using h
  | cons c l ih =>
    intro acc h
    rw [orAccList_cons] at h
    exact and_left_of_or_and_eq_zero (ih (acc ||| c.zeroExtend 64) h)

/-- **Key lemma.** If the OR-accumulator over `bs` (from `0`) has bit 7 clear,
    then every byte of `bs` is `< 0x80`. -/
theorem orAccList_and_0x80_eq_zero_imp_all_lt (bs : List (BitVec 8))
    (h : (orAccList 0 bs) &&& (0x80 : Word) = 0) :
    ∀ b ∈ bs, b.toNat < 0x80 := by
  suffices H : ∀ (acc : Word) (l : List (BitVec 8)),
      (orAccList acc l) &&& (0x80 : Word) = 0 → ∀ b ∈ l, b.toNat < 0x80 from H 0 bs h
  intro acc l
  induction l generalizing acc with
  | nil => intro _ b hb; simp at hb
  | cons c l ih =>
    intro hacc b hb
    rw [orAccList_cons] at hacc
    rcases List.mem_cons.mp hb with rfl | hbl
    · exact byte_zext_and_0x80_eq_zero_imp_lt
        (and_right_of_or_and_eq_zero (orAccList_and_zero_imp_acc _ hacc))
    · exact ih (acc ||| c.zeroExtend 64) hacc b hbl

/-- Peel the head off a `drop`-then-`take`, exposing the `orAccList` recursion. -/
theorem dropTake_succ_peel (bs : List (BitVec 8)) (start m : Nat)
    (h : start < bs.length) :
    (bs.drop start).take (m + 1) = (bs[start]'h) :: (bs.drop (start + 1)).take m := by
  rw [List.drop_eq_getElem_cons h, List.take_succ_cons]

-- ============================================================================
-- Validated one iteration (LBU + OR accumulator + ptr advance + counter dec)
-- ============================================================================

/-- Four-instruction validated iteration body. -/
def sbll_val_iter_prog : Program :=
  [.LBU .x12 .x13 0, .OR .x11 .x11 .x12, .ADDI .x13 .x13 1, .ADDI .x14 .x14 (-1)]

example : sbll_val_iter_prog.length = 4 := rfl

private theorem sbll_val_iter_code_split {base : Word} :
    CodeReq.ofProg base sbll_val_iter_prog =
    (CodeReq.singleton base (.LBU .x12 .x13 0)).union
    ((CodeReq.singleton (base + 4) (.OR .x11 .x11 .x12)).union
    ((CodeReq.singleton (base + 8) (.ADDI .x13 .x13 1)).union
    ((CodeReq.singleton (base + 12) (.ADDI .x14 .x14 (-1))).union
     CodeReq.empty))) := by
  have e2 : (base + 4 + 4 : Word) = base + 8 := by bv_omega
  have e3 : (base + 8 + 4 : Word) = base + 12 := by bv_omega
  simp only [sbll_val_iter_prog, CodeReq.ofProg_cons, CodeReq.ofProg_nil, e2, e3]

/-- One validated iteration: reads byte `i`, ORs it into `x11`, advances `x13`,
    decrements `x14`. -/
theorem sbll_val_iter_spec_within
    (regionBase v11Old v12Old cnt base : Word) (bs : List (BitVec 8)) (i : Nat)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 4 base (base + 16)
      (CodeReq.ofProg base sbll_val_iter_prog)
      ((.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ cnt) **
       bytesRegion regionBase bs)
      ((.x11 ↦ᵣ (v11Old ||| (bs[i]'hi).zeroExtend 64)) **
       (.x12 ↦ᵣ ((bs[i]'hi).zeroExtend 64)) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) **
       (.x14 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) **
       bytesRegion regionBase bs) := by
  rw [sbll_val_iter_code_split]
  have h01 : (base : Word) ≠ base + 4 := by bv_omega
  have h02 : (base : Word) ≠ base + 8 := by bv_omega
  have h03 : (base : Word) ≠ base + 12 := by bv_omega
  have h12 : (base + 4 : Word) ≠ base + 8 := by bv_omega
  have h13 : (base + 4 : Word) ≠ base + 12 := by bv_omega
  have h23 : (base + 8 : Word) ≠ base + 12 := by bv_omega
  have lbu_raw := bytesRegion_lbu_within .x12 .x13 regionBase v12Old base bs i
    (by decide) halign hi hover hvalid
  set byteZext := (bs[i]'hi).zeroExtend 64 with hbz
  -- Step 1: LBU x12, x13, 0.
  have s1 : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU .x12 .x13 0))
      ((.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ cnt) **
       bytesRegion regionBase bs)
      ((.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ byteZext) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ cnt) **
       bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR ((.x11 ↦ᵣ v11Old) ** (.x14 ↦ᵣ cnt)) (by pcFree) lbu_raw)
  -- Step 2: OR x11, x11, x12.
  have or_raw := or_spec_gen_rd_eq_rs1_within .x11 .x12 v11Old byteZext (base + 4) (by nofun)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at or_raw
  have s2 : cpsTripleWithin 1 (base + 4) (base + 8)
      (CodeReq.singleton (base + 4) (.OR .x11 .x11 .x12))
      ((.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ byteZext) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ cnt) **
       bytesRegion regionBase bs)
      ((.x11 ↦ᵣ (v11Old ||| byteZext)) ** (.x12 ↦ᵣ byteZext) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ cnt) **
       bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ cnt) **
         bytesRegion regionBase bs) (by pcFree) or_raw)
  -- Step 3: ADDI x13, x13, 1.
  have addi_ptr_raw := addi_spec_gen_same_within .x13 (regionBase + BitVec.ofNat 64 i)
    1 (base + 8) (by nofun)
  rw [show (base + 8 : Word) + 4 = base + 12 from by bv_omega, se12_1,
      show (regionBase + BitVec.ofNat 64 i) + 1 = regionBase + BitVec.ofNat 64 (i + 1) from by
        rw [word_ofNat_add_one i]; bv_omega] at addi_ptr_raw
  have s3 : cpsTripleWithin 1 (base + 8) (base + 12)
      (CodeReq.singleton (base + 8) (.ADDI .x13 .x13 1))
      ((.x11 ↦ᵣ (v11Old ||| byteZext)) ** (.x12 ↦ᵣ byteZext) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ cnt) **
       bytesRegion regionBase bs)
      ((.x11 ↦ᵣ (v11Old ||| byteZext)) ** (.x12 ↦ᵣ byteZext) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) ** (.x14 ↦ᵣ cnt) **
       bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x11 ↦ᵣ (v11Old ||| byteZext)) ** (.x12 ↦ᵣ byteZext) ** (.x14 ↦ᵣ cnt) **
         bytesRegion regionBase bs) (by pcFree) addi_ptr_raw)
  -- Step 4: ADDI x14, x14, -1.
  have addi_cnt_raw := addi_spec_gen_same_within .x14 cnt (-1) (base + 12) (by nofun)
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at addi_cnt_raw
  have s4 : cpsTripleWithin 1 (base + 12) (base + 16)
      (CodeReq.singleton (base + 12) (.ADDI .x14 .x14 (-1)))
      ((.x11 ↦ᵣ (v11Old ||| byteZext)) ** (.x12 ↦ᵣ byteZext) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) ** (.x14 ↦ᵣ cnt) **
       bytesRegion regionBase bs)
      ((.x11 ↦ᵣ (v11Old ||| byteZext)) ** (.x12 ↦ᵣ byteZext) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) **
       (.x14 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x11 ↦ᵣ (v11Old ||| byteZext)) ** (.x12 ↦ᵣ byteZext) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) ** bytesRegion regionBase bs)
        (by pcFree) addi_cnt_raw)
  -- Disjointness + chain.
  have hd3 : CodeReq.Disjoint
      (CodeReq.singleton (base + 8) (.ADDI .x13 .x13 1))
      ((CodeReq.singleton (base + 12) (.ADDI .x14 .x14 (-1))).union CodeReq.empty) :=
    CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h23)
      (CodeReq.Disjoint.empty_right _)
  have hd2 : CodeReq.Disjoint
      (CodeReq.singleton (base + 4) (.OR .x11 .x11 .x12))
      ((CodeReq.singleton (base + 8) (.ADDI .x13 .x13 1)).union
        ((CodeReq.singleton (base + 12) (.ADDI .x14 .x14 (-1))).union CodeReq.empty)) :=
    CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h12)
      (CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h13)
        (CodeReq.Disjoint.empty_right _))
  have hd1 : CodeReq.Disjoint
      (CodeReq.singleton base (.LBU .x12 .x13 0))
      ((CodeReq.singleton (base + 4) (.OR .x11 .x11 .x12)).union
        ((CodeReq.singleton (base + 8) (.ADDI .x13 .x13 1)).union
          ((CodeReq.singleton (base + 12) (.ADDI .x14 .x14 (-1))).union CodeReq.empty))) :=
    CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h01)
      (CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h02)
        (CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h03)
          (CodeReq.Disjoint.empty_right _)))
  have s4_ext : cpsTripleWithin 1 (base + 12) (base + 16)
      ((CodeReq.singleton (base + 12) (.ADDI .x14 .x14 (-1))).union CodeReq.empty) _ _ :=
    cpsTripleWithin_extend_code
      (fun a _ hcr => by
        show (CodeReq.singleton (base + 12) (.ADDI .x14 .x14 (-1))).union CodeReq.empty a = _
        simp only [CodeReq.union, hcr])
      s4
  have t34 := cpsTripleWithin_seq hd3 s3 s4_ext
  have t234 := cpsTripleWithin_seq hd2 s2 t34
  exact cpsTripleWithin_seq hd1 s1 t234

-- ============================================================================
-- Validated loop body (with back-branch): a 2-exit cpsBranchWithin
-- ============================================================================

/-- Five-instruction validated loop body: one iteration + `BNE x14, x0, back`. -/
def sbll_val_body_prog (back : BitVec 13) : Program :=
  [.LBU .x12 .x13 0, .OR .x11 .x11 .x12, .ADDI .x13 .x13 1, .ADDI .x14 .x14 (-1),
   .BNE .x14 .x0 back]

example (back : BitVec 13) : (sbll_val_body_prog back).length = 5 := rfl

/-- Bundled post for either exit of the validated loop body. -/
@[irreducible]
def sbll_val_body_post (regionBase accFinal byteZext nextPtr cnt' : Word)
    (bs : List (BitVec 8)) (P : Prop) : Assertion :=
  (.x11 ↦ᵣ accFinal) ** (.x12 ↦ᵣ byteZext) ** (.x13 ↦ᵣ nextPtr) ** (.x14 ↦ᵣ cnt') **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs ** ⌜P⌝

theorem sbll_val_body_post_unfold (regionBase accFinal byteZext nextPtr cnt' : Word)
    (bs : List (BitVec 8)) (P : Prop) :
    sbll_val_body_post regionBase accFinal byteZext nextPtr cnt' bs P =
    ((.x11 ↦ᵣ accFinal) ** (.x12 ↦ᵣ byteZext) ** (.x13 ↦ᵣ nextPtr) ** (.x14 ↦ᵣ cnt') **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs ** ⌜P⌝) := by
  delta sbll_val_body_post; rfl

theorem sbll_val_body_post_pure {regionBase accFinal byteZext nextPtr cnt' : Word}
    {bs : List (BitVec 8)} {P : Prop} :
    ∀ hp, sbll_val_body_post regionBase accFinal byteZext nextPtr cnt' bs P hp → P := by
  intro hp hpost
  simp only [sbll_val_body_post_unfold] at hpost
  open EvmAsm.Rv64.Tactics in extract_pure hpost
  exact hpost.1

/-- Step-bounded spec for one pass through the validated loop body. -/
theorem sbll_val_body_spec_within
    (regionBase v11Old v12Old cnt base : Word) (back : BitVec 13)
    (bs : List (BitVec 8)) (i : Nat)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true) :
    let byteZext := (bs[i]'hi).zeroExtend 64
    let cnt'     := cnt + signExtend12 (-1 : BitVec 12)
    cpsBranchWithin 5 base (CodeReq.ofProg base (sbll_val_body_prog back))
      ((.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ cnt) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs)
      ((base + 16) + signExtend13 back)
        (sbll_val_body_post regionBase (v11Old ||| byteZext) byteZext
          (regionBase + BitVec.ofNat 64 (i + 1)) cnt' bs (cnt' ≠ 0))
      (base + 20)
        (sbll_val_body_post regionBase (v11Old ||| byteZext) byteZext
          (regionBase + BitVec.ofNat 64 (i + 1)) cnt' bs (cnt' = 0)) := by
  have hcr_eq : CodeReq.ofProg base (sbll_val_body_prog back) =
      (CodeReq.ofProg base sbll_val_iter_prog).union
      ((CodeReq.singleton (base + 16) (.BNE .x14 .x0 back)).union CodeReq.empty) := by
    funext a
    have e2 : (base + 4 + 4 : Word) = base + 8 := by bv_omega
    have e3 : (base + 8 + 4 : Word) = base + 12 := by bv_omega
    have e4 : (base + 12 + 4 : Word) = base + 16 := by bv_omega
    simp only [sbll_val_body_prog, sbll_val_iter_prog, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
      CodeReq.union, CodeReq.empty, e2, e3, e4, CodeReq.singleton]
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
    simp [h0, h1, h2, h3, h4]
  rw [hcr_eq]
  simp only [sbll_val_body_post_unfold]
  set byteZext := (bs[i]'hi).zeroExtend 64 with hbz
  set cnt' := cnt + signExtend12 (-1 : BitVec 12) with hcnt
  have iter := sbll_val_iter_spec_within regionBase v11Old v12Old cnt base bs i
    halign hi hover hvalid
  have iter' : cpsTripleWithin 4 base (base + 16)
      (CodeReq.ofProg base sbll_val_iter_prog)
      ((.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ cnt) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs)
      ((.x14 ↦ᵣ cnt') ** (.x0 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ (v11Old ||| byteZext)) ** (.x12 ↦ᵣ byteZext) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) iter)
  have bne_raw := bne_spec_gen_within .x14 .x0 back cnt' (0 : Word) (base + 16)
  have bne_framed : cpsBranchWithin 1 (base + 16)
      (CodeReq.singleton (base + 16) (.BNE .x14 .x0 back))
      ((.x14 ↦ᵣ cnt') ** (.x0 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ (v11Old ||| byteZext)) ** (.x12 ↦ᵣ byteZext) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) ** bytesRegion regionBase bs)
      ((base + 16) + signExtend13 back)
        ((.x11 ↦ᵣ (v11Old ||| byteZext)) ** (.x12 ↦ᵣ byteZext) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) ** (.x14 ↦ᵣ cnt') **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs ** ⌜cnt' ≠ 0⌝)
      (base + 20)
        ((.x11 ↦ᵣ (v11Old ||| byteZext)) ** (.x12 ↦ᵣ byteZext) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) ** (.x14 ↦ᵣ cnt') **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs ** ⌜cnt' = 0⌝) := by
    have h_eq_16_4 : (base + 16 : Word) + 4 = base + 20 := by bv_omega
    rw [h_eq_16_4] at bne_raw
    exact cpsBranchWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsBranchWithin_frameR
        ((.x11 ↦ᵣ (v11Old ||| byteZext)) ** (.x12 ↦ᵣ byteZext) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (i + 1))) ** bytesRegion regionBase bs)
        (by pcFree) bne_raw)
  have hd_iter_bne : (CodeReq.ofProg base sbll_val_iter_prog).Disjoint
      ((CodeReq.singleton (base + 16) (.BNE .x14 .x0 back)).union CodeReq.empty) := by
    refine CodeReq.Disjoint.union_right ?_ (CodeReq.Disjoint.empty_right _)
    apply CodeReq.Disjoint.ofProg_singleton
    apply CodeReq.ofProg_none_range
    intro k hk
    simp only [sbll_val_iter_prog, List.length_cons, List.length_nil] at hk
    interval_cases k <;> bv_omega
  have bne_ext : cpsBranchWithin 1 (base + 16)
      ((CodeReq.singleton (base + 16) (.BNE .x14 .x0 back)).union CodeReq.empty)
      _ _ _ _ _ :=
    cpsBranchWithin_extend_code
      (fun a _ hcr => by
        show (CodeReq.singleton (base + 16) (.BNE .x14 .x0 back)).union CodeReq.empty a = _
        simp only [CodeReq.union, hcr])
      bne_framed
  exact cpsTripleWithin_seq_cpsBranchWithin hd_iter_bne iter' bne_ext

-- ============================================================================
-- n-iteration closure (operational cpsTriple, OR accumulator threaded)
-- ============================================================================

/-- One-step recursion for the threaded accumulator. -/
theorem orAccList_dropTake_succ (acc : Word) (bs : List (BitVec 8)) (start k : Nat)
    (h : start < bs.length) :
    orAccList acc ((bs.drop start).take (k + 1))
      = orAccList (acc ||| (bs[start]'h).zeroExtend 64) ((bs.drop (start + 1)).take k) := by
  rw [dropTake_succ_peel bs start k h, orAccList_cons]

/-- Loop closure for `k + 1` validated iterations from index `start`, threading
    the OR accumulator `acc`. -/
theorem sbll_val_loop_succ_spec_within (k start : Nat)
    (regionBase acc v12Old base : Word) (back : BitVec 13) (bs : List (BitVec 8))
    (halign : regionBase.toNat % 8 = 0) (hk_len : start + k < bs.length)
    (hover : regionBase.toNat + (start + k) < 2 ^ 64)
    (hwin : ∀ j, j < k + 1 →
        isValidByteAccess (regionBase + BitVec.ofNat 64 (start + j)) = true)
    (hback : (base + 16) + signExtend13 back = base) :
    cpsTripleWithin (5 * (k + 1)) base (base + 20)
      (CodeReq.ofProg base (sbll_val_body_prog back))
      ((.x11 ↦ᵣ acc) ** (.x12 ↦ᵣ v12Old) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 start)) **
       (.x14 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion regionBase bs)
      ((.x11 ↦ᵣ orAccList acc ((bs.drop start).take (k + 1))) **
       (.x12 ↦ᵣ ((bs[start + k]'(by omega)).zeroExtend 64)) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (start + (k + 1)))) **
       (.x14 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion regionBase bs) := by
  induction k generalizing start acc v12Old with
  | zero =>
    have hvalid0 := hwin 0 (by omega)
    rw [show start + 0 = start from rfl] at hvalid0
    have body := sbll_val_body_spec_within regionBase acc v12Old (1 : Word) base back bs start
      halign (by omega) (by omega) hvalid0
    rw [cnt_dec_1] at body
    set byteZext := (bs[start]'(by omega : start < bs.length)).zeroExtend 64 with hbz
    have h_absurd : ∀ hp,
        sbll_val_body_post regionBase (acc ||| byteZext) byteZext
          (regionBase + BitVec.ofNat 64 (start + 1)) (0 : Word) bs ((0 : Word) ≠ 0) hp → False :=
      fun hp hpost => sbll_val_body_post_pure hp hpost rfl
    have tri := cpsBranchWithin_ntakenPath body h_absurd
    rw [orAccList_dropTake_succ acc bs start 0 (by omega), List.take_zero, orAccList_nil]
    exact cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [sbll_val_body_post_unfold] at hp
        open EvmAsm.Rv64.Tactics in xperm_pure hp)
      tri
  | succ k ih =>
    have hvalid0 := hwin 0 (by omega)
    rw [show start + 0 = start from rfl] at hvalid0
    have body := sbll_val_body_spec_within regionBase acc v12Old (BitVec.ofNat 64 (k + 1 + 1))
      base back bs start halign (by omega) (by omega) hvalid0
    rw [word_ofNat_succ_dec (k + 1)] at body
    set byteZext := (bs[start]'(by omega : start < bs.length)).zeroExtend 64 with hbz
    have hne : BitVec.ofNat 64 (k + 1) ≠ (0 : Word) :=
      word_ofNat_succ_ne_zero k (by omega)
    have h_absurd : ∀ hp,
        sbll_val_body_post regionBase (acc ||| byteZext) byteZext
          (regionBase + BitVec.ofNat 64 (start + 1)) (BitVec.ofNat 64 (k + 1)) bs
          ((BitVec.ofNat 64 (k + 1) : Word) = 0) hp → False :=
      fun hp hpost => absurd (sbll_val_body_post_pure hp hpost) hne
    have tri1 := cpsBranchWithin_takenPath body h_absurd
    rw [hback] at tri1
    have tri1' : cpsTripleWithin 5 base base
        (CodeReq.ofProg base (sbll_val_body_prog back))
        ((.x11 ↦ᵣ acc) ** (.x12 ↦ᵣ v12Old) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 start)) **
         (.x14 ↦ᵣ BitVec.ofNat 64 (k + 1 + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion regionBase bs)
        ((.x11 ↦ᵣ (acc ||| byteZext)) ** (.x12 ↦ᵣ byteZext) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (start + 1))) **
         (.x14 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion regionBase bs) :=
      cpsTripleWithin_weaken
        (fun _ hp => hp)
        (fun _ hp => by
          simp only [sbll_val_body_post_unfold] at hp
          open EvmAsm.Rv64.Tactics in xperm_pure hp)
        tri1
    have hwin' : ∀ j, j < k + 1 →
        isValidByteAccess (regionBase + BitVec.ofNat 64 ((start + 1) + j)) = true := by
      intro j hj
      have h := hwin (j + 1) (by omega)
      rwa [show start + (j + 1) = (start + 1) + j from by omega] at h
    have ihspec := ih (start + 1) (acc ||| byteZext) byteZext (by omega) (by omega) hwin'
    have composed :=
      cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) tri1' ihspec
    rw [show (5 * (k + 1 + 1)) = 5 + 5 * (k + 1) from by ring,
        orAccList_dropTake_succ acc bs start (k + 1) (by omega)]
    simp only [show start + (k + 1) = (start + 1) + k from by omega,
               show start + (k + 1 + 1) = (start + 1) + (k + 1) from by omega]
    exact composed

/-- General `n ≥ 1` validated loop closure: accumulator `acc` ends at
    `orAccList acc (bs.take n)`. -/
theorem sbll_val_loop_n_spec_within (n : Nat) (hn1 : 1 ≤ n)
    (regionBase acc v12Old base : Word) (back : BitVec 13) (bs : List (BitVec 8))
    (halign : regionBase.toNat % 8 = 0) (hn_len : n ≤ bs.length)
    (hover : regionBase.toNat + n < 2 ^ 64)
    (hwin : ∀ i, i < n → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hback : (base + 16) + signExtend13 back = base) :
    cpsTripleWithin (5 * n) base (base + 20)
      (CodeReq.ofProg base (sbll_val_body_prog back))
      ((.x11 ↦ᵣ acc) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ regionBase) **
       (.x14 ↦ᵣ BitVec.ofNat 64 n) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion regionBase bs)
      ((.x11 ↦ᵣ orAccList acc (bs.take n)) **
       (.x12 ↦ᵣ ((bs[n - 1]'(by omega)).zeroExtend 64)) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 n)) **
       (.x14 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion regionBase bs) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have core := sbll_val_loop_succ_spec_within k 0 regionBase acc v12Old base back bs
    halign (by omega) (by omega)
    (by intro j hj; rw [Nat.zero_add]; exact hwin j hj) hback
  simp only [Nat.zero_add, List.drop_zero] at core
  rw [show regionBase + BitVec.ofNat 64 0 = regionBase from by simp] at core
  exact core

-- ============================================================================
-- Post-loop bit-7 check + full validated spec (2-exit cpsBranchWithin)
-- ============================================================================

theorem se12_0x80 : signExtend12 (0x80 : BitVec 12) = (0x80 : Word) := by decide

/-- Full validated loop: the OR-accumulator loop followed by `ANDI x15, x11, 0x80`
    and `BNE x15, x0, fail`. Success (`x15 = 0`) means every scanned byte had
    bit 7 clear (`acc &&& 0x80 = 0`); fail means some byte had bit 7 set. -/
theorem sbll_val_loop_checked_spec_within (n : Nat) (hn1 : 1 ≤ n)
    (regionBase acc v12Old v15Old base : Word) (back fail : BitVec 13) (bs : List (BitVec 8))
    (halign : regionBase.toNat % 8 = 0) (hn_len : n ≤ bs.length)
    (hover : regionBase.toNat + n < 2 ^ 64)
    (hwin : ∀ i, i < n → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hback : (base + 16) + signExtend13 back = base) :
    let accF := orAccList acc (bs.take n)
    cpsBranchWithin (5 * n + 2) base
      ((CodeReq.ofProg base (sbll_val_body_prog back)).union
        ((CodeReq.singleton (base + 20) (.ANDI .x15 .x11 0x80)).union
          ((CodeReq.singleton (base + 24) (.BNE .x15 .x0 fail)).union CodeReq.empty)))
      ((.x11 ↦ᵣ acc) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ regionBase) **
       (.x14 ↦ᵣ BitVec.ofNat 64 n) ** (.x0 ↦ᵣ (0 : Word)) ** (.x15 ↦ᵣ v15Old) **
       bytesRegion regionBase bs)
      ((base + 24) + signExtend13 fail)
        ((.x15 ↦ᵣ (accF &&& (0x80 : Word))) ** (.x11 ↦ᵣ accF) **
         (.x12 ↦ᵣ ((bs[n - 1]'(by omega)).zeroExtend 64)) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 n)) ** (.x14 ↦ᵣ (0 : Word)) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
         ⌜accF &&& (0x80 : Word) ≠ 0⌝)
      (base + 28)
        ((.x15 ↦ᵣ (accF &&& (0x80 : Word))) ** (.x11 ↦ᵣ accF) **
         (.x12 ↦ᵣ ((bs[n - 1]'(by omega)).zeroExtend 64)) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 n)) ** (.x14 ↦ᵣ (0 : Word)) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
         ⌜accF &&& (0x80 : Word) = 0⌝) := by
  intro accF
  -- Loop (5n steps, base → base+20), framed with x15.
  have loop := sbll_val_loop_n_spec_within n hn1 regionBase acc v12Old base back bs
    halign hn_len hover hwin hback
  have loopF : cpsTripleWithin (5 * n) base (base + 20)
      (CodeReq.ofProg base (sbll_val_body_prog back))
      ((.x11 ↦ᵣ acc) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ regionBase) **
       (.x14 ↦ᵣ BitVec.ofNat 64 n) ** (.x0 ↦ᵣ (0 : Word)) ** (.x15 ↦ᵣ v15Old) **
       bytesRegion regionBase bs)
      ((.x11 ↦ᵣ accF) ** (.x15 ↦ᵣ v15Old) **
       (.x12 ↦ᵣ ((bs[n - 1]'(by omega)).zeroExtend 64)) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 n)) ** (.x14 ↦ᵣ (0 : Word)) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR (.x15 ↦ᵣ v15Old) (by pcFree) loop)
  -- ANDI x15, x11, 0x80 (base+20 → base+24): x15 := accF &&& 0x80.
  have andi_raw := andi_spec_gen_within .x15 .x11 v15Old accF 0x80 (base + 20) (by nofun)
  rw [show (base + 20 : Word) + 4 = base + 24 from by bv_omega, se12_0x80] at andi_raw
  have andi : cpsTripleWithin 1 (base + 20) (base + 24)
      (CodeReq.singleton (base + 20) (.ANDI .x15 .x11 0x80))
      ((.x11 ↦ᵣ accF) ** (.x15 ↦ᵣ v15Old) **
       (.x12 ↦ᵣ ((bs[n - 1]'(by omega)).zeroExtend 64)) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 n)) ** (.x14 ↦ᵣ (0 : Word)) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs)
      ((.x15 ↦ᵣ (accF &&& (0x80 : Word))) ** (.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ accF) **
       (.x12 ↦ᵣ ((bs[n - 1]'(by omega)).zeroExtend 64)) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 n)) ** (.x14 ↦ᵣ (0 : Word)) **
       bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x12 ↦ᵣ ((bs[n - 1]'(by omega)).zeroExtend 64)) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 n)) ** (.x14 ↦ᵣ (0 : Word)) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs) (by pcFree) andi_raw)
  -- BNE x15, x0, fail (base+24): fail if accF &&& 0x80 ≠ 0.
  have bne_raw := bne_spec_gen_within .x15 .x0 fail (accF &&& (0x80 : Word)) (0 : Word) (base + 24)
  have bne_framed : cpsBranchWithin 1 (base + 24)
      (CodeReq.singleton (base + 24) (.BNE .x15 .x0 fail))
      ((.x15 ↦ᵣ (accF &&& (0x80 : Word))) ** (.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ accF) **
       (.x12 ↦ᵣ ((bs[n - 1]'(by omega)).zeroExtend 64)) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 n)) ** (.x14 ↦ᵣ (0 : Word)) **
       bytesRegion regionBase bs)
      ((base + 24) + signExtend13 fail)
        ((.x15 ↦ᵣ (accF &&& (0x80 : Word))) ** (.x11 ↦ᵣ accF) **
         (.x12 ↦ᵣ ((bs[n - 1]'(by omega)).zeroExtend 64)) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 n)) ** (.x14 ↦ᵣ (0 : Word)) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
         ⌜accF &&& (0x80 : Word) ≠ 0⌝)
      (base + 28)
        ((.x15 ↦ᵣ (accF &&& (0x80 : Word))) ** (.x11 ↦ᵣ accF) **
         (.x12 ↦ᵣ ((bs[n - 1]'(by omega)).zeroExtend 64)) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 n)) ** (.x14 ↦ᵣ (0 : Word)) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
         ⌜accF &&& (0x80 : Word) = 0⌝) := by
    have h_eq_24_4 : (base + 24 : Word) + 4 = base + 28 := by bv_omega
    rw [h_eq_24_4] at bne_raw
    exact cpsBranchWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsBranchWithin_frameR
        ((.x11 ↦ᵣ accF) ** (.x12 ↦ᵣ ((bs[n - 1]'(by omega)).zeroExtend 64)) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 n)) ** (.x14 ↦ᵣ (0 : Word)) **
         bytesRegion regionBase bs) (by pcFree) bne_raw)
  -- Compose ANDI ∘ BNE, then loop ∘ (ANDI ∘ BNE).
  have hd_andi_bne : (CodeReq.singleton (base + 20) (.ANDI .x15 .x11 0x80)).Disjoint
      ((CodeReq.singleton (base + 24) (.BNE .x15 .x0 fail)).union CodeReq.empty) :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega)) (CodeReq.Disjoint.empty_right _)
  have bne_ext : cpsBranchWithin 1 (base + 24)
      ((CodeReq.singleton (base + 24) (.BNE .x15 .x0 fail)).union CodeReq.empty)
      _ _ _ _ _ :=
    cpsBranchWithin_extend_code
      (fun a _ hcr => by
        show (CodeReq.singleton (base + 24) (.BNE .x15 .x0 fail)).union CodeReq.empty a = _
        simp only [CodeReq.union, hcr])
      bne_framed
  have andi_bne :=
    cpsTripleWithin_seq_cpsBranchWithin hd_andi_bne andi bne_ext
  have hd_loop_rest : (CodeReq.ofProg base (sbll_val_body_prog back)).Disjoint
      ((CodeReq.singleton (base + 20) (.ANDI .x15 .x11 0x80)).union
        ((CodeReq.singleton (base + 24) (.BNE .x15 .x0 fail)).union CodeReq.empty)) := by
    refine CodeReq.Disjoint.union_right ?_ (CodeReq.Disjoint.union_right ?_
      (CodeReq.Disjoint.empty_right _))
    · apply CodeReq.Disjoint.ofProg_singleton
      apply CodeReq.ofProg_none_range
      intro k hk
      simp only [sbll_val_body_prog, List.length_cons, List.length_nil] at hk
      interval_cases k <;> bv_omega
    · apply CodeReq.Disjoint.ofProg_singleton
      apply CodeReq.ofProg_none_range
      intro k hk
      simp only [sbll_val_body_prog, List.length_cons, List.length_nil] at hk
      interval_cases k <;> bv_omega
  have composed := cpsTripleWithin_seq_cpsBranchWithin hd_loop_rest loopF andi_bne
  rw [show 5 * n + 2 = 5 * n + (1 + 1) from by ring]
  exact composed

-- ============================================================================
-- Bridge to the pure spec (no `hsingle`)
-- ============================================================================

/-- **Bridge (no `hsingle`).** On the success exit of the validated loop seeded
    at `acc = 0` — where `sbll_val_loop_checked_spec_within` establishes
    `orAccList 0 bs &&& 0x80 = 0` *operationally* — the payload decodes to
    `bs.length` single-byte items. The `< 0x80` precondition the assume-version
    of the loop required is now discharged by the machine-checked accumulator. -/
theorem sbll_val_loop_bridge (bs : List (BitVec 8))
    (h : orAccList 0 bs &&& (0x80 : Word) = 0) :
    decodeItems (2 * bs.length) bs = some (bs.map (fun b => RLPItem.bytes [b]), []) :=
  decodeItems_singleByte_run bs (2 * bs.length)
    (orAccList_and_0x80_eq_zero_imp_all_lt bs h) (le_refl _)

/-- Cross-dword cross-check: the validated loop over a 10-byte payload (spanning
    two dwords) scans bytes `0…9`, and on success decodes to 10 single-byte
    items — with no `hsingle` assumption (the `< 0x80` fact is machine-checked). -/
example (base regionBase v12Old v15Old : Word) (back fail : BitVec 13)
    (bs : List (BitVec 8)) (hlen : bs.length = 10) (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + 10 < 2 ^ 64)
    (hwin : ∀ i, i < 10 → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hback : (base + 16) + signExtend13 back = base) :
    cpsBranchWithin (5 * 10 + 2) base
      ((CodeReq.ofProg base (sbll_val_body_prog back)).union
        ((CodeReq.singleton (base + 20) (.ANDI .x15 .x11 0x80)).union
          ((CodeReq.singleton (base + 24) (.BNE .x15 .x0 fail)).union CodeReq.empty)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ regionBase) **
       (.x14 ↦ᵣ BitVec.ofNat 64 10) ** (.x0 ↦ᵣ (0 : Word)) ** (.x15 ↦ᵣ v15Old) **
       bytesRegion regionBase bs)
      ((base + 24) + signExtend13 fail)
        ((.x15 ↦ᵣ (orAccList 0 (bs.take 10) &&& (0x80 : Word))) **
         (.x11 ↦ᵣ orAccList 0 (bs.take 10)) **
         (.x12 ↦ᵣ ((bs[10 - 1]'(by omega)).zeroExtend 64)) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 10)) ** (.x14 ↦ᵣ (0 : Word)) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
         ⌜orAccList 0 (bs.take 10) &&& (0x80 : Word) ≠ 0⌝)
      (base + 28)
        ((.x15 ↦ᵣ (orAccList 0 (bs.take 10) &&& (0x80 : Word))) **
         (.x11 ↦ᵣ orAccList 0 (bs.take 10)) **
         (.x12 ↦ᵣ ((bs[10 - 1]'(by omega)).zeroExtend 64)) **
         (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 10)) ** (.x14 ↦ᵣ (0 : Word)) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
         ⌜orAccList 0 (bs.take 10) &&& (0x80 : Word) = 0⌝)
    ∧ (orAccList 0 bs &&& (0x80 : Word) = 0 →
        decodeItems 20 bs = some (bs.map (fun b => RLPItem.bytes [b]), [])) :=
  ⟨sbll_val_loop_checked_spec_within 10 (by omega) regionBase 0 v12Old v15Old base back fail bs
      halign (by omega) hover hwin hback,
   fun h => by have hd := sbll_val_loop_bridge bs h; rwa [hlen] at hd⟩

end EvmAsm.Rv64.RLP
