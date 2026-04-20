/-
  EvmAsm.Rv64.RLP.Phase2LongIter

  EL.3 Phase 2 (long form) — one full loop iteration body (no back-branch).

  Extends the load-and-accumulate step with pointer and counter advance,
  giving the 5-instruction body executed once per big-endian
  length-of-length byte:

      LBU  x12, x13, 0        ; byte = mem[x13]
      SLLI x11, x11, 8        ; length <<= 8
      ADD  x11, x11, x12      ; length += byte
      ADDI x13, x13, 1        ; ptr += 1
      ADDI x14, x14, -1       ; counter -= 1

  The BNE back-branch that closes the loop is the next slice; this file
  stops at "one iteration worth of state change".

  Register usage:
    x11 — accumulated length (mutated)
    x12 — scratch byte slot (mutated to hold the loaded byte)
    x13 — byte pointer (mutated: advances by 1)
    x14 — iteration counter (mutated: decrements by 1)
-/

import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.Program
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_0 se12_1 bv6_toNat_8)

-- ============================================================================
-- Program definition
-- ============================================================================

/-- Five-instruction loop body: load-and-accumulate followed by pointer
    advance and counter decrement. -/
def rlp_phase2_long_iter_prog : Program :=
  [.LBU .x12 .x13 0, .SLLI .x11 .x11 8, .ADD .x11 .x11 .x12,
   .ADDI .x13 .x13 1, .ADDI .x14 .x14 (-1)]

example : rlp_phase2_long_iter_prog.length = 5 := rfl

-- ============================================================================
-- Spec
-- ============================================================================

/-- Bundled post: length folds in the new byte, `x12` holds the byte,
    `x13` has advanced by one, `x14` has decremented by one; memory is
    unchanged. -/
@[irreducible]
def rlp_phase2_long_iter_post
    (len ptr cnt byteZext word_val dwordAddr : Word) : Assertion :=
  let length' := (len <<< 8) + byteZext
  let ptr'    := ptr + 1
  let cnt'    := cnt + signExtend12 (-1 : BitVec 12)
  (.x11 ↦ᵣ length') ** (.x13 ↦ᵣ ptr') ** (.x14 ↦ᵣ cnt') **
    (.x12 ↦ᵣ byteZext) ** (dwordAddr ↦ₘ word_val)

theorem rlp_phase2_long_iter_post_unfold
    (len ptr cnt byteZext word_val dwordAddr : Word) :
    rlp_phase2_long_iter_post len ptr cnt byteZext word_val dwordAddr =
    ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) **
     (.x13 ↦ᵣ (ptr + 1)) **
     (.x14 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) **
     (.x12 ↦ᵣ byteZext) ** (dwordAddr ↦ₘ word_val)) := by
  delta rlp_phase2_long_iter_post; rfl

-- ============================================================================
-- Proof infrastructure: CodeReq split and disjointness
-- ============================================================================

/-- Split `ofProg base iter_prog` into five singleton CodeReqs plus an
    `empty` tail. Each instruction lives at a distinct 4-byte offset. -/
private theorem iter_code_split (base : Word) :
    CodeReq.ofProg base rlp_phase2_long_iter_prog =
    (CodeReq.singleton base (.LBU .x12 .x13 0)).union
    ((CodeReq.singleton (base + 4) (.SLLI .x11 .x11 8)).union
    ((CodeReq.singleton (base + 8) (.ADD .x11 .x11 .x12)).union
    ((CodeReq.singleton (base + 12) (.ADDI .x13 .x13 1)).union
    ((CodeReq.singleton (base + 16) (.ADDI .x14 .x14 (-1))).union
     CodeReq.empty)))) := by
  have e2 : (base + 4 + 4 : Word) = base + 8 := by bv_omega
  have e3 : (base + 8 + 4 : Word) = base + 12 := by bv_omega
  have e4 : (base + 12 + 4 : Word) = base + 16 := by bv_omega
  simp only [rlp_phase2_long_iter_prog, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    e2, e3, e4]

/-- Pairwise distinctness of the five instruction addresses; helper for
    building disjointness proofs between singleton CodeReqs. -/
private theorem iter_addrs_distinct (base : Word) :
    (base : Word) ≠ base + 4 ∧ base ≠ base + 8 ∧ base ≠ base + 12 ∧
    base ≠ base + 16 ∧
    (base + 4 : Word) ≠ base + 8 ∧ base + 4 ≠ base + 12 ∧
    base + 4 ≠ base + 16 ∧
    (base + 8 : Word) ≠ base + 12 ∧ base + 8 ≠ base + 16 ∧
    (base + 12 : Word) ≠ base + 16 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

-- ============================================================================
-- Main spec
-- ============================================================================

/-- `cpsTriple` spec for one iteration of the long-form length loop.

    Composes five instruction specs — LBU + SLLI + ADD + ADDI (ptr) +
    ADDI (counter) — each framed with the registers and memory not
    touched by that instruction. -/
theorem rlp_phase2_long_iter_spec
    (len ptr cnt v12_old word_val dwordAddr : Word) (base : Word)
    (halign : alignToDword ptr = dwordAddr)
    (hvalid : isValidByteAccess ptr = true) :
    let byteZext := (extractByte word_val (byteOffset ptr)).zeroExtend 64
    cpsTriple base (base + 20)
      (CodeReq.ofProg base rlp_phase2_long_iter_prog)
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ cnt) **
       (.x12 ↦ᵣ v12_old) ** (dwordAddr ↦ₘ word_val))
      (rlp_phase2_long_iter_post len ptr cnt byteZext word_val dwordAddr) := by
  simp only [rlp_phase2_long_iter_post_unfold]
  rw [iter_code_split]
  -- Helpers: `signExtend12 1 = 1` and `signExtend12 0 = 0`.
  have h_se1 := se12_1
  have h_se0 := se12_0
  have h_shamt := bv6_toNat_8
  -- Distinct-addresses plumbing.
  obtain ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩ :=
    iter_addrs_distinct base
  set byteZext := (extractByte word_val (byteOffset ptr)).zeroExtend 64
  -- Step 1: LBU x12, x13, 0.
  have halign0 : alignToDword (ptr + signExtend12 (0 : BitVec 12)) = dwordAddr := by
    rw [h_se0]; simpa using halign
  have hvalid0 : isValidByteAccess (ptr + signExtend12 (0 : BitVec 12)) = true := by
    rw [h_se0]; simpa using hvalid
  have lbu_raw := generic_lbu_spec .x12 .x13 ptr v12_old 0 base dwordAddr word_val
    (by nofun) halign0 hvalid0
  rw [show ptr + signExtend12 (0 : BitVec 12) = ptr from by
        rw [h_se0]; bv_omega] at lbu_raw
  -- Step 2: SLLI x11, x11, 8.
  have slli_raw := slli_spec_gen_same .x11 len 8 (base + 4) (by nofun)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at slli_raw
  rw [h_shamt] at slli_raw
  -- Step 3: ADD x11, x11, x12.
  have add_raw := add_spec_gen_rd_eq_rs1 .x11 .x12 (len <<< 8) byteZext
    (base + 8) (by nofun)
  rw [show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at add_raw
  -- Step 4: ADDI x13, x13, 1.
  have addi_ptr_raw := addi_spec_gen_same .x13 ptr 1 (base + 12) (by nofun)
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at addi_ptr_raw
  rw [h_se1] at addi_ptr_raw
  -- Step 5: ADDI x14, x14, -1.
  have addi_cnt_raw := addi_spec_gen_same .x14 cnt (-1) (base + 16) (by nofun)
  rw [show (base + 16 : Word) + 4 = base + 20 from by bv_omega] at addi_cnt_raw
  -- Frame each step with the assertions it doesn't touch, and chain.
  -- To keep the proof compact, we use `cpsTriple_weaken` with
  -- `xperm_hyp` to reshape pre/post to a common right-associated form.
  have frame_and_perm :=
    fun {entry exit_ : Word} {cr : CodeReq} {P P' Q Q' : Assertion}
        (hpre : ∀ h, P' h → P h) (hpost : ∀ h, Q h → Q' h)
        (h : cpsTriple entry exit_ cr P Q) =>
      cpsTriple_weaken (P := P) (Q := Q) (P' := P') (Q' := Q') hpre hpost h
  -- Step 1 framed with (x11, x14, memory) — leaves (x12, x13) to LBU.
  have s1 : cpsTriple base (base + 4)
      (CodeReq.singleton base (.LBU .x12 .x13 0))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ cnt) **
       (.x12 ↦ᵣ v12_old) ** (dwordAddr ↦ₘ word_val))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ cnt) **
       (.x12 ↦ᵣ byteZext) ** (dwordAddr ↦ₘ word_val)) :=
    frame_and_perm
      (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsTriple_frameR
        ((.x11 ↦ᵣ len) ** (.x14 ↦ᵣ cnt)) (by pcFree) lbu_raw)
  -- Step 2 (SLLI x11 x11 8) — leaves (x13, x14, x12, mem) untouched.
  have s2 : cpsTriple (base + 4) (base + 8)
      (CodeReq.singleton (base + 4) (.SLLI .x11 .x11 8))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ cnt) **
       (.x12 ↦ᵣ byteZext) ** (dwordAddr ↦ₘ word_val))
      ((.x11 ↦ᵣ (len <<< 8)) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ cnt) **
       (.x12 ↦ᵣ byteZext) ** (dwordAddr ↦ₘ word_val)) :=
    frame_and_perm
      (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsTriple_frameR
        ((.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ cnt) ** (.x12 ↦ᵣ byteZext) **
         (dwordAddr ↦ₘ word_val)) (by pcFree) slli_raw)
  -- Step 3 (ADD x11 x11 x12) — uses (x11, x12); frames (x13, x14, mem).
  have s3 : cpsTriple (base + 8) (base + 12)
      (CodeReq.singleton (base + 8) (.ADD .x11 .x11 .x12))
      ((.x11 ↦ᵣ (len <<< 8)) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ cnt) **
       (.x12 ↦ᵣ byteZext) ** (dwordAddr ↦ₘ word_val))
      ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) ** (.x13 ↦ᵣ ptr) **
       (.x14 ↦ᵣ cnt) ** (.x12 ↦ᵣ byteZext) **
       (dwordAddr ↦ₘ word_val)) :=
    frame_and_perm
      (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsTriple_frameR
        ((.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ cnt) ** (dwordAddr ↦ₘ word_val))
        (by pcFree) add_raw)
  -- Step 4 (ADDI x13 x13 1) — mutates x13; frames the rest.
  have s4 : cpsTriple (base + 12) (base + 16)
      (CodeReq.singleton (base + 12) (.ADDI .x13 .x13 1))
      ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) ** (.x13 ↦ᵣ ptr) **
       (.x14 ↦ᵣ cnt) ** (.x12 ↦ᵣ byteZext) **
       (dwordAddr ↦ₘ word_val))
      ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) ** (.x13 ↦ᵣ (ptr + 1)) **
       (.x14 ↦ᵣ cnt) ** (.x12 ↦ᵣ byteZext) **
       (dwordAddr ↦ₘ word_val)) :=
    frame_and_perm
      (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsTriple_frameR
        ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) ** (.x14 ↦ᵣ cnt) **
         (.x12 ↦ᵣ byteZext) ** (dwordAddr ↦ₘ word_val))
        (by pcFree) addi_ptr_raw)
  -- Step 5 (ADDI x14 x14 -1) — mutates x14; frames the rest.
  have s5 : cpsTriple (base + 16) (base + 20)
      (CodeReq.singleton (base + 16) (.ADDI .x14 .x14 (-1)))
      ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) ** (.x13 ↦ᵣ (ptr + 1)) **
       (.x14 ↦ᵣ cnt) ** (.x12 ↦ᵣ byteZext) **
       (dwordAddr ↦ₘ word_val))
      ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) ** (.x13 ↦ᵣ (ptr + 1)) **
       (.x14 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) **
       (.x12 ↦ᵣ byteZext) ** (dwordAddr ↦ₘ word_val)) :=
    frame_and_perm
      (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
      (cpsTriple_frameR
        ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) ** (.x13 ↦ᵣ (ptr + 1)) **
         (.x12 ↦ᵣ byteZext) ** (dwordAddr ↦ₘ word_val))
        (by pcFree) addi_cnt_raw)
  -- Disjointness builders for the union chain produced by `cpsTriple_seq`.
  have hd5 : CodeReq.Disjoint
      (CodeReq.singleton (base + 16) (.ADDI .x14 .x14 (-1)))
      CodeReq.empty := CodeReq.Disjoint.empty_right _
  have hd4 : CodeReq.Disjoint
      (CodeReq.singleton (base + 12) (.ADDI .x13 .x13 1))
      ((CodeReq.singleton (base + 16) (.ADDI .x14 .x14 (-1))).union
        CodeReq.empty) :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton h34 _ _)
      (CodeReq.Disjoint.empty_right _)
  have hd3 : CodeReq.Disjoint
      (CodeReq.singleton (base + 8) (.ADD .x11 .x11 .x12))
      ((CodeReq.singleton (base + 12) (.ADDI .x13 .x13 1)).union
        ((CodeReq.singleton (base + 16) (.ADDI .x14 .x14 (-1))).union
          CodeReq.empty)) :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton h23 _ _)
      (CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton h24 _ _)
        (CodeReq.Disjoint.empty_right _))
  have hd2 : CodeReq.Disjoint
      (CodeReq.singleton (base + 4) (.SLLI .x11 .x11 8))
      ((CodeReq.singleton (base + 8) (.ADD .x11 .x11 .x12)).union
        ((CodeReq.singleton (base + 12) (.ADDI .x13 .x13 1)).union
          ((CodeReq.singleton (base + 16) (.ADDI .x14 .x14 (-1))).union
            CodeReq.empty))) :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton h12 _ _)
      (CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton h13 _ _)
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.singleton h14 _ _)
          (CodeReq.Disjoint.empty_right _)))
  have hd1 : CodeReq.Disjoint
      (CodeReq.singleton base (.LBU .x12 .x13 0))
      ((CodeReq.singleton (base + 4) (.SLLI .x11 .x11 8)).union
        ((CodeReq.singleton (base + 8) (.ADD .x11 .x11 .x12)).union
          ((CodeReq.singleton (base + 12) (.ADDI .x13 .x13 1)).union
            ((CodeReq.singleton (base + 16) (.ADDI .x14 .x14 (-1))).union
              CodeReq.empty)))) :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton h01 _ _)
      (CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton h02 _ _)
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.singleton h03 _ _)
          (CodeReq.Disjoint.union_right
            (CodeReq.Disjoint.singleton h04 _ _)
            (CodeReq.Disjoint.empty_right _))))
  -- Extend s5's CR with a trailing empty.
  have s5_ext : cpsTriple (base + 16) (base + 20)
      ((CodeReq.singleton (base + 16) (.ADDI .x14 .x14 (-1))).union
        CodeReq.empty) _ _ :=
    cpsTriple_extend_code
      (fun a _ hcr => by
        show (CodeReq.singleton (base + 16) (.ADDI .x14 .x14 (-1))).union
            CodeReq.empty a = _
        simp only [CodeReq.union, hcr])
      s5
  -- Chain bottom up.
  have t45 := cpsTriple_seq _ _ _ _ _ hd4 _ _ _ s4 s5_ext
  have t345 := cpsTriple_seq _ _ _ _ _ hd3 _ _ _ s3 t45
  have t2345 := cpsTriple_seq _ _ _ _ _ hd2 _ _ _ s2 t345
  exact cpsTriple_seq _ _ _ _ _ hd1 _ _ _ s1 t2345

end EvmAsm.Rv64.RLP
