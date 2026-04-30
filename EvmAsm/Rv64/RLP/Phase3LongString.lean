/-
  EvmAsm.Rv64.RLP.Phase3LongString

  EL.3 Phase 3 (long-string entry): seed the long-form length-of-length
  loop for the long byte-string category.

  When Phase 1's classifier reaches `e3` — i.e. the prefix byte
  `p ∈ [0xB8, 0xC0)` — the RLP item is a *long byte string* whose total
  payload length is encoded in the next `(p − 0xB7)` bytes after the
  prefix. The Phase 3 entry leaves the machine in the canonical pre-loop
  state expected by the Phase 2 long-form loop:

      x14 = lenLen   = p − 0xB7   (number of length bytes; range [1, 8])
      x11 = len_acc  = 0          (initial accumulator)
      x13 = data_ptr = old_ptr+1  (advance past the prefix byte; the next
                                   `lenLen` bytes are the encoded length)

  Three instructions:

      ADDI x14, x5, -0xB7     ; lenLen = prefix - 0xB7
      ADDI x11, x0, 0         ; len_acc := 0
      ADDI x13, x13, 1        ; data_ptr += 1

  After this entry block, the caller dispatches to the matching
  `rlp_phase2_long_loop_*_byte_spec` (or the planned `n`-iteration
  closure) on `x14` to fold the length bytes into `x11`.

  Register usage:
    x0  — zero register (unchanged)
    x5  — input: the RLP prefix byte (preserved)
    x11 — output: cleared length accumulator (= 0)
    x13 — input/output: byte pointer (advances by 1)
    x14 — output: length-of-length counter (= prefix − 0xB7)
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- Program definition
-- ============================================================================

/-- Three-instruction long-string entry emitter:
    `ADDI x14, x5, -0xB7 ; ADDI x11, x0, 0 ; ADDI x13, x13, 1`. -/
def rlp_phase3_long_string_prog : Program :=
  [.ADDI .x14 .x5 (-0xB7), .ADDI .x11 .x0 0, .ADDI .x13 .x13 1]

example : rlp_phase3_long_string_prog.length = 3 := rfl

/-! ## Concrete sanity checks -/

-- Long byte string with prefix 0xB8 (1-byte length): lenLen = 1.
example : ((0xB8 : Word) + signExtend12 (-(0xB7 : BitVec 12))) = (1 : Word) := by decide

-- Long byte string with prefix 0xBF (8-byte length): lenLen = 8.
example : ((0xBF : Word) + signExtend12 (-(0xB7 : BitVec 12))) = (8 : Word) := by decide

-- ADDI x11, x0, 0 with x0 = 0: x11 := 0.
example : ((0 : Word) + signExtend12 (0 : BitVec 12)) = (0 : Word) := by decide

-- ============================================================================
-- Spec
-- ============================================================================

/-- `cpsTripleWithin` spec for the long-string entry. After three instructions:
    * `x14` holds `prefix − 0xB7` (length-of-length counter),
    * `x11` is cleared to 0 (initial length accumulator),
    * `x13` has advanced by 1 (skips past the prefix byte),
    * `x5` and `x0` are preserved.

    The spec places no range constraint on `v5`; if the caller reaches
    this program outside the long-string category, the subtraction
    `v5 + signExtend12 (-0xB7)` still has a well-defined value but does
    not interpret as a length-of-length. Downstream consumers compose
    this with the preceding Phase 1 `e3` exit so that `v5 ∈ [0xB8, 0xC0)`
    and the result lands in `[1, 8]`. -/
theorem rlp_phase3_long_string_spec_within
    (v5 v11Old v13 v14Old : Word) (base : Word) :
    cpsTripleWithin 3 base (base + 12)
      (CodeReq.ofProg base rlp_phase3_long_string_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ (0 : Word)) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
       (.x14 ↦ᵣ (v5 + signExtend12 (-(0xB7 : BitVec 12))))) := by
  -- Decompose the 3-instruction `ofProg` as singleton ∪ ofProg-of-tail.
  have hcr_eq : CodeReq.ofProg base rlp_phase3_long_string_prog =
      (CodeReq.singleton base (.ADDI .x14 .x5 (-0xB7))).union
      (CodeReq.ofProg (base + 4) [.ADDI .x11 .x0 0, .ADDI .x13 .x13 1]) := by
    simp only [rlp_phase3_long_string_prog, CodeReq.ofProg_cons]
  rw [hcr_eq]
  -- Sub-decompose the tail similarly: singleton ∪ singleton.
  have hcr_tail : CodeReq.ofProg (base + 4) [.ADDI .x11 .x0 0, .ADDI .x13 .x13 1] =
      (CodeReq.singleton (base + 4) (.ADDI .x11 .x0 0)).union
      (CodeReq.singleton ((base + 4) + 4) (.ADDI .x13 .x13 1)) :=
    CodeReq.ofProg_pair
  -- Step 1: ADDI x14, x5, -0xB7 at base.
  have s1Base := addi_spec_gen_within .x14 .x5 v14Old v5 (-0xB7) base (by nofun)
  have s1 : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.ADDI .x14 .x5 (-0xB7)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) **
       (.x14 ↦ᵣ (v5 + signExtend12 (-(0xB7 : BitVec 12))))) := by
    have framed := cpsTripleWithin_frameR
      ((.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      (by pcFree) s1Base
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      framed
  -- Step 2: ADDI x11, x0, 0 at base + 4.
  have s2Base := addi_spec_gen_within .x11 .x0 v11Old (0 : Word) 0 (base + 4) (by nofun)
  have hsig0 : (0 : Word) + signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  rw [hsig0] at s2Base
  have s2 : cpsTripleWithin 1 (base + 4) ((base + 4) + 4)
      (CodeReq.singleton (base + 4) (.ADDI .x11 .x0 0))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) **
       (.x14 ↦ᵣ (v5 + signExtend12 (-(0xB7 : BitVec 12)))))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ v13) **
       (.x14 ↦ᵣ (v5 + signExtend12 (-(0xB7 : BitVec 12))))) := by
    have framed := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ v5) ** (.x13 ↦ᵣ v13) **
       (.x14 ↦ᵣ (v5 + signExtend12 (-(0xB7 : BitVec 12)))))
      (by pcFree) s2Base
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      framed
  -- Step 3: ADDI x13, x13, 1 at (base + 4) + 4.
  have s3Base := addi_spec_gen_same_within .x13 v13 1 ((base + 4) + 4) (by nofun)
  have s3 : cpsTripleWithin 1 ((base + 4) + 4) (((base + 4) + 4) + 4)
      (CodeReq.singleton ((base + 4) + 4) (.ADDI .x13 .x13 1))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ v13) **
       (.x14 ↦ᵣ (v5 + signExtend12 (-(0xB7 : BitVec 12)))))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ (0 : Word)) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
       (.x14 ↦ᵣ (v5 + signExtend12 (-(0xB7 : BitVec 12))))) := by
    have framed := cpsTripleWithin_frameR
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ (0 : Word)) **
       (.x14 ↦ᵣ (v5 + signExtend12 (-(0xB7 : BitVec 12)))))
      (by pcFree) s3Base
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      framed
  -- Compose s2 ; s3 over the tail.
  have hd23 : CodeReq.Disjoint
      (CodeReq.singleton (base + 4) (.ADDI .x11 .x0 0))
      (CodeReq.singleton ((base + 4) + 4) (.ADDI .x13 .x13 1)) :=
    CodeReq.Disjoint.singleton (by bv_omega)
  have s23_raw := cpsTripleWithin_seq hd23 s2 s3
  -- Re-express the composed code as `ofProg (base + 4) tail` and adjust
  -- the exit PC from `((base + 4) + 4) + 4` to `base + 12`.
  have hexit : (((base + 4) + 4) + 4 : Word) = base + 12 := by bv_omega
  rw [← hcr_tail, hexit] at s23_raw
  -- Compose s1 ; s23.
  have hd1_23 : CodeReq.Disjoint
      (CodeReq.singleton base (.ADDI .x14 .x5 (-0xB7)))
      (CodeReq.ofProg (base + 4) [.ADDI .x11 .x0 0, .ADDI .x13 .x13 1]) := by
    apply CodeReq.Disjoint.ofProg_cons_right
    · exact CodeReq.Disjoint.singleton (by bv_omega)
    apply CodeReq.Disjoint.ofProg_cons_right
    · exact CodeReq.Disjoint.singleton (by bv_omega)
    exact CodeReq.Disjoint.ofProg_nil_right _ _
  exact cpsTripleWithin_seq hd1_23 s1 s23_raw

theorem rlp_phase3_long_string_spec_at_0xB8_within
    (v11Old v13 v14Old : Word) (base : Word) :
    cpsTripleWithin 3 base (base + 12)
      (CodeReq.ofProg base rlp_phase3_long_string_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xB8 : Word)) **
       (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xB8 : Word)) **
       (.x11 ↦ᵣ (0 : Word)) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
       (.x14 ↦ᵣ (1 : Word))) := by
  have h := rlp_phase3_long_string_spec_within (0xB8 : Word) v11Old v13 v14Old base
  have hsig : (0xB8 : Word) + signExtend12 (-(0xB7 : BitVec 12)) = (1 : Word) := by
    decide
  rw [hsig] at h
  exact h

theorem rlp_phase3_long_string_spec_at_0xB9_within
    (v11Old v13 v14Old : Word) (base : Word) :
    cpsTripleWithin 3 base (base + 12)
      (CodeReq.ofProg base rlp_phase3_long_string_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xB9 : Word)) **
       (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xB9 : Word)) **
       (.x11 ↦ᵣ (0 : Word)) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
       (.x14 ↦ᵣ (2 : Word))) := by
  have h := rlp_phase3_long_string_spec_within (0xB9 : Word) v11Old v13 v14Old base
  have hsig : (0xB9 : Word) + signExtend12 (-(0xB7 : BitVec 12)) = (2 : Word) := by
    decide
  rw [hsig] at h
  exact h

theorem rlp_phase3_long_string_spec_at_0xBA_within
    (v11Old v13 v14Old : Word) (base : Word) :
    cpsTripleWithin 3 base (base + 12)
      (CodeReq.ofProg base rlp_phase3_long_string_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xBA : Word)) **
       (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xBA : Word)) **
       (.x11 ↦ᵣ (0 : Word)) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
       (.x14 ↦ᵣ (3 : Word))) := by
  have h := rlp_phase3_long_string_spec_within (0xBA : Word) v11Old v13 v14Old base
  have hsig : (0xBA : Word) + signExtend12 (-(0xB7 : BitVec 12)) = (3 : Word) := by
    decide
  rw [hsig] at h
  exact h

theorem rlp_phase3_long_string_spec_at_0xBB_within
    (v11Old v13 v14Old : Word) (base : Word) :
    cpsTripleWithin 3 base (base + 12)
      (CodeReq.ofProg base rlp_phase3_long_string_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xBB : Word)) **
       (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xBB : Word)) **
       (.x11 ↦ᵣ (0 : Word)) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
       (.x14 ↦ᵣ (4 : Word))) := by
  have h := rlp_phase3_long_string_spec_within (0xBB : Word) v11Old v13 v14Old base
  have hsig : (0xBB : Word) + signExtend12 (-(0xB7 : BitVec 12)) = (4 : Word) := by
    decide
  rw [hsig] at h
  exact h

theorem rlp_phase3_long_string_spec_at_0xBC_within
    (v11Old v13 v14Old : Word) (base : Word) :
    cpsTripleWithin 3 base (base + 12)
      (CodeReq.ofProg base rlp_phase3_long_string_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xBC : Word)) **
       (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xBC : Word)) **
       (.x11 ↦ᵣ (0 : Word)) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
       (.x14 ↦ᵣ (5 : Word))) := by
  have h := rlp_phase3_long_string_spec_within (0xBC : Word) v11Old v13 v14Old base
  have hsig : (0xBC : Word) + signExtend12 (-(0xB7 : BitVec 12)) = (5 : Word) := by
    decide
  rw [hsig] at h
  exact h

theorem rlp_phase3_long_string_spec_at_0xBD_within
    (v11Old v13 v14Old : Word) (base : Word) :
    cpsTripleWithin 3 base (base + 12)
      (CodeReq.ofProg base rlp_phase3_long_string_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xBD : Word)) **
       (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xBD : Word)) **
       (.x11 ↦ᵣ (0 : Word)) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
       (.x14 ↦ᵣ (6 : Word))) := by
  have h := rlp_phase3_long_string_spec_within (0xBD : Word) v11Old v13 v14Old base
  have hsig : (0xBD : Word) + signExtend12 (-(0xB7 : BitVec 12)) = (6 : Word) := by
    decide
  rw [hsig] at h
  exact h

theorem rlp_phase3_long_string_spec_at_0xBE_within
    (v11Old v13 v14Old : Word) (base : Word) :
    cpsTripleWithin 3 base (base + 12)
      (CodeReq.ofProg base rlp_phase3_long_string_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xBE : Word)) **
       (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xBE : Word)) **
       (.x11 ↦ᵣ (0 : Word)) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
       (.x14 ↦ᵣ (7 : Word))) := by
  have h := rlp_phase3_long_string_spec_within (0xBE : Word) v11Old v13 v14Old base
  have hsig : (0xBE : Word) + signExtend12 (-(0xB7 : BitVec 12)) = (7 : Word) := by
    decide
  rw [hsig] at h
  exact h

theorem rlp_phase3_long_string_spec_at_0xBF_within
    (v11Old v13 v14Old : Word) (base : Word) :
    cpsTripleWithin 3 base (base + 12)
      (CodeReq.ofProg base rlp_phase3_long_string_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xBF : Word)) **
       (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xBF : Word)) **
       (.x11 ↦ᵣ (0 : Word)) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
       (.x14 ↦ᵣ (8 : Word))) := by
  have h := rlp_phase3_long_string_spec_within (0xBF : Word) v11Old v13 v14Old base
  have hsig : (0xBF : Word) + signExtend12 (-(0xB7 : BitVec 12)) = (8 : Word) := by
    decide
  rw [hsig] at h
  exact h

end EvmAsm.Rv64.RLP
