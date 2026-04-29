/-
  EvmAsm.Rv64.RLP.Phase3ShortString

  EL.3 Phase 3 (short-string exit): flat decode for the short byte-string
  category.

  When Phase 1's classifier reaches `e2` — i.e. the prefix byte
  `p ∈ [0x80, 0xB8)` — the RLP item is a *short byte string* whose payload
  occupies the next `(p − 0x80)` bytes after the prefix. The flat-decode
  output is therefore:

      length   = p − 0x80   (range [0, 55])
      data_ptr = input_ptr + 1   (skip past the prefix byte)

  Two instructions:

      ADDI x11, x5, -0x80     ; length = prefix - 0x80
      ADDI x13, x13, 1        ; data_ptr += 1

  Register usage:
    x5  — input: the RLP prefix byte (preserved)
    x11 — output: payload length
    x13 — input/output: byte pointer (advances by 1 to point at the
                         first payload byte)
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- Program definition
-- ============================================================================

/-- Two-instruction short-string flat-decode emitter:
    `ADDI x11, x5, -0x80 ; ADDI x13, x13, 1`. -/
def rlp_phase3_short_string_prog : Program :=
  [.ADDI .x11 .x5 (-0x80), .ADDI .x13 .x13 1]

example : rlp_phase3_short_string_prog.length = 2 := rfl

/-! ## Concrete sanity checks -/

-- Short byte string with prefix 0x85 (5-byte payload): length = 5.
example : ((0x85 : Word) + signExtend12 (-(0x80 : BitVec 12))) = (5 : Word) := by decide

-- Short byte string with prefix 0xB7 (55-byte payload): length = 55.
example : ((0xB7 : Word) + signExtend12 (-(0x80 : BitVec 12))) = (55 : Word) := by decide

-- Empty short byte string (prefix = 0x80): length = 0.
example : ((0x80 : Word) + signExtend12 (-(0x80 : BitVec 12))) = (0 : Word) := by decide

-- ============================================================================
-- Spec
-- ============================================================================

/-- `cpsTriple` spec for the short-string flat-decode. After two
    instructions, `x11` holds `prefix − 0x80` (the payload length) and
    `x13` has advanced by 1 to point at the first payload byte. `x5`
    is preserved.

    The spec places no range constraint on `v5`; if the caller reaches
    this program outside the short-string category the result is still
    well-defined (just not interpretable as a payload length). Downstream
    consumers typically compose this with a preceding Phase 1 exit post
    so that `v5 ∈ [0x80, 0xB8)` is available and the subtraction lands
    in `[0, 55]`. -/
theorem rlp_phase3_short_string_spec (v5 v11Old v13 : Word) (base : Word) :
    cpsTriple base (base + 8)
      (CodeReq.ofProg base rlp_phase3_short_string_prog)
      ((.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ (v5 + signExtend12 (-(0x80 : BitVec 12)))) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12)))) := by
  -- Reshape the two-instruction `ofProg` into a singleton-union pair.
  rw [show CodeReq.ofProg base rlp_phase3_short_string_prog =
      (CodeReq.singleton base (.ADDI .x11 .x5 (-0x80))).union
      (CodeReq.singleton (base + 4) (.ADDI .x13 .x13 1)) from CodeReq.ofProg_pair]
  -- Disjointness of the two singletons (distinct PCs).
  have hd : CodeReq.Disjoint
      (CodeReq.singleton base (.ADDI .x11 .x5 (-0x80)))
      (CodeReq.singleton (base + 4) (.ADDI .x13 .x13 1)) :=
    CodeReq.Disjoint.singleton (by bv_omega)
  -- Step 1: ADDI x11, x5, -0x80 at base. Frame with `x13`.
  have s1Base := addi_spec_gen .x11 .x5 v11Old v5 (-0x80) base (by nofun)
  have s1 : cpsTriple base (base + 4)
      (CodeReq.singleton base (.ADDI .x11 .x5 (-0x80)))
      ((.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ (v5 + signExtend12 (-(0x80 : BitVec 12)))) **
       (.x13 ↦ᵣ v13)) := by
    have framed := cpsTriple_frameR (.x13 ↦ᵣ v13) (by pcFree) s1Base
    exact cpsTriple_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      framed
  -- Step 2: ADDI x13, x13, 1 at base + 4. Frame with `x5` and `x11`.
  have s2Base := addi_spec_gen_same .x13 v13 1 (base + 4) (by nofun)
  have s2 : cpsTriple (base + 4) (base + 8)
      (CodeReq.singleton (base + 4) (.ADDI .x13 .x13 1))
      ((.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ (v5 + signExtend12 (-(0x80 : BitVec 12)))) **
       (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ (v5 + signExtend12 (-(0x80 : BitVec 12)))) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12)))) := by
    have framed := cpsTriple_frameR
      ((.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ (v5 + signExtend12 (-(0x80 : BitVec 12)))))
      (by pcFree) s2Base
    rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at framed
    exact cpsTriple_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      framed
  exact cpsTriple_seq hd s1 s2

/-! ## Concrete specializations for individual short-string prefixes -/

/-- Specialization at `v5 = 0x80` (empty short-string prefix, length = 0). -/
theorem rlp_phase3_short_string_spec_at_0x80
    (v11Old v13 : Word) (base : Word) :
    cpsTriple base (base + 8)
      (CodeReq.ofProg base rlp_phase3_short_string_prog)
      ((.x5 ↦ᵣ (0x80 : Word)) ** (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ (0x80 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12)))) := by
  have h := rlp_phase3_short_string_spec (0x80 : Word) v11Old v13 base
  have hsig : (0x80 : Word) + signExtend12 (-(0x80 : BitVec 12)) = (0 : Word) := by
    decide
  rw [hsig] at h
  exact h

/-- Specialization at `v5 = 0x81` (length = 1). Note that under the
    canonical-form rules a single payload byte `≥ 0x80` requires this
    prefix; the caller is responsible for the data semantics. -/
theorem rlp_phase3_short_string_spec_at_0x81
    (v11Old v13 : Word) (base : Word) :
    cpsTriple base (base + 8)
      (CodeReq.ofProg base rlp_phase3_short_string_prog)
      ((.x5 ↦ᵣ (0x81 : Word)) ** (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ (0x81 : Word)) ** (.x11 ↦ᵣ (1 : Word)) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12)))) := by
  have h := rlp_phase3_short_string_spec (0x81 : Word) v11Old v13 base
  have hsig : (0x81 : Word) + signExtend12 (-(0x80 : BitVec 12)) = (1 : Word) := by
    decide
  rw [hsig] at h
  exact h

/-- Specialization at `v5 = 0x82` (length = 2). -/
theorem rlp_phase3_short_string_spec_at_0x82
    (v11Old v13 : Word) (base : Word) :
    cpsTriple base (base + 8)
      (CodeReq.ofProg base rlp_phase3_short_string_prog)
      ((.x5 ↦ᵣ (0x82 : Word)) ** (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ (0x82 : Word)) ** (.x11 ↦ᵣ (2 : Word)) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12)))) := by
  have h := rlp_phase3_short_string_spec (0x82 : Word) v11Old v13 base
  have hsig : (0x82 : Word) + signExtend12 (-(0x80 : BitVec 12)) = (2 : Word) := by
    decide
  rw [hsig] at h
  exact h

/-- Specialization at `v5 = 0x83` (length = 3). -/
theorem rlp_phase3_short_string_spec_at_0x83
    (v11Old v13 : Word) (base : Word) :
    cpsTriple base (base + 8)
      (CodeReq.ofProg base rlp_phase3_short_string_prog)
      ((.x5 ↦ᵣ (0x83 : Word)) ** (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ (0x83 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12)))) := by
  have h := rlp_phase3_short_string_spec (0x83 : Word) v11Old v13 base
  have hsig : (0x83 : Word) + signExtend12 (-(0x80 : BitVec 12)) = (3 : Word) := by
    decide
  rw [hsig] at h
  exact h

/-- Specialization at `v5 = 0xB7` (maximum short-string length = 55). -/
theorem rlp_phase3_short_string_spec_at_0xB7
    (v11Old v13 : Word) (base : Word) :
    cpsTriple base (base + 8)
      (CodeReq.ofProg base rlp_phase3_short_string_prog)
      ((.x5 ↦ᵣ (0xB7 : Word)) ** (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ (0xB7 : Word)) ** (.x11 ↦ᵣ (55 : Word)) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12)))) := by
  have h := rlp_phase3_short_string_spec (0xB7 : Word) v11Old v13 base
  have hsig : (0xB7 : Word) + signExtend12 (-(0x80 : BitVec 12)) = (55 : Word) := by
    decide
  rw [hsig] at h
  exact h

end EvmAsm.Rv64.RLP
