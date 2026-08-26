/-
  EvmAsm.Evm64.Exp.SquaringCall

  Prep for `exp_squaring_call_block_spec_within` (#92 slice 4-squaring-call,
  beads evm-asm-eh4jq → evm-asm-nrfpf). Decomposes the 26-instruction
  `exp_squaring_call_block mulOff` into a `CodeReq.unionAll` of its four
  sub-block `ofProg` codes:

      exp_squaring_call_block_code base mulOff :=
        CodeReq.unionAll [
          CodeReq.ofProg base                  exp_loop_marshal_factor1,           -- offset 0   (8 instr)
          CodeReq.ofProg (base + 32) exp_loop_marshal_result_to_factor2,           -- offset 32  (8 instr)
          CodeReq.ofProg (base + 64) (exp_square_block mulOff),                    -- offset 64  (1 instr)
          CodeReq.ofProg (base + 68) exp_loop_un_marshal_and_restore               -- offset 68  (9 instr)
        ]

  Provides:
    * `exp_squaring_call_block_code_eq_ofProg`: equality with the canonical
      `CodeReq.ofProg base (exp_squaring_call_block mulOff)` form.
    * Four leaf subsumption lemmas (`_marshal_factor1_sub`,
      `_marshal_result_to_factor2_sub`, `_square_sub`,
      `_un_marshal_and_restore_sub`) ready for use by the spec slice
      (evm-asm-nrfpf).

  Mirrors `expOneIterCode` in `Compose/Base.lean` (4-block unionAll +
  per-block `_sub` lemmas) and `evm_div_callable_code_eq_ofProg` in
  `DivMod/Callable.lean` (long `ofProg_append` chain with offset
  normalization). Authored by @pirapira; implemented by Hermes-bot.
-/

module

public import EvmAsm.Evm64.Exp.MarshalPair
public import EvmAsm.Evm64.Exp.AddrNorm
public import EvmAsm.Evm64.Stack
public import EvmAsm.Evm64.Exp.LimbSpec

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64 (CodeReq Program seq)

/-- 4-block `unionAll` decomposition of `exp_squaring_call_block mulOff`. The
    four sub-blocks live at offsets 0 / 32 / 64 / 68 from `base` and total
    104 bytes. Used by the slice-4 squaring-call spec (`evm-asm-nrfpf`) and
    its conditional-multiply sibling. -/
abbrev exp_squaring_call_block_code (base : Word) (mulOff : BitVec 21) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base                exp_loop_marshal_factor1,
    CodeReq.ofProg (base + 32)         exp_loop_marshal_result_to_factor2,
    CodeReq.ofProg (base + 64)         (exp_square_block mulOff),
    CodeReq.ofProg (base + 68)         exp_loop_un_marshal_and_restore
  ]

/-- The 4-block decomposition is exactly the canonical `ofProg` of
    `exp_squaring_call_block`. Mirrors `evm_div_callable_code_eq_ofProg`
    (DivMod/Callable.lean): iterate `CodeReq.ofProg_append` 3 times and
    normalize each running base offset against the per-block lengths. -/
theorem exp_squaring_call_block_code_eq_ofProg (base : Word) (mulOff : BitVec 21) :
    exp_squaring_call_block_code base mulOff =
      CodeReq.ofProg base (exp_squaring_call_block mulOff) := by
  unfold exp_squaring_call_block_code exp_squaring_call_block
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil,
    CodeReq.union_empty_right]
  unfold seq
  unfold Program
  symm
  -- factor1 (8 instr = 32 bytes) → marshal_result_to_factor2 (8 instr) → square (1 instr) → un_marshal
  rw [CodeReq.ofProg_append]
  rw [show base + BitVec.ofNat 64 (4 * exp_loop_marshal_factor1.length) =
        base + 32 by rw [exp_loop_marshal_factor1_length]; rfl]
  rw [CodeReq.ofProg_append]
  rw [show (base + 32) +
        BitVec.ofNat 64 (4 * exp_loop_marshal_result_to_factor2.length) =
        base + 64 by
    rw [exp_loop_marshal_result_to_factor2_length]
    exact EvmAsm.Evm64.Exp.AddrNorm.expCallBlock_factor2_end_addr base]
  rw [CodeReq.ofProg_append]
  rw [show (base + 64) + BitVec.ofNat 64 (4 * (exp_square_block mulOff).length) =
        base + 68 by
    rw [exp_square_block_length]
    exact EvmAsm.Evm64.Exp.AddrNorm.expCallBlock_square_end_addr base]

/-- factor1 sub-block ⊆ exp_squaring_call_block_code. -/
theorem exp_squaring_call_block_code_marshal_factor1_sub
    (base : Word) (mulOff : BitVec 21) :
    ∀ a i, (CodeReq.ofProg base exp_loop_marshal_factor1) a = some i →
      (exp_squaring_call_block_code base mulOff) a = some i := by
  unfold exp_squaring_call_block_code
  simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left

/-- marshal-result-to-factor2 sub-block ⊆ exp_squaring_call_block_code. -/
theorem exp_squaring_call_block_code_marshal_result_to_factor2_sub
    (base : Word) (mulOff : BitVec 21) :
    ∀ a i, (CodeReq.ofProg (base + 32)
      exp_loop_marshal_result_to_factor2) a = some i →
      (exp_squaring_call_block_code base mulOff) a = some i := by
  unfold exp_squaring_call_block_code
  simp only [CodeReq.unionAll_cons]
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_loop_marshal_factor1_length,
        exp_loop_marshal_result_to_factor2_length] at hk1 hk2
      exact EvmAsm.Evm64.Exp.AddrNorm.expCallBlock_factor1_factor2_disjoint_addr
        base hk1 hk2))
  exact CodeReq.union_mono_left

/-- square sub-block ⊆ exp_squaring_call_block_code. -/
theorem exp_squaring_call_block_code_square_sub
    (base : Word) (mulOff : BitVec 21) :
    ∀ a i, (CodeReq.ofProg (base + 64) (exp_square_block mulOff)) a = some i →
      (exp_squaring_call_block_code base mulOff) a = some i := by
  unfold exp_squaring_call_block_code
  simp only [CodeReq.unionAll_cons]
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_loop_marshal_factor1_length,
        exp_square_block_length] at hk1 hk2
      exact EvmAsm.Evm64.Exp.AddrNorm.expCallBlock_factor1_square_disjoint_addr
        base hk1 hk2))
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_loop_marshal_result_to_factor2_length,
        exp_square_block_length] at hk1 hk2
      exact EvmAsm.Evm64.Exp.AddrNorm.expCallBlock_factor2_square_disjoint_addr
        base hk1 hk2))
  exact CodeReq.union_mono_left

/-- un_marshal_and_restore sub-block ⊆ exp_squaring_call_block_code. -/
theorem exp_squaring_call_block_code_un_marshal_and_restore_sub
    (base : Word) (mulOff : BitVec 21) :
    ∀ a i, (CodeReq.ofProg (base + 68) exp_loop_un_marshal_and_restore) a = some i →
      (exp_squaring_call_block_code base mulOff) a = some i := by
  unfold exp_squaring_call_block_code
  simp only [CodeReq.unionAll_cons]
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_loop_marshal_factor1_length,
        exp_loop_un_marshal_and_restore_length] at hk1 hk2
      exact EvmAsm.Evm64.Exp.AddrNorm.expCallBlock_factor1_restore_disjoint_addr
        base hk1 hk2))
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_loop_marshal_result_to_factor2_length,
        exp_loop_un_marshal_and_restore_length] at hk1 hk2
      exact EvmAsm.Evm64.Exp.AddrNorm.expCallBlock_factor2_restore_disjoint_addr
        base hk1 hk2))
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_square_block_length,
        exp_loop_un_marshal_and_restore_length] at hk1 hk2
      exact EvmAsm.Evm64.Exp.AddrNorm.expCallBlock_square_restore_disjoint_addr
        base hk1 hk2))
  exact CodeReq.union_mono_left

/-- Bundled per-sub-block subsumption witnesses for
    `exp_squaring_call_block_code`, packaged for downstream `extend_code`
    composition (mirrors `expOneIterCode_block_subs`). -/
theorem exp_squaring_call_block_code_block_subs
    (base : Word) (mulOff : BitVec 21) :
    (∀ a i, (CodeReq.ofProg base exp_loop_marshal_factor1) a = some i →
      (exp_squaring_call_block_code base mulOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 32)
      exp_loop_marshal_result_to_factor2) a = some i →
      (exp_squaring_call_block_code base mulOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 64) (exp_square_block mulOff)) a = some i →
      (exp_squaring_call_block_code base mulOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 68) exp_loop_un_marshal_and_restore) a = some i →
      (exp_squaring_call_block_code base mulOff) a = some i) := by
  exact ⟨exp_squaring_call_block_code_marshal_factor1_sub base mulOff,
    exp_squaring_call_block_code_marshal_result_to_factor2_sub base mulOff,
    exp_squaring_call_block_code_square_sub base mulOff,
    exp_squaring_call_block_code_un_marshal_and_restore_sub base mulOff⟩

end EvmAsm.Evm64
