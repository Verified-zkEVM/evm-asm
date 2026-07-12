/-
  EvmAsm.Evm64.AddMod.Compose.CondSubSpec

  Machine-level `cpsTripleWithin` specs for `evm_addmod_carry_cond_sub` —
  the branch-free conditional subtract closing the carry-path pre-reduced
  modular add of `evm_addmod_total` (issue #9704, Phase 3).

  On entry `x12 = G = sp + 64`, the truncated sum `s` sits at `G + 0..24`,
  `N` is parked at `G − 224..−200` (offsets 3872..3896, the S1 cells), and
  the `evm_add` carry-out bit is in `x5`. The block computes

    pass 1 : the borrow-out `B` of `s − N`   (22 instr; `B = 1 ↔ s < N`)
    take   : `mask = 0 − (carry ∨ ¬B)`       (3 instr)
    pass 2 : `s := s − (N &&& mask)`         (30 instr, in place)

  Split into three sub-specs (pass 2 takes `mask` as a parameter) so the
  raw-expression instantiation sites stay shallow; the full-block spec
  composes them and exposes every per-limb value through `let` bindings.
  The value-level `EvmWord.modAdd` bridge is the next milestone's job.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Evm64.AddMod.Program

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64
open EvmAsm.Evm64

-- ============================================================================
-- Pass 1 — borrow-out of s − N (22 instructions)
-- ============================================================================

/-- Pass-1 head chunk: park the `evm_add` carry-out (`x10 := x5 + 0`) and
    compute the limb-0 borrow `s0 < n0`. -/
theorem evm_addmod_cond_sub_pass1_head_spec_within
    (base carry x6Old x7Old x10Old x11Old sp s0 n0 : Word) :
    cpsTripleWithin 4 base (base + 16)
      (CodeReq.union (CodeReq.singleton base (.ADDI .x10 .x5 (0 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 (0 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x7 .x12 (3872 : BitVec 12)))
       (CodeReq.singleton (base + 12) (.SLTU .x11 .x6 .x7)))))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ carry) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ carry) ** (.x6 ↦ᵣ s0) ** (.x7 ↦ᵣ n0) **
       (.x10 ↦ᵣ (carry + signExtend12 (0 : BitVec 12))) **
       (.x11 ↦ᵣ (if BitVec.ult s0 n0 then (1 : Word) else 0)) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0)) := by
  have P := addi_spec_gen_within .x10 .x5 x10Old carry 0 base (by nofun)
  have L0 := ld_spec_gen_within .x6 .x12 sp x6Old s0 0 (base + 4) (by nofun)
  have L1 := ld_spec_gen_within .x7 .x12 sp x7Old n0 3872 (base + 8) (by nofun)
  have C := sltu_spec_gen_within .x11 .x6 .x7 x11Old s0 n0 (base + 12) (by nofun)
  runBlock P L0 L1 C

/-- Pass-1 limb chunk (limbs 1–3, offset-generic): fold one limb of the
    `s − N` borrow chain. `borrowIn` is a parameter so instantiation keeps
    expression depth shallow. Uses the verified `evm_sub` idiom — the
    incoming-borrow test runs before the borrow subtraction. -/
theorem evm_addmod_cond_sub_pass1_limb_spec_within (offS offN : BitVec 12)
    (base sp x5Old x6Old x7Old s n borrowIn : Word) :
    cpsTripleWithin 6 base (base + 24)
      (CodeReq.union (CodeReq.singleton base (.LD .x6 .x12 offS))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x7 .x12 offN))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SLTU .x7 .x6 .x11))
       (CodeReq.singleton (base + 20) (.OR .x11 .x5 .x7)))))))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       (.x11 ↦ᵣ borrowIn) **
       ((sp + signExtend12 offS) ↦ₘ s) **
       ((sp + signExtend12 offN) ↦ₘ n))
      ((.x12 ↦ᵣ sp) **
       (.x5 ↦ᵣ (if BitVec.ult s n then (1 : Word) else 0)) **
       (.x6 ↦ᵣ (s - n)) **
       (.x7 ↦ᵣ (if BitVec.ult (s - n) borrowIn then (1 : Word) else 0)) **
       (.x11 ↦ᵣ ((if BitVec.ult s n then (1 : Word) else 0) |||
          (if BitVec.ult (s - n) borrowIn then (1 : Word) else 0))) **
       ((sp + signExtend12 offS) ↦ₘ s) **
       ((sp + signExtend12 offN) ↦ₘ n)) := by
  have L0 := ld_spec_gen_within .x6 .x12 sp x6Old s offS base (by nofun)
  have L1 := ld_spec_gen_within .x7 .x12 sp x7Old n offN (base + 4) (by nofun)
  have C1 := sltu_spec_gen_within .x5 .x6 .x7 x5Old s n (base + 8) (by nofun)
  have D := sub_spec_gen_rd_eq_rs1_within .x6 .x7 s n (base + 12) (by nofun)
  have C2 := sltu_spec_gen_within .x7 .x6 .x11 n (s - n) borrowIn
    (base + 16) (by nofun)
  have O := or_spec_gen_within .x11 .x5 .x7 borrowIn
    (if BitVec.ult s n then (1 : Word) else 0)
    (if BitVec.ult (s - n) borrowIn then (1 : Word) else 0)
    (base + 20) (by nofun)
  runBlock L0 L1 C1 D C2 O

-- ============================================================================
-- Take/mask chunk (3 instructions)
-- ============================================================================

/-- Take chunk: `mask = 0 − (carryParked ||| (borrow ^^^ 1))` — all-ones
    when the subtract must fire (`carry = 1` or `s ≥ N`), zero otherwise. -/
theorem evm_addmod_cond_sub_take_spec_within
    (base cIn b3In : Word) :
    cpsTripleWithin 3 base (base + 12)
      (CodeReq.union (CodeReq.singleton base (.XORI .x11 .x11 (1 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 4) (.OR .x11 .x10 .x11))
       (CodeReq.singleton (base + 8) (.SUB .x11 .x0 .x11))))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ cIn) ** (.x11 ↦ᵣ b3In))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ cIn) **
       (.x11 ↦ᵣ ((0 : Word) -
          (cIn ||| (b3In ^^^ signExtend12 (1 : BitVec 12)))))) := by
  have X := xori_spec_gen_same_within .x11 b3In 1 base (by nofun)
  have O := or_spec_gen_rd_eq_rs2_within .x11 .x10 cIn
    (b3In ^^^ signExtend12 (1 : BitVec 12)) (base + 4) (by nofun)
  have S := sub_spec_gen_rd_eq_rs2_within .x11 .x0 (0 : Word)
    (cIn ||| (b3In ^^^ signExtend12 (1 : BitVec 12))) (base + 8) (by nofun)
  runBlock X O S

-- ============================================================================
-- Pass 2 — s := s − (N &&& mask) (30 instructions, mask as parameter)
-- ============================================================================

/-- Pass-2 limb-0 chunk: mask the low modulus limb and subtract it, seeding
    the borrow chain in `x10`. -/
theorem evm_addmod_cond_sub_pass2_low_spec_within
    (base sp x5Old x6Old x7Old x10Old maskIn s0 n0 : Word) :
    cpsTripleWithin 6 base (base + 24)
      (CodeReq.union (CodeReq.singleton base (.LD .x6 .x12 (0 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x7 .x12 (3872 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 8) (.AND .x7 .x7 .x11))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x10 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x5 .x6 .x7))
       (CodeReq.singleton (base + 20) (.SD .x12 .x5 (0 : BitVec 12))))))))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ maskIn) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (s0 - (n0 &&& maskIn))) ** (.x6 ↦ᵣ s0) **
       (.x7 ↦ᵣ (n0 &&& maskIn)) **
       (.x10 ↦ᵣ (if BitVec.ult s0 (n0 &&& maskIn) then (1 : Word) else 0)) **
       (.x11 ↦ᵣ maskIn) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ (s0 - (n0 &&& maskIn))) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0)) := by
  have L0 := ld_spec_gen_within .x6 .x12 sp x6Old s0 0 base (by nofun)
  have L1 := ld_spec_gen_within .x7 .x12 sp x7Old n0 3872 (base + 4) (by nofun)
  have A := and_spec_gen_rd_eq_rs1_within .x7 .x11 n0 maskIn (base + 8) (by nofun)
  have C := sltu_spec_gen_within .x10 .x6 .x7 x10Old s0 (n0 &&& maskIn)
    (base + 12) (by nofun)
  have D := sub_spec_gen_within .x5 .x6 .x7 s0 (n0 &&& maskIn) x5Old
    (base + 16) (by nofun)
  have S := sd_spec_gen_within .x12 .x5 sp (s0 - (n0 &&& maskIn)) s0 0
    (base + 20)
  runBlock L0 L1 A C D S

/-- Pass-2 limb chunk (limbs 1–2, offset-generic): mask the modulus limb,
    subtract it and the incoming borrow (verified `evm_sub` idiom), store,
    and propagate the borrow. `maskIn`/`borrowIn` are parameters. -/
theorem evm_addmod_cond_sub_pass2_limb_spec_within (offS offN : BitVec 12)
    (base sp x5Old x6Old x7Old maskIn borrowIn s n : Word) :
    cpsTripleWithin 9 base (base + 36)
      (CodeReq.union (CodeReq.singleton base (.LD .x6 .x12 offS))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x7 .x12 offN))
      (CodeReq.union (CodeReq.singleton (base + 8) (.AND .x7 .x7 .x11))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 20) (.SLTU .x7 .x6 .x10))
      (CodeReq.union (CodeReq.singleton (base + 24) (.SUB .x6 .x6 .x10))
      (CodeReq.union (CodeReq.singleton (base + 28) (.OR .x10 .x5 .x7))
       (CodeReq.singleton (base + 32) (.SD .x12 .x6 offS))))))))))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       (.x10 ↦ᵣ borrowIn) ** (.x11 ↦ᵣ maskIn) **
       ((sp + signExtend12 offS) ↦ₘ s) **
       ((sp + signExtend12 offN) ↦ₘ n))
      ((.x12 ↦ᵣ sp) **
       (.x5 ↦ᵣ (if BitVec.ult s (n &&& maskIn) then (1 : Word) else 0)) **
       (.x6 ↦ᵣ ((s - (n &&& maskIn)) - borrowIn)) **
       (.x7 ↦ᵣ (if BitVec.ult (s - (n &&& maskIn)) borrowIn
          then (1 : Word) else 0)) **
       (.x10 ↦ᵣ ((if BitVec.ult s (n &&& maskIn) then (1 : Word) else 0) |||
          (if BitVec.ult (s - (n &&& maskIn)) borrowIn
            then (1 : Word) else 0))) **
       (.x11 ↦ᵣ maskIn) **
       ((sp + signExtend12 offS) ↦ₘ ((s - (n &&& maskIn)) - borrowIn)) **
       ((sp + signExtend12 offN) ↦ₘ n)) := by
  have L0 := ld_spec_gen_within .x6 .x12 sp x6Old s offS base (by nofun)
  have L1 := ld_spec_gen_within .x7 .x12 sp x7Old n offN (base + 4) (by nofun)
  have A := and_spec_gen_rd_eq_rs1_within .x7 .x11 n maskIn (base + 8) (by nofun)
  have C1 := sltu_spec_gen_within .x5 .x6 .x7 x5Old s (n &&& maskIn)
    (base + 12) (by nofun)
  have D1 := sub_spec_gen_rd_eq_rs1_within .x6 .x7 s (n &&& maskIn)
    (base + 16) (by nofun)
  have C2 := sltu_spec_gen_within .x7 .x6 .x10 (n &&& maskIn)
    (s - (n &&& maskIn)) borrowIn (base + 20) (by nofun)
  have D2 := sub_spec_gen_rd_eq_rs1_within .x6 .x10 (s - (n &&& maskIn))
    borrowIn (base + 24) (by nofun)
  have O := or_spec_gen_within .x10 .x5 .x7 borrowIn
    (if BitVec.ult s (n &&& maskIn) then (1 : Word) else 0)
    (if BitVec.ult (s - (n &&& maskIn)) borrowIn then (1 : Word) else 0)
    (base + 28) (by nofun)
  have S := sd_spec_gen_within .x12 .x6 sp
    ((s - (n &&& maskIn)) - borrowIn) s offS (base + 32)
  runBlock L0 L1 A C1 D1 C2 D2 O S

/-- Pass-2 high-limb chunk: mask, double subtract (no borrow-out), store. -/
theorem evm_addmod_cond_sub_pass2_high_spec_within
    (base sp x5Old x6Old x7Old maskIn borrowIn s3 n3 : Word) :
    cpsTripleWithin 6 base (base + 24)
      (CodeReq.union (CodeReq.singleton base (.LD .x6 .x12 (24 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x7 .x12 (3896 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 8) (.AND .x7 .x7 .x11))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x6 .x6 .x10))
       (CodeReq.singleton (base + 20) (.SD .x12 .x6 (24 : BitVec 12))))))))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       (.x10 ↦ᵣ borrowIn) ** (.x11 ↦ᵣ maskIn) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) **
       (.x6 ↦ᵣ ((s3 - (n3 &&& maskIn)) - borrowIn)) **
       (.x7 ↦ᵣ (n3 &&& maskIn)) **
       (.x10 ↦ᵣ borrowIn) ** (.x11 ↦ᵣ maskIn) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ
          ((s3 - (n3 &&& maskIn)) - borrowIn)) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ n3)) := by
  have L0 := ld_spec_gen_within .x6 .x12 sp x6Old s3 24 base (by nofun)
  have L1 := ld_spec_gen_within .x7 .x12 sp x7Old n3 3896 (base + 4) (by nofun)
  have A := and_spec_gen_rd_eq_rs1_within .x7 .x11 n3 maskIn (base + 8) (by nofun)
  have D1 := sub_spec_gen_rd_eq_rs1_within .x6 .x7 s3 (n3 &&& maskIn)
    (base + 12) (by nofun)
  have D2 := sub_spec_gen_rd_eq_rs1_within .x6 .x10 (s3 - (n3 &&& maskIn))
    borrowIn (base + 16) (by nofun)
  have S := sd_spec_gen_within .x12 .x6 sp
    ((s3 - (n3 &&& maskIn)) - borrowIn) s3 24 (base + 20)
  runBlock L0 L1 A D1 D2 S

-- ============================================================================
-- Compositions: pass-1 / pass-2 halves and full passes
-- ============================================================================

/-- Pass-1 front half: head + limb 1 (10 instructions). -/
theorem evm_addmod_cond_sub_pass1_front_spec_within
    (base sp carry x6Old x7Old x10Old x11Old : Word)
    (s0 s1 n0 n1 : Word) :
    cpsTripleWithin 10 base (base + 40)
      (CodeReq.union (CodeReq.singleton base (.ADDI .x10 .x5 (0 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 (0 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x7 .x12 (3872 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x11 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 16) (.LD .x6 .x12 (8 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x7 .x12 (3880 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 24) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 32) (.SLTU .x7 .x6 .x11))
       (CodeReq.singleton (base + 36) (.OR .x11 .x5 .x7)))))))))))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ carry) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ n1))
      ((.x12 ↦ᵣ sp) **
       (.x5 ↦ᵣ (if BitVec.ult s1 n1 then (1 : Word) else 0)) **
       (.x6 ↦ᵣ (s1 - n1)) **
       (.x7 ↦ᵣ (if BitVec.ult (s1 - n1)
          (if BitVec.ult s0 n0 then (1 : Word) else 0) then (1 : Word) else 0)) **
       (.x10 ↦ᵣ (carry + signExtend12 (0 : BitVec 12))) **
       (.x11 ↦ᵣ ((if BitVec.ult s1 n1 then (1 : Word) else 0) |||
          (if BitVec.ult (s1 - n1)
            (if BitVec.ult s0 n0 then (1 : Word) else 0)
            then (1 : Word) else 0))) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ n1)) := by
  have H := evm_addmod_cond_sub_pass1_head_spec_within base carry
    x6Old x7Old x10Old x11Old sp s0 n0
  have L1 := evm_addmod_cond_sub_pass1_limb_spec_within 8 3880 (base + 16) sp
    carry s0 n0 s1 n1
    (if BitVec.ult s0 n0 then (1 : Word) else 0)
  runBlock H L1

/-- Pass-1 back half: limbs 2 + 3 (12 instructions), incoming values as
    parameters. -/
theorem evm_addmod_cond_sub_pass1_back_spec_within
    (base sp x5In x6In x7In x10In borrowIn : Word)
    (s2 s3 n2 n3 : Word) :
    cpsTripleWithin 12 base (base + 48)
      (CodeReq.union (CodeReq.singleton base (.LD .x6 .x12 (16 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x7 .x12 (3888 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SLTU .x7 .x6 .x11))
      (CodeReq.union (CodeReq.singleton (base + 20) (.OR .x11 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x6 .x12 (24 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x7 .x12 (3896 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 32) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 40) (.SLTU .x7 .x6 .x11))
       (CodeReq.singleton (base + 44) (.OR .x11 .x5 .x7)))))))))))))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5In) ** (.x6 ↦ᵣ x6In) ** (.x7 ↦ᵣ x7In) **
       (.x10 ↦ᵣ x10In) ** (.x11 ↦ᵣ borrowIn) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ sp) **
       (.x5 ↦ᵣ (if BitVec.ult s3 n3 then (1 : Word) else 0)) **
       (.x6 ↦ᵣ (s3 - n3)) **
       (.x7 ↦ᵣ (if BitVec.ult (s3 - n3)
          ((if BitVec.ult s2 n2 then (1 : Word) else 0) |||
           (if BitVec.ult (s2 - n2) borrowIn then (1 : Word) else 0))
          then (1 : Word) else 0)) **
       (.x10 ↦ᵣ x10In) **
       (.x11 ↦ᵣ ((if BitVec.ult s3 n3 then (1 : Word) else 0) |||
          (if BitVec.ult (s3 - n3)
            ((if BitVec.ult s2 n2 then (1 : Word) else 0) |||
             (if BitVec.ult (s2 - n2) borrowIn then (1 : Word) else 0))
            then (1 : Word) else 0))) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ n3)) := by
  have L2 := evm_addmod_cond_sub_pass1_limb_spec_within 16 3888 base sp
    x5In x6In x7In s2 n2 borrowIn
  have L3 := evm_addmod_cond_sub_pass1_limb_spec_within 24 3896 (base + 24) sp
    (if BitVec.ult s2 n2 then (1 : Word) else 0)
    (s2 - n2)
    (if BitVec.ult (s2 - n2) borrowIn then (1 : Word) else 0)
    s3 n3
    ((if BitVec.ult s2 n2 then (1 : Word) else 0) |||
     (if BitVec.ult (s2 - n2) borrowIn then (1 : Word) else 0))
  runBlock L2 L3


/-- Pass-1 full spec via the two halves. -/
theorem evm_addmod_cond_sub_pass1_spec_within
    (base sp carry x6Old x7Old x10Old x11Old : Word)
    (s0 s1 s2 s3 n0 n1 n2 n3 : Word) :
    let b0 := if BitVec.ult s0 n0 then (1 : Word) else 0
    let t1 := if BitVec.ult s1 n1 then (1 : Word) else 0
    let d1 := s1 - n1
    let u1 := if BitVec.ult d1 b0 then (1 : Word) else 0
    let b1 := t1 ||| u1
    let t2 := if BitVec.ult s2 n2 then (1 : Word) else 0
    let d2 := s2 - n2
    let u2 := if BitVec.ult d2 b1 then (1 : Word) else 0
    let b2 := t2 ||| u2
    let t3 := if BitVec.ult s3 n3 then (1 : Word) else 0
    let d3 := s3 - n3
    let u3 := if BitVec.ult d3 b2 then (1 : Word) else 0
    let b3 := t3 ||| u3
    cpsTripleWithin 22 base (base + 88)
      (CodeReq.union (CodeReq.singleton base (.ADDI .x10 .x5 (0 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 (0 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x7 .x12 (3872 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x11 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 16) (.LD .x6 .x12 (8 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x7 .x12 (3880 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 24) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 32) (.SLTU .x7 .x6 .x11))
      (CodeReq.union (CodeReq.singleton (base + 36) (.OR .x11 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 40) (.LD .x6 .x12 (16 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 44) (.LD .x7 .x12 (3888 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 48) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 52) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 56) (.SLTU .x7 .x6 .x11))
      (CodeReq.union (CodeReq.singleton (base + 60) (.OR .x11 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 64) (.LD .x6 .x12 (24 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 68) (.LD .x7 .x12 (3896 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 72) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 76) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 80) (.SLTU .x7 .x6 .x11))
       (CodeReq.singleton (base + 84) (.OR .x11 .x5 .x7)))))))))))))))))))))))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ carry) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ t3) ** (.x6 ↦ᵣ d3) ** (.x7 ↦ᵣ u3) **
       (.x10 ↦ᵣ (carry + signExtend12 (0 : BitVec 12))) ** (.x11 ↦ᵣ b3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ n3)) := by
  intro b0 t1 d1 u1 b1 t2 d2 u2 b2 t3 d3 u3 b3
  simp only [b0, t1, d1, u1, b1, t2, d2, u2, b2, t3, d3, u3, b3]
  have F := evm_addmod_cond_sub_pass1_front_spec_within base sp carry x6Old x7Old x10Old x11Old
    s0 s1 n0 n1
  have B := evm_addmod_cond_sub_pass1_back_spec_within (base + 40) sp
    (if BitVec.ult s1 n1 then (1 : Word) else 0)
    (s1 - n1)
    (if BitVec.ult (s1 - n1)
      (if BitVec.ult s0 n0 then (1 : Word) else 0) then (1 : Word) else 0)
    (carry + signExtend12 (0 : BitVec 12))
    ((if BitVec.ult s1 n1 then (1 : Word) else 0) |||
     (if BitVec.ult (s1 - n1)
       (if BitVec.ult s0 n0 then (1 : Word) else 0) then (1 : Word) else 0))
    s2 s3 n2 n3
  runBlock F B


/-- Pass-2 front half: masked limb 0 + limb 1 (15 instructions). -/
theorem evm_addmod_cond_sub_pass2_front_spec_within
    (base sp maskIn x5Old x6Old x7Old x10Old : Word)
    (s0 s1 n0 n1 : Word) :
    cpsTripleWithin 15 base (base + 60)
      (CodeReq.union (CodeReq.singleton base (.LD .x6 .x12 (0 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x7 .x12 (3872 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 8) (.AND .x7 .x7 .x11))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x10 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 20) (.SD .x12 .x5 (0 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x6 .x12 (8 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x7 .x12 (3880 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 32) (.AND .x7 .x7 .x11))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 40) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 44) (.SLTU .x7 .x6 .x10))
      (CodeReq.union (CodeReq.singleton (base + 48) (.SUB .x6 .x6 .x10))
      (CodeReq.union (CodeReq.singleton (base + 52) (.OR .x10 .x5 .x7))
       (CodeReq.singleton (base + 56) (.SD .x12 .x6 (8 : BitVec 12)))))))))))))))))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ maskIn) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ n1))
      ((.x12 ↦ᵣ sp) **
       (.x5 ↦ᵣ (if BitVec.ult s1 (n1 &&& maskIn) then (1 : Word) else 0)) **
       (.x6 ↦ᵣ ((s1 - (n1 &&& maskIn)) -
          (if BitVec.ult s0 (n0 &&& maskIn) then (1 : Word) else 0))) **
       (.x7 ↦ᵣ (if BitVec.ult (s1 - (n1 &&& maskIn))
          (if BitVec.ult s0 (n0 &&& maskIn) then (1 : Word) else 0)
          then (1 : Word) else 0)) **
       (.x10 ↦ᵣ ((if BitVec.ult s1 (n1 &&& maskIn) then (1 : Word) else 0) |||
          (if BitVec.ult (s1 - (n1 &&& maskIn))
            (if BitVec.ult s0 (n0 &&& maskIn) then (1 : Word) else 0)
            then (1 : Word) else 0))) **
       (.x11 ↦ᵣ maskIn) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ (s0 - (n0 &&& maskIn))) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ ((s1 - (n1 &&& maskIn)) -
          (if BitVec.ult s0 (n0 &&& maskIn) then (1 : Word) else 0))) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ n1)) := by
  have P0 := evm_addmod_cond_sub_pass2_low_spec_within base sp
    x5Old x6Old x7Old x10Old maskIn s0 n0
  have P1 := evm_addmod_cond_sub_pass2_limb_spec_within 8 3880 (base + 24) sp
    (s0 - (n0 &&& maskIn)) s0 (n0 &&& maskIn) maskIn
    (if BitVec.ult s0 (n0 &&& maskIn) then (1 : Word) else 0)
    s1 n1
  runBlock P0 P1

/-- Pass-2 back half: masked limb 2 + high limb (15 instructions), incoming
    values as parameters. -/
theorem evm_addmod_cond_sub_pass2_back_spec_within
    (base sp maskIn x5In x6In x7In borrowIn : Word)
    (s2 s3 n2 n3 : Word) :
    cpsTripleWithin 15 base (base + 60)
      (CodeReq.union (CodeReq.singleton base (.LD .x6 .x12 (16 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x7 .x12 (3888 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 8) (.AND .x7 .x7 .x11))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 20) (.SLTU .x7 .x6 .x10))
      (CodeReq.union (CodeReq.singleton (base + 24) (.SUB .x6 .x6 .x10))
      (CodeReq.union (CodeReq.singleton (base + 28) (.OR .x10 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 32) (.SD .x12 .x6 (16 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 36) (.LD .x6 .x12 (24 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 40) (.LD .x7 .x12 (3896 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 44) (.AND .x7 .x7 .x11))
      (CodeReq.union (CodeReq.singleton (base + 48) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 52) (.SUB .x6 .x6 .x10))
       (CodeReq.singleton (base + 56) (.SD .x12 .x6 (24 : BitVec 12)))))))))))))))))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5In) ** (.x6 ↦ᵣ x6In) ** (.x7 ↦ᵣ x7In) **
       (.x10 ↦ᵣ borrowIn) ** (.x11 ↦ᵣ maskIn) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ sp) **
       (.x5 ↦ᵣ (if BitVec.ult s2 (n2 &&& maskIn) then (1 : Word) else 0)) **
       (.x6 ↦ᵣ ((s3 - (n3 &&& maskIn)) -
          ((if BitVec.ult s2 (n2 &&& maskIn) then (1 : Word) else 0) |||
           (if BitVec.ult (s2 - (n2 &&& maskIn)) borrowIn
             then (1 : Word) else 0)))) **
       (.x7 ↦ᵣ (n3 &&& maskIn)) **
       (.x10 ↦ᵣ ((if BitVec.ult s2 (n2 &&& maskIn) then (1 : Word) else 0) |||
          (if BitVec.ult (s2 - (n2 &&& maskIn)) borrowIn
            then (1 : Word) else 0))) **
       (.x11 ↦ᵣ maskIn) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ
          ((s2 - (n2 &&& maskIn)) - borrowIn)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ
          ((s3 - (n3 &&& maskIn)) -
           ((if BitVec.ult s2 (n2 &&& maskIn) then (1 : Word) else 0) |||
            (if BitVec.ult (s2 - (n2 &&& maskIn)) borrowIn
              then (1 : Word) else 0)))) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ n3)) := by
  have P2 := evm_addmod_cond_sub_pass2_limb_spec_within 16 3888 base sp
    x5In x6In x7In maskIn borrowIn s2 n2
  have P3 := evm_addmod_cond_sub_pass2_high_spec_within (base + 36) sp
    (if BitVec.ult s2 (n2 &&& maskIn) then (1 : Word) else 0)
    ((s2 - (n2 &&& maskIn)) - borrowIn)
    (if BitVec.ult (s2 - (n2 &&& maskIn)) borrowIn then (1 : Word) else 0)
    maskIn
    ((if BitVec.ult s2 (n2 &&& maskIn) then (1 : Word) else 0) |||
     (if BitVec.ult (s2 - (n2 &&& maskIn)) borrowIn then (1 : Word) else 0))
    s3 n3
  runBlock P2 P3


/-- Pass-2 full spec via the two halves. -/
theorem evm_addmod_cond_sub_pass2_spec_within
    (base sp maskIn x5Old x6Old x7Old x10Old : Word)
    (s0 s1 s2 s3 n0 n1 n2 n3 : Word) :
    let mm0 := n0 &&& maskIn
    let c0 := if BitVec.ult s0 mm0 then (1 : Word) else 0
    let r0 := s0 - mm0
    let mm1 := n1 &&& maskIn
    let f1 := if BitVec.ult s1 mm1 then (1 : Word) else 0
    let e1 := s1 - mm1
    let g1 := if BitVec.ult e1 c0 then (1 : Word) else 0
    let r1 := e1 - c0
    let c1 := f1 ||| g1
    let mm2 := n2 &&& maskIn
    let f2 := if BitVec.ult s2 mm2 then (1 : Word) else 0
    let e2 := s2 - mm2
    let g2 := if BitVec.ult e2 c1 then (1 : Word) else 0
    let r2 := e2 - c1
    let c2 := f2 ||| g2
    let mm3 := n3 &&& maskIn
    let r3 := (s3 - mm3) - c2
    cpsTripleWithin 30 base (base + 120)
      (CodeReq.union (CodeReq.singleton base (.LD .x6 .x12 (0 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x7 .x12 (3872 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 8) (.AND .x7 .x7 .x11))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x10 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 20) (.SD .x12 .x5 (0 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x6 .x12 (8 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x7 .x12 (3880 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 32) (.AND .x7 .x7 .x11))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 40) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 44) (.SLTU .x7 .x6 .x10))
      (CodeReq.union (CodeReq.singleton (base + 48) (.SUB .x6 .x6 .x10))
      (CodeReq.union (CodeReq.singleton (base + 52) (.OR .x10 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 56) (.SD .x12 .x6 (8 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 60) (.LD .x6 .x12 (16 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 64) (.LD .x7 .x12 (3888 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 68) (.AND .x7 .x7 .x11))
      (CodeReq.union (CodeReq.singleton (base + 72) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 76) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 80) (.SLTU .x7 .x6 .x10))
      (CodeReq.union (CodeReq.singleton (base + 84) (.SUB .x6 .x6 .x10))
      (CodeReq.union (CodeReq.singleton (base + 88) (.OR .x10 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 92) (.SD .x12 .x6 (16 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 96) (.LD .x6 .x12 (24 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 100) (.LD .x7 .x12 (3896 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 104) (.AND .x7 .x7 .x11))
      (CodeReq.union (CodeReq.singleton (base + 108) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 112) (.SUB .x6 .x6 .x10))
       (CodeReq.singleton (base + 116) (.SD .x12 .x6 (24 : BitVec 12))))))))))))))))))))))))))))))))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ maskIn) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ f2) ** (.x6 ↦ᵣ r3) ** (.x7 ↦ᵣ mm3) **
       (.x10 ↦ᵣ c2) ** (.x11 ↦ᵣ maskIn) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ n3)) := by
  intro mm0 c0 r0 mm1 f1 e1 g1 r1 c1 mm2 f2 e2 g2 r2 c2 mm3 r3
  simp only [mm0, c0, r0, mm1, f1, e1, g1, r1, c1, mm2, f2, e2, g2, r2, c2,
    mm3, r3]
  have F := evm_addmod_cond_sub_pass2_front_spec_within base sp maskIn
    x5Old x6Old x7Old x10Old s0 s1 n0 n1
  have B := evm_addmod_cond_sub_pass2_back_spec_within (base + 60) sp maskIn
    (if BitVec.ult s1 (n1 &&& maskIn) then (1 : Word) else 0)
    ((s1 - (n1 &&& maskIn)) -
      (if BitVec.ult s0 (n0 &&& maskIn) then (1 : Word) else 0))
    (if BitVec.ult (s1 - (n1 &&& maskIn))
      (if BitVec.ult s0 (n0 &&& maskIn) then (1 : Word) else 0)
      then (1 : Word) else 0)
    ((if BitVec.ult s1 (n1 &&& maskIn) then (1 : Word) else 0) |||
     (if BitVec.ult (s1 - (n1 &&& maskIn))
       (if BitVec.ult s0 (n0 &&& maskIn) then (1 : Word) else 0)
       then (1 : Word) else 0))
    s2 s3 n2 n3
  runBlock F B

end EvmAsm.Evm64.AddMod.Compose
