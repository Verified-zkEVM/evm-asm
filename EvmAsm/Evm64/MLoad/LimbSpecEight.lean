/-
  EvmAsm.Evm64.MLoad.LimbSpecEight

  Eight-byte byte-pack spec for the MLOAD per-limb loop, extracted from
  `LimbSpec.lean` to satisfy the 1500-line file-size guardrail (slice 3c
  brought the merged file to 1528 lines). The seven-byte spec and its
  helper definitions (`mloadBytePackSevenCode`,
  `mloadBytePackSevenPre/Post_unfold`, `mload_byte_pack_seven_spec_within`)
  remain in `LimbSpec.lean`; this file consumes them via the umbrella
  import below.

  Defines:
    * `mloadBytePackEightCode` (22-instruction `CodeReq` union)
    * `mloadBytePackEightPre` / `mloadBytePackEightPost` (irreducible
      assertions) and their `_unfold` lemmas
    * `mload_byte_pack_eight_spec_within`, the final `n = 8` rung
      composing the seven-byte spec with one trailing
      `LBU + SLLI + OR` triple via `cpsTripleWithin_seq`.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.MLoad.LimbSpec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Bundled CodeReq for `mload_byte_pack_eight_spec_within`: a 22-instruction
    union extending `mloadBytePackSevenCode` with one additional
    `LBU/SLLI/OR` triple at `base + 76 / base + 80 / base + 84` for the
    eighth byte. -/
def mloadBytePackEightCode
    (addrReg byteReg accReg : Reg)
    (off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12)
    (base : Word) : CodeReq :=
  (mloadBytePackSevenCode addrReg byteReg accReg
      off0 off1 off2 off3 off4 off5 off6 base).union
    ((CodeReq.singleton (base + 76) (.LBU byteReg addrReg off7)).union
     ((CodeReq.singleton (base + 80) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
      (CodeReq.singleton (base + 84) (.OR accReg accReg byteReg))))

/-- Bundled precondition for `mload_byte_pack_eight_spec_within`: the
    three roles `addrReg ↦ᵣ addrPtr`, `byteReg ↦ᵣ byteOld`,
    `accReg ↦ᵣ accOld`, plus the source dword `dwordAddr ↦ₘ wordVal`.

    Pulled into an `@[irreducible]` definition (mirroring the slice 3d-pre6
    convention from PR #1703) so the spec statement is not cluttered by a
    long chain of `let`-bindings; downstream callers see a single named
    handle and use `mloadBytePackEightPre_unfold` to expand on demand. -/
@[irreducible]
def mloadBytePackEightPre
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld wordVal dwordAddr : Word) : Assertion :=
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
  (dwordAddr ↦ₘ wordVal)

theorem mloadBytePackEightPre_unfold
    {addrReg byteReg accReg : Reg}
    {addrPtr accOld byteOld wordVal dwordAddr : Word} :
    mloadBytePackEightPre addrReg byteReg accReg
        addrPtr accOld byteOld wordVal dwordAddr =
    ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
     (dwordAddr ↦ₘ wordVal)) := by
  delta mloadBytePackEightPre; rfl

/-- Bundled postcondition for `mload_byte_pack_eight_spec_within`: after
    the 22-instruction sequence, `byteReg` holds the last byte loaded
    (`b7`) and `accReg` holds the big-endian fold
    `(((((((b0 <<< 8) ||| b1) <<< 8 ||| b2) <<< 8 ||| b3) <<< 8 ||| b4)
        <<< 8 ||| b5) <<< 8 ||| b6) <<< 8 ||| b7`. -/
@[irreducible]
def mloadBytePackEightPost
    (addrReg byteReg accReg : Reg)
    (addrPtr wordVal dwordAddr : Word)
    (off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12) : Assertion :=
  let b0 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off0))).zeroExtend 64
  let b1 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off1))).zeroExtend 64
  let b2 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off2))).zeroExtend 64
  let b3 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off3))).zeroExtend 64
  let b4 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off4))).zeroExtend 64
  let b5 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off5))).zeroExtend 64
  let b6 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off6))).zeroExtend 64
  let b7 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off7))).zeroExtend 64
  let accFinal :=
    ((((((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3)
        <<< (8 : Nat) ||| b4) <<< (8 : Nat) ||| b5) <<< (8 : Nat) ||| b6)
        <<< (8 : Nat) ||| b7
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b7) ** (accReg ↦ᵣ accFinal) **
  (dwordAddr ↦ₘ wordVal)

theorem mloadBytePackEightPost_unfold
    {addrReg byteReg accReg : Reg}
    {addrPtr wordVal dwordAddr : Word}
    {off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12} :
    mloadBytePackEightPost addrReg byteReg accReg
        addrPtr wordVal dwordAddr off0 off1 off2 off3 off4 off5 off6 off7 =
    (let b0 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off0))).zeroExtend 64
     let b1 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off1))).zeroExtend 64
     let b2 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off2))).zeroExtend 64
     let b3 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off3))).zeroExtend 64
     let b4 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off4))).zeroExtend 64
     let b5 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off5))).zeroExtend 64
     let b6 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off6))).zeroExtend 64
     let b7 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off7))).zeroExtend 64
     let accFinal :=
       ((((((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3)
           <<< (8 : Nat) ||| b4) <<< (8 : Nat) ||| b5) <<< (8 : Nat) ||| b6)
           <<< (8 : Nat) ||| b7
     (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b7) ** (accReg ↦ᵣ accFinal) **
     (dwordAddr ↦ₘ wordVal)) := by
  delta mloadBytePackEightPost; rfl

/-- Eight-byte big-endian byte-pack spec (22 instructions): seed `LBU`
    loading `b0`, then seven `LBU + SLLI + OR` triples folding `b1`..`b7`
    in big-endian order, yielding
    `(((((((b0 <<< 8) ||| b1) <<< 8 ||| b2) <<< 8 ||| b3) <<< 8 ||| b4)
        <<< 8 ||| b5) <<< 8 ||| b6) <<< 8 ||| b7`
    in `accReg`.

    This is the final `n = 8` rung in the inductive ladder
    `mload_byte_pack_init` (n=1) → `mload_byte_pack_two` (n=2) → … →
    `mload_byte_pack_seven` (n=7) → `mload_byte_pack_eight` (n=8). The
    full per-limb spec `mload_one_limb_spec_within` then composes this
    8-byte pattern with a single trailing `SD`. Proved by composing the
    existing 7-byte spec (PR #1703) with one
    `mload_byte_pack_step_spec_within` application; no new tactic
    machinery is needed. -/
theorem mload_byte_pack_eight_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld wordVal : Word)
    (dwordAddr : Word)
    (off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0  : accReg  ≠ .x0)
    (h_align0 : alignToDword (addrPtr + signExtend12 off0) = dwordAddr)
    (h_valid0 : isValidByteAccess (addrPtr + signExtend12 off0) = true)
    (h_align1 : alignToDword (addrPtr + signExtend12 off1) = dwordAddr)
    (h_valid1 : isValidByteAccess (addrPtr + signExtend12 off1) = true)
    (h_align2 : alignToDword (addrPtr + signExtend12 off2) = dwordAddr)
    (h_valid2 : isValidByteAccess (addrPtr + signExtend12 off2) = true)
    (h_align3 : alignToDword (addrPtr + signExtend12 off3) = dwordAddr)
    (h_valid3 : isValidByteAccess (addrPtr + signExtend12 off3) = true)
    (h_align4 : alignToDword (addrPtr + signExtend12 off4) = dwordAddr)
    (h_valid4 : isValidByteAccess (addrPtr + signExtend12 off4) = true)
    (h_align5 : alignToDword (addrPtr + signExtend12 off5) = dwordAddr)
    (h_valid5 : isValidByteAccess (addrPtr + signExtend12 off5) = true)
    (h_align6 : alignToDword (addrPtr + signExtend12 off6) = dwordAddr)
    (h_valid6 : isValidByteAccess (addrPtr + signExtend12 off6) = true)
    (h_align7 : alignToDword (addrPtr + signExtend12 off7) = dwordAddr)
    (h_valid7 : isValidByteAccess (addrPtr + signExtend12 off7) = true) :
    cpsTripleWithin 22 base (base + 88)
      (mloadBytePackEightCode addrReg byteReg accReg
        off0 off1 off2 off3 off4 off5 off6 off7 base)
      (mloadBytePackEightPre addrReg byteReg accReg
        addrPtr accOld byteOld wordVal dwordAddr)
      (mloadBytePackEightPost addrReg byteReg accReg
        addrPtr wordVal dwordAddr off0 off1 off2 off3 off4 off5 off6 off7) := by
  rw [mloadBytePackEightPre_unfold, mloadBytePackEightPost_unfold]
  set b0 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off0))).zeroExtend 64
  set b1 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off1))).zeroExtend 64
  set b2 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off2))).zeroExtend 64
  set b3 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off3))).zeroExtend 64
  set b4 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off4))).zeroExtend 64
  set b5 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off5))).zeroExtend 64
  set b6 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off6))).zeroExtend 64
  set b7 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off7))).zeroExtend 64
  set accAfter7 :=
    (((((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3)
        <<< (8 : Nat) ||| b4) <<< (8 : Nat) ||| b5) <<< (8 : Nat) ||| b6
    with h_accAfter7
  set accFinal := (accAfter7 <<< (8 : Nat)) ||| b7
  -- Step 1: 19-instruction 7-byte spec at `base`.
  have sevenRaw := mload_byte_pack_seven_spec_within addrReg byteReg accReg
    addrPtr accOld byteOld wordVal dwordAddr off0 off1 off2 off3 off4 off5 off6 base
    h_byte_ne_x0 h_acc_ne_x0 h_align0 h_valid0 h_align1 h_valid1
    h_align2 h_valid2 h_align3 h_valid3 h_align4 h_valid4 h_align5 h_valid5
    h_align6 h_valid6
  rw [mloadBytePackSevenPre_unfold, mloadBytePackSevenPost_unfold] at sevenRaw
  -- Step 2: 3-instruction byte-pack triple at `base + 76` folding `b7`.
  have step := mload_byte_pack_step_spec_within addrReg byteReg accReg
    addrPtr accAfter7 b6 wordVal dwordAddr off7 (base + 76)
    h_byte_ne_x0 h_acc_ne_x0 h_align7 h_valid7
  rw [show (base + 76 : Word) + 12 = base + 88 from by bv_omega] at step
  rw [show (base + 76 : Word) + 4 = base + 80 from by bv_omega,
      show (base + 76 : Word) + 8 = base + 84 from by bv_omega] at step
  -- Disjointness between the seven-byte block (addresses base, base+4,
  -- base+8, …, base+72) and the trailing triple (base+76, base+80,
  -- base+84). 19 leaf inequalities.
  have hd_step : CodeReq.Disjoint
      (mloadBytePackSevenCode addrReg byteReg accReg
        off0 off1 off2 off3 off4 off5 off6 base)
      ((CodeReq.singleton (base + 76) (.LBU byteReg addrReg off7)).union
       ((CodeReq.singleton (base + 80) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
        (CodeReq.singleton (base + 84) (.OR accReg accReg byteReg)))) := by
    unfold mloadBytePackSevenCode mloadBytePackSixCode mloadBytePackFiveCode
      mloadBytePackFourCode mloadBytePackThreeCode mloadBytePackTwoCode
    have leaf : ∀ {a : Word} {i : Instr},
        a ≠ base + 76 → a ≠ base + 80 → a ≠ base + 84 →
        CodeReq.Disjoint (CodeReq.singleton a i)
            ((CodeReq.singleton (base + 76) (.LBU byteReg addrReg off7)).union
             ((CodeReq.singleton (base + 80) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
              (CodeReq.singleton (base + 84) (.OR accReg accReg byteReg)))) := by
      intro a i h76 h80 h84
      exact CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton h76)
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.singleton h80)
          (CodeReq.Disjoint.singleton h84))
    -- Top-level structure of mloadBytePackSevenCode is
    --   Seven = Six ∪ trio_64
    -- Six = Five ∪ trio_52
    -- Five = Four ∪ trio_40
    -- Four = (Two ∪ trio_16) ∪ trio_28
    -- Two = leaves at base, +4, +8, +12.
    refine CodeReq.Disjoint.union_left ?_ ?_
    · -- Six
      refine CodeReq.Disjoint.union_left ?_ ?_
      · -- Five
        refine CodeReq.Disjoint.union_left ?_ ?_
        · -- Four
          refine CodeReq.Disjoint.union_left ?_ ?_
          · -- (Two ∪ trio_16)
            refine CodeReq.Disjoint.union_left ?_ ?_
            · -- Two: 4 leaves at base, +4, +8, +12
              refine CodeReq.Disjoint.union_left
                (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
              refine CodeReq.Disjoint.union_left
                (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
              refine CodeReq.Disjoint.union_left
                (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
              exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
            · -- trio_16: leaves at +16, +20, +24
              refine CodeReq.Disjoint.union_left
                (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
              refine CodeReq.Disjoint.union_left
                (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
              exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
          · -- trio_28: leaves at +28, +32, +36
            refine CodeReq.Disjoint.union_left
              (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
            refine CodeReq.Disjoint.union_left
              (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
            exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
        · -- trio_40: leaves at +40, +44, +48
          refine CodeReq.Disjoint.union_left
            (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
          refine CodeReq.Disjoint.union_left
            (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
          exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
      · -- trio_52: leaves at +52, +56, +60
        refine CodeReq.Disjoint.union_left
          (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
        refine CodeReq.Disjoint.union_left
          (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
        exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
    · -- trio_64: leaves at +64, +68, +72
      refine CodeReq.Disjoint.union_left
        (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
      refine CodeReq.Disjoint.union_left
        (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
      exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
  -- The final code-req shape is `mloadBytePackEightCode = seven.union triple`.
  exact cpsTripleWithin_seq hd_step sevenRaw step

/-! ## One-limb spec (8-byte byte-pack + final SD)

Composes `mload_byte_pack_eight_spec_within` (22 instructions covering
`base..base+88`) with `generic_sd_spec_within` (1 instruction at
`base + 88`) into a single 23-instruction spec for one EVM-stack output
limb. This is the level-2 building block per `docs/99-mload-design.md`
§5.2; `evm_mload_stack_spec_within` (slice 3e) composes four of these
back-to-back. Beads tracking: `evm-asm-h9e8`. -/

/-- Bundled CodeReq for `mload_one_limb_spec_within`: the eight-byte
    byte-pack block at `base..base+84` plus a single `SD .x12 accReg
    dstOff` at `base + 88`. -/
def mloadOneLimbCode
    (addrReg byteReg accReg : Reg)
    (off0 off1 off2 off3 off4 off5 off6 off7 dstOff : BitVec 12)
    (base : Word) : CodeReq :=
  (mloadBytePackEightCode addrReg byteReg accReg
      off0 off1 off2 off3 off4 off5 off6 off7 base).union
    (CodeReq.singleton (base + 88) (.SD .x12 accReg dstOff))

/-- Bundled precondition for `mload_one_limb_spec_within`: the four
    "byte-pack" atoms (`addrReg`, `byteReg`, `accReg`, source
    `dwordAddr`) plus the SD-side atoms (`.x12 ↦ᵣ sp` and the
    destination dword cell at `sp + signExtend12 dstOff`).

    Pulled into an `@[irreducible]` definition (mirroring
    `mloadBytePackEightPre`) so the spec statement is not cluttered by a
    long chain of `let`-bindings; downstream callers see a single named
    handle and use `mloadOneLimbPre_unfold` to expand on demand. -/
@[irreducible]
def mloadOneLimbPre
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld wordVal dwordAddr sp dstWordOld : Word)
    (dstOff : BitVec 12) : Assertion :=
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
  (dwordAddr ↦ₘ wordVal) ** ((.x12 : Reg) ↦ᵣ sp) **
  ((sp + signExtend12 dstOff) ↦ₘ dstWordOld)

theorem mloadOneLimbPre_unfold
    {addrReg byteReg accReg : Reg}
    {addrPtr accOld byteOld wordVal dwordAddr sp dstWordOld : Word}
    {dstOff : BitVec 12} :
    mloadOneLimbPre addrReg byteReg accReg
        addrPtr accOld byteOld wordVal dwordAddr sp dstWordOld dstOff =
    ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
     (dwordAddr ↦ₘ wordVal) ** ((.x12 : Reg) ↦ᵣ sp) **
     ((sp + signExtend12 dstOff) ↦ₘ dstWordOld)) := by
  delta mloadOneLimbPre; rfl

/-- Bundled postcondition for `mload_one_limb_spec_within`: after the
    23-instruction sequence, `byteReg` holds the last loaded byte
    (`b7`), `accReg` holds the big-endian fold `accFinal`, and the
    destination dword slot at `sp + signExtend12 dstOff` has been
    overwritten with `accFinal`. The byte/`accFinal` `let`-bindings
    mirror `mloadBytePackEightPost` so downstream proofs can `rfl` past
    the unfold and reuse the same atoms. -/
@[irreducible]
def mloadOneLimbPost
    (addrReg byteReg accReg : Reg)
    (addrPtr wordVal dwordAddr sp : Word)
    (off0 off1 off2 off3 off4 off5 off6 off7 dstOff : BitVec 12) : Assertion :=
  let b0 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off0))).zeroExtend 64
  let b1 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off1))).zeroExtend 64
  let b2 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off2))).zeroExtend 64
  let b3 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off3))).zeroExtend 64
  let b4 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off4))).zeroExtend 64
  let b5 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off5))).zeroExtend 64
  let b6 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off6))).zeroExtend 64
  let b7 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off7))).zeroExtend 64
  let accFinal :=
    ((((((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3)
        <<< (8 : Nat) ||| b4) <<< (8 : Nat) ||| b5) <<< (8 : Nat) ||| b6)
        <<< (8 : Nat) ||| b7
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b7) ** (accReg ↦ᵣ accFinal) **
  (dwordAddr ↦ₘ wordVal) ** ((.x12 : Reg) ↦ᵣ sp) **
  ((sp + signExtend12 dstOff) ↦ₘ accFinal)

theorem mloadOneLimbPost_unfold
    {addrReg byteReg accReg : Reg}
    {addrPtr wordVal dwordAddr sp : Word}
    {off0 off1 off2 off3 off4 off5 off6 off7 dstOff : BitVec 12} :
    mloadOneLimbPost addrReg byteReg accReg
        addrPtr wordVal dwordAddr sp
        off0 off1 off2 off3 off4 off5 off6 off7 dstOff =
    (let b0 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off0))).zeroExtend 64
     let b1 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off1))).zeroExtend 64
     let b2 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off2))).zeroExtend 64
     let b3 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off3))).zeroExtend 64
     let b4 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off4))).zeroExtend 64
     let b5 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off5))).zeroExtend 64
     let b6 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off6))).zeroExtend 64
     let b7 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off7))).zeroExtend 64
     let accFinal :=
       ((((((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3)
           <<< (8 : Nat) ||| b4) <<< (8 : Nat) ||| b5) <<< (8 : Nat) ||| b6)
           <<< (8 : Nat) ||| b7
     (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b7) ** (accReg ↦ᵣ accFinal) **
     (dwordAddr ↦ₘ wordVal) ** ((.x12 : Reg) ↦ᵣ sp) **
     ((sp + signExtend12 dstOff) ↦ₘ accFinal)) := by
  delta mloadOneLimbPost; rfl

/-- One-limb MLOAD spec (23 instructions): pack eight big-endian bytes
    from EVM memory at `addrPtr + off0..off7` into `accReg` (via the
    seed-LBU + 7×(LBU+SLLI+OR) eight-byte rung), then `SD` the packed
    limb to the EVM stack slot at `sp + signExtend12 dstOff`.

    Precondition: the four "byte-pack" atoms (`addrReg`, `byteReg`,
    `accReg`, source `dwordAddr`) plus the SD-side atoms (`.x12 ↦ᵣ sp`
    and the destination dword cell). Postcondition: `accReg` holds the
    big-endian fold `accFinal`, `byteReg` holds the last loaded byte
    (`b7`), and the destination dword has been overwritten with
    `accFinal`.

    Side conditions: `byteReg`/`accReg` are not `x0`; each source byte
    address aligns to `dwordAddr` and is a valid byte access; the
    destination dword address is aligned (it IS the address used as the
    `↦ₘ` key) and a valid dword access. Register disjointness between
    `.x12`, `accReg`, `addrReg`, `byteReg` is enforced implicitly by
    `sepConj` compatibility in the precondition; it does NOT need to be
    spelled out as separate hypotheses. -/
theorem mload_one_limb_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld wordVal sp dstWordOld : Word)
    (dwordAddr : Word)
    (off0 off1 off2 off3 off4 off5 off6 off7 dstOff : BitVec 12) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0  : accReg  ≠ .x0)
    (h_align0 : alignToDword (addrPtr + signExtend12 off0) = dwordAddr)
    (h_valid0 : isValidByteAccess (addrPtr + signExtend12 off0) = true)
    (h_align1 : alignToDword (addrPtr + signExtend12 off1) = dwordAddr)
    (h_valid1 : isValidByteAccess (addrPtr + signExtend12 off1) = true)
    (h_align2 : alignToDword (addrPtr + signExtend12 off2) = dwordAddr)
    (h_valid2 : isValidByteAccess (addrPtr + signExtend12 off2) = true)
    (h_align3 : alignToDword (addrPtr + signExtend12 off3) = dwordAddr)
    (h_valid3 : isValidByteAccess (addrPtr + signExtend12 off3) = true)
    (h_align4 : alignToDword (addrPtr + signExtend12 off4) = dwordAddr)
    (h_valid4 : isValidByteAccess (addrPtr + signExtend12 off4) = true)
    (h_align5 : alignToDword (addrPtr + signExtend12 off5) = dwordAddr)
    (h_valid5 : isValidByteAccess (addrPtr + signExtend12 off5) = true)
    (h_align6 : alignToDword (addrPtr + signExtend12 off6) = dwordAddr)
    (h_valid6 : isValidByteAccess (addrPtr + signExtend12 off6) = true)
    (h_align7 : alignToDword (addrPtr + signExtend12 off7) = dwordAddr)
    (h_valid7 : isValidByteAccess (addrPtr + signExtend12 off7) = true) :
    cpsTripleWithin 23 base (base + 92)
      (mloadOneLimbCode addrReg byteReg accReg
        off0 off1 off2 off3 off4 off5 off6 off7 dstOff base)
      (mloadOneLimbPre addrReg byteReg accReg
        addrPtr accOld byteOld wordVal dwordAddr sp dstWordOld dstOff)
      (mloadOneLimbPost addrReg byteReg accReg
        addrPtr wordVal dwordAddr sp
        off0 off1 off2 off3 off4 off5 off6 off7 dstOff) := by
  rw [mloadOneLimbPre_unfold, mloadOneLimbPost_unfold]
  -- Zeta-reduce the `let`-bindings exposed by `mloadOneLimbPost_unfold`
  -- so that subsequent `set` tactics can fold occurrences of `b0..b7`
  -- and `accFinal` uniformly across the goal.
  dsimp only []
  set b0 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off0))).zeroExtend 64
  set b1 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off1))).zeroExtend 64
  set b2 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off2))).zeroExtend 64
  set b3 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off3))).zeroExtend 64
  set b4 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off4))).zeroExtend 64
  set b5 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off5))).zeroExtend 64
  set b6 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off6))).zeroExtend 64
  set b7 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off7))).zeroExtend 64
  set accFinal :=
    ((((((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3)
        <<< (8 : Nat) ||| b4) <<< (8 : Nat) ||| b5) <<< (8 : Nat) ||| b6)
        <<< (8 : Nat) ||| b7
  unfold mloadOneLimbCode
  rw [show (23 : Nat) = 22 + 1 from rfl,
      show (base + 92 : Word) = base + 88 + 4 from by bv_omega]
  -- Step 1: 22-instruction eight-byte byte-pack at `base`. Unfold its
  -- bundled pre/post so the hypothesis is in raw `sepConj` shape.
  have eight := mload_byte_pack_eight_spec_within addrReg byteReg accReg
    addrPtr accOld byteOld wordVal dwordAddr
    off0 off1 off2 off3 off4 off5 off6 off7 base
    h_byte_ne_x0 h_acc_ne_x0
    h_align0 h_valid0 h_align1 h_valid1 h_align2 h_valid2 h_align3 h_valid3
    h_align4 h_valid4 h_align5 h_valid5 h_align6 h_valid6 h_align7 h_valid7
  rw [mloadBytePackEightPre_unfold, mloadBytePackEightPost_unfold] at eight
  -- Step 2: SD spec at `base + 88` with rs1 = .x12, rs2 = accReg.
  have sd := generic_sd_spec_within (.x12 : Reg) accReg sp accFinal dstWordOld
    dstOff (base + 88)
  -- Frame eight with `(.x12 ↦ᵣ sp) ** (dstSlot ↦ₘ dstWordOld)` on the right.
  have eightF := cpsTripleWithin_frameR
    (F := ((.x12 : Reg) ↦ᵣ sp) ** ((sp + signExtend12 dstOff) ↦ₘ dstWordOld))
    (by pcFree) eight
  -- Frame SD with `(addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b7) **
  -- (dwordAddr ↦ₘ wordVal)` on the left.
  have sdF := cpsTripleWithin_frameL
    (F := (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b7) ** (dwordAddr ↦ₘ wordVal))
    (by pcFree) sd
  -- Bridge: eight's framed post equals sd's framed pre (AC-equivalence).
  have hMid :
      (((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b7) ** (dwordAddr ↦ₘ wordVal)) **
        (((.x12 : Reg) ↦ᵣ sp) ** (accReg ↦ᵣ accFinal) **
         ((sp + signExtend12 dstOff) ↦ₘ dstWordOld))) =
      (((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b7) ** (accReg ↦ᵣ accFinal) **
       (dwordAddr ↦ₘ wordVal)) **
        (((.x12 : Reg) ↦ᵣ sp) **
         ((sp + signExtend12 dstOff) ↦ₘ dstWordOld))) := by ac_rfl
  -- Disjointness between the eight-byte block (addresses base, base+4,
  -- …, base+84) and the trailing SD at base+88. 22 leaf inequalities.
  have hd_step : CodeReq.Disjoint
      (mloadBytePackEightCode addrReg byteReg accReg
        off0 off1 off2 off3 off4 off5 off6 off7 base)
      (CodeReq.singleton (base + 88) (.SD (.x12 : Reg) accReg dstOff)) := by
    unfold mloadBytePackEightCode mloadBytePackSevenCode mloadBytePackSixCode
      mloadBytePackFiveCode mloadBytePackFourCode mloadBytePackThreeCode
      mloadBytePackTwoCode
    have leaf : ∀ {a : Word} {i : Instr},
        a ≠ base + 88 →
        CodeReq.Disjoint (CodeReq.singleton a i)
            (CodeReq.singleton (base + 88) (.SD (.x12 : Reg) accReg dstOff)) := by
      intro a i h88
      exact CodeReq.Disjoint.singleton h88
    -- mloadBytePackEightCode unfolds to 22 leaves at offsets
    -- 0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60,
    -- 64, 68, 72, 76, 80, 84.
    refine CodeReq.Disjoint.union_left ?_ ?_
    · -- Seven block
      refine CodeReq.Disjoint.union_left ?_ ?_
      · -- Six block
        refine CodeReq.Disjoint.union_left ?_ ?_
        · -- Five block
          refine CodeReq.Disjoint.union_left ?_ ?_
          · -- Four block
            refine CodeReq.Disjoint.union_left ?_ ?_
            · -- (Two ∪ trio_16)
              refine CodeReq.Disjoint.union_left ?_ ?_
              · -- Two: leaves at base, +4, +8, +12
                refine CodeReq.Disjoint.union_left
                  (leaf (by bv_omega)) ?_
                refine CodeReq.Disjoint.union_left
                  (leaf (by bv_omega)) ?_
                refine CodeReq.Disjoint.union_left
                  (leaf (by bv_omega)) ?_
                exact leaf (by bv_omega)
              · -- trio_16: leaves at +16, +20, +24
                refine CodeReq.Disjoint.union_left
                  (leaf (by bv_omega)) ?_
                refine CodeReq.Disjoint.union_left
                  (leaf (by bv_omega)) ?_
                exact leaf (by bv_omega)
            · -- trio_28: leaves at +28, +32, +36
              refine CodeReq.Disjoint.union_left
                (leaf (by bv_omega)) ?_
              refine CodeReq.Disjoint.union_left
                (leaf (by bv_omega)) ?_
              exact leaf (by bv_omega)
          · -- trio_40: leaves at +40, +44, +48
            refine CodeReq.Disjoint.union_left
              (leaf (by bv_omega)) ?_
            refine CodeReq.Disjoint.union_left
              (leaf (by bv_omega)) ?_
            exact leaf (by bv_omega)
        · -- trio_52: leaves at +52, +56, +60
          refine CodeReq.Disjoint.union_left
            (leaf (by bv_omega)) ?_
          refine CodeReq.Disjoint.union_left
            (leaf (by bv_omega)) ?_
          exact leaf (by bv_omega)
      · -- trio_64: leaves at +64, +68, +72
        refine CodeReq.Disjoint.union_left
          (leaf (by bv_omega)) ?_
        refine CodeReq.Disjoint.union_left
          (leaf (by bv_omega)) ?_
        exact leaf (by bv_omega)
    · -- trio_76: leaves at +76, +80, +84
      refine CodeReq.Disjoint.union_left
        (leaf (by bv_omega)) ?_
      refine CodeReq.Disjoint.union_left
        (leaf (by bv_omega)) ?_
      exact leaf (by bv_omega)
  -- Compose: the running assertion at base+88 must match sdF's pre.
  -- Use `cpsTripleWithin_seq` after rewriting eightF's post via `hMid`.
  have composed := cpsTripleWithin_seq hd_step (hMid ▸ eightF) sdF
  -- The composition's pre is `eightF.pre`, which is the eight-byte
  -- pre re-associated under `frameR`:
  --   ((addrReg ** byteReg ** accReg ** dwordAddr) ** (.x12 ** dstSlot))
  -- Goal pre is the flat sepConj
  --   addrReg ** byteReg ** accReg ** dwordAddr ** .x12 ** dstSlot
  -- The composition's post is sdF.post, which is similarly re-associated.
  -- Both AC-equal to the goal; use `cpsTripleWithin_weaken` + `sep_perm`.
  exact cpsTripleWithin_weaken
    (fun h hp => by sep_perm hp)
    (fun h hp => by sep_perm hp)
    composed

end EvmAsm.Evm64
