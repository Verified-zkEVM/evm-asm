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

import EvmAsm.Rv64.Program
import EvmAsm.Evm64.MLoad.LimbSpec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Side conditions for one eight-byte aligned MLOAD source window: the eight
    byte addresses `addrPtr + signExtend12 offᵢ` (i = 0..7) all align to the
    same `dwordAddr` and are valid byte accesses. Bundling the 16 per-byte
    facts (alignment + validity for each of `i = 0..7`) avoids 16-parameter
    lemma signatures in the aligned byte-pack composition layer.

    Aligned analog of `MLoad.Spec.mloadLimbWindowOk` (which threads the
    unaligned `loAddr/hiAddr/start` shape and additionally tracks
    `byteOffset`); see evm-asm-yrz5 / evm-asm-jb8a. -/
def mloadAlignedLimbWindowOk
    (addrPtr dwordAddr : Word)
    (off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12) : Prop :=
  alignToDword (addrPtr + signExtend12 off0) = dwordAddr ∧
  isValidByteAccess (addrPtr + signExtend12 off0) = true ∧
  alignToDword (addrPtr + signExtend12 off1) = dwordAddr ∧
  isValidByteAccess (addrPtr + signExtend12 off1) = true ∧
  alignToDword (addrPtr + signExtend12 off2) = dwordAddr ∧
  isValidByteAccess (addrPtr + signExtend12 off2) = true ∧
  alignToDword (addrPtr + signExtend12 off3) = dwordAddr ∧
  isValidByteAccess (addrPtr + signExtend12 off3) = true ∧
  alignToDword (addrPtr + signExtend12 off4) = dwordAddr ∧
  isValidByteAccess (addrPtr + signExtend12 off4) = true ∧
  alignToDword (addrPtr + signExtend12 off5) = dwordAddr ∧
  isValidByteAccess (addrPtr + signExtend12 off5) = true ∧
  alignToDword (addrPtr + signExtend12 off6) = dwordAddr ∧
  isValidByteAccess (addrPtr + signExtend12 off6) = true ∧
  alignToDword (addrPtr + signExtend12 off7) = dwordAddr ∧
  isValidByteAccess (addrPtr + signExtend12 off7) = true

/-- Wrapper assertion combining the canonical aligned-dword ownership cell
    `dwordAddr ↦ₘ wordVal` with the `mloadAlignedLimbWindowOk` per-byte
    alignment / validity bundle. Migrating MLOAD consumers from the
    explicit `h_window` hypothesis to this assertion (slice 3 of
    evm-asm-8xc6 / GH #2278) lets the consumer signature drop the bundle
    and recover it on demand from the assertion via the bridge lemmas
    below. Strategy (b) from evm-asm-928x: the wrapper is MLoad-specific
    and lives next to its consumers; the core sep-logic primitive
    `↦ₘ` stays untouched.

    Distinctive token: `mloadAlignedDwordIs-2278`. -/
def mloadAlignedDwordIs
    (addrPtr dwordAddr wordVal : Word)
    (off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12) : EvmAsm.Rv64.Assertion :=
  (dwordAddr ↦ₘ wordVal) **
    ⌜mloadAlignedLimbWindowOk addrPtr dwordAddr
        off0 off1 off2 off3 off4 off5 off6 off7⌝

/-- Bridge: extract the `mloadAlignedLimbWindowOk` bundle from a
    `mloadAlignedDwordIs` witness. Lets consumers that still take the
    bundle as a hypothesis migrate one call-site at a time without
    touching their proof body — the new assertion implies the old
    bundle, so the bundle is recoverable by `obtain` after `rw` of the
    consumer's pre.

    Distinctive token: `mloadAlignedLimbWindowOk_of_mloadAlignedDwordIs-2278`. -/
theorem mloadAlignedLimbWindowOk_of_mloadAlignedDwordIs
    {addrPtr dwordAddr wordVal : Word}
    {off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12}
    {s : MachineState}
    (h : (mloadAlignedDwordIs addrPtr dwordAddr wordVal
            off0 off1 off2 off3 off4 off5 off6 off7).holdsFor s) :
    mloadAlignedLimbWindowOk addrPtr dwordAddr
        off0 off1 off2 off3 off4 off5 off6 off7 := by
  obtain ⟨h, _hcompat, hP⟩ := h
  rw [mloadAlignedDwordIs] at hP
  exact ((sepConj_pure_right h).mp hP).2

/-- Bridge: extract the `↦ₘ` ownership cell from a `mloadAlignedDwordIs`
    witness. Sibling of `mloadAlignedLimbWindowOk_of_mloadAlignedDwordIs`;
    together they fully decompose the wrapper. -/
theorem memIs_of_mloadAlignedDwordIs
    {addrPtr dwordAddr wordVal : Word}
    {off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12}
    {s : MachineState}
    (h : (mloadAlignedDwordIs addrPtr dwordAddr wordVal
            off0 off1 off2 off3 off4 off5 off6 off7).holdsFor s) :
    (dwordAddr ↦ₘ wordVal).holdsFor s := by
  obtain ⟨h, hcompat, hP⟩ := h
  rw [mloadAlignedDwordIs] at hP
  exact ⟨h, hcompat, ((sepConj_pure_right h).mp hP).1⟩

/-- Introduction: pair the `↦ₘ` ownership cell with the
    `mloadAlignedLimbWindowOk` bundle to obtain the wrapper assertion.
    Used by call sites that still assemble the wrapper from an explicit
    bundle hypothesis (during the migration window). -/
theorem mloadAlignedDwordIs_of_memIs
    {addrPtr dwordAddr wordVal : Word}
    {off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12}
    {s : MachineState}
    (hMem : (dwordAddr ↦ₘ wordVal).holdsFor s)
    (hWindow : mloadAlignedLimbWindowOk addrPtr dwordAddr
        off0 off1 off2 off3 off4 off5 off6 off7) :
    (mloadAlignedDwordIs addrPtr dwordAddr wordVal
        off0 off1 off2 off3 off4 off5 off6 off7).holdsFor s := by
  obtain ⟨h, hcompat, hMem⟩ := hMem
  refine ⟨h, hcompat, ?_⟩
  rw [mloadAlignedDwordIs]
  exact (sepConj_pure_right h).mpr ⟨hMem, hWindow⟩

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

/-- Public program form of the eight-byte MLOAD byte-pack block. This mirrors
    `mloadBytePackEightCode` and gives downstream consumers an `ofProg`
    bridge without depending on the private recursive helpers in
    `MLoad.Program`. -/
def mloadBytePackEightProg
    (addrReg byteReg accReg : Reg)
    (off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12) : Program :=
  LBU accReg addrReg off0 ;;
  LBU byteReg addrReg off1 ;; SLLI accReg accReg (BitVec.ofNat 6 8) ;;
  OR' accReg accReg byteReg ;;
  LBU byteReg addrReg off2 ;; SLLI accReg accReg (BitVec.ofNat 6 8) ;;
  OR' accReg accReg byteReg ;;
  LBU byteReg addrReg off3 ;; SLLI accReg accReg (BitVec.ofNat 6 8) ;;
  OR' accReg accReg byteReg ;;
  LBU byteReg addrReg off4 ;; SLLI accReg accReg (BitVec.ofNat 6 8) ;;
  OR' accReg accReg byteReg ;;
  LBU byteReg addrReg off5 ;; SLLI accReg accReg (BitVec.ofNat 6 8) ;;
  OR' accReg accReg byteReg ;;
  LBU byteReg addrReg off6 ;; SLLI accReg accReg (BitVec.ofNat 6 8) ;;
  OR' accReg accReg byteReg ;;
  LBU byteReg addrReg off7 ;; SLLI accReg accReg (BitVec.ofNat 6 8) ;;
  OR' accReg accReg byteReg

theorem mloadBytePackEightCode_eq_ofProg
    (addrReg byteReg accReg : Reg)
    (off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12)
    (base : Word) :
    mloadBytePackEightCode addrReg byteReg accReg
      off0 off1 off2 off3 off4 off5 off6 off7 base =
    CodeReq.ofProg base
      (mloadBytePackEightProg addrReg byteReg accReg
        off0 off1 off2 off3 off4 off5 off6 off7) := by
  unfold mloadBytePackEightCode mloadBytePackSevenCode mloadBytePackSixCode
    mloadBytePackFiveCode mloadBytePackFourCode mloadBytePackThreeCode
    mloadBytePackTwoCode mloadBytePackEightProg LBU SLLI OR' single seq
  change _ = CodeReq.ofProg base
    [.LBU accReg addrReg off0,
     .LBU byteReg addrReg off1, .SLLI accReg accReg (BitVec.ofNat 6 8),
     .OR accReg accReg byteReg,
     .LBU byteReg addrReg off2, .SLLI accReg accReg (BitVec.ofNat 6 8),
     .OR accReg accReg byteReg,
     .LBU byteReg addrReg off3, .SLLI accReg accReg (BitVec.ofNat 6 8),
     .OR accReg accReg byteReg,
     .LBU byteReg addrReg off4, .SLLI accReg accReg (BitVec.ofNat 6 8),
     .OR accReg accReg byteReg,
     .LBU byteReg addrReg off5, .SLLI accReg accReg (BitVec.ofNat 6 8),
     .OR accReg accReg byteReg,
     .LBU byteReg addrReg off6, .SLLI accReg accReg (BitVec.ofNat 6 8),
     .OR accReg accReg byteReg,
     .LBU byteReg addrReg off7, .SLLI accReg accReg (BitVec.ofNat 6 8),
     .OR accReg accReg byteReg]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_singleton]
  simp only [CodeReq.union_assoc]
  bv_addr

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
    (h_window : mloadAlignedLimbWindowOk addrPtr dwordAddr
      off0 off1 off2 off3 off4 off5 off6 off7) :
    cpsTripleWithin 22 base (base + 88)
      (mloadBytePackEightCode addrReg byteReg accReg
        off0 off1 off2 off3 off4 off5 off6 off7 base)
      (mloadBytePackEightPre addrReg byteReg accReg
        addrPtr accOld byteOld wordVal dwordAddr)
      (mloadBytePackEightPost addrReg byteReg accReg
        addrPtr wordVal dwordAddr off0 off1 off2 off3 off4 off5 off6 off7) := by
  obtain ⟨h_align0, h_valid0, h_align1, h_valid1, h_align2, h_valid2,
          h_align3, h_valid3, h_align4, h_valid4, h_align5, h_valid5,
          h_align6, h_valid6, h_align7, h_valid7⟩ := h_window
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

/-- Local structural rule used by the `…_via_assertion_spec_within` migration
    (slice 3 of `evm-asm-8xc6` / GH #2278). Lifts a fact-parameterised
    triple `fact → cpsTripleWithin … P Q` to one whose precondition bundles
    the fact as a pure conjunct: `cpsTripleWithin … (P ** ⌜fact⌝) Q`.
    Symmetric counterpart of `cpsTripleWithin_strip_pure_and_convert`
    (which strips a fact while letting only the postcondition depend on
    it). Kept private here while only one consumer family uses it. -/
private theorem cpsTripleWithin_of_pure_imp
    {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} {fact : Prop}
    (h : fact → cpsTripleWithin nSteps entry exit_ cr P Q) :
    cpsTripleWithin nSteps entry exit_ cr (P ** ⌜fact⌝) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, hpq⟩ := hPR
  obtain ⟨h1, h2, hd, hunion, hPF, hR_⟩ := hpq
  have hpf := (sepConj_pure_right h1).1 hPF
  exact h hpf.2 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hunion, hpf.1, hR_⟩ hpc

/-- Migration sibling of `mload_byte_pack_eight_spec_within` that takes the
    new `mloadAlignedDwordIs` wrapper assertion (PR #2284) in its
    precondition instead of an explicit `h_window` hypothesis. The
    `mloadAlignedLimbWindowOk` bundle is now bundled into the assertion via
    `⌜·⌝`, and the canonical `dwordAddr ↦ₘ wordVal` cell from the original
    pre is replaced by the wrapper. Proved by reducing to the original
    spec via AC-rewrite of the precondition followed by
    `cpsTripleWithin_of_pure_imp` to peel the bundled fact and feed it as
    `h_window` to the original spec.

    First consumer-family migration of slice 3 of `evm-asm-8xc6`
    (GH #2278). Distinctive token:
    `mloadAlignedLimbWindowOk-consumer-migration-2278 byte_pack_eight via_assertion`. -/
theorem mload_byte_pack_eight_via_assertion_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld wordVal : Word)
    (dwordAddr : Word)
    (off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0  : accReg  ≠ .x0) :
    cpsTripleWithin 22 base (base + 88)
      (mloadBytePackEightCode addrReg byteReg accReg
        off0 off1 off2 off3 off4 off5 off6 off7 base)
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (mloadAlignedDwordIs addrPtr dwordAddr wordVal
          off0 off1 off2 off3 off4 off5 off6 off7))
      (mloadBytePackEightPost addrReg byteReg accReg
        addrPtr wordVal dwordAddr off0 off1 off2 off3 off4 off5 off6 off7) := by
  unfold mloadAlignedDwordIs
  -- AC-rearrange the precondition into `<original-pre> ** ⌜fact⌝` shape so
  -- `cpsTripleWithin_of_pure_imp` can peel the bundled `mloadAligned-
  -- LimbWindowOk` fact.
  have hpre_eq :
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
        ((dwordAddr ↦ₘ wordVal) **
          ⌜mloadAlignedLimbWindowOk addrPtr dwordAddr
              off0 off1 off2 off3 off4 off5 off6 off7⌝)) =
      (((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (dwordAddr ↦ₘ wordVal)) **
        ⌜mloadAlignedLimbWindowOk addrPtr dwordAddr
            off0 off1 off2 off3 off4 off5 off6 off7⌝) := by
    ac_rfl
  rw [hpre_eq]
  refine cpsTripleWithin_of_pure_imp (fun h_window => ?_)
  have base_spec := mload_byte_pack_eight_spec_within addrReg byteReg accReg
    addrPtr accOld byteOld wordVal dwordAddr
    off0 off1 off2 off3 off4 off5 off6 off7 base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  rw [mloadBytePackEightPre_unfold] at base_spec
  exact base_spec

/-! ## One-limb spec (8-byte byte-pack + final SD)

Composes `mload_byte_pack_eight_spec_within` (22 instructions covering
`base..base+88`) with `generic_sd_spec_within` (1 instruction at
`base + 88`) into a single 23-instruction spec for one EVM-stack output
limb. This is the level-2 building block; `evm_mload_stack_spec_within`
(slice 3e) composes four of these
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

/-- Public program form of one MLOAD limb: pack eight bytes and store the
    resulting limb to the EVM stack. -/
def mloadOneLimbProg
    (addrReg byteReg accReg : Reg)
    (off0 off1 off2 off3 off4 off5 off6 off7 dstOff : BitVec 12) : Program :=
  mloadBytePackEightProg addrReg byteReg accReg
    off0 off1 off2 off3 off4 off5 off6 off7 ;;
  SD .x12 accReg dstOff

theorem mloadOneLimbCode_eq_ofProg
    (addrReg byteReg accReg : Reg)
    (off0 off1 off2 off3 off4 off5 off6 off7 dstOff : BitVec 12)
    (base : Word) :
    mloadOneLimbCode addrReg byteReg accReg
      off0 off1 off2 off3 off4 off5 off6 off7 dstOff base =
    CodeReq.ofProg base
      (mloadOneLimbProg addrReg byteReg accReg
        off0 off1 off2 off3 off4 off5 off6 off7 dstOff) := by
  unfold mloadOneLimbCode mloadOneLimbProg
  rw [mloadBytePackEightCode_eq_ofProg]
  let pack := mloadBytePackEightProg addrReg byteReg accReg
    off0 off1 off2 off3 off4 off5 off6 off7
  let tail := SD .x12 accReg dstOff
  change (CodeReq.ofProg base pack).union
      (CodeReq.singleton (base + 88) (Instr.SD .x12 accReg dstOff)) =
    CodeReq.ofProg base (List.append pack tail)
  calc
    (CodeReq.ofProg base pack).union
        (CodeReq.singleton (base + 88) (Instr.SD .x12 accReg dstOff))
        =
      (CodeReq.ofProg base pack).union
        (CodeReq.ofProg (base + BitVec.ofNat 64 (4 * pack.length)) tail) := by
        rw [show base + BitVec.ofNat 64 (4 * pack.length) = base + 88 from by
          unfold pack mloadBytePackEightProg LBU SLLI OR' single seq
          rfl]
        unfold tail SD single
        rw [CodeReq.ofProg_singleton]
    _ = CodeReq.ofProg base (List.append pack tail) := by
        exact (@CodeReq.ofProg_append base pack tail).symm

/-- Bundled CodeReq for two adjacent MLOAD output limbs. Each one-limb block
    is 23 instructions = 92 bytes, so the second block starts at `base + 92`. -/
def mloadTwoLimbsCode
    (addrReg byteReg accReg : Reg)
    (a0 a1 a2 a3 a4 a5 a6 a7 aDst : BitVec 12)
    (b0 b1 b2 b3 b4 b5 b6 b7 bDst : BitVec 12)
    (base : Word) : CodeReq :=
  (mloadOneLimbCode addrReg byteReg accReg
    a0 a1 a2 a3 a4 a5 a6 a7 aDst base).union
  (mloadOneLimbCode addrReg byteReg accReg
    b0 b1 b2 b3 b4 b5 b6 b7 bDst (base + 92))

/-- Program form of two adjacent MLOAD output limbs. -/
def mloadTwoLimbsProg
    (addrReg byteReg accReg : Reg)
    (a0 a1 a2 a3 a4 a5 a6 a7 aDst : BitVec 12)
    (b0 b1 b2 b3 b4 b5 b6 b7 bDst : BitVec 12) : Program :=
  mloadOneLimbProg addrReg byteReg accReg
    a0 a1 a2 a3 a4 a5 a6 a7 aDst ;;
  mloadOneLimbProg addrReg byteReg accReg
    b0 b1 b2 b3 b4 b5 b6 b7 bDst

theorem mloadTwoLimbsCode_eq_ofProg
    (addrReg byteReg accReg : Reg)
    (a0 a1 a2 a3 a4 a5 a6 a7 aDst : BitVec 12)
    (b0 b1 b2 b3 b4 b5 b6 b7 bDst : BitVec 12)
    (base : Word) :
    mloadTwoLimbsCode addrReg byteReg accReg
      a0 a1 a2 a3 a4 a5 a6 a7 aDst
      b0 b1 b2 b3 b4 b5 b6 b7 bDst base =
    CodeReq.ofProg base
      (mloadTwoLimbsProg addrReg byteReg accReg
        a0 a1 a2 a3 a4 a5 a6 a7 aDst
        b0 b1 b2 b3 b4 b5 b6 b7 bDst) := by
  unfold mloadTwoLimbsCode mloadTwoLimbsProg
  rw [mloadOneLimbCode_eq_ofProg, mloadOneLimbCode_eq_ofProg]
  let p1 := mloadOneLimbProg addrReg byteReg accReg
    a0 a1 a2 a3 a4 a5 a6 a7 aDst
  let p2 := mloadOneLimbProg addrReg byteReg accReg
    b0 b1 b2 b3 b4 b5 b6 b7 bDst
  change (CodeReq.ofProg base p1).union (CodeReq.ofProg (base + 92) p2) =
    CodeReq.ofProg base (List.append p1 p2)
  rw [show base + 92 = base + BitVec.ofNat 64 (4 * p1.length) from by
    unfold p1 mloadOneLimbProg mloadBytePackEightProg LBU SLLI OR' SD single seq
    rfl]
  exact (@CodeReq.ofProg_append base p1 p2).symm

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
    (h_window : mloadAlignedLimbWindowOk addrPtr dwordAddr
      off0 off1 off2 off3 off4 off5 off6 off7) :
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
    h_byte_ne_x0 h_acc_ne_x0 h_window
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

/-- Migration sibling of `mload_one_limb_spec_within` that takes the new
    `mloadAlignedDwordIs` wrapper assertion (PR #2284) in its precondition
    instead of an explicit `h_window` hypothesis. The
    `mloadAlignedLimbWindowOk` bundle is now bundled into the assertion via
    `⌜·⌝`, and the canonical `dwordAddr ↦ₘ wordVal` cell from the original
    pre is replaced by the wrapper. Proved by reducing to the original spec
    via AC-rewrite of the precondition followed by
    `cpsTripleWithin_of_pure_imp` to peel the bundled fact and feed it as
    `h_window` to the original spec.

    Second consumer-family migration of slice 3 of `evm-asm-8xc6`
    (GH #2278). Mirrors `mload_byte_pack_eight_via_assertion_spec_within`
    (PR #2340). Distinctive token:
    `mloadAlignedLimbWindowOk-consumer-migration-2278 one_limb via_assertion`. -/
theorem mload_one_limb_via_assertion_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld wordVal sp dstWordOld : Word)
    (dwordAddr : Word)
    (off0 off1 off2 off3 off4 off5 off6 off7 dstOff : BitVec 12) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0  : accReg  ≠ .x0) :
    cpsTripleWithin 23 base (base + 92)
      (mloadOneLimbCode addrReg byteReg accReg
        off0 off1 off2 off3 off4 off5 off6 off7 dstOff base)
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (mloadAlignedDwordIs addrPtr dwordAddr wordVal
          off0 off1 off2 off3 off4 off5 off6 off7) **
       ((.x12 : Reg) ↦ᵣ sp) **
       ((sp + signExtend12 dstOff) ↦ₘ dstWordOld))
      (mloadOneLimbPost addrReg byteReg accReg
        addrPtr wordVal dwordAddr sp
        off0 off1 off2 off3 off4 off5 off6 off7 dstOff) := by
  unfold mloadAlignedDwordIs
  -- AC-rearrange the precondition into `<original-pre> ** ⌜fact⌝` shape so
  -- `cpsTripleWithin_of_pure_imp` can peel the bundled `mloadAligned-
  -- LimbWindowOk` fact.
  have hpre_eq :
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
        ((dwordAddr ↦ₘ wordVal) **
          ⌜mloadAlignedLimbWindowOk addrPtr dwordAddr
              off0 off1 off2 off3 off4 off5 off6 off7⌝) **
        ((.x12 : Reg) ↦ᵣ sp) **
        ((sp + signExtend12 dstOff) ↦ₘ dstWordOld)) =
      (((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (dwordAddr ↦ₘ wordVal) ** ((.x12 : Reg) ↦ᵣ sp) **
         ((sp + signExtend12 dstOff) ↦ₘ dstWordOld)) **
        ⌜mloadAlignedLimbWindowOk addrPtr dwordAddr
            off0 off1 off2 off3 off4 off5 off6 off7⌝) := by
    ac_rfl
  rw [hpre_eq]
  refine cpsTripleWithin_of_pure_imp (fun h_window => ?_)
  have base_spec := mload_one_limb_spec_within addrReg byteReg accReg
    addrPtr accOld byteOld wordVal sp dstWordOld dwordAddr
    off0 off1 off2 off3 off4 off5 off6 off7 dstOff base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  rw [mloadOneLimbPre_unfold] at base_spec
  exact base_spec

end EvmAsm.Evm64
