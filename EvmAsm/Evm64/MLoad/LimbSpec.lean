/-
  EvmAsm.Evm64.MLoad.LimbSpec

  Per-byte spec for the MLOAD per-limb byte-pack loop.

  This sub-slice (#99 slice 3c, beads `evm-asm-8dk7`) lands the level-1
  building block of the MLOAD three-tier proof architecture
  (`docs/99-mload-design.md` §5): a `cpsTripleWithin` spec for the
  3-instruction `LBU + SLLI + OR` triple that folds one byte from EVM
  memory into the running 64-bit accumulator.

  The next sub-slice (#99 slice 3d) composes 8 of these per limb (plus a
  final `SD`) to obtain `mload_one_limb_spec_within`; that step also
  consumes `bytePack8_eq` from `Evm64/MLoad/ByteAlg.lean` to bridge the
  runtime shift-OR chain to a single big-endian-concatenated 64-bit
  value.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.MLoad.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Per-byte byte-pack step spec (3 instructions): `LBU byteReg addrReg
    offset`, `SLLI accReg accReg 8`, `OR accReg accReg byteReg`.

    Loads one byte from `addrReg + offset` (zero-extended to 64 bits),
    left-shifts the running accumulator by 8, and ORs the new byte into
    the low 8 bits. The byte and accumulator registers are completely
    rewritten; the address register and the source memory dword are
    unchanged.

    All three roles (`addrReg`, `byteReg`, `accReg`) must be distinct
    and non-`x0`. The byte address must be byte-access valid and align to
    `dwordAddr`, where `wordVal` is the source dword's contents.

    This is the analogue of `EvmAsm.Evm64.push_one_byte_spec_within` for
    MLOAD and is the level-1 building block of the three-tier MLOAD
    proof architecture (`docs/99-mload-design.md` §5). -/
theorem mload_byte_pack_step_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld wordVal : Word)
    (dwordAddr : Word)
    (offset : BitVec 12) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0  : accReg  ≠ .x0)
    (h_align : alignToDword (addrPtr + signExtend12 offset) = dwordAddr)
    (h_valid : isValidByteAccess (addrPtr + signExtend12 offset) = true) :
    let byteZext :=
      (extractByte wordVal (byteOffset (addrPtr + signExtend12 offset))).zeroExtend 64
    let accNew := (accOld <<< (8 : Nat)) ||| byteZext
    let cr :=
      (CodeReq.singleton base (.LBU byteReg addrReg offset)).union
        ((CodeReq.singleton (base + 4) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
         (CodeReq.singleton (base + 8) (.OR accReg accReg byteReg)))
    cpsTripleWithin 3 base (base + 12) cr
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (dwordAddr ↦ₘ wordVal))
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteZext) ** (accReg ↦ᵣ accNew) **
       (dwordAddr ↦ₘ wordVal)) := by
  intro byteZext accNew cr
  have L := lbu_spec_gen_within byteReg addrReg addrPtr byteOld offset base
              dwordAddr wordVal h_byte_ne_x0 h_align h_valid
  have I := slli_spec_gen_same_within accReg accOld (BitVec.ofNat 6 8) (base + 4) h_acc_ne_x0
  have O := or_spec_gen_rd_eq_rs1_within accReg byteReg (accOld <<< (8 : Nat)) byteZext
              (base + 8) h_acc_ne_x0
  -- `(BitVec.ofNat 6 8).toNat = 8` definitionally; rewrite the SLLI post
  -- so it matches the OR pre.
  have h8 : ((BitVec.ofNat 6 8 : BitVec 6).toNat) = 8 := by decide
  rw [h8] at I
  runBlock L I O

/-- Bundled CodeReq for `mload_byte_pack_two_spec_within`: a 4-instruction
    union covering the seed `LBU` at `base`, the inner-byte `LBU` at
    `base + 4`, and the `SLLI`/`OR` byte-pack pair at `base + 8` /
    `base + 12`.

    Pulled out of the spec body (per @pirapira review on PR #1659) so the
    code requirement is a named handle that callers and downstream
    composition lemmas can refer to without re-spelling the union. -/
def mloadBytePackTwoCode
    (addrReg byteReg accReg : Reg) (off0 off1 : BitVec 12) (base : Word) :
    CodeReq :=
  (CodeReq.singleton base (.LBU accReg addrReg off0)).union
    ((CodeReq.singleton (base + 4) (.LBU byteReg addrReg off1)).union
     ((CodeReq.singleton (base + 8) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
      (CodeReq.singleton (base + 12) (.OR accReg accReg byteReg))))

/-- Two-byte big-endian byte-pack spec (4 instructions): seed `LBU`
    loading `b0` into `accReg`, followed by one
    `mload_byte_pack_step_spec_within` triple loading `b1` and folding it
    in via `(b0 <<< 8) ||| b1`.

    This is the smallest non-trivial composition exercising the seed-LBU
    + per-byte-pack-step shape. It scales by induction to the full
    8-byte limb spec (`mload_one_limb_spec_within`, beads
    `evm-asm-h9e8`) and ultimately to `evm_mload_stack_spec_within`
    (slice 3e). Establishing the pattern here keeps each composition
    step well-typed and lets later slices reuse the same skeleton.

    Both source bytes live in the same source dwordAddr; the caller
    supplies one `(alignToDword, isValidByteAccess)` pair per byte. -/
theorem mload_byte_pack_two_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld wordVal : Word)
    (dwordAddr : Word)
    (off0 off1 : BitVec 12) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0  : accReg  ≠ .x0)
    (h_align0 : alignToDword (addrPtr + signExtend12 off0) = dwordAddr)
    (h_valid0 : isValidByteAccess (addrPtr + signExtend12 off0) = true)
    (h_align1 : alignToDword (addrPtr + signExtend12 off1) = dwordAddr)
    (h_valid1 : isValidByteAccess (addrPtr + signExtend12 off1) = true) :
    let b0 :=
      (extractByte wordVal (byteOffset (addrPtr + signExtend12 off0))).zeroExtend 64
    let b1 :=
      (extractByte wordVal (byteOffset (addrPtr + signExtend12 off1))).zeroExtend 64
    let accFinal := (b0 <<< (8 : Nat)) ||| b1
    let cr := mloadBytePackTwoCode addrReg byteReg accReg off0 off1 base
    cpsTripleWithin 4 base (base + 16) cr
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (dwordAddr ↦ₘ wordVal))
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b1) ** (accReg ↦ᵣ accFinal) **
       (dwordAddr ↦ₘ wordVal)) := by
  intro b0 b1 accFinal cr
  -- Step 1: seed LBU (loads `b0` into `accReg`). Frame in `byteReg ↦ᵣ
  -- byteOld` so the post matches the pre of the byte-pack-step triple.
  have lbu0Raw := lbu_spec_gen_within accReg addrReg addrPtr accOld
    off0 base dwordAddr wordVal h_acc_ne_x0 h_align0 h_valid0
  have lbu0Framed := cpsTripleWithin_frameR (byteReg ↦ᵣ byteOld)
    (by pcFree) lbu0Raw
  -- Permute pre/post to canonical 4-atom shape
  -- `addrReg ** byteReg ** accReg ** mem`.
  have s1 : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU accReg addrReg off0))
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (dwordAddr ↦ₘ wordVal))
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ b0) **
       (dwordAddr ↦ₘ wordVal)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp) lbu0Framed
  -- Step 2: 3-instruction byte-pack triple at `base + 4`. Specialising
  -- `accOld := b0` makes its post equal `(b0 <<< 8) ||| b1 = accFinal`.
  have step := mload_byte_pack_step_spec_within addrReg byteReg accReg
    addrPtr b0 byteOld wordVal dwordAddr off1 (base + 4)
    h_byte_ne_x0 h_acc_ne_x0 h_align1 h_valid1
  -- The `step`'s exit address is `(base + 4) + 12 = base + 16`.
  rw [show (base + 4 : Word) + 12 = base + 16 from by bv_omega] at step
  -- Also normalize the `step`'s code-req sub-addresses so they match
  -- the `cr` shape (`base + 4`, `base + 8`, `base + 12`).
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega,
      show (base + 4 : Word) + 8 = base + 12 from by bv_omega] at step
  -- Disjointness of the seed LBU code-req with the triple's union-of-3.
  -- Distinct addresses base, base+4, base+8, base+12.
  have h01 : base ≠ base + 4 := by bv_omega
  have h02 : base ≠ base + 8 := by bv_omega
  have h03 : base ≠ base + 12 := by bv_omega
  have hd_step : CodeReq.Disjoint
      (CodeReq.singleton base (.LBU accReg addrReg off0))
      ((CodeReq.singleton (base + 4) (.LBU byteReg addrReg off1)).union
       ((CodeReq.singleton (base + 8) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
        (CodeReq.singleton (base + 12) (.OR accReg accReg byteReg)))) :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton h01)
      (CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton h02)
        (CodeReq.Disjoint.singleton h03))
  exact cpsTripleWithin_seq hd_step s1 step

/-- Bundled CodeReq for `mload_byte_pack_three_spec_within`: a 7-instruction
    union extending `mloadBytePackTwoCode` with one additional
    `LBU/SLLI/OR` triple at `base + 16 / base + 20 / base + 24` for the
    third byte.

    Pulled out of the spec body (mirroring the slice-3d-prep convention
    @pirapira asked for on PR #1659) so the code requirement is a named
    handle that callers and downstream composition lemmas can refer to
    without re-spelling the union. -/
def mloadBytePackThreeCode
    (addrReg byteReg accReg : Reg) (off0 off1 off2 : BitVec 12) (base : Word) :
    CodeReq :=
  (mloadBytePackTwoCode addrReg byteReg accReg off0 off1 base).union
    ((CodeReq.singleton (base + 16) (.LBU byteReg addrReg off2)).union
     ((CodeReq.singleton (base + 20) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
      (CodeReq.singleton (base + 24) (.OR accReg accReg byteReg))))

/-- Bundled precondition for `mload_byte_pack_three_spec_within`: the
    three roles `addrReg ↦ᵣ addrPtr`, `byteReg ↦ᵣ byteOld`,
    `accReg ↦ᵣ accOld`, plus the source dword `dwordAddr ↦ₘ wordVal`.

    Pulled into an `@[irreducible]` definition (per @pirapira review on
    PR #1674) so the spec statement is not cluttered by a long chain of
    `let`-bindings; downstream callers see a single named handle and
    use `mloadBytePackThreePre_unfold` to expand on demand. -/
@[irreducible]
def mloadBytePackThreePre
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld wordVal dwordAddr : Word) : Assertion :=
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
  (dwordAddr ↦ₘ wordVal)

theorem mloadBytePackThreePre_unfold
    {addrReg byteReg accReg : Reg}
    {addrPtr accOld byteOld wordVal dwordAddr : Word} :
    mloadBytePackThreePre addrReg byteReg accReg
        addrPtr accOld byteOld wordVal dwordAddr =
    ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
     (dwordAddr ↦ₘ wordVal)) := by
  delta mloadBytePackThreePre; rfl

/-- Bundled postcondition for `mload_byte_pack_three_spec_within`: after
    the 7-instruction sequence, `byteReg` holds the last byte loaded
    (`b2`) and `accReg` holds the big-endian fold
    `((b0 <<< 8) ||| b1) <<< 8 ||| b2`.

    Pulled into an `@[irreducible]` definition (per @pirapira review on
    PR #1674) so the byte-extraction `let`-chain is hidden inside this
    handle rather than spelled out in the spec statement. Use
    `mloadBytePackThreePost_unfold` to expose the underlying atomic
    `**`-shape when composing further. -/
@[irreducible]
def mloadBytePackThreePost
    (addrReg byteReg accReg : Reg)
    (addrPtr wordVal dwordAddr : Word)
    (off0 off1 off2 : BitVec 12) : Assertion :=
  let b0 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off0))).zeroExtend 64
  let b1 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off1))).zeroExtend 64
  let b2 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off2))).zeroExtend 64
  let accFinal := (((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b2) ** (accReg ↦ᵣ accFinal) **
  (dwordAddr ↦ₘ wordVal)

theorem mloadBytePackThreePost_unfold
    {addrReg byteReg accReg : Reg}
    {addrPtr wordVal dwordAddr : Word}
    {off0 off1 off2 : BitVec 12} :
    mloadBytePackThreePost addrReg byteReg accReg
        addrPtr wordVal dwordAddr off0 off1 off2 =
    (let b0 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off0))).zeroExtend 64
     let b1 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off1))).zeroExtend 64
     let b2 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off2))).zeroExtend 64
     let accFinal := (((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2
     (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b2) ** (accReg ↦ᵣ accFinal) **
     (dwordAddr ↦ₘ wordVal)) := by
  delta mloadBytePackThreePost; rfl

/-- Three-byte big-endian byte-pack spec (7 instructions): seed `LBU`
    loading `b0`, then two `LBU + SLLI + OR` triples folding `b1` and
    `b2` in big-endian order, yielding
    `((b0 <<< 8) ||| b1) <<< 8 ||| b2` in `accReg`.

    This is the `n = 3` step in the inductive ladder
    `mload_byte_pack_init` (n=1) → `mload_byte_pack_two` (n=2) →
    `mload_byte_pack_three` (n=3) → … → `mload_one_limb` (n=8). It is
    proved by composing the existing 2-byte spec with one
    `mload_byte_pack_step_spec_within` application; no new tactic
    machinery is needed.

    All three bytes live in the same source `dwordAddr`; the caller
    supplies one `(alignToDword, isValidByteAccess)` pair per byte.

    Pre/post are bundled as `@[irreducible]` definitions
    (`mloadBytePackThreePre`, `mloadBytePackThreePost`) so the spec
    statement does not carry a `let`-chain over `b0/b1/b2/accFinal`;
    callers compose against the named handles and unfold via the
    `_unfold` lemmas only when they need atomic access.

    NOTE: the beads task `evm-asm-svpr` titled this slice "5-instr
    3-byte pattern", but the natural composition (reusing the
    seed-LBU + per-byte-pack-step shape established in slice 3d-prep)
    is 7 instructions: 1 seed LBU + 2 × (LBU + SLLI + OR). -/
theorem mload_byte_pack_three_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld wordVal : Word)
    (dwordAddr : Word)
    (off0 off1 off2 : BitVec 12) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0  : accReg  ≠ .x0)
    (h_align0 : alignToDword (addrPtr + signExtend12 off0) = dwordAddr)
    (h_valid0 : isValidByteAccess (addrPtr + signExtend12 off0) = true)
    (h_align1 : alignToDword (addrPtr + signExtend12 off1) = dwordAddr)
    (h_valid1 : isValidByteAccess (addrPtr + signExtend12 off1) = true)
    (h_align2 : alignToDword (addrPtr + signExtend12 off2) = dwordAddr)
    (h_valid2 : isValidByteAccess (addrPtr + signExtend12 off2) = true) :
    cpsTripleWithin 7 base (base + 28)
      (mloadBytePackThreeCode addrReg byteReg accReg off0 off1 off2 base)
      (mloadBytePackThreePre addrReg byteReg accReg
        addrPtr accOld byteOld wordVal dwordAddr)
      (mloadBytePackThreePost addrReg byteReg accReg
        addrPtr wordVal dwordAddr off0 off1 off2) := by
  rw [mloadBytePackThreePre_unfold, mloadBytePackThreePost_unfold]
  set b0 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off0))).zeroExtend 64
  set b1 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off1))).zeroExtend 64
  set b2 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off2))).zeroExtend 64
  set accAfter2 := (b0 <<< (8 : Nat)) ||| b1 with h_accAfter2
  set accFinal := (accAfter2 <<< (8 : Nat)) ||| b2
  set cr := mloadBytePackThreeCode addrReg byteReg accReg off0 off1 off2 base
  -- Step 1: 4-instruction 2-byte spec at `base`.
  have two := mload_byte_pack_two_spec_within addrReg byteReg accReg
    addrPtr accOld byteOld wordVal dwordAddr off0 off1 base
    h_byte_ne_x0 h_acc_ne_x0 h_align0 h_valid0 h_align1 h_valid1
  -- Step 2: 3-instruction byte-pack triple at `base + 16` folding `b2`.
  -- Specialising `accOld := accAfter2` makes its post equal
  -- `(accAfter2 <<< 8) ||| b2 = accFinal`. The `byteOld` slot of `step`
  -- is filled with `b1` (the trailing byte left in `byteReg` by `two`).
  have step := mload_byte_pack_step_spec_within addrReg byteReg accReg
    addrPtr accAfter2 b1 wordVal dwordAddr off2 (base + 16)
    h_byte_ne_x0 h_acc_ne_x0 h_align2 h_valid2
  -- Normalise the `step`'s exit and code-req sub-addresses so they
  -- match the `cr` shape.
  rw [show (base + 16 : Word) + 12 = base + 28 from by bv_omega] at step
  rw [show (base + 16 : Word) + 4 = base + 20 from by bv_omega,
      show (base + 16 : Word) + 8 = base + 24 from by bv_omega] at step
  -- Disjointness between the two-byte block (addresses base, base+4,
  -- base+8, base+12) and the trailing triple (base+16, base+20,
  -- base+24).
  have h_b_b16  : base ≠ base + 16 := by bv_omega
  have h_b_b20  : base ≠ base + 20 := by bv_omega
  have h_b_b24  : base ≠ base + 24 := by bv_omega
  have h_b4_b16 : base + 4 ≠ base + 16 := by bv_omega
  have h_b4_b20 : base + 4 ≠ base + 20 := by bv_omega
  have h_b4_b24 : base + 4 ≠ base + 24 := by bv_omega
  have h_b8_b16 : base + 8 ≠ base + 16 := by bv_omega
  have h_b8_b20 : base + 8 ≠ base + 20 := by bv_omega
  have h_b8_b24 : base + 8 ≠ base + 24 := by bv_omega
  have h_b12_b16 : base + 12 ≠ base + 16 := by bv_omega
  have h_b12_b20 : base + 12 ≠ base + 20 := by bv_omega
  have h_b12_b24 : base + 12 ≠ base + 24 := by bv_omega
  -- Build the trailing triple's union and prove `mloadBytePackTwoCode`
  -- is disjoint from it.
  have hd_step : CodeReq.Disjoint
      (mloadBytePackTwoCode addrReg byteReg accReg off0 off1 base)
      ((CodeReq.singleton (base + 16) (.LBU byteReg addrReg off2)).union
       ((CodeReq.singleton (base + 20) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
        (CodeReq.singleton (base + 24) (.OR accReg accReg byteReg)))) := by
    unfold mloadBytePackTwoCode
    refine CodeReq.Disjoint.union_left ?_ (CodeReq.Disjoint.union_left ?_
      (CodeReq.Disjoint.union_left ?_ ?_))
    · refine CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h_b_b16) ?_
      exact CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h_b_b20)
        (CodeReq.Disjoint.singleton h_b_b24)
    · refine CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h_b4_b16) ?_
      exact CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h_b4_b20)
        (CodeReq.Disjoint.singleton h_b4_b24)
    · refine CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h_b8_b16) ?_
      exact CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h_b8_b20)
        (CodeReq.Disjoint.singleton h_b8_b24)
    · refine CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h_b12_b16) ?_
      exact CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h_b12_b20)
        (CodeReq.Disjoint.singleton h_b12_b24)
  exact cpsTripleWithin_seq hd_step two step

/-- Init step of the `mload_byte_pack` recursion: a single `LBU accReg
    addrReg offset` that loads the leading (most-significant) byte of a
    limb directly into `accReg`, with no shift/OR (since the accumulator
    is freshly overwritten).

    This is the level-1 base-case spec for sub-slice 3d
    (`mload_one_limb_spec_within`, `docs/99-mload-design.md` §6). The
    inductive step is `mload_byte_pack_step_spec_within` above. Together
    they let the limb-spec slice fold 1 init + 7 triples = 22 instructions
    into a single per-limb postcondition; the SD that closes the limb is
    then a one-instruction `sd_spec_gen_within` application.

    The address register and the source memory dword are unchanged; the
    accumulator and the byte register the spec mentions are limited to
    the accumulator only — the byte register is not used in this step,
    so it does not appear in the spec's footprint. -/
theorem mload_byte_pack_init_spec_within
    (addrReg accReg : Reg)
    (addrPtr accOld wordVal : Word)
    (dwordAddr : Word)
    (offset : BitVec 12) (base : Word)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_align : alignToDword (addrPtr + signExtend12 offset) = dwordAddr)
    (h_valid : isValidByteAccess (addrPtr + signExtend12 offset) = true) :
    let byteZext :=
      (extractByte wordVal (byteOffset (addrPtr + signExtend12 offset))).zeroExtend 64
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU accReg addrReg offset))
      ((addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ accOld) ** (dwordAddr ↦ₘ wordVal))
      ((addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ byteZext) ** (dwordAddr ↦ₘ wordVal)) := by
  intro byteZext
  exact lbu_spec_gen_within accReg addrReg addrPtr accOld offset base
    dwordAddr wordVal h_acc_ne_x0 h_align h_valid

/-- Bundled CodeReq for `mload_byte_pack_four_spec_within`: a 10-instruction
    union extending `mloadBytePackThreeCode` with one additional
    `LBU/SLLI/OR` triple at `base + 28 / base + 32 / base + 36` for the
    fourth byte. -/
def mloadBytePackFourCode
    (addrReg byteReg accReg : Reg) (off0 off1 off2 off3 : BitVec 12) (base : Word) :
    CodeReq :=
  (mloadBytePackThreeCode addrReg byteReg accReg off0 off1 off2 base).union
    ((CodeReq.singleton (base + 28) (.LBU byteReg addrReg off3)).union
     ((CodeReq.singleton (base + 32) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
      (CodeReq.singleton (base + 36) (.OR accReg accReg byteReg))))

/-- Bundled precondition for `mload_byte_pack_four_spec_within`: the
    three roles `addrReg ↦ᵣ addrPtr`, `byteReg ↦ᵣ byteOld`,
    `accReg ↦ᵣ accOld`, plus the source dword `dwordAddr ↦ₘ wordVal`.

    Pulled into an `@[irreducible]` definition (mirroring the slice 3d-pre2
    convention from PR #1674) so the spec statement is not cluttered by a
    long chain of `let`-bindings; downstream callers see a single named
    handle and use `mloadBytePackFourPre_unfold` to expand on demand. -/
@[irreducible]
def mloadBytePackFourPre
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld wordVal dwordAddr : Word) : Assertion :=
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
  (dwordAddr ↦ₘ wordVal)

theorem mloadBytePackFourPre_unfold
    {addrReg byteReg accReg : Reg}
    {addrPtr accOld byteOld wordVal dwordAddr : Word} :
    mloadBytePackFourPre addrReg byteReg accReg
        addrPtr accOld byteOld wordVal dwordAddr =
    ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
     (dwordAddr ↦ₘ wordVal)) := by
  delta mloadBytePackFourPre; rfl

/-- Bundled postcondition for `mload_byte_pack_four_spec_within`: after
    the 10-instruction sequence, `byteReg` holds the last byte loaded
    (`b3`) and `accReg` holds the big-endian fold
    `(((b0 <<< 8) ||| b1) <<< 8 ||| b2) <<< 8 ||| b3`. -/
@[irreducible]
def mloadBytePackFourPost
    (addrReg byteReg accReg : Reg)
    (addrPtr wordVal dwordAddr : Word)
    (off0 off1 off2 off3 : BitVec 12) : Assertion :=
  let b0 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off0))).zeroExtend 64
  let b1 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off1))).zeroExtend 64
  let b2 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off2))).zeroExtend 64
  let b3 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off3))).zeroExtend 64
  let accFinal :=
    ((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b3) ** (accReg ↦ᵣ accFinal) **
  (dwordAddr ↦ₘ wordVal)

theorem mloadBytePackFourPost_unfold
    {addrReg byteReg accReg : Reg}
    {addrPtr wordVal dwordAddr : Word}
    {off0 off1 off2 off3 : BitVec 12} :
    mloadBytePackFourPost addrReg byteReg accReg
        addrPtr wordVal dwordAddr off0 off1 off2 off3 =
    (let b0 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off0))).zeroExtend 64
     let b1 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off1))).zeroExtend 64
     let b2 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off2))).zeroExtend 64
     let b3 :=
       (extractByte wordVal (byteOffset (addrPtr + signExtend12 off3))).zeroExtend 64
     let accFinal :=
       ((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3
     (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b3) ** (accReg ↦ᵣ accFinal) **
     (dwordAddr ↦ₘ wordVal)) := by
  delta mloadBytePackFourPost; rfl

/-- Four-byte big-endian byte-pack spec (10 instructions): seed `LBU`
    loading `b0`, then three `LBU + SLLI + OR` triples folding `b1`, `b2`,
    `b3` in big-endian order, yielding
    `(((b0 <<< 8) ||| b1) <<< 8 ||| b2) <<< 8 ||| b3` in `accReg`.

    This is the `n = 4` step in the inductive ladder
    `mload_byte_pack_init` (n=1) → `mload_byte_pack_two` (n=2) →
    `mload_byte_pack_three` (n=3) → `mload_byte_pack_four` (n=4) → … →
    `mload_one_limb` (n=8). It is proved by composing the existing 3-byte
    spec with one `mload_byte_pack_step_spec_within` application; no new
    tactic machinery is needed. -/
theorem mload_byte_pack_four_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld wordVal : Word)
    (dwordAddr : Word)
    (off0 off1 off2 off3 : BitVec 12) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0  : accReg  ≠ .x0)
    (h_align0 : alignToDword (addrPtr + signExtend12 off0) = dwordAddr)
    (h_valid0 : isValidByteAccess (addrPtr + signExtend12 off0) = true)
    (h_align1 : alignToDword (addrPtr + signExtend12 off1) = dwordAddr)
    (h_valid1 : isValidByteAccess (addrPtr + signExtend12 off1) = true)
    (h_align2 : alignToDword (addrPtr + signExtend12 off2) = dwordAddr)
    (h_valid2 : isValidByteAccess (addrPtr + signExtend12 off2) = true)
    (h_align3 : alignToDword (addrPtr + signExtend12 off3) = dwordAddr)
    (h_valid3 : isValidByteAccess (addrPtr + signExtend12 off3) = true) :
    cpsTripleWithin 10 base (base + 40)
      (mloadBytePackFourCode addrReg byteReg accReg off0 off1 off2 off3 base)
      (mloadBytePackFourPre addrReg byteReg accReg
        addrPtr accOld byteOld wordVal dwordAddr)
      (mloadBytePackFourPost addrReg byteReg accReg
        addrPtr wordVal dwordAddr off0 off1 off2 off3) := by
  rw [mloadBytePackFourPre_unfold, mloadBytePackFourPost_unfold]
  set b0 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off0))).zeroExtend 64
  set b1 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off1))).zeroExtend 64
  set b2 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off2))).zeroExtend 64
  set b3 :=
    (extractByte wordVal (byteOffset (addrPtr + signExtend12 off3))).zeroExtend 64
  set accAfter3 := (((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2 with h_accAfter3
  set accFinal := (accAfter3 <<< (8 : Nat)) ||| b3
  -- Step 1: 7-instruction 3-byte spec at `base`. Unfold its bundled
  -- pre/post into atomic shapes that match what `cpsTripleWithin_seq`
  -- expects when paired with the trailing triple.
  have threeRaw := mload_byte_pack_three_spec_within addrReg byteReg accReg
    addrPtr accOld byteOld wordVal dwordAddr off0 off1 off2 base
    h_byte_ne_x0 h_acc_ne_x0 h_align0 h_valid0 h_align1 h_valid1
    h_align2 h_valid2
  rw [mloadBytePackThreePre_unfold, mloadBytePackThreePost_unfold] at threeRaw
  -- Step 2: 3-instruction byte-pack triple at `base + 28` folding `b3`.
  -- Specialising `accOld := accAfter3` makes its post equal
  -- `(accAfter3 <<< 8) ||| b3 = accFinal`.
  have step := mload_byte_pack_step_spec_within addrReg byteReg accReg
    addrPtr accAfter3 b2 wordVal dwordAddr off3 (base + 28)
    h_byte_ne_x0 h_acc_ne_x0 h_align3 h_valid3
  rw [show (base + 28 : Word) + 12 = base + 40 from by bv_omega] at step
  rw [show (base + 28 : Word) + 4 = base + 32 from by bv_omega,
      show (base + 28 : Word) + 8 = base + 36 from by bv_omega] at step
  -- Disjointness between the three-byte block (addresses base, base+4,
  -- base+8, base+12, base+16, base+20, base+24) and the trailing triple
  -- (base+28, base+32, base+36).
  have h_b_b28   : base ≠ base + 28 := by bv_omega
  have h_b_b32   : base ≠ base + 32 := by bv_omega
  have h_b_b36   : base ≠ base + 36 := by bv_omega
  have h_b4_b28  : base + 4  ≠ base + 28 := by bv_omega
  have h_b4_b32  : base + 4  ≠ base + 32 := by bv_omega
  have h_b4_b36  : base + 4  ≠ base + 36 := by bv_omega
  have h_b8_b28  : base + 8  ≠ base + 28 := by bv_omega
  have h_b8_b32  : base + 8  ≠ base + 32 := by bv_omega
  have h_b8_b36  : base + 8  ≠ base + 36 := by bv_omega
  have h_b12_b28 : base + 12 ≠ base + 28 := by bv_omega
  have h_b12_b32 : base + 12 ≠ base + 32 := by bv_omega
  have h_b12_b36 : base + 12 ≠ base + 36 := by bv_omega
  have h_b16_b28 : base + 16 ≠ base + 28 := by bv_omega
  have h_b16_b32 : base + 16 ≠ base + 32 := by bv_omega
  have h_b16_b36 : base + 16 ≠ base + 36 := by bv_omega
  have h_b20_b28 : base + 20 ≠ base + 28 := by bv_omega
  have h_b20_b32 : base + 20 ≠ base + 32 := by bv_omega
  have h_b20_b36 : base + 20 ≠ base + 36 := by bv_omega
  have h_b24_b28 : base + 24 ≠ base + 28 := by bv_omega
  have h_b24_b32 : base + 24 ≠ base + 32 := by bv_omega
  have h_b24_b36 : base + 24 ≠ base + 36 := by bv_omega
  -- Build the trailing triple's union and prove `mloadBytePackThreeCode`
  -- is disjoint from it.
  have hd_step : CodeReq.Disjoint
      (mloadBytePackThreeCode addrReg byteReg accReg off0 off1 off2 base)
      ((CodeReq.singleton (base + 28) (.LBU byteReg addrReg off3)).union
       ((CodeReq.singleton (base + 32) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
        (CodeReq.singleton (base + 36) (.OR accReg accReg byteReg)))) := by
    unfold mloadBytePackThreeCode mloadBytePackTwoCode
    -- Helper: each leaf address (base, base+4, …, base+24) is disjoint
    -- from the trailing triple at (base+28, base+32, base+36). The
    -- instruction stored at `a` is generic; only the address inequalities
    -- feed `CodeReq.Disjoint.singleton`.
    have leaf : ∀ {a : Word} {i : Instr},
        a ≠ base + 28 → a ≠ base + 32 → a ≠ base + 36 →
        CodeReq.Disjoint (CodeReq.singleton a i)
            ((CodeReq.singleton (base + 28) (.LBU byteReg addrReg off3)).union
             ((CodeReq.singleton (base + 32) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
              (CodeReq.singleton (base + 36) (.OR accReg accReg byteReg)))) := by
      intro a i h28 h32 h36
      exact CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton h28)
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.singleton h32)
          (CodeReq.Disjoint.singleton h36))
    -- Top split: twoCode-block ∪ trailing-trio-of-three vs. trailing triple.
    refine CodeReq.Disjoint.union_left ?_ ?_
    · -- twoCode: 4 right-associated leaves (base, base+4, base+8, base+12)
      refine CodeReq.Disjoint.union_left (leaf h_b_b28 h_b_b32 h_b_b36) ?_
      refine CodeReq.Disjoint.union_left (leaf h_b4_b28 h_b4_b32 h_b4_b36) ?_
      refine CodeReq.Disjoint.union_left (leaf h_b8_b28 h_b8_b32 h_b8_b36) ?_
      exact leaf h_b12_b28 h_b12_b32 h_b12_b36
    · -- trailing trio of three (base+16, base+20, base+24)
      refine CodeReq.Disjoint.union_left (leaf h_b16_b28 h_b16_b32 h_b16_b36) ?_
      refine CodeReq.Disjoint.union_left (leaf h_b20_b28 h_b20_b32 h_b20_b36) ?_
      exact leaf h_b24_b28 h_b24_b32 h_b24_b36
  -- The final code-req shape is `mloadBytePackFourCode = three.union triple`.
  -- `cpsTripleWithin_seq` produces exactly that union.
  exact cpsTripleWithin_seq hd_step threeRaw step

/-- Bundled CodeReq for `mload_byte_pack_five_spec_within`: a 13-instruction
    union extending `mloadBytePackFourCode` with one additional
    `LBU/SLLI/OR` triple at `base + 40 / base + 44 / base + 48` for the
    fifth byte. -/
def mloadBytePackFiveCode
    (addrReg byteReg accReg : Reg) (off0 off1 off2 off3 off4 : BitVec 12)
    (base : Word) : CodeReq :=
  (mloadBytePackFourCode addrReg byteReg accReg off0 off1 off2 off3 base).union
    ((CodeReq.singleton (base + 40) (.LBU byteReg addrReg off4)).union
     ((CodeReq.singleton (base + 44) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
      (CodeReq.singleton (base + 48) (.OR accReg accReg byteReg))))

/-- Bundled precondition for `mload_byte_pack_five_spec_within`: the
    three roles `addrReg ↦ᵣ addrPtr`, `byteReg ↦ᵣ byteOld`,
    `accReg ↦ᵣ accOld`, plus the source dword `dwordAddr ↦ₘ wordVal`.

    Pulled into an `@[irreducible]` definition (mirroring the slice 3d-pre3
    convention from PR #1690) so the spec statement is not cluttered by a
    long chain of `let`-bindings; downstream callers see a single named
    handle and use `mloadBytePackFivePre_unfold` to expand on demand. -/
@[irreducible]
def mloadBytePackFivePre
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld wordVal dwordAddr : Word) : Assertion :=
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
  (dwordAddr ↦ₘ wordVal)

theorem mloadBytePackFivePre_unfold
    {addrReg byteReg accReg : Reg}
    {addrPtr accOld byteOld wordVal dwordAddr : Word} :
    mloadBytePackFivePre addrReg byteReg accReg
        addrPtr accOld byteOld wordVal dwordAddr =
    ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
     (dwordAddr ↦ₘ wordVal)) := by
  delta mloadBytePackFivePre; rfl

/-- Bundled postcondition for `mload_byte_pack_five_spec_within`: after
    the 13-instruction sequence, `byteReg` holds the last byte loaded
    (`b4`) and `accReg` holds the big-endian fold
    `((((b0 <<< 8) ||| b1) <<< 8 ||| b2) <<< 8 ||| b3) <<< 8 ||| b4`. -/
@[irreducible]
def mloadBytePackFivePost
    (addrReg byteReg accReg : Reg)
    (addrPtr wordVal dwordAddr : Word)
    (off0 off1 off2 off3 off4 : BitVec 12) : Assertion :=
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
  let accFinal :=
    (((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3)
      <<< (8 : Nat) ||| b4
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b4) ** (accReg ↦ᵣ accFinal) **
  (dwordAddr ↦ₘ wordVal)

theorem mloadBytePackFivePost_unfold
    {addrReg byteReg accReg : Reg}
    {addrPtr wordVal dwordAddr : Word}
    {off0 off1 off2 off3 off4 : BitVec 12} :
    mloadBytePackFivePost addrReg byteReg accReg
        addrPtr wordVal dwordAddr off0 off1 off2 off3 off4 =
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
     let accFinal :=
       (((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3)
         <<< (8 : Nat) ||| b4
     (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b4) ** (accReg ↦ᵣ accFinal) **
     (dwordAddr ↦ₘ wordVal)) := by
  delta mloadBytePackFivePost; rfl

/-- Five-byte big-endian byte-pack spec (13 instructions): seed `LBU`
    loading `b0`, then four `LBU + SLLI + OR` triples folding `b1`, `b2`,
    `b3`, `b4` in big-endian order, yielding
    `((((b0 <<< 8) ||| b1) <<< 8 ||| b2) <<< 8 ||| b3) <<< 8 ||| b4` in
    `accReg`.

    This is the `n = 5` step in the inductive ladder
    `mload_byte_pack_init` (n=1) → `mload_byte_pack_two` (n=2) →
    `mload_byte_pack_three` (n=3) → `mload_byte_pack_four` (n=4) →
    `mload_byte_pack_five` (n=5) → … → `mload_one_limb` (n=8). It is
    proved by composing the existing 4-byte spec (PR #1690) with one
    `mload_byte_pack_step_spec_within` application; no new tactic
    machinery is needed. -/
theorem mload_byte_pack_five_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld wordVal : Word)
    (dwordAddr : Word)
    (off0 off1 off2 off3 off4 : BitVec 12) (base : Word)
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
    (h_valid4 : isValidByteAccess (addrPtr + signExtend12 off4) = true) :
    cpsTripleWithin 13 base (base + 52)
      (mloadBytePackFiveCode addrReg byteReg accReg off0 off1 off2 off3 off4 base)
      (mloadBytePackFivePre addrReg byteReg accReg
        addrPtr accOld byteOld wordVal dwordAddr)
      (mloadBytePackFivePost addrReg byteReg accReg
        addrPtr wordVal dwordAddr off0 off1 off2 off3 off4) := by
  rw [mloadBytePackFivePre_unfold, mloadBytePackFivePost_unfold]
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
  set accAfter4 :=
    ((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3
    with h_accAfter4
  set accFinal := (accAfter4 <<< (8 : Nat)) ||| b4
  -- Step 1: 10-instruction 4-byte spec at `base`. Unfold its bundled
  -- pre/post into atomic shapes that match what `cpsTripleWithin_seq`
  -- expects when paired with the trailing triple.
  have fourRaw := mload_byte_pack_four_spec_within addrReg byteReg accReg
    addrPtr accOld byteOld wordVal dwordAddr off0 off1 off2 off3 base
    h_byte_ne_x0 h_acc_ne_x0 h_align0 h_valid0 h_align1 h_valid1
    h_align2 h_valid2 h_align3 h_valid3
  rw [mloadBytePackFourPre_unfold, mloadBytePackFourPost_unfold] at fourRaw
  -- Step 2: 3-instruction byte-pack triple at `base + 40` folding `b4`.
  -- Specialising `accOld := accAfter4` makes its post equal
  -- `(accAfter4 <<< 8) ||| b4 = accFinal`.
  have step := mload_byte_pack_step_spec_within addrReg byteReg accReg
    addrPtr accAfter4 b3 wordVal dwordAddr off4 (base + 40)
    h_byte_ne_x0 h_acc_ne_x0 h_align4 h_valid4
  rw [show (base + 40 : Word) + 12 = base + 52 from by bv_omega] at step
  rw [show (base + 40 : Word) + 4 = base + 44 from by bv_omega,
      show (base + 40 : Word) + 8 = base + 48 from by bv_omega] at step
  -- Disjointness between the four-byte block (addresses base, base+4,
  -- base+8, …, base+36) and the trailing triple (base+40, base+44,
  -- base+48). Use the same `leaf` helper pattern as the 4-byte slice:
  -- one address inequality triple per leaf instruction in the prefix.
  have hd_step : CodeReq.Disjoint
      (mloadBytePackFourCode addrReg byteReg accReg off0 off1 off2 off3 base)
      ((CodeReq.singleton (base + 40) (.LBU byteReg addrReg off4)).union
       ((CodeReq.singleton (base + 44) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
        (CodeReq.singleton (base + 48) (.OR accReg accReg byteReg)))) := by
    unfold mloadBytePackFourCode mloadBytePackThreeCode mloadBytePackTwoCode
    -- Helper: each leaf address `a ∈ {base, base+4, …, base+36}` is
    -- disjoint from the trailing triple at (base+40, base+44, base+48).
    have leaf : ∀ {a : Word} {i : Instr},
        a ≠ base + 40 → a ≠ base + 44 → a ≠ base + 48 →
        CodeReq.Disjoint (CodeReq.singleton a i)
            ((CodeReq.singleton (base + 40) (.LBU byteReg addrReg off4)).union
             ((CodeReq.singleton (base + 44) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
              (CodeReq.singleton (base + 48) (.OR accReg accReg byteReg)))) := by
      intro a i h40 h44 h48
      exact CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton h40)
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.singleton h44)
          (CodeReq.Disjoint.singleton h48))
    -- Top-level structure is
    --   Four = (Two ∪ trio_16) ∪ trio_28
    -- where Two = base ∪ +4 ∪ +8 ∪ +12 (right-associated chain).
    refine CodeReq.Disjoint.union_left ?_ ?_
    · -- Two ∪ trio_16
      refine CodeReq.Disjoint.union_left ?_ ?_
      · -- Two: 4 right-associated leaves at base, +4, +8, +12
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
  -- The final code-req shape is `mloadBytePackFiveCode = four.union triple`.
  exact cpsTripleWithin_seq hd_step fourRaw step

/-- Bundled CodeReq for `mload_byte_pack_six_spec_within`: a 16-instruction
    union extending `mloadBytePackFiveCode` with one additional
    `LBU/SLLI/OR` triple at `base + 52 / base + 56 / base + 60` for the
    sixth byte. -/
def mloadBytePackSixCode
    (addrReg byteReg accReg : Reg)
    (off0 off1 off2 off3 off4 off5 : BitVec 12)
    (base : Word) : CodeReq :=
  (mloadBytePackFiveCode addrReg byteReg accReg off0 off1 off2 off3 off4 base).union
    ((CodeReq.singleton (base + 52) (.LBU byteReg addrReg off5)).union
     ((CodeReq.singleton (base + 56) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
      (CodeReq.singleton (base + 60) (.OR accReg accReg byteReg))))

/-- Bundled precondition for `mload_byte_pack_six_spec_within`: the
    three roles `addrReg ↦ᵣ addrPtr`, `byteReg ↦ᵣ byteOld`,
    `accReg ↦ᵣ accOld`, plus the source dword `dwordAddr ↦ₘ wordVal`.

    Pulled into an `@[irreducible]` definition (mirroring the slice 3d-pre4
    convention from PR #1697) so the spec statement is not cluttered by a
    long chain of `let`-bindings; downstream callers see a single named
    handle and use `mloadBytePackSixPre_unfold` to expand on demand. -/
@[irreducible]
def mloadBytePackSixPre
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld wordVal dwordAddr : Word) : Assertion :=
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
  (dwordAddr ↦ₘ wordVal)

theorem mloadBytePackSixPre_unfold
    {addrReg byteReg accReg : Reg}
    {addrPtr accOld byteOld wordVal dwordAddr : Word} :
    mloadBytePackSixPre addrReg byteReg accReg
        addrPtr accOld byteOld wordVal dwordAddr =
    ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
     (dwordAddr ↦ₘ wordVal)) := by
  delta mloadBytePackSixPre; rfl

/-- Bundled postcondition for `mload_byte_pack_six_spec_within`: after
    the 16-instruction sequence, `byteReg` holds the last byte loaded
    (`b5`) and `accReg` holds the big-endian fold
    `(((((b0 <<< 8) ||| b1) <<< 8 ||| b2) <<< 8 ||| b3) <<< 8 ||| b4) <<< 8 ||| b5`. -/
@[irreducible]
def mloadBytePackSixPost
    (addrReg byteReg accReg : Reg)
    (addrPtr wordVal dwordAddr : Word)
    (off0 off1 off2 off3 off4 off5 : BitVec 12) : Assertion :=
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
  let accFinal :=
    ((((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3)
        <<< (8 : Nat) ||| b4) <<< (8 : Nat) ||| b5
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b5) ** (accReg ↦ᵣ accFinal) **
  (dwordAddr ↦ₘ wordVal)

theorem mloadBytePackSixPost_unfold
    {addrReg byteReg accReg : Reg}
    {addrPtr wordVal dwordAddr : Word}
    {off0 off1 off2 off3 off4 off5 : BitVec 12} :
    mloadBytePackSixPost addrReg byteReg accReg
        addrPtr wordVal dwordAddr off0 off1 off2 off3 off4 off5 =
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
     let accFinal :=
       ((((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3)
           <<< (8 : Nat) ||| b4) <<< (8 : Nat) ||| b5
     (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b5) ** (accReg ↦ᵣ accFinal) **
     (dwordAddr ↦ₘ wordVal)) := by
  delta mloadBytePackSixPost; rfl

/-- Six-byte big-endian byte-pack spec (16 instructions): seed `LBU`
    loading `b0`, then five `LBU + SLLI + OR` triples folding `b1`..`b5`
    in big-endian order, yielding
    `(((((b0 <<< 8) ||| b1) <<< 8 ||| b2) <<< 8 ||| b3) <<< 8 ||| b4) <<< 8 ||| b5`
    in `accReg`.

    This is the `n = 6` step in the inductive ladder
    `mload_byte_pack_init` (n=1) → `mload_byte_pack_two` (n=2) →
    `mload_byte_pack_three` (n=3) → `mload_byte_pack_four` (n=4) →
    `mload_byte_pack_five` (n=5) → `mload_byte_pack_six` (n=6) → … →
    `mload_one_limb` (n=8). Proved by composing the existing 5-byte spec
    (PR #1697) with one `mload_byte_pack_step_spec_within` application;
    no new tactic machinery is needed. -/
theorem mload_byte_pack_six_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld wordVal : Word)
    (dwordAddr : Word)
    (off0 off1 off2 off3 off4 off5 : BitVec 12) (base : Word)
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
    (h_valid5 : isValidByteAccess (addrPtr + signExtend12 off5) = true) :
    cpsTripleWithin 16 base (base + 64)
      (mloadBytePackSixCode addrReg byteReg accReg off0 off1 off2 off3 off4 off5 base)
      (mloadBytePackSixPre addrReg byteReg accReg
        addrPtr accOld byteOld wordVal dwordAddr)
      (mloadBytePackSixPost addrReg byteReg accReg
        addrPtr wordVal dwordAddr off0 off1 off2 off3 off4 off5) := by
  rw [mloadBytePackSixPre_unfold, mloadBytePackSixPost_unfold]
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
  set accAfter5 :=
    (((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3)
        <<< (8 : Nat) ||| b4
    with h_accAfter5
  set accFinal := (accAfter5 <<< (8 : Nat)) ||| b5
  -- Step 1: 13-instruction 5-byte spec at `base`.
  have fiveRaw := mload_byte_pack_five_spec_within addrReg byteReg accReg
    addrPtr accOld byteOld wordVal dwordAddr off0 off1 off2 off3 off4 base
    h_byte_ne_x0 h_acc_ne_x0 h_align0 h_valid0 h_align1 h_valid1
    h_align2 h_valid2 h_align3 h_valid3 h_align4 h_valid4
  rw [mloadBytePackFivePre_unfold, mloadBytePackFivePost_unfold] at fiveRaw
  -- Step 2: 3-instruction byte-pack triple at `base + 52` folding `b5`.
  have step := mload_byte_pack_step_spec_within addrReg byteReg accReg
    addrPtr accAfter5 b4 wordVal dwordAddr off5 (base + 52)
    h_byte_ne_x0 h_acc_ne_x0 h_align5 h_valid5
  rw [show (base + 52 : Word) + 12 = base + 64 from by bv_omega] at step
  rw [show (base + 52 : Word) + 4 = base + 56 from by bv_omega,
      show (base + 52 : Word) + 8 = base + 60 from by bv_omega] at step
  -- Disjointness between the five-byte block (addresses base, base+4,
  -- base+8, …, base+48) and the trailing triple (base+52, base+56,
  -- base+60). 13 leaf inequalities.
  have hd_step : CodeReq.Disjoint
      (mloadBytePackFiveCode addrReg byteReg accReg off0 off1 off2 off3 off4 base)
      ((CodeReq.singleton (base + 52) (.LBU byteReg addrReg off5)).union
       ((CodeReq.singleton (base + 56) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
        (CodeReq.singleton (base + 60) (.OR accReg accReg byteReg)))) := by
    unfold mloadBytePackFiveCode mloadBytePackFourCode
      mloadBytePackThreeCode mloadBytePackTwoCode
    have leaf : ∀ {a : Word} {i : Instr},
        a ≠ base + 52 → a ≠ base + 56 → a ≠ base + 60 →
        CodeReq.Disjoint (CodeReq.singleton a i)
            ((CodeReq.singleton (base + 52) (.LBU byteReg addrReg off5)).union
             ((CodeReq.singleton (base + 56) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
              (CodeReq.singleton (base + 60) (.OR accReg accReg byteReg)))) := by
      intro a i h52 h56 h60
      exact CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton h52)
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.singleton h56)
          (CodeReq.Disjoint.singleton h60))
    -- Top-level structure of mloadBytePackFiveCode is
    --   Five = ((Four = (Two ∪ trio_16) ∪ trio_28) ∪ trio_40)
    -- Two = leaves at base, +4, +8, +12.
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
  -- The final code-req shape is `mloadBytePackSixCode = five.union triple`.
  exact cpsTripleWithin_seq hd_step fiveRaw step

/-- Bundled CodeReq for `mload_byte_pack_seven_spec_within`: a 19-instruction
    union extending `mloadBytePackSixCode` with one additional
    `LBU/SLLI/OR` triple at `base + 64 / base + 68 / base + 72` for the
    seventh byte. -/
def mloadBytePackSevenCode
    (addrReg byteReg accReg : Reg)
    (off0 off1 off2 off3 off4 off5 off6 : BitVec 12)
    (base : Word) : CodeReq :=
  (mloadBytePackSixCode addrReg byteReg accReg
      off0 off1 off2 off3 off4 off5 base).union
    ((CodeReq.singleton (base + 64) (.LBU byteReg addrReg off6)).union
     ((CodeReq.singleton (base + 68) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
      (CodeReq.singleton (base + 72) (.OR accReg accReg byteReg))))

/-- Bundled precondition for `mload_byte_pack_seven_spec_within`: the
    three roles `addrReg ↦ᵣ addrPtr`, `byteReg ↦ᵣ byteOld`,
    `accReg ↦ᵣ accOld`, plus the source dword `dwordAddr ↦ₘ wordVal`.

    Pulled into an `@[irreducible]` definition (mirroring the slice 3d-pre5
    convention from PR #1701) so the spec statement is not cluttered by a
    long chain of `let`-bindings; downstream callers see a single named
    handle and use `mloadBytePackSevenPre_unfold` to expand on demand. -/
@[irreducible]
def mloadBytePackSevenPre
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld wordVal dwordAddr : Word) : Assertion :=
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
  (dwordAddr ↦ₘ wordVal)

theorem mloadBytePackSevenPre_unfold
    {addrReg byteReg accReg : Reg}
    {addrPtr accOld byteOld wordVal dwordAddr : Word} :
    mloadBytePackSevenPre addrReg byteReg accReg
        addrPtr accOld byteOld wordVal dwordAddr =
    ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
     (dwordAddr ↦ₘ wordVal)) := by
  delta mloadBytePackSevenPre; rfl

/-- Bundled postcondition for `mload_byte_pack_seven_spec_within`: after
    the 19-instruction sequence, `byteReg` holds the last byte loaded
    (`b6`) and `accReg` holds the big-endian fold
    `((((((b0 <<< 8) ||| b1) <<< 8 ||| b2) <<< 8 ||| b3) <<< 8 ||| b4)
        <<< 8 ||| b5) <<< 8 ||| b6`. -/
@[irreducible]
def mloadBytePackSevenPost
    (addrReg byteReg accReg : Reg)
    (addrPtr wordVal dwordAddr : Word)
    (off0 off1 off2 off3 off4 off5 off6 : BitVec 12) : Assertion :=
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
  let accFinal :=
    (((((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3)
        <<< (8 : Nat) ||| b4) <<< (8 : Nat) ||| b5) <<< (8 : Nat) ||| b6
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b6) ** (accReg ↦ᵣ accFinal) **
  (dwordAddr ↦ₘ wordVal)

theorem mloadBytePackSevenPost_unfold
    {addrReg byteReg accReg : Reg}
    {addrPtr wordVal dwordAddr : Word}
    {off0 off1 off2 off3 off4 off5 off6 : BitVec 12} :
    mloadBytePackSevenPost addrReg byteReg accReg
        addrPtr wordVal dwordAddr off0 off1 off2 off3 off4 off5 off6 =
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
     let accFinal :=
       (((((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3)
           <<< (8 : Nat) ||| b4) <<< (8 : Nat) ||| b5) <<< (8 : Nat) ||| b6
     (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b6) ** (accReg ↦ᵣ accFinal) **
     (dwordAddr ↦ₘ wordVal)) := by
  delta mloadBytePackSevenPost; rfl

/-- Seven-byte big-endian byte-pack spec (19 instructions): seed `LBU`
    loading `b0`, then six `LBU + SLLI + OR` triples folding `b1`..`b6`
    in big-endian order, yielding
    `((((((b0 <<< 8) ||| b1) <<< 8 ||| b2) <<< 8 ||| b3) <<< 8 ||| b4)
        <<< 8 ||| b5) <<< 8 ||| b6`
    in `accReg`.

    This is the `n = 7` step in the inductive ladder
    `mload_byte_pack_init` (n=1) → `mload_byte_pack_two` (n=2) →
    `mload_byte_pack_three` (n=3) → `mload_byte_pack_four` (n=4) →
    `mload_byte_pack_five` (n=5) → `mload_byte_pack_six` (n=6) →
    `mload_byte_pack_seven` (n=7) → `mload_one_limb` (n=8). Proved by
    composing the existing 6-byte spec (PR #1701) with one
    `mload_byte_pack_step_spec_within` application; no new tactic
    machinery is needed. -/
theorem mload_byte_pack_seven_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld wordVal : Word)
    (dwordAddr : Word)
    (off0 off1 off2 off3 off4 off5 off6 : BitVec 12) (base : Word)
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
    (h_valid6 : isValidByteAccess (addrPtr + signExtend12 off6) = true) :
    cpsTripleWithin 19 base (base + 76)
      (mloadBytePackSevenCode addrReg byteReg accReg
        off0 off1 off2 off3 off4 off5 off6 base)
      (mloadBytePackSevenPre addrReg byteReg accReg
        addrPtr accOld byteOld wordVal dwordAddr)
      (mloadBytePackSevenPost addrReg byteReg accReg
        addrPtr wordVal dwordAddr off0 off1 off2 off3 off4 off5 off6) := by
  rw [mloadBytePackSevenPre_unfold, mloadBytePackSevenPost_unfold]
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
  set accAfter6 :=
    ((((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3)
        <<< (8 : Nat) ||| b4) <<< (8 : Nat) ||| b5
    with h_accAfter6
  set accFinal := (accAfter6 <<< (8 : Nat)) ||| b6
  -- Step 1: 16-instruction 6-byte spec at `base`.
  have sixRaw := mload_byte_pack_six_spec_within addrReg byteReg accReg
    addrPtr accOld byteOld wordVal dwordAddr off0 off1 off2 off3 off4 off5 base
    h_byte_ne_x0 h_acc_ne_x0 h_align0 h_valid0 h_align1 h_valid1
    h_align2 h_valid2 h_align3 h_valid3 h_align4 h_valid4 h_align5 h_valid5
  rw [mloadBytePackSixPre_unfold, mloadBytePackSixPost_unfold] at sixRaw
  -- Step 2: 3-instruction byte-pack triple at `base + 64` folding `b6`.
  have step := mload_byte_pack_step_spec_within addrReg byteReg accReg
    addrPtr accAfter6 b5 wordVal dwordAddr off6 (base + 64)
    h_byte_ne_x0 h_acc_ne_x0 h_align6 h_valid6
  rw [show (base + 64 : Word) + 12 = base + 76 from by bv_omega] at step
  rw [show (base + 64 : Word) + 4 = base + 68 from by bv_omega,
      show (base + 64 : Word) + 8 = base + 72 from by bv_omega] at step
  -- Disjointness between the six-byte block (addresses base, base+4,
  -- base+8, …, base+60) and the trailing triple (base+64, base+68,
  -- base+72). 16 leaf inequalities.
  have hd_step : CodeReq.Disjoint
      (mloadBytePackSixCode addrReg byteReg accReg off0 off1 off2 off3 off4 off5 base)
      ((CodeReq.singleton (base + 64) (.LBU byteReg addrReg off6)).union
       ((CodeReq.singleton (base + 68) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
        (CodeReq.singleton (base + 72) (.OR accReg accReg byteReg)))) := by
    unfold mloadBytePackSixCode mloadBytePackFiveCode mloadBytePackFourCode
      mloadBytePackThreeCode mloadBytePackTwoCode
    have leaf : ∀ {a : Word} {i : Instr},
        a ≠ base + 64 → a ≠ base + 68 → a ≠ base + 72 →
        CodeReq.Disjoint (CodeReq.singleton a i)
            ((CodeReq.singleton (base + 64) (.LBU byteReg addrReg off6)).union
             ((CodeReq.singleton (base + 68) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
              (CodeReq.singleton (base + 72) (.OR accReg accReg byteReg)))) := by
      intro a i h64 h68 h72
      exact CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton h64)
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.singleton h68)
          (CodeReq.Disjoint.singleton h72))
    -- Top-level structure of mloadBytePackSixCode is
    --   Six = Five ∪ trio_52
    -- Five = ((Four = (Two ∪ trio_16) ∪ trio_28) ∪ trio_40)
    -- Two = leaves at base, +4, +8, +12.
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
  -- The final code-req shape is `mloadBytePackSevenCode = six.union triple`.
  exact cpsTripleWithin_seq hd_step sixRaw step

end EvmAsm.Evm64
