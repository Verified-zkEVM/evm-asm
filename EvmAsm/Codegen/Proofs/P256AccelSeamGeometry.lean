/-
  EvmAsm.Codegen.Proofs.P256AccelSeamGeometry

  The measured P-256 accelerator geometry, as kernel-checked facts.

  `csrs_arith256Mod_distributed_spec_within` (`Rv64/SAsm/AccelStep.lean`) lets
  each of `a`, `b`, `c`, `module` resolve into EITHER the parameter region or
  the operand arena.  This module records why that generality is needed rather
  than the simpler segregated shape, in a form that cannot rot: every address
  is cited through `GuestAddrs`, never transcribed, and every claim is
  `decide`-checked against the linked layout.

  ## The split, and where it comes from

  The emitter declares the LE staging buffers and the parameter blocks
  adjacently (`P256Verify.lean`), which reads as one contiguous arena.  It is
  not one.  `.zero`-initialised symbols are routed to `.bss` and initialised
  `.quad` symbols to `.data`, so at link time they land in different regions —
  the source order says nothing about the image, and `nm` (equivalently
  `scripts/asm-fixtures/symbol-addresses.tsv`, which records the section per
  symbol) is the oracle.

  `p256_pb_mul_p` is `{a, b, c, module, d}` = `{le_a, le_b, le_zero, le_p,
  le_d}`.  Four of those are `.bss` staging buffers; `le_p`, the modulus, is
  `.data` — the SAME region as the parameter block itself.  `pb_add_p` and
  `pb_sub_p` put two each in `.data`.  So "parameters here, operands there" is
  not merely inconvenient for this image: it is false of it.

  ## What is and is not pinned here

  `GuestAddrs` is GENERATED, and emits a constant only for a symbol some
  `_prog` references.  `p256_le_p`, `p256_le_zero`, `p256_le_one` are
  referenced only from `.data` initialisers, so they have no constant to cite.
  The offsets below are therefore plain `Nat`s measured from the linked image;
  what IS pinned symbolically is every relationship that can be: the two region
  bases, their alignment, their separation, and the parameter block's own
  offset.  The negative control needs nothing more, because it is about where
  the modulus can NOT be.

  Layering: Codegen-side because `GuestAddrs` is Codegen and the verified core
  may not import it (`check-layering.sh`).
-/
import EvmAsm.Rv64.SAsm.AccelStep
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.P256AccelSeamGeometry

open EvmAsm.Rv64

-- The two negative controls are `∀ n < k` enumerations over concrete
-- `BitVec` arithmetic; `k = 392` overruns the default recursion depth.
set_option maxRecDepth 8000

/-! ## The two regions, cited by symbol -/

/-- Base of the `.data` region that holds the LE constants and, after them, the
    four parameter blocks. -/
abbrev dataBase : Word := (GuestAddrs.p256_a_be : Word)

/-- Base of the `.bss` staging region: `le_a`, `le_b`, `le_d`, `le_zero`. -/
abbrev bssBase : Word := (GuestAddrs.p256_le_a : Word)

/-- Offset of the modulus (`p256_le_p`) within the `.data` region. -/
abbrev modulusOff : Nat := 256

/-- Offset of `p256_pb_mul_p` within the `.data` region. -/
abbrev mulParamsOff : Nat := 352

/-- Both bases are dword-aligned, as `bytesRegion` requires of a region base. -/
theorem bases_aligned :
    dataBase.toNat % 8 = 0 ∧ bssBase.toNat % 8 = 0 := by decide

/-- The regions are disjoint by a very wide margin — the geometry that made a
    single window unusable to begin with. -/
theorem regions_far_apart :
    bssBase.toNat > dataBase.toNat + 0x10000000 := by decide

/-- The parameter block's offset, pinned symbolically: both endpoints are
    `GuestAddrs` constants, so a relink that moves either one breaks this
    proof rather than silently invalidating the offsets below. -/
theorem mulParams_offset :
    (GuestAddrs.p256_pb_mul_p : Word) = dataBase + BitVec.ofNat 64 mulParamsOff := by
  decide

/-- Two of the four staging offsets are pinned symbolically for the same
    reason (`le_zero` has no `GuestAddrs` constant to cite). -/
theorem staging_offsets :
    (GuestAddrs.p256_le_b : Word) = bssBase + BitVec.ofNat 64 32
      ∧ (GuestAddrs.p256_le_d : Word) = bssBase + BitVec.ofNat 64 64 := by
  decide

/-! ## Why a single selector cannot serve

    The seam takes one selector per pointer.  These two theorems show that
    neither constant selector works for `pb_mul_p`, so the per-pointer form is
    forced — not merely convenient. -/

/-- **Negative control: the modulus does not live in the operand arena.**  With
    `srcM = false` the seam would need `modulus = bssBase + ofNat mOff` for some
    offset inside the 128-byte staging region.  No such offset exists — this is
    refuted, not merely unproven, so an "all operands in the arena" instance
    cannot be written for this block. -/
theorem modulus_not_in_arena :
    ∀ mOff : Nat, mOff < 128 →
      dataBase + BitVec.ofNat 64 modulusOff ≠ bssBase + BitVec.ofNat 64 mOff := by
  decide

/-- The converse control: the first operand does not live in the parameter
    region either, so `srcA = true` is refuted as well.  Together with
    `modulus_not_in_arena` this rules out BOTH constant selectors. -/
theorem operandA_not_in_params :
    ∀ aOff : Nat, aOff < 392 →
      bssBase ≠ dataBase + BitVec.ofNat 64 aOff := by
  decide

end EvmAsm.Codegen.P256AccelSeamGeometry
