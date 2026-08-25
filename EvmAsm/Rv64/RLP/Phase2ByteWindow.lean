/-
  EvmAsm.Rv64.RLP.Phase2ByteWindow

  Bundled per-byte side conditions for an eight-byte aligned window inside a
  single doubleword, used by the RLP Phase 2 long-form loop closures.

  Sibling of `mloadAlignedLimbWindowOk` (Evm64/MLoad/LimbSpec.lean) and
  `mstoreLimbWindowOk` (Evm64/MStore/Spec.lean). See parent task evm-asm-yrz5
  / sibling slice evm-asm-jb8a.

  The closures `rlp_phase2_long_loop_{seven,eight}_byte_spec_within` previously
  took `2*N` separate `alignToDword`/`isValidByteAccess` hypotheses per call
  site (N = 7 or 8). Bundling them under a single predicate cuts the lemma
  signature down to one hypothesis per dword window and removes the
  `halign1..halignN` / `hvalid1..hvalidN` boilerplate.
-/

module

public import EvmAsm.Rv64.Basic

@[expose] public section

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64

/--
Side conditions for one eight-byte aligned RLP byte window: every byte at
offsets `0..7` from `ptr` lives in the same doubleword `dwordAddr` and is a
valid byte access.

Used by the RLP Phase 2 long-form loop closures (`rlp_phase2_long_loop_*_byte_spec_within`)
that iteratively load consecutive bytes from a single doubleword.

The eight conjuncts are listed in the order the consumer specs introduce
them (`halign1..halign8` then `hvalid1..hvalid8`) so destructuring matches the
historical naming.
-/
def rlpAlignedByteWindowOk (ptr dwordAddr : Word) : Prop :=
  alignToDword ptr = dwordAddr ∧
  alignToDword (ptr + 1) = dwordAddr ∧
  alignToDword (ptr + 2) = dwordAddr ∧
  alignToDword (ptr + 3) = dwordAddr ∧
  alignToDword (ptr + 4) = dwordAddr ∧
  alignToDword (ptr + 5) = dwordAddr ∧
  alignToDword (ptr + 6) = dwordAddr ∧
  alignToDword (ptr + 7) = dwordAddr ∧
  isValidByteAccess ptr = true ∧
  isValidByteAccess (ptr + 1) = true ∧
  isValidByteAccess (ptr + 2) = true ∧
  isValidByteAccess (ptr + 3) = true ∧
  isValidByteAccess (ptr + 4) = true ∧
  isValidByteAccess (ptr + 5) = true ∧
  isValidByteAccess (ptr + 6) = true ∧
  isValidByteAccess (ptr + 7) = true

/-- Constructor wrapper — assemble the bundle from the legacy 16-argument form
    so existing call sites (and downstream consumers that still produce raw
    per-byte hypotheses) can adopt the bundle without rebuilding their own
    derivation chains. -/
theorem rlpAlignedByteWindowOk.mk
    {ptr dwordAddr : Word}
    (halign1 : alignToDword ptr = dwordAddr)
    (halign2 : alignToDword (ptr + 1) = dwordAddr)
    (halign3 : alignToDword (ptr + 2) = dwordAddr)
    (halign4 : alignToDword (ptr + 3) = dwordAddr)
    (halign5 : alignToDword (ptr + 4) = dwordAddr)
    (halign6 : alignToDword (ptr + 5) = dwordAddr)
    (halign7 : alignToDword (ptr + 6) = dwordAddr)
    (halign8 : alignToDword (ptr + 7) = dwordAddr)
    (hvalid1 : isValidByteAccess ptr = true)
    (hvalid2 : isValidByteAccess (ptr + 1) = true)
    (hvalid3 : isValidByteAccess (ptr + 2) = true)
    (hvalid4 : isValidByteAccess (ptr + 3) = true)
    (hvalid5 : isValidByteAccess (ptr + 4) = true)
    (hvalid6 : isValidByteAccess (ptr + 5) = true)
    (hvalid7 : isValidByteAccess (ptr + 6) = true)
    (hvalid8 : isValidByteAccess (ptr + 7) = true) :
    rlpAlignedByteWindowOk ptr dwordAddr :=
  ⟨halign1, halign2, halign3, halign4, halign5, halign6, halign7, halign8,
   hvalid1, hvalid2, hvalid3, hvalid4, hvalid5, hvalid6, hvalid7, hvalid8⟩

/--
Side conditions for one seven-byte aligned RLP byte window: every byte at
offsets `0..6` from `ptr` lives in the same doubleword `dwordAddr` and is a
valid byte access.

Used by `rlp_phase2_long_loop_seven_byte_spec_within` (Phase 2 long-form
loop, lenLen = 7). Sibling of `rlpAlignedByteWindowOk` (eight-byte form).
-/
def rlpAlignedByteWindow7Ok (ptr dwordAddr : Word) : Prop :=
  alignToDword ptr = dwordAddr ∧
  alignToDword (ptr + 1) = dwordAddr ∧
  alignToDword (ptr + 2) = dwordAddr ∧
  alignToDword (ptr + 3) = dwordAddr ∧
  alignToDword (ptr + 4) = dwordAddr ∧
  alignToDword (ptr + 5) = dwordAddr ∧
  alignToDword (ptr + 6) = dwordAddr ∧
  isValidByteAccess ptr = true ∧
  isValidByteAccess (ptr + 1) = true ∧
  isValidByteAccess (ptr + 2) = true ∧
  isValidByteAccess (ptr + 3) = true ∧
  isValidByteAccess (ptr + 4) = true ∧
  isValidByteAccess (ptr + 5) = true ∧
  isValidByteAccess (ptr + 6) = true

/-- Constructor wrapper for `rlpAlignedByteWindow7Ok` from the legacy
    14-argument form. -/
theorem rlpAlignedByteWindow7Ok.mk
    {ptr dwordAddr : Word}
    (halign1 : alignToDword ptr = dwordAddr)
    (halign2 : alignToDword (ptr + 1) = dwordAddr)
    (halign3 : alignToDword (ptr + 2) = dwordAddr)
    (halign4 : alignToDword (ptr + 3) = dwordAddr)
    (halign5 : alignToDword (ptr + 4) = dwordAddr)
    (halign6 : alignToDword (ptr + 5) = dwordAddr)
    (halign7 : alignToDword (ptr + 6) = dwordAddr)
    (hvalid1 : isValidByteAccess ptr = true)
    (hvalid2 : isValidByteAccess (ptr + 1) = true)
    (hvalid3 : isValidByteAccess (ptr + 2) = true)
    (hvalid4 : isValidByteAccess (ptr + 3) = true)
    (hvalid5 : isValidByteAccess (ptr + 4) = true)
    (hvalid6 : isValidByteAccess (ptr + 5) = true)
    (hvalid7 : isValidByteAccess (ptr + 6) = true) :
    rlpAlignedByteWindow7Ok ptr dwordAddr :=
  ⟨halign1, halign2, halign3, halign4, halign5, halign6, halign7,
   hvalid1, hvalid2, hvalid3, hvalid4, hvalid5, hvalid6, hvalid7⟩

/-- The eight-byte bundle implies the seven-byte bundle by dropping the
    last conjuncts. Useful when a caller already has the eight-byte form
    on hand. -/
theorem rlpAlignedByteWindow7Ok.of_eight
    {ptr dwordAddr : Word}
    (h : rlpAlignedByteWindowOk ptr dwordAddr) :
    rlpAlignedByteWindow7Ok ptr dwordAddr := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, _, h9, h10, h11, h12, h13, h14, h15, _⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h9, h10, h11, h12, h13, h14, h15⟩

/--
Side conditions for one six-byte aligned RLP byte window: every byte at
offsets `0..5` from `ptr` lives in the same doubleword `dwordAddr` and is a
valid byte access.

Used by `rlp_phase2_long_loop_six_byte_spec_within` (Phase 2 long-form
loop, lenLen = 6). Sibling of `rlpAlignedByteWindowOk` (eight-byte form)
and `rlpAlignedByteWindow7Ok` (seven-byte form).
-/
def rlpAlignedByteWindow6Ok (ptr dwordAddr : Word) : Prop :=
  alignToDword ptr = dwordAddr ∧
  alignToDword (ptr + 1) = dwordAddr ∧
  alignToDword (ptr + 2) = dwordAddr ∧
  alignToDword (ptr + 3) = dwordAddr ∧
  alignToDword (ptr + 4) = dwordAddr ∧
  alignToDword (ptr + 5) = dwordAddr ∧
  isValidByteAccess ptr = true ∧
  isValidByteAccess (ptr + 1) = true ∧
  isValidByteAccess (ptr + 2) = true ∧
  isValidByteAccess (ptr + 3) = true ∧
  isValidByteAccess (ptr + 4) = true ∧
  isValidByteAccess (ptr + 5) = true

/-- Constructor wrapper for `rlpAlignedByteWindow6Ok` from the legacy
    12-argument form. -/
theorem rlpAlignedByteWindow6Ok.mk
    {ptr dwordAddr : Word}
    (halign1 : alignToDword ptr = dwordAddr)
    (halign2 : alignToDword (ptr + 1) = dwordAddr)
    (halign3 : alignToDword (ptr + 2) = dwordAddr)
    (halign4 : alignToDword (ptr + 3) = dwordAddr)
    (halign5 : alignToDword (ptr + 4) = dwordAddr)
    (halign6 : alignToDword (ptr + 5) = dwordAddr)
    (hvalid1 : isValidByteAccess ptr = true)
    (hvalid2 : isValidByteAccess (ptr + 1) = true)
    (hvalid3 : isValidByteAccess (ptr + 2) = true)
    (hvalid4 : isValidByteAccess (ptr + 3) = true)
    (hvalid5 : isValidByteAccess (ptr + 4) = true)
    (hvalid6 : isValidByteAccess (ptr + 5) = true) :
    rlpAlignedByteWindow6Ok ptr dwordAddr :=
  ⟨halign1, halign2, halign3, halign4, halign5, halign6,
   hvalid1, hvalid2, hvalid3, hvalid4, hvalid5, hvalid6⟩

/-- The seven-byte bundle implies the six-byte bundle by dropping the
    last conjuncts. -/
theorem rlpAlignedByteWindow6Ok.of_seven
    {ptr dwordAddr : Word}
    (h : rlpAlignedByteWindow7Ok ptr dwordAddr) :
    rlpAlignedByteWindow6Ok ptr dwordAddr := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _, h8, h9, h10, h11, h12, h13, _⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h8, h9, h10, h11, h12, h13⟩

/-- The eight-byte bundle implies the six-byte bundle by dropping the
    last conjuncts. -/
theorem rlpAlignedByteWindow6Ok.of_eight
    {ptr dwordAddr : Word}
    (h : rlpAlignedByteWindowOk ptr dwordAddr) :
    rlpAlignedByteWindow6Ok ptr dwordAddr :=
  rlpAlignedByteWindow6Ok.of_seven (rlpAlignedByteWindow7Ok.of_eight h)

end EvmAsm.Rv64.RLP
