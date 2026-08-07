/-
  EvmAsm.Crypto.BeBytesBridge

  The missing equality between the tree's **two** big-endian byte decoders
  (GH #11574).

  `EvmAsm.Crypto.beBytesToNat` (`PowLadder.lean`) is a left fold with an
  accumulator; `EvmAsm.EL.RLP.Nat.fromBytesBE` (`EL/RLP/Basic.lean`) is a
  structural recursion multiplying by a positional power. They compute the same
  function and **nothing in the tree said so** — 36 files use the `foldl` form,
  the `SpecRef` port uses the recursion (`bytesBEtoNat` is an abbrev for it,
  `SpecRef/Crypto.lean`), and no lemma connected them.

  ## Why this is load-bearing rather than tidying

  Every guest-side triple over a big-endian field element states its post in the
  `foldl` form — `blsgLtP_spec` and `bnfLtP_spec` both conclude
  `a0 = if beBytesToNat xs < beBytesToNat pBytes then 1 else 0`. Every SpecRef
  counterpart (`Bls12.bytes_to_fq`, `Bn128.bytes_to_g1`) is written over
  `bytesBEtoNat`. So a correspondence bridge between them has **no ground to
  stand on** without this equality: the two sides would be talking about
  syntactically different functions that a reader assumes are the same.

  `U256MinSAsm.beBytesToNat_foldl` proves the accumulator generalisation, but it
  is `private`, lives under `Codegen`, and stops short of the equality — so it is
  unavailable to a core-side bridge on both counts.
-/

import EvmAsm.Crypto.PowLadder
import EvmAsm.EL.RLP.Basic

namespace EvmAsm.Crypto

open EvmAsm.EL.RLP

/-- The accumulator generalisation: folding from `acc` scales it by the width of
    what remains. Stated over `fromBytesBE` directly, so the specialisation below
    is the bridge rather than a restatement. -/
private theorem foldl_be_eq (bs : List (BitVec 8)) (acc : Nat) :
    bs.foldl (fun a b => a * 256 + b.toNat) acc
      = acc * 256 ^ bs.length + Nat.fromBytesBE bs := by
  induction bs generalizing acc with
  | nil => simp [Nat.fromBytesBE]
  | cons b rest ih =>
      -- Mathlib-free layer, so the regrouping is explicit core `Nat` lemmas
      -- rather than `ring`.
      show rest.foldl _ (acc * 256 + b.toNat) = _
      rw [ih (acc * 256 + b.toNat)]
      show (acc * 256 + b.toNat) * 256 ^ rest.length + Nat.fromBytesBE rest
          = acc * 256 ^ (rest.length + 1)
            + (b.toNat * 256 ^ rest.length + Nat.fromBytesBE rest)
      rw [Nat.pow_succ, Nat.add_mul, Nat.add_assoc, Nat.mul_assoc,
        Nat.mul_comm 256 (256 ^ rest.length)]

/-- **The bridge.** The guest's fold and the model's recursion are the same
    function on every input.

    This is what lets a `blsgLtP_spec`-style post (`beBytesToNat xs < …`) be read
    against a `SpecRef` clause written over `bytesBEtoNat` — without it the two
    are different functions that merely look alike. -/
theorem beBytesToNat_eq_fromBytesBE (bs : List (BitVec 8)) :
    beBytesToNat bs = Nat.fromBytesBE bs := by
  show bs.foldl (fun a b => a * 256 + b.toNat) 0 = _
  rw [foldl_be_eq bs 0, Nat.zero_mul, Nat.zero_add]

/-- The same equality in the direction a `SpecRef`-side rewrite wants. -/
theorem fromBytesBE_eq_beBytesToNat (bs : List (BitVec 8)) :
    Nat.fromBytesBE bs = beBytesToNat bs :=
  (beBytesToNat_eq_fromBytesBE bs).symm

/-! ## Witnesses

    Concrete checks that the two decoders agree, including the cases where a
    plausible-but-wrong bridge would differ: a leading zero byte (positional
    weight must still be paid), and a multi-byte value whose bytes are not
    symmetric under reversal (so an accidental little-endian reading is
    excluded). -/

#guard beBytesToNat [] == Nat.fromBytesBE []
#guard beBytesToNat [0x01] == Nat.fromBytesBE [0x01]
#guard beBytesToNat [0x01, 0x02] == Nat.fromBytesBE [0x01, 0x02]
#guard beBytesToNat [0x00, 0x01] == Nat.fromBytesBE [0x00, 0x01]
#guard beBytesToNat [0xde, 0xad, 0xbe, 0xef] == Nat.fromBytesBE [0xde, 0xad, 0xbe, 0xef]

-- ⚠️ Non-palindromic, so this one fails if either side is read little-endian.
#guard Nat.fromBytesBE [0x01, 0x02] == 0x0102
#guard Nat.fromBytesBE [0x01, 0x02] != 0x0201

end EvmAsm.Crypto
