/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file EvmAsm/SLHDSA/LICENSE.
Authors: Nicolas Consigny
-/

module
public import EvmAsm.SLHDSA.Hypertree

/-!
# SLH-DSA Scheme, deterministic core (FIPS 205 §9)

The deterministic internal algorithms of SLH-DSA for the `d = 1` parameter shape, assembled
from FORS (`EvmAsm.SLHDSA.Fors`) and the single-layer hypertree (`EvmAsm.SLHDSA.Hypertree`):

- `slhKeygenInternal` / `slhSignInternal` / `slhVerifyInternal` (Algorithms 18–20),
- `splitDigest`, the message-digest split into `(md, idxLeaf)` (§9; for `d = 1` the tree index
  is always `0`, so it is omitted).

The headline result `slhVerifyInternal_slhSignInternal` proves the deterministic correctness
core with no `sorry`: every honestly generated signature verifies, for every choice of seeds
and randomizer. It is a hash-tree consistency fact composing WOTS+/XMSS/FORS/hypertree
correctness.

This module is ported from the VCVio development (`HashSig.SLHDSA.Scheme`); the probabilistic
external wrappers (Algorithms 21–24) and the generic `SignatureAlg` instantiation live there,
on top of VCVio's `OracleComp` framework, and are intentionally not ported — the RISC-V
verifier only needs the deterministic `slhVerifyInternal`.

## References

- NIST FIPS 205, §9 (Algorithms 18–20), §4.1 (the H_msg digest split)
-/

@[expose] public section


namespace SLHDSA

variable {p : Params}

/-- The SLH-DSA public key: public seed and hypertree root. -/
structure PublicKey (prims : Primitives p) where
  /-- Public seed `PK.seed`. -/
  pkSeed : prims.PkSeed
  /-- Hypertree root `PK.root`. -/
  pkRoot : prims.Y

/-- The SLH-DSA secret key: it carries the public material for signing. -/
structure SecretKey (prims : Primitives p) where
  /-- Secret seed `SK.seed`. -/
  skSeed : prims.SkSeed
  /-- Message-PRF key `SK.prf`. -/
  skPrf : prims.SkPrf
  /-- Public seed `PK.seed`. -/
  pkSeed : prims.PkSeed
  /-- Hypertree root `PK.root`. -/
  pkRoot : prims.Y

/-- An SLH-DSA signature: randomizer `R`, FORS signature, and hypertree signature
(`R ‖ SIG_FORS ‖ SIG_HT`). -/
abbrev Signature (prims : Primitives p) := prims.Y × ForsSig p prims × HtSig p prims

/-! ### Message-digest split (FIPS 205 §9) -/

/-- Split the message digest into the FORS message `md` and the hypertree leaf index `idxLeaf`
(reduced mod `2^{h'}`). For `d = 1` the tree-index field is empty, so the tree index is `0` and
omitted. -/
def splitDigest (p : Params) (digest : Bytes p.m) : List Byte × ℕ :=
  let bytes := digest.toList
  (bytes.take p.digestBytes,
    toInt ((bytes.drop (p.digestBytes + p.treeIdxBytes)).take p.leafIdxBytes) % 2 ^ p.hp)

theorem splitDigest_snd_lt (p : Params) (digest : Bytes p.m) :
    (splitDigest p digest).2 < 2 ^ p.hp := by
  simp only [splitDigest]
  exact Nat.mod_lt _ (by positivity)

/-- The FORS base address keyed to the per-message hypertree leaf `idxLeaf` (FIPS 205 Alg 19). -/
def forsAdrsOf (idxLeaf : ℕ) : Adrs :=
  ((Adrs.zero.setTreeAddress 0).setTypeAndClear .forsTree).setKeyPairAddress idxLeaf

/-! ### Internal algorithms (FIPS 205 §9) -/

/-- SLH-DSA internal key generation (FIPS 205 Algorithm 18): the public root is the hypertree
root of the single tree. -/
def slhKeygenInternal (prims : Primitives p) (skSeed : prims.SkSeed) (skPrf : prims.SkPrf)
    (pkSeed : prims.PkSeed) : PublicKey prims × SecretKey prims :=
  let pkRoot := htRoot prims skSeed pkSeed Adrs.zero 0
  (⟨pkSeed, pkRoot⟩, ⟨skSeed, skPrf, pkSeed, pkRoot⟩)

/-- SLH-DSA internal signing (FIPS 205 Algorithm 19): derive `R` and the digest, sign the FORS
public key with the hypertree. -/
def slhSignInternal (prims : Primitives p) (msg : List Byte) (sk : SecretKey prims)
    (addrnd : prims.Y) : Signature prims :=
  let R := prims.PRFmsg sk.skPrf addrnd msg
  let digest := prims.Hmsg R sk.pkSeed sk.pkRoot msg
  let idxLeaf := (splitDigest p digest).2
  let md := (splitDigest p digest).1
  let fAdrs := forsAdrsOf idxLeaf
  (R, forsSign prims md sk.skSeed sk.pkSeed fAdrs,
    htSign prims (forsPkGen prims sk.skSeed sk.pkSeed fAdrs) sk.skSeed sk.pkSeed Adrs.zero 0
      idxLeaf)

/-- SLH-DSA internal verification (FIPS 205 Algorithm 20): recompute the FORS public key and
verify it against the hypertree. -/
def slhVerifyInternal (prims : Primitives p) [DecidableEq prims.Y] (msg : List Byte)
    (sig : Signature prims) (pk : PublicKey prims) : Bool :=
  let digest := prims.Hmsg sig.1 pk.pkSeed pk.pkRoot msg
  let idxLeaf := (splitDigest p digest).2
  let md := (splitDigest p digest).1
  let fAdrs := forsAdrsOf idxLeaf
  htVerify prims (forsPkFromSig prims sig.2.1 md pk.pkSeed fAdrs) sig.2.2 pk.pkSeed Adrs.zero 0
    idxLeaf pk.pkRoot

/-- **Deterministic correctness core**: an honestly generated signature verifies, for every
choice of seeds and randomizer. Composes FORS correctness (`forsPkFromSig_forsSign`) with
hypertree correctness (`htVerify_htSign`). -/
theorem slhVerifyInternal_slhSignInternal (prims : Primitives p) [DecidableEq prims.Y]
    (msg : List Byte) (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed)
    (addrnd : prims.Y) :
    slhVerifyInternal prims msg
        (slhSignInternal prims msg (slhKeygenInternal prims skSeed skPrf pkSeed).2 addrnd)
        (slhKeygenInternal prims skSeed skPrf pkSeed).1 = true := by
  simp only [slhKeygenInternal, slhSignInternal, slhVerifyInternal]
  rw [forsPkFromSig_forsSign]
  exact htVerify_htSign prims _ skSeed pkSeed Adrs.zero 0 _ (splitDigest_snd_lt p _)

end SLHDSA
