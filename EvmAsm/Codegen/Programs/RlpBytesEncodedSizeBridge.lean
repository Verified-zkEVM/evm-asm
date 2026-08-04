/-
  EvmAsm.Codegen.Programs.RlpBytesEncodedSizeBridge

  GH #11341 — the **inheritance bridge** for the `rlp_bytes_encoded_size`
  Correspondence row (`EvmAsm/Progress/Correspondence.lean`), which carried
  verdict `.agrees` on basis `.machineOnly`.

  THE GAP THIS CLOSES. `rlpBytesEncodedSize_spec` (`RlpBytesEncodedSizeSAsm.lean:539`)
  states its post as `a0 = rbesSize xs len`, and `rbesSize` (`:89`) is **standalone
  arithmetic** — an `if`-ladder on `len` against the literals `1`/`56`, not
  `(encodeBytes xs).length`. So the routine was proven to match a *local restatement*
  of RLP's size rule, and the executable differential over the shared model
  (`lake exe correspondence-check rlp`, 3757 records) did **not** transfer: a
  transcription slip in `rbesSize` would leave the proof closing, the differential
  green, and the verdict reading `.agrees`.

  WHAT IS HERE, AND WHAT IS DELIBERATELY NOT. Per `docs/agents/spec-correspondence.md`
  §4, closing a `machine-only` row means a lemma
  `<local predicate> ↔ <shared-model statement>` — **the bridge is the artefact, not
  a re-proof**. `rbesSize_eq_encodeBytes_length` is that lemma, and
  `rlpBytesEncodedSize_encode_spec` is the one-rewrite consumer that restates the
  existing triple's post over `EvmAsm.EL.RLP.encodeBytes`. The machine-level proof in
  `RlpBytesEncodedSizeSAsm.lean` is **untouched**. This mirrors
  `risSpan_eq_encode_length` / `rlp_item_size_form_own_spec_within`
  (`RlpSpliceHelperSpec.lean:610`/`:637`), the pattern the method doc cites by name.

  THE LOAD-BEARING SUBLEMMA. `u64ByteLen_eq_toBytesBE_length` — the guest's
  9-way `if`-ladder length-of-length (`RlpListEncodedSizeSAsm.lean:70`) IS the
  minimal big-endian byte count `(Nat.toBytesBE ·).length`. `Nat.toBytesBE_length_le`
  (`EL/RLP/Properties.lean:2111`) already gave the upper bound; the converse
  (`lt_pow_toBytesBE_length`) was missing and is proved here. It is stated
  independently of `rbesSize` because `rlp_list_encoded_size` — the sibling
  `.machineOnly` row — needs exactly the same fact.

  WHY THE DOMAIN IS FULL, not restricted. `rbesSize` and `encodeBytes` agree on
  every input: `xs = []` (→ 1), the two singleton cases either side of `0x80`
  (→ 1 / 2), `2 ≤ len ≤ 55` (→ len+1) and `len ≥ 56` (→ len + lenOfLen + 1). The
  only side condition is `hbound`.

  ⭐ **`hbound` is a representability guard, not a domain restriction**, and the two
  are graded differently on purpose. `domainRestricted` is for a spec that *excludes
  inputs the reference accepts* — a real coverage gap a caller must respect, like
  `rlp_item_size`'s `SpanForm`. `hbound` excludes nothing the routine could ever be
  handed: a `List Byte` of length ≥ `2 ^ 64 - 9` has no representation on the target,
  so the hypothesis is unfalsifiable in any execution rather than carving inputs out
  of the claim. Every byte string the guest can physically be called on is covered,
  hence `.agrees`. The general rule: ask whether the condition rules out a *reachable*
  input, not whether the statement has a hypothesis.
-/

import EvmAsm.Codegen.Programs.RlpBytesEncodedSizeSAsm
import EvmAsm.EL.RLP.Properties

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.EL.RLP

namespace RlpBytesEncodedSizeSAsm

open RlpListEncodedSizeSAsm (u64ByteLen)

/-! ## The minimal big-endian byte length, pinned exactly

    `Nat.toBytesBE_length_le` bounds the encoding above; these two pin it. -/

/-- **The missing converse of `Nat.toBytesBE_length_le`**: the minimal big-endian
    encoding of `n` is always wide enough to hold `n`. Induction follows
    `toBytesBE`'s own division recursion. -/
theorem lt_pow_toBytesBE_length (n : Nat) : n < 256 ^ (Nat.toBytesBE n).length := by
  induction n using Nat.toBytesBE.induct with
  | case1 => simp [Nat.toBytesBE]
  | case2 m _hlt ih =>
    rw [Nat.toBytesBE_succ, List.length_append]
    simp only [List.length_cons, List.length_nil, Nat.zero_add]
    have hdm : 256 * ((m + 1) / 256) + (m + 1) % 256 = m + 1 :=
      Nat.div_add_mod (m + 1) 256
    have hmod : (m + 1) % 256 < 256 := Nat.mod_lt _ (by omega)
    have hpow : 256 ^ ((Nat.toBytesBE ((m + 1) / 256)).length + 1)
        = 256 ^ (Nat.toBytesBE ((m + 1) / 256)).length * 256 := Nat.pow_succ _ _
    omega

/-- The exact length, from a two-sided bound. Together with
    `Nat.toBytesBE_length_le` this makes `(Nat.toBytesBE ·).length` computable
    from any bracketing pair of powers. -/
theorem toBytesBE_length_eq_of_bounds (n k : Nat)
    (hlt : n < 256 ^ k) (hge : k = 0 ∨ 256 ^ (k - 1) ≤ n) :
    (Nat.toBytesBE n).length = k := by
  have hle : (Nat.toBytesBE n).length ≤ k := Nat.toBytesBE_length_le n k hlt
  rcases hge with rfl | hge
  · omega
  · by_contra hne
    have hlt' : (Nat.toBytesBE n).length ≤ k - 1 := by omega
    have hmono : 256 ^ (Nat.toBytesBE n).length ≤ 256 ^ (k - 1) :=
      Nat.pow_le_pow_right (by omega) hlt'
    have := lt_pow_toBytesBE_length n
    omega

/-- ⭐ **`u64ByteLen` IS the minimal big-endian byte count.** The guest's 9-way
    `if`-ladder (`RlpListEncodedSizeSAsm.lean:70`) and the shared model's
    `Nat.toBytesBE` agree on the whole `Word` domain — the cap at 8 never binds
    because a `Word` is below `256 ^ 8`. This is the fact both `.machineOnly`
    size rows rest on. -/
theorem u64ByteLen_eq_toBytesBE_length (v : Word) :
    u64ByteLen v = (Nat.toBytesBE v.toNat).length := by
  have hv : v.toNat < 2 ^ 64 := v.isLt
  symm
  unfold u64ByteLen
  split_ifs with h0 h1 h2 h3 h4 h5 h6 h7
  · exact toBytesBE_length_eq_of_bounds _ 0 (by norm_num at h0 ⊢; omega) (Or.inl rfl)
  · exact toBytesBE_length_eq_of_bounds _ 1 (by norm_num at h1 ⊢; omega)
      (Or.inr (by norm_num at h0 ⊢; omega))
  · exact toBytesBE_length_eq_of_bounds _ 2 (by norm_num at h2 ⊢; omega)
      (Or.inr (by norm_num at h1 ⊢; omega))
  · exact toBytesBE_length_eq_of_bounds _ 3 (by norm_num at h3 ⊢; omega)
      (Or.inr (by norm_num at h2 ⊢; omega))
  · exact toBytesBE_length_eq_of_bounds _ 4 (by norm_num at h4 ⊢; omega)
      (Or.inr (by norm_num at h3 ⊢; omega))
  · exact toBytesBE_length_eq_of_bounds _ 5 (by norm_num at h5 ⊢; omega)
      (Or.inr (by norm_num at h4 ⊢; omega))
  · exact toBytesBE_length_eq_of_bounds _ 6 (by norm_num at h6 ⊢; omega)
      (Or.inr (by norm_num at h5 ⊢; omega))
  · exact toBytesBE_length_eq_of_bounds _ 7 (by norm_num at h7 ⊢; omega)
      (Or.inr (by norm_num at h6 ⊢; omega))
  · exact toBytesBE_length_eq_of_bounds _ 8 (by norm_num; omega)
      (Or.inr (by norm_num at h7 ⊢; omega))

/-! ## The bridge -/

/-- ⭐ **The encoded-size bridge.** The guest's standalone arithmetic `rbesSize`
    is exactly the length of the shared model's `encodeBytes` — so
    `rlp_bytes_encoded_size` inherits the RLP differential instead of resting on a
    local restatement.

    `hbound` is the 64-bit non-overflow guard (the widest encoding adds a 1-byte
    prefix plus at most 8 length bytes, hence `+ 9`); it is a resource condition on
    the register, not a restriction on which byte strings are covered. -/
theorem rbesSize_eq_encodeBytes_length (xs : List Byte) (len : Word)
    (hlen : xs.length = len.toNat) (hbound : xs.length + 9 < 2 ^ 64) :
    rbesSize xs len = BitVec.ofNat 64 (encodeBytes xs).length := by
  match xs with
  | [] =>
    -- `encodeBytes [] = [0x80]`; the guest takes the `< 56` arm at `len = 0`.
    have hlen0 : len = (0 : Word) := by
      apply BitVec.eq_of_toNat_eq
      simpa using hlen.symm
    subst hlen0
    decide
  | [b] =>
    have hlen1 : len = (1 : Word) := by
      apply BitVec.eq_of_toNat_eq
      simpa using hlen.symm
    subst hlen1
    by_cases hb : b.toNat < 128
    · -- single byte below 0x80 encodes as itself
      simp [rbesSize, encodeBytes, hb]
    · -- otherwise a 0x81 prefix
      have hb' : ¬ b.toNat < 0x80 := by omega
      norm_num [rbesSize, encodeBytes, hb, hb']
      decide
  | a :: b :: t =>
    -- Two or more bytes: the singleton special case is out, so both sides are
    -- driven purely by the length.
    have hge2 : 2 ≤ len.toNat := by simp at hlen; omega
    have hne1 : ¬ (len = (1 : Word) ∧ ((a :: b :: t).getD 0 0).toNat < 128) := by
      rintro ⟨rfl, -⟩
      simp at hge2
    by_cases hshort : BitVec.ult len (56 : Word)
    · -- `len ≤ 55`: a single 0x80+len header byte
      have hlt56 : len.toNat < 56 := by simpa [BitVec.ult] using hshort
      have hle55 : (a :: b :: t).length ≤ 55 := by omega
      rw [rbesSize, if_neg hne1, if_pos hshort]
      rw [encodeBytes_short_of_length_ne_one _ hle55 (by simp)]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, List.length_append,
        List.length_cons, List.length_nil, show ((1 : Word)).toNat = 1 from rfl]
      simp only [List.length_cons] at hlen hbound
      omega
    · -- `len ≥ 56`: a 0xB7+lenOfLen header plus the big-endian length field
      have hge56 : 56 ≤ len.toNat := by
        simpa [BitVec.ult, Nat.not_lt] using hshort
      have hgt55 : ¬ ((a :: b :: t).length ≤ 55) := by omega
      have hL : (Nat.toBytesBE (a :: b :: t).length).length = u64ByteLen len := by
        rw [u64ByteLen_eq_toBytesBE_length, hlen]
      have hLle : u64ByteLen len ≤ 8 := RlpListEncodedSizeSAsm.u64ByteLen_le len
      rw [rbesSize, if_neg hne1, if_neg hshort]
      have henc : (encodeBytes (a :: b :: t)).length
          = 1 + (Nat.toBytesBE (a :: b :: t).length).length
              + (a :: b :: t).length := by
        rw [show encodeBytes (a :: b :: t)
              = [BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE (a :: b :: t).length).length)]
                  ++ Nat.toBytesBE (a :: b :: t).length ++ (a :: b :: t) from by
          simp only [encodeBytes]
          rw [if_neg hgt55]]
        simp [List.length_append]
        omega
      rw [henc, hL]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, Nat.mod_eq_of_lt, hlen]
      omega

/-! ## Non-vacuity pins

    A bridge between two definitions is worth exactly as much as the reader's
    confidence that both sides are the intended ones, so both sides are evaluated
    at every boundary the two formulas branch on. If `rbesSize` and `encodeBytes`
    were ever "bridged" by a shared mistake, these would move together — but a
    transcription slip in one of the three arms shows up here immediately, which
    is the failure the `machineOnly` grade was warning about. -/

section Pins

private def z (n : Nat) : List Byte := List.replicate n (0 : Byte)

-- empty, and the two singleton arms either side of 0x80
#guard rbesSize [] 0 == BitVec.ofNat 64 (encodeBytes []).length
#guard rbesSize [(0x7f : Byte)] 1 == BitVec.ofNat 64 (encodeBytes [(0x7f : Byte)]).length
#guard rbesSize [(0x80 : Byte)] 1 == BitVec.ofNat 64 (encodeBytes [(0x80 : Byte)]).length
-- the short/long form boundary at 55/56
#guard rbesSize (z 55) 55 == BitVec.ofNat 64 (encodeBytes (z 55)).length
#guard rbesSize (z 56) 56 == BitVec.ofNat 64 (encodeBytes (z 56)).length
-- the length-of-length boundary at 255/256 (1-byte → 2-byte length field)
#guard rbesSize (z 255) 255 == BitVec.ofNat 64 (encodeBytes (z 255)).length
#guard rbesSize (z 256) 256 == BitVec.ofNat 64 (encodeBytes (z 256)).length
-- and the sublemma at the same boundaries, including the `u64ByteLen 0 = 0` corner
#guard u64ByteLen 0 == (Nat.toBytesBE (0 : Word).toNat).length
#guard u64ByteLen 255 == (Nat.toBytesBE (255 : Word).toNat).length
#guard u64ByteLen 256 == (Nat.toBytesBE (256 : Word).toNat).length
#guard u64ByteLen (BitVec.ofNat 64 (2 ^ 56)) ==
  (Nat.toBytesBE ((BitVec.ofNat 64 (2 ^ 56)) : Word).toNat).length

end Pins

/-! ## The consumer — the same triple, stated over the shared model

    Availability is not use (method doc §4): a bridge lemma that exists but is not
    consumed does not earn the `.bridged` grade. This is the theorem the
    Correspondence row now names. -/

variable (ptr len ret : Word) (xs : List (BitVec 8))

/-- **`rlp_bytes_encoded_size` at its linked address, against `EL.RLP`.** Identical
    to `rlpBytesEncodedSize_spec` except that `a0` is pinned to
    `(encodeBytes xs).length` — the shared-model function the differential covers —
    rather than to the local `rbesSize`. One rewrite, then the untouched machine
    proof. -/
theorem rlpBytesEncodedSize_encode_spec
    (hlenXs : xs.length = len.toNat)
    (hbound : xs.length + 9 < 2 ^ 64)
    (halignPtr : ptr.toNat % 8 = 0)
    (hvalidPtr : ∀ k, k < len.toNat →
      isValidByteAccess (ptr + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 48 rbesBase ret
      (CodeReq.ofProg rbesBase rlpBytesEncodedSize_prog)
      (((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        bytesRegion ptr xs)
      (((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 (encodeBytes xs).length) **
        ((.x11 : Reg) ↦ᵣ len) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        bytesRegion ptr xs) := by
  rw [← rbesSize_eq_encodeBytes_length xs len hlenXs hbound]
  exact rlpBytesEncodedSize_spec ptr len ret xs hlenXs halignPtr hvalidPtr halignRet

end RlpBytesEncodedSizeSAsm

end EvmAsm.Codegen
