/-
  EvmAsm.Rv64.RLP.ContentToU256BeBridge

  GH #11341 — the **inheritance bridge** for the `rlp_content_to_u256_be`
  Correspondence row. Third of the four.

  THE GAP THIS CLOSES. `rlp_content_to_u256_be_spec_within`
  (`ContentToU256Be.lean:1040`) states its four-way outcome entirely in *local*
  vocabulary: the value is a right-aligned `copyN` into a 32-byte buffer (`:492`),
  and the canonicality rule is the literal byte test `getByteAt srcBytes srcOff = 0`
  (`Rv64/ByteOps.lean:261`). No `decode`, no `RLPItem`, no `fromBytesBE` appears in
  the statement — so the RLP differential did not transfer, and a drift between that
  byte test and the reference's leading-zero rule would have been invisible.

  WHAT THE SHARED-MODEL SIDE IS. `EvmAsm.EL.RLP.decodeScalar` (`EL/RLP/Scalar.lean:26`)
  is the model function whose docstring pins it to execution-specs
  `_deserialize_to_uint`: decode one item, reject `data.headD 1 = 0` as non-canonical,
  otherwise read `Nat.fromBytesBE`. That is exactly the rule the guest implements, and
  `decodeScalar` bottoms out in `decodeFully`/`decode`, so a bridge to it inherits the
  3757-record differential.

  ⚠️ THE ONE ASYMMETRY, STATED RATHER THAN PAPERED OVER. `decodeScalar` is **untyped** —
  it returns an unbounded `Nat`. The guest is the **U256** instance and rejects
  `len > 32` with status 2, which `decodeScalar` alone does not model; that rejection
  corresponds to `class_.from_be_bytes` at `U256` on the Python side, one layer up from
  `decodeScalar`. So the bridge below is stated for `len ≤ 32` and the `len > 32` arm is
  deliberately **not** claimed to follow from `decodeScalar`. This is the existing
  "U256 fields only" caveat, now precise about which arm it applies to rather than
  attached to the row as a whole.

  THREE PIECES:
  * `fromBytesBE_replicate_zero_append` — leading zero bytes do not change a
    big-endian value. This is why right-alignment is value-preserving.
  * `copyN_rightAlign_eq` — the guest's 32-byte output IS
    `replicate (32 - len) 0 ++ content`. Falls out of the existing `copyN_eq_append`
    (`ContentToU256Be.lean:516`).
  * `ctu256_value_eq_decodeScalar` / `ctu256_reject_iff_decodeScalar_none` — the value
    and the rejection, both against `decodeScalar (encodeBytes content)`.

  `ContentToU256Be.lean` is **untouched** — the bridge is the artefact, not a re-proof
  (`docs/agents/spec-correspondence.md` §4).
-/

import EvmAsm.Rv64.RLP.ContentToU256Be
import EvmAsm.EL.RLP.Scalar

namespace EvmAsm.Rv64.RLP

open EvmAsm.EL.RLP

/-! ## Right-alignment is value-preserving -/

/-- Leading zero bytes do not change a big-endian value. The reason the guest may
    right-align a short payload into a fixed 32-byte buffer and still denote the
    same number. -/
theorem fromBytesBE_replicate_zero_append (k : Nat) (xs : List Byte) :
    Nat.fromBytesBE (List.replicate k (0 : Byte) ++ xs) = Nat.fromBytesBE xs := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, Nat.fromBytesBE, ih]
    simp

/-- Corollary: an all-zero buffer denotes `0`, whatever its width. -/
theorem fromBytesBE_replicate_zero (k : Nat) :
    Nat.fromBytesBE (List.replicate k (0 : Byte)) = 0 := by
  have := fromBytesBE_replicate_zero_append k ([] : List Byte)
  rwa [List.append_nil, Nat.fromBytesBE_nil] at this

/-- The guest's 32-byte output buffer, in closed form: `32 - len` zero bytes followed
    by the `len` content bytes. Immediate from the existing `copyN_eq_append`. -/
theorem copyN_rightAlign_eq (srcBytes : List Byte) (srcOff len : Nat)
    (hlen : len ≤ 32) (hs : srcOff + len ≤ srcBytes.length) :
    copyN (List.replicate 32 (0 : Byte)) srcBytes (32 - len) srcOff len
      = List.replicate (32 - len) (0 : Byte) ++ (srcBytes.drop srcOff).take len := by
  rw [copyN_eq_append _ _ _ _ _ (by simp; omega) hs]
  have h1 : (List.replicate 32 (0 : Byte)).take (32 - len) = List.replicate (32 - len) 0 := by
    rw [List.take_replicate]
    congr 1
    omega
  have h2 : (List.replicate 32 (0 : Byte)).drop (32 - len + len) = [] := by
    rw [List.drop_eq_nil_iff]
    simp
    omega
  rw [h1, h2, List.append_nil]

/-- ⭐ **The value bridge.** The 32-byte buffer the routine writes denotes exactly the
    big-endian value of the content it was given. -/
theorem fromBytesBE_ctu256_out (srcBytes : List Byte) (srcOff len : Nat)
    (hlen : len ≤ 32) (hs : srcOff + len ≤ srcBytes.length) :
    Nat.fromBytesBE (copyN (List.replicate 32 (0 : Byte)) srcBytes (32 - len) srcOff len)
      = Nat.fromBytesBE ((srcBytes.drop srcOff).take len) := by
  rw [copyN_rightAlign_eq srcBytes srcOff len hlen hs,
    fromBytesBE_replicate_zero_append]

/-! ## The canonicality rule, against `decodeScalar`

    `decodeScalar` is stated over the RLP *encoding* of the content, since that is the
    boundary the model works at; the guest is handed the already-decoded content. The
    two are tied by `decode_encode_bytes`. -/

/-- `decodeScalar` on the encoding of `content`, unfolded: it succeeds exactly when the
    leading byte is not zero, and then returns the big-endian value. -/
theorem decodeScalar_encodeBytes (content : List Byte)
    (hlen : content.length < 256 ^ 8) :
    decodeScalar (encodeBytes content)
      = if content.headD 1 = 0 then none else some (Nat.fromBytesBE content, []) := by
  have hd : decode (encodeBytes content) = some (.bytes content, []) := by
    have := decode_encode_bytes content hlen
    simpa [encode] using this
  unfold decodeScalar
  rw [hd]
  rfl

/-- The guest's byte test IS the model's leading-zero test, on the content window. -/
theorem getByteAt_eq_headD (srcBytes : List Byte) (srcOff len : Nat)
    (hpos : 0 < len) (hs : srcOff + len ≤ srcBytes.length) :
    (getByteAt srcBytes srcOff = 0) ↔ (((srcBytes.drop srcOff).take len).headD 1 = 0) := by
  have hlt : srcOff < srcBytes.length := by omega
  have hd : (srcBytes.drop srcOff).take len
      = srcBytes[srcOff]'hlt :: ((srcBytes.drop (srcOff + 1)).take (len - 1)) := by
    cases len with
    | zero => omega
    | succ k =>
      rw [List.drop_eq_getElem_cons hlt, List.take_succ_cons]
      simp
  rw [hd, getByteAt]
  simp [hlt]

/-! ## The two model-facing statements the row now rests on -/

/-- ⭐ **Rejection agrees with the model.** For a nonempty content window inside the
    buffer, the routine's status-3 condition holds exactly when `decodeScalar` rejects
    the corresponding RLP item as non-canonical. -/
theorem ctu256_reject_iff_decodeScalar_none (srcBytes : List Byte) (srcOff len : Nat)
    (hpos : 0 < len) (hs : srcOff + len ≤ srcBytes.length)
    (hlen8 : len < 256 ^ 8) :
    getByteAt srcBytes srcOff = 0
      ↔ decodeScalar (encodeBytes ((srcBytes.drop srcOff).take len)) = none := by
  have hclen : ((srcBytes.drop srcOff).take len).length < 256 ^ 8 := by
    have : ((srcBytes.drop srcOff).take len).length ≤ len := by
      simp [List.length_take]
    omega
  rw [decodeScalar_encodeBytes _ hclen, getByteAt_eq_headD srcBytes srcOff len hpos hs]
  split <;> simp_all

/-- ⭐ **Acceptance agrees with the model, value and all.** For an accepted nonempty
    window, `decodeScalar` returns precisely the big-endian value of the 32-byte buffer
    the routine writes. -/
theorem ctu256_accept_decodeScalar (srcBytes : List Byte) (srcOff len : Nat)
    (hpos : 0 < len) (hlen : len ≤ 32) (hs : srcOff + len ≤ srcBytes.length)
    (hne : getByteAt srcBytes srcOff ≠ 0) :
    decodeScalar (encodeBytes ((srcBytes.drop srcOff).take len))
      = some (Nat.fromBytesBE
          (copyN (List.replicate 32 (0 : Byte)) srcBytes (32 - len) srcOff len), []) := by
  have hclen : ((srcBytes.drop srcOff).take len).length < 256 ^ 8 := by
    have h1 : ((srcBytes.drop srcOff).take len).length ≤ len := by simp [List.length_take]
    have : (32 : Nat) < 256 ^ 8 := by norm_num
    omega
  have hhead : ¬ (((srcBytes.drop srcOff).take len).headD 1 = 0) := by
    rw [← getByteAt_eq_headD srcBytes srcOff len hpos hs]; exact hne
  rw [decodeScalar_encodeBytes _ hclen, if_neg hhead,
    fromBytesBE_ctu256_out srcBytes srcOff len hlen hs]

/-- **The empty window is the canonical zero**, matching `decodeScalar`'s treatment of
    the empty byte string (`headD 1 = 1 ≠ 0`), and the routine's `len = 0 → a0 = 0`
    arm with an all-zero output. Stated so all three accepting arms are covered, not
    just the interesting one. -/
theorem ctu256_empty_decodeScalar :
    decodeScalar (encodeBytes ([] : List Byte)) = some (0, [])
      ∧ Nat.fromBytesBE (List.replicate 32 (0 : Byte)) = 0 := by
  refine ⟨?_, fromBytesBE_replicate_zero 32⟩
  rw [decodeScalar_encodeBytes [] (by norm_num)]
  simp [Nat.fromBytesBE_nil]

/-! ## Non-vacuity pins

    Both sides at the boundaries: empty, a 1-byte value, a full 32-byte value, and a
    leading-zero payload that must be rejected. -/

section Pins

private def w (bs : List Byte) : List Byte := bs

#guard decodeScalar (encodeBytes []) == some (0, [])
#guard decodeScalar (encodeBytes [(0x00 : Byte)]) == none
#guard decodeScalar (encodeBytes [(0x00 : Byte), (0x01 : Byte)]) == none
#guard decodeScalar (encodeBytes [(0x01 : Byte)]) == some (1, [])
#guard decodeScalar (encodeBytes [(0x01 : Byte), (0x00 : Byte)]) == some (256, [])
-- right-alignment really is value-preserving at the 32-byte width
#guard Nat.fromBytesBE (copyN (List.replicate 32 (0 : Byte))
    [(0x01 : Byte), (0x02 : Byte)] 30 0 2) == 258
#guard Nat.fromBytesBE (List.replicate 32 (0 : Byte)) == 0
-- and the guest's byte test matches the model's leading-zero test
#guard (getByteAt [(0x00 : Byte), (0x01 : Byte)] 0 == 0)
  == (decodeScalar (encodeBytes [(0x00 : Byte), (0x01 : Byte)]) == none)
#guard (getByteAt [(0x01 : Byte), (0x00 : Byte)] 0 == 0)
  == (decodeScalar (encodeBytes [(0x01 : Byte), (0x00 : Byte)]) == none)

end Pins

/-! ## The consumer — the same triple, outcomes stated over `decodeScalar`

    Availability is not use (`docs/agents/spec-correspondence.md` §4): a bridge lemma
    that exists but is not consumed does not earn the `.bridged` grade. This restates
    `rlp_content_to_u256_be_spec_within`'s two *interesting* arms — the non-canonical
    rejection and the accepted value — in shared-model vocabulary. The proof is a
    post-weakening over the untouched machine triple; no step count, footprint or
    precondition changes.

    Scoped to `len ≤ 32`, which drops the status-2 arm: that arm is the U256 width
    rejection, and `decodeScalar` is untyped, so it is the one outcome the model does
    not speak to. Saying so with a hypothesis is more honest than inventing a model
    function to match it. -/

/-- ⭐ **`rlp_content_to_u256_be` against `EL.RLP.decodeScalar`, on the U256 domain.**
    Same triple, same bound; the outcome disjunction now reads:
    `len = 0` → zero, `decodeScalar … = none` → status 3, otherwise status 0 with the
    output buffer denoting exactly the value `decodeScalar` returns. -/
theorem rlp_content_to_u256_be_scalar_spec_within
    (base srcBase outPtr raVal x5Old x6Old x7Old x28Old x29Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat)
    (hlen64 : len < 2 ^ 64) (hle32 : len ≤ 32)
    (hsalign : srcBase.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64) (hoover : outPtr.toNat + 32 ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hdvalid : ∀ k, k < 32 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * len + 16) base (raVal &&& ~~~1) (rlp_content_to_u256_be_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
       (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
       bytesRegion srcBase srcBytes ** memOwnU256 outPtr)
      (((.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ outPtr) ** regOwn .x5 ** regOwn .x6 **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) **
       (fun h =>
         (((.x10 ↦ᵣ (2 : Word)) ** memOwnU256 outPtr ** ⌜32 < len⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) ** bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) **
            ⌜len = 0⌝) h) ∨
         (((.x10 ↦ᵣ (3 : Word)) ** memOwnU256 outPtr **
            ⌜0 < len ∧
              decodeScalar (encodeBytes ((srcBytes.drop srcOff).take len)) = none⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) **
            bytesRegion outPtr (copyN (List.replicate 32 (0 : BitVec 8)) srcBytes (32 - len) srcOff len) **
            ⌜0 < len ∧
              decodeScalar (encodeBytes ((srcBytes.drop srcOff).take len))
                = some (Nat.fromBytesBE
                    (copyN (List.replicate 32 (0 : BitVec 8)) srcBytes (32 - len) srcOff len),
                  [])⌝) h))) := by
  have hlen8 : len < 256 ^ 8 := by
    have : (32 : Nat) < 256 ^ 8 := by norm_num
    omega
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_)
    (rlp_content_to_u256_be_spec_within base srcBase outPtr raVal x5Old x6Old x7Old
      x28Old x29Old srcBytes srcOff len hlen64 hsalign hoalign hslen hsover hoover
      hsvalid hdvalid)
  refine sepConj_mono_right (fun h' hbody => ?_) h hq
  rcases hbody with h1 | h2 | h3 | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · -- non-canonical: rewrite the guest byte test into `decodeScalar … = none`
    refine Or.inr (Or.inr (Or.inl ?_))
    refine sepConj_mono_right (fun h'' hb => ?_) h' h3
    obtain ⟨hpure, hrest⟩ := (sepConj_pure_right h'').1 hb
    refine (sepConj_pure_right h'').2 ⟨hpure, ?_⟩
    exact ⟨hrest.1, (ctu256_reject_iff_decodeScalar_none srcBytes srcOff len hrest.1
      hslen hlen8).1 hrest.2⟩
  · -- accepted: the output buffer denotes exactly the value the model returns
    refine Or.inr (Or.inr (Or.inr ?_))
    refine sepConj_mono_right (fun h'' hb => ?_) h' h4
    obtain ⟨hpure, hrest⟩ := (sepConj_pure_right h'').1 hb
    refine (sepConj_pure_right h'').2 ⟨hpure, ?_⟩
    exact ⟨hrest.1, ctu256_accept_decodeScalar srcBytes srcOff len hrest.1 hle32 hslen
      hrest.2⟩

end EvmAsm.Rv64.RLP
