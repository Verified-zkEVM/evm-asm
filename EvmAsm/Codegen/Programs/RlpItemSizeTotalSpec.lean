/-
  EvmAsm.Codegen.Programs.RlpItemSizeTotalSpec

  **`rlp_item_size`, total dispatch** (GH #10780) — one triple covering all five
  RLP prefix forms, with no `SpanForm` gate.

  ## What this adds, and why it is a *new* theorem

  `RlpSpliceHelperSpec.rlp_item_size_spec_within` is the constant-time statement
  the `rlp_item_span` / `mpt_splice_slot` compositions consume: `cpsTripleWithin
  12`, clobbering only `t0`/`t1`, gated on `SpanForm` (the three short forms).
  Nothing about it is touched here. This module *adds* a second, total statement
  beside it, in the same way #11922 added `rlpItemDecodeStrict` beside
  `rlpItemDecode` rather than editing a relation with dozens of consumers.

  A total statement cannot be the covered one with a widened gate, for two
  independent reasons — both properties of the machine, not of how the proof is
  written:

  | | covered forms (`SpanForm`) | long forms |
  |---|---|---|
  | step bound | `12` — a *literal* | `7 * lenOfLen + 17` / `+ 18` — *variable* |
  | clobbers   | `t0`, `t1` only | `t0, t1, t2, t3, t4, t5, t6` |

  So the total triple necessarily carries (a) a prefix-dependent step bound,
  `risStepsTotal`, and (b) the larger seven-register footprint. Widening the
  existing theorem to either shape would break every consumer; hence a sibling.

  ## The five arms

  The three short arms come from `RlpSpliceHelperSpec` (`5`, `8` and `12` steps,
  each clobbering only `t0`/`t1`); the two long arms from
  `RlpItemSizeLongSpec`. The short arms are framed up to the seven-register
  footprint — `t2`/`t3`–`t6` are threaded through untouched and then released to
  `regOwn`, which is sound precisely because a register that is never written
  still satisfies `regOwn` if it was owned going in — and their step bounds are
  weakened to the common `12`.

  For the long arms the `..._encode_length_spec_within` corollaries are used, not
  the raw pinned arms, so that all five arms agree on the post
  `x10 ↦ BitVec.ofNat 64 (EL.RLP.encode item).length`. Those corollaries want a
  successful `readLength` alongside the successful `decode`; that is *derived*
  here (`readLength_of_decode_long{Bytes,List}`) from `h_decode` alone, via the
  contrapositive of `decodeAux_long_{bytes,list}_readLength_none`, so the total
  theorem's hypothesis list stays at `decode bs = some (item, rest)`.

  ## ⚠️ `h_nover` is a genuine ABI obligation

  The two long arms require `ptr.toNat + bs.length ≤ 2 ^ 64` — the buffer must not
  wrap the address space — because their length loop walks `lenOfLen` bytes past
  the prefix with an incrementing address. The short arms never need it (they read
  byte 0 only). The total theorem therefore carries it as a hypothesis. It is a
  resource/ABI condition on the *caller's buffer*, discharged wherever the routine
  is actually invoked; it excludes no prefix range and no RLP input, so the
  dispatch stays total over the head byte.

  ## Scope

  Proof only. `SpanForm`, `risSpan`, `rlp_item_size_spec_within` and
  `rlp_item_size_form_own_spec_within` are unchanged, and no registry row is
  re-graded here.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; default elaboration budget.
-/

import EvmAsm.EL.RLP.LongForm
import EvmAsm.Codegen.Programs.RlpSpliceHelperSpec
import EvmAsm.Codegen.Programs.RlpItemSizeLongSpec

namespace EvmAsm.Codegen

namespace RlpItemSizeTotalSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP
open EvmAsm.Codegen.RlpSpliceHelperSpec
  (rlp_item_size_single_pinned_spec_within
   rlp_item_size_short_string_pinned_spec_within
   rlp_item_size_short_list_pinned_spec_within
   decode_span_singleByte decode_span_shortBytes decode_span_shortList)
open EvmAsm.Codegen.RlpItemSizeLongSpec
  (rlp_item_size_long_string_encode_length_spec_within
   rlp_item_size_long_list_encode_length_spec_within)

/-! ## The prefix-dependent step bound -/

/-- **Steps `rlp_item_size` takes, per head byte.** Constant `12` on the three
    short forms — the literal `RlpSpliceHelperSpec.rlp_item_size_spec_within`
    already publishes, so the two statements' bounds agree wherever both apply —
    and `7 * lenOfLen + 17` / `+ 18` on the two long forms, where the routine runs
    a length-of-length loop whose trip count is read out of the prefix byte. -/
def risStepsTotal (b : BitVec 8) : Nat :=
  if b.toNat < 0xb8 then 12
  else if b.toNat < 0xc0 then 7 * rlpPrefixLongBytesLenOfLen b + 17
  else if b.toNat < 0xf8 then 12
  else 7 * rlpPrefixLongListLenOfLen b + 18

/-! ## `readLength` succeeds whenever a long-form buffer decodes

    The long arms' `..._encode_length_spec_within` corollaries take a successful
    `readLength` as a hypothesis. It is not an extra assumption: a long-form
    prefix whose `readLength` fails makes `decodeAux` — hence `decode` — `none`,
    which `h_decode` already rules out. These two lemmas turn that contrapositive
    into the `∃` the corollaries want, keeping the total theorem's hypothesis list
    down to `h_decode`. -/

/-- Long-string prefixes: `decode` succeeding forces the length-of-length read to
    succeed. Contrapositive of `decodeAux_long_bytes_readLength_none`. -/
private theorem readLength_of_decode_longBytes {bs : List Byte} {item : RLPItem}
    {rest : List Byte}
    (h_decode : decode bs = some (item, rest))
    (h_lo : 0xb8 ≤ (bs.getD 0 0).toNat) (h_hi : (bs.getD 0 0).toNat < 0xc0) :
    ∃ lenVal lenRest,
      readLength (bs.drop 1) (rlpPrefixLongBytesLenOfLen (bs.getD 0 0))
        = some (lenVal, lenRest) := by
  cases bs with
  | nil =>
    rw [decode_eq_decodeAux_length, decodeAux_nil] at h_decode
    exact absurd h_decode (by simp)
  | cons pfx rest0 =>
    rw [show (pfx :: rest0).getD 0 0 = pfx from rfl] at h_lo h_hi
    rw [show (pfx :: rest0).getD 0 0 = pfx from rfl,
        show (pfx :: rest0).drop 1 = rest0 from rfl]
    cases h_read : readLength rest0 (rlpPrefixLongBytesLenOfLen pfx) with
    | none =>
      exfalso
      have h_none := decodeAux_long_bytes_readLength_none (2 * rest0.length + 1) pfx rest0
        (by omega) (by omega) h_read
      rw [decode_cons_eq_decodeAux_fuel,
          show 2 * rest0.length + 2 = (2 * rest0.length + 1) + 1 from rfl,
          h_none] at h_decode
      exact absurd h_decode (by simp)
    | some pair =>
      -- `cases h_read : ·` has already rewritten the goal's `readLength` call to
      -- `some pair`, so the witness closes by `rfl`.
      obtain ⟨lenVal, lenRest⟩ := pair
      exact ⟨lenVal, lenRest, rfl⟩

/-- Long-list prefixes: the same, over `decodeAux_long_list_readLength_none`. -/
private theorem readLength_of_decode_longList {bs : List Byte} {item : RLPItem}
    {rest : List Byte}
    (h_decode : decode bs = some (item, rest))
    (h_lo : 0xf8 ≤ (bs.getD 0 0).toNat) :
    ∃ lenVal lenRest,
      readLength (bs.drop 1) (rlpPrefixLongListLenOfLen (bs.getD 0 0))
        = some (lenVal, lenRest) := by
  cases bs with
  | nil =>
    rw [decode_eq_decodeAux_length, decodeAux_nil] at h_decode
    exact absurd h_decode (by simp)
  | cons pfx rest0 =>
    rw [show (pfx :: rest0).getD 0 0 = pfx from rfl] at h_lo
    rw [show (pfx :: rest0).getD 0 0 = pfx from rfl,
        show (pfx :: rest0).drop 1 = rest0 from rfl]
    cases h_read : readLength rest0 (rlpPrefixLongListLenOfLen pfx) with
    | none =>
      exfalso
      have h_none := decodeAux_long_list_readLength_none (2 * rest0.length + 1) pfx rest0
        (by omega) h_read
      rw [decode_cons_eq_decodeAux_fuel,
          show 2 * rest0.length + 2 = (2 * rest0.length + 1) + 1 from rfl,
          h_none] at h_decode
      exact absurd h_decode (by simp)
    | some pair =>
      -- `cases h_read : ·` has already rewritten the goal's `readLength` call to
      -- `some pair`, so the witness closes by `rfl`.
      obtain ⟨lenVal, lenRest⟩ := pair
      exact ⟨lenVal, lenRest, rfl⟩

/-! ## Widening a short arm to the total footprint

    A short arm owns `t0`/`t1` and says nothing about `t2`/`t3`–`t6`. The total
    triple owns all seven. Framing the five untouched registers across the arm and
    then releasing them with `regIs_to_regOwn` is exactly the "never written, so
    still owned" step, and it costs no steps — so the arm's own bound is what gets
    weakened to `12`, not the other way round. -/

/-- Lift any short-form `rlp_item_size` triple (footprint `t0`/`t1`, bound `n ≤
    12`) to the total triple's seven-register footprint and its `12`-step bound. -/
private theorem ris_short_to_total {n : Nat}
    (base ptr raVal v5 v6 v7 v28 v29 v30 v31 spanVal : Word)
    (bs : List (BitVec 8))
    (h_steps : n ≤ 12)
    (h_arm : cpsTripleWithin n base (raVal &&& ~~~1)
      (CodeReq.ofProg base rlpItemSize_prog)
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ spanVal) **
       regOwn .x5 ** regOwn .x6 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)) :
    cpsTripleWithin 12 base (raVal &&& ~~~1)
      (CodeReq.ofProg base rlpItemSize_prog)
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
       ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ spanVal) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs) := by
  refine cpsTripleWithin_mono_nSteps h_steps
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
      (cpsTripleWithin_frameR
        (((.x7 : Reg) ↦ᵣ v7) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
          ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31))
        (by pcFree) h_arm))
  have hq1 : ((((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ spanVal) **
        regOwn .x5 ** regOwn .x6 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs) **
      (regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) h :=
    sepConj_mono (fun _ hh => hh)
      (sepConj_mono (regIs_to_regOwn .x7 v7)
        (sepConj_mono (regIs_to_regOwn .x28 v28)
          (sepConj_mono (regIs_to_regOwn .x29 v29)
            (sepConj_mono (regIs_to_regOwn .x30 v30) (regIs_to_regOwn .x31 v31)))))
      h hq
  xperm_hyp hq1

/-! ## ⭐ The total dispatch -/

/-- **`rlp_item_size`, total**: one triple for *every* RLP head byte.

    For any buffer whose head decodes successfully — no `SpanForm` gate, no
    restriction on the prefix range — `a0` returns the item's full encoded byte
    span `(EL.RLP.encode item).length`, in `risStepsTotal (bs.getD 0 0)` steps,
    clobbering `t0`–`t2` (`x5`–`x7`) and `t3`–`t6` (`x28`–`x31`).

    The three short forms take the constant `12` steps and in fact leave
    `t2`/`t3`–`t6` alone; they are still listed as clobbered because the statement
    is uniform across the five arms, and an untouched owned register trivially
    still satisfies `regOwn`. Callers that need the tighter constant-time,
    two-register statement should keep using
    `RlpSpliceHelperSpec.rlp_item_size_spec_within`, which this theorem does not
    replace.

    ⚠️ `h_nover` (`ptr.toNat + bs.length ≤ 2 ^ 64`) is required by the two long
    arms, whose length loop walks past the prefix byte with an incrementing
    address; it is an ABI obligation on the caller's buffer, not a restriction on
    which RLP inputs are covered. -/
theorem rlp_item_size_total_spec_within
    (base ptr raVal v5 v6 v7 v28 v29 v30 v31 : Word)
    (bs : List (BitVec 8)) (item : RLPItem) (rest : List Byte)
    (h_align : ptr.toNat % 8 = 0)
    (h_nover : ptr.toNat + bs.length ≤ 2 ^ 64)
    (h_valid : ∀ k, k < bs.length → isValidByteAccess (ptr + BitVec.ofNat 64 k) = true)
    (h_decode : decode bs = some (item, rest)) :
    cpsTripleWithin (risStepsTotal (bs.getD 0 0)) base (raVal &&& ~~~1)
      (CodeReq.ofProg base rlpItemSize_prog)
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
       ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 (encode item).length) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs) := by
  have h_len : 0 < bs.length := by
    cases bs with
    | nil =>
      rw [decode_eq_decodeAux_length, decodeAux_nil] at h_decode
      exact absurd h_decode (by simp)
    | cons a l => simp
  -- The three short spans, read off the model rather than off the machine.
  have h_span1 : (bs.getD 0 0).toNat < 0x80 → (encode item).length = 1 := by
    intro h_b
    cases bs with
    | nil => exact absurd h_len (by simp)
    | cons pfx rest0 =>
      rw [show (pfx :: rest0).getD 0 0 = pfx from rfl] at h_b
      exact decode_span_singleByte pfx rest0 item rest h_decode h_b
  have h_span2 : 0x80 ≤ (bs.getD 0 0).toNat → (bs.getD 0 0).toNat < 0xb8 →
      (encode item).length = (bs.getD 0 0).toNat - 127 := by
    intro h_lo h_hi
    cases bs with
    | nil => exact absurd h_len (by simp)
    | cons pfx rest0 =>
      rw [show (pfx :: rest0).getD 0 0 = pfx from rfl] at h_lo h_hi ⊢
      exact decode_span_shortBytes pfx rest0 item rest h_decode h_lo (by omega)
  have h_span3 : 0xc0 ≤ (bs.getD 0 0).toNat → (bs.getD 0 0).toNat < 0xf8 →
      (encode item).length = (bs.getD 0 0).toNat - 191 := by
    intro h_lo h_hi
    cases bs with
    | nil => exact absurd h_len (by simp)
    | cons pfx rest0 =>
      rw [show (pfx :: rest0).getD 0 0 = pfx from rfl] at h_lo h_hi ⊢
      exact decode_span_shortList pfx rest0 item rest h_decode h_lo (by omega)
  -- ══ the five-way split on the head byte ══
  by_cases h_b1 : (bs.getD 0 0).toNat < 0x80
  · -- single byte (`< 0x80`), span 1
    rw [show risStepsTotal (bs.getD 0 0) = 12 from by
          unfold risStepsTotal; rw [if_pos (by omega : (bs.getD 0 0).toNat < 0xb8)],
        show BitVec.ofNat 64 (encode item).length = (1 : Word) from by
          rw [h_span1 h_b1]; decide]
    exact ris_short_to_total base ptr raVal v5 v6 v7 v28 v29 v30 v31 (1 : Word) bs (by omega)
      (rlp_item_size_single_pinned_spec_within base ptr raVal v5 v6 bs
        h_align h_len h_valid h_b1)
  by_cases h_b2 : (bs.getD 0 0).toNat < 0xb8
  · -- short string (`0x80 ≤ · < 0xb8`), span `b - 127`
    rw [show risStepsTotal (bs.getD 0 0) = 12 from by
          unfold risStepsTotal; rw [if_pos h_b2],
        h_span2 (by omega) h_b2]
    exact ris_short_to_total base ptr raVal v5 v6 v7 v28 v29 v30 v31
      (BitVec.ofNat 64 ((bs.getD 0 0).toNat - 127)) bs (by omega)
      (rlp_item_size_short_string_pinned_spec_within base ptr raVal v5 v6 bs
        h_align h_len h_valid (by omega) h_b2)
  by_cases h_b3 : (bs.getD 0 0).toNat < 0xc0
  · -- ⭐ long string (`0xb8 ≤ · < 0xc0`), span `1 + lenOfLen + <length bytes>`
    obtain ⟨lenVal, lenRest, h_read⟩ :=
      readLength_of_decode_longBytes h_decode (by omega) h_b3
    rw [show risStepsTotal (bs.getD 0 0)
          = 7 * rlpPrefixLongBytesLenOfLen (bs.getD 0 0) + 17 from by
        unfold risStepsTotal; rw [if_neg h_b2, if_pos h_b3]]
    exact rlp_item_size_long_string_encode_length_spec_within base ptr raVal v5 v6 v7
      v28 v29 v30 v31 bs item rest lenRest lenVal h_align (by omega) h_b3 h_nover h_valid
      h_decode h_read
  by_cases h_b4 : (bs.getD 0 0).toNat < 0xf8
  · -- short list (`0xc0 ≤ · < 0xf8`), span `b - 191`
    rw [show risStepsTotal (bs.getD 0 0) = 12 from by
          unfold risStepsTotal; rw [if_neg h_b2, if_neg h_b3, if_pos h_b4],
        h_span3 (by omega) h_b4]
    exact ris_short_to_total base ptr raVal v5 v6 v7 v28 v29 v30 v31
      (BitVec.ofNat 64 ((bs.getD 0 0).toNat - 191)) bs (by omega)
      (rlp_item_size_short_list_pinned_spec_within base ptr raVal v5 v6 bs
        h_align h_len h_valid (by omega) h_b4)
  · -- ⭐ long list (`0xf8 ≤ ·`), span `1 + lenOfLen + <length bytes>`
    obtain ⟨lenVal, lenRest, h_read⟩ :=
      readLength_of_decode_longList h_decode (by omega)
    rw [show risStepsTotal (bs.getD 0 0)
          = 7 * rlpPrefixLongListLenOfLen (bs.getD 0 0) + 18 from by
        unfold risStepsTotal; rw [if_neg h_b2, if_neg h_b3, if_neg h_b4]]
    exact rlp_item_size_long_list_encode_length_spec_within base ptr raVal v5 v6 v7
      v28 v29 v30 v31 bs item rest lenRest lenVal h_align (by omega) h_nover h_valid
      h_decode h_read

/-! ## Totality, stated as a fact rather than left implicit

    The point of the theorem above is the *absence* of a gate, which is invisible
    in the statement. These two lemmas make it checkable: every head byte lands in
    exactly one of the five arms, and `risStepsTotal` is finite everywhere. -/

/-- Every head byte is covered: the five ranges the proof splits on are exhaustive
    and pairwise disjoint. `SpanForm` is the first, second and fourth disjunct
    only — the third and fifth are what this module adds. -/
theorem risStepsTotal_covers (b : BitVec 8) :
    b.toNat < 0x80
      ∨ (0x80 ≤ b.toNat ∧ b.toNat < 0xb8)
      ∨ (0xb8 ≤ b.toNat ∧ b.toNat < 0xc0)
      ∨ (0xc0 ≤ b.toNat ∧ b.toNat < 0xf8)
      ∨ 0xf8 ≤ b.toNat := by
  omega

/-- The step bound is finite on every head byte, and never worse than `74` —
    `lenOfLen ≤ 8`, so the long-list arm's `7 * 8 + 18` at prefix `0xff` is the
    maximum. -/
theorem risStepsTotal_le (b : BitVec 8) : risStepsTotal b ≤ 74 := by
  have h_lt : b.toNat < 256 := b.isLt
  unfold risStepsTotal rlpPrefixLongBytesLenOfLen rlpPrefixLongListLenOfLen
  split_ifs <;> omega

end RlpItemSizeTotalSpec

end EvmAsm.Codegen
