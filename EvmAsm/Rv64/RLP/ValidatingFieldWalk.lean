/-
  EvmAsm.Rv64.RLP.ValidatingFieldWalk

  Composition glue for the untrusted RLP field walker (F1 of the verified guest-decoder plan,
  #9373). The validating single-item decoders are 2-exit `cpsBranchWithin`s whose SUCCESS is the
  *taken* exit and FAIL the fall-through. To advance to the next field after a successful decode,
  we must sequence the pointer-advance instructions on the **taken** (success) exit, using
  `cpsBranchWithin_seq_cpsTripleWithin_taken` from CPSSpec.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.RLP.UnifiedDecodeItemShortBytesValidatedAt
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.WPAttr
import EvmAsm.Rv64.WP.CFG

namespace EvmAsm.Rv64

namespace RLP

open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- **Validating shortBytes decode-and-advance** (one field step of the untrusted walk, F1 of
    #9373). Runs the offset-general validating shortBytes decoder at byte offset `O`
    (`rlp_decode_shortBytes_validated_at`) and, on its SUCCESS (taken) exit, sequences
    `ADD x13, x13, x11` to advance the cursor `x13` past the just-decoded item's payload.

    SUCCESS post: `x13 = (regionBase + O) + 1 + payloadLen` (item start + prefix + payload — the
    next item start), carrying the pure verdict `decode (pfx :: rest) = some (.bytes …)`. FAIL
    (fall) is the decoder's abort exit unchanged (`decode = none`). -/
theorem rlp_decode_shortBytes_advance_at
    (pfx : Byte) (rest : List Byte) (bs : List Byte) (O : Nat)
    (v10 v11Old v12Old v14Old : Word)
    (regionBase : Word)
    (off1 off2 succOff : BitVec 13) (base e2_target : Word)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hns : rlpPrefixShortBytesPayloadLen pfx ≠ 1)
    (hLfit : (pfx :: rest).length < 2 ^ 64)
    (htarget : (base + 8 + 4) + signExtend13 off2 = e2_target)
    (hd_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
    (hd_bltu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff)))
    (succPC : Word)
    (hsuccPC : (e2_target + 8) + signExtend13 succOff = succPC)
    (hd_add : ((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))).Disjoint
               (CodeReq.singleton succPC (.ADD .x13 .x13 .x11))) :
    cpsBranchWithin (7 + 1) base
      (((((rlp_phase1_step_code 0x80 off1 base).union
          (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
         (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
        (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))).union
        (CodeReq.singleton succPC (.ADD .x13 .x13 .x11)))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs)
      -- SUCCESS (taken): item decoded; cursor advanced past the payload.
      (succPC + 4)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ (((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))
                    + BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase bs **
          ⌜decode (pfx :: rest)
            = some (.bytes (rest.take (rlpPrefixShortBytesPayloadLen pfx)),
                    rest.drop (rlpPrefixShortBytesPayloadLen pfx))⌝)
      -- FAIL (fall): the decoder's abort exit, unchanged.
      (e2_target + 12)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase bs **
          ⌜decode (pfx :: rest) = none⌝) := by
  -- The validating decoder at offset `O` (taken = success).
  have decAt := rlp_decode_shortBytes_validated_at pfx rest bs O v10 v11Old v12Old v14Old
    regionBase off1 off2 succOff base e2_target h_class hns hLfit htarget hd_phase3 hd_bltu
  rw [hsuccPC] at decAt
  -- ADD x13, x13, x11 at `succPC`, framed with the 8-atom complement (incl. the pure verdict).
  have add_raw := add_spec_gen_rd_eq_rs1_within .x13 .x11
    ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))
    (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx)) succPC (by nofun)
  have addF : cpsTripleWithin 1 succPC (succPC + 4)
      (CodeReq.singleton succPC (.ADD .x13 .x13 .x11))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
        (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
        bytesRegion regionBase bs **
        ⌜decode (pfx :: rest)
          = some (.bytes (rest.take (rlpPrefixShortBytesPayloadLen pfx)),
                  rest.drop (rlpPrefixShortBytesPayloadLen pfx))⌝)
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
        (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))
                  + BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
        (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
        bytesRegion regionBase bs **
        ⌜decode (pfx :: rest)
          = some (.bytes (rest.take (rlpPrefixShortBytesPayloadLen pfx)),
                  rest.drop (rlpPrefixShortBytesPayloadLen pfx))⌝) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) ** (.x12 ↦ᵣ v12Old) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase bs **
          ⌜decode (pfx :: rest)
            = some (.bytes (rest.take (rlpPrefixShortBytesPayloadLen pfx)),
                    rest.drop (rlpPrefixShortBytesPayloadLen pfx))⌝)
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj (bytesRegion_pcFree _ _) pcFree_pure)))))))
        add_raw)
  exact cpsBranchWithin_seq_cpsTripleWithin_taken hd_add decAt addF

/-- The cursor `x13` after a shortBytes decode-and-advance from offset `O` lands at the next item
    start `regionBase + (O + 1 + payloadLen)` (item start + 1 prefix byte + payload). Unconditional:
    `BitVec.ofNat` is mod-`2^64`, so the offset combination never needs an in-range hypothesis. -/
theorem advance_cursor_clean (regionBase : Word) (O payloadLen : Nat) :
    (regionBase + BitVec.ofNat 64 O + signExtend12 (1 : BitVec 12)) + BitVec.ofNat 64 payloadLen
    = regionBase + BitVec.ofNat 64 (O + 1 + payloadLen) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
      show (1 : Word) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, BitVec.add_assoc,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add, Nat.add_assoc]

/-- **Clean-form** validating shortBytes decode-and-advance: identical to
    `rlp_decode_shortBytes_advance_at` but the SUCCESS cursor `x13` is stated in the canonical
    next-item-start form `regionBase + (O + 1 + payloadLen)` — the precondition shape the next
    field's decoder consumes, so successive steps chain without arithmetic glue on `x13`. -/
theorem rlp_decode_shortBytes_advance_at_clean
    (pfx : Byte) (rest : List Byte) (bs : List Byte) (O : Nat)
    (v10 v11Old v12Old v14Old : Word)
    (regionBase : Word)
    (off1 off2 succOff : BitVec 13) (base e2_target : Word)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hns : rlpPrefixShortBytesPayloadLen pfx ≠ 1)
    (hLfit : (pfx :: rest).length < 2 ^ 64)
    (htarget : (base + 8 + 4) + signExtend13 off2 = e2_target)
    (hd_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
    (hd_bltu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff)))
    (succPC : Word)
    (hsuccPC : (e2_target + 8) + signExtend13 succOff = succPC)
    (hd_add : ((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))).Disjoint
               (CodeReq.singleton succPC (.ADD .x13 .x13 .x11))) :
    cpsBranchWithin (7 + 1) base
      (((((rlp_phase1_step_code 0x80 off1 base).union
          (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
         (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
        (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))).union
        (CodeReq.singleton succPC (.ADD .x13 .x13 .x11)))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs)
      (succPC + 4)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ (regionBase
                    + BitVec.ofNat 64 (O + 1 + rlpPrefixShortBytesPayloadLen pfx))) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase bs **
          ⌜decode (pfx :: rest)
            = some (.bytes (rest.take (rlpPrefixShortBytesPayloadLen pfx)),
                    rest.drop (rlpPrefixShortBytesPayloadLen pfx))⌝)
      (e2_target + 12)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase bs **
          ⌜decode (pfx :: rest) = none⌝) := by
  have h := rlp_decode_shortBytes_advance_at pfx rest bs O v10 v11Old v12Old v14Old regionBase
    off1 off2 succOff base e2_target h_class hns hLfit htarget hd_phase3 hd_bltu succPC hsuccPC hd_add
  rw [advance_cursor_clean regionBase O (rlpPrefixShortBytesPayloadLen pfx)] at h
  exact h

/-! ## WP certificate wrapper -/

/-- Code requirement for validating shortBytes decode-and-advance. -/
def validatingShortBytesAdvanceCR
    (base e2Target succPC : Word) (off1 off2 succOff : BitVec 13) : CodeReq :=
  (((((rlp_phase1_step_code 0x80 off1 base).union
      (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
     (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).union
    (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff))).union
    (CodeReq.singleton succPC (.ADD .x13 .x13 .x11)))

/-- Computed precondition for validating shortBytes decode-and-advance. -/
def validatingShortBytesAdvancePre
    (pfx : Byte) (rest bs : List Byte) (O : Nat)
    (v10 v11Old v12Old v14Old regionBase : Word) : Assertion :=
  ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
    (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) **
    (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
    (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs)

/-- Success postcondition for validating shortBytes decode-and-advance. -/
def validatingShortBytesAdvanceSuccessPost
    (pfx : Byte) (rest bs : List Byte) (O : Nat)
    (v12Old v14Old regionBase : Word) : Assertion :=
  ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
    (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
    (.x12 ↦ᵣ v12Old) **
    (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + 1 + rlpPrefixShortBytesPayloadLen pfx))) **
    (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
    bytesRegion regionBase bs **
    ⌜decode (pfx :: rest)
      = some (.bytes (rest.take (rlpPrefixShortBytesPayloadLen pfx)),
              rest.drop (rlpPrefixShortBytesPayloadLen pfx))⌝)

/-- Failure postcondition for validating shortBytes decode-and-advance. -/
def validatingShortBytesAdvanceFailurePost
    (pfx : Byte) (rest bs : List Byte) (O : Nat)
    (v12Old v14Old regionBase : Word) : Assertion :=
  ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
    (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
    (.x12 ↦ᵣ v12Old) **
    (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
    (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
    bytesRegion regionBase bs ** ⌜decode (pfx :: rest) = none⌝)

/-- WP branch certificate for validating shortBytes decode-and-advance.
    The taken exit is success; the fall-through exit is failure. -/
def validatingShortBytesAdvanceBranch
    (pfx : Byte) (rest bs : List Byte) (O : Nat)
    (v10 v11Old v12Old v14Old regionBase : Word)
    (off1 off2 succOff : BitVec 13) (base e2Target : Word)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hns : rlpPrefixShortBytesPayloadLen pfx ≠ 1)
    (h_lfit : (pfx :: rest).length < 2 ^ 64)
    (h_target : (base + 8 + 4) + signExtend13 off2 = e2Target)
    (h_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog))
    (h_bltu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff)))
    (succPC : Word)
    (h_succ_pc : (e2Target + 8) + signExtend13 succOff = succPC)
    (h_add : ((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff))).Disjoint
               (CodeReq.singleton succPC (.ADD .x13 .x13 .x11))) :
    WP.Branch base (validatingShortBytesAdvanceCR base e2Target succPC off1 off2 succOff) :=
  WP.Branch.ofSpec
    (rlp_decode_shortBytes_advance_at_clean pfx rest bs O v10 v11Old v12Old v14Old regionBase
      off1 off2 succOff base e2Target h_class hns h_lfit h_target h_phase3 h_bltu succPC
      h_succ_pc h_add)

/-- The validating advance branch computes the named precondition. -/
theorem validatingShortBytesAdvanceBranch_pre
    (pfx : Byte) (rest bs : List Byte) (O : Nat)
    (v10 v11Old v12Old v14Old regionBase : Word)
    (off1 off2 succOff : BitVec 13) (base e2Target : Word)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hns : rlpPrefixShortBytesPayloadLen pfx ≠ 1)
    (h_lfit : (pfx :: rest).length < 2 ^ 64)
    (h_target : (base + 8 + 4) + signExtend13 off2 = e2Target)
    (h_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog))
    (h_bltu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff)))
    (succPC : Word)
    (h_succ_pc : (e2Target + 8) + signExtend13 succOff = succPC)
    (h_add : ((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff))).Disjoint
               (CodeReq.singleton succPC (.ADD .x13 .x13 .x11))) :
    (validatingShortBytesAdvanceBranch pfx rest bs O v10 v11Old v12Old v14Old regionBase
      off1 off2 succOff base e2Target h_class hns h_lfit h_target h_phase3 h_bltu succPC
      h_succ_pc h_add).pre =
      validatingShortBytesAdvancePre pfx rest bs O v10 v11Old v12Old v14Old regionBase := by
  rfl

/-- The validating advance branch's taken exit is success. -/
theorem validatingShortBytesAdvanceBranch_exit_t
    (pfx : Byte) (rest bs : List Byte) (O : Nat)
    (v10 v11Old v12Old v14Old regionBase : Word)
    (off1 off2 succOff : BitVec 13) (base e2Target : Word)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hns : rlpPrefixShortBytesPayloadLen pfx ≠ 1)
    (h_lfit : (pfx :: rest).length < 2 ^ 64)
    (h_target : (base + 8 + 4) + signExtend13 off2 = e2Target)
    (h_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog))
    (h_bltu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff)))
    (succPC : Word)
    (h_succ_pc : (e2Target + 8) + signExtend13 succOff = succPC)
    (h_add : ((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff))).Disjoint
               (CodeReq.singleton succPC (.ADD .x13 .x13 .x11))) :
    (validatingShortBytesAdvanceBranch pfx rest bs O v10 v11Old v12Old v14Old regionBase
      off1 off2 succOff base e2Target h_class hns h_lfit h_target h_phase3 h_bltu succPC
      h_succ_pc h_add).exit_t = succPC + 4 := by
  rfl

/-- The validating advance branch's fall-through exit is failure. -/
theorem validatingShortBytesAdvanceBranch_exit_f
    (pfx : Byte) (rest bs : List Byte) (O : Nat)
    (v10 v11Old v12Old v14Old regionBase : Word)
    (off1 off2 succOff : BitVec 13) (base e2Target : Word)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hns : rlpPrefixShortBytesPayloadLen pfx ≠ 1)
    (h_lfit : (pfx :: rest).length < 2 ^ 64)
    (h_target : (base + 8 + 4) + signExtend13 off2 = e2Target)
    (h_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog))
    (h_bltu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff)))
    (succPC : Word)
    (h_succ_pc : (e2Target + 8) + signExtend13 succOff = succPC)
    (h_add : ((((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2Target rlp_phase3_short_string_prog)).union
                 (CodeReq.singleton (e2Target + 8) (.BLTU .x11 .x15 succOff))).Disjoint
               (CodeReq.singleton succPC (.ADD .x13 .x13 .x11))) :
    (validatingShortBytesAdvanceBranch pfx rest bs O v10 v11Old v12Old v14Old regionBase
      off1 off2 succOff base e2Target h_class hns h_lfit h_target h_phase3 h_bltu succPC
      h_succ_pc h_add).exit_f = e2Target + 12 := by
  rfl

attribute [rv64_wp]
  validatingShortBytesAdvanceBranch_pre
  validatingShortBytesAdvanceBranch_exit_t
  validatingShortBytesAdvanceBranch_exit_f

attribute [rv64_wp_cert]
  validatingShortBytesAdvanceBranch

end RLP

end EvmAsm.Rv64
