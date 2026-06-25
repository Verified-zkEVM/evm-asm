/-
  EvmAsm.Rv64.RLP.UnifiedDecodeItemShortBytesValidated

  Phase B.1 of issue #9373 — a VALIDATING shortBytes RLP single-item decoder over UNTRUSTED input.
  Unlike the valid-path decoder (which assumes the input is a well-formed encoding), this is a
  2-exit `cpsBranchWithin`: the SUCCESS exit carries `⌜decode (pfx::rest) = some (.bytes data, rest')⌝`
  and the FAIL exit carries `⌜decode (pfx::rest) = none⌝`, with NO validity hypotheses on the input.

  The untrusted-length contract: register `x15` holds the available byte count `L = (pfx::rest).length`
  (the codegen K20 model). The decoder runs the valid-path shortBytes handler (which computes
  `x11 = payloadLen = pfx-0x80`, `x13 = payloadPtr`), then a single `BLTU x11, x15` bound check:
  taken (`payloadLen < L`) ⟺ the payload fits ⟺ `takeBytes rest payloadLen = some …` ⟺ SUCCESS;
  fall-through (`payloadLen ≥ L`) ⟺ truncated ⟺ `takeBytes = none` ⟺ FAIL.

  This first unit covers the non-singleton case (`payloadLen ≠ 1`), for which the RLP single-byte
  canonical check is vacuous; the `payloadLen = 1` (prefix `0x81`) singleton-canonical sub-branch
  (`LBU`/`ANDI 0x80`/`BNE`, reusing `byte_zext_and_0x80_eq_zero_imp_lt`) is the follow-up that drops
  the `hns` hypothesis. The success/fail distinction is exposed as two exit PCs (a thin wrapper sets
  `a0`); the verified content is the `⌜decode = some/none⌝` propositions.
-/

import EvmAsm.Rv64.RLP.Phase1E2FullPath
import EvmAsm.Rv64.MemRegion
import EvmAsm.EL.RLP.ByteStringDecodeBridge

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.EL.RLP.ByteStringDecodeBridge
open EvmAsm.Rv64.Tactics

/-- The bound-check `BLTU x11, x15` taken condition `ult (ofNat len) (ofNat L)` is exactly the
    Nat fact `len < L`, given both fit in 64 bits. -/
private theorem ult_ofNat_len (len L : Nat) (hlen : len < 2 ^ 64) (hL : L < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 L) ↔ len < L := by
  rw [BitVec.ult_eq_decide]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen, Nat.mod_eq_of_lt hL, decide_eq_true_eq]

set_option maxRecDepth 8000 in
/-- **Validating shortBytes single-item decoder (non-singleton), at offset 0.** From an untrusted
    `bytesRegion regionBase (pfx::rest)` with `x15 = (pfx::rest).length`, runs the valid-path
    shortBytes handler then a `BLTU x11, x15` bound check. SUCCESS (taken) ⇒ `decode (pfx::rest)`
    yields the byte string; FAIL (fall) ⇒ `decode (pfx::rest) = none`. No validity hypotheses. -/
theorem rlp_decode_shortBytes_validated
    (pfx : Byte) (rest : List Byte)
    (v10 v11Old v12Old v14Old : Word)
    (regionBase : Word)
    (off1 off2 succOff : BitVec 13) (base e2_target : Word)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hns : rlpPrefixShortBytesPayloadLen pfx ≠ 1)
    (hover : regionBase.toNat + (pfx :: rest).length < 2 ^ 64)
    (htarget : (base + 8 + 4) + signExtend13 off2 = e2_target)
    (hd_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
    (hd_bltu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))) :
    cpsBranchWithin 7 base
      ((((rlp_phase1_step_code 0x80 off1 base).union
          (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
         (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
        (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff)))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ regionBase) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest))
      -- SUCCESS (taken: payloadLen < L)
      ((e2_target + 8) + signExtend13 succOff)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase (pfx :: rest) **
          ⌜decode (pfx :: rest)
            = some (.bytes (rest.take (rlpPrefixShortBytesPayloadLen pfx)),
                    rest.drop (rlpPrefixShortBytesPayloadLen pfx))⌝)
      -- FAIL (fall: payloadLen ≥ L)
      (e2_target + 12)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase (pfx :: rest) **
          ⌜decode (pfx :: rest) = none⌝) := by
  -- payloadLen ≤ 55 ⇒ both fit in 64 bits; abbreviate len/L.
  set len := rlpPrefixShortBytesPayloadLen pfx with hlen_def
  have hlen55 : len ≤ 55 := rlpPrefixShortBytesPayloadLen_le_55_of_class h_class
  have hL_lt : (pfx :: rest).length < 2 ^ 64 := by omega
  have hlen_lt : len < 2 ^ 64 := by omega
  -- The two semantic bridges (pure): the runtime bound-check condition ⇒ the decode verdict.
  have hsome : BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (pfx :: rest).length) →
      decode (pfx :: rest) = some (.bytes (rest.take len), rest.drop len) := by
    intro hult
    have hlt : len < (pfx :: rest).length := (ult_ofNat_len len _ hlen_lt hL_lt).mp hult
    have hle : len ≤ rest.length := by simp only [List.length_cons] at hlt; omega
    have htake : takeBytes rest len = some (rest.take len, rest.drop len) := by
      unfold takeBytes; rw [if_pos (by omega)]
    -- canonical condition is vacuous: `rest.take len` is not a singleton (len ≠ 1).
    have hlen_take : (rest.take len).length = len := by
      rw [List.length_take, Nat.min_eq_left hle]
    have hcanon : (match rest.take len with | [b] => ¬ b.toNat < 0x80 | _ => True) := by
      split
      · exfalso; rename_i b heq; rw [heq] at hlen_take; simp at hlen_take; omega
      · trivial
    rw [decode_cons_eq_decodeAux_fuel,
        show 2 * rest.length + 2 = (2 * rest.length + 1) + 1 from rfl,
        decodeAux_cons_shortBytes_eq_some_iff (2 * rest.length + 1) pfx rest h_class
          (rest.take len) (rest.drop len)]
    exact ⟨rest.take len, htake, rfl, hcanon⟩
  have hnone : ¬ BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (pfx :: rest).length) →
      decode (pfx :: rest) = none := by
    intro hnu
    have hge : ¬ len < (pfx :: rest).length := fun hlt => hnu ((ult_ofNat_len len _ hlen_lt hL_lt).mpr hlt)
    have hgt : rest.length < len := by simp only [List.length_cons] at hge; omega
    have htake : takeBytes rest len = none := by unfold takeBytes; rw [if_neg (by omega)]
    rw [decode_cons_eq_decodeAux_fuel,
        show 2 * rest.length + 2 = (2 * rest.length + 1) + 1 from rfl]
    exact decodeAux_cons_shortBytes_eq_none_of_takeBytes_none (2 * rest.length + 1) pfx rest h_class htake
  -- The valid-path handler (6 steps, base → e2_target+8), framed with x12/x14/x15/region.
  have handler := rlp_phase1_e2_full_path_payload_len_of_class_spec_within
    pfx v10 v11Old regionBase off1 off2 base e2_target htarget h_class hd_phase3
  have handlerF := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ v12Old) ** (.x14 ↦ᵣ v14Old) **
     (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest))
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)))) handler
  -- The bound check `BLTU x11, x15` (1 step) at e2_target+8, framed with the rest of the state.
  have bltuF := cpsBranchWithin_frameR
    ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) ** (.x12 ↦ᵣ v12Old) **
      (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14Old) **
      bytesRegion regionBase (pfx :: rest))
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
        (bytesRegion_pcFree _ _)))))))
    (bltu_spec_gen_within .x11 .x15 succOff (BitVec.ofNat 64 len)
      (BitVec.ofNat 64 (pfx :: rest).length) (e2_target + 8))
  -- Reshape the handler's POST to exactly the branch's PRE (target pinned ⇒ xperm is concrete).
  have handlerF' := cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp)
    (Q' := (((.x11 ↦ᵣ (BitVec.ofNat 64 len)) **
              (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length))) **
            ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
              (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) ** (.x12 ↦ᵣ v12Old) **
              (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14Old) **
              bytesRegion regionBase (pfx :: rest)))) handlerF
  have composed := cpsTripleWithin_seq_cpsBranchWithin hd_bltu handlerF' bltuF
  rw [show (e2_target + 8 : Word) + 4 = e2_target + 12 from by bv_omega] at composed
  -- Weaken to the goal: reshape the PRE (xperm) and the two posts to the decode verdicts.
  refine cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp) ?succ ?fail composed
  case succ =>
    intro h hp
    have hp' : (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest)) **
        ⌜BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (pfx :: rest).length)⌝) h := by
      xperm_hyp hp
    obtain ⟨hregs, hult⟩ := (sepConj_pure_right h).1 hp'
    have hgoal := (sepConj_pure_right h).2 ⟨hregs, hsome hult⟩
    xperm_hyp hgoal
  case fail =>
    intro h hp
    have hp' : (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest)) **
        ⌜¬ BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (pfx :: rest).length)⌝) h := by
      xperm_hyp hp
    obtain ⟨hregs, hnu⟩ := (sepConj_pure_right h).1 hp'
    have hgoal := (sepConj_pure_right h).2 ⟨hregs, hnone hnu⟩
    xperm_hyp hgoal

-- Concrete cross-check: the validating decoder applies to a 3-byte short string `0x83 'a''b''c'`
-- (`classifyPrefix 0x83 = .shortBytes`, payload length `3 ≠ 1`), discharged by `decide`; the
-- address/disjointness side-conditions ride as parameters (a concrete program discharges them).
example (regionBase base e2_target : Word) (off1 off2 succOff : BitVec 13)
    (hover : regionBase.toNat + ((0x83 : Byte) :: [0x61, 0x62, 0x63]).length < 2 ^ 64)
    (htarget : (base + 8 + 4) + signExtend13 off2 = e2_target)
    (hd_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
    (hd_bltu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))) :=
  rlp_decode_shortBytes_validated (0x83 : Byte) [0x61, 0x62, 0x63] 0 0 0 0 regionBase
    off1 off2 succOff base e2_target (by decide) (by decide) hover htarget hd_phase3 hd_bltu

end EvmAsm.Rv64.RLP
