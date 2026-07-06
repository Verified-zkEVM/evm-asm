/-
  EvmAsm.Rv64.RLP.UnifiedDecodeItemShortListValidated

  Validating shortList DESCEND over UNTRUSTED input — the list gateway for the verified guest
  decoders (#9373). The fixed-schema decoders (`withdrawal_decode`, `header_minimal_decode`,
  `tx_eip1559_decode`) take an RLP *list*; before walking its fields they must validate the list
  header and enter its payload. This is the shortList (`0xc0..0xf7`) analog of
  `rlp_decode_shortBytes_validated_at`: the e4 handler classifies the prefix and computes the
  payload length, then a `BLTU x11, x15` bound check rejects a header whose claimed payload exceeds
  the available bytes.

  SUCCESS (`payloadLen < L`): `x13` = list payload start, `x11` = payload length, and the payload
  window is available (`takeBytes rest payloadLen = some (rest.take payloadLen, rest.drop payloadLen)`),
  so — with the shortList Phase-A bridge — `decode (pfx :: rest)` reduces to decoding that window as
  a list. FAIL (`payloadLen ≥ L`): the claimed payload runs off the end, so `decode (pfx :: rest) =
  none`. shortList is canonical-clean (the length lives in the prefix), so no leading-zero check is
  needed — the bound check alone validates the header.
-/

import EvmAsm.Rv64.RLP.Phase1E4FullPath
import EvmAsm.Rv64.MemRegion
import EvmAsm.EL.RLP.ListDecodeBridge

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.EL.RLP.ListDecodeBridge
open EvmAsm.Rv64.Tactics

/-- `ult (ofNat a) (ofNat b) ↔ a < b` for in-range `a`,`b`. -/
private theorem ult_ofNat_len' (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) ↔ a < b := by
  rw [BitVec.ult_eq_decide]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, decide_eq_true_eq]

set_option linter.unusedVariables false in
/-- **Validating shortList descend** at byte offset `O`. The list `pfx :: rest` sits at offset `O`
    of `bytesRegion regionBase bs` (`x13 = regionBase + O`, `x5 = pfx`, `x15 = (pfx :: rest).length`
    = bytes available from `O`). Runs the e4 shortList handler then a `BLTU x11, x15` bound check:
    SUCCESS (`payloadLen < L`) ⇒ the payload window is available; FAIL (`payloadLen ≥ L`) ⇒
    `decode (pfx :: rest) = none`. No validity hypotheses. -/
theorem rlp_decode_shortList_validated_at
    (pfx : Byte) (rest : List Byte) (bs : List Byte) (O : Nat)
    (v10 v11Old v12Old v14Old : Word)
    (regionBase : Word)
    (off1 off2 off3 off4 succOff : BitVec 13) (base e4_target : Word)
    (h_class : classifyPrefix pfx = .shortList)
    (hLfit : (pfx :: rest).length < 2 ^ 64)
    (htarget : (base + 24 + 4) + signExtend13 off4 = e4_target)
    (hd_phase3 : (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg e4_target rlp_phase3_short_list_prog))
    (hd_bltu : (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg e4_target rlp_phase3_short_list_prog)).Disjoint
        (CodeReq.singleton (e4_target + 8) (.BLTU .x11 .x15 succOff))) :
    cpsBranchWithin 11 base
      ((((rlp_phase1_step_code 0x80 off1 base).union
          ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
            ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
              (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg e4_target rlp_phase3_short_list_prog)).union
        (CodeReq.singleton (e4_target + 8) (.BLTU .x11 .x15 succOff)))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs)
      -- SUCCESS (taken: payloadLen < L): payload window available.
      ((e4_target + 8) + signExtend13 succOff)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortListPayloadLen pfx))) **
          (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase bs **
          ⌜takeBytes rest (rlpPrefixShortListPayloadLen pfx)
            = some (rest.take (rlpPrefixShortListPayloadLen pfx),
                    rest.drop (rlpPrefixShortListPayloadLen pfx))⌝)
      -- FAIL (fall: payloadLen ≥ L): the list runs off the end.
      (e4_target + 12)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortListPayloadLen pfx))) **
          (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase bs **
          ⌜decode (pfx :: rest) = none⌝) := by
  set len := rlpPrefixShortListPayloadLen pfx with hlen_def
  have hlen55 : len ≤ 55 := rlpPrefixShortListPayloadLen_le_55_of_class h_class
  have hlen_lt : len < 2 ^ 64 := by omega
  have hsome : BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (pfx :: rest).length) →
      takeBytes rest len = some (rest.take len, rest.drop len) := by
    intro hult
    have hlt : len < (pfx :: rest).length := (ult_ofNat_len' len _ hlen_lt hLfit).mp hult
    have hle : len ≤ rest.length := by simp only [List.length_cons] at hlt; omega
    unfold takeBytes; rw [if_pos hle]
  have hnone : ¬ BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (pfx :: rest).length) →
      decode (pfx :: rest) = none := by
    intro hnu
    have hge : ¬ len < (pfx :: rest).length :=
      fun hlt => hnu ((ult_ofNat_len' len _ hlen_lt hLfit).mpr hlt)
    have hgt : rest.length < len := by simp only [List.length_cons] at hge; omega
    have htake : takeBytes rest len = none := by unfold takeBytes; rw [if_neg (by omega)]
    rw [decode_cons_eq_decodeAux_fuel,
        show 2 * rest.length + 2 = (2 * rest.length + 1) + 1 from rfl,
        decodeAux_cons_shortList_eq_decodeListPayload (2 * rest.length + 1) pfx rest h_class, htake]
    rfl
  -- e4 handler with item-start pointer `regionBase + O`, framed with x12/x14/x15/full region.
  have handler := rlp_phase1_e4_full_path_payload_len_of_class_spec_within
    pfx v10 v11Old (regionBase + BitVec.ofNat 64 O) off1 off2 off3 off4 base e4_target
    htarget h_class hd_phase3
  have handlerF := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ v12Old) ** (.x14 ↦ᵣ v14Old) **
     (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs)
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)))) handler
  have bltuF := cpsBranchWithin_frameR
    ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) ** (.x12 ↦ᵣ v12Old) **
      (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14Old) **
      bytesRegion regionBase bs)
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
        (bytesRegion_pcFree _ _)))))))
    (bltu_spec_gen_within .x11 .x15 succOff (BitVec.ofNat 64 len)
      (BitVec.ofNat 64 (pfx :: rest).length) (e4_target + 8))
  have handlerF' := cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp)
    (Q' := (((.x11 ↦ᵣ (BitVec.ofNat 64 len)) **
              (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length))) **
            ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
              (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) ** (.x12 ↦ᵣ v12Old) **
              (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
              (.x14 ↦ᵣ v14Old) ** bytesRegion regionBase bs))) handlerF
  have composed := cpsTripleWithin_seq_cpsBranchWithin hd_bltu handlerF' bltuF
  rw [show (e4_target + 8 : Word) + 4 = e4_target + 12 from by bv_omega] at composed
  refine cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp) ?succ ?fail composed
  case succ =>
    intro h hp
    have hp' : (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs) **
        ⌜BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (pfx :: rest).length)⌝) h := by
      xperm_hyp hp
    obtain ⟨hregs, hult⟩ := (sepConj_pure_right h).1 hp'
    have hgoal := (sepConj_pure_right h).2 ⟨hregs, hsome hult⟩
    xperm_hyp hgoal
  case fail =>
    intro h hp
    have hp' : (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs) **
        ⌜¬ BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (pfx :: rest).length)⌝) h := by
      xperm_hyp hp
    obtain ⟨hregs, hnu⟩ := (sepConj_pure_right h).1 hp'
    have hgoal := (sepConj_pure_right h).2 ⟨hregs, hnone hnu⟩
    xperm_hyp hgoal

end EvmAsm.Rv64.RLP
