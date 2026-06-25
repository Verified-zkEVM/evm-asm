/-
  EvmAsm.Rv64.RLP.UnifiedDecodeItemShortBytesValidatedAt

  Offset-general validating shortBytes single-item decoder over UNTRUSTED input — the building
  block for the field walker (F1 of the verified guest-decoder plan, #9373). The merged
  `rlp_decode_shortBytes_validated` decodes the item at the region START (offset 0); a list-field
  walk needs to decode the item at an arbitrary byte offset `O` within the region (the prefix byte
  `pfx = bs[O]` is supplied in `x5` by the caller's `LBU`, `x13 = regionBase + O` is the item start,
  `x15 = (the available byte count from O)`).

  The shortBytes handler + `BLTU x11, x15` bound check are **register-only** (they never read the
  region — the prefix rides in `x5`), so this is the merged proof with three changes: the handler's
  item-start pointer is `regionBase + O` (not `regionBase`), the full `bytesRegion regionBase bs` is
  framed (not the item-only region), and the verdict is about `decode (pfx :: rest)` (the item at
  `O`, i.e. `bs.drop O`). The Phase-A bridges are list-generic, so they transfer verbatim.

  Non-singleton case (`payloadLen ≠ 1`); the singleton (`0x81`) and singleByte offset-general arms
  reuse `UnifiedDecodeItem{Singleton,SingleByte}Validated`'s pattern the same way.
-/

import EvmAsm.Rv64.RLP.Phase1E2FullPath
import EvmAsm.Rv64.RLP.Phase1ToPhase3SingleByte
import EvmAsm.Rv64.MemRegion
import EvmAsm.EL.RLP.ByteStringDecodeBridge

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.EL.RLP.ByteStringDecodeBridge
open EvmAsm.Rv64.Tactics

/-- `ult (ofNat a) (ofNat b) ↔ a < b` for in-range `a`,`b`. -/
private theorem ult_ofNat_len (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) ↔ a < b := by
  rw [BitVec.ult_eq_decide]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, decide_eq_true_eq]

set_option maxRecDepth 8000 in
/-- **Offset-general validating shortBytes decoder (non-singleton).** The item `pfx :: rest` sits at
    byte offset `O` of `bytesRegion regionBase bs` (`x13 = regionBase + O`, `x5 = pfx`,
    `x15 = (pfx :: rest).length` = bytes available from `O`). Runs the shortBytes handler then a
    `BLTU x11, x15` bound check: SUCCESS (`len < L`) ⇒ `decode (pfx :: rest) = some (.bytes …)`,
    FAIL (`len ≥ L`) ⇒ `decode (pfx :: rest) = none`. No validity hypotheses. -/
theorem rlp_decode_shortBytes_validated_at
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
               (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))) :
    cpsBranchWithin 7 base
      ((((rlp_phase1_step_code 0x80 off1 base).union
          (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
         (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
        (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff)))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs)
      -- SUCCESS (taken: payloadLen < L)
      ((e2_target + 8) + signExtend13 succOff)
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
      -- FAIL (fall: payloadLen ≥ L)
      (e2_target + 12)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          (.x12 ↦ᵣ v12Old) **
          (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase bs **
          ⌜decode (pfx :: rest) = none⌝) := by
  set len := rlpPrefixShortBytesPayloadLen pfx with hlen_def
  have hlen55 : len ≤ 55 := rlpPrefixShortBytesPayloadLen_le_55_of_class h_class
  have hlen_lt : len < 2 ^ 64 := by omega
  have hsome : BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (pfx :: rest).length) →
      decode (pfx :: rest) = some (.bytes (rest.take len), rest.drop len) := by
    intro hult
    have hlt : len < (pfx :: rest).length := (ult_ofNat_len len _ hlen_lt hLfit).mp hult
    have hle : len ≤ rest.length := by simp only [List.length_cons] at hlt; omega
    have htake : takeBytes rest len = some (rest.take len, rest.drop len) := by
      unfold takeBytes; rw [if_pos (by omega)]
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
    have hge : ¬ len < (pfx :: rest).length := fun hlt => hnu ((ult_ofNat_len len _ hlen_lt hLfit).mpr hlt)
    have hgt : rest.length < len := by simp only [List.length_cons] at hge; omega
    have htake : takeBytes rest len = none := by unfold takeBytes; rw [if_neg (by omega)]
    rw [decode_cons_eq_decodeAux_fuel,
        show 2 * rest.length + 2 = (2 * rest.length + 1) + 1 from rfl]
    exact decodeAux_cons_shortBytes_eq_none_of_takeBytes_none (2 * rest.length + 1) pfx rest h_class htake
  -- Handler with item-start pointer `regionBase + O`, framed with x12/x14/x15/full region.
  have handler := rlp_phase1_e2_full_path_payload_len_of_class_spec_within
    pfx v10 v11Old (regionBase + BitVec.ofNat 64 O) off1 off2 base e2_target htarget h_class hd_phase3
  have handlerF := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ v12Old) ** (.x14 ↦ᵣ v14Old) **
     (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs)
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)))) handler
  have bltuF := cpsBranchWithin_frameR
    ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) ** (.x12 ↦ᵣ v12Old) **
      (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14Old) **
      bytesRegion regionBase bs)
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
        (bytesRegion_pcFree _ _)))))))
    (bltu_spec_gen_within .x11 .x15 succOff (BitVec.ofNat 64 len)
      (BitVec.ofNat 64 (pfx :: rest).length) (e2_target + 8))
  have handlerF' := cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp)
    (Q' := (((.x11 ↦ᵣ (BitVec.ofNat 64 len)) **
              (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length))) **
            ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
              (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) ** (.x12 ↦ᵣ v12Old) **
              (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) **
              (.x14 ↦ᵣ v14Old) ** bytesRegion regionBase bs))) handlerF
  have composed := cpsTripleWithin_seq_cpsBranchWithin hd_bltu handlerF' bltuF
  rw [show (e2_target + 8 : Word) + 4 = e2_target + 12 from by bv_omega] at composed
  refine cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp) ?succ ?fail composed
  case succ =>
    intro h hp
    have hp' : (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
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
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ ((regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase bs) **
        ⌜¬ BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (pfx :: rest).length)⌝) h := by
      xperm_hyp hp
    obtain ⟨hregs, hnu⟩ := (sepConj_pure_right h).1 hp'
    have hgoal := (sepConj_pure_right h).2 ⟨hregs, hnone hnu⟩
    xperm_hyp hgoal

/-- **Offset-general validating singleByte decoder.** A canonical single byte (`pfx < 0x80`) at
    offset `O` always decodes to `[pfx]`; single-exit `cpsTripleWithin` carrying
    `⌜decode (pfx :: rest) = some (.bytes [pfx], rest)⌝`. `x13 = regionBase + O` and the full region
    are framed through the register-only e1 handler. No failure case. -/
theorem rlp_decode_singleByte_validated_at
    (pfx : Byte) (rest : List Byte) (bs : List Byte) (O : Nat)
    (v10 v11Old v12 v14 v15 : Word) (regionBase : Word)
    (offset : BitVec 13) (base target : Word)
    (h_class : classifyPrefix pfx = .singleByte)
    (htarget : (base + 4) + signExtend13 offset = target)
    (hd : (rlp_phase1_step_code 0x80 offset base).Disjoint
            (CodeReq.ofProg target rlp_phase3_single_byte_prog)) :
    cpsTripleWithin 3 base (target + 4)
      ((rlp_phase1_step_code 0x80 offset base).union
         (CodeReq.ofProg target rlp_phase3_single_byte_prog))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0x80 : BitVec 12))) **
        (.x11 ↦ᵣ (1 : Word)) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** bytesRegion regionBase bs **
        ⌜decode (pfx :: rest) = some (.bytes [pfx], rest)⌝) := by
  have hsome : decode (pfx :: rest) = some (.bytes [pfx], rest) := by
    rw [decode_cons_eq_decodeAux_fuel,
        show 2 * rest.length + 2 = (2 * rest.length + 1) + 1 from rfl,
        decodeAux_cons_singleByte_eq_some_iff (2 * rest.length + 1) pfx rest h_class [pfx] rest]
    exact ⟨rfl, rfl⟩
  have handler := rlp_phase1_e1_single_byte_of_class_spec_within pfx v10 v11Old offset base target
    htarget h_class hd
  have framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14) **
      (.x15 ↦ᵣ v15) ** bytesRegion regionBase bs)
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _))))) handler
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) ?_ framed
  intro s hq
  have hgoal := (sepConj_pure_right s).2 ⟨hq, hsome⟩
  xperm_hyp hgoal

end EvmAsm.Rv64.RLP
