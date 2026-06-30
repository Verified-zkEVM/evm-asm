/-
  EvmAsm.Rv64.RLP.WithdrawalDecodeFailureWP

  Semantic failure adapters for the withdrawal decoder WP calculus.  The exact
  control-flow reason remains in a scratch frame; the public ABI component only
  states that the pure `decodeWithdrawal` result is failure.
-/

import EvmAsm.Rv64.RLP.WithdrawalDecode
import EvmAsm.Rv64.RLP.WithdrawalSchemaWP

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

namespace WithdrawalDecode

/-- A byte/string RLP prefix cannot decode as a list. -/
theorem decodeAux_ne_list_of_head_lt_c0
    (fuel : Nat) (pfx : Byte) (rest leftover : List Byte) (items : List RLPItem)
    (h : BitVec.ult (pfx.zeroExtend 64) (0xc0 : Word) = true) :
    decodeAux (fuel + 1) (pfx :: rest) ≠ some (.list items, leftover) := by
  have hp : pfx.toNat < 192 := by
    simp only [BitVec.ult, decide_eq_true_eq, show (0xc0 : Word).toNat = 192 from by decide,
      BitVec.toNat_setWidth] at h
    have hb : pfx.toNat < 2 ^ 64 := by
      have := pfx.isLt
      omega
    rw [Nat.mod_eq_of_lt hb] at h
    exact h
  intro hdec
  unfold decodeAux at hdec
  by_cases h80 : pfx.toNat < 128
  · simp [h80] at hdec
  · by_cases hB7 : pfx.toNat ≤ 183
    · simp [h80, hB7] at hdec
      cases ht : takeBytes rest (pfx.toNat - 128) with
      | none => simp [ht] at hdec
      | some pair =>
          cases pair with
          | mk data rest' =>
              simp [ht] at hdec
              cases data with
              | nil => simp at hdec
              | cons b tail =>
                  cases tail with
                  | nil => by_cases hb : b.toNat < 128 <;> simp [hb] at hdec
                  | cons _ _ => simp at hdec
    · have hBF : pfx.toNat ≤ 191 := by omega
      simp [h80, hB7, hBF] at hdec
      cases hr : readLength rest (pfx.toNat - 183) with
      | none => simp [hr] at hdec
      | some pair =>
          cases pair with
          | mk lenVal rest' =>
              by_cases hlen : lenVal ≤ 55
              · simp [hr, hlen] at hdec
              · simp [hr, hlen] at hdec
                cases ht : takeBytes rest' lenVal with
                | none => simp [ht] at hdec
                | some pair2 =>
                    cases pair2 with
                    | mk _ _ => simp [ht] at hdec

/-- A complete RLP decode whose first byte is below `0xc0` cannot be a list. -/
theorem decodeFully_ne_list_of_head_lt_c0
    (pfx : Byte) (rest : List Byte) (items : List RLPItem)
    (h : BitVec.ult (pfx.zeroExtend 64) (0xc0 : Word) = true) :
    decodeFully (pfx :: rest) ≠ some (.list items) := by
  intro hfull
  have hdecode : decode (pfx :: rest) = some (.list items, []) :=
    (decodeFully_eq_some_iff (pfx :: rest) (.list items)).1 hfull
  rw [decode_cons_eq_decodeAux_fuel] at hdecode
  exact decodeAux_ne_list_of_head_lt_c0 (2 * rest.length + 1) pfx rest [] items h hdecode

/-- A withdrawal is encoded as an RLP list, so any byte/string prefix is a
    reason-erased semantic failure. -/
theorem decodeWithdrawal_none_of_head_lt_c0
    (pfx : Byte) (rest : List Byte)
    (h : BitVec.ult (pfx.zeroExtend 64) (0xc0 : Word) = true) :
    decodeWithdrawal (pfx :: rest) = none := by
  unfold decodeWithdrawal
  generalize hfull : decodeFully (pfx :: rest) = decoded
  cases decoded with
  | none => rfl
  | some item =>
      cases item with
      | bytes _ => rfl
      | list items =>
          exfalso
          exact decodeFully_ne_list_of_head_lt_c0 pfx rest items h hfull

/-- A failed complete RLP decode is a reason-erased withdrawal failure. -/
theorem decodeWithdrawal_none_of_decodeFully_none
    {input : List Byte} (hfull : decodeFully input = none) :
    decodeWithdrawal input = none := by
  unfold decodeWithdrawal
  rw [hfull]

/-- A failed raw RLP decode is a reason-erased withdrawal failure. -/
theorem decodeWithdrawal_none_of_decode_none
    {input : List Byte} (hdecode : decode input = none) :
    decodeWithdrawal input = none :=
  decodeWithdrawal_none_of_decodeFully_none (decodeFully_eq_none_of_decode_none hdecode)

/-- A raw RLP decode with trailing input is a reason-erased withdrawal failure. -/
theorem decodeWithdrawal_none_of_decode_leftover
    {input leftover : List Byte} {item : RLPItem}
    (hdecode : decode input = some (item, leftover))
    (hleftover : leftover ≠ []) :
    decodeWithdrawal input = none :=
  decodeWithdrawal_none_of_decodeFully_none
    (decodeFully_eq_none_of_decode_leftover hdecode hleftover)

/-- A complete RLP bytes item cannot be a withdrawal list. -/
theorem decodeWithdrawal_none_of_decodeFully_bytes
    {input data : List Byte} (hfull : decodeFully input = some (.bytes data)) :
    decodeWithdrawal input = none := by
  unfold decodeWithdrawal
  rw [hfull]

/-- A completely decoded list with the wrong arity is rejected by
    `decodeWithdrawal`; the precise failure reason is intentionally erased. -/
theorem decodeWithdrawal_none_of_decodeFully_list_length_ne_four
    {input : List Byte} {items : List RLPItem}
    (hfull : decodeFully input = some (.list items))
    (hlen : items.length ≠ 4) :
    decodeWithdrawal input = none := by
  cases hdec : decodeWithdrawal input with
  | none => rfl
  | some w =>
      exfalso
      rcases (decodeWithdrawal_eq_some_iff input w).mp hdec with
        ⟨d0, d1, d2, d3, hfull', _hc0, _hl0, _hc1, _hl1, _haddr, _hc3, _hl3,
          _hi, _hv, _ha, _hamt⟩
      have hsome : some (RLPItem.list items) =
          some (RLPItem.list [RLPItem.bytes d0, RLPItem.bytes d1, RLPItem.bytes d2,
            RLPItem.bytes d3]) :=
        hfull.symm.trans hfull'
      have hitems : items = [RLPItem.bytes d0, RLPItem.bytes d1, RLPItem.bytes d2,
          RLPItem.bytes d3] := by
        simpa using hsome
      apply hlen
      rw [hitems]
      rfl

/-- A nonempty byte stream cannot decode as zero list-payload items with
    positive fuel. -/
theorem decodeItems_ne_empty_of_ne_nil
    {fuel : Nat} {bs : List Byte}
    (hfuel : 1 ≤ fuel) (hne : bs ≠ []) :
    decodeItems fuel bs ≠ some ([], []) := by
  intro hitems
  obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := by
    cases fuel with
    | zero => omega
    | succ fuel' => exact ⟨fuel', rfl⟩
  rw [decodeItems_succ_of_ne_nil fuel' bs hne] at hitems
  cases haux : decodeAux fuel' bs with
  | none =>
      simp [haux] at hitems
  | some decoded =>
      rcases decoded with ⟨item, rest⟩
      cases hrest : decodeItems fuel' rest with
      | none =>
          simp [haux, hrest] at hitems
      | some decodedRest =>
          rcases decodedRest with ⟨items, rest'⟩
          simp [haux, hrest] at hitems

/-- If four byte-string field decoders have succeeded inside a short-list
    payload but the cursor has not reached the payload end, the withdrawal decode
    is a reason-erased semantic failure. This is the pure bridge used by the
    validating exact-arity failure path. -/
theorem decodeWithdrawal_none_of_shortList_four_leftover
    (pfx : Byte) (payload : List Byte)
    (off1 off2 off3 off4 : Nat) (d0 d1 d2 d3 : List Byte)
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (h0 : ∀ m, decodeAux (m + 1) payload = some (.bytes d0, payload.drop off1))
    (h1 : ∀ m, decodeAux (m + 1) (payload.drop off1) =
      some (.bytes d1, payload.drop off2))
    (h2 : ∀ m, decodeAux (m + 1) (payload.drop off2) =
      some (.bytes d2, payload.drop off3))
    (h3 : ∀ m, decodeAux (m + 1) (payload.drop off3) =
      some (.bytes d3, payload.drop off4))
    (h_leftover : payload.drop off4 ≠ [])
    (h_min : 2 ≤ payload.length) :
    decodeWithdrawal (pfx :: payload) = none := by
  cases hdec : decodeWithdrawal (pfx :: payload) with
  | none => rfl
  | some w =>
      exfalso
      rcases (decodeWithdrawal_eq_some_iff (pfx :: payload) w).mp hdec with
        ⟨e0, e1, e2, e3, hfull, _hc0, _hl0, _hc1, _hl1, _haddr, _hc3, _hl3,
          _hi, _hv, _ha, _hamt⟩
      have hdecode : decode (pfx :: payload) =
          some (.list [.bytes e0, .bytes e1, .bytes e2, .bytes e3], []) :=
        (decodeFully_eq_some_iff (pfx :: payload)
          (.list [.bytes e0, .bytes e1, .bytes e2, .bytes e3])).1 hfull
      rw [decode_cons_eq_decodeAux_fuel,
        show 2 * payload.length + 2 = (2 * payload.length + 1) + 1 by omega,
        ListDecodeBridge.decodeAux_cons_shortList_eq_decodeListPayload
          (2 * payload.length + 1) pfx payload h_class] at hdecode
      have htake : takeBytes payload (rlpPrefixShortListPayloadLen pfx) =
          some (payload, []) := by
        rw [h_len, takeBytes_length_ge (le_refl payload.length), List.take_length,
          List.drop_length]
      rw [htake] at hdecode
      change Option.bind (ListDecodeBridge.decodeListPayload (2 * payload.length + 1) payload)
          (fun items => some (RLPItem.list items, ([] : List Byte))) =
        some (RLPItem.list [.bytes e0, .bytes e1, .bytes e2, .bytes e3], []) at hdecode
      have hpayload : ListDecodeBridge.decodeListPayload (2 * payload.length + 1) payload =
          some [.bytes e0, .bytes e1, .bytes e2, .bytes e3] := by
        cases hpayload :
            ListDecodeBridge.decodeListPayload (2 * payload.length + 1) payload with
        | none =>
            simp [hpayload] at hdecode
        | some items =>
            simpa [hpayload] using hdecode
      have hitems : decodeItems (2 * payload.length + 1) payload =
          some ([.bytes e0, .bytes e1, .bytes e2, .bytes e3], []) :=
        (ListDecodeBridge.decodeListPayload_eq_some_iff
          (2 * payload.length + 1) payload
          [.bytes e0, .bytes e1, .bytes e2, .bytes e3]).1 hpayload
      have hne0 : payload ≠ [] := by
        intro hnil
        rw [hnil] at h_min
        simp at h_min
      rcases decodeItems_cons_inv payload (.bytes e0)
          [.bytes e1, .bytes e2, .bytes e3] [] (2 * payload.length) hne0 hitems with
        ⟨r0, hitem0, htail0⟩
      have h0fuel : decodeAux (2 * payload.length) payload =
          some (.bytes d0, payload.drop off1) := by
        have h := h0 (2 * payload.length - 1)
        rw [show 2 * payload.length - 1 + 1 = 2 * payload.length by omega] at h
        exact h
      have hr0 : r0 = payload.drop off1 := by
        have h_eq := Option.some.inj (hitem0.symm.trans h0fuel)
        exact congrArg Prod.snd h_eq
      subst r0
      have htail0' : decodeItems ((2 * payload.length - 1) + 1) (payload.drop off1) =
          some ([.bytes e1, .bytes e2, .bytes e3], []) := by
        rw [show 2 * payload.length - 1 + 1 = 2 * payload.length by omega]
        exact htail0
      rcases decodeItems_cons_inv (payload.drop off1) (.bytes e1)
          [.bytes e2, .bytes e3] [] (2 * payload.length - 1)
          (by
            intro hnil
            have hbad := h1 0
            rw [hnil, decodeAux_nil] at hbad
            simp at hbad) htail0' with
        ⟨r1, hitem1, htail1⟩
      have h1fuel : decodeAux (2 * payload.length - 1) (payload.drop off1) =
          some (.bytes d1, payload.drop off2) := by
        have h := h1 (2 * payload.length - 2)
        rw [show 2 * payload.length - 2 + 1 = 2 * payload.length - 1 by omega] at h
        exact h
      have hr1 : r1 = payload.drop off2 := by
        have h_eq := Option.some.inj (hitem1.symm.trans h1fuel)
        exact congrArg Prod.snd h_eq
      subst r1
      have htail1' : decodeItems ((2 * payload.length - 2) + 1) (payload.drop off2) =
          some ([.bytes e2, .bytes e3], []) := by
        rw [show 2 * payload.length - 2 + 1 = 2 * payload.length - 1 by omega]
        exact htail1
      rcases decodeItems_cons_inv (payload.drop off2) (.bytes e2)
          [.bytes e3] [] (2 * payload.length - 2)
          (by
            intro hnil
            have hbad := h2 0
            rw [hnil, decodeAux_nil] at hbad
            simp at hbad) htail1' with
        ⟨r2, hitem2, htail2⟩
      have h2fuel : decodeAux (2 * payload.length - 2) (payload.drop off2) =
          some (.bytes d2, payload.drop off3) := by
        have h := h2 (2 * payload.length - 3)
        rw [show 2 * payload.length - 3 + 1 = 2 * payload.length - 2 by omega] at h
        exact h
      have hr2 : r2 = payload.drop off3 := by
        have h_eq := Option.some.inj (hitem2.symm.trans h2fuel)
        exact congrArg Prod.snd h_eq
      subst r2
      have htail2' : decodeItems ((2 * payload.length - 3) + 1) (payload.drop off3) =
          some ([.bytes e3], []) := by
        rw [show 2 * payload.length - 3 + 1 = 2 * payload.length - 2 by omega]
        exact htail2
      rcases decodeItems_cons_inv (payload.drop off3) (.bytes e3)
          [] [] (2 * payload.length - 3)
          (by
            intro hnil
            have hbad := h3 0
            rw [hnil, decodeAux_nil] at hbad
            simp at hbad) htail2' with
        ⟨r3, hitem3, htail3⟩
      have h3fuel : decodeAux (2 * payload.length - 3) (payload.drop off3) =
          some (.bytes d3, payload.drop off4) := by
        have h := h3 (2 * payload.length - 4)
        rw [show 2 * payload.length - 4 + 1 = 2 * payload.length - 3 by omega] at h
        exact h
      have hr3 : r3 = payload.drop off4 := by
        have h_eq := Option.some.inj (hitem3.symm.trans h3fuel)
        exact congrArg Prod.snd h_eq
      subst r3
      exact decodeItems_ne_empty_of_ne_nil (fuel := 2 * payload.length - 3)
        (bs := payload.drop off4) (by omega) h_leftover htail3

/-- If four byte-string field decoders have succeeded inside a short-list
    payload but the fourth remainder is nonempty, the withdrawal decode fails.
    This chain form matches validating WP field posts and hides synthetic offsets. -/
theorem decodeWithdrawal_none_of_shortList_four_leftover_chain
    (pfx : Byte) (payload r1 r2 r3 r4 : List Byte) (d0 d1 d2 d3 : List Byte)
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (h0 : ∀ m, decodeAux (m + 1) payload = some (.bytes d0, r1))
    (h1 : ∀ m, decodeAux (m + 1) r1 = some (.bytes d1, r2))
    (h2 : ∀ m, decodeAux (m + 1) r2 = some (.bytes d2, r3))
    (h3 : ∀ m, decodeAux (m + 1) r3 = some (.bytes d3, r4))
    (h_leftover : r4 ≠ [])
    (h_min : 2 ≤ payload.length) :
    decodeWithdrawal (pfx :: payload) = none := by
  cases hdec : decodeWithdrawal (pfx :: payload) with
  | none => rfl
  | some w =>
      exfalso
      rcases (decodeWithdrawal_eq_some_iff (pfx :: payload) w).mp hdec with
        ⟨e0, e1, e2, e3, hfull, _hc0, _hl0, _hc1, _hl1, _haddr, _hc3, _hl3,
          _hi, _hv, _ha, _hamt⟩
      have hdecode : decode (pfx :: payload) =
          some (.list [.bytes e0, .bytes e1, .bytes e2, .bytes e3], []) :=
        (decodeFully_eq_some_iff (pfx :: payload)
          (.list [.bytes e0, .bytes e1, .bytes e2, .bytes e3])).1 hfull
      rw [decode_cons_eq_decodeAux_fuel,
        show 2 * payload.length + 2 = (2 * payload.length + 1) + 1 by omega,
        ListDecodeBridge.decodeAux_cons_shortList_eq_decodeListPayload
          (2 * payload.length + 1) pfx payload h_class] at hdecode
      have htake : takeBytes payload (rlpPrefixShortListPayloadLen pfx) =
          some (payload, []) := by
        rw [h_len, takeBytes_length_ge (le_refl payload.length), List.take_length,
          List.drop_length]
      rw [htake] at hdecode
      change Option.bind (ListDecodeBridge.decodeListPayload (2 * payload.length + 1) payload)
          (fun items => some (RLPItem.list items, ([] : List Byte))) =
        some (RLPItem.list [.bytes e0, .bytes e1, .bytes e2, .bytes e3], []) at hdecode
      have hpayload : ListDecodeBridge.decodeListPayload (2 * payload.length + 1) payload =
          some [.bytes e0, .bytes e1, .bytes e2, .bytes e3] := by
        cases hpayload :
            ListDecodeBridge.decodeListPayload (2 * payload.length + 1) payload with
        | none =>
            simp [hpayload] at hdecode
        | some items =>
            simpa [hpayload] using hdecode
      have hitems : decodeItems (2 * payload.length + 1) payload =
          some ([.bytes e0, .bytes e1, .bytes e2, .bytes e3], []) :=
        (ListDecodeBridge.decodeListPayload_eq_some_iff
          (2 * payload.length + 1) payload
          [.bytes e0, .bytes e1, .bytes e2, .bytes e3]).1 hpayload
      have hne0 : payload ≠ [] := by
        intro hnil
        rw [hnil] at h_min
        simp at h_min
      rcases decodeItems_cons_inv payload (.bytes e0)
          [.bytes e1, .bytes e2, .bytes e3] [] (2 * payload.length) hne0 hitems with
        ⟨r0, hitem0, htail0⟩
      have h0fuel : decodeAux (2 * payload.length) payload = some (.bytes d0, r1) := by
        have h := h0 (2 * payload.length - 1)
        rw [show 2 * payload.length - 1 + 1 = 2 * payload.length by omega] at h
        exact h
      have hr0 : r0 = r1 := by
        have h_eq := Option.some.inj (hitem0.symm.trans h0fuel)
        exact congrArg Prod.snd h_eq
      subst r0
      have htail0' : decodeItems ((2 * payload.length - 1) + 1) r1 =
          some ([.bytes e1, .bytes e2, .bytes e3], []) := by
        rw [show 2 * payload.length - 1 + 1 = 2 * payload.length by omega]
        exact htail0
      rcases decodeItems_cons_inv r1 (.bytes e1) [.bytes e2, .bytes e3] []
          (2 * payload.length - 1)
          (by
            intro hnil
            have hbad := h1 0
            rw [hnil, decodeAux_nil] at hbad
            simp at hbad) htail0' with
        ⟨r1', hitem1, htail1⟩
      have h1fuel : decodeAux (2 * payload.length - 1) r1 = some (.bytes d1, r2) := by
        have h := h1 (2 * payload.length - 2)
        rw [show 2 * payload.length - 2 + 1 = 2 * payload.length - 1 by omega] at h
        exact h
      have hr1 : r1' = r2 := by
        have h_eq := Option.some.inj (hitem1.symm.trans h1fuel)
        exact congrArg Prod.snd h_eq
      subst r1'
      have htail1' : decodeItems ((2 * payload.length - 2) + 1) r2 =
          some ([.bytes e2, .bytes e3], []) := by
        rw [show 2 * payload.length - 2 + 1 = 2 * payload.length - 1 by omega]
        exact htail1
      rcases decodeItems_cons_inv r2 (.bytes e2) [.bytes e3] [] (2 * payload.length - 2)
          (by
            intro hnil
            have hbad := h2 0
            rw [hnil, decodeAux_nil] at hbad
            simp at hbad) htail1' with
        ⟨r2', hitem2, htail2⟩
      have h2fuel : decodeAux (2 * payload.length - 2) r2 = some (.bytes d2, r3) := by
        have h := h2 (2 * payload.length - 3)
        rw [show 2 * payload.length - 3 + 1 = 2 * payload.length - 2 by omega] at h
        exact h
      have hr2 : r2' = r3 := by
        have h_eq := Option.some.inj (hitem2.symm.trans h2fuel)
        exact congrArg Prod.snd h_eq
      subst r2'
      have htail2' : decodeItems ((2 * payload.length - 3) + 1) r3 =
          some ([.bytes e3], []) := by
        rw [show 2 * payload.length - 3 + 1 = 2 * payload.length - 2 by omega]
        exact htail2
      rcases decodeItems_cons_inv r3 (.bytes e3) [] [] (2 * payload.length - 3)
          (by
            intro hnil
            have hbad := h3 0
            rw [hnil, decodeAux_nil] at hbad
            simp at hbad) htail2' with
        ⟨r3', hitem3, htail3⟩
      have h3fuel : decodeAux (2 * payload.length - 3) r3 = some (.bytes d3, r4) := by
        have h := h3 (2 * payload.length - 4)
        rw [show 2 * payload.length - 4 + 1 = 2 * payload.length - 3 by omega] at h
        exact h
      have hr3 : r3' = r4 := by
        have h_eq := Option.some.inj (hitem3.symm.trans h3fuel)
        exact congrArg Prod.snd h_eq
      subst r3'
      exact decodeItems_ne_empty_of_ne_nil (fuel := 2 * payload.length - 3)
        (bs := r4) (by omega) h_leftover htail3

/-- Implicit-argument facade for tactic use of
    `decodeWithdrawal_none_of_shortList_four_leftover`. -/
theorem decodeWithdrawal_none_of_shortList_four_leftover_auto
    {pfx : Byte} {payload d0 d1 d2 d3 : List Byte}
    {off1 off2 off3 off4 : Nat}
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (h0 : ∀ m, decodeAux (m + 1) payload = some (.bytes d0, payload.drop off1))
    (h1 : ∀ m, decodeAux (m + 1) (payload.drop off1) =
      some (.bytes d1, payload.drop off2))
    (h2 : ∀ m, decodeAux (m + 1) (payload.drop off2) =
      some (.bytes d2, payload.drop off3))
    (h3 : ∀ m, decodeAux (m + 1) (payload.drop off3) =
      some (.bytes d3, payload.drop off4))
    (h_leftover : payload.drop off4 ≠ [])
    (h_min : 2 ≤ payload.length) :
    decodeWithdrawal (pfx :: payload) = none :=
  decodeWithdrawal_none_of_shortList_four_leftover pfx payload off1 off2 off3 off4
    d0 d1 d2 d3 h_class h_len h0 h1 h2 h3 h_leftover h_min

/-- Implicit-argument facade for tactic use of the chain-shaped exact-arity
    failure bridge. -/
theorem decodeWithdrawal_none_of_shortList_four_leftover_chain_auto
    {pfx : Byte} {payload r1 r2 r3 r4 d0 d1 d2 d3 : List Byte}
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (h0 : ∀ m, decodeAux (m + 1) payload = some (.bytes d0, r1))
    (h1 : ∀ m, decodeAux (m + 1) r1 = some (.bytes d1, r2))
    (h2 : ∀ m, decodeAux (m + 1) r2 = some (.bytes d2, r3))
    (h3 : ∀ m, decodeAux (m + 1) r3 = some (.bytes d3, r4))
    (h_leftover : r4 ≠ [])
    (h_min : 2 ≤ payload.length) :
    decodeWithdrawal (pfx :: payload) = none :=
  decodeWithdrawal_none_of_shortList_four_leftover_chain pfx payload r1 r2 r3 r4 d0 d1 d2 d3
    h_class h_len h0 h1 h2 h3 h_leftover h_min

/-- Exact-arity failure bridge for generated schema walks.  Once the four
    withdrawal fields have consumed a strict prefix of the short-list payload,
    the public semantic result is failure; the exact failure reason remains
    erased.  The schema itself stays result-free: the field bytes appear only as
    postcondition witnesses. -/
theorem decodeWithdrawal_none_of_shortList_successFieldSpecs_leftover
    (pfx : Byte) (payload tail d0 d1 d2 d3 : List Byte)
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (hl0 : d0.length ≤ 8) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20) (hl3 : d3.length ≤ 8)
    (h_payload : payload = schemaEncBytes (successFieldSpecs d0 d1 d2 d3) ++ tail)
    (h_tail : tail ≠ [])
    (h_min : 2 ≤ payload.length) :
    decodeWithdrawal (pfx :: payload) = none := by
  let off1 := (encodeBytes d0).length
  let off2 := off1 + (encodeBytes d1).length
  let off3 := off2 + (encodeBytes d2).length
  let off4 := off3 + (encodeBytes d3).length
  have h_payload_norm :
      payload =
        encodeBytes d0 ++ (encodeBytes d1 ++ (encodeBytes d2 ++ (encodeBytes d3 ++ tail))) := by
    rw [h_payload]
    simp [schemaEncBytes, successFieldSpecs, encode, List.append_assoc]
  have hd0_lt : d0.length < 256 ^ 8 := by omega
  have hd1_lt : d1.length < 256 ^ 8 := by omega
  have hd2_lt : d2.length < 256 ^ 8 := by omega
  have hd3_lt : d3.length < 256 ^ 8 := by omega
  have hdrop1 :
      payload.drop off1 = encodeBytes d1 ++ (encodeBytes d2 ++ (encodeBytes d3 ++ tail)) := by
    rw [h_payload_norm]
    dsimp [off1]
    rw [List.drop_append_length]
  have hdrop2 : payload.drop off2 = encodeBytes d2 ++ (encodeBytes d3 ++ tail) := by
    rw [h_payload_norm]
    dsimp [off1, off2]
    rw [← List.drop_drop, List.drop_append_length, List.drop_append_length]
  have hdrop3 : payload.drop off3 = encodeBytes d3 ++ tail := by
    rw [h_payload_norm]
    dsimp [off1, off2, off3]
    rw [← List.drop_drop, ← List.drop_drop]
    rw [List.drop_append_length, List.drop_append_length, List.drop_append_length]
  have hdrop4 : payload.drop off4 = tail := by
    rw [h_payload_norm]
    dsimp [off1, off2, off3, off4]
    rw [← List.drop_drop, ← List.drop_drop, ← List.drop_drop]
    rw [List.drop_append_length, List.drop_append_length, List.drop_append_length,
      List.drop_append_length]
  have h0 : ∀ m, decodeAux (m + 1) payload = some (.bytes d0, payload.drop off1) := by
    intro m
    rw [h_payload_norm]
    dsimp [off1]
    rw [decodeAux_succ_encodeBytes_append m d0
      (encodeBytes d1 ++ (encodeBytes d2 ++ (encodeBytes d3 ++ tail))) hd0_lt]
    rw [List.drop_append_length]
  have h1 : ∀ m, decodeAux (m + 1) (payload.drop off1) =
      some (.bytes d1, payload.drop off2) := by
    intro m
    rw [hdrop1]
    rw [decodeAux_succ_encodeBytes_append m d1 (encodeBytes d2 ++ (encodeBytes d3 ++ tail))
      hd1_lt]
    rw [hdrop2]
  have h2 : ∀ m, decodeAux (m + 1) (payload.drop off2) =
      some (.bytes d2, payload.drop off3) := by
    intro m
    rw [hdrop2]
    rw [decodeAux_succ_encodeBytes_append m d2 (encodeBytes d3 ++ tail) hd2_lt]
    rw [hdrop3]
  have h3 : ∀ m, decodeAux (m + 1) (payload.drop off3) =
      some (.bytes d3, payload.drop off4) := by
    intro m
    rw [hdrop3]
    rw [decodeAux_succ_encodeBytes_append m d3 tail hd3_lt]
    rw [hdrop4]
  have h_leftover : payload.drop off4 ≠ [] := by
    rw [hdrop4]
    exact h_tail
  exact decodeWithdrawal_none_of_shortList_four_leftover pfx payload off1 off2 off3 off4
    d0 d1 d2 d3 h_class h_len h0 h1 h2 h3 h_leftover h_min

/-- Implicit-argument facade for tactic use with a schema payload-concat fact. -/
theorem decodeWithdrawal_none_of_shortList_successFieldSpecs_leftover_auto
    {pfx : Byte} {payload tail d0 d1 d2 d3 : List Byte}
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (hl0 : d0.length ≤ 8) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20) (hl3 : d3.length ≤ 8)
    (h_payload : payload = schemaEncBytes (successFieldSpecs d0 d1 d2 d3) ++ tail)
    (h_tail : tail ≠ [])
    (h_min : 2 ≤ payload.length) :
    decodeWithdrawal (pfx :: payload) = none :=
  decodeWithdrawal_none_of_shortList_successFieldSpecs_leftover pfx payload tail d0 d1 d2 d3
    h_class h_len hl0 hl1 haddr hl3 h_payload h_tail h_min

/-- Four decoded byte fields that fail the withdrawal field contract are a
    semantic failure, independent of which guard failed. -/
theorem decodeWithdrawal_none_of_decodeFully_fields_not_canonical
    {input d0 d1 d2 d3 : List Byte}
    (hfull : decodeFully input = some (.list [.bytes d0, .bytes d1, .bytes d2, .bytes d3]))
    (hbad : ¬
      (d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
        d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
        d2.length = 20 ∧
        d3.headD 1 ≠ 0 ∧ d3.length ≤ 8)) :
    decodeWithdrawal input = none := by
  cases hdec : decodeWithdrawal input with
  | none => rfl
  | some _w =>
      exfalso
      unfold decodeWithdrawal at hdec
      rw [hfull] at hdec
      simp at hdec
      have hgood :
          d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
            d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
            d2.length = 20 ∧
            d3.headD 1 ≠ 0 ∧ d3.length ≤ 8 := by
        simpa [List.headD_eq_head?] using hdec.1
      exact hbad hgood

/-- The shallow empty-input split has a semantic failure head exit and one
    syntactic nonzero fall-through exit. -/
theorem walkInitEmptyInputFailureNBranch_exits
    (base inputBase outBase raVal statusOld : Word) :
    (walkInitEmptyInputFailureNBranch base inputBase outBase raVal statusOld).exits =
      [ (failStatusReturnExit raVal, emptyInputFailurePost inputBase outBase raVal)
      , (base + 4,
          walkInitNonzeroOpenStatusPost (0 : Word) raVal statusOld **
            emptyInputAbiFrame inputBase outBase)
      ] := by
  rfl

/-- The nonzero fall-through exit of the empty-input specialization is
    contradictory because it carries `0 != 0`. -/
theorem walkInitEmptyInputNonzeroExit_contradicts
    (inputBase outBase raVal statusOld : Word) :
    ∀ h,
      (walkInitNonzeroOpenStatusPost (0 : Word) raVal statusOld **
        emptyInputAbiFrame inputBase outBase) h → False := by
  intro h hp
  unfold walkInitNonzeroOpenStatusPost walkInitNonzeroPost at hp
  rcases hp with ⟨hMain, _hFrame, _hdFrame, _hunionFrame, hMain_prop, _hFrame_prop⟩
  rcases hMain_prop with ⟨hRegs, _hFail, _hdFail, _hunionFail, hRegs_prop, _hFail_prop⟩
  rcases hRegs_prop with ⟨_hRegs, hTail, _hdTail, _hunionTail, _hRegs_prop, hTail_prop⟩
  rcases hTail_prop with ⟨_hX0, _hPure, _hdPure, _hunionPure, _hX0_prop, hPure_prop⟩
  unfold EvmAsm.Rv64.pure at hPure_prop
  exact hPure_prop.2 rfl

attribute [rv64_wp_dead] walkInitEmptyInputNonzeroExit_contradicts

/-- Resolved empty-input certificate: the impossible nonzero exit is closed by
    contradiction, leaving the semantic failure post as the only result. -/
def walkInitEmptyInputFailureCert
    (base inputBase outBase raVal statusOld : Word) :
    WP.CFG.Cert base (failStatusReturnExit raVal) (walkInitEmptyFailStatusCode base)
      (emptyInputFailurePost inputBase outBase raVal) := by
  let br := walkInitEmptyInputFailureNBranch base inputBase outBase raVal statusOld
  wp_rv64_nbranch_join2_resolve_first_dead_auto br,
    (walkInitEmptyInputFailureNBranch_exits base inputBase outBase raVal statusOld),
    (emptyInputFailurePost inputBase outBase raVal)

/-- The resolved empty-input certificate reduces to the shallow walk-init
    empty-input precondition. -/
theorem walkInitEmptyInputFailureCert_pre
    (base inputBase outBase raVal statusOld : Word) :
    (walkInitEmptyInputFailureCert base inputBase outBase raVal statusOld).pre =
      (walkInitEmptyInputFailureNBranch base inputBase outBase raVal statusOld).pre := by
  rfl

/-- Scratch facts preserved by the empty-input failure case after exposing the
    public ABI failure component. -/
def walkInitEmptyFailAbiFrame (listLen t0Old t1Old : Word) : Assertion :=
  ((.x11 ↦ᵣ listLen) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
    ⌜listLen = (0 : Word)⌝)

/-- Scratch facts preserved by the not-list failure case after exposing the
    public ABI failure component. -/
def walkInitNotListFailAbiFrame
    (listBase listLen : Word) (listBytes : List Byte)
    (listOff : Nat) (hoff : listOff < listBytes.length) : Assertion :=
  ((.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
    (.x5 ↦ᵣ walkInitPrefixWord listBytes listOff hoff) **
    (.x6 ↦ᵣ (0xc0 : Word)) **
    ⌜listLen ≠ (0 : Word)⌝ **
    ⌜BitVec.ult (walkInitPrefixWord listBytes listOff hoff) (0xc0 : Word)⌝)

theorem walkInitEmptyFailOutputPost_entails_abiFailureFrame
    (inputBase listLen raVal t0Old t1Old outBase : Word) (input : List Byte)
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hBound : input.length < 2 ^ 64) :
    WP.Entails
      (walkInitEmptyFailOutputPost inputBase listLen raVal t0Old t1Old outBase input)
      (abiPost inputBase outBase raVal input ** walkInitEmptyFailAbiFrame listLen t0Old t1Old) := by
  intro h hp
  have hpCase := hp
  unfold walkInitEmptyFailOutputPost walkInitEmptyFailStatusPost failStatusReturnPost
    statusReturnPost walkInitZeroPost at hpCase
  rcases hpCase with ⟨hA, _hOut, _hdOut, _hunionOut, hA_prop, _hOut_prop⟩
  rcases hA_prop with ⟨hB, _hBytes, _hdBytes, _hunionBytes, hB_prop, _hBytes_prop⟩
  rcases hB_prop with ⟨hC, _hX6, _hdX6, _hunionX6, hC_prop, _hX6_prop⟩
  rcases hC_prop with ⟨_hX1, _hX10, _hdX10, _hunionX10, _hX1_prop, _hX10_prop⟩
  have hX6Pure := _hX6_prop
  extract_pure hX6Pure
  have hzero : listLen = (0 : Word) := hX6Pure.1
  have hLengthZero : input.length = 0 := by
    have heq : BitVec.ofNat 64 input.length = (0 : Word) := by
      rw [← hLen]
      exact hzero
    have htn := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from by decide] at htn
    rw [Nat.mod_eq_of_lt hBound] at htn
    exact htn
  have hnil : input = [] := by
    cases input with
    | nil => rfl
    | cons _ _ => simp at hLengthZero
  have hdec : decodeWithdrawal input = none := by
    rw [hnil]
    exact decodeWithdrawal_nil
  unfold walkInitEmptyFailOutputPost walkInitEmptyFailStatusPost failStatusReturnPost
    statusReturnPost walkInitZeroPost at hp
  unfold abiPost walkInitEmptyFailAbiFrame
  rw [resultPost_failure hdec]
  rw [show (⌜decodeWithdrawal input = none⌝ : Assertion) = empAssertion by
    funext h
    unfold EvmAsm.Rv64.pure EvmAsm.Rv64.empAssertion
    apply propext
    constructor
    · intro h_p
      exact h_p.1
    · intro h_empty
      exact ⟨h_empty, hdec⟩]
  simp only [sepConj_emp_right']
  xperm_hyp hp

theorem walkInitNotListFailOutputPost_entails_abiFailureFrame_zeroOff
    (inputBase listLen raVal outBase : Word) (input : List Byte)
    (hoff : 0 < input.length) :
    WP.Entails
      (walkInitNotListFailOutputPost inputBase listLen raVal outBase input 0 hoff)
      (abiPost inputBase outBase raVal input **
        walkInitNotListFailAbiFrame inputBase listLen input 0 hoff) := by
  intro h hp
  have hpCase := hp
  unfold walkInitNotListFailOutputPost walkInitPrefixNotListFailStatusPost
    walkInitPrefixNotListFailStatusFrame walkInitPrefixWord at hpCase
  rcases hpCase with ⟨hMain, _hOut, _hdOut, _hunionOut, hMain_prop, _hOut_prop⟩
  rcases hMain_prop with ⟨_hFail, hFrame, _hdFrame, _hunionFrame, _hFail_prop, hFrame_prop⟩
  rcases hFrame_prop with ⟨_hFrameHead, hFrameTail, _hdFrameTail, _hunionFrameTail,
    _hFrameHead_prop, hFrameTail_prop⟩
  have hFrameTailPure := hFrameTail_prop
  extract_pure hFrameTailPure
  have hlt : BitVec.ult (walkInitPrefixWord input 0 hoff) (0xc0 : Word) = true :=
    hFrameTailPure.1
  have hdec : decodeWithdrawal input = none := by
    cases input with
    | nil => simp at hoff
    | cons pfx rest =>
        simpa using decodeWithdrawal_none_of_head_lt_c0 pfx rest hlt
  unfold walkInitNotListFailOutputPost walkInitPrefixNotListFailStatusPost
    walkInitPrefixNotListFailStatusFrame failStatusReturnPost statusReturnPost walkInitPrefixWord at hp
  unfold abiPost walkInitNotListFailAbiFrame walkInitPrefixWord
  rw [resultPost_failure hdec]
  rw [show (⌜decodeWithdrawal input = none⌝ : Assertion) = empAssertion by
    funext h
    unfold EvmAsm.Rv64.pure EvmAsm.Rv64.empAssertion
    apply propext
    constructor
    · intro h_p
      exact h_p.1
    · intro h_empty
      exact ⟨h_empty, hdec⟩]
  simp only [sepConj_emp_right']
  xperm_hyp hp

/-- Walk-init classifier whose empty and not-list exits expose the semantic ABI
    failure post, while short-list and long-list candidates remain open. -/
def walkInitEmptyNotListAbiFailureNBranch
    (base inputBase listLen raVal t0Old t1Old outBase : Word)
    (input : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover0 : inputBase.toNat + 0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (inputBase + BitVec.ofNat 64 0) = true)
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hBound : input.length < 2 ^ 64) :
    WP.NBranch base (walkInitEmptyFailNotListFailShortLongCode base) :=
  walkInitEmptyFailNotListFailShortLongOutputCaseNBranch base inputBase listLen raVal
    t0Old t1Old outBase input 0 hsalign hoff hover0 hvalid0
    (abiPost inputBase outBase raVal input ** walkInitEmptyFailAbiFrame listLen t0Old t1Old)
    (abiPost inputBase outBase raVal input ** walkInitNotListFailAbiFrame inputBase listLen input 0 hoff)
    (walkInitShortListOutputPost inputBase listLen raVal outBase input 0 hoff)
    (walkInitLongListOutputPost inputBase listLen raVal outBase input 0 hoff)
    (walkInitEmptyFailOutputPost_entails_abiFailureFrame inputBase listLen raVal t0Old t1Old
      outBase input hLen hBound)
    (walkInitNotListFailOutputPost_entails_abiFailureFrame_zeroOff inputBase listLen raVal
      outBase input hoff)
    (WP.Entails.refl _)
    (WP.Entails.refl _)

theorem walkInitEmptyNotListAbiFailureNBranch_pre
    (base inputBase listLen raVal t0Old t1Old outBase : Word)
    (input : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover0 : inputBase.toNat + 0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (inputBase + BitVec.ofNat 64 0) = true)
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hBound : input.length < 2 ^ 64) :
    (walkInitEmptyNotListAbiFailureNBranch base inputBase listLen raVal t0Old t1Old outBase
      input hsalign hoff hover0 hvalid0 hLen hBound).pre =
      (walkInitEmptyFailNotListFailShortLongOutputNBranch base inputBase listLen raVal t0Old
        t1Old outBase input 0 hsalign hoff hover0 hvalid0).pre := by
  rfl

theorem walkInitEmptyNotListAbiFailureNBranch_exits
    (base inputBase listLen raVal t0Old t1Old outBase : Word)
    (input : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover0 : inputBase.toNat + 0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (inputBase + BitVec.ofNat 64 0) = true)
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hBound : input.length < 2 ^ 64) :
    (walkInitEmptyNotListAbiFailureNBranch base inputBase listLen raVal t0Old t1Old outBase
      input hsalign hoff hover0 hvalid0 hLen hBound).exits =
      [ (failStatusReturnExit raVal,
          abiPost inputBase outBase raVal input ** walkInitEmptyFailAbiFrame listLen t0Old t1Old)
      , (failStatusReturnExit raVal,
          abiPost inputBase outBase raVal input **
            walkInitNotListFailAbiFrame inputBase listLen input 0 hoff)
      , (base + 124,
          walkInitShortListOutputPost inputBase listLen raVal outBase input 0 hoff)
      , (base + 28,
          walkInitLongListOutputPost inputBase listLen raVal outBase input 0 hoff)
      ] := by
  rfl

end WithdrawalDecode

end EvmAsm.Rv64.RLP
