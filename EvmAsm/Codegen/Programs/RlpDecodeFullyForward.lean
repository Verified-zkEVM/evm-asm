/-
  EvmAsm.Codegen.Programs.RlpDecodeFullyForward

  Top of the forward (model → guest) stack: from a whole-input model decode
  `decodeFully bytes = some (.list items)`, produce the two ingredients
  `success_forward` needs — the guest's `StrictListPayload` for the outer
  header and the offset-indexed `DecodeChain` for its children.

  Kept separate from `RlpListNthItemForward.lean` so the list-header inversion
  (which reasons about `decodeFully`/`decodeListPayload`) does not enlarge the
  child-composition module.

  Children must be byte strings, inherited from `ItemDecodeForward`.  For the
  header-extractor family that costs nothing and is in fact **free**:
  `_decode_header` runs `items.mapM rlpBytes?`, and `rlpBytes?` sends `.list`
  to `none`, so a successful header decode already implies it.
-/

import EvmAsm.Codegen.Programs.RlpListNthItemForward

namespace EvmAsm.Codegen.RlpListNthItemSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP

/-- A `takeBytes` that consumes the rest of a suffix pins the split point. -/
private theorem takeBytes_all_of_nil {bytes : List Byte} {k n : Nat}
    {payload : List Byte}
    (h : takeBytes (bytes.drop k) n = some (payload, [])) :
    n = bytes.length - k ∧ payload = bytes.drop k := by
  obtain ⟨hcat, hlen⟩ := takeBytes_eq_some_imp h
  rw [List.append_nil] at hcat
  have := congrArg List.length hcat
  rw [List.length_drop] at this
  exact ⟨by omega, hcat.symm⟩

/-- From a whole-input list decode, the guest's outer-list predicate and the
    child chain, both at the offsets the walk uses.  `listLen` is the full
    buffer length because `decodeFully` leaves no trailing bytes. -/
theorem listPayload_chain_of_decodeFully
    (bytes : List Byte) (base : Word) (items : List RLPItem)
    (hdec : decodeFully bytes = some (.list items))
    (hbytes : ∀ it ∈ items, ∃ q, it = RLPItem.bytes q) :
    ∃ cursorOff,
      StrictListPayload bytes base bytes.length cursorOff
        (base + BitVec.ofNat 64 bytes.length) ∧
      DecodeChain bytes cursorOff items bytes.length := by
  rw [decodeFully_eq_some_iff] at hdec
  cases hbs : bytes with
  | nil => rw [hbs] at hdec; simp [decode, decodeAux] at hdec
  | cons x xs =>
      rw [hbs, decode_cons_eq_decodeAux_fuel] at hdec
      have hfuel : 2 * xs.length + 2 = (2 * xs.length + 1) + 1 := by omega
      rw [hfuel] at hdec
      set n := 2 * xs.length + 1 with hn
      have hxs : (x :: xs).length = xs.length + 1 := rfl
      have hdrop1 : (x :: xs).drop 1 = xs := rfl
      have hget0 : (x :: xs)[0]? = some x := rfl
      cases hclass : classifyPrefix x with
      | singleByte =>
          rw [decodeAux_cons_singleByte_of_classifyPrefix n x xs hclass] at hdec
          simp at hdec
      | shortBytes =>
          rw [decodeAux_cons_shortBytes_of_classifyPrefix n x xs hclass] at hdec
          cases htake : takeBytes xs (rlpPrefixShortBytesPayloadLen x) with
          | none => simp [htake] at hdec
          | some pr =>
              obtain ⟨data, rest'⟩ := pr
              rw [htake] at hdec
              rcases data with _ | ⟨c, tl⟩
              · simp at hdec
              · cases tl with
                | nil => by_cases hc : c.toNat < 128 <;> simp [hc] at hdec
                | cons d ds => simp at hdec
      | longBytes =>
          rw [decodeAux_cons_longBytes_of_classifyPrefix n x xs hclass] at hdec
          cases hread : readLength xs (rlpPrefixLongBytesLenOfLen x) with
          | none => simp [hread] at hdec
          | some pr =>
              obtain ⟨lenVal, rest'⟩ := pr
              rw [hread] at hdec
              by_cases hshort : lenVal ≤ 55
              · simp [hshort] at hdec
              · cases htake : takeBytes rest' lenVal with
                | none => simp [hshort, htake] at hdec
                | some pr2 => obtain ⟨d, r⟩ := pr2; simp [hshort, htake] at hdec
      | shortList =>
          obtain ⟨hlo, hhi⟩ := (classifyPrefix_shortList_iff x).mp hclass
          obtain ⟨payload, htake, hpay⟩ :=
            (ListDecodeBridge.decodeAux_cons_shortList_eq_some_iff n x xs hclass
              items []).mp hdec
          rw [← hdrop1] at htake
          obtain ⟨hplen, hpayEq⟩ := takeBytes_all_of_nil htake
          rw [hxs] at hplen
          have hlenEq : (x :: xs).length = rlpPrefixShortListPayloadLen x + 1 := by
            rw [hxs]; omega
          refine ⟨1, ?_, ?_⟩
          · rw [hlenEq]
            exact strictListPayload_short_forward (x :: xs) base x
              (rlpPrefixShortListPayloadLen x) hget0 (by omega) (by omega) rfl
          · refine decodeItems_to_chain (x :: xs) items n 1 ?_ (by rw [hxs]; omega) hbytes
            rw [hdrop1] at hpayEq
            rw [← hpayEq]
            exact (ListDecodeBridge.decodeListPayload_eq_some_iff n payload items).mp hpay
      | longList =>
          have hlo := (classifyPrefix_longList_iff x).mp hclass
          obtain ⟨lenVal, rest', payload, hread, hlong, htake, hpay⟩ :=
            (ListDecodeBridge.decodeAux_cons_longList_eq_some_iff n x xs hclass
              items []).mp hdec
          have hlolEq : rlpPrefixLongListLenOfLen x = x.toNat - 0xF7 := rfl
          rw [hlolEq] at hread
          obtain ⟨hklen, hlenVal, hrestEq, c, hc0, hcnz⟩ :=
            readLength_inv (by omega) hread
          -- the length bytes sit at offset 1, the payload right after them
          have hrest' : rest' = (x :: xs).drop (1 + (x.toNat - 0xF7)) := by
            rw [hrestEq, show (1 + (x.toNat - 0xF7)) = (x.toNat - 0xF7) + 1 from by omega,
              List.drop_succ_cons]
          rw [hrest'] at htake
          obtain ⟨hplen, hpayEq⟩ := takeBytes_all_of_nil htake
          rw [hxs] at hplen
          have hnz : ∃ first : Byte, (x :: xs)[1]? = some first ∧ first ≠ 0 := by
            refine ⟨c, by simpa using hc0, ?_⟩
            rcases Nat.lt_or_ge 1 (x.toNat - 0xF7) with hk | hk
            · intro hzero
              exact hcnz hk (by rw [hzero]; rfl)
            · have hk1 : x.toNat - 0xF7 = 1 := by omega
              intro hzero
              have hsing : xs.take (x.toNat - 0xF7) = [c] := by
                rw [hk1]
                cases hxx : xs with
                | nil => rw [hxx] at hc0; simp at hc0
                | cons y ys =>
                    rw [hxx] at hc0
                    have hy : y = c := by
                      rw [List.getElem?_eq_getElem (by simp)] at hc0
                      exact Option.some.inj hc0
                    simp [hy]
              rw [hsing] at hlenVal
              have hcv : lenVal = c.toNat := by rw [hlenVal]; simp [Nat.fromBytesBE]
              rw [hzero] at hcv
              simp at hcv
              omega
          have hlenEq : (x :: xs).length
              = 1 + (x.toNat - 0xF7) + (xs.length + 1 - (1 + (x.toNat - 0xF7))) := by
            rw [hxs]; omega
          refine ⟨1 + (x.toNat - 0xF7), ?_, ?_⟩
          · rw [hlenEq]
            refine strictListPayload_long_forward (x :: xs) base x (x.toNat - 0xF7)
              (xs.length + 1 - (1 + (x.toNat - 0xF7))) hget0 (by omega) rfl hnz ?_ (by omega)
            rw [hdrop1, ← hlenVal]
            exact hplen
          · refine decodeItems_to_chain (x :: xs) items n (1 + (x.toNat - 0xF7)) ?_
              (by rw [hxs]; omega) hbytes
            rw [← hpayEq]
            exact (ListDecodeBridge.decodeListPayload_eq_some_iff n payload items).mp hpay

/-! ## Capstone

The whole forward stack in one step: a model decode of the buffer as a list of
byte strings yields the guest's `Success` for whichever child index the model
provides.  This is the form the header extractors consume — for
`header_extract_number`, `index = 8`. -/

theorem success_of_decodeFully_list
    (bytes : List Byte) (base : Word) (items : List RLPItem) (index : Nat) (p : List Byte)
    (hdec : decodeFully bytes = some (.list items))
    (hbytes : ∀ it ∈ items, ∃ q, it = RLPItem.bytes q)
    (hidx : items[index]? = some (RLPItem.bytes p))
    (hover : base.toNat + bytes.length < 2 ^ 64) :
    ∃ offset, Success bytes base bytes.length index offset (BitVec.ofNat 64 p.length) := by
  obtain ⟨cursorOff, hpay, hchain⟩ :=
    listPayload_chain_of_decodeFully bytes base items hdec hbytes
  exact success_forward bytes base bytes.length cursorOff index items p hpay hchain
    hbytes hidx (le_refl _) hover

/-! ## Non-vacuity

`c4 83 01 02 03` decoded by the **model** (not hand-assembled), driven all the
way to the guest's `Success`. -/

set_option maxRecDepth 8000 in
example :
    ∃ offset, Success [0xc4, 0x83, 0x01, 0x02, 0x03] (0x1000 : Word) 5 0 offset
      (BitVec.ofNat 64 3) := by
  refine success_of_decodeFully_list [0xc4, 0x83, 0x01, 0x02, 0x03] (0x1000 : Word)
    [RLPItem.bytes [0x01, 0x02, 0x03]] 0 [0x01, 0x02, 0x03] rfl ?_ rfl (by decide)
  intro it hit
  simp only [List.mem_singleton] at hit
  exact ⟨[0x01, 0x02, 0x03], hit⟩

end EvmAsm.Codegen.RlpListNthItemSAsm
