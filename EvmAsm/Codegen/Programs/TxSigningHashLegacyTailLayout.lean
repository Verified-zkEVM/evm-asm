/-
  K146 caller-layout bridges for the H+324 tail composition.
-/

import EvmAsm.Codegen.Programs.TxSigningHashLegacyTailCompose

namespace EvmAsm.Codegen.TxSigningHashLegacyTailCompose

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxSigningHashLegacySpec
open EvmAsm.Codegen.TxSigningHashLegacyCompose
open EvmAsm.Codegen.TxSigningHashLegacyCopySpec
open EvmAsm.Codegen.TxSigningHashLegacyLoopSpec
open EvmAsm.Codegen.TxSigningHashLegacyChainCompose
open EvmAsm.Codegen.TxSigningHashLegacyUintCompose
open EvmAsm.Codegen.TxSigningHashLegacyPrefixCompose
open EvmAsm.Codegen.TxSigningHashLegacyPrefixCopyCompose
open EvmAsm.Codegen.TxSigningHashSpec
open EvmAsm.Codegen.MptSpliceSlotSpec
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.RlpEncodeUintBeSAsm
open EvmAsm.EL.RLP

/-! ## K146's canonical payload slice

    The Nth post reports a selected content offset and length, while the KSS
    source adapter is indexed by the caller's input list.  These lemmas keep
    that bridge in the K146 composition rather than changing the generic Nth
    contract or adding a free payload-equality premise. -/

theorem legacyStrictNthItem_content_ge {bytes : List (BitVec 8)} {base : Word}
    {endOff : Nat} : ∀ {index cursorOff : Nat} {next len : Word},
    EvmAsm.Codegen.RlpListNthItemSAsm.StrictNthItem bytes base
      (base + BitVec.ofNat 64 endOff) index cursorOff next len →
    cursorOff ≤ endOff →
    base.toNat + endOff + 9 < 2 ^ 64 →
    cursorOff ≤ (next - len - base).toNat := by
  intro index cursorOff next len h
  induction h with
  | zero off n l hitem =>
      intro hcursor hover
      exact (EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.rlpItemDecode_spanStart
        hitem hcursor hover).2.1
  | succ idx off n l fn fl hitem hrest ih =>
      intro hcursor hover
      have hadv := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.rlpItemDecode_advance
        hitem hcursor hover
      have hrest_ge := ih hadv.2.2 hover
      exact le_trans (Nat.le_of_lt hadv.2.1) hrest_ge

theorem legacyStrictListPayload_cursor_eq_hdrLen
    {input : List (BitVec 8)} {base : Word} {listLen cursorOff : Nat}
    {endPtr : Word} (h0 : 0 < input.length)
    (hlist : EvmAsm.Codegen.RlpListNthItemSAsm.StrictListPayload input base
      listLen cursorOff endPtr) :
    cursorOff = (legacyHdrLen input h0).toNat := by
  cases hlist with
  | short b hbyte hge hshort hcursor hlen =>
      rw [List.getElem?_eq_getElem h0] at hbyte
      have hb : input[0]'h0 = b := Option.some.inj hbyte
      subst b
      subst cursorOff
      have hlenOf : legacyHdrLen input h0 = (1 : Word) := by
        unfold legacyHdrLen legacyHdrByte
        exact legacyHdrLenOf_short _ hshort
      rw [hlenOf]
      decide
  | long b first hbyte hlong hfirst hnz hminimal hcursor hlen =>
      rw [List.getElem?_eq_getElem h0] at hbyte
      have hb : input[0]'h0 = b := Option.some.inj hbyte
      subst b
      have hlenOf : legacyHdrLen input h0 =
          (input[0]'h0).zeroExtend 64 - (246 : Word) := by
        unfold legacyHdrLen legacyHdrByte
        exact legacyHdrLenOf_long _ hlong
      rw [hlenOf]
      rw [hcursor]
      have hb8 : (input[0]'h0).toNat < 256 := by
        exact (input[0]'h0).isLt
      have hge248 : 248 ≤ (input[0]'h0).toNat := by
        have hh := hlong
        simp [BitVec.ult] at hh
        omega
      bv_omega

theorem legacyStrictNthItem_content_le {bytes : List (BitVec 8)} {base : Word}
    {endOff : Nat} : ∀ {index cursorOff : Nat} {next len : Word},
    EvmAsm.Codegen.RlpListNthItemSAsm.StrictNthItem bytes base
      (base + BitVec.ofNat 64 endOff) index cursorOff next len →
    cursorOff ≤ endOff →
    base.toNat + endOff + 9 < 2 ^ 64 →
    (next - len - base).toNat + len.toNat ≤ endOff := by
  intro index cursorOff next len h
  induction h with
  | zero off n l hitem =>
      intro hcursor hover
      exact (EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.rlpItemDecode_spanStart
        hitem hcursor hover).2.2
  | succ idx off n l fn fl hitem hrest ih =>
      intro hcursor hover
      have hadv := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.rlpItemDecode_advance
        hitem hcursor hover
      exact ih hadv.2.2 hover

theorem legacyNthSuccess_payloadSlice
    {input : List (BitVec 8)} {base hdrLen : Word}
    {listLen : Nat} {offset len : Word}
    (h0 : 0 < input.length)
    (hheader : hdrLen = legacyHdrLen input h0)
    (hslack : listLen + 9 ≤ input.length)
    (hover : base.toNat + input.length < 2 ^ 64)
    (halign : base.toNat % 8 = 0)
    (hsucc : EvmAsm.Codegen.RlpListNthItemSAsm.Success input base listLen 5 offset len) :
    ∃ payload : List (BitVec 8),
      ∃ _sourceSpec : KssInputSourceSpec base hdrLen input payload,
        BitVec.ofNat 64 payload.length = (offset + len) - hdrLen := by
  obtain ⟨cursorOff, endPtr, next, hlist, hnth, hoff⟩ := hsucc
  have hend := hlist.end_eq
  subst endPtr
  have hcur := hlist.cursor_le
  have hover9 : base.toNat + listLen + 9 < 2 ^ 64 := by omega
  have hupper := legacyStrictNthItem_content_le hnth hcur hover9
  have hlower := legacyStrictNthItem_content_ge hnth hcur hover9
  have hcursor := legacyStrictListPayload_cursor_eq_hdrLen h0 hlist
  have hcursorHdr : cursorOff = hdrLen.toNat := by
    simpa [hheader] using hcursor
  have hlower' : hdrLen.toNat ≤ offset.toNat := by
    calc
      hdrLen.toNat = cursorOff := hcursorHdr.symm
      _ ≤ (next - len - base).toNat := hlower
      _ = offset.toNat := by rw [hoff]
  have hupper' : offset.toNat + len.toNat ≤ listLen := by
    simpa [hoff] using hupper
  have hinput : input.length < 2 ^ 64 := by omega
  have hsum : offset.toNat + len.toNat < 2 ^ 64 := by omega
  have hsum_word : (offset + len).toNat = offset.toNat + len.toNat := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt hsum
  have hsub : ((offset + len) - hdrLen).toNat =
      offset.toNat + len.toNat - hdrLen.toNat := by
    rw [BitVec.toNat_sub, hsum_word]
    rw [show 2 ^ 64 - hdrLen.toNat + (offset.toNat + len.toNat) =
        2 ^ 64 + (offset.toNat + len.toNat - hdrLen.toNat) by omega]
    rw [Nat.mod_eq_sub_mod (by omega)]
    have hsub_lt : offset.toNat + len.toNat - hdrLen.toNat < 2 ^ 64 := by omega
    have hcancel : 2 ^ 64 + (offset.toNat + len.toNat - hdrLen.toNat) - 2 ^ 64 =
        offset.toNat + len.toNat - hdrLen.toNat := by omega
    rw [hcancel, Nat.mod_eq_of_lt hsub_lt]
  have hslice_len : hdrLen.toNat + ((offset + len) - hdrLen).toNat ≤ input.length := by
    rw [hsub]
    omega
  let payload : List (BitVec 8) :=
    (input.drop hdrLen.toNat).take ((offset + len - hdrLen).toNat)
  have hpayload_len : payload.length = ((offset + len - hdrLen).toNat) := by
    dsimp [payload]
    simp only [List.length_take, List.length_drop]
    omega
  have hpayload_len_word : BitVec.ofNat 64 payload.length =
      (offset + len) - hdrLen := by
    rw [hpayload_len]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hlen : payload.length + hdrLen.toNat ≤ input.length := by
    rw [hpayload_len]
    omega
  have hpayload : (input.drop hdrLen.toNat).take payload.length = payload := by
    simp [payload]
  refine ⟨payload,
    kssInputSourceSpec_of_payload base hdrLen input payload halign hlen hover hpayload,
    hpayload_len_word⟩

#print axioms legacyNthSuccess_payloadSlice

/-! The canonical source returned above is `kssInputSource`: its payload pair is
    intentionally overridden to lend the caller's input region.  The two other
    KSS segments are linked static buffers.  This small bridge exposes the
    source equation once a pointer is proved not to be the payload pointer and
    is dword aligned; it does not add a memory premise. -/

theorem legacyKssInputSource_static_region
    {input payload bs : List (BitVec 8)} {base hdrLen p : Word}
    (halign : base.toNat % 8 = 0)
    (hlen : payload.length + hdrLen.toNat ≤ input.length)
    (hover : base.toNat + input.length < 2 ^ 64)
    (hbytes : ∀ i (hi : i < payload.length),
      input[hdrLen.toNat + i]'(by omega) = payload[i]'hi)
    (hptr : p ≠ base + hdrLen)
    (hzero : byteOffset p = 0) :
    (kssInputSource base hdrLen input payload halign hlen hover hbytes).region p bs =
      bytesRegion p bs := by
  by_cases hbs : bs = []
  · subst bs
    simp [kssInputSource, hptr, kssSourceRegion]
  · simp [kssInputSource, hptr, kssSourceRegion, hzero, hbs]

/-! `INPUT_MEM_END` is a named linked-layout dependency.  The production
    caller supplies this bound because the transaction slice is carved out of
    the host input zone, while `t155_buf` and its suffix are linked in RAM.
    If either layout moves, these equations must be rechecked; no generic
    `hslack` fact implies them. -/

theorem legacyKssInputSource_prefix_region_of_input_layout
    {input payload : List (BitVec 8)} {base hdrLen : Word}
    (halign : base.toNat % 8 = 0)
    (hlen : payload.length + hdrLen.toNat ≤ input.length)
    (hover : base.toNat + input.length < 2 ^ 64)
    (hbytes : ∀ i (hi : i < payload.length),
      input[hdrLen.toNat + i]'(by omega) = payload[i]'hi)
    (hinput_hi : base.toNat + input.length ≤ EvmAsm.Codegen.INPUT_MEM_END)
    (bs : List (BitVec 8)) :
    (kssInputSource base hdrLen input payload halign hlen hover hbytes).region
      legacyPrefixOutPtr bs = bytesRegion legacyPrefixOutPtr bs := by
  apply legacyKssInputSource_static_region halign hlen hover hbytes
  · intro heq
    have hhdr : hdrLen.toNat ≤ input.length := by omega
    have hbase_sum_hi : base.toNat + hdrLen.toNat ≤ EvmAsm.Codegen.INPUT_MEM_END := by
      omega
    have hbase_lt64 : base.toNat + hdrLen.toNat < 2 ^ 64 := by omega
    have hbase_word : (base + hdrLen).toNat = base.toNat + hdrLen.toNat := by
      rw [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt hbase_lt64
    have hp : legacyPrefixOutPtr.toNat = base.toNat + hdrLen.toNat := by
      calc
        legacyPrefixOutPtr.toNat = (base + hdrLen).toNat := by rw [heq]
        _ = base.toNat + hdrLen.toNat := hbase_word
    have hout : legacyPrefixOutPtr.toNat = GuestAddrs.t155_buf := by
      simp [legacyPrefixOutPtr, GuestAddrs.t155_buf]
    simp only [hout, GuestAddrs.t155_buf] at hp
    simp only [EvmAsm.Codegen.INPUT_MEM_END] at hbase_sum_hi
    omega
  · simp [legacyPrefixOutPtr, GuestAddrs.t155_buf, byteOffset]

theorem legacyKssInputSource_suffix_region_of_input_layout
    {input payload : List (BitVec 8)} {base hdrLen : Word}
    (halign : base.toNat % 8 = 0)
    (hlen : payload.length + hdrLen.toNat ≤ input.length)
    (hover : base.toNat + input.length < 2 ^ 64)
    (hbytes : ∀ i (hi : i < payload.length),
      input[hdrLen.toNat + i]'(by omega) = payload[i]'hi)
    (hinput_hi : base.toNat + input.length ≤ EvmAsm.Codegen.INPUT_MEM_END)
    (bs : List (BitVec 8)) :
    (kssInputSource base hdrLen input payload halign hlen hover hbytes).region
      legacySuffixOutPtr bs = bytesRegion legacySuffixOutPtr bs := by
  apply legacyKssInputSource_static_region halign hlen hover hbytes
  · intro heq
    have hhdr : hdrLen.toNat ≤ input.length := by omega
    have hbase_sum_hi : base.toNat + hdrLen.toNat ≤ EvmAsm.Codegen.INPUT_MEM_END := by
      omega
    have hbase_lt64 : base.toNat + hdrLen.toNat < 2 ^ 64 := by omega
    have hbase_word : (base + hdrLen).toNat = base.toNat + hdrLen.toNat := by
      rw [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt hbase_lt64
    have hp : legacySuffixOutPtr.toNat = base.toNat + hdrLen.toNat := by
      calc
        legacySuffixOutPtr.toNat = (base + hdrLen).toNat := by rw [heq]
        _ = base.toNat + hdrLen.toNat := hbase_word
    have hout : legacySuffixOutPtr.toNat = 0xa3a2bf40 := by
      simp [legacySuffixOutPtr, legacyPrefixOutPtr, GuestAddrs.t155_buf]
    rw [hout] at hp
    simp only [EvmAsm.Codegen.INPUT_MEM_END] at hbase_sum_hi
    omega
  · simp [legacySuffixOutPtr, legacyPrefixOutPtr,
      GuestAddrs.t155_buf, byteOffset]

/-! The combined form is the artifact consumed by the K146 tail composition.
    Keeping both static views under one theorem prevents a caller from
    discharging one side of the linked-buffer separation and silently leaving
    the other side on the generic source premise.  The input-layout bound is
    intentionally still explicit: this theorem records the consequence of a
    caller-owned layout fact; it does not manufacture that fact from `hslack`.
-/

theorem legacyKssInputSource_static_regions_of_input_layout
    {input payload : List (BitVec 8)} {base hdrLen : Word}
    (halign : base.toNat % 8 = 0)
    (hlen : payload.length + hdrLen.toNat ≤ input.length)
    (hover : base.toNat + input.length < 2 ^ 64)
    (hbytes : ∀ i (hi : i < payload.length),
      input[hdrLen.toNat + i]'(by omega) = payload[i]'hi)
    (hinput_hi : base.toNat + input.length ≤ EvmAsm.Codegen.INPUT_MEM_END)
    (prefixBytes suffixBytes : List (BitVec 8)) :
    ((kssInputSource base hdrLen input payload halign hlen hover hbytes).region
      legacyPrefixOutPtr prefixBytes = bytesRegion legacyPrefixOutPtr prefixBytes) ∧
    ((kssInputSource base hdrLen input payload halign hlen hover hbytes).region
      legacySuffixOutPtr suffixBytes = bytesRegion legacySuffixOutPtr suffixBytes) := by
  constructor
  · exact legacyKssInputSource_prefix_region_of_input_layout
      halign hlen hover hbytes hinput_hi prefixBytes
  · exact legacyKssInputSource_suffix_region_of_input_layout
      halign hlen hover hbytes hinput_hi suffixBytes

end EvmAsm.Codegen.TxSigningHashLegacyTailCompose
