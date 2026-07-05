/-
  EvmAsm.Evm64.Calldata.Region

  The padded calldata byte region (GH #104): the separation-logic resource
  backing the verified CALLDATALOAD bounds-check program.

  `calldataRegionIs cdp data` asserts that the calldata bytes live in memory
  at `cdp = env.callDataPtr` followed by a 32-byte zero tail
  (`paddedCallData`).  The tail is the **padded-region contract**: with it, a
  2-arm bounds check suffices for CALLDATALOAD — any window read starting
  in-bounds (`offset < len`) is fully backed by region cells, and every byte
  read past `len` is zero-backed, so the straddle case
  (`offset < len < offset + 32`) needs no per-byte staging.

  `CalldataRegionWf` bundles the static resource-shape facts (alignment,
  no-wrap, per-byte validity) the extraction lemmas need.  The quarter
  extraction lemmas produce exactly the hypotheses the transported MLOAD
  one-limb engine (`mload_one_limb_unaligned_spec_within`) consumes:

  * `calldataRegionIs_quarter_pair` — the adjacent lo/hi dword pair backing
    window quarter `w ∈ {0, 8, 16, 24}` at in-bounds byte offset `offLo`,
    extracted from the region with a pcFree frame (extract → use → fold back).
  * `calldataRegion_limb_window_ok_q{0,1,2,3}` — the per-quarter
    `mloadLimbWindowOk` side-condition bundle, with the concrete `BitVec 12`
    immediates the CALLDATALOAD window program bakes in.
  * `calldataRegion_dwordPair_byte` — the packed pair bytes are
    `callDataByte` (zero past the end, via the pad).
-/

import EvmAsm.Rv64.MemRegion
import EvmAsm.Evm64.MLoad.Spec
import EvmAsm.Evm64.Calldata.Basic

namespace EvmAsm.Evm64
namespace Calldata

open EvmAsm.Rv64

/-- Calldata bytes followed by the 32-byte zero tail of the padded-region
    contract. -/
def paddedCallData (data : List (BitVec 8)) : List (BitVec 8) :=
  data ++ List.replicate 32 0

@[simp] theorem paddedCallData_length (data : List (BitVec 8)) :
    (paddedCallData data).length = data.length + 32 := by
  simp [paddedCallData]

/-- The calldata byte region: `data` plus the 32-byte zero tail stored at
    the (dword-aligned) calldata pointer `cdp`. -/
def calldataRegionIs (cdp : Word) (data : List (BitVec 8)) : Assertion :=
  bytesRegion cdp (paddedCallData data)

theorem calldataRegionIs_unfold (cdp : Word) (data : List (BitVec 8)) :
    calldataRegionIs cdp data = bytesRegion cdp (paddedCallData data) := rfl

/-- Static resource-shape facts for the calldata region: the pointer is
    dword-aligned, the padded buffer does not wrap the address space, and
    every padded byte is a valid memory access.  These are facts about where
    the caller placed the buffer — not restrictions on the CALLDATALOAD
    operand domain. -/
structure CalldataRegionWf (cdp : Word) (data : List (BitVec 8)) : Prop where
  aligned : cdp.toNat % 8 = 0
  no_wrap : cdp.toNat + (data.length + 32) < 2 ^ 64
  valid : ∀ i, i < data.length + 32 →
    isValidByteAccess (cdp + BitVec.ofNat 64 i) = true

theorem calldataRegionIs_pcFree (cdp : Word) (data : List (BitVec 8)) :
    (calldataRegionIs cdp data).pcFree :=
  bytesRegion_pcFree _ _

instance pcFreeInst_calldataRegionIs (cdp : Word) (data : List (BitVec 8)) :
    Assertion.PCFree (calldataRegionIs cdp data) :=
  ⟨calldataRegionIs_pcFree cdp data⟩

/-- Reading the padded buffer is `callDataByte`: the data prefix in-bounds,
    zero in the 32-byte tail.  Proof-irrelevant in the index bound so it
    rewrites any `getElem` occurrence. -/
theorem paddedCallData_getElem (data : List (BitVec 8)) (idx : Nat)
    (h_idx : idx < (paddedCallData data).length) :
    (paddedCallData data)[idx] = callDataByte data idx := by
  simp only [paddedCallData, List.getElem_append]
  by_cases h_lt : idx < data.length
  · rw [dif_pos h_lt, callDataByte_of_lt h_lt]
  · rw [dif_neg h_lt, List.getElem_replicate,
        callDataByte_of_ge (show data.length ≤ idx by omega)]

/-! ## Quarter extraction

The 32-byte CALLDATALOAD window at in-bounds byte offset `offLo` is read in
four 8-byte quarters with window-byte bases `w ∈ {0, 8, 16, 24}`.  Quarter
`w` reads bytes `offLo + w .. offLo + w + 7`, spanning the adjacent dword
pair `dw = (offLo.toNat + w) / 8` and `dw + 1` of the region, with byte
offset `start = offLo.toNat % 8` into the lo dword (uniform across quarters
because `w % 8 = 0`).  The worst-case hi-dword byte index is
`offLo + w + 7 ≤ (len - 1) + 31 < len + 32` — exactly what the 32-byte pad
guarantees to exist. -/

/-- Extract the adjacent lo/hi dword pair backing window quarter `w` at
    in-bounds byte offset `offLo`, framing the rest of the region.  The cell
    values are the `packBytes` chunks `calldataRegion_dwordPair_byte`
    decodes. -/
theorem calldataRegionIs_quarter_pair (cdp offLo : Word) (data : List (BitVec 8))
    (w : Nat) (h_w_le : w ≤ 24)
    (h_off : offLo.toNat < data.length) :
    ∃ front rest : Assertion, front.pcFree ∧ rest.pcFree ∧
      calldataRegionIs cdp data
        = (front ** (((cdp + BitVec.ofNat 64 (8 * ((offLo.toNat + w) / 8))) ↦ₘ
            packBytes (((paddedCallData data).drop
              (8 * ((offLo.toNat + w) / 8))).take 8)) **
            (((cdp + BitVec.ofNat 64 (8 * ((offLo.toNat + w) / 8) + 8)) ↦ₘ
              packBytes (((paddedCallData data).drop
                (8 * ((offLo.toNat + w) / 8) + 8)).take 8)) ** rest))) := by
  rw [calldataRegionIs_unfold]
  exact bytesRegion_dword_pair_at cdp (paddedCallData data)
    ((offLo.toNat + w) / 8)
    (by rw [paddedCallData_length]; omega)

/-- One byte of the window-quarter side-condition bundle: the address
    `(cdp + offLo) + signExtend12 off` (with `off` evaluating to window byte
    `j`) aligns to the dword containing padded byte `offLo.toNat + j`, is a
    valid access, and has byte offset `(offLo.toNat + j) % 8`. -/
private theorem window_byte_fact (cdp offLo : Word) (data : List (BitVec 8))
    (h_wf : CalldataRegionWf cdp data)
    (h_off : offLo.toNat < data.length)
    (j : Nat) (h_j : j < 32) (off : BitVec 12)
    (h_se : signExtend12 off = BitVec.ofNat 64 j) :
    alignToDword ((cdp + offLo) + signExtend12 off)
        = cdp + BitVec.ofNat 64 (8 * ((offLo.toNat + j) / 8)) ∧
      isValidByteAccess ((cdp + offLo) + signExtend12 off) = true ∧
      byteOffset ((cdp + offLo) + signExtend12 off) = (offLo.toNat + j) % 8 := by
  have h_addr : (cdp + offLo) + signExtend12 off
      = cdp + BitVec.ofNat 64 (offLo.toNat + j) := by
    rw [h_se, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have h_lt := offLo.isLt
    omega
  have h_over : cdp.toNat + (offLo.toNat + j) < 2 ^ 64 := by
    have := h_wf.no_wrap
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [h_addr]
    exact alignToDword_add_ofNat_of_aligned h_wf.aligned h_over
  · rw [h_addr]
    exact h_wf.valid _ (by omega)
  · rw [h_addr]
    exact byteOffset_add_ofNat_of_aligned h_wf.aligned h_over

/-- One `mloadLimbWindowOk` conjunct triple, phrased against the quarter's
    lo/hi pair addresses.  `w` is the quarter byte base, `i` the byte index
    within the quarter (`j = w + i`). -/
private theorem window_byte_conjuncts (cdp offLo : Word) (data : List (BitVec 8))
    (h_wf : CalldataRegionWf cdp data)
    (h_off : offLo.toNat < data.length)
    (w i : Nat) (h_w_mod : w % 8 = 0) (h_w_le : w ≤ 24) (h_i : i < 8)
    (off : BitVec 12)
    (h_se : signExtend12 off = BitVec.ofNat 64 (w + i)) :
    alignToDword ((cdp + offLo) + signExtend12 off)
        = mloadDwordPairAddr
            (cdp + BitVec.ofNat 64 (8 * ((offLo.toNat + w) / 8)))
            (cdp + BitVec.ofNat 64 (8 * ((offLo.toNat + w) / 8) + 8))
            (offLo.toNat % 8) i ∧
      isValidByteAccess ((cdp + offLo) + signExtend12 off) = true ∧
      byteOffset ((cdp + offLo) + signExtend12 off)
        = (offLo.toNat % 8 + i) % 8 := by
  obtain ⟨h_align, h_valid, h_byte⟩ :=
    window_byte_fact cdp offLo data h_wf h_off (w + i) (by omega) off h_se
  refine ⟨?_, h_valid, ?_⟩
  · rw [h_align]
    by_cases h_lo : offLo.toNat % 8 + i < 8
    · rw [mloadDwordPairAddr_low _ _ h_lo]
      have h_div : 8 * ((offLo.toNat + (w + i)) / 8)
          = 8 * ((offLo.toNat + w) / 8) := by omega
      rw [h_div]
    · rw [mloadDwordPairAddr_high _ _ (by omega)]
      have h_div : 8 * ((offLo.toNat + (w + i)) / 8)
          = 8 * ((offLo.toNat + w) / 8) + 8 := by omega
      rw [h_div]
  · rw [h_byte]
    omega

/-- The per-quarter `mloadLimbWindowOk` side-condition bundle, parametric in
    the quarter byte base `w` and the eight 12-bit immediates.  The concrete
    CALLDATALOAD window immediates are supplied by the
    `calldataRegion_limb_window_ok_q{0,1,2,3}` instantiations below. -/
theorem calldataRegion_limb_window_ok (cdp offLo : Word) (data : List (BitVec 8))
    (w : Nat) (off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12)
    (h_wf : CalldataRegionWf cdp data)
    (h_off : offLo.toNat < data.length)
    (h_w_mod : w % 8 = 0) (h_w_le : w ≤ 24)
    (h_se0 : signExtend12 off0 = BitVec.ofNat 64 (w + 0))
    (h_se1 : signExtend12 off1 = BitVec.ofNat 64 (w + 1))
    (h_se2 : signExtend12 off2 = BitVec.ofNat 64 (w + 2))
    (h_se3 : signExtend12 off3 = BitVec.ofNat 64 (w + 3))
    (h_se4 : signExtend12 off4 = BitVec.ofNat 64 (w + 4))
    (h_se5 : signExtend12 off5 = BitVec.ofNat 64 (w + 5))
    (h_se6 : signExtend12 off6 = BitVec.ofNat 64 (w + 6))
    (h_se7 : signExtend12 off7 = BitVec.ofNat 64 (w + 7)) :
    mloadLimbWindowOk (cdp + offLo)
      (cdp + BitVec.ofNat 64 (8 * ((offLo.toNat + w) / 8)))
      (cdp + BitVec.ofNat 64 (8 * ((offLo.toNat + w) / 8) + 8))
      (offLo.toNat % 8) off0 off1 off2 off3 off4 off5 off6 off7 := by
  obtain ⟨a0, v0, b0⟩ := window_byte_conjuncts cdp offLo data h_wf h_off
    w 0 h_w_mod h_w_le (by omega) off0 h_se0
  obtain ⟨a1, v1, b1⟩ := window_byte_conjuncts cdp offLo data h_wf h_off
    w 1 h_w_mod h_w_le (by omega) off1 h_se1
  obtain ⟨a2, v2, b2⟩ := window_byte_conjuncts cdp offLo data h_wf h_off
    w 2 h_w_mod h_w_le (by omega) off2 h_se2
  obtain ⟨a3, v3, b3⟩ := window_byte_conjuncts cdp offLo data h_wf h_off
    w 3 h_w_mod h_w_le (by omega) off3 h_se3
  obtain ⟨a4, v4, b4⟩ := window_byte_conjuncts cdp offLo data h_wf h_off
    w 4 h_w_mod h_w_le (by omega) off4 h_se4
  obtain ⟨a5, v5, b5⟩ := window_byte_conjuncts cdp offLo data h_wf h_off
    w 5 h_w_mod h_w_le (by omega) off5 h_se5
  obtain ⟨a6, v6, b6⟩ := window_byte_conjuncts cdp offLo data h_wf h_off
    w 6 h_w_mod h_w_le (by omega) off6 h_se6
  obtain ⟨a7, v7, b7⟩ := window_byte_conjuncts cdp offLo data h_wf h_off
    w 7 h_w_mod h_w_le (by omega) off7 h_se7
  exact ⟨a0, v0, b0, a1, v1, b1, a2, v2, b2, a3, v3, b3,
         a4, v4, b4, a5, v5, b5, a6, v6, b6, a7, v7, b7⟩

/-- Quarter `w = 24` (first executed block: output limb 0, immediates
    `24..31`). -/
theorem calldataRegion_limb_window_ok_q0 (cdp offLo : Word)
    (data : List (BitVec 8))
    (h_wf : CalldataRegionWf cdp data)
    (h_off : offLo.toNat < data.length) :
    mloadLimbWindowOk (cdp + offLo)
      (cdp + BitVec.ofNat 64 (8 * ((offLo.toNat + 24) / 8)))
      (cdp + BitVec.ofNat 64 (8 * ((offLo.toNat + 24) / 8) + 8))
      (offLo.toNat % 8) 24 25 26 27 28 29 30 31 :=
  calldataRegion_limb_window_ok cdp offLo data 24 _ _ _ _ _ _ _ _ h_wf h_off
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- Quarter `w = 16` (output limb 1, immediates `16..23`). -/
theorem calldataRegion_limb_window_ok_q1 (cdp offLo : Word)
    (data : List (BitVec 8))
    (h_wf : CalldataRegionWf cdp data)
    (h_off : offLo.toNat < data.length) :
    mloadLimbWindowOk (cdp + offLo)
      (cdp + BitVec.ofNat 64 (8 * ((offLo.toNat + 16) / 8)))
      (cdp + BitVec.ofNat 64 (8 * ((offLo.toNat + 16) / 8) + 8))
      (offLo.toNat % 8) 16 17 18 19 20 21 22 23 :=
  calldataRegion_limb_window_ok cdp offLo data 16 _ _ _ _ _ _ _ _ h_wf h_off
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- Quarter `w = 8` (output limb 2, immediates `8..15`). -/
theorem calldataRegion_limb_window_ok_q2 (cdp offLo : Word)
    (data : List (BitVec 8))
    (h_wf : CalldataRegionWf cdp data)
    (h_off : offLo.toNat < data.length) :
    mloadLimbWindowOk (cdp + offLo)
      (cdp + BitVec.ofNat 64 (8 * ((offLo.toNat + 8) / 8)))
      (cdp + BitVec.ofNat 64 (8 * ((offLo.toNat + 8) / 8) + 8))
      (offLo.toNat % 8) 8 9 10 11 12 13 14 15 :=
  calldataRegion_limb_window_ok cdp offLo data 8 _ _ _ _ _ _ _ _ h_wf h_off
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- Quarter `w = 0` (output limb 3, immediates `0..7`). -/
theorem calldataRegion_limb_window_ok_q3 (cdp offLo : Word)
    (data : List (BitVec 8))
    (h_wf : CalldataRegionWf cdp data)
    (h_off : offLo.toNat < data.length) :
    mloadLimbWindowOk (cdp + offLo)
      (cdp + BitVec.ofNat 64 (8 * ((offLo.toNat + 0) / 8)))
      (cdp + BitVec.ofNat 64 (8 * ((offLo.toNat + 0) / 8) + 8))
      (offLo.toNat % 8) 0 1 2 3 4 5 6 7 :=
  calldataRegion_limb_window_ok cdp offLo data 0 _ _ _ _ _ _ _ _ h_wf h_off
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- Decode one window byte from the quarter's packed lo/hi dword pair: the
    byte the engine packs is `callDataByte data (offLo.toNat + w + i)` —
    the real calldata byte in-bounds, zero past the end (via the pad). -/
theorem calldataRegion_dwordPair_byte (data : List (BitVec 8)) (offLo : Word)
    (w i : Nat)
    (h_off : offLo.toNat < data.length)
    (h_w_mod : w % 8 = 0) (h_w_le : w ≤ 24) (h_i : i < 8) :
    mloadByteFromDwordPair
      (packBytes (((paddedCallData data).drop
        (8 * ((offLo.toNat + w) / 8))).take 8))
      (packBytes (((paddedCallData data).drop
        (8 * ((offLo.toNat + w) / 8) + 8)).take 8))
      (offLo.toNat % 8) i
      = callDataByte data (offLo.toNat + w + i) := by
  have h_len : (paddedCallData data).length = data.length + 32 :=
    paddedCallData_length data
  by_cases h_lo : offLo.toNat % 8 + i < 8
  · rw [mloadByteFromDwordPair_low _ _ h_lo,
        show (offLo.toNat % 8 + i) % 8 = offLo.toNat % 8 + i from
          Nat.mod_eq_of_lt h_lo,
        extractByte_packBytes _ _ h_lo
          (by rw [List.length_take, List.length_drop, h_len]; omega),
        List.getElem_take, List.getElem_drop, paddedCallData_getElem]
    congr 1
    omega
  · rw [mloadByteFromDwordPair_high _ _ (by omega),
        show (offLo.toNat % 8 + i) % 8 = offLo.toNat % 8 + i - 8 from by omega,
        extractByte_packBytes _ _ (by omega)
          (by rw [List.length_take, List.length_drop, h_len]; omega),
        List.getElem_take, List.getElem_drop, paddedCallData_getElem]
    congr 1
    omega

/-! ## Anti-vacuity witness

The `CalldataRegionWf` bundle is satisfiable at an ordinary buffer placement
— it is a static fact about where the guest put the calldata arena, not an
operand-domain restriction. -/

example : CalldataRegionWf 4096 [0xde, 0xad, 0xbe, 0xef] :=
  ⟨by decide, by decide, by decide⟩

end Calldata
end EvmAsm.Evm64
