/-
  EvmAsm.EL.RLP.Prefix

  Pure RLP prefix-byte classifier. This is the semantic target for the
  RISC-V prefix-classifier phase of the executable decoder.
-/

import EvmAsm.EL.RLP.Basic

namespace EvmAsm.EL.RLP

/-- The five Yellow Paper RLP prefix classes. -/
inductive PrefixClass where
  | singleByte
  | shortBytes
  | longBytes
  | shortList
  | longList
  deriving Repr, BEq, DecidableEq

/-- Classify an RLP prefix byte by its numeric range. -/
def classifyPrefix (pfx : Byte) : PrefixClass :=
  let p := pfx.toNat
  if p < 0x80 then .singleByte
  else if p ≤ 0xB7 then .shortBytes
  else if p ≤ 0xBF then .longBytes
  else if p ≤ 0xF7 then .shortList
  else .longList

/-- Payload length encoded directly in a short string prefix (`0x80..0xB7`). -/
def rlpPrefixShortBytesPayloadLen (pfx : Byte) : Nat :=
  pfx.toNat - 0x80

/-- Number of length bytes following a long string prefix (`0xB8..0xBF`). -/
def rlpPrefixLongBytesLenOfLen (pfx : Byte) : Nat :=
  pfx.toNat - 0xB7

/-- Payload length encoded directly in a short list prefix (`0xC0..0xF7`). -/
def rlpPrefixShortListPayloadLen (pfx : Byte) : Nat :=
  pfx.toNat - 0xC0

/-- Number of length bytes following a long list prefix (`0xF8..0xFF`). -/
def rlpPrefixLongListLenOfLen (pfx : Byte) : Nat :=
  pfx.toNat - 0xF7

theorem classifyPrefix_singleByte_iff (pfx : Byte) :
    classifyPrefix pfx = .singleByte ↔ pfx.toNat < 0x80 := by
  unfold classifyPrefix
  have h_bound : pfx.toNat < 256 := pfx.isLt
  by_cases h0 : pfx.toNat < 0x80
  · simp [h0]
  · by_cases h1 : pfx.toNat ≤ 0xB7
    · simp [h0, h1] <;> omega
    · by_cases h2 : pfx.toNat ≤ 0xBF
      · simp [h0, h1, h2] <;> omega
      · by_cases h3 : pfx.toNat ≤ 0xF7
        · simp [h0, h1, h2, h3] <;> omega
        · simp [h0, h1, h2, h3] <;> omega

theorem classifyPrefix_shortBytes_iff (pfx : Byte) :
    classifyPrefix pfx = .shortBytes ↔ 0x80 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xB7 := by
  unfold classifyPrefix
  have h_bound : pfx.toNat < 256 := pfx.isLt
  by_cases h0 : pfx.toNat < 0x80
  · simp [h0] <;> omega
  · by_cases h1 : pfx.toNat ≤ 0xB7
    · simp [h0, h1] <;> omega
    · by_cases h2 : pfx.toNat ≤ 0xBF
      · simp [h0, h1, h2] <;> omega
      · by_cases h3 : pfx.toNat ≤ 0xF7
        · simp [h0, h1, h2, h3] <;> omega
        · simp [h0, h1, h2, h3] <;> omega

theorem classifyPrefix_longBytes_iff (pfx : Byte) :
    classifyPrefix pfx = .longBytes ↔ 0xB8 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xBF := by
  unfold classifyPrefix
  have h_bound : pfx.toNat < 256 := pfx.isLt
  by_cases h0 : pfx.toNat < 0x80
  · simp [h0] <;> omega
  · by_cases h1 : pfx.toNat ≤ 0xB7
    · simp [h0, h1] <;> omega
    · by_cases h2 : pfx.toNat ≤ 0xBF
      · simp [h0, h1, h2] <;> omega
      · by_cases h3 : pfx.toNat ≤ 0xF7
        · simp [h0, h1, h2, h3] <;> omega
        · simp [h0, h1, h2, h3] <;> omega

theorem classifyPrefix_shortList_iff (pfx : Byte) :
    classifyPrefix pfx = .shortList ↔ 0xC0 ≤ pfx.toNat ∧ pfx.toNat ≤ 0xF7 := by
  unfold classifyPrefix
  have h_bound : pfx.toNat < 256 := pfx.isLt
  by_cases h0 : pfx.toNat < 0x80
  · simp [h0] <;> omega
  · by_cases h1 : pfx.toNat ≤ 0xB7
    · simp [h0, h1] <;> omega
    · by_cases h2 : pfx.toNat ≤ 0xBF
      · simp [h0, h1, h2] <;> omega
      · by_cases h3 : pfx.toNat ≤ 0xF7
        · simp [h0, h1, h2, h3] <;> omega
        · simp [h0, h1, h2, h3] <;> omega

theorem classifyPrefix_longList_iff (pfx : Byte) :
    classifyPrefix pfx = .longList ↔ 0xF8 ≤ pfx.toNat := by
  unfold classifyPrefix
  have h_bound : pfx.toNat < 256 := pfx.isLt
  by_cases h0 : pfx.toNat < 0x80
  · simp [h0] <;> omega
  · by_cases h1 : pfx.toNat ≤ 0xB7
    · simp [h0, h1] <;> omega
    · by_cases h2 : pfx.toNat ≤ 0xBF
      · simp [h0, h1, h2] <;> omega
      · by_cases h3 : pfx.toNat ≤ 0xF7
        · simp [h0, h1, h2, h3] <;> omega
        · simp [h0, h1, h2, h3] <;> omega

theorem rlpPrefixShortBytesPayloadLen_le_55_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .shortBytes) :
    rlpPrefixShortBytesPayloadLen pfx ≤ 55 := by
  rw [classifyPrefix_shortBytes_iff] at h
  unfold rlpPrefixShortBytesPayloadLen
  omega

theorem rlpPrefixShortListPayloadLen_le_55_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .shortList) :
    rlpPrefixShortListPayloadLen pfx ≤ 55 := by
  rw [classifyPrefix_shortList_iff] at h
  unfold rlpPrefixShortListPayloadLen
  omega

theorem rlpPrefixLongBytesLenOfLen_pos_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .longBytes) :
    0 < rlpPrefixLongBytesLenOfLen pfx := by
  rw [classifyPrefix_longBytes_iff] at h
  unfold rlpPrefixLongBytesLenOfLen
  omega

theorem rlpPrefixLongBytesLenOfLen_le_8_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .longBytes) :
    rlpPrefixLongBytesLenOfLen pfx ≤ 8 := by
  rw [classifyPrefix_longBytes_iff] at h
  unfold rlpPrefixLongBytesLenOfLen
  omega

theorem rlpPrefixLongListLenOfLen_pos_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .longList) :
    0 < rlpPrefixLongListLenOfLen pfx := by
  rw [classifyPrefix_longList_iff] at h
  unfold rlpPrefixLongListLenOfLen
  omega

theorem rlpPrefixLongListLenOfLen_le_8_of_class {pfx : Byte}
    (h : classifyPrefix pfx = .longList) :
    rlpPrefixLongListLenOfLen pfx ≤ 8 := by
  rw [classifyPrefix_longList_iff] at h
  unfold rlpPrefixLongListLenOfLen
  have h_bound : pfx.toNat < 256 := pfx.isLt
  omega

end EvmAsm.EL.RLP
