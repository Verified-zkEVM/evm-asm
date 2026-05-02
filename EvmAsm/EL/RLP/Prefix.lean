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

end EvmAsm.EL.RLP
