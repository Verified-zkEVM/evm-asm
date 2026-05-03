/-
  EvmAsm.Evm64.MLoad.ByteWindow

  Small semantic bridges for the unaligned MLOAD byte-window helpers in
  `MLoad.Spec`. These lemmas make explicit that the byte selected from a
  dword pair is governed by the runtime byte offset and selected dword value;
  no alignment premise is needed at this pure layer.
-/

import EvmAsm.Evm64.MLoad.Spec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Generic byte-window bridge for MLOAD: once a runtime address has the
    expected byte offset, the dword-pair byte helper is just `extractByte`
    from the selected low/high dword value at that runtime offset. -/
theorem mloadByteFromDwordPair_eq_extractByte_of_byteOffset
    (loVal hiVal addr : Word) (start i : Nat)
    (h_byte : byteOffset addr = (start + i) % 8) :
    mloadByteFromDwordPair loVal hiVal start i =
      extractByte (mloadDwordPairVal loVal hiVal start i) (byteOffset addr) := by
  rw [mloadByteFromDwordPair_eq_extractByte_pair, h_byte]

/-- Zero-extended form of `mloadByteFromDwordPair_eq_extractByte_of_byteOffset`
    for executable specs whose byte loads land in 64-bit registers. -/
theorem mloadByteFromDwordPair_zeroExtend_eq_extractByte_of_byteOffset
    (loVal hiVal addr : Word) (start i : Nat)
    (h_byte : byteOffset addr = (start + i) % 8) :
    (mloadByteFromDwordPair loVal hiVal start i).zeroExtend 64 =
      (extractByte (mloadDwordPairVal loVal hiVal start i)
        (byteOffset addr)).zeroExtend 64 := by
  rw [mloadByteFromDwordPair_eq_extractByte_of_byteOffset
    loVal hiVal addr start i h_byte]

end EvmAsm.Evm64
