/-
  Structural decomposition for K146 `tx_signing_hash_legacy_eip155`.

  The linked routine is an ABI frame around a 101-instruction body.  Keeping
  this fact separate from the semantic body proof makes the frame entry/exit
  addresses explicit without treating the body contract as an assumption.
-/

import EvmAsm.Codegen.Programs.TxSigningHash
import EvmAsm.Rv64.SAsm.AbiFrame

namespace EvmAsm.Codegen.TxSigningHashLegacySpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

abbrev legacyH : Word := BitVec.ofNat 64 GuestAddrs.tx_signing_hash_legacy_eip155

def legacyFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40),
   (.x21, 48), (.x22, 56)]

def legacyBody : List Instr :=
  (txSigningHashLegacyEip155_prog.drop 9).take 101

def legacyCode : CodeReq := CodeReq.ofProg legacyH txSigningHashLegacyEip155_prog

abbrev legacyBodyEntry : Word := legacyH + BitVec.ofNat 64 36
abbrev legacyBodyExit : Word := legacyH + BitVec.ofNat 64 440

theorem legacyFrame_length : legacyFrame.length = 8 := by decide

theorem legacyBody_length : legacyBody.length = 101 := by decide

theorem legacy_prog_length : txSigningHashLegacyEip155_prog.length = 120 := by decide

theorem legacy_prog_eq_abiFrame :
    abiFrameProg (-64 : BitVec 12) (64 : BitVec 12) legacyFrame legacyBody =
      txSigningHashLegacyEip155_prog := by decide

theorem legacyBodyEntry_eq :
    legacyH + BitVec.ofNat 64 (4 * (1 + legacyFrame.length)) = legacyBodyEntry := by
  rw [legacyFrame_length]

theorem legacyBodyExit_eq :
    legacyH + BitVec.ofNat 64
      (4 * (1 + legacyFrame.length + legacyBody.length)) = legacyBodyExit := by
  rw [legacyFrame_length, legacyBody_length]

end EvmAsm.Codegen.TxSigningHashLegacySpec
