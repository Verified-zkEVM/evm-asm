/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakSpec

  Proof-only correspondence facts for the inline Keccak bridge.  The emitted
  `zkvmKeccak256_prog` remains the flat 69-instruction Program in
  `HashBridgeProg`; this module supplies the concrete CSRS seam and the pure
  padding/absorption facts needed to structure its proof.

  The eventual wrapper theorem quantifies over the ABI envelope documented at
  `docs/4ch8f-top-spec.md:55` and §2a (`MAX_INPUT_BYTES = 0x37FFFFF8`).  That
  envelope is a resource fact, not a smaller proof convenience cap; the fuel
  bound is derived from the input length.
-/

import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Rv64.SAsm.KeccakStep
import EvmAsm.Stateless.SpecRef.Crypto

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Stateless.SpecRef

/-- The padding suffix for a message whose length is a multiple of the rate.
    This is the branch that is easy to lose when modelling the emitted
    residual loop: a zero remainder still gets a complete pad-only block. -/
theorem keccakPad_zero_remainder (msg : Bytes)
    (hrem : msg.length % keccakRateBytes = 0) :
    (keccakPad msg).drop msg.length =
      (0x01 : Byte) :: List.replicate 134 (0 : Byte) ++ [(0x80 : Byte)] := by
  have hrem' : msg.length % 136 = 0 := by
    simpa [keccakRateBytes] using hrem
  simp [keccakPad, keccakRateBytes, hrem']

/-- Two consecutive inline accelerator calls cover the two adjacent
    permutation points used by a full block followed by a pad-only block.
    This is proof-only structure: the emitted bridge remains the flat
    69-instruction program, and this theorem deliberately keeps the concrete
    `Accel.keccakF` image at each seam. -/
theorem keccak_two_csrs_spec_within
    (entry : Word) (rs1 : Reg) (hrs1 : Reg.isExposed rs1 = true)
    (B : Word) (len : Nat) (ws : List (BitVec 8)) (rf : RegFile)
    (hwslen : ws.length = len)
    (hb8 : B.toNat % 8 = 0)
    (hvalid : ∀ j, j < len → isValidMemAddr (B + BitVec.ofNat 64 j) = true)
    (pOff : Nat) (hp : rf.get rs1 = B + BitVec.ofNat 64 pOff)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 200 ≤ len) :
    cpsTripleWithin 2 entry (entry + BitVec.ofNat 64 8)
      (CodeReq.ofProg entry [.CSRS 0x800 rs1, .CSRS 0x800 rs1])
      ((regFileIs rf) ** bytesRegion B ws)
      ((regFileIs rf) ** bytesRegion B
        (setBytes (setBytes ws pOff (keccakBytes ws pOff)) pOff
          (keccakBytes (setBytes ws pOff (keccakBytes ws pOff)) pOff))) := by
  have hws1len : (setBytes ws pOff (keccakBytes ws pOff)).length = len := by
    rw [length_setBytes]
    exact hwslen
  have h1 := csrs_keccak_spec_within entry rs1 hrs1 B len ws rf hwslen
    hb8 hvalid pOff hp h8p hpfit
  have h2 := csrs_keccak_spec_within (entry + 4) rs1 hrs1 B len
    (setBytes ws pOff (keccakBytes ws pOff)) rf hws1len hb8 hvalid pOff hp
    h8p hpfit
  have hd : (CodeReq.singleton entry (.CSRS 0x800 rs1)).Disjoint
      (CodeReq.singleton (entry + 4) (.CSRS 0x800 rs1)) :=
    CodeReq.Disjoint.singleton (by bv_omega)
  have hseq := cpsTripleWithin_seq hd h1 h2
  rw [← CodeReq.ofProg_pair] at hseq
  have hExit : entry + 4 + 4 = entry + BitVec.ofNat 64 8 := by bv_omega
  rw [hExit] at hseq
  exact hseq

end EvmAsm.Codegen.Proofs
