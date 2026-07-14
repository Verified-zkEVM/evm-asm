/- Framed caller contract for the strict cursor-walk next-item primitive. -/

import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.SAsm.Fn

namespace EvmAsm.Codegen.RlpWalkNextFlatSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

#guard EvmAsm.Rv64.RLP.rlp_walk_next_prog.length = 103

def frameCps
    {n : Nat} {base ret : Word} {cr : CodeReq}
    {P Q : Assertion} (A : Assertion) (hA : A.pcFree)
    (h : cpsTripleWithin n base ret cr P Q) :
    Prop := by
  let _hA := hA
  let _h := h
  exact cpsTripleWithin n base ret cr (P ** A) (Q ** A)

/-- `rlp_walk_next` with a caller-owned ambient assertion framed around the
    exact unified raw post (the canonical success relation and all five
    strict failure statuses are preserved). -/
theorem rlp_walk_next_flat_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (A : Assertion)
    (hA : A.pcFree) (hsalign : srcBase.toNat % 8 = 0)
    (hoff : srcOff < srcBytes.length) (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < srcBytes.length ∧ srcBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    frameCps A hA
      (rlp_walk_next_spec_within base srcBase endPtr raVal a2Old t0Old t1Old t2Old
        t3Old t4Old t5Old t6Old srcBytes srcOff hsalign hoff hover hvalid hss hls hll) := by
  exact cpsTripleWithin_frameR A hA
    (rlp_walk_next_spec_within base srcBase endPtr raVal a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old srcBytes srcOff hsalign hoff hover hvalid hss hls hll)

#print axioms rlp_walk_next_flat_spec_within

end EvmAsm.Codegen.RlpWalkNextFlatSAsm
