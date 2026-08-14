/-
  Framed caller contract for the strict cursor-walk initializer.

  The underlying theorem is in the verified Rv64 layer.  This adapter keeps
  its complete nine-way status/result post unchanged and only frames an
  arbitrary caller-owned ambient assertion, which is the shape consumed by
  CPS caller composition.
-/

import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.SAsm.Fn

namespace EvmAsm.Codegen.RlpWalkInitFlatSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm


def frameCps
    {n : Nat} {base ret : Word} {cr : CodeReq}
    {P Q : Assertion} (A : Assertion) (hA : A.pcFree)
    (h : cpsTripleWithin n base ret cr P Q) :
    Prop := by
  let _hA := hA
  let _h := h
  exact cpsTripleWithin n base ret cr (P ** A) (Q ** A)

/-- `rlp_walk_init` with a caller-owned ambient assertion framed around the
    exact unified raw post (all nine strict outcomes are preserved). -/
theorem rlp_walk_init_flat_spec_within
    (base listBase raVal listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat) (A : Assertion)
    (hA : A.pcFree) (hsalign : listBase.toNat % 8 = 0)
    (hoff : listOff < listBytes.length) (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hll_len : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        listOff + 1 + ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ listBytes.length)
    (hll_over : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        listBase.toNat + (listOff + 1 +
          ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hll_valid : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        ∀ k, k < ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (listOff + 1 + k)) = true) :
    frameCps A hA
      (rlp_walk_init_spec_within base listBase raVal listLen a2Old t0Old t1Old t2Old
        t3Old t4Old t5Old t6Old listBytes listOff hsalign hoff hover hvalid hll_len
        hll_over hll_valid) := by
  exact cpsTripleWithin_frameR A hA
    (rlp_walk_init_spec_within base listBase raVal listLen a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old listBytes listOff hsalign hoff hover hvalid hll_len
      hll_over hll_valid)


end EvmAsm.Codegen.RlpWalkInitFlatSAsm
