/-
  EvmAsm.Evm64.EvmWordArith.SignExtend

  SIGNEXTEND correctness: limb-level sign-extension definitions and getLimb lemmas.
-/

import EvmAsm.Evm64.EvmWordArith.Common

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- SIGNEXTEND
-- ============================================================================

/-- Limb-level sign-extension helper: given shift_amount sa and a limb value,
    compute the sign-extended result and sign fill. -/
def signextLimb (limb sa : Word) : Word :=
  BitVec.sshiftRight (limb <<< (sa.toNat % 64)) (sa.toNat % 64)

def signextFill (limb sa : Word) : Word :=
  BitVec.sshiftRight (signextLimb limb sa) 63

/-- EVM SIGNEXTEND: sign-extend x from byte b.
    If b >= 31, x is unchanged.
    Otherwise, limbs below limb_idx are unchanged, the target limb is
    sign-extended in place, and higher limbs are filled with the sign bit.
    limb_idx = b.toNat / 8, sa = 56 - (b.toNat % 8) * 8. -/
def signextend (b x : EvmWord) : EvmWord :=
  if b.toNat ≥ 31 then x
  else
    let bn := b.toNat
    let limb_idx := bn / 8
    let sa_nat := 56 - (bn % 8) * 8
    let sa : Word := BitVec.ofNat 64 sa_nat
    let target_limb := x.getLimbN limb_idx
    let ext := signextLimb target_limb sa
    let fill := signextFill target_limb sa
    EvmWord.fromLimbs fun i =>
      if i.val < limb_idx then x.getLimb i
      else if i.val = limb_idx then ext
      else fill

/-- When b >= 31, signextend is the identity. -/
theorem signextend_ge31 (b x : EvmWord) (h : b.toNat ≥ 31) :
    signextend b x = x := by
  simp [signextend, h]

/-- When b < 31, getLimb of signextend for limbs below limb_idx. -/
theorem signextend_getLimb_below (b x : EvmWord) (h : ¬ b.toNat ≥ 31)
    (i : Fin 4) (hi : i.val < b.toNat / 8) :
    (signextend b x).getLimb i = x.getLimb i := by
  simp only [signextend, h, ite_false, getLimb_fromLimbs]
  simp only [hi, ite_true]

/-- When b < 31, getLimb of signextend for the target limb. -/
theorem signextend_getLimb_target (b x : EvmWord) (h : ¬ b.toNat ≥ 31)
    (i : Fin 4) (hi : i.val = b.toNat / 8) :
    (signextend b x).getLimb i = signextLimb (x.getLimbN (b.toNat / 8))
      (BitVec.ofNat 64 (56 - (b.toNat % 8) * 8)) := by
  simp only [signextend, h, ite_false, getLimb_fromLimbs]
  simp only [show ¬ (i.val < b.toNat / 8) from by omega, ite_false]
  simp only [hi, ite_true]

/-- When b < 31, getLimb of signextend for limbs above limb_idx. -/
theorem signextend_getLimb_above (b x : EvmWord) (h : ¬ b.toNat ≥ 31)
    (i : Fin 4) (hi : i.val > b.toNat / 8) :
    (signextend b x).getLimb i = signextFill (x.getLimbN (b.toNat / 8))
      (BitVec.ofNat 64 (56 - (b.toNat % 8) * 8)) := by
  simp only [signextend, h, ite_false, getLimb_fromLimbs]
  simp only [show ¬ (i.val < b.toNat / 8) from by omega,
             show ¬ (i.val = b.toNat / 8) from by omega, ite_false]

end EvmWord

end EvmAsm.Evm64
