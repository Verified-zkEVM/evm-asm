import EvmAsm.Evm64.DivMod.LoopDefs.IterV5

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem div128Quot_phase2b_q0'_and_form (q rhat dLo un : Word) :
    (if rhat >>> (32 : BitVec 6).toNat = 0 ∧
        BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo) then
      q + signExtend12 4095 else q) = div128Quot_phase2b_q0' q rhat dLo un := by
  unfold div128Quot_phase2b_q0'
  by_cases h_hi : rhat >>> (32 : BitVec 6).toNat = (0 : Word)
  · by_cases h_ult : BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
    · rw [if_pos ⟨h_hi, h_ult⟩, if_pos h_hi, if_pos h_ult]
    · rw [if_neg (fun h => h_ult h.2), if_pos h_hi, if_neg h_ult]
  · rw [if_neg (fun h => h_hi h.1), if_neg h_hi]

theorem div128Quot_phase2b_rhat_and_form (q rhat dHi dLo un : Word) :
    (if rhat >>> (32 : BitVec 6).toNat = 0 ∧
        BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo) then
      rhat + dHi else rhat) =
      (if rhat >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q * dLo
        let rhatUn := (rhat <<< (32 : BitVec 6).toNat) ||| un
        if BitVec.ult rhatUn qDlo then rhat + dHi else rhat
      else rhat) := by
  by_cases h_hi : rhat >>> (32 : BitVec 6).toNat = (0 : Word)
  · by_cases h_ult : BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
    · rw [if_pos ⟨h_hi, h_ult⟩, if_pos h_hi, if_pos h_ult]
    · rw [if_neg (fun h => h_ult h.2), if_pos h_hi, if_neg h_ult]
  · rw [if_neg (fun h => h_hi h.1), if_neg h_hi]

end EvmAsm.Evm64
