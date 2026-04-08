/-
  EvmAsm.Evm64.DivMod.Compose.ModN1Full

  End-to-end composition for n=1 MOD (b[3]=b[2]=b[1]=0, b[0]≠0, shift≠0).
  Composes: pre-loop (base→base+448) + loop body j=3 (cpsBranch at base+448) +
            loop body j=2 (cpsBranch at base+448) +
            loop body j=1 (cpsBranch at base+448) +
            loop body j=0 (base+448→base+904) + post-loop (base+904→base+1064).
  For n=1, the loop runs 4 iterations: j=3,2,1 (loop back) then j=0 (exits).
-/

import EvmAsm.Evm64.DivMod.LoopBodyN1
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN1
import EvmAsm.Evm64.DivMod.Compose.FullPath

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Address simplification lemmas for j=0 (n=1)
-- ============================================================================

/-- u_base for j=0: sp + signExtend12 4056 - 0<<<3 = sp + signExtend12 4056 -/
private theorem j0_u_base_eq (sp : Word) :
    sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4056 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide]
  bv_omega

/-- Simplify x + 0 for Word -/
private theorem word_add_zero (x : Word) : x + (0 : Word) = x := by bv_omega

/-- q_addr for j=0: sp + signExtend12 4088 - 0<<<3 = sp + signExtend12 4088 -/
private theorem j0_q_addr_eq (sp : Word) :
    sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4088 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide]
  bv_omega

/-- u0 addr for j=0: u_base + signExtend12 0 = sp + signExtend12 4056 -/
private theorem j0_u0_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0 = sp + signExtend12 4056 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide]
  bv_omega

/-- u1 addr for j=0: u_base + signExtend12 4088 = sp + signExtend12 4048 -/
private theorem j0_u1_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 = sp + signExtend12 4048 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by native_decide,
    show signExtend12 (4048 : BitVec 12) = (18446744073709551568 : Word) from by native_decide]
  bv_omega

/-- u2 addr for j=0: u_base + signExtend12 4080 = sp + signExtend12 4040 -/
private theorem j0_u2_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 = sp + signExtend12 4040 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by native_decide,
    show signExtend12 (4040 : BitVec 12) = (18446744073709551560 : Word) from by native_decide]
  bv_omega

/-- u3 addr for j=0: u_base + signExtend12 4072 = sp + signExtend12 4032 -/
private theorem j0_u3_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 = sp + signExtend12 4032 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by native_decide,
    show signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) from by native_decide]
  bv_omega

/-- u4 addr for j=0: u_base + signExtend12 4064 = sp + signExtend12 4024 -/
private theorem j0_u4_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 = sp + signExtend12 4024 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by native_decide,
    show signExtend12 (4024 : BitVec 12) = (18446744073709551544 : Word) from by native_decide]
  bv_omega

/-- Validity: uhi addr for j=0, n=1: sp + SE12(4056) - ((0+1)<<<3) = sp + SE12(4048) -/
private theorem j0_uhi_addr_eq_n1 (sp : Word) :
    sp + signExtend12 4056 - ((0 : Word) + (1 : Word)) <<< (3 : BitVec 6).toNat = sp + signExtend12 4048 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4048 : BitVec 12) = (18446744073709551568 : Word) from by native_decide]
  bv_omega

/-- Validity: ulo addr for j=0, n=1: (sp + SE12(4056) - ((0+1)<<<3)) + 8 = sp + SE12(4056) -/
private theorem j0_ulo_addr_eq_n1 (sp : Word) :
    (sp + signExtend12 4056 - ((0 : Word) + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8 = sp + signExtend12 4056 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide]
  bv_omega

/-- Validity: vtop addr for n=1: sp + ((1 + SE12(4095))<<<3) + SE12(32) = sp + 32 -/
private theorem j0_vtop_addr_eq_n1 (sp : Word) :
    sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32 = sp + 32 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4095 : BitVec 12) = (18446744073709551615 : Word) from by native_decide,
    show signExtend12 (32 : BitVec 12) = (32 : Word) from by native_decide]
  bv_omega

/-- x5 in loop body post for j=0: 0<<<3 = 0 -/
private theorem j0_shl3_eq :
    (0 : Word) <<< (3 : BitVec 6).toNat = (0 : Word) := by native_decide

/-- u_base for j=0 after shl3: sp + SE12(4056) - 0 = sp + SE12(4056) -/
private theorem j0_sub_zero (sp : Word) :
    sp + signExtend12 4056 - (0 : Word) = sp + signExtend12 4056 := by bv_omega

/-- q_addr for j=0 after shl3: sp + SE12(4088) - 0 = sp + SE12(4088) -/
private theorem j0_q_sub_zero (sp : Word) :
    sp + signExtend12 4088 - (0 : Word) = sp + signExtend12 4088 := by bv_omega

/-- j' for j=0: 0 + signExtend12 4095 -/
private theorem j0_j'_eq :
    (0 : Word) + signExtend12 (4095 : BitVec 12) = signExtend12 (4095 : BitVec 12) := by
  bv_omega

-- ============================================================================
-- Address simplification lemmas for j=1 (n=1)
-- ============================================================================

/-- u_base for j=1: sp + SE12(4056) - 1<<<3 = sp + SE12(4048) -/
private theorem j1_u_base_eq (sp : Word) :
    sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4048 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4048 : BitVec 12) = (18446744073709551568 : Word) from by native_decide]
  bv_omega

/-- q_addr for j=1: sp + SE12(4088) - 1<<<3 = sp + SE12(4080) -/
private theorem j1_q_addr_eq (sp : Word) :
    sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4080 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by native_decide,
    show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by native_decide]
  bv_omega

/-- u0 addr for j=1: u_base(j=1) + SE12(0) = sp + SE12(4048) -/
private theorem j1_u0_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0 = sp + signExtend12 4048 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4048 : BitVec 12) = (18446744073709551568 : Word) from by native_decide]
  bv_omega

/-- u1 addr for j=1: u_base(j=1) + SE12(4088) = sp + SE12(4040) -/
private theorem j1_u1_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 = sp + signExtend12 4040 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by native_decide,
    show signExtend12 (4040 : BitVec 12) = (18446744073709551560 : Word) from by native_decide]
  bv_omega

/-- u2 addr for j=1: u_base(j=1) + SE12(4080) = sp + SE12(4032) -/
private theorem j1_u2_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 = sp + signExtend12 4032 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by native_decide,
    show signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) from by native_decide]
  bv_omega

/-- u3 addr for j=1: u_base(j=1) + SE12(4072) = sp + SE12(4024) -/
private theorem j1_u3_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 = sp + signExtend12 4024 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by native_decide,
    show signExtend12 (4024 : BitVec 12) = (18446744073709551544 : Word) from by native_decide]
  bv_omega

/-- u4 addr for j=1: u_base(j=1) + SE12(4064) = sp + SE12(4016) -/
private theorem j1_u4_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 = sp + signExtend12 4016 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by native_decide,
    show signExtend12 (4016 : BitVec 12) = (18446744073709551536 : Word) from by native_decide]
  bv_omega

/-- Validity: uhi addr for j=1, n=1: sp + SE12(4056) - ((1+1)<<<3) = sp + SE12(4040) -/
private theorem j1_uhi_addr_eq_n1 (sp : Word) :
    sp + signExtend12 4056 - ((1 : Word) + (1 : Word)) <<< (3 : BitVec 6).toNat = sp + signExtend12 4040 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4040 : BitVec 12) = (18446744073709551560 : Word) from by native_decide]
  bv_omega

/-- Validity: ulo addr for j=1, n=1: (sp + SE12(4056) - ((1+1)<<<3)) + 8 = sp + SE12(4048) -/
private theorem j1_ulo_addr_eq_n1 (sp : Word) :
    (sp + signExtend12 4056 - ((1 : Word) + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8 = sp + signExtend12 4048 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4048 : BitVec 12) = (18446744073709551568 : Word) from by native_decide]
  bv_omega

/-- x5 in loop body post for j=1: 1<<<3 = 8 -/
private theorem j1_shl3_eq :
    (1 : Word) <<< (3 : BitVec 6).toNat = (8 : Word) := by native_decide

/-- j' for j=1: 1 + signExtend12 4095 = 0 -/
private theorem j1_j'_eq :
    (1 : Word) + signExtend12 (4095 : BitVec 12) = (0 : Word) := by
  simp only [show signExtend12 (4095 : BitVec 12) = (18446744073709551615 : Word) from by native_decide]
  bv_omega

/-- u_base for j=1 after shl3: sp + SE12(4056) - 8 = sp + SE12(4048) -/
private theorem j1_sub_8 (sp : Word) :
    sp + signExtend12 4056 - (8 : Word) = sp + signExtend12 4048 := by
  simp only [show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4048 : BitVec 12) = (18446744073709551568 : Word) from by native_decide]
  bv_omega

/-- q_addr for j=1 after shl3: sp + SE12(4088) - 8 = sp + SE12(4080) -/
private theorem j1_q_sub_8 (sp : Word) :
    sp + signExtend12 4088 - (8 : Word) = sp + signExtend12 4080 := by
  simp only [show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by native_decide,
    show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by native_decide]
  bv_omega

-- ============================================================================
-- Address simplification lemmas for j=2 (n=1)
-- ============================================================================

/-- u_base for j=2: sp + SE12(4056) - 2<<<3 = sp + SE12(4040) -/
private theorem j2_u_base_eq (sp : Word) :
    sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4040 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4040 : BitVec 12) = (18446744073709551560 : Word) from by native_decide]
  bv_omega

/-- q_addr for j=2: sp + SE12(4088) - 2<<<3 = sp + SE12(4072) -/
private theorem j2_q_addr_eq (sp : Word) :
    sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4072 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by native_decide,
    show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by native_decide]
  bv_omega

/-- u0 addr for j=2: u_base(j=2) + SE12(0) = sp + SE12(4040) -/
private theorem j2_u0_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0 = sp + signExtend12 4040 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4040 : BitVec 12) = (18446744073709551560 : Word) from by native_decide]
  bv_omega

/-- u1 addr for j=2: u_base(j=2) + SE12(4088) = sp + SE12(4032) -/
private theorem j2_u1_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 = sp + signExtend12 4032 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by native_decide,
    show signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) from by native_decide]
  bv_omega

/-- u2 addr for j=2: u_base(j=2) + SE12(4080) = sp + SE12(4024) -/
private theorem j2_u2_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 = sp + signExtend12 4024 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by native_decide,
    show signExtend12 (4024 : BitVec 12) = (18446744073709551544 : Word) from by native_decide]
  bv_omega

/-- u3 addr for j=2: u_base(j=2) + SE12(4072) = sp + SE12(4016) -/
private theorem j2_u3_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 = sp + signExtend12 4016 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by native_decide,
    show signExtend12 (4016 : BitVec 12) = (18446744073709551536 : Word) from by native_decide]
  bv_omega

/-- u4 addr for j=2: u_base(j=2) + SE12(4064) = sp + SE12(4008) -/
private theorem j2_u4_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 = sp + signExtend12 4008 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by native_decide,
    show signExtend12 (4008 : BitVec 12) = (18446744073709551528 : Word) from by native_decide]
  bv_omega

/-- Validity: uhi addr for j=2, n=1: sp + SE12(4056) - ((2+1)<<<3) = sp + SE12(4032) -/
private theorem j2_uhi_addr_eq_n1 (sp : Word) :
    sp + signExtend12 4056 - ((2 : Word) + (1 : Word)) <<< (3 : BitVec 6).toNat = sp + signExtend12 4032 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) from by native_decide]
  bv_omega

/-- Validity: ulo addr for j=2, n=1: (sp + SE12(4056) - ((2+1)<<<3)) + 8 = sp + SE12(4040) -/
private theorem j2_ulo_addr_eq_n1 (sp : Word) :
    (sp + signExtend12 4056 - ((2 : Word) + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8 = sp + signExtend12 4040 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4040 : BitVec 12) = (18446744073709551560 : Word) from by native_decide]
  bv_omega

/-- x5 in loop body post for j=2: 2<<<3 = 16 -/
private theorem j2_shl3_eq :
    (2 : Word) <<< (3 : BitVec 6).toNat = (16 : Word) := by native_decide

/-- j' for j=2: 2 + signExtend12 4095 = 1 -/
private theorem j2_j'_eq :
    (2 : Word) + signExtend12 (4095 : BitVec 12) = (1 : Word) := by
  simp only [show signExtend12 (4095 : BitVec 12) = (18446744073709551615 : Word) from by native_decide]
  bv_omega

/-- u_base for j=2 after shl3: sp + SE12(4056) - 16 = sp + SE12(4040) -/
private theorem j2_sub_16 (sp : Word) :
    sp + signExtend12 4056 - (16 : Word) = sp + signExtend12 4040 := by
  simp only [show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4040 : BitVec 12) = (18446744073709551560 : Word) from by native_decide]
  bv_omega

/-- q_addr for j=2 after shl3: sp + SE12(4088) - 16 = sp + SE12(4072) -/
private theorem j2_q_sub_16 (sp : Word) :
    sp + signExtend12 4088 - (16 : Word) = sp + signExtend12 4072 := by
  simp only [show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by native_decide,
    show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by native_decide]
  bv_omega

-- ============================================================================
-- Address simplification lemmas for j=3 (n=1)
-- ============================================================================

/-- u_base for j=3: sp + SE12(4056) - 3<<<3 = sp + SE12(4032) -/
private theorem j3_u_base_eq (sp : Word) :
    sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4032 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) from by native_decide]
  bv_omega

/-- q_addr for j=3: sp + SE12(4088) - 3<<<3 = sp + SE12(4064) -/
private theorem j3_q_addr_eq (sp : Word) :
    sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4064 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by native_decide,
    show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by native_decide]
  bv_omega

/-- u0 addr for j=3: u_base(j=3) + SE12(0) = sp + SE12(4032) -/
private theorem j3_u0_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0 = sp + signExtend12 4032 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) from by native_decide]
  bv_omega

/-- u1 addr for j=3: u_base(j=3) + SE12(4088) = sp + SE12(4024) -/
private theorem j3_u1_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 = sp + signExtend12 4024 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by native_decide,
    show signExtend12 (4024 : BitVec 12) = (18446744073709551544 : Word) from by native_decide]
  bv_omega

/-- u2 addr for j=3: u_base(j=3) + SE12(4080) = sp + SE12(4016) -/
private theorem j3_u2_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 = sp + signExtend12 4016 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by native_decide,
    show signExtend12 (4016 : BitVec 12) = (18446744073709551536 : Word) from by native_decide]
  bv_omega

/-- u3 addr for j=3: u_base(j=3) + SE12(4072) = sp + SE12(4008) -/
private theorem j3_u3_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 = sp + signExtend12 4008 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by native_decide,
    show signExtend12 (4008 : BitVec 12) = (18446744073709551528 : Word) from by native_decide]
  bv_omega

/-- u4 addr for j=3: u_base(j=3) + SE12(4064) = sp + SE12(4000) -/
private theorem j3_u4_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 = sp + signExtend12 4000 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by native_decide,
    show signExtend12 (4000 : BitVec 12) = (18446744073709551520 : Word) from by native_decide]
  bv_omega

/-- Validity: uhi addr for j=3, n=1: sp + SE12(4056) - ((3+1)<<<3) = sp + SE12(4024) -/
private theorem j3_uhi_addr_eq_n1 (sp : Word) :
    sp + signExtend12 4056 - ((3 : Word) + (1 : Word)) <<< (3 : BitVec 6).toNat = sp + signExtend12 4024 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4024 : BitVec 12) = (18446744073709551544 : Word) from by native_decide]
  bv_omega

/-- Validity: ulo addr for j=3, n=1: (sp + SE12(4056) - ((3+1)<<<3)) + 8 = sp + SE12(4032) -/
private theorem j3_ulo_addr_eq_n1 (sp : Word) :
    (sp + signExtend12 4056 - ((3 : Word) + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8 = sp + signExtend12 4032 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) from by native_decide]
  bv_omega

/-- x5 in loop body post for j=3: 3<<<3 = 24 -/
private theorem j3_shl3_eq :
    (3 : Word) <<< (3 : BitVec 6).toNat = (24 : Word) := by native_decide

/-- j' for j=3: 3 + signExtend12 4095 = 2 -/
private theorem j3_j'_eq :
    (3 : Word) + signExtend12 (4095 : BitVec 12) = (2 : Word) := by
  simp only [show signExtend12 (4095 : BitVec 12) = (18446744073709551615 : Word) from by native_decide]
  bv_omega

/-- u_base for j=3 after shl3: sp + SE12(4056) - 24 = sp + SE12(4032) -/
private theorem j3_sub_24 (sp : Word) :
    sp + signExtend12 4056 - (24 : Word) = sp + signExtend12 4032 := by
  simp only [show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) from by native_decide]
  bv_omega

/-- q_addr for j=3 after shl3: sp + SE12(4088) - 24 = sp + SE12(4064) -/
private theorem j3_q_sub_24 (sp : Word) :
    sp + signExtend12 4088 - (24 : Word) = sp + signExtend12 4064 := by
  simp only [show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by native_decide,
    show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by native_decide]
  bv_omega

/-- x1 in pre-loop for n=1: signExtend12 4 - 1 = 3 -/
private theorem se12_4_sub_1 :
    signExtend12 (4 : BitVec 12) - (1 : Word) = (3 : Word) := by native_decide

-- ============================================================================
-- Composition: pre-loop + four loop iterations (base → base+904) for n=1, shift≠0
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 20000000 in
/-- Pre-loop + four-iteration loop body for n=1 MOD (shift≠0).
    Composes base→base+448 (normalization) with four iterations of loop body
    at base+448: j=3 (cpsBranch, loops back) then j=2 (cpsBranch, loops back)
    then j=1 (cpsBranch, loops back) then j=0 (cpsTriple, exits to base+904).
    Postcondition uses loopBodyPostN1 with existentials for computed values. -/
theorem evm_mod_n1_preloop_loopbody_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 : Word)
    (n_mem shift_mem j_old ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true)
    (hv_n  : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hv_j  : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch : isValidDwordAccess (sp + signExtend12 3944) = true) :
    let shift := (clzResult b0).1
    let anti_shift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    let u4 := a3 >>> (anti_shift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
    let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
    let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
    let u0 := a0 <<< (shift.toNat % 64)
    cpsTriple base (base + 904) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) ** (.x11 ↦ᵣ v11) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0_old) ** ((sp + signExtend12 4048) ↦ₘ u1_old) **
       ((sp + signExtend12 4040) ↦ₘ u2_old) ** ((sp + signExtend12 4032) ↦ₘ u3_old) **
       ((sp + signExtend12 4024) ↦ₘ u4_old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3992) ↦ₘ shift_mem) **
       ((sp + signExtend12 3984) ↦ₘ n_mem) **
       ((sp + signExtend12 3976) ↦ₘ j_old) **
       ((sp + signExtend12 3968) ↦ₘ ret_mem) ** ((sp + signExtend12 3960) ↦ₘ d_mem) **
       ((sp + signExtend12 3952) ↦ₘ dlo_mem) ** ((sp + signExtend12 3944) ↦ₘ scratch_un0))
      (fun h => ∃ (x1out x5out x6out x7out x2out x10out x11out : Word)
        (u0out u1out u2out u3out u4out q0out : Word)
        (u5out q1out u6out q2out u7out q3out : Word)
        (j_mem_out : Word)
        (retout dout dlout scout : Word),
       ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ x1out) **
        (.x5 ↦ᵣ x5out) ** (.x6 ↦ᵣ x6out) **
        (.x7 ↦ᵣ x7out) ** (.x10 ↦ᵣ x10out) ** (.x11 ↦ᵣ x11out) **
        (.x2 ↦ᵣ x2out) ** (.x0 ↦ᵣ (0 : Word)) **
        (sp + signExtend12 3976 ↦ₘ j_mem_out) **
        (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
        ((sp + 32) ↦ₘ b0') ** ((sp + signExtend12 4056) ↦ₘ u0out) **
        ((sp + 40) ↦ₘ b1') ** ((sp + signExtend12 4048) ↦ₘ u1out) **
        ((sp + 48) ↦ₘ b2') ** ((sp + signExtend12 4040) ↦ₘ u2out) **
        ((sp + 56) ↦ₘ b3') ** ((sp + signExtend12 4032) ↦ₘ u3out) **
        ((sp + signExtend12 4024) ↦ₘ u4out) **
        ((sp + signExtend12 4088) ↦ₘ q0out) **
        ((sp + signExtend12 4016) ↦ₘ u5out) **
        ((sp + signExtend12 4080) ↦ₘ q1out) **
        ((sp + signExtend12 4008) ↦ₘ u6out) **
        ((sp + signExtend12 4072) ↦ₘ q2out) **
        ((sp + signExtend12 4000) ↦ₘ u7out) **
        ((sp + signExtend12 4064) ↦ₘ q3out) **
        (sp + signExtend12 3968 ↦ₘ retout) **
        (sp + signExtend12 3960 ↦ₘ dout) **
        (sp + signExtend12 3952 ↦ₘ dlout) **
        (sp + signExtend12 3944 ↦ₘ scout) **
        ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 3992) ↦ₘ shift)) h) := by
  intro shift anti_shift b3' b2' b1' b0' u4 u3 u2 u1 u0
  -- Step 1: Pre-loop (base → base+448)
  have hPL := evm_mod_n1_to_loopSetup_spec sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem
    hbnz hb3z hb2z hb1z hshift_nz hvalid hv_q0 hv_q1 hv_q2 hv_q3
    hv_u0 hv_u1 hv_u2 hv_u3 hv_u4 hv_u5 hv_u6 hv_u7 hv_n hv_shift
  intro_lets at hPL
  -- Frame pre-loop with x11, j_old, scratch memory
  have hPLf := cpsTriple_frame_left _ _ _ _ _
    ((.x11 ↦ᵣ v11) **
     ((sp + signExtend12 3976) ↦ₘ j_old) **
     ((sp + signExtend12 3968) ↦ₘ ret_mem) ** ((sp + signExtend12 3960) ↦ₘ d_mem) **
     ((sp + signExtend12 3952) ↦ₘ dlo_mem) ** ((sp + signExtend12 3944) ↦ₘ scratch_un0))
    (by pcFree) hPL
  -- Rewrite x1 in pre-loop postcondition to match j=3 loop body's x1=3
  rw [se12_4_sub_1] at hPLf
  -- Step 2: j=3 cpsBranch (base+448 → base+448/904)
  -- j=3 window: u[0] at SE12(4032)=u3, u[1] at SE12(4024)=u4,
  -- u[2] at SE12(4016)=0, u[3] at SE12(4008)=0,
  -- u_top at SE12(4000)=0, q_old at SE12(4064)=0
  have hJ3 := divK_loop_body_n1_combined_spec
    sp (3 : Word) j_old (1 : Word) shift u0 (a0 >>> (anti_shift.toNat % 64)) v11 anti_shift
    b0' b1' b2' b3' u3 u4 (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    ret_mem d_mem dlo_mem scratch_un0
    base
    hv_j hv_n
    (by rw [j3_uhi_addr_eq_n1]; exact hv_u4)
    (by rw [j3_ulo_addr_eq_n1]; exact hv_u3)
    (by rw [j0_vtop_addr_eq_n1]; exact ValidMemRange.fetch hvalid 4 _ (by omega) (by rfl))
    hv_ret hv_d hv_dlo hv_scratch
    halign
    (by rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by native_decide]
        exact ValidMemRange.fetch hvalid 4 _ (by omega) (by rfl))
    (by rw [j3_u0_addr_eq]; exact hv_u3)
    (by rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by native_decide]
        exact ValidMemRange.fetch hvalid 5 _ (by omega) (by rfl))
    (by rw [j3_u1_addr_eq]; exact hv_u4)
    (by rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by native_decide]
        exact ValidMemRange.fetch hvalid 6 _ (by omega) (by rfl))
    (by rw [j3_u2_addr_eq]; exact hv_u5)
    (by rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by native_decide]
        exact ValidMemRange.fetch hvalid 7 _ (by omega) (by rfl))
    (by rw [j3_u3_addr_eq]; exact hv_u6)
    (by rw [j3_u4_addr_eq]; exact hv_u7)
    (by rw [j3_q_addr_eq]; exact hv_q3)
  -- Expand let-bindings and canonicalize j=3 addresses
  dsimp only [] at hJ3
  simp only [j3_u0_addr_eq, j3_q_addr_eq, j3_u1_addr_eq,
    j3_u2_addr_eq, j3_u3_addr_eq, j3_u4_addr_eq,
    signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56] at hJ3
  -- Lift j=3 from sharedDivModCode to modCode
  have hJ3d := cpsBranch_extend_code (sharedDivModCode_sub_modCode base) hJ3
  -- Frame j=3 with cells not in its precondition
  have hJ3f := cpsBranch_frame_left _ _ _ _ _ _ _
    (((sp + signExtend12 4056) ↦ₘ u0) **
     ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hJ3d
  -- Step 3: Compose pre-loop + four loop iterations at holdsFor level
  show cpsTriple base (base + 904) (modCode base) _ _
  intro F hF st hcr hPF hpc
  -- Execute pre-loop: base → base+448
  obtain ⟨h_pre, hcompat_pre, hSep_pre⟩ := hPF
  obtain ⟨k1, s1, hstep1, hpc1, hQ1F⟩ := hPLf F hF st hcr
    ⟨h_pre, hcompat_pre, by xperm_hyp hSep_pre⟩ hpc
  have hcr1 := CodeReq.SatisfiedBy_preserved (modCode base) k1 st s1 hstep1 hcr
  -- Rearrange pre-loop postcondition to match j=3 cpsBranch precondition
  obtain ⟨h_f1, hc1, hSep1⟩ := hQ1F
  -- Execute j=3 cpsBranch: base+448 → base+448 (loop back) or base+904 (exit)
  obtain ⟨k2, s2, hstep2, hcase2⟩ := hJ3f F hF s1 hcr1
    ⟨h_f1, hc1, by xperm_hyp hSep1⟩ hpc1
  have hcr2 := CodeReq.SatisfiedBy_preserved (modCode base) k2 s1 s2 hstep2 hcr1
  -- Case split: loop-back (base+448) vs exit (base+904)
  rcases hcase2 with ⟨hpc2, hQ2F⟩ | ⟨hpc2, hQ2F⟩
  · -- Loop-back case: j=3 looped back to base+448, now execute j=2 then j=1 then j=0
    obtain ⟨h_full2, hcompat2, h_qf2, h_f2, hdisj2, heq2, hQF2, hF2⟩ := hQ2F
    obtain ⟨h_lp2, h_frame2, hdisj_i2, heq_i2, hLP2, hFrame2⟩ := hQF2
    -- Unfold and canonicalize loopBodyPostN1 at j=3
    change loopBodyPostN1 sp (3 : Word) b0' b1' b2' b3' h_lp2 at hLP2
    unfold loopBodyPostN1 at hLP2
    simp only [j3_u0_addr_eq, j3_u1_addr_eq, j3_u2_addr_eq, j3_u3_addr_eq, j3_u4_addr_eq,
      j3_q_addr_eq] at hLP2
    simp only [j3_u_base_eq, j3_shl3_eq, j3_j'_eq, j3_sub_24, j3_q_sub_24,
      signExtend12_0, signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56,
      word_add_zero] at hLP2
    obtain ⟨x2v_j3, x10v_j3, x11v_j3, un0v_j3, un1v_j3, un2v_j3, un3v_j3, u4v_j3, qv_j3,
      retv_j3, dv_j3, dlov_j3, sunv_j3, hLP2_atoms⟩ := hLP2
    -- Build j=2 combined_spec with j=3 output values
    -- After j=3: x1=2, x5=24, x6=sp+SE12(4032), x7=sp+SE12(4064),
    -- x10=x10v_j3, x11=x11v_j3, x2=x2v_j3
    -- Memory j_old=(3:Word) (stored by j=3), n_mem=(1:Word)
    -- u window at j=2: u0 at SE12(4040)=u2, u1 at SE12(4032)=un0v_j3,
    -- u2 at SE12(4024)=un1v_j3, u3 at SE12(4016)=un2v_j3,
    -- u_top at SE12(4008)=un3v_j3, q_old at SE12(4072)=0
    have hJ2 := divK_loop_body_n1_combined_spec
      sp (2 : Word) (3 : Word) (24 : Word) (sp + signExtend12 4032) (sp + signExtend12 4064)
      x10v_j3 x11v_j3 x2v_j3
      b0' b1' b2' b3' u2 un0v_j3 un1v_j3 un2v_j3 un3v_j3 (0 : Word)
      retv_j3 dv_j3 dlov_j3 sunv_j3
      base
      hv_j hv_n
      (by rw [j2_uhi_addr_eq_n1]; exact hv_u3)
      (by rw [j2_ulo_addr_eq_n1]; exact hv_u2)
      (by rw [j0_vtop_addr_eq_n1]; exact ValidMemRange.fetch hvalid 4 _ (by omega) (by rfl))
      hv_ret hv_d hv_dlo hv_scratch
      halign
      (by rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by native_decide]
          exact ValidMemRange.fetch hvalid 4 _ (by omega) (by rfl))
      (by rw [j2_u0_addr_eq]; exact hv_u2)
      (by rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by native_decide]
          exact ValidMemRange.fetch hvalid 5 _ (by omega) (by rfl))
      (by rw [j2_u1_addr_eq]; exact hv_u3)
      (by rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by native_decide]
          exact ValidMemRange.fetch hvalid 6 _ (by omega) (by rfl))
      (by rw [j2_u2_addr_eq]; exact hv_u4)
      (by rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by native_decide]
          exact ValidMemRange.fetch hvalid 7 _ (by omega) (by rfl))
      (by rw [j2_u3_addr_eq]; exact hv_u5)
      (by rw [j2_u4_addr_eq]; exact hv_u6)
      (by rw [j2_q_addr_eq]; exact hv_q2)
    dsimp only [] at hJ2
    simp only [j2_u0_addr_eq, j2_q_addr_eq, j2_u1_addr_eq,
      j2_u2_addr_eq, j2_u3_addr_eq, j2_u4_addr_eq,
      signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56] at hJ2
    have hJ2d := cpsBranch_extend_code (sharedDivModCode_sub_modCode base) hJ2
    -- Frame j=2 with cells not in its precondition (includes j=3 outputs)
    have hJ2f := cpsBranch_frame_left _ _ _ _ _ _ _
      (((sp + signExtend12 4056) ↦ₘ u0) **
       ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4064) ↦ₘ qv_j3) **
       ((sp + signExtend12 4000) ↦ₘ u4v_j3) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 3992) ↦ₘ shift))
      (by pcFree) hJ2d
    -- Recombine j=3 atoms for rearrangement to j=2 precondition
    have hCombined2 : sepConj _ _ h_qf2 :=
      ⟨h_lp2, h_frame2, hdisj_i2, heq_i2, hLP2_atoms, hFrame2⟩
    have hAll2 : sepConj _ _ h_full2 :=
      ⟨h_qf2, h_f2, hdisj2, heq2, hCombined2, hF2⟩
    rw [sepConj_assoc'] at hAll2
    -- Execute j=2 cpsBranch
    obtain ⟨k3, s3, hstep3, hcase3⟩ := hJ2f F hF s2 hcr2
      ⟨h_full2, hcompat2, by xperm_hyp hAll2⟩ hpc2
    have hcr3 := CodeReq.SatisfiedBy_preserved (modCode base) k3 s2 s3 hstep3 hcr2
    -- Case split: j=2 loop-back vs exit
    rcases hcase3 with ⟨hpc3, hQ3F⟩ | ⟨hpc3, hQ3F⟩
    · -- j=2 loop-back: now execute j=1 then j=0
      obtain ⟨h_full3, hcompat3, h_qf3, h_f3, hdisj3, heq3, hQF3, hF3⟩ := hQ3F
      obtain ⟨h_lp3, h_frame3, hdisj_i3, heq_i3, hLP3, hFrame3⟩ := hQF3
      -- Unfold and canonicalize loopBodyPostN1 at j=2
      change loopBodyPostN1 sp (2 : Word) b0' b1' b2' b3' h_lp3 at hLP3
      unfold loopBodyPostN1 at hLP3
      simp only [j2_u0_addr_eq, j2_u1_addr_eq, j2_u2_addr_eq, j2_u3_addr_eq, j2_u4_addr_eq,
        j2_q_addr_eq] at hLP3
      simp only [j2_u_base_eq, j2_shl3_eq, j2_j'_eq, j2_sub_16, j2_q_sub_16,
        signExtend12_0, signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56,
        word_add_zero] at hLP3
      obtain ⟨x2v_j2, x10v_j2, x11v_j2, un0v_j2, un1v_j2, un2v_j2, un3v_j2, u4v_j2, qv_j2,
        retv_j2, dv_j2, dlov_j2, sunv_j2, hLP3_atoms⟩ := hLP3
      -- Build j=1 combined_spec with j=2 output values
      -- After j=2: x1=1, x5=16, x6=sp+SE12(4040), x7=sp+SE12(4072)
      -- u window at j=1: u0 at SE12(4048)=u1, u1 at SE12(4040)=un0v_j2,
      -- u2 at SE12(4032)=un1v_j2, u3 at SE12(4024)=un2v_j2,
      -- u_top at SE12(4016)=un3v_j2, q_old at SE12(4080)=0
      have hJ1 := divK_loop_body_n1_combined_spec
        sp (1 : Word) (2 : Word) (16 : Word) (sp + signExtend12 4040) (sp + signExtend12 4072)
        x10v_j2 x11v_j2 x2v_j2
        b0' b1' b2' b3' u1 un0v_j2 un1v_j2 un2v_j2 un3v_j2 (0 : Word)
        retv_j2 dv_j2 dlov_j2 sunv_j2
        base
        hv_j hv_n
        (by rw [j1_uhi_addr_eq_n1]; exact hv_u2)
        (by rw [j1_ulo_addr_eq_n1]; exact hv_u1)
        (by rw [j0_vtop_addr_eq_n1]; exact ValidMemRange.fetch hvalid 4 _ (by omega) (by rfl))
        hv_ret hv_d hv_dlo hv_scratch
        halign
        (by rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by native_decide]
            exact ValidMemRange.fetch hvalid 4 _ (by omega) (by rfl))
        (by rw [j1_u0_addr_eq]; exact hv_u1)
        (by rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by native_decide]
            exact ValidMemRange.fetch hvalid 5 _ (by omega) (by rfl))
        (by rw [j1_u1_addr_eq]; exact hv_u2)
        (by rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by native_decide]
            exact ValidMemRange.fetch hvalid 6 _ (by omega) (by rfl))
        (by rw [j1_u2_addr_eq]; exact hv_u3)
        (by rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by native_decide]
            exact ValidMemRange.fetch hvalid 7 _ (by omega) (by rfl))
        (by rw [j1_u3_addr_eq]; exact hv_u4)
        (by rw [j1_u4_addr_eq]; exact hv_u5)
        (by rw [j1_q_addr_eq]; exact hv_q1)
      dsimp only [] at hJ1
      simp only [j1_u0_addr_eq, j1_q_addr_eq, j1_u1_addr_eq,
        j1_u2_addr_eq, j1_u3_addr_eq, j1_u4_addr_eq,
        signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56] at hJ1
      have hJ1d := cpsBranch_extend_code (sharedDivModCode_sub_modCode base) hJ1
      -- Frame j=1 with cells not in its precondition (includes j=2 and j=3 outputs)
      have hJ1f := cpsBranch_frame_left _ _ _ _ _ _ _
        (((sp + signExtend12 4056) ↦ₘ u0) **
         ((sp + signExtend12 4088) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 4072) ↦ₘ qv_j2) **
         ((sp + signExtend12 4064) ↦ₘ qv_j3) **
         ((sp + signExtend12 4008) ↦ₘ u4v_j2) **
         ((sp + signExtend12 4000) ↦ₘ u4v_j3) **
         ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
         ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
         ((sp + signExtend12 3992) ↦ₘ shift))
        (by pcFree) hJ1d
      -- Recombine j=2 atoms for rearrangement to j=1 precondition
      have hCombined3 : sepConj _ _ h_qf3 :=
        ⟨h_lp3, h_frame3, hdisj_i3, heq_i3, hLP3_atoms, hFrame3⟩
      have hAll3 : sepConj _ _ h_full3 :=
        ⟨h_qf3, h_f3, hdisj3, heq3, hCombined3, hF3⟩
      rw [sepConj_assoc'] at hAll3
      -- Execute j=1 cpsBranch
      obtain ⟨k4, s4, hstep4, hcase4⟩ := hJ1f F hF s3 hcr3
        ⟨h_full3, hcompat3, by xperm_hyp hAll3⟩ hpc3
      have hcr4 := CodeReq.SatisfiedBy_preserved (modCode base) k4 s3 s4 hstep4 hcr3
      -- Case split: j=1 loop-back vs exit
      rcases hcase4 with ⟨hpc4, hQ4F⟩ | ⟨hpc4, hQ4F⟩
      · -- j=1 loop-back: now execute j=0
        obtain ⟨h_full4, hcompat4, h_qf4, h_f4, hdisj4, heq4, hQF4, hF4⟩ := hQ4F
        obtain ⟨h_lp4, h_frame4, hdisj_i4, heq_i4, hLP4, hFrame4⟩ := hQF4
        -- Unfold and canonicalize loopBodyPostN1 at j=1
        change loopBodyPostN1 sp (1 : Word) b0' b1' b2' b3' h_lp4 at hLP4
        unfold loopBodyPostN1 at hLP4
        simp only [j1_u0_addr_eq, j1_u1_addr_eq, j1_u2_addr_eq, j1_u3_addr_eq, j1_u4_addr_eq,
          j1_q_addr_eq] at hLP4
        simp only [j1_u_base_eq, j1_shl3_eq, j1_j'_eq, j1_sub_8, j1_q_sub_8,
          signExtend12_0, signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56,
          word_add_zero] at hLP4
        obtain ⟨x2v_j1, x10v_j1, x11v_j1, un0v_j1, un1v_j1, un2v_j1, un3v_j1, u4v_j1, qv_j1,
          retv_j1, dv_j1, dlov_j1, sunv_j1, hLP4_atoms⟩ := hLP4
        -- Build j=0 spec with j=1 output values
        -- After j=1: x1=0, x5=8, x6=sp+SE12(4048), x7=sp+SE12(4080)
        -- u window at j=0: u0 at SE12(4056)=u0, u1 at SE12(4048)=un0v_j1,
        -- u2 at SE12(4040)=un1v_j1, u3 at SE12(4032)=un2v_j1,
        -- u_top at SE12(4024)=un3v_j1, q_old at SE12(4088)=0
        have hLB0 := divK_loop_body_n1_j0_spec sp
          (1 : Word) (8 : Word) (sp + signExtend12 4048) (sp + signExtend12 4080)
          x10v_j1 x11v_j1 x2v_j1
          b0' b1' b2' b3' u0 un0v_j1 un1v_j1 un2v_j1 un3v_j1 (0 : Word)
          retv_j1 dv_j1 dlov_j1 sunv_j1
          base
          hv_j hv_n
          (by rw [j0_uhi_addr_eq_n1]; exact hv_u1)
          (by rw [j0_ulo_addr_eq_n1]; exact hv_u0)
          (by rw [j0_vtop_addr_eq_n1]; exact ValidMemRange.fetch hvalid 4 _ (by omega) (by rfl))
          hv_ret hv_d hv_dlo hv_scratch
          halign
          (by rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by native_decide]
              exact ValidMemRange.fetch hvalid 4 _ (by omega) (by rfl))
          (by rw [j0_u0_addr_eq]; exact hv_u0)
          (by rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by native_decide]
              exact ValidMemRange.fetch hvalid 5 _ (by omega) (by rfl))
          (by rw [j0_u1_addr_eq]; exact hv_u1)
          (by rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by native_decide]
              exact ValidMemRange.fetch hvalid 6 _ (by omega) (by rfl))
          (by rw [j0_u2_addr_eq]; exact hv_u2)
          (by rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by native_decide]
              exact ValidMemRange.fetch hvalid 7 _ (by omega) (by rfl))
          (by rw [j0_u3_addr_eq]; exact hv_u3)
          (by rw [j0_u4_addr_eq]; exact hv_u4)
          (by rw [j0_q_addr_eq]; exact hv_q0)
        dsimp only [] at hLB0
        simp only [j0_u0_addr_eq, j0_q_addr_eq, j0_u1_addr_eq,
          j0_u2_addr_eq, j0_u3_addr_eq, j0_u4_addr_eq,
          signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56] at hLB0
        have hLB0d := cpsTriple_extend_code (sharedDivModCode_sub_modCode base) hLB0
        have hLB0f := cpsTriple_frame_left _ _ _ _ _
          (((sp + signExtend12 4080) ↦ₘ qv_j1) **
           ((sp + signExtend12 4072) ↦ₘ qv_j2) **
           ((sp + signExtend12 4064) ↦ₘ qv_j3) **
           ((sp + signExtend12 4016) ↦ₘ u4v_j1) **
           ((sp + signExtend12 4008) ↦ₘ u4v_j2) **
           ((sp + signExtend12 4000) ↦ₘ u4v_j3) **
           ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
           ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
           ((sp + signExtend12 3992) ↦ₘ shift))
          (by pcFree) hLB0d
        -- Recombine j=1 atoms for rearrangement to j=0 precondition
        have hCombined4 : sepConj _ _ h_qf4 :=
          ⟨h_lp4, h_frame4, hdisj_i4, heq_i4, hLP4_atoms, hFrame4⟩
        have hAll4 : sepConj _ _ h_full4 :=
          ⟨h_qf4, h_f4, hdisj4, heq4, hCombined4, hF4⟩
        rw [sepConj_assoc'] at hAll4
        -- Apply j=0 spec
        obtain ⟨k5, s5, hstep5, hpc5, hQ5F⟩ := hLB0f F hF s4 hcr4
          ⟨h_full4, hcompat4, by xperm_hyp hAll4⟩ hpc4
        -- Chain five execution steps
        refine ⟨k1 + k2 + k3 + k4 + k5, s5,
          stepN_add_eq _ _ _ _ _ (stepN_add_eq _ _ _ _ _ (stepN_add_eq _ _ _ _ _ (stepN_add_eq _ _ _ _ _ hstep1 hstep2) hstep3) hstep4) hstep5, hpc5, ?_⟩
        -- Destructure j=0 postcondition and provide final existential witnesses
        obtain ⟨h_res5, hcompat5, h_qf5, h_f5, hdisj5, heq5, hQF5, hF5⟩ := hQ5F
        refine ⟨h_res5, hcompat5, h_qf5, h_f5, hdisj5, heq5, ?_, hF5⟩
        obtain ⟨h_j0, h_fr0, hdisj_j0, heq_j0, hJ0post, hFR0⟩ := hQF5
        change loopBodyPostN1 sp (0 : Word) b0' b1' b2' b3' h_j0 at hJ0post
        unfold loopBodyPostN1 at hJ0post
        simp only [j0_u0_addr_eq, j0_u1_addr_eq, j0_u2_addr_eq, j0_u3_addr_eq, j0_u4_addr_eq,
          j0_q_addr_eq] at hJ0post
        simp only [j0_u_base_eq, j0_shl3_eq, j0_j'_eq, j0_sub_zero, j0_q_sub_zero,
          signExtend12_0, signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56,
          word_add_zero] at hJ0post
        obtain ⟨x2v_j0, x10v_j0, x11v_j0, un0v_j0, un1v_j0, un2v_j0, un3v_j0, u4v_j0, qv_j0,
          retv_j0, dv_j0, dlov_j0, sunv_j0, hJ0_atoms⟩ := hJ0post
        have hCombined5 : sepConj _ _ h_qf5 :=
          ⟨h_j0, h_fr0, hdisj_j0, heq_j0, hJ0_atoms, hFR0⟩
        -- Existential ordering: (u5out q1out u6out q2out u7out q3out)
        exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, u4v_j1, qv_j1, u4v_j2, qv_j2, u4v_j3, qv_j3, _, _, _, _, _,
          by xperm_hyp hCombined5⟩
      · -- j=1 exit case: j=1 exited to base+904 directly
        obtain ⟨h_full4, hcompat4, h_qf4, h_f4, hdisj4, heq4, hQF4, hF4⟩ := hQ4F
        refine ⟨k1 + k2 + k3 + k4, s4, stepN_add_eq _ _ _ _ _ (stepN_add_eq _ _ _ _ _ (stepN_add_eq _ _ _ _ _ hstep1 hstep2) hstep3) hstep4, hpc4, ?_⟩
        refine ⟨h_full4, hcompat4, h_qf4, h_f4, hdisj4, heq4, ?_, hF4⟩
        obtain ⟨h_lp4, h_frame4, hdisj_i4, heq_i4, hLP4, hFrame4⟩ := hQF4
        change loopBodyPostN1 sp (1 : Word) b0' b1' b2' b3' h_lp4 at hLP4
        unfold loopBodyPostN1 at hLP4
        simp only [j1_u0_addr_eq, j1_u1_addr_eq, j1_u2_addr_eq, j1_u3_addr_eq, j1_u4_addr_eq,
          j1_q_addr_eq] at hLP4
        simp only [j1_u_base_eq, j1_shl3_eq, j1_j'_eq, j1_sub_8, j1_q_sub_8,
          signExtend12_0, signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56,
          word_add_zero] at hLP4
        obtain ⟨x2v_j1, x10v_j1, x11v_j1, un0v_j1, un1v_j1, un2v_j1, un3v_j1, u4v_j1, qv_j1,
          retv_j1, dv_j1, dlov_j1, sunv_j1, hLP4_atoms⟩ := hLP4
        have hCombined4 : sepConj _ _ h_qf4 :=
          ⟨h_lp4, h_frame4, hdisj_i4, heq_i4, hLP4_atoms, hFrame4⟩
        -- Existential ordering: (u5out q1out u6out q2out u7out q3out)
        exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, u4v_j1, qv_j1, u4v_j2, qv_j2, u4v_j3, qv_j3, _, _, _, _, _,
          by xperm_hyp hCombined4⟩
    · -- j=2 exit case: j=2 exited to base+904 directly
      obtain ⟨h_full3, hcompat3, h_qf3, h_f3, hdisj3, heq3, hQF3, hF3⟩ := hQ3F
      refine ⟨k1 + k2 + k3, s3, stepN_add_eq _ _ _ _ _ (stepN_add_eq _ _ _ _ _ hstep1 hstep2) hstep3, hpc3, ?_⟩
      refine ⟨h_full3, hcompat3, h_qf3, h_f3, hdisj3, heq3, ?_, hF3⟩
      obtain ⟨h_lp3, h_frame3, hdisj_i3, heq_i3, hLP3, hFrame3⟩ := hQF3
      change loopBodyPostN1 sp (2 : Word) b0' b1' b2' b3' h_lp3 at hLP3
      unfold loopBodyPostN1 at hLP3
      simp only [j2_u0_addr_eq, j2_u1_addr_eq, j2_u2_addr_eq, j2_u3_addr_eq, j2_u4_addr_eq,
        j2_q_addr_eq] at hLP3
      simp only [j2_u_base_eq, j2_shl3_eq, j2_j'_eq, j2_sub_16, j2_q_sub_16,
        signExtend12_0, signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56,
        word_add_zero] at hLP3
      obtain ⟨x2v_j2, x10v_j2, x11v_j2, un0v_j2, un1v_j2, un2v_j2, un3v_j2, u4v_j2, qv_j2,
        retv_j2, dv_j2, dlov_j2, sunv_j2, hLP3_atoms⟩ := hLP3
      have hCombined3 : sepConj _ _ h_qf3 :=
        ⟨h_lp3, h_frame3, hdisj_i3, heq_i3, hLP3_atoms, hFrame3⟩
      -- Existential ordering: (u5out q1out u6out q2out u7out q3out)
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, un3v_j2, _, u4v_j2, qv_j2, u4v_j3, qv_j3, _, _, _, _, _,
        by xperm_hyp hCombined3⟩
  · -- j=3 exit case: j=3 exited to base+904 directly
    obtain ⟨h_full2, hcompat2, h_qf2, h_f2, hdisj2, heq2, hQF2, hF2⟩ := hQ2F
    refine ⟨k1 + k2, s2, stepN_add_eq _ _ _ _ _ hstep1 hstep2, hpc2, ?_⟩
    refine ⟨h_full2, hcompat2, h_qf2, h_f2, hdisj2, heq2, ?_, hF2⟩
    obtain ⟨h_lp2, h_frame2, hdisj_i2, heq_i2, hLP2, hFrame2⟩ := hQF2
    change loopBodyPostN1 sp (3 : Word) b0' b1' b2' b3' h_lp2 at hLP2
    unfold loopBodyPostN1 at hLP2
    simp only [j3_u0_addr_eq, j3_u1_addr_eq, j3_u2_addr_eq, j3_u3_addr_eq, j3_u4_addr_eq,
      j3_q_addr_eq] at hLP2
    simp only [j3_u_base_eq, j3_shl3_eq, j3_j'_eq, j3_sub_24, j3_q_sub_24,
      signExtend12_0, signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56,
      word_add_zero] at hLP2
    obtain ⟨x2v_j3, x10v_j3, x11v_j3, un0v_j3, un1v_j3, un2v_j3, un3v_j3, u4v_j3, qv_j3,
      retv_j3, dv_j3, dlov_j3, sunv_j3, hLP2_atoms⟩ := hLP2
    have hCombined2 : sepConj _ _ h_qf2 :=
      ⟨h_lp2, h_frame2, hdisj_i2, heq_i2, hLP2_atoms, hFrame2⟩
    -- Existential ordering: (u5out q1out u6out q2out u7out q3out)
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, un2v_j3, _, un3v_j3, _, u4v_j3, qv_j3, _, _, _, _, _,
      by xperm_hyp hCombined2⟩

-- ============================================================================
-- Full n=1 MOD spec: base → base+1064
-- Composes preloop+loopbody (base→base+904) with denorm+epilogue (base+904→base+1064)
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Full n=1 MOD spec (b[3]=b[2]=b[1]=0, b[0]≠0, shift≠0): base → base+1064.
    Composes pre-loop + four-iteration loop body (base→base+904) with
    preamble + denorm + epilogue (base+904→base+1064). -/
theorem evm_mod_n1_full_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 : Word)
    (n_mem shift_mem j_old ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true)
    (hv_n  : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hv_j  : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch : isValidDwordAccess (sp + signExtend12 3944) = true) :
    let shift := (clzResult b0).1
    let anti_shift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    cpsTriple base (base + 1064) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) ** (.x11 ↦ᵣ v11) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0_old) ** ((sp + signExtend12 4048) ↦ₘ u1_old) **
       ((sp + signExtend12 4040) ↦ₘ u2_old) ** ((sp + signExtend12 4032) ↦ₘ u3_old) **
       ((sp + signExtend12 4024) ↦ₘ u4_old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3992) ↦ₘ shift_mem) **
       ((sp + signExtend12 3984) ↦ₘ n_mem) **
       ((sp + signExtend12 3976) ↦ₘ j_old) **
       ((sp + signExtend12 3968) ↦ₘ ret_mem) ** ((sp + signExtend12 3960) ↦ₘ d_mem) **
       ((sp + signExtend12 3952) ↦ₘ dlo_mem) ** ((sp + signExtend12 3944) ↦ₘ scratch_un0))
      (fun h => ∃ (q0v q1v q2v q3v x2out x1out x11out : Word)
        (u0out u1out u2out u3out u4out u5out u6out u7out : Word)
        (j_mem_out : Word)
        (retout dout dlout scout : Word),
        ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ u0out) ** (.x6 ↦ᵣ u1out) ** (.x7 ↦ᵣ u2out) **
         (.x2 ↦ᵣ x2out) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ u3out) **
         (.x1 ↦ᵣ x1out) ** (.x11 ↦ᵣ x11out) **
         ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
         ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
         ((sp + 32) ↦ₘ u0out) ** ((sp + 40) ↦ₘ u1out) **
         ((sp + 48) ↦ₘ u2out) ** ((sp + 56) ↦ₘ u3out) **
         ((sp + signExtend12 3992) ↦ₘ shift) **
         ((sp + signExtend12 4056) ↦ₘ u0out) ** ((sp + signExtend12 4048) ↦ₘ u1out) **
         ((sp + signExtend12 4040) ↦ₘ u2out) ** ((sp + signExtend12 4032) ↦ₘ u3out) **
         ((sp + signExtend12 4088) ↦ₘ q0v) **
         ((sp + signExtend12 4080) ↦ₘ q1v) **
         ((sp + signExtend12 4072) ↦ₘ q2v) **
         ((sp + signExtend12 4064) ↦ₘ q3v) **
         ((sp + signExtend12 4024) ↦ₘ u4out) **
         ((sp + signExtend12 4016) ↦ₘ u5out) ** ((sp + signExtend12 4008) ↦ₘ u6out) **
         ((sp + signExtend12 4000) ↦ₘ u7out) **
         ((sp + signExtend12 3984) ↦ₘ (1 : Word)) ** ((sp + signExtend12 3976) ↦ₘ j_mem_out) **
         ((sp + signExtend12 3968) ↦ₘ retout) ** ((sp + signExtend12 3960) ↦ₘ dout) **
         ((sp + signExtend12 3952) ↦ₘ dlout) ** ((sp + signExtend12 3944) ↦ₘ scout)) h) := by
  intro shift anti_shift b3' b2' b1' b0'
  -- Step 1: Pre-loop + loop body (base → base+904)
  have hPLLB := evm_mod_n1_preloop_loopbody_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7
    n_mem shift_mem j_old ret_mem d_mem dlo_mem scratch_un0
    hbnz hb3z hb2z hb1z hshift_nz hvalid halign
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch
  intro_lets at hPLLB
  -- Step 2: Compose via cpsTriple definition to handle existential intermediate
  show cpsTriple base (base + 1064) (modCode base) _ _
  intro F hF st hcr hPF hpc
  -- Execute first half: base → base+904
  obtain ⟨k1, s1, hstep1, hpc1, hQF⟩ := hPLLB F hF st hcr hPF hpc
  -- Destructure holdsFor and sep conj with existential intermediate
  obtain ⟨h_full, hcompat1, h_q, h_f, hdisj_qf, heq_qf,
    ⟨x1v, x5v, x6v, x7v, x2v, x10v, x11v,
     u0v, u1v, u2v, u3v, u4v, q0v,
     u5v, q1v, u6v, q2v, u7v, q3v, j_v,
     retv, dv, dlov, sunv, hQ_atoms⟩, hF_heap⟩ := hQF
  -- Get post-loop chain for MOD: denorm + epilogue (base+904 → base+1064)
  have hDE := evm_mod_preamble_denorm_epilogue_spec sp base
    u0v u1v u2v u3v shift
    x2v x5v x6v x7v x10v
    b0' b1' b2' b3'
    hshift_nz hvalid hv_shift hv_u0 hv_u1 hv_u2 hv_u3
  intro_lets at hDE
  -- Recombine heaps: Q_atoms ** F
  have hAll : sepConj _ _ h_full :=
    ⟨h_q, h_f, hdisj_qf, heq_qf, hQ_atoms, hF_heap⟩
  -- Rearrange atoms to match POST_LOOP_PRE ** (LEFTOVER ** F)
  -- POST_LOOP_PRE = epilogue precondition (16 atoms: registers + shift_mem + u[] + output)
  let POST_LOOP_PRE :=
    (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ x6v) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x5 ↦ᵣ x5v) ** (.x7 ↦ᵣ x7v) ** (.x2 ↦ᵣ x2v) ** (.x10 ↦ᵣ x10v) **
    ((sp + signExtend12 3992) ↦ₘ shift) **
    ((sp + signExtend12 4056) ↦ₘ u0v) ** ((sp + signExtend12 4048) ↦ₘ u1v) **
    ((sp + signExtend12 4040) ↦ₘ u2v) ** ((sp + signExtend12 4032) ↦ₘ u3v) **
    ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
    ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3')
  -- LEFTOVER = atoms carried through: x1, x11, j, n, u4, u5, u6, u7, a0-a3, q[], ret, d, dlo, scratch
  have hRearranged : (POST_LOOP_PRE ** (((.x1 ↦ᵣ x1v) ** (.x11 ↦ᵣ x11v) **
     (sp + signExtend12 3976 ↦ₘ j_v) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     ((sp + signExtend12 4024) ↦ₘ u4v) **
     ((sp + signExtend12 4016) ↦ₘ u5v) **
     ((sp + signExtend12 4008) ↦ₘ u6v) **
     ((sp + signExtend12 4000) ↦ₘ u7v) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4088) ↦ₘ q0v) **
     ((sp + signExtend12 4080) ↦ₘ q1v) **
     ((sp + signExtend12 4072) ↦ₘ q2v) **
     ((sp + signExtend12 4064) ↦ₘ q3v) **
     (sp + signExtend12 3968 ↦ₘ retv) ** (sp + signExtend12 3960 ↦ₘ dv) **
     (sp + signExtend12 3952 ↦ₘ dlov) ** (sp + signExtend12 3944 ↦ₘ sunv)) ** F)) h_full := by
    xperm_hyp hAll
  have hQ2F : (POST_LOOP_PRE ** (((.x1 ↦ᵣ x1v) ** (.x11 ↦ᵣ x11v) **
     (sp + signExtend12 3976 ↦ₘ j_v) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     ((sp + signExtend12 4024) ↦ₘ u4v) **
     ((sp + signExtend12 4016) ↦ₘ u5v) **
     ((sp + signExtend12 4008) ↦ₘ u6v) **
     ((sp + signExtend12 4000) ↦ₘ u7v) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4088) ↦ₘ q0v) **
     ((sp + signExtend12 4080) ↦ₘ q1v) **
     ((sp + signExtend12 4072) ↦ₘ q2v) **
     ((sp + signExtend12 4064) ↦ₘ q3v) **
     (sp + signExtend12 3968 ↦ₘ retv) ** (sp + signExtend12 3960 ↦ₘ dv) **
     (sp + signExtend12 3952 ↦ₘ dlov) ** (sp + signExtend12 3944 ↦ₘ sunv)) ** F)).holdsFor s1 :=
    ⟨h_full, hcompat1, hRearranged⟩
  -- Prove pcFree for LEFTOVER ** F
  have hLOF_pcFree : (((.x1 ↦ᵣ x1v) ** (.x11 ↦ᵣ x11v) **
     (sp + signExtend12 3976 ↦ₘ j_v) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     ((sp + signExtend12 4024) ↦ₘ u4v) **
     ((sp + signExtend12 4016) ↦ₘ u5v) **
     ((sp + signExtend12 4008) ↦ₘ u6v) **
     ((sp + signExtend12 4000) ↦ₘ u7v) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4088) ↦ₘ q0v) **
     ((sp + signExtend12 4080) ↦ₘ q1v) **
     ((sp + signExtend12 4072) ↦ₘ q2v) **
     ((sp + signExtend12 4064) ↦ₘ q3v) **
     (sp + signExtend12 3968 ↦ₘ retv) ** (sp + signExtend12 3960 ↦ₘ dv) **
     (sp + signExtend12 3952 ↦ₘ dlov) ** (sp + signExtend12 3944 ↦ₘ sunv)) ** F).pcFree := by
    pcFree; exact hF
  -- Apply epilogue with LEFTOVER ** F as the frame
  obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ :=
    hDE (((.x1 ↦ᵣ x1v) ** (.x11 ↦ᵣ x11v) **
     (sp + signExtend12 3976 ↦ₘ j_v) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     ((sp + signExtend12 4024) ↦ₘ u4v) **
     ((sp + signExtend12 4016) ↦ₘ u5v) **
     ((sp + signExtend12 4008) ↦ₘ u6v) **
     ((sp + signExtend12 4000) ↦ₘ u7v) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4088) ↦ₘ q0v) **
     ((sp + signExtend12 4080) ↦ₘ q1v) **
     ((sp + signExtend12 4072) ↦ₘ q2v) **
     ((sp + signExtend12 4064) ↦ₘ q3v) **
     (sp + signExtend12 3968 ↦ₘ retv) ** (sp + signExtend12 3960 ↦ₘ dv) **
     (sp + signExtend12 3952 ↦ₘ dlov) ** (sp + signExtend12 3944 ↦ₘ sunv)) ** F) hLOF_pcFree s1
      (CodeReq.SatisfiedBy_preserved (modCode base) k1 _ _ hstep1 hcr) hQ2F hpc1
  -- Chain the steps
  refine ⟨k1 + k2, s2, stepN_add_eq k1 k2 st s1 s2 hstep1 hstep2, hpc2, ?_⟩
  -- Convert: (POST_LOOP_POST ** LEFTOVER ** F).holdsFor → (declared_post ** F).holdsFor
  obtain ⟨h_res, hcompat2, hRF_heap⟩ := hRF
  refine ⟨h_res, hcompat2, ?_⟩
  -- Re-associate: POST ** (LO ** F) → (POST ** LO) ** F
  rw [← sepConj_assoc'] at hRF_heap
  obtain ⟨h_pl, h_f3, heq_r, hdisj_r, hPL, hF3⟩ := hRF_heap
  refine ⟨h_pl, h_f3, heq_r, hdisj_r, ?_, hF3⟩
  -- Expand let-bindings in POST_LOOP_POST
  intro_lets at hPL
  exact ⟨q0v, q1v, q2v, q3v, _, x1v, x11v,
    _, _, _, _, u4v, u5v, u6v, u7v, j_v,
    retv, dv, dlov, sunv,
    by xperm_hyp hPL⟩

end EvmAsm.Rv64
