/-
  EvmAsm.Evm64.Byte.LimbSpec

  CPS specifications for the 256-bit EVM BYTE program (64-bit).
  Modular decomposition:
  - Phase B: byte_phase_b_spec (5 instrs): compute bit_shift and limbFromMsb
  - body_3: extract from limb 0 at sp+32, JAL to store (4 instrs)
  - body_2: extract from limb 1 at sp+40, JAL to store (4 instrs)
  - body_1: extract from limb 2 at sp+48, JAL to store (4 instrs)
  - body_0: extract from limb 3 at sp+56, falls through to store (3 instrs)
  - store: pop index word, write byte result + 3 zero limbs (6 instrs)
  - zero_path: pop index word, write all zeros (5 instrs)
-/

import EvmAsm.Evm64.Byte.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Phase A: OR-reduce high index limbs (5 instructions, offset 0-16)
-- Uses full byte_phase_a code as CodeReq for composition.
-- ============================================================================

abbrev byte_phase_a_code (base : Word) : CodeReq :=
  CodeReq.ofProg base byte_phase_a

/-- Phase A OR-reduce body: LD idx[1], LD idx[2], OR, LD idx[3], OR.
    Produces x5 = idx1 ||| idx2 ||| idx3. Uses full phase_a code. -/
theorem byte_phase_a_or_reduce_spec (sp v5 v10 idx1 idx2 idx3 : Word) (base : Word) :
    let orHigh := idx1 ||| idx2 ||| idx3
    let cr := byte_phase_a_code base
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 8) ↦ₘ idx1) **
       ((sp + signExtend12 16) ↦ₘ idx2) **
       ((sp + signExtend12 24) ↦ₘ idx3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ orHigh) ** (.x10 ↦ᵣ idx3) **
       ((sp + signExtend12 8) ↦ₘ idx1) **
       ((sp + signExtend12 16) ↦ₘ idx2) **
       ((sp + signExtend12 24) ↦ₘ idx3)) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 idx1 8 base (by nofun)
  have I1 := ld_spec_gen .x10 .x12 sp v10 idx2 16 (base + 4) (by nofun)
  have I2 := or_spec_gen_rd_eq_rs1 .x5 .x10 idx1 idx2 (base + 8) (by nofun)
  have I3 := ld_spec_gen .x10 .x12 sp idx2 idx3 24 (base + 12) (by nofun)
  have I4 := or_spec_gen_rd_eq_rs1 .x5 .x10 (idx1 ||| idx2) idx3 (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- Phase A: Load idx[0] and check < 32 (2 instructions, offset 24-28)
-- ============================================================================

/-- Phase A low-check: LD idx[0] into x5, SLTIU x10 = (idx0 < 32).
    Located at offset 24 within byte_phase_a (after OR-reduce + BNE). -/
theorem byte_phase_a_low_check_spec (sp v5 idx0 v10 : Word) (base : Word) :
    let cr := byte_phase_a_code base
    cpsTriple (base + 24) (base + 32) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 0) ↦ₘ idx0))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ idx0) **
       (.x10 ↦ᵣ (if BitVec.ult idx0 (signExtend12 32) then (1 : Word) else 0)) **
       ((sp + signExtend12 0) ↦ₘ idx0)) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 idx0 0 (base + 24) (by nofun)
  have I1 := sltiu_spec_gen .x10 .x5 v10 idx0 32 (base + 28) (by nofun)
  runBlock I0 I1

-- ============================================================================
-- Phase B: Compute bit_shift and limbFromMsb (5 instructions)
-- Same computation as SignExtend Phase B
-- ============================================================================

abbrev byte_phase_b_code (base : Word) : CodeReq :=
  CodeReq.ofProg base byte_phase_b

/-- Phase B spec: compute byte extraction parameters.
    ANDI x10,x5,7; SLLI x10,x10,3; ADDI x6,x0,56;
    SUB x6,x6,x10; SRLI x5,x5,3.
    Outputs: x6 = 56 - (idx%8)*8 (bit_shift), x5 = idx/8 (limbFromMsb). -/
theorem byte_phase_b_spec (idx r6 r10 : Word) (base : Word) :
    let byteInLimb := idx &&& signExtend12 (7 : BitVec 12)
    let byteShift := byteInLimb <<< (3 : BitVec 6).toNat
    let shiftAmount := (56 : Word) - byteShift
    let limbFromMsb := idx >>> (3 : BitVec 6).toNat
    let code := byte_phase_b_code base
    cpsTriple base (base + 20) code
      ((.x5 ↦ᵣ idx) ** (.x6 ↦ᵣ r6) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10))
      ((.x5 ↦ᵣ limbFromMsb) ** (.x6 ↦ᵣ shiftAmount) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ byteShift)) := by
  have A := andi_spec_gen .x10 .x5 r10 idx 7 base (by nofun)
  have SL := slli_spec_gen_same .x10 (idx &&& signExtend12 7) 3 (base + 4) (by nofun)
  have AD := addi_x0_spec_gen .x6 r6 56 (base + 8) (by nofun)
  have SU := sub_spec_gen_rd_eq_rs1 .x6 .x10 (signExtend12 56)
    ((idx &&& signExtend12 7) <<< (3 : BitVec 6).toNat) (base + 12) (by nofun)
  have SR := srli_spec_gen_same .x5 idx 3 (base + 16) (by nofun)
  runBlock A SL AD SU SR

-- ============================================================================
-- Body specs: extract byte from limb (LD + SRL + ANDI 0xFF + optional JAL)
-- ============================================================================

-- body_3: LD sp+32, SRL, ANDI 0xFF, JAL 48 (4 instrs)
-- limbFromMsb = 3 → extract from limb 0 (LSB) at sp+32

abbrev byte_body_3_code (base : Word) : CodeReq :=
  CodeReq.ofProg base byte_body_3

/-- body_3 spec: load limb 0 from sp+32, extract byte, jump to store. -/
theorem byte_body_3_spec (sp v5 shiftAmount limb : Word) (base : Word) :
    let result := (limb >>> (shiftAmount.toNat % 64)) &&& signExtend12 (255 : BitVec 12)
    let code := byte_body_3_code base
    cpsTriple base ((base + 12) + signExtend21 (48 : BitVec 21)) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shiftAmount) **
       ((sp + signExtend12 32) ↦ₘ limb))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shiftAmount) **
       ((sp + signExtend12 32) ↦ₘ limb)) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 limb 32 base (by nofun)
  have I1 := srl_spec_gen_rd_eq_rs1 .x5 .x6 limb shiftAmount (base + 4) (by nofun)
  have I2 := andi_spec_gen_same .x5 (limb >>> (shiftAmount.toNat % 64)) 255 (base + 8) (by nofun)
  have I3 := jal_x0_spec_gen (48 : BitVec 21) (base + 12)
  runBlock I0 I1 I2 I3

-- body_2: LD sp+40, SRL, ANDI 0xFF, JAL 32 (4 instrs)
-- limbFromMsb = 2 → extract from limb 1 at sp+40

abbrev byte_body_2_code (base : Word) : CodeReq :=
  CodeReq.ofProg base byte_body_2

/-- body_2 spec: load limb 1 from sp+40, extract byte, jump to store. -/
theorem byte_body_2_spec (sp v5 shiftAmount limb : Word) (base : Word) :
    let result := (limb >>> (shiftAmount.toNat % 64)) &&& signExtend12 (255 : BitVec 12)
    let code := byte_body_2_code base
    cpsTriple base ((base + 12) + signExtend21 (32 : BitVec 21)) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shiftAmount) **
       ((sp + signExtend12 40) ↦ₘ limb))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shiftAmount) **
       ((sp + signExtend12 40) ↦ₘ limb)) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 limb 40 base (by nofun)
  have I1 := srl_spec_gen_rd_eq_rs1 .x5 .x6 limb shiftAmount (base + 4) (by nofun)
  have I2 := andi_spec_gen_same .x5 (limb >>> (shiftAmount.toNat % 64)) 255 (base + 8) (by nofun)
  have I3 := jal_x0_spec_gen (32 : BitVec 21) (base + 12)
  runBlock I0 I1 I2 I3

-- body_1: LD sp+48, SRL, ANDI 0xFF, JAL 16 (4 instrs)
-- limbFromMsb = 1 → extract from limb 2 at sp+48

abbrev byte_body_1_code (base : Word) : CodeReq :=
  CodeReq.ofProg base byte_body_1

/-- body_1 spec: load limb 2 from sp+48, extract byte, jump to store. -/
theorem byte_body_1_spec (sp v5 shiftAmount limb : Word) (base : Word) :
    let result := (limb >>> (shiftAmount.toNat % 64)) &&& signExtend12 (255 : BitVec 12)
    let code := byte_body_1_code base
    cpsTriple base ((base + 12) + signExtend21 (16 : BitVec 21)) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shiftAmount) **
       ((sp + signExtend12 48) ↦ₘ limb))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shiftAmount) **
       ((sp + signExtend12 48) ↦ₘ limb)) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 limb 48 base (by nofun)
  have I1 := srl_spec_gen_rd_eq_rs1 .x5 .x6 limb shiftAmount (base + 4) (by nofun)
  have I2 := andi_spec_gen_same .x5 (limb >>> (shiftAmount.toNat % 64)) 255 (base + 8) (by nofun)
  have I3 := jal_x0_spec_gen (16 : BitVec 21) (base + 12)
  runBlock I0 I1 I2 I3

-- body_0: LD sp+56, SRL, ANDI 0xFF (3 instrs, falls through to store)
-- limbFromMsb = 0 → extract from limb 3 (MSB) at sp+56

abbrev byte_body_0_code (base : Word) : CodeReq :=
  CodeReq.ofProg base byte_body_0

/-- body_0 spec: load limb 3 from sp+56, extract byte. Falls through to store. -/
theorem byte_body_0_spec (sp v5 shiftAmount limb : Word) (base : Word) :
    let result := (limb >>> (shiftAmount.toNat % 64)) &&& signExtend12 (255 : BitVec 12)
    let code := byte_body_0_code base
    cpsTriple base (base + 12) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shiftAmount) **
       ((sp + signExtend12 56) ↦ₘ limb))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shiftAmount) **
       ((sp + signExtend12 56) ↦ₘ limb)) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 limb 56 base (by nofun)
  have I1 := srl_spec_gen_rd_eq_rs1 .x5 .x6 limb shiftAmount (base + 4) (by nofun)
  have I2 := andi_spec_gen_same .x5 (limb >>> (shiftAmount.toNat % 64)) 255 (base + 8) (by nofun)
  runBlock I0 I1 I2

-- ============================================================================
-- Store: pop index word, write byte result + 3 zero limbs (6 instrs)
-- ============================================================================

abbrev byte_store_code (base : Word) : CodeReq :=
  CodeReq.ofProg base byte_store

/-- Store spec: ADDI x12 32, SD result, SD 0×3, JAL 24.
    Pops the index word (sp → sp+32), writes result at sp+32 and zeros at sp+40..56. -/
theorem byte_store_spec (sp result m0 m8 m16 m24 : Word) (base : Word) :
    let nsp := sp + signExtend12 (32 : BitVec 12)
    let code := byte_store_code base
    cpsTriple base ((base + 20) + signExtend21 (24 : BitVec 21)) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ nsp) ** (.x5 ↦ᵣ result) **
       ((sp + 32) ↦ₘ result) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  have I0 := addi_spec_gen_same .x12 sp 32 base (by nofun)
  have I1 := sd_spec_gen .x12 .x5 (sp + signExtend12 32) result m0 0 (base + 4)
  have I2 := sd_x0_spec_gen .x12 (sp + signExtend12 32) m8 8 (base + 8)
  have I3 := sd_x0_spec_gen .x12 (sp + signExtend12 32) m16 16 (base + 12)
  have I4 := sd_x0_spec_gen .x12 (sp + signExtend12 32) m24 24 (base + 16)
  have I5 := jal_x0_spec_gen (24 : BitVec 21) (base + 20)
  runBlock I0 I1 I2 I3 I4 I5

-- ============================================================================
-- Zero path: pop index word, write all zeros (5 instrs)
-- ============================================================================

abbrev byte_zero_path_code (base : Word) : CodeReq :=
  CodeReq.ofProg base byte_zero_path

/-- Zero path spec: ADDI x12 32, SD 0×4.
    Pops the index word (sp → sp+32), writes zeros at sp+32..56. -/
theorem byte_zero_path_spec (sp m0 m8 m16 m24 : Word) (base : Word) :
    let nsp := sp + signExtend12 (32 : BitVec 12)
    let code := byte_zero_path_code base
    cpsTriple base (base + 20) code
      ((.x12 ↦ᵣ sp) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ nsp) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  have I0 := addi_spec_gen_same .x12 sp 32 base (by nofun)
  have I1 := sd_x0_spec_gen .x12 (sp + signExtend12 32) m0 0 (base + 4)
  have I2 := sd_x0_spec_gen .x12 (sp + signExtend12 32) m8 8 (base + 8)
  have I3 := sd_x0_spec_gen .x12 (sp + signExtend12 32) m16 16 (base + 12)
  have I4 := sd_x0_spec_gen .x12 (sp + signExtend12 32) m24 24 (base + 16)
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- Phase C: Cascade dispatch on limbFromMsb (5 instructions)
-- ============================================================================

abbrev byte_phase_c_code (base : Word) : CodeReq :=
  CodeReq.ofProg base byte_phase_c

/-- Each singleton instruction in byte_phase_c is subsumed by the full program CodeReq. -/
private theorem byte_pc_instr_sub (base addr : Word) (instr : Instr) (k : Nat)
    (hk : k < byte_phase_c.length)
    (h_addr : addr = base + BitVec.ofNat 64 (4 * k))
    (h_instr : byte_phase_c.get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i → (byte_phase_c_code base) a = some i :=
  CodeReq.singleton_mono (h_instr ▸ CodeReq.ofProg_lookup_addr base byte_phase_c k addr hk
    (by decide) h_addr)

-- Per-instruction subsumption lemmas (k = 0..4)
private theorem byte_pc_sub_0 (base : Word) :
    ∀ a i, CodeReq.singleton base (.BEQ .x5 .x0 68) a = some i →
      (byte_phase_c_code base) a = some i :=
  byte_pc_instr_sub base base _ 0 (by decide) (by bv_omega) (by decide)

private theorem byte_pc_sub_1 (base : Word) :
    ∀ a i, CodeReq.singleton (base + 4) (.ADDI .x10 .x0 1) a = some i →
      (byte_phase_c_code base) a = some i :=
  byte_pc_instr_sub base (base + 4) _ 1 (by decide) (by bv_omega) (by decide)

private theorem byte_pc_sub_2 (base : Word) :
    ∀ a i, CodeReq.singleton (base + 8) (.BEQ .x5 .x10 44) a = some i →
      (byte_phase_c_code base) a = some i :=
  byte_pc_instr_sub base (base + 8) _ 2 (by decide) (by bv_omega) (by decide)

private theorem byte_pc_sub_3 (base : Word) :
    ∀ a i, CodeReq.singleton (base + 12) (.ADDI .x10 .x0 2) a = some i →
      (byte_phase_c_code base) a = some i :=
  byte_pc_instr_sub base (base + 12) _ 3 (by decide) (by bv_omega) (by decide)

private theorem byte_pc_sub_4 (base : Word) :
    ∀ a i, CodeReq.singleton (base + 16) (.BEQ .x5 .x10 20) a = some i →
      (byte_phase_c_code base) a = some i :=
  byte_pc_instr_sub base (base + 16) _ 4 (by decide) (by bv_omega) (by decide)

/-- Phase C cascade dispatch spec: branches on x5 (limbFromMsb) to 4 body entry points.
    Each exit postcondition includes pure constraints identifying which branch was taken. -/
theorem byte_phase_c_spec (v5 v10 : Word) (base : Word)
    (e0 e1 e2 e3 : Word)
    (he0 : base + signExtend13 68 = e0)
    (he1 : (base + 8) + signExtend13 44 = e1)
    (he2 : (base + 16) + signExtend13 20 = e2)
    (he3 : base + 20 = e3) :
    let code := byte_phase_c_code base
    cpsNBranch base code
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      [(e0, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** ⌜v5 = 0⌝),
       (e1, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1)) ** ⌜v5 = (0 : Word) + signExtend12 1⌝),
       (e2, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 = (0 : Word) + signExtend12 2⌝),
       (e3, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1 ∧ v5 ≠ (0 : Word) + signExtend12 2⌝)] := by
  intro code
  let cr := byte_phase_c_code base
  -- Step 0: BEQ x5 x0 68 at base — extend to cr, frame with x10
  have beq0_raw := beq_spec_gen .x5 .x0 68 v5 (0 : Word) base
  rw [he0] at beq0_raw
  have beq0_cr := cpsBranch_extend_code (byte_pc_sub_0 base) beq0_raw
  have beq0f : cpsBranch base cr
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      e0 ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** ⌜v5 = 0⌝)
      (base + 4) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** ⌜v5 ≠ 0⌝) :=
    cpsBranch_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsBranch_frameR (.x10 ↦ᵣ v10) (by pcFree) beq0_cr)
  -- Step 1: ADDI x10 x0 1 at base+4 (extend to cr, frame with x5)
  have addi1_raw := addi_spec_gen .x10 .x0 v10 (0 : Word) 1 (base + 4) (by nofun)
  have addi1_cr := cpsTriple_extend_code (byte_pc_sub_1 base) addi1_raw
  have addi1f := cpsTriple_frameR
    (.x5 ↦ᵣ v5) (by pcFree) addi1_cr
  -- Normalize ADDI1 exit PC
  have haddi1_exit : (base + 4 : Word) + 4 = base + 8 := by bv_omega
  rw [haddi1_exit] at addi1f
  -- Step 2: BEQ x5 x10 44 at base+8 (extend to cr, frame with x0)
  have beq1_raw := beq_spec_gen .x5 .x10 44 v5 ((0 : Word) + signExtend12 1) (base + 8)
  rw [he1] at beq1_raw
  have beq1_cr := cpsBranch_extend_code (byte_pc_sub_2 base) beq1_raw
  -- Normalize BEQ1 ntaken exit
  have hbeq1_nf : (base + 8 : Word) + 4 = base + 12 := by bv_omega
  rw [hbeq1_nf] at beq1_raw beq1_cr
  have beq1f := cpsBranch_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) beq1_cr
  -- Compose addi1 + beq1 (let Lean infer intermediate shapes)
  have cs1_composed := cpsTriple_seq_cpsBranch_perm_same_cr
    (fun h hp => by xperm_hyp hp) addi1f beq1f
  -- Clean up cs1 to canonical form via cpsBranch_weaken
  have cs1_clean : cpsBranch (base + 4) cr
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      e1 ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1)) ** ⌜v5 = (0 : Word) + signExtend12 1⌝)
      (base + 12) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1)) ** ⌜v5 ≠ (0 : Word) + signExtend12 1⌝) :=
    cpsBranch_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      cs1_composed
  -- Frame cs1 with ⌜v5 ≠ 0⌝, clean up postconditions
  have cs1_framed := cpsBranch_frameR
    (⌜v5 ≠ (0 : Word)⌝) pcFree_pure cs1_clean
  have cs1_final : cpsBranch (base + 4) cr
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** ⌜v5 ≠ (0 : Word)⌝)
      e1 ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1)) ** ⌜v5 = (0 : Word) + signExtend12 1⌝)
      (base + 12) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1⌝) :=
    cpsBranch_weaken
      (fun h hp => (congrFun (show _ = _ from by xperm) h).mp hp)
      -- taken: strip ⌜v5 ≠ 0⌝ frame
      (fun h hp => (sepConj_pure_right h).1 hp |>.1)
      -- ntaken: combine ⌜v5 ≠ 0⌝ ∧ ⌜v5 ≠ 1⌝
      (fun h hp => by
        have ⟨hinner, hne0⟩ := (sepConj_pure_right h).1 hp
        have hne1 := sepConj_extract_pure_end3 h hinner
        have hregs := sepConj_strip_pure_end3 h hinner
        exact (congrFun (show _ = _ from by xperm) h).mp
          ((sepConj_pure_right h).2 (And.intro hregs (And.intro hne0 hne1))))
      cs1_framed
  -- Step 3: ADDI x10 x0 2 at base+12 (extend to cr, frame with x5)
  have addi2_raw := addi_spec_gen .x10 .x0 ((0 : Word) + signExtend12 1) (0 : Word) 2 (base + 12) (by nofun)
  have addi2_cr := cpsTriple_extend_code (byte_pc_sub_3 base) addi2_raw
  have addi2f := cpsTriple_frameR
    (.x5 ↦ᵣ v5) (by pcFree) addi2_cr
  -- Normalize ADDI2 exit PC
  have haddi2_exit : (base + 12 : Word) + 4 = base + 16 := by bv_omega
  rw [haddi2_exit] at addi2f
  -- Step 4: BEQ x5 x10 20 at base+16 (extend to cr, frame with x0)
  have beq2_raw := beq_spec_gen .x5 .x10 20 v5 ((0 : Word) + signExtend12 2) (base + 16)
  rw [he2] at beq2_raw
  have beq2_cr := cpsBranch_extend_code (byte_pc_sub_4 base) beq2_raw
  -- Normalize BEQ2 ntaken exit
  have hbeq2_nf : (base + 16 : Word) + 4 = base + 20 := by bv_omega
  rw [hbeq2_nf] at beq2_raw beq2_cr
  have beq2f := cpsBranch_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) beq2_cr
  -- Compose addi2 + beq2 (let Lean infer intermediate shapes)
  have cs2_composed := cpsTriple_seq_cpsBranch_perm_same_cr
    (fun h hp => by xperm_hyp hp) addi2f beq2f
  -- Clean up cs2 to canonical form
  have cs2_clean : cpsBranch (base + 12) cr
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1)))
      e2 ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 = (0 : Word) + signExtend12 2⌝)
      (base + 20) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 ≠ (0 : Word) + signExtend12 2⌝) :=
    cpsBranch_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      cs2_composed
  -- Frame cs2 with ⌜v5 ≠ 0 ∧ v5 ≠ 1⌝, clean up postconditions
  have cs2_framed := cpsBranch_frameR
    (⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1⌝) pcFree_pure cs2_clean
  have cs2_final : cpsBranch (base + 12) cr
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1⌝)
      e2 ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 = (0 : Word) + signExtend12 2⌝)
      (base + 20) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1 ∧ v5 ≠ (0 : Word) + signExtend12 2⌝) :=
    cpsBranch_weaken
      (fun h hp => (congrFun (show _ = _ from by xperm) h).mp hp)
      -- taken: strip ⌜conj⌝ frame
      (fun h hp => (sepConj_pure_right h).1 hp |>.1)
      -- ntaken: combine ⌜v5≠0 ∧ v5≠1⌝ ∧ ⌜v5≠2⌝
      (fun h hp => by
        have ⟨hinner, ⟨hne0, hne1⟩⟩ := (sepConj_pure_right h).1 hp
        have hne2 := sepConj_extract_pure_end3 h hinner
        have hregs := sepConj_strip_pure_end3 h hinner
        exact (congrFun (show _ = _ from by xperm) h).mp
          ((sepConj_pure_right h).2 (And.intro hregs (And.intro hne0 (And.intro hne1 hne2)))))
      cs2_framed
  -- Build cpsNBranch from inside out
  -- Fallthrough at base+20: trivial single-exit (0 steps)
  have ft : cpsNBranch (base + 20) cr
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1 ∧ v5 ≠ (0 : Word) + signExtend12 2⌝)
      [(e3, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1 ∧ v5 ≠ (0 : Word) + signExtend12 2⌝)] := by
    intro R hR s _hcr hPR hpc
    exact ⟨0, s, rfl, (e3, _), List.Mem.head _, he3 ▸ hpc, hPR⟩
  -- Chain cs2_final + ft → exits [e2, e3]
  have n3 := cpsBranch_cons_cpsNBranch_same_cr cs2_final ft
  -- Chain cs1_final + n3 → exits [e1, e2, e3]
  have n2 := cpsBranch_cons_cpsNBranch_with_perm_same_cr
    (fun h hp => by xperm_hyp hp) cs1_final n3
  -- Chain beq0f + n2 → exits [e0, e1, e2, e3]
  have n1 := cpsBranch_cons_cpsNBranch_with_perm_same_cr
    (fun h hp => by xperm_hyp hp) beq0f n2
  exact n1

end EvmAsm.Evm64
