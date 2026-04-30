/-
  EvmAsm.Rv64.SyscallSpecs

  Spec database registrations for the `runBlock` auto-mode tactic.
  Each `@[spec_gen_rv64]` theorem is auto-detected by instruction constructor.

  64-bit RISC-V (RV64IM) variant. Uses LD/SD instead of LW/SW for
  64-bit doubleword memory access. Shift amounts use % 64 (not % 32).

  Code is accessed via CodeReq.singleton side-condition (not instrAt in P/Q).
-/

-- `InstructionSpecs → GenericSpecs → Basic, Instructions, SepLogic,
-- Execution, CPSSpec`. `ByteOps`/`HalfwordOps`/`WordOps` are independent
-- leaves and remain as direct imports.
import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.HalfwordOps
import EvmAsm.Rv64.WordOps
import EvmAsm.Rv64.Tactics.SpecDb

namespace EvmAsm.Rv64

-- ============================================================================
-- LD/SD specs (primary memory access for EVM64)
-- ============================================================================

@[spec_gen_rv64] theorem ld_spec_gen_within (rd rs1 : Reg) (v_addr vOld memVal : Word)
    (offset : BitVec 12) (addr : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.LD rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** ((v_addr + signExtend12 offset) ↦ₘ memVal))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ memVal) ** ((v_addr + signExtend12 offset) ↦ₘ memVal)) :=
  generic_ld_spec_within rd rs1 v_addr vOld memVal offset addr hrd_ne_x0
@[spec_gen_rv64] theorem sd_spec_gen_within (rs1 rs2 : Reg) (v_addr v_data memOld : Word)
    (offset : BitVec 12) (addr : Word) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SD rs1 rs2 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ memOld))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v_data)) :=
  generic_sd_spec_within rs1 rs2 v_addr v_data memOld offset addr
@[spec_gen_rv64] theorem sd_spec_gen_own_within (rs1 rs2 : Reg) (v_addr v_data : Word)
    (offset : BitVec 12) (addr : Word) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SD rs1 rs2 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memOwn (v_addr + signExtend12 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v_data)) := by
  intro R hR s hcr hPR hpc
  obtain ⟨h, hcompat, h_P, h_R, hdisj, hunion, hpP, hpR⟩ := hPR
  obtain ⟨hR1, hRest2, hd2, hu2, hpR1, hpRest2⟩ := hpP
  obtain ⟨hR2, hM, hd3, hu3, hpR2, hpM⟩ := hpRest2
  obtain ⟨v, hv⟩ := hpM
  have hPR' : (((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v)) ** R).holdsFor s :=
    ⟨h, hcompat, h_P, h_R, hdisj, hunion, ⟨hR1, hRest2, hd2, hu2, hpR1, hR2, hM, hd3, hu3, hpR2, hv⟩, hpR⟩
  exact sd_spec_gen_within rs1 rs2 v_addr v_data v offset addr R hR s hcr hPR' hpc
@[spec_gen_rv64] theorem add_spec_gen_rd_eq_rs1_within (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.ADD rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 + v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec_within (.ADD rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem sub_spec_gen_rd_eq_rs1_within (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SUB rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 - v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec_within (.SUB rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem and_spec_gen_rd_eq_rs1_within (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.AND rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 &&& v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec_within (.AND rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem or_spec_gen_rd_eq_rs1_within (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.OR rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 ||| v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec_within (.OR rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem xor_spec_gen_rd_eq_rs1_within (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.XOR rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 ^^^ v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec_within (.XOR rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem sltu_spec_gen_rd_eq_rs1_within (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SLTU rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (if BitVec.ult v1 v2 then (1 : Word) else 0)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec_within (.SLTU rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem srl_spec_gen_rd_eq_rs1_within (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SRL rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 >>> (v2.toNat % 64))) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec_within (.SRL rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem sll_spec_gen_rd_eq_rs1_within (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SLL rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 <<< (v2.toNat % 64))) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec_within (.SLL rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem sra_spec_gen_rd_eq_rs1_within (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SRA rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (BitVec.sshiftRight v1 (v2.toNat % 64))) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec_within (.SRA rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem addi_spec_gen_same_within (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.ADDI rd rd imm))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (v + signExtend12 imm)) :=
  generic_1reg_spec_within (.ADDI rd rd imm) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem addi_spec_gen_within (rd rs1 : Reg) (vOld v1 : Word) (imm : BitVec 12)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.ADDI rd rs1 imm))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + signExtend12 imm))) :=
  generic_2reg_spec_within (.ADDI rd rs1 imm) rs1 rd v1 vOld (v1 + signExtend12 imm) addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem xori_spec_gen_same_within (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.XORI rd rd imm))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (v ^^^ signExtend12 imm)) :=
  generic_1reg_spec_within (.XORI rd rd imm) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem andi_spec_gen_within (rd rs1 : Reg) (vOld v1 : Word) (imm : BitVec 12)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.ANDI rd rs1 imm))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 &&& signExtend12 imm))) :=
  generic_2reg_spec_within (.ANDI rd rs1 imm) rs1 rd v1 vOld (v1 &&& signExtend12 imm) addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem andi_spec_gen_same_within (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.ANDI rd rd imm))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (v &&& signExtend12 imm)) :=
  generic_1reg_spec_within (.ANDI rd rd imm) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem sltiu_spec_gen_same_within (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SLTIU rd rd imm))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (if BitVec.ult v (signExtend12 imm) then (1 : Word) else (0 : Word))) :=
  generic_1reg_spec_within (.SLTIU rd rd imm) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem slli_spec_gen_same_within (rd : Reg) (v : Word) (shamt : BitVec 6)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SLLI rd rd shamt))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (v <<< shamt.toNat)) :=
  generic_1reg_spec_within (.SLLI rd rd shamt) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem slli_spec_gen_within (rd rs1 : Reg) (vOld v1 : Word) (shamt : BitVec 6)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SLLI rd rs1 shamt))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 <<< shamt.toNat))) :=
  generic_2reg_spec_within (.SLLI rd rs1 shamt) rs1 rd v1 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem srli_spec_gen_same_within (rd : Reg) (v : Word) (shamt : BitVec 6)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SRLI rd rd shamt))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (v >>> shamt.toNat)) :=
  generic_1reg_spec_within (.SRLI rd rd shamt) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem srli_spec_gen_within (rd rs1 : Reg) (vOld v1 : Word) (shamt : BitVec 6)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SRLI rd rs1 shamt))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 >>> shamt.toNat))) :=
  generic_2reg_spec_within (.SRLI rd rs1 shamt) rs1 rd v1 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem srai_spec_gen_same_within (rd : Reg) (v : Word) (shamt : BitVec 6)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SRAI rd rd shamt))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (BitVec.sshiftRight v shamt.toNat)) :=
  generic_1reg_spec_within (.SRAI rd rd shamt) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem srai_spec_gen_within (rd rs1 : Reg) (vOld v1 : Word) (shamt : BitVec 6)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SRAI rd rs1 shamt))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (BitVec.sshiftRight v1 shamt.toNat))) :=
  generic_2reg_spec_within (.SRAI rd rs1 shamt) rs1 rd v1 vOld (BitVec.sshiftRight v1 shamt.toNat) addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem li_spec_gen_within (rd : Reg) (vOld imm : Word) (addr : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.LI rd imm))
      (rd ↦ᵣ vOld)
      (rd ↦ᵣ imm) :=
  generic_1reg_spec_within (.LI rd imm) rd vOld _ addr hrd_ne_x0
    (by intro s _ _; simp [execInstrBr])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem li_spec_gen_own_within (rd : Reg) (imm : Word) (addr : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.LI rd imm))
      (regOwn rd)
      (rd ↦ᵣ imm) := by
  intro R hR s hcr hPR hpc
  obtain ⟨h, hcompat, hPQ, hR_ps, hdisj, hunion, hpq, hrR⟩ := hPR
  obtain ⟨v, hv⟩ := hpq
  have hPR' : ((rd ↦ᵣ v) ** R).holdsFor s :=
    ⟨h, hcompat, hPQ, hR_ps, hdisj, hunion, hv, hrR⟩
  exact li_spec_gen_within rd v imm addr hrd_ne_x0 R hR s hcr hPR' hpc
@[spec_gen_rv64] theorem mv_spec_gen_within (rd rs : Reg) (v vOld : Word) (addr : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.MV rd rs))
      ((rs ↦ᵣ v) ** (rd ↦ᵣ vOld))
      ((rs ↦ᵣ v) ** (rd ↦ᵣ v)) :=
  generic_2reg_spec_within (.MV rd rs) rs rd v vOld v addr hrd_ne_x0
    (by intro s _ hrs _; simp [execInstrBr, hrs])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem bne_spec_gen_within (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word)
    (addr : Word) :
    cpsBranchWithin 1 addr (CodeReq.singleton addr (.BNE rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (addr + signExtend13 offset)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝)
      (addr + 4)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝) :=
  generic_bne_spec_within rs1 rs2 offset v1 v2 addr
@[spec_gen_rv64] theorem beq_spec_gen_within (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word)
    (addr : Word) :
    cpsBranchWithin 1 addr (CodeReq.singleton addr (.BEQ rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (addr + signExtend13 offset)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝)
      (addr + 4)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝) :=
  generic_beq_spec_within rs1 rs2 offset v1 v2 addr
@[spec_gen_rv64] theorem bltu_spec_gen_within (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word)
    (addr : Word) :
    cpsBranchWithin 1 addr (CodeReq.singleton addr (.BLTU rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (addr + signExtend13 offset)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜BitVec.ult v1 v2⌝)
      (addr + 4)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜¬BitVec.ult v1 v2⌝) :=
  generic_bltu_spec_within rs1 rs2 offset v1 v2 addr
@[spec_gen_rv64] theorem bge_spec_gen_within (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word)
    (addr : Word) :
    cpsBranchWithin 1 addr (CodeReq.singleton addr (.BGE rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (addr + signExtend13 offset)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜¬BitVec.slt v1 v2⌝)
      (addr + 4)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜BitVec.slt v1 v2⌝) :=
  generic_bge_spec_within rs1 rs2 offset v1 v2 addr
@[spec_gen_rv64] theorem blt_spec_gen_within (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word)
    (addr : Word) :
    cpsBranchWithin 1 addr (CodeReq.singleton addr (.BLT rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (addr + signExtend13 offset)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜BitVec.slt v1 v2⌝)
      (addr + 4)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜¬BitVec.slt v1 v2⌝) :=
  generic_blt_spec_within rs1 rs2 offset v1 v2 addr
@[spec_gen_rv64] theorem ecall_halt_spec_gen_within (exitCode : Word) (addr : Word) :
    cpsHaltTripleWithin 0 addr (CodeReq.singleton addr .ECALL)
      ((addr ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode))
      ((addr ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some .ECALL :=
    holdsFor_instrAt.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hx5 : s.getReg .x5 = (0 : Word) :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  refine ⟨0, Nat.le_refl 0, s, rfl, ?_, hPR⟩
  simp only [isHalted, step_ecall_halt hfetch hx5, Option.isNone]
@[spec_gen_rv64] theorem slt_spec_gen_within (rd rs1 rs2 : Reg) (vOld v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SLT rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (if BitVec.slt v1 v2 then (1 : Word) else 0))) :=
  generic_3reg_spec_within (.SLT rd rs1 rs2) rs1 rs2 rd v1 v2 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem sltu_spec_gen_within (rd rs1 rs2 : Reg) (vOld v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SLTU rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (if BitVec.ult v1 v2 then (1 : Word) else 0))) :=
  generic_3reg_spec_within (.SLTU rd rs1 rs2) rs1 rs2 rd v1 v2 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem sltu_spec_gen_rd_eq_rs2_within (rd rs1 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SLTU rd rs1 rd))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v2))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (if BitVec.ult v1 v2 then (1 : Word) else 0))) :=
  generic_2reg_spec_within (.SLTU rd rs1 rd) rs1 rd v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrs1 hrd; simp [execInstrBr, hrs1, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem or_spec_gen_within (rd rs1 rs2 : Reg) (vOld v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.OR rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 ||| v2))) :=
  generic_3reg_spec_within (.OR rd rs1 rs2) rs1 rs2 rd v1 v2 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem mul_spec_gen_within (rd rs1 rs2 : Reg) (vOld v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.MUL rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 * v2))) :=
  generic_3reg_spec_within (.MUL rd rs1 rs2) rs1 rs2 rd v1 v2 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem mul_spec_gen_rd_eq_rs1_within (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.MUL rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 * v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec_within (.MUL rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem mulhu_spec_gen_within (rd rs1 rs2 : Reg) (vOld v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.MULHU rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ rv64_mulhu v1 v2)) :=
  generic_3reg_spec_within (.MULHU rd rs1 rs2) rs1 rs2 rd v1 v2 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem mulhu_spec_gen_rd_eq_rs1_within (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.MULHU rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ rv64_mulhu v1 v2) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec_within (.MULHU rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem mulhu_spec_gen_rd_eq_rs2_within (rd rs1 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.MULHU rd rs1 rd))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v2))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ rv64_mulhu v1 v2)) :=
  generic_2reg_spec_within (.MULHU rd rs1 rd) rs1 rd v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrs1 hrd; simp [execInstrBr, hrs1, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem mul_spec_gen_rd_eq_rs2_within (rd rs1 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.MUL rd rs1 rd))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v2))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 * v2))) :=
  generic_2reg_spec_within (.MUL rd rs1 rd) rs1 rd v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrs1 hrd; simp [execInstrBr, hrs1, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem divu_spec_gen_within (rd rs1 rs2 : Reg) (vOld v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.DIVU rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ rv64_divu v1 v2)) :=
  generic_3reg_spec_within (.DIVU rd rs1 rs2) rs1 rs2 rd v1 v2 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem divu_spec_gen_rd_eq_rs1_within (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.DIVU rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ rv64_divu v1 v2) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec_within (.DIVU rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem remu_spec_gen_within (rd rs1 rs2 : Reg) (vOld v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.REMU rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ rv64_remu v1 v2)) :=
  generic_3reg_spec_within (.REMU rd rs1 rs2) rs1 rs2 rd v1 v2 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem remu_spec_gen_rd_eq_rs1_within (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.REMU rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ rv64_remu v1 v2) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec_within (.REMU rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem sub_spec_gen_rd_eq_rs2_within (rd rs1 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SUB rd rs1 rd))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v2))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 - v2))) :=
  generic_2reg_spec_within (.SUB rd rs1 rd) rs1 rd v1 v2 (v1 - v2) addr hrd_ne_x0
    (by intro s _ hrs1 hrd; simp [execInstrBr, hrs1, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem sub_spec_gen_within (rd rs1 rs2 : Reg) (v1 v2 vOld : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SUB rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 - v2))) :=
  generic_3reg_spec_within (.SUB rd rs1 rs2) rs1 rs2 rd v1 v2 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem sltiu_spec_gen_within (rd rs1 : Reg) (vOld v1 : Word) (imm : BitVec 12)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SLTIU rd rs1 imm))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (if BitVec.ult v1 (signExtend12 imm) then (1 : Word) else (0 : Word)))) :=
  generic_2reg_spec_within (.SLTIU rd rs1 imm) rs1 rd v1 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem sd_x0_spec_gen_within (rs1 : Reg) (v_addr memOld : Word)
    (offset : BitVec 12) (addr : Word) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SD rs1 .x0 offset))
      ((rs1 ↦ᵣ v_addr) ** ((v_addr + signExtend12 offset) ↦ₘ memOld))
      ((rs1 ↦ᵣ v_addr) ** ((v_addr + signExtend12 offset) ↦ₘ (0 : Word))) :=
  generic_sd_x0_spec_within rs1 v_addr memOld offset addr
@[spec_gen_rv64] theorem srl_spec_gen_within (rd rs1 rs2 : Reg) (vOld v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SRL rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 >>> (v2.toNat % 64)))) :=
  generic_3reg_spec_within (.SRL rd rs1 rs2) rs1 rs2 rd v1 v2 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem sll_spec_gen_within (rd rs1 rs2 : Reg) (vOld v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SLL rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 <<< (v2.toNat % 64)))) :=
  generic_3reg_spec_within (.SLL rd rs1 rs2) rs1 rs2 rd v1 v2 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem add_spec_gen_rd_eq_rs2_within (rd rs1 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.ADD rd rs1 rd))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v2))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + v2))) :=
  generic_2reg_spec_within (.ADD rd rs1 rd) rs1 rd v1 v2 (v1 + v2) addr hrd_ne_x0
    (by intro s _ hrs1 hrd; simp [execInstrBr, hrs1, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem add_spec_gen_within (rd rs1 rs2 : Reg) (v1 v2 vOld : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.ADD rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 + v2))) :=
  generic_3reg_spec_within (.ADD rd rs1 rs2) rs1 rs2 rd v1 v2 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem addi_x0_spec_gen_within (rd : Reg) (vOld : Word) (imm : BitVec 12)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.ADDI rd .x0 imm))
      ((.x0 ↦ᵣ (0 : Word)) ** (rd ↦ᵣ vOld))
      ((.x0 ↦ᵣ (0 : Word)) ** (rd ↦ᵣ (signExtend12 imm))) := by
  have h := addi_spec_gen_within rd .x0 vOld (0 : Word) imm addr hrd_ne_x0
  have heq : (0 : Word) + signExtend12 imm = signExtend12 imm := by bv_omega
  rw [heq] at h; exact h
@[spec_gen_rv64] theorem ld_spec_gen_same_within (rd : Reg) (v_addr memVal : Word)
    (offset : BitVec 12) (addr : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.LD rd rd offset))
      ((rd ↦ᵣ v_addr) ** ((v_addr + signExtend12 offset) ↦ₘ memVal))
      ((rd ↦ᵣ memVal) ** ((v_addr + signExtend12 offset) ↦ₘ memVal)) :=
  ld_spec_same_within rd v_addr memVal offset addr hrd_ne_x0
@[spec_gen_rv64] theorem ori_spec_gen_same_within (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.ORI rd rd imm))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (v ||| signExtend12 imm)) :=
  generic_1reg_spec_within (.ORI rd rd imm) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem ori_spec_gen_within (rd rs1 : Reg) (vOld v1 : Word) (imm : BitVec 12)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.ORI rd rs1 imm))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 ||| signExtend12 imm))) :=
  generic_2reg_spec_within (.ORI rd rs1 imm) rs1 rd v1 vOld (v1 ||| signExtend12 imm) addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem slti_spec_gen_same_within (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SLTI rd rd imm))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (if BitVec.slt v (signExtend12 imm) then 1 else 0)) :=
  generic_1reg_spec_within (.SLTI rd rd imm) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem slti_spec_gen_within (rd rs1 : Reg) (vOld v1 : Word) (imm : BitVec 12)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.SLTI rd rs1 imm))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (if BitVec.slt v1 (signExtend12 imm) then 1 else 0))) :=
  generic_2reg_spec_within (.SLTI rd rs1 imm) rs1 rd v1 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem addiw_spec_gen_same_within (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.ADDIW rd rd imm))
      (rd ↦ᵣ v)
      (rd ↦ᵣ ((v.truncate 32 + (signExtend12 imm).truncate 32 : BitVec 32).signExtend 64)) :=
  generic_1reg_spec_within (.ADDIW rd rd imm) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem addiw_spec_gen_within (rd rs1 : Reg) (vOld v1 : Word) (imm : BitVec 12)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.ADDIW rd rs1 imm))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ ((v1.truncate 32 + (signExtend12 imm).truncate 32 : BitVec 32).signExtend 64))) :=
  generic_2reg_spec_within (.ADDIW rd rs1 imm) rs1 rd v1 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem bgeu_spec_gen_within (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word)
    (addr : Word) :
    cpsBranchWithin 1 addr (CodeReq.singleton addr (.BGEU rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (addr + signExtend13 offset)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜¬BitVec.ult v1 v2⌝)
      (addr + 4)
        ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜BitVec.ult v1 v2⌝) :=
  generic_bgeu_spec_within rs1 rs2 offset v1 v2 addr
@[spec_gen_rv64] theorem lui_spec_gen_within (rd : Reg) (vOld : Word) (imm : BitVec 20)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.LUI rd imm))
      (rd ↦ᵣ vOld)
      (rd ↦ᵣ ((imm.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64) :=
  generic_1reg_spec_within (.LUI rd imm) rd vOld _ addr hrd_ne_x0
    (by intro s _ _; simp [execInstrBr])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem auipc_spec_gen_within (rd : Reg) (vOld : Word) (imm : BitVec 20)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.AUIPC rd imm))
      (rd ↦ᵣ vOld)
      (rd ↦ᵣ (addr + ((imm.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64)) :=
  generic_1reg_spec_within (.AUIPC rd imm) rd vOld _ addr hrd_ne_x0
    (by intro s hpc _; simp [execInstrBr, hpc])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem lbu_spec_gen_within (rd rs1 : Reg) (v_addr vOld : Word)
    (offset : BitVec 12) (addr : Word)
    (dwordAddr : Word) (wordVal : Word)
    (hrd_ne_x0 : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidByteAccess (v_addr + signExtend12 offset) = true) :
    cpsTripleWithin 1 addr (addr + 4)
      (CodeReq.singleton addr (.LBU rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** (dwordAddr ↦ₘ wordVal))
      ((rs1 ↦ᵣ v_addr) **
       (rd ↦ᵣ (extractByte wordVal (byteOffset (v_addr + signExtend12 offset))).zeroExtend 64) **
       (dwordAddr ↦ₘ wordVal)) :=
  generic_lbu_spec_within rd rs1 v_addr vOld offset addr dwordAddr wordVal
    hrd_ne_x0 halign hvalid
@[spec_gen_rv64] theorem lb_spec_gen_within (rd rs1 : Reg) (v_addr vOld : Word)
    (offset : BitVec 12) (addr : Word)
    (dwordAddr : Word) (wordVal : Word)
    (hrd_ne_x0 : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidByteAccess (v_addr + signExtend12 offset) = true) :
    cpsTripleWithin 1 addr (addr + 4)
      (CodeReq.singleton addr (.LB rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** (dwordAddr ↦ₘ wordVal))
      ((rs1 ↦ᵣ v_addr) **
       (rd ↦ᵣ (extractByte wordVal (byteOffset (v_addr + signExtend12 offset))).signExtend 64) **
       (dwordAddr ↦ₘ wordVal)) :=
  generic_lb_spec_within rd rs1 v_addr vOld offset addr dwordAddr wordVal
    hrd_ne_x0 halign hvalid
@[spec_gen_rv64] theorem sb_spec_gen_within (rs1 rs2 : Reg) (v_addr v_data : Word)
    (offset : BitVec 12) (addr : Word)
    (dwordAddr : Word) (wordOld : Word)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidByteAccess (v_addr + signExtend12 offset) = true) :
    cpsTripleWithin 1 addr (addr + 4)
      (CodeReq.singleton addr (.SB rs1 rs2 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (dwordAddr ↦ₘ wordOld))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) **
       (dwordAddr ↦ₘ replaceByte wordOld (byteOffset (v_addr + signExtend12 offset)) (v_data.truncate 8))) :=
  generic_sb_spec_within rs1 rs2 v_addr v_data offset addr dwordAddr wordOld
    halign hvalid
@[spec_gen_rv64] theorem mulh_spec_gen_within (rd rs1 rs2 : Reg) (vOld v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.MULH rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ rv64_mulh v1 v2)) :=
  generic_3reg_spec_within (.MULH rd rs1 rs2) rs1 rs2 rd v1 v2 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem mulh_spec_gen_rd_eq_rs1_within (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.MULH rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ rv64_mulh v1 v2) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec_within (.MULH rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem mulhsu_spec_gen_within (rd rs1 rs2 : Reg) (vOld v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.MULHSU rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ rv64_mulhsu v1 v2)) :=
  generic_3reg_spec_within (.MULHSU rd rs1 rs2) rs1 rs2 rd v1 v2 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem mulhsu_spec_gen_rd_eq_rs1_within (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.MULHSU rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ rv64_mulhsu v1 v2) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec_within (.MULHSU rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem div_spec_gen_within (rd rs1 rs2 : Reg) (vOld v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.DIV rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ rv64_div v1 v2)) :=
  generic_3reg_spec_within (.DIV rd rs1 rs2) rs1 rs2 rd v1 v2 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem div_spec_gen_rd_eq_rs1_within (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.DIV rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ rv64_div v1 v2) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec_within (.DIV rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem rem_spec_gen_within (rd rs1 rs2 : Reg) (vOld v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.REM rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ rv64_rem v1 v2)) :=
  generic_3reg_spec_within (.REM rd rs1 rs2) rs1 rs2 rd v1 v2 vOld _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem rem_spec_gen_rd_eq_rs1_within (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.REM rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ rv64_rem v1 v2) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec_within (.REM rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))
@[spec_gen_rv64] theorem lhu_spec_gen_within (rd rs1 : Reg) (v_addr vOld : Word)
    (offset : BitVec 12) (addr : Word)
    (dwordAddr : Word) (wordVal : Word)
    (hrd_ne_x0 : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidHalfwordAccess (v_addr + signExtend12 offset) = true) :
    cpsTripleWithin 1 addr (addr + 4)
      (CodeReq.singleton addr (.LHU rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** (dwordAddr ↦ₘ wordVal))
      ((rs1 ↦ᵣ v_addr) **
       (rd ↦ᵣ (extractHalfword wordVal ((byteOffset (v_addr + signExtend12 offset)) / 2)).zeroExtend 64) **
       (dwordAddr ↦ₘ wordVal)) :=
  generic_lhu_spec_within rd rs1 v_addr vOld offset addr dwordAddr wordVal
    hrd_ne_x0 halign hvalid
@[spec_gen_rv64] theorem lh_spec_gen_within (rd rs1 : Reg) (v_addr vOld : Word)
    (offset : BitVec 12) (addr : Word)
    (dwordAddr : Word) (wordVal : Word)
    (hrd_ne_x0 : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidHalfwordAccess (v_addr + signExtend12 offset) = true) :
    cpsTripleWithin 1 addr (addr + 4)
      (CodeReq.singleton addr (.LH rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** (dwordAddr ↦ₘ wordVal))
      ((rs1 ↦ᵣ v_addr) **
       (rd ↦ᵣ (extractHalfword wordVal ((byteOffset (v_addr + signExtend12 offset)) / 2)).signExtend 64) **
       (dwordAddr ↦ₘ wordVal)) :=
  generic_lh_spec_within rd rs1 v_addr vOld offset addr dwordAddr wordVal
    hrd_ne_x0 halign hvalid
@[spec_gen_rv64] theorem sh_spec_gen_within (rs1 rs2 : Reg) (v_addr v_data : Word)
    (offset : BitVec 12) (addr : Word)
    (dwordAddr : Word) (wordOld : Word)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidHalfwordAccess (v_addr + signExtend12 offset) = true) :
    cpsTripleWithin 1 addr (addr + 4)
      (CodeReq.singleton addr (.SH rs1 rs2 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (dwordAddr ↦ₘ wordOld))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) **
       (dwordAddr ↦ₘ replaceHalfword wordOld ((byteOffset (v_addr + signExtend12 offset)) / 2) (v_data.truncate 16))) :=
  generic_sh_spec_within rs1 rs2 v_addr v_data offset addr dwordAddr wordOld
    halign hvalid
@[spec_gen_rv64] theorem lwu_spec_gen_within (rd rs1 : Reg) (v_addr vOld : Word)
    (offset : BitVec 12) (addr : Word)
    (dwordAddr : Word) (wordVal : Word)
    (hrd_ne_x0 : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTripleWithin 1 addr (addr + 4)
      (CodeReq.singleton addr (.LWU rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** (dwordAddr ↦ₘ wordVal))
      ((rs1 ↦ᵣ v_addr) **
       (rd ↦ᵣ (extractWord32 wordVal ((byteOffset (v_addr + signExtend12 offset)) / 4)).zeroExtend 64) **
       (dwordAddr ↦ₘ wordVal)) :=
  generic_lwu_spec_within rd rs1 v_addr vOld offset addr dwordAddr wordVal
    hrd_ne_x0 halign hvalid
@[spec_gen_rv64] theorem lw_spec_gen_within (rd rs1 : Reg) (v_addr vOld : Word)
    (offset : BitVec 12) (addr : Word)
    (dwordAddr : Word) (wordVal : Word)
    (hrd_ne_x0 : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTripleWithin 1 addr (addr + 4)
      (CodeReq.singleton addr (.LW rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** (dwordAddr ↦ₘ wordVal))
      ((rs1 ↦ᵣ v_addr) **
       (rd ↦ᵣ (extractWord32 wordVal ((byteOffset (v_addr + signExtend12 offset)) / 4)).signExtend 64) **
       (dwordAddr ↦ₘ wordVal)) :=
  generic_lw_spec_within rd rs1 v_addr vOld offset addr dwordAddr wordVal
    hrd_ne_x0 halign hvalid
@[spec_gen_rv64] theorem sw_spec_gen_within (rs1 rs2 : Reg) (v_addr v_data : Word)
    (offset : BitVec 12) (addr : Word)
    (dwordAddr : Word) (wordOld : Word)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTripleWithin 1 addr (addr + 4)
      (CodeReq.singleton addr (.SW rs1 rs2 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (dwordAddr ↦ₘ wordOld))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) **
       (dwordAddr ↦ₘ replaceWord32 wordOld ((byteOffset (v_addr + signExtend12 offset)) / 4) (v_data.truncate 32))) :=
  generic_sw_spec_within rs1 rs2 v_addr v_data offset addr dwordAddr wordOld
    halign hvalid
end EvmAsm.Rv64
