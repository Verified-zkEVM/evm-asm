/-
  EvmAsm.Rv64.SyscallSpecs

  Spec database registrations for the `runBlock` auto-mode tactic.
  Each `@[spec_gen_rv64]` theorem is auto-detected by instruction constructor.

  64-bit RISC-V (RV64IM) variant. Uses LD/SD instead of LW/SW for
  64-bit doubleword memory access. Shift amounts use % 64 (not % 32).
-/

import EvmAsm.Rv64.Basic
import EvmAsm.Rv64.Instructions
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.GenericSpecs
import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Rv64.Tactics.SpecDb

namespace EvmAsm.Rv64

-- ============================================================================
-- LD/SD specs (primary memory access for EVM64)
-- ============================================================================

@[spec_gen_rv64] theorem ld_spec_gen (rd rs1 : Reg) (v_addr v_old mem_val : Word)
    (offset : BitVec 12) (addr : Addr)
    (hrd_ne_x0 : rd ≠ .x0)
    (hvalid : isValidDwordAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .LD rd rs1 offset) ** (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ v_old) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val))
      ((addr ↦ᵢ .LD rd rs1 offset) ** (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ mem_val) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val)) :=
  generic_ld_spec rd rs1 v_addr v_old mem_val offset addr hrd_ne_x0 hvalid

@[spec_gen_rv64] theorem sd_spec_gen (rs1 rs2 : Reg) (v_addr v_data mem_old : Word)
    (offset : BitVec 12) (addr : Addr)
    (hvalid : isValidDwordAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SD rs1 rs2 offset) ** (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ mem_old))
      ((addr ↦ᵢ .SD rs1 rs2 offset) ** (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v_data)) :=
  generic_sd_spec rs1 rs2 v_addr v_data mem_old offset addr hvalid

@[spec_gen_rv64] theorem sd_spec_gen_own (rs1 rs2 : Reg) (v_addr v_data : Word)
    (offset : BitVec 12) (addr : Addr)
    (hvalid : isValidDwordAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SD rs1 rs2 offset) ** (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memOwn (v_addr + signExtend12 offset))
      ((addr ↦ᵢ .SD rs1 rs2 offset) ** (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v_data)) := by
  intro R hR s hPR hpc
  obtain ⟨h, hcompat, h_P, h_R, hdisj, hunion, hpP, hpR⟩ := hPR
  obtain ⟨hI, hRest, hd1, hu1, hpI, hpRest⟩ := hpP
  obtain ⟨hR1, hRest2, hd2, hu2, hpR1, hpRest2⟩ := hpRest
  obtain ⟨hR2, hM, hd3, hu3, hpR2, hpM⟩ := hpRest2
  obtain ⟨v, hv⟩ := hpM
  have hPR' : (((addr ↦ᵢ .SD rs1 rs2 offset) ** (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v)) ** R).holdsFor s :=
    ⟨h, hcompat, h_P, h_R, hdisj, hunion, ⟨hI, hRest, hd1, hu1, hpI, hR1, hRest2, hd2, hu2, hpR1, hR2, hM, hd3, hu3, hpR2, hv⟩, hpR⟩
  exact sd_spec_gen rs1 rs2 v_addr v_data v offset addr hvalid R hR s hPR' hpc

-- ============================================================================
-- ALU specs (rd = rs1 case, most common in EVM programs)
-- ============================================================================

@[spec_gen_rv64] theorem add_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .ADD rd rd rs2) ** (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((addr ↦ᵢ .ADD rd rd rs2) ** (rd ↦ᵣ (v1 + v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.ADD rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem sub_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SUB rd rd rs2) ** (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((addr ↦ᵢ .SUB rd rd rs2) ** (rd ↦ᵣ (v1 - v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.SUB rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem and_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .AND rd rd rs2) ** (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((addr ↦ᵢ .AND rd rd rs2) ** (rd ↦ᵣ (v1 &&& v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.AND rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem or_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .OR rd rd rs2) ** (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((addr ↦ᵢ .OR rd rd rs2) ** (rd ↦ᵣ (v1 ||| v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.OR rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem xor_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .XOR rd rd rs2) ** (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((addr ↦ᵢ .XOR rd rd rs2) ** (rd ↦ᵣ (v1 ^^^ v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.XOR rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem sltu_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SLTU rd rd rs2) ** (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((addr ↦ᵢ .SLTU rd rd rs2) ** (rd ↦ᵣ (if BitVec.ult v1 v2 then (1 : Word) else 0)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.SLTU rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem srl_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SRL rd rd rs2) ** (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((addr ↦ᵢ .SRL rd rd rs2) ** (rd ↦ᵣ (v1 >>> (v2.toNat % 64))) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.SRL rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem sll_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SLL rd rd rs2) ** (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((addr ↦ᵢ .SLL rd rd rs2) ** (rd ↦ᵣ (v1 <<< (v2.toNat % 64))) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.SLL rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem sra_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SRA rd rd rs2) ** (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((addr ↦ᵢ .SRA rd rd rs2) ** (rd ↦ᵣ (BitVec.sshiftRight v1 (v2.toNat % 64))) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.SRA rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

-- ============================================================================
-- Immediate specs
-- ============================================================================

@[spec_gen_rv64] theorem addi_spec_gen_same (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .ADDI rd rd imm) ** (rd ↦ᵣ v))
      ((addr ↦ᵢ .ADDI rd rd imm) ** (rd ↦ᵣ (v + signExtend12 imm))) :=
  generic_1reg_spec (.ADDI rd rd imm) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem addi_spec_gen (rd rs1 : Reg) (v_old v1 : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .ADDI rd rs1 imm) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((addr ↦ᵢ .ADDI rd rs1 imm) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + signExtend12 imm))) :=
  generic_2reg_spec (.ADDI rd rs1 imm) rs1 rd v1 v_old (v1 + signExtend12 imm) addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem xori_spec_gen_same (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .XORI rd rd imm) ** (rd ↦ᵣ v))
      ((addr ↦ᵢ .XORI rd rd imm) ** (rd ↦ᵣ (v ^^^ signExtend12 imm))) :=
  generic_1reg_spec (.XORI rd rd imm) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem andi_spec_gen (rd rs1 : Reg) (v_old v1 : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .ANDI rd rs1 imm) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((addr ↦ᵢ .ANDI rd rs1 imm) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 &&& signExtend12 imm))) :=
  generic_2reg_spec (.ANDI rd rs1 imm) rs1 rd v1 v_old (v1 &&& signExtend12 imm) addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem andi_spec_gen_same (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .ANDI rd rd imm) ** (rd ↦ᵣ v))
      ((addr ↦ᵢ .ANDI rd rd imm) ** (rd ↦ᵣ (v &&& signExtend12 imm))) :=
  generic_1reg_spec (.ANDI rd rd imm) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem sltiu_spec_gen_same (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SLTIU rd rd imm) ** (rd ↦ᵣ v))
      ((addr ↦ᵢ .SLTIU rd rd imm) ** (rd ↦ᵣ (if BitVec.ult v (signExtend12 imm) then (1 : Word) else (0 : Word)))) :=
  generic_1reg_spec (.SLTIU rd rd imm) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem slli_spec_gen_same (rd : Reg) (v : Word) (shamt : BitVec 6)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SLLI rd rd shamt) ** (rd ↦ᵣ v))
      ((addr ↦ᵢ .SLLI rd rd shamt) ** (rd ↦ᵣ (v <<< shamt.toNat))) :=
  generic_1reg_spec (.SLLI rd rd shamt) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem srli_spec_gen_same (rd : Reg) (v : Word) (shamt : BitVec 6)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SRLI rd rd shamt) ** (rd ↦ᵣ v))
      ((addr ↦ᵢ .SRLI rd rd shamt) ** (rd ↦ᵣ (v >>> shamt.toNat))) :=
  generic_1reg_spec (.SRLI rd rd shamt) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem srai_spec_gen_same (rd : Reg) (v : Word) (shamt : BitVec 6)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SRAI rd rd shamt) ** (rd ↦ᵣ v))
      ((addr ↦ᵢ .SRAI rd rd shamt) ** (rd ↦ᵣ (BitVec.sshiftRight v shamt.toNat))) :=
  generic_1reg_spec (.SRAI rd rd shamt) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem srai_spec_gen (rd rs1 : Reg) (v_old v1 : Word) (shamt : BitVec 6)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SRAI rd rs1 shamt) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((addr ↦ᵢ .SRAI rd rs1 shamt) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (BitVec.sshiftRight v1 shamt.toNat))) :=
  generic_2reg_spec (.SRAI rd rs1 shamt) rs1 rd v1 v_old (BitVec.sshiftRight v1 shamt.toNat) addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

-- ============================================================================
-- Pseudo instructions
-- ============================================================================

@[spec_gen_rv64] theorem li_spec_gen (rd : Reg) (v_old imm : Word) (addr : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .LI rd imm) ** (rd ↦ᵣ v_old))
      ((addr ↦ᵢ .LI rd imm) ** (rd ↦ᵣ imm)) :=
  generic_1reg_spec (.LI rd imm) rd v_old _ addr hrd_ne_x0
    (by intro s _ _; simp [execInstrBr])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem li_spec_gen_own (rd : Reg) (imm : Word) (addr : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .LI rd imm) ** regOwn rd)
      ((addr ↦ᵢ .LI rd imm) ** (rd ↦ᵣ imm)) := by
  intro R hR s hPR hpc
  obtain ⟨h, hcompat, hPQ, hR_ps, hdisj, hunion, hpq, hrR⟩ := hPR
  obtain ⟨hI, hOwn, hdisjI, hunionI, hpI, hpOwn⟩ := hpq
  obtain ⟨v, hv⟩ := hpOwn
  have hPR' : (((addr ↦ᵢ .LI rd imm) ** (rd ↦ᵣ v)) ** R).holdsFor s :=
    ⟨h, hcompat, hPQ, hR_ps, hdisj, hunion, ⟨hI, hOwn, hdisjI, hunionI, hpI, hv⟩, hrR⟩
  exact li_spec_gen rd v imm addr hrd_ne_x0 R hR s hPR' hpc

@[spec_gen_rv64] theorem mv_spec_gen (rd rs : Reg) (v v_old : Word) (addr : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .MV rd rs) ** (rs ↦ᵣ v) ** (rd ↦ᵣ v_old))
      ((addr ↦ᵢ .MV rd rs) ** (rs ↦ᵣ v) ** (rd ↦ᵣ v)) :=
  generic_2reg_spec (.MV rd rs) rs rd v v_old v addr hrd_ne_x0
    (by intro s _ hrs _; simp [execInstrBr, hrs])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

-- ============================================================================
-- Branch/Jump specs
-- ============================================================================

@[spec_gen_rv64] theorem bne_spec_gen (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word)
    (addr : Addr) :
    cpsBranch addr
      ((addr ↦ᵢ .BNE rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (addr + signExtend13 offset)
        ((addr ↦ᵢ .BNE rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝)
      (addr + 4)
        ((addr ↦ᵢ .BNE rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝) :=
  generic_bne_spec rs1 rs2 offset v1 v2 addr

@[spec_gen_rv64] theorem beq_spec_gen (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word)
    (addr : Addr) :
    cpsBranch addr
      ((addr ↦ᵢ .BEQ rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (addr + signExtend13 offset)
        ((addr ↦ᵢ .BEQ rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝)
      (addr + 4)
        ((addr ↦ᵢ .BEQ rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝) :=
  generic_beq_spec rs1 rs2 offset v1 v2 addr

-- ============================================================================
-- ECALL halt spec
-- ============================================================================

@[spec_gen_rv64] theorem ecall_halt_spec_gen (exitCode : Word) (addr : Addr) :
    cpsHaltTriple addr
      ((addr ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode))
      ((addr ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) := by
  intro R hR s hPR hpc; subst hpc
  have hfetch : s.code s.pc = some .ECALL :=
    (holdsFor_instrAt _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hx5 : s.getReg .x5 = (0 : Word) :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  refine ⟨0, s, rfl, ?_, hPR⟩
  simp only [isHalted, step_ecall_halt s hfetch hx5, Option.isNone]

-- ============================================================================
-- 3-register ALU specs (all distinct)
-- ============================================================================

@[spec_gen_rv64] theorem slt_spec_gen (rd rs1 rs2 : Reg) (v_old v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SLT rd rs1 rs2) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ v_old))
      ((addr ↦ᵢ .SLT rd rs1 rs2) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (if BitVec.slt v1 v2 then (1 : Word) else 0))) :=
  generic_3reg_spec (.SLT rd rs1 rs2) rs1 rs2 rd v1 v2 v_old _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem sltu_spec_gen (rd rs1 rs2 : Reg) (v_old v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SLTU rd rs1 rs2) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ v_old))
      ((addr ↦ᵢ .SLTU rd rs1 rs2) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (if BitVec.ult v1 v2 then (1 : Word) else 0))) :=
  generic_3reg_spec (.SLTU rd rs1 rs2) rs1 rs2 rd v1 v2 v_old _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem or_spec_gen (rd rs1 rs2 : Reg) (v_old v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .OR rd rs1 rs2) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ v_old))
      ((addr ↦ᵢ .OR rd rs1 rs2) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 ||| v2))) :=
  generic_3reg_spec (.OR rd rs1 rs2) rs1 rs2 rd v1 v2 v_old _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem sub_spec_gen_rd_eq_rs2 (rd rs1 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rs1 ≠ rd) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SUB rd rs1 rd) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v2))
      ((addr ↦ᵢ .SUB rd rs1 rd) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 - v2))) :=
  generic_2reg_spec (.SUB rd rs1 rd) rs1 rd v1 v2 (v1 - v2) addr hrd_ne_x0
    (by intro s _ hrs1 hrd; simp [execInstrBr, hrs1, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

@[spec_gen_rv64] theorem sltiu_spec_gen (rd rs1 : Reg) (v_old v1 : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SLTIU rd rs1 imm) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((addr ↦ᵢ .SLTIU rd rs1 imm) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (if BitVec.ult v1 (signExtend12 imm) then (1 : Word) else (0 : Word)))) :=
  generic_2reg_spec (.SLTIU rd rs1 imm) rs1 rd v1 v_old _ addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SD rs1 x0 offset: mem[rs1 + sext(offset)] := 0.
    Specialized version of sd_spec_gen for x0 (always reads as 0).
    Does not require (x0 ↦ᵣ 0) in pre/post. -/
@[spec_gen_rv64] theorem sd_x0_spec_gen (rs1 : Reg) (v_addr mem_old : Word)
    (offset : BitVec 12) (addr : Addr)
    (hvalid : isValidDwordAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SD rs1 .x0 offset) ** (rs1 ↦ᵣ v_addr) ** ((v_addr + signExtend12 offset) ↦ₘ mem_old))
      ((addr ↦ᵢ .SD rs1 .x0 offset) ** (rs1 ↦ᵣ v_addr) ** ((v_addr + signExtend12 offset) ↦ₘ (0 : Word))) :=
  generic_sd_x0_spec rs1 v_addr mem_old offset addr hvalid

end EvmAsm.Rv64
