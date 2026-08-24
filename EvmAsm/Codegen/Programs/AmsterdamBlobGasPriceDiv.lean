/-
  EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceDiv

  The 19-instruction restoring-division block of
  `amsterdam_blob_gas_price_u256` (issue #12346, item 7), verified once and
  instantiated at its two linked sites (loop division at `PriceK + 720`,
  final division at `PriceK + 824`).

  The block divides a 384-bit little-endian buffer by a u64 divisor in
  place: six limbs from the most significant down, 64 restoring bit-steps
  per limb.  `divBitState`, `div_bititer`, `div_bittail`, `div_bitloop`,
  `div_limb_iter`, `div_limbloop`, and finally `div_block_spec` give the
  whole block: from `x5 = d`, `x6 = rem`, `x30 = buf + 40`, `x31 = 6` to the
  quotient limbs written back and `x6` holding the final remainder.

  Also home to the small `x0`-source spec variants the routine needs
  (the shared generic specs require ownership of both source registers;
  `priceEntryRest` deliberately does not carry an `x0` atom).
-/

import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceMem
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock

set_option maxRecDepth 8000

namespace EvmAsm.Codegen.AmsterdamBlobGasPrice

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec

/-! ## `x0`-source spec variants -/

/-- `BNE rs, x0` without an `x0` atom (`getReg x0 = 0` definitionally). -/
theorem bne_x0_spec_within (rs1 : Reg) (offset : BitVec 13) (v1 : Word) (base : Word) :
    cpsBranchWithin 1 base (CodeReq.singleton base (.BNE rs1 .x0 offset))
      (rs1 ↦ᵣ v1)
      (base + signExtend13 offset) ((rs1 ↦ᵣ v1) ** ⌜v1 ≠ 0⌝)
      (base + 4) ((rs1 ↦ᵣ v1) ** ⌜v1 = 0⌝) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BNE rs1 .x0 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v1 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hPR)
  have hstep' : step s = some (execInstrBr s (.BNE rs1 .x0 offset)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  by_cases heq : v1 = 0
  · have hexec' : execInstrBr s (.BNE rs1 .x0 offset) = s.setPC (s.pc + 4) := by
      simp only [execInstrBr, hrs1]
      rw [show s.getReg .x0 = (0 : Word) from rfl]
      rw [show (v1 != (0 : Word)) = false from
        Bool.eq_false_iff.mpr (by simp [bne_iff_ne, beq_iff_eq, heq]),
        if_neg (by decide : ¬ (false = true))]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + 4), ?_, Or.inr ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : ((rs1 ↦ᵣ v1) ** R).pcFree := pcFree_sepConj pcFree_regIs hR
      have hPR' := holdsFor_pcFree_setPC hpc_free (v := s.pc + 4) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hRs1, hR2⟩ := hPR'
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        (sepConj_pure_right h1).mpr ⟨hRs1, heq⟩, hR2⟩
  · have hexec' : execInstrBr s (.BNE rs1 .x0 offset) =
        s.setPC (s.pc + signExtend13 offset) := by
      simp only [execInstrBr, hrs1]
      rw [show s.getReg .x0 = (0 : Word) from rfl]
      rw [show (v1 != (0 : Word)) = true from bne_iff_ne.mpr heq,
        if_pos rfl]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + signExtend13 offset), ?_, Or.inl ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : ((rs1 ↦ᵣ v1) ** R).pcFree := pcFree_sepConj pcFree_regIs hR
      have hPR' := holdsFor_pcFree_setPC hpc_free (v := s.pc + signExtend13 offset) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hRs1, hR2⟩ := hPR'
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        (sepConj_pure_right h1).mpr ⟨hRs1, heq⟩, hR2⟩

/-- `BEQ rs, x0` without an `x0` atom. -/
theorem beq_x0_spec_within (rs1 : Reg) (offset : BitVec 13) (v1 : Word) (base : Word) :
    cpsBranchWithin 1 base (CodeReq.singleton base (.BEQ rs1 .x0 offset))
      (rs1 ↦ᵣ v1)
      (base + signExtend13 offset) ((rs1 ↦ᵣ v1) ** ⌜v1 = 0⌝)
      (base + 4) ((rs1 ↦ᵣ v1) ** ⌜v1 ≠ 0⌝) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BEQ rs1 .x0 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v1 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hPR)
  have hstep' : step s = some (execInstrBr s (.BEQ rs1 .x0 offset)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  by_cases heq : v1 = 0
  · have hexec' : execInstrBr s (.BEQ rs1 .x0 offset) =
        s.setPC (s.pc + signExtend13 offset) := by
      simp only [execInstrBr, hrs1]
      rw [show s.getReg .x0 = (0 : Word) from rfl]
      rw [show (v1 == (0 : Word)) = true from beq_iff_eq.mpr heq,
        if_pos rfl]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + signExtend13 offset), ?_,
      Or.inl ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : ((rs1 ↦ᵣ v1) ** R).pcFree := pcFree_sepConj pcFree_regIs hR
      have hPR' := holdsFor_pcFree_setPC hpc_free (v := s.pc + signExtend13 offset) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hRs1, hR2⟩ := hPR'
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        (sepConj_pure_right h1).mpr ⟨hRs1, heq⟩, hR2⟩
  · have hexec' : execInstrBr s (.BEQ rs1 .x0 offset) = s.setPC (s.pc + 4) := by
      simp only [execInstrBr, hrs1]
      rw [show s.getReg .x0 = (0 : Word) from rfl]
      have hfalse : (v1 == (0 : Word)) = false := by
        apply Bool.eq_false_iff.mpr
        show ¬((v1 == (0 : Word)) = true)
        rw [beq_iff_eq]
        exact heq
      rw [hfalse, if_neg (by decide : ¬ (false = true))]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + 4), ?_, Or.inr ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : ((rs1 ↦ᵣ v1) ** R).pcFree := pcFree_sepConj pcFree_regIs hR
      have hPR' := holdsFor_pcFree_setPC hpc_free (v := s.pc + 4) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hRs1, hR2⟩ := hPR'
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        (sepConj_pure_right h1).mpr ⟨hRs1, heq⟩, hR2⟩

/-- `BLT rs, x0` without an `x0` atom. -/
theorem blt_x0_spec_within (rs1 : Reg) (offset : BitVec 13) (v1 : Word) (base : Word) :
    cpsBranchWithin 1 base (CodeReq.singleton base (.BLT rs1 .x0 offset))
      (rs1 ↦ᵣ v1)
      (base + signExtend13 offset) ((rs1 ↦ᵣ v1) ** ⌜BitVec.slt v1 0⌝)
      (base + 4) ((rs1 ↦ᵣ v1) ** ⌜¬ BitVec.slt v1 0⌝) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BLT rs1 .x0 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v1 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hPR)
  have hstep' : step s = some (execInstrBr s (.BLT rs1 .x0 offset)) :=
    step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  by_cases heq : BitVec.slt v1 (0 : Word)
  · have hexec' : execInstrBr s (.BLT rs1 .x0 offset) =
        s.setPC (s.pc + signExtend13 offset) := by
      simp only [execInstrBr, hrs1]
      rw [show s.getReg .x0 = (0 : Word) from rfl, heq, if_pos rfl]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + signExtend13 offset), ?_,
      Or.inl ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : ((rs1 ↦ᵣ v1) ** R).pcFree := pcFree_sepConj pcFree_regIs hR
      have hPR' := holdsFor_pcFree_setPC hpc_free (v := s.pc + signExtend13 offset) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hRs1, hR2⟩ := hPR'
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        (sepConj_pure_right h1).mpr ⟨hRs1, heq⟩, hR2⟩
  · have hexec' : execInstrBr s (.BLT rs1 .x0 offset) = s.setPC (s.pc + 4) := by
      simp only [execInstrBr, hrs1]
      rw [show s.getReg .x0 = (0 : Word) from rfl, if_neg heq]
    refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + 4), ?_, Or.inr ⟨rfl, ?_⟩⟩
    · show (step s).bind (stepN 0) = some _
      rw [hstep', hexec']; rfl
    · have hpc_free : ((rs1 ↦ᵣ v1) ** R).pcFree := pcFree_sepConj pcFree_regIs hR
      have hPR' := holdsFor_pcFree_setPC hpc_free (v := s.pc + 4) hPR
      obtain ⟨hp, hcompat, h1, h2, hd, hu, hRs1, hR2⟩ := hPR'
      exact ⟨hp, hcompat, h1, h2, hd, hu,
        (sepConj_pure_right h1).mpr ⟨hRs1, heq⟩, hR2⟩

/-- `MV rd, x0` without an `x0` atom. -/
theorem mv_x0_spec_within (rd : Reg) (vOld : Word) (addr : Word) (hrd : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.MV rd .x0))
      (rd ↦ᵣ vOld) (rd ↦ᵣ (0 : Word)) :=
  generic_1reg_spec_within (.MV rd .x0) rd vOld (0 : Word) addr hrd
    (by intro s _ hrs; simp [execInstrBr, MachineState.getReg])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))

/-- Signed-negativity of a word is its most significant bit. -/
theorem slt_zero_iff_msb (x : Word) : BitVec.slt x (0 : Word) = x.msb := by
  apply Bool.eq_iff_iff.mpr
  rw [msb_iff_toNat, BitVec.slt_eq_decide, BitVec.toInt_eq_toNat_bmod]
  have h0 : ((0 : Word)).toInt = 0 := by decide
  rw [h0]
  simp only [decide_eq_true_eq, Int.bmod]
  have hlt : x.toNat < 2 ^ 64 := x.isLt
  omega

/-! ## The division block program -/

/-- The 19-instruction restoring-division block (identical at both sites). -/
def divBlockProg : Program :=
  [ .LD .x7 .x30 (0 : BitVec 12),
    .LI .x28 (0 : Word),
    .LI .x29 (64 : Word),
    .SLLI .x6 .x6 (1 : BitVec 6),
    .BLT .x7 .x0 (12 : BitVec 13),
    .SLLI .x7 .x7 (1 : BitVec 6),
    .JAL .x0 (12 : BitVec 21),
    .SLLI .x7 .x7 (1 : BitVec 6),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SLLI .x28 .x28 (1 : BitVec 6),
    .BLTU .x6 .x5 (12 : BitVec 13),
    .SUB .x6 .x6 .x5,
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .BNE .x29 .x0 (-44 : BitVec 13),
    .SD .x30 .x28 (0 : BitVec 12),
    .ADDI .x30 .x30 (-8 : BitVec 12),
    .ADDI .x31 .x31 (-1 : BitVec 12),
    .BNE .x31 .x0 (-72 : BitVec 13) ]

theorem divBlockProg_length : divBlockProg.length = 19 := rfl

theorem priceProg_length : amsterdamBlobGasPriceU256_prog.length = 252 := by decide

/-- The loop site (instructions 180..198 of the routine). -/
theorem divBlock_slice_loop :
    (amsterdamBlobGasPriceU256_prog.drop 180 |>.take 19) = divBlockProg := by
  decide

/-- The final-division site (instructions 206..224). -/
theorem divBlock_slice_final :
    (amsterdamBlobGasPriceU256_prog.drop 206 |>.take 19) = divBlockProg := by
  decide

/-- Lift block code into the full linked requirement at a slice site. -/
theorem divBlock_code_mono (idx : Nat)
    (hslice : (amsterdamBlobGasPriceU256_prog.drop idx |>.take 19) = divBlockProg)
    (hlen : (amsterdamBlobGasPriceU256_prog.take idx).length = idx)
    (hbound : 4 * amsterdamBlobGasPriceU256_prog.length < 2 ^ 64)
    (a : Word) (i : Instr)
    (hm : CodeReq.ofProg (PriceK + BitVec.ofNat 64 (4 * idx)) divBlockProg a = some i) :
    priceCode a = some i := by
  have hpre1 : amsterdamBlobGasPriceU256_prog =
      amsterdamBlobGasPriceU256_prog.take idx ++
        amsterdamBlobGasPriceU256_prog.drop idx :=
    (List.take_append_drop idx amsterdamBlobGasPriceU256_prog).symm
  have hpre2 : amsterdamBlobGasPriceU256_prog.drop idx =
      (amsterdamBlobGasPriceU256_prog.drop idx).take 19 ++
        amsterdamBlobGasPriceU256_prog.drop (idx + 19) := by
    rw [show amsterdamBlobGasPriceU256_prog.drop (idx + 19) =
        (amsterdamBlobGasPriceU256_prog.drop idx).drop 19 from
      (List.drop_drop (i := 19) (j := idx)).symm]
    exact (List.take_append_drop 19 (amsterdamBlobGasPriceU256_prog.drop idx)).symm
  have hpre : amsterdamBlobGasPriceU256_prog =
      amsterdamBlobGasPriceU256_prog.take idx ++ divBlockProg ++
        amsterdamBlobGasPriceU256_prog.drop (idx + 19) := by
    calc amsterdamBlobGasPriceU256_prog
        = amsterdamBlobGasPriceU256_prog.take idx ++
            amsterdamBlobGasPriceU256_prog.drop idx := hpre1
      _ = amsterdamBlobGasPriceU256_prog.take idx ++ divBlockProg ++
            amsterdamBlobGasPriceU256_prog.drop (idx + 19) := by
          conv_lhs => rw [hpre2, hslice]
          rw [← List.append_assoc]
  have hbound' : 4 * (amsterdamBlobGasPriceU256_prog.take idx ++ divBlockProg ++
      amsterdamBlobGasPriceU256_prog.drop (idx + 19)).length < 2 ^ 64 := by
    rw [← hpre]
    exact hbound
  rw [← hlen] at hm
  show CodeReq.ofProg PriceK amsterdamBlobGasPriceU256_prog a = some i
  rw [hpre]
  exact CodeReq.ofProg_mono_subrange PriceK
    (amsterdamBlobGasPriceU256_prog.take idx) divBlockProg
    (amsterdamBlobGasPriceU256_prog.drop (idx + 19)) hbound' a i hm

/-- `divBlockProg` code at `b` lifts to the loop site. -/
theorem divBlock_code_mono_loop (b : Word) (hb : b = PriceK + 720)
    (a : Word) (i : Instr)
    (hm : CodeReq.ofProg b divBlockProg a = some i) :
    priceCode a = some i := by
  subst hb
  have h720 : (720 : Word) = BitVec.ofNat 64 (4 * 180) := by decide
  rw [h720] at hm
  exact divBlock_code_mono 180 divBlock_slice_loop (by decide) (by decide) a i hm

/-- `divBlockProg` code at `b` lifts to the final-division site. -/
theorem divBlock_code_mono_final (b : Word) (hb : b = PriceK + 824)
    (a : Word) (i : Instr)
    (hm : CodeReq.ofProg b divBlockProg a = some i) :
    priceCode a = some i := by
  subst hb
  have h824 : (824 : Word) = BitVec.ofNat 64 (4 * 206) := by decide
  rw [h824] at hm
  exact divBlock_code_mono 206 divBlock_slice_final (by decide) (by decide) a i hm

/-! ## The bit loop -/

/-- Register state of the division bit loop. -/
abbrev divBitState (d r w q cnt : Word) : Assertion :=
  (.x5 ↦ᵣ d) ** (.x6 ↦ᵣ r) ** (.x7 ↦ᵣ w) ** (.x28 ↦ᵣ q) ** (.x29 ↦ᵣ cnt)

/-- Registers owned but untouched by the bit loop. -/
abbrev divBitFrame : Assertion :=
  regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))

theorem divBitFrame_pcFree : divBitFrame.pcFree := by
  dsimp [divBitFrame]
  pcf

/-- `BitVec.ofNat` successor decrement as a word identity. -/
theorem ofNat_succ_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
  bv_omega

/-- The shared tail of a bit-loop iteration (instructions 9..14): quotient
    shift, the compare-and-subtract, counter decrement, and the back-edge. -/
theorem div_bittail (b : Word) (d r1v w1 q : Word) (n : Nat) :
    cpsBranchWithin 6 (b + 36) (CodeReq.ofProg b divBlockProg)
      (divBitState d r1v w1 q (BitVec.ofNat 64 (n + 1)) ** divBitFrame)
      (b + 12)
      ((divBitState d (if BitVec.ule d r1v then r1v - d else r1v) w1
        (if BitVec.ule d r1v then (q <<< (1 : Nat)) + 1 else q <<< (1 : Nat))
        (BitVec.ofNat 64 n)) ** divBitFrame ** ⌜BitVec.ofNat 64 n ≠ (0 : Word)⌝)
      (b + 60)
      ((divBitState d (if BitVec.ule d r1v then r1v - d else r1v) w1
        (if BitVec.ule d r1v then (q <<< (1 : Nat)) + 1 else q <<< (1 : Nat))
        (BitVec.ofNat 64 n)) ** divBitFrame ** ⌜BitVec.ofNat 64 n = (0 : Word)⌝) := by
  have s1 := slli_spec_gen_same_within .x28 q (1 : BitVec 6) (b + 36) (by nofun)
  rw [show (1 : BitVec 6).toNat = 1 from by decide,
    show b + 36 + 4 = b + 40 from by bv_omega] at s1
  have s1C := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr b divBlockProg 9 (b + 36)
      (by rw [divBlockProg_length]; decide) (by rw [divBlockProg_length]; decide)
      (by bv_omega)))
    (cpsTripleWithin_frameR
      ((.x5 ↦ᵣ d) ** (.x6 ↦ᵣ r1v) ** (.x7 ↦ᵣ w1) **
        (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)
      (by dsimp [divBitFrame]; pcf) s1)
  have hb := bltu_spec_gen_within .x6 .x5 (12 : BitVec 13) r1v d (b + 40)
  rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide,
    show (b + 40) + (12 : Word) = b + 52 from by bv_omega,
    show b + 40 + 4 = b + 44 from by bv_omega] at hb
  have hbC := cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr b divBlockProg 10 (b + 40)
      (by rw [divBlockProg_length]; decide) (by rw [divBlockProg_length]; decide)
      (by bv_omega)))
    (cpsBranchWithin_frameR
      ((.x28 ↦ᵣ (q <<< (1 : Nat))) ** (.x7 ↦ᵣ w1) **
        (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)
      (by dsimp [divBitFrame]; pcf) hb)
  have hseq := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (Q1 := ((.x28 ↦ᵣ (q <<< (1 : Nat))) ** ((.x5 ↦ᵣ d) ** (.x6 ↦ᵣ r1v) **
      (.x7 ↦ᵣ w1) ** (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)))
    (Q2 := (((.x6 ↦ᵣ r1v) ** (.x5 ↦ᵣ d)) ** ((.x28 ↦ᵣ (q <<< (1 : Nat))) **
      (.x7 ↦ᵣ w1) ** (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)))
    (by intro h hp; xperm_hyp hp) s1C hbC
  have s5 := addi_spec_gen_same_within .x29 (BitVec.ofNat 64 (n + 1)) (-1 : BitVec 12)
    (b + 52) (by nofun)
  rw [ofNat_succ_sub_one n, show b + 52 + 4 = b + 56 from by bv_omega] at s5
  have hb2 := bne_x0_spec_within .x29 (-44 : BitVec 13) (BitVec.ofNat 64 n) (b + 56)
  rw [show signExtend13 (-44 : BitVec 13) = (-44 : Word) from by decide,
    show (b + 56) + (-44 : Word) = b + 12 from by bv_omega,
    show b + 56 + 4 = b + 60 from by bv_omega] at hb2
  by_cases hule : BitVec.ule d r1v
  · have hnult : ¬ BitVec.ult r1v d := by
      rw [BitVec.ult_iff_toNat_lt]
      have h := BitVec.ule_iff_toNat_le.mp hule
      omega
    have hnt := cpsBranchWithin_ntakenPath hseq (fun hp hQt => by
      obtain ⟨h1, h2, hd, hu, hHEAD, hF⟩ := hQt
      obtain ⟨h1a, h1b, hd1, hu1, hx6, hrest⟩ := hHEAD
      obtain ⟨h1c, h1d, hd2, hu2, hx5, hpure⟩ := hrest
      exact hnult hpure.2)
    have hntS := cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => sepConj_mono_left sepConj_strip_pure_end2 _ hq) hnt
    have s3C := cpsTripleWithin_extend_code
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr b divBlockProg 11 (b + 44)
        (by rw [divBlockProg_length]; decide) (by rw [divBlockProg_length]; decide)
        (by bv_omega)))
      (cpsTripleWithin_frameR
        ((.x28 ↦ᵣ (q <<< (1 : Nat))) ** (.x7 ↦ᵣ w1) **
          (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)
        (by dsimp [divBitFrame]; pcf)
        (by
          have s3 := sub_spec_gen_rd_eq_rs1_within .x6 .x5 r1v d (b + 44) (by nofun)
          rw [show b + 44 + 4 = b + 48 from by bv_omega] at s3
          exact s3))
    have s4C := cpsTripleWithin_extend_code
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr b divBlockProg 12 (b + 48)
        (by rw [divBlockProg_length]; decide) (by rw [divBlockProg_length]; decide)
        (by bv_omega)))
      (cpsTripleWithin_frameR
        ((.x6 ↦ᵣ (r1v - d)) ** (.x5 ↦ᵣ d) ** (.x7 ↦ᵣ w1) **
          (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)
        (by dsimp [divBitFrame]; pcf)
        (by
          have s4 := addi_spec_gen_same_within .x28 (q <<< (1 : Nat)) (1 : BitVec 12)
            (b + 48) (by nofun)
          rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
            show b + 48 + 4 = b + 52 from by bv_omega] at s4
          exact s4))
    have s34 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s3C s4C
    have s5C := cpsTripleWithin_extend_code
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr b divBlockProg 13 (b + 52)
        (by rw [divBlockProg_length]; decide) (by rw [divBlockProg_length]; decide)
        (by bv_omega)))
      (cpsTripleWithin_frameR
        ((.x6 ↦ᵣ (r1v - d)) ** (.x5 ↦ᵣ d) ** (.x28 ↦ᵣ ((q <<< (1 : Nat)) + 1)) **
          (.x7 ↦ᵣ w1) ** divBitFrame)
        (by dsimp [divBitFrame]; pcf) s5)
    have s345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s34 s5C
    have htail := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hntS s345
    have hb2C := cpsBranchWithin_extend_code
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr b divBlockProg 14 (b + 56)
        (by rw [divBlockProg_length]; decide) (by rw [divBlockProg_length]; decide)
        (by bv_omega)))
      (cpsBranchWithin_frameR
        ((.x6 ↦ᵣ (r1v - d)) ** (.x5 ↦ᵣ d) ** (.x28 ↦ᵣ ((q <<< (1 : Nat)) + 1)) **
          (.x7 ↦ᵣ w1) ** divBitFrame)
        (by dsimp [divBitFrame]; pcf) hb2)
    have hfin := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (by intro h hp; xperm_hyp hp) htail hb2C
    refine cpsBranchWithin_weaken
      (P := ((.x28 ↦ᵣ q) ** ((.x5 ↦ᵣ d) ** (.x6 ↦ᵣ r1v) ** (.x7 ↦ᵣ w1) **
        (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)))
      (fun _ hp => by xperm_hyp hp) ?_ ?_ hfin
    · intro h hq
      have hx6 : (if BitVec.ule d r1v then r1v - d else r1v) = r1v - d := if_pos hule
      have hx28 : (if BitVec.ule d r1v then (q <<< (1 : Nat)) + 1 else q <<< (1 : Nat)) =
          (q <<< (1 : Nat)) + 1 := if_pos hule
      rw [hx6, hx28]
      xperm_hyp hq
    · intro h hq
      have hx6 : (if BitVec.ule d r1v then r1v - d else r1v) = r1v - d := if_pos hule
      have hx28 : (if BitVec.ule d r1v then (q <<< (1 : Nat)) + 1 else q <<< (1 : Nat)) =
          (q <<< (1 : Nat)) + 1 := if_pos hule
      rw [hx6, hx28]
      xperm_hyp hq
  · have hult : BitVec.ult r1v d := by
      rw [BitVec.ult_iff_toNat_lt]
      have h := BitVec.ule_iff_toNat_le.not.mp hule
      omega
    have ht := cpsBranchWithin_takenPath hseq (fun hp hQf => by
      obtain ⟨h1, h2, hd, hu, hHEAD, hF⟩ := hQf
      obtain ⟨h1a, h1b, hd1, hu1, hx6, hrest⟩ := hHEAD
      obtain ⟨h1c, h1d, hd2, hu2, hx5, hpure⟩ := hrest
      exact hpure.2 hult)
    have htS := cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => sepConj_mono_left sepConj_strip_pure_end2 _ hq) ht
    have s5C := cpsTripleWithin_extend_code
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr b divBlockProg 13 (b + 52)
        (by rw [divBlockProg_length]; decide) (by rw [divBlockProg_length]; decide)
        (by bv_omega)))
      (cpsTripleWithin_frameR
        ((.x6 ↦ᵣ r1v) ** (.x5 ↦ᵣ d) ** (.x28 ↦ᵣ (q <<< (1 : Nat))) **
          (.x7 ↦ᵣ w1) ** divBitFrame)
        (by dsimp [divBitFrame]; pcf) s5)
    have htail := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) htS s5C
    have hb2C := cpsBranchWithin_extend_code
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr b divBlockProg 14 (b + 56)
        (by rw [divBlockProg_length]; decide) (by rw [divBlockProg_length]; decide)
        (by bv_omega)))
      (cpsBranchWithin_frameR
        ((.x6 ↦ᵣ r1v) ** (.x5 ↦ᵣ d) ** (.x28 ↦ᵣ (q <<< (1 : Nat))) **
          (.x7 ↦ᵣ w1) ** divBitFrame)
        (by dsimp [divBitFrame]; pcf) hb2)
    have hfin := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (by intro h hp; xperm_hyp hp) htail hb2C
    have hfin6 := cpsBranchWithin_mono_nSteps (by decide : 1 + 1 + 1 + 1 ≤ 6) hfin
    refine cpsBranchWithin_weaken
      (P := ((.x28 ↦ᵣ q) ** ((.x5 ↦ᵣ d) ** (.x6 ↦ᵣ r1v) ** (.x7 ↦ᵣ w1) **
        (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)))
      (fun _ hp => by xperm_hyp hp) ?_ ?_ hfin6
    · intro h hq
      have hx6 : (if BitVec.ule d r1v then r1v - d else r1v) = r1v := if_neg hule
      have hx28 : (if BitVec.ule d r1v then (q <<< (1 : Nat)) + 1 else q <<< (1 : Nat)) =
          q <<< (1 : Nat) := if_neg hule
      rw [hx6, hx28]
      xperm_hyp hq
    · intro h hq
      have hx6 : (if BitVec.ule d r1v then r1v - d else r1v) = r1v := if_neg hule
      have hx28 : (if BitVec.ule d r1v then (q <<< (1 : Nat)) + 1 else q <<< (1 : Nat)) =
          q <<< (1 : Nat) := if_neg hule
      rw [hx6, hx28]
      xperm_hyp hq

/-- One bit-loop iteration (instructions 3..14): from the loop head with
    counter `n + 1` to either the loop head with counter `n` (taken
    back-edge) or the exit with counter `0`. -/
theorem div_bititer (b : Word) (d r w q : Word) (n : Nat) :
    cpsBranchWithin 10 (b + 12) (CodeReq.ofProg b divBlockProg)
      (divBitState d r w q (BitVec.ofNat 64 (n + 1)) ** divBitFrame)
      (b + 12)
      ((divBitState d (divBitStep d r w q).1 (divBitStep d r w q).2.1
        (divBitStep d r w q).2.2 (BitVec.ofNat 64 n)) ** divBitFrame **
        ⌜BitVec.ofNat 64 n ≠ (0 : Word)⌝)
      (b + 60)
      ((divBitState d (divBitStep d r w q).1 (divBitStep d r w q).2.1
        (divBitStep d r w q).2.2 (BitVec.ofNat 64 n)) ** divBitFrame **
        ⌜BitVec.ofNat 64 n = (0 : Word)⌝) := by
  by_cases hmsb : w.msb
  · -- BLT taken: x7 path through idx 7, 8
    have hblt : BitVec.slt w (0 : Word) := by
      rw [slt_zero_iff_msb]
      exact hmsb
    have s1 := slli_spec_gen_same_within .x6 r (1 : BitVec 6) (b + 12) (by nofun)
    rw [show (1 : BitVec 6).toNat = 1 from by decide,
      show b + 12 + 4 = b + 16 from by bv_omega] at s1
    have s1C := cpsTripleWithin_extend_code
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr b divBlockProg 3 (b + 12)
        (by rw [divBlockProg_length]; decide) (by rw [divBlockProg_length]; decide)
        (by bv_omega)))
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ d) ** (.x7 ↦ᵣ w) ** (.x28 ↦ᵣ q) **
          (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)
        (by dsimp [divBitFrame]; pcf) s1)
    have hb := blt_x0_spec_within .x7 (12 : BitVec 13) w (b + 16)
    rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide,
      show (b + 16) + (12 : Word) = b + 28 from by bv_omega,
      show b + 16 + 4 = b + 20 from by bv_omega] at hb
    have hbC := cpsBranchWithin_extend_code
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr b divBlockProg 4 (b + 16)
        (by rw [divBlockProg_length]; decide) (by rw [divBlockProg_length]; decide)
        (by bv_omega)))
      (cpsBranchWithin_frameR
        ((.x6 ↦ᵣ (r <<< (1 : Nat))) ** (.x5 ↦ᵣ d) ** (.x28 ↦ᵣ q) **
          (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)
        (by dsimp [divBitFrame]; pcf) hb)
    have hseq := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
        (Q1 := ((.x6 ↦ᵣ (r <<< (1 : Nat))) ** ((.x5 ↦ᵣ d) ** (.x7 ↦ᵣ w) **
          (.x28 ↦ᵣ q) ** (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)))
        (Q2 := ((.x7 ↦ᵣ w) ** ((.x6 ↦ᵣ (r <<< (1 : Nat))) ** (.x5 ↦ᵣ d) **
          (.x28 ↦ᵣ q) ** (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)))
        (by intro h hp; xperm_hyp hp) s1C hbC
    have ht := cpsBranchWithin_takenPath hseq (fun hp hQf => by
      obtain ⟨h1, h2, hd, hu, hHEAD, hF⟩ := hQf
      obtain ⟨h1a, h1b, hd1, hu1, hx7, hpure⟩ := hHEAD
      have hcon : ¬ BitVec.slt w (0 : Word) := hpure.2
      exact hcon hblt)
    have htS := cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => sepConj_mono_left (fun h' hA => ((sepConj_pure_right h').1 hA).1)
        _ hq) ht
    have s2C := cpsTripleWithin_extend_code
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr b divBlockProg 7 (b + 28)
        (by rw [divBlockProg_length]; decide) (by rw [divBlockProg_length]; decide)
        (by bv_omega)))
      (cpsTripleWithin_frameR
        ((.x6 ↦ᵣ (r <<< (1 : Nat))) ** (.x5 ↦ᵣ d) ** (.x28 ↦ᵣ q) **
          (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)
        (by dsimp [divBitFrame]; pcf)
        (slli_spec_gen_same_within .x7 w (1 : BitVec 6) (b + 28) (by nofun)))
    rw [show (1 : BitVec 6).toNat = 1 from by decide,
      show b + 28 + 4 = b + 32 from by bv_omega] at s2C
    have s3C := cpsTripleWithin_extend_code
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr b divBlockProg 8 (b + 32)
        (by rw [divBlockProg_length]; decide) (by rw [divBlockProg_length]; decide)
        (by bv_omega)))
      (cpsTripleWithin_frameR
        ((.x7 ↦ᵣ (w <<< (1 : Nat))) ** (.x5 ↦ᵣ d) ** (.x28 ↦ᵣ q) **
          (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)
        (by dsimp [divBitFrame]; pcf)
        (addi_spec_gen_same_within .x6 (r <<< (1 : Nat)) (1 : BitVec 12) (b + 32)
          (by nofun)))
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
      show (r <<< (1 : Nat)) + (1 : Word) = (r <<< (1 : Nat)) + 1 from by bv_omega,
      show b + 32 + 4 = b + 36 from by bv_omega] at s3C
    have s23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2C s3C
    have hpre := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) htS s23
    have htail := div_bittail b d ((r <<< (1 : Nat)) + 1) (w <<< (1 : Nat)) q n
    have hfin := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (by intro h hp; xperm_hyp hp) hpre htail
    refine cpsBranchWithin_weaken
      (P := ((.x6 ↦ᵣ r) ** ((.x5 ↦ᵣ d) ** (.x7 ↦ᵣ w) ** (.x28 ↦ᵣ q) **
        (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)))
      (fun _ hp => by xperm_hyp hp) ?_ ?_ hfin
    · intro h hq
      have h1 : (divBitStep d r w q).1 =
          (if BitVec.ule d ((r <<< (1 : Nat)) + 1) then ((r <<< (1 : Nat)) + 1) - d
          else (r <<< (1 : Nat)) + 1) := by
        simp only [divBitStep, if_pos hmsb]
        split <;> rfl
      have h2 : (divBitStep d r w q).2.1 = w <<< (1 : Nat) := by
        simp only [divBitStep, if_pos hmsb]
        split <;> rfl
      have h3 : (divBitStep d r w q).2.2 =
          (if BitVec.ule d ((r <<< (1 : Nat)) + 1) then (q <<< (1 : Nat)) + 1
          else q <<< (1 : Nat)) := by
        simp only [divBitStep, if_pos hmsb]
        split <;> rfl
      rw [h1, h2, h3]
      xperm_hyp hq
    · intro h hq
      have h1 : (divBitStep d r w q).1 =
          (if BitVec.ule d ((r <<< (1 : Nat)) + 1) then ((r <<< (1 : Nat)) + 1) - d
          else (r <<< (1 : Nat)) + 1) := by
        simp only [divBitStep, if_pos hmsb]
        split <;> rfl
      have h2 : (divBitStep d r w q).2.1 = w <<< (1 : Nat) := by
        simp only [divBitStep, if_pos hmsb]
        split <;> rfl
      have h3 : (divBitStep d r w q).2.2 =
          (if BitVec.ule d ((r <<< (1 : Nat)) + 1) then (q <<< (1 : Nat)) + 1
          else q <<< (1 : Nat)) := by
        simp only [divBitStep, if_pos hmsb]
        split <;> rfl
      rw [h1, h2, h3]
      xperm_hyp hq
  · -- BLT not taken: x7 path through idx 5, 6
    have hblt : ¬ BitVec.slt w (0 : Word) := by
      rw [slt_zero_iff_msb]
      exact hmsb
    have s1 := slli_spec_gen_same_within .x6 r (1 : BitVec 6) (b + 12) (by nofun)
    rw [show (1 : BitVec 6).toNat = 1 from by decide,
      show b + 12 + 4 = b + 16 from by bv_omega] at s1
    have s1C := cpsTripleWithin_extend_code
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr b divBlockProg 3 (b + 12)
        (by rw [divBlockProg_length]; decide) (by rw [divBlockProg_length]; decide)
        (by bv_omega)))
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ d) ** (.x7 ↦ᵣ w) ** (.x28 ↦ᵣ q) **
          (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)
        (by dsimp [divBitFrame]; pcf) s1)
    have hb := blt_x0_spec_within .x7 (12 : BitVec 13) w (b + 16)
    rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide,
      show (b + 16) + (12 : Word) = b + 28 from by bv_omega,
      show b + 16 + 4 = b + 20 from by bv_omega] at hb
    have hbC := cpsBranchWithin_extend_code
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr b divBlockProg 4 (b + 16)
        (by rw [divBlockProg_length]; decide) (by rw [divBlockProg_length]; decide)
        (by bv_omega)))
      (cpsBranchWithin_frameR
        ((.x6 ↦ᵣ (r <<< (1 : Nat))) ** (.x5 ↦ᵣ d) ** (.x28 ↦ᵣ q) **
          (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)
        (by dsimp [divBitFrame]; pcf) hb)
    have hseq := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
        (Q1 := ((.x6 ↦ᵣ (r <<< (1 : Nat))) ** ((.x5 ↦ᵣ d) ** (.x7 ↦ᵣ w) **
          (.x28 ↦ᵣ q) ** (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)))
        (Q2 := ((.x7 ↦ᵣ w) ** ((.x6 ↦ᵣ (r <<< (1 : Nat))) ** (.x5 ↦ᵣ d) **
          (.x28 ↦ᵣ q) ** (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)))
        (by intro h hp; xperm_hyp hp) s1C hbC
    have ht := cpsBranchWithin_ntakenPath hseq (fun hp hQt => by
      obtain ⟨h1, h2, hd, hu, hHEAD, hF⟩ := hQt
      obtain ⟨h1a, h1b, hd1, hu1, hx7, hpure⟩ := hHEAD
      have hcon : BitVec.slt w (0 : Word) := hpure.2
      exact hblt hcon)
    have htS := cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => sepConj_mono_left (fun h' hA => ((sepConj_pure_right h').1 hA).1)
        _ hq) ht
    have s2C := cpsTripleWithin_extend_code
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr b divBlockProg 5 (b + 20)
        (by rw [divBlockProg_length]; decide) (by rw [divBlockProg_length]; decide)
        (by bv_omega)))
      (cpsTripleWithin_frameR
        ((.x6 ↦ᵣ (r <<< (1 : Nat))) ** (.x5 ↦ᵣ d) ** (.x28 ↦ᵣ q) **
          (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)
        (by dsimp [divBitFrame]; pcf)
        (slli_spec_gen_same_within .x7 w (1 : BitVec 6) (b + 20) (by nofun)))
    rw [show (1 : BitVec 6).toNat = 1 from by decide,
      show b + 20 + 4 = b + 24 from by bv_omega] at s2C
    have s3C := cpsTripleWithin_extend_code
      (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr b divBlockProg 6 (b + 24)
        (by rw [divBlockProg_length]; decide) (by rw [divBlockProg_length]; decide)
        (by bv_omega)))
      (cpsTripleWithin_frameR
        ((.x6 ↦ᵣ (r <<< (1 : Nat))) ** (.x7 ↦ᵣ (w <<< (1 : Nat))) ** (.x5 ↦ᵣ d) **
          (.x28 ↦ᵣ q) ** (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)
        (by dsimp [divBitFrame]; pcf)
        (jal_x0_spec_gen_within (12 : BitVec 21) (b + 24)))
    rw [show signExtend21 (12 : BitVec 21) = (12 : Word) from by decide,
      show (b + 24) + (12 : Word) = b + 36 from by bv_omega,
      sepConj_emp_left'] at s3C
    have s23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2C s3C
    have hpre := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) htS s23
    have htail := div_bittail b d (r <<< (1 : Nat)) (w <<< (1 : Nat)) q n
    have hfin := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (by intro h hp; xperm_hyp hp) hpre htail
    refine cpsBranchWithin_weaken
      (P := ((.x6 ↦ᵣ r) ** ((.x5 ↦ᵣ d) ** (.x7 ↦ᵣ w) ** (.x28 ↦ᵣ q) **
        (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)))
      (fun _ hp => by xperm_hyp hp) ?_ ?_ hfin
    · intro h hq
      have h1 : (divBitStep d r w q).1 =
          (if BitVec.ule d (r <<< (1 : Nat)) then (r <<< (1 : Nat)) - d
          else r <<< (1 : Nat)) := by
        simp only [divBitStep, if_neg hmsb,
          show (r <<< (1 : Nat)) + (0 : Word) = r <<< (1 : Nat) from by bv_omega]
        split <;> rfl
      have h2 : (divBitStep d r w q).2.1 = w <<< (1 : Nat) := by
        simp only [divBitStep, if_neg hmsb,
          show (r <<< (1 : Nat)) + (0 : Word) = r <<< (1 : Nat) from by bv_omega]
        split <;> rfl
      have h3 : (divBitStep d r w q).2.2 =
          (if BitVec.ule d (r <<< (1 : Nat)) then (q <<< (1 : Nat)) + 1
          else q <<< (1 : Nat)) := by
        simp only [divBitStep, if_neg hmsb,
          show (r <<< (1 : Nat)) + (0 : Word) = r <<< (1 : Nat) from by bv_omega]
        split <;> rfl
      rw [h1, h2, h3]
      xperm_hyp hq
    · intro h hq
      have h1 : (divBitStep d r w q).1 =
          (if BitVec.ule d (r <<< (1 : Nat)) then (r <<< (1 : Nat)) - d
          else r <<< (1 : Nat)) := by
        simp only [divBitStep, if_neg hmsb,
          show (r <<< (1 : Nat)) + (0 : Word) = r <<< (1 : Nat) from by bv_omega]
        split <;> rfl
      have h2 : (divBitStep d r w q).2.1 = w <<< (1 : Nat) := by
        simp only [divBitStep, if_neg hmsb,
          show (r <<< (1 : Nat)) + (0 : Word) = r <<< (1 : Nat) from by bv_omega]
        split <;> rfl
      have h3 : (divBitStep d r w q).2.2 =
          (if BitVec.ule d (r <<< (1 : Nat)) then (q <<< (1 : Nat)) + 1
          else q <<< (1 : Nat)) := by
        simp only [divBitStep, if_neg hmsb,
          show (r <<< (1 : Nat)) + (0 : Word) = r <<< (1 : Nat) from by bv_omega]
        split <;> rfl
      rw [h1, h2, h3]
      xperm_hyp hq

theorem test_xperm (b : Word) (d r1v w1 q : Word) (n : Nat) (h : PartialState)
    (hp : (((.x28 : Reg) ↦ᵣ (q <<< (1 : Nat))) ** ((.x5 ↦ᵣ d) ** (.x6 ↦ᵣ r1v) **
      (.x7 ↦ᵣ w1) ** (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame)) h) :
    (((.x6 : Reg) ↦ᵣ r1v) ** ((.x5 ↦ᵣ d) ** ((.x28 ↦ᵣ (q <<< (1 : Nat))) **
      (.x7 ↦ᵣ w1) ** (.x29 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** divBitFrame))) h := by
  xperm_hyp hp

/-- Unrolling `divBitRun` from the front by one step. -/
theorem divBitRun_succ (d r w q : Word) (k : Nat) :
    divBitRun d r w q (k + 1) =
      divBitRun d (divBitStep d r w q).1 (divBitStep d r w q).2.1
        (divBitStep d r w q).2.2 k := by
  induction k generalizing r w q with
  | zero => rfl
  | succ k ih =>
    rw [show divBitRun d r w q (k + 1 + 1) =
        divBitStep d (divBitRun d r w q (k + 1)).1 (divBitRun d r w q (k + 1)).2.1
          (divBitRun d r w q (k + 1)).2.2 from rfl,
      show divBitRun d (divBitStep d r w q).1 (divBitStep d r w q).2.1
          (divBitStep d r w q).2.2 (k + 1) =
        divBitStep d (divBitRun d (divBitStep d r w q).1 (divBitStep d r w q).2.1
          (divBitStep d r w q).2.2 k).1
          (divBitRun d (divBitStep d r w q).1 (divBitStep d r w q).2.1
            (divBitStep d r w q).2.2 k).2.1
          (divBitRun d (divBitStep d r w q).1 (divBitStep d r w q).2.1
            (divBitStep d r w q).2.2 k).2.2 from rfl,
      ih]

/-- The full bit loop (instructions 3..14 iterated): `n` iterations from
    counter `n` to the exit with counter `0`. -/
theorem div_bitloop (b : Word) (d r w q : Word) (n : Nat) (hn : n + 1 ≤ 64) :
    cpsTripleWithin (10 * (n + 1)) (b + 12) (b + 60) (CodeReq.ofProg b divBlockProg)
      (divBitState d r w q (BitVec.ofNat 64 (n + 1)) ** divBitFrame)
      (divBitState d (divBitRun d r w q (n + 1)).1 (divBitRun d r w q (n + 1)).2.1
        (divBitRun d r w q (n + 1)).2.2 (BitVec.ofNat 64 0) ** divBitFrame) := by
  induction n generalizing r w q with
  | zero =>
    have hiter := div_bititer b d r w q 0
    have hnt := cpsBranchWithin_ntakenPath hiter (fun hp hQt => by
      obtain ⟨h1, h2, hd, hu, hA, hBP⟩ := hQt
      obtain ⟨h2a, h2b, hd2, hu2, hF, hpure⟩ := hBP
      have hcon : BitVec.ofNat 64 0 ≠ (0 : Word) := hpure.2
      exact hcon (by decide))
    have hmono := cpsTripleWithin_mono_nSteps (by decide : 10 ≤ 10 * (0 + 1)) hnt
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => by
        have h1 : (divBitRun d r w q 1) = divBitStep d r w q := rfl
        rw [h1]
        exact sepConj_mono_right (fun h' hBP => ((sepConj_pure_right h').1 hBP).1)
          _ hq)
      hmono
  | succ k ih =>
    have hiter := div_bititer b d r w q (k + 1)
    have ht := cpsBranchWithin_takenPath hiter (fun hp hQf => by
      obtain ⟨h1, h2, hd, hu, hA, hBP⟩ := hQf
      obtain ⟨h2a, h2b, hd2, hu2, hF, hpure⟩ := hBP
      have hcon : BitVec.ofNat 64 (k + 1) = (0 : Word) := hpure.2
      have hne : BitVec.ofNat 64 (k + 1) ≠ (0 : Word) := by
        bv_omega
      exact hne hcon)
    have htS := cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => sepConj_mono_right (fun h' hBP => ((sepConj_pure_right h').1 hBP).1)
        _ hq) ht
    have hih := ih (divBitStep d r w q).1 (divBitStep d r w q).2.1
      (divBitStep d r w q).2.2 (by omega)
    have hrun : divBitRun d r w q (k + 1 + 1) =
        divBitRun d (divBitStep d r w q).1 (divBitStep d r w q).2.1
          (divBitStep d r w q).2.2 (k + 1) := divBitRun_succ d r w q (k + 1)
    rw [← hrun] at hih
    have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) htS hih
    have hmono := cpsTripleWithin_mono_nSteps (nSteps' := 10 * (k + 1 + 1)) (by omega) hseq
    exact hmono

/-! ## The limb loop -/

/-- Register state of the division limb loop. -/
abbrev divLimbState (d rem cur cnt : Word) : Assertion :=
  (.x5 ↦ᵣ d) ** (.x6 ↦ᵣ rem) ** (.x30 ↦ᵣ cur) ** (.x31 ↦ᵣ cnt)

/-- Registers owned but untouched across the limb loop header. -/
abbrev divLimbFrame (v7 v28 v29 : Word) : Assertion :=
  (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x0 ↦ᵣ (0 : Word))

/-- One limb of the division (instructions 0..14 of the block): load the
    limb, run the 64-iteration bit loop, store the quotient limb, and adjust
    cursor and counter, ending just before the back-edge branch. -/
theorem div_limb_iter (b bufPtr : Word) (low : List Word) (a : Word)
    (done : List Word) (d rem : Word) (v7 v28 v29 : Word) (m : Nat) :
    cpsTripleWithin 646 b (b + 72) (CodeReq.ofProg b divBlockProg)
      (divLimbState d rem (bufPtr + BitVec.ofNat 64 (8 * (low.length + 1)) - 8)
        (BitVec.ofNat 64 (m + 1)) **
        divLimbFrame v7 v28 v29 **
        cellsOf bufPtr (low ++ a :: done))
      (divLimbState d (divBitRun d rem a 0 64).1
        (bufPtr + BitVec.ofNat 64 (8 * low.length) - 8) (BitVec.ofNat 64 m) **
        ((.x28 ↦ᵣ (divBitRun d rem a 0 64).2.2) ** (.x29 ↦ᵣ BitVec.ofNat 64 0) **
          regOwn .x7 ** (.x0 ↦ᵣ (0 : Word))) **
        cellsOf bufPtr (low ++ (divBitRun d rem a 0 64).2.2 :: done)) := by
  sorry

/-- The whole limb loop: `low.length + 1` limbs remaining. -/
theorem div_limbloop (b bufPtr : Word) (low : List Word) (a : Word)
    (done : List Word) (d rem : Word) (v7 v28 v29 : Word) :
    cpsTripleWithin (647 * (low.length + 1)) b (b + 76) (CodeReq.ofProg b divBlockProg)
      (divLimbState d rem (bufPtr + BitVec.ofNat 64 (8 * (low.length + 1)) - 8)
        (BitVec.ofNat 64 (low.length + 1)) **
        divLimbFrame v7 v28 v29 **
        cellsOf bufPtr ((low ++ [a]) ++ done))
      ((.x5 ↦ᵣ d) ** (.x6 ↦ᵣ (divLimbFrom d rem (a :: low.reverse)).2) **
        (.x30 ↦ᵣ (bufPtr - 8)) ** (.x31 ↦ᵣ (0 : Word)) **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) **
        cellsOf bufPtr ((divLimbFrom d rem (a :: low.reverse)).1.reverse ++ done)) := by
  sorry

/-- The 19-instruction division block: from `x5 = d`, `x6 = rem`,
    `x30 = bufPtr + 40`, `x31 = 6` to the quotient limbs written back in
    place and `x6` holding the final remainder. -/
theorem div_block_spec (b bufPtr : Word) (ws : List Word) (d rem : Word)
    (v7 v28 v29 : Word) (hws : ws.length = 6) :
    cpsTripleWithin (647 * 6) b (b + 76) (CodeReq.ofProg b divBlockProg)
      (divLimbState d rem (bufPtr + 40) (6 : Word) **
        divLimbFrame v7 v28 v29 ** cellsOf bufPtr ws)
      ((.x5 ↦ᵣ d) ** (.x6 ↦ᵣ (div384by64 d ws).2) **
        (.x30 ↦ᵣ (bufPtr - 8)) ** (.x31 ↦ᵣ (0 : Word)) **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) **
        cellsOf bufPtr (div384by64 d ws).1) := by
  sorry

end EvmAsm.Codegen.AmsterdamBlobGasPrice
