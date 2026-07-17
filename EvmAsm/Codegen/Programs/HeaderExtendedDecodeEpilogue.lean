/-
  The shared epilogue of `headerExtendedDecode_prog`
  (`Programs/HeaderDecode.lean`, PR-K39), slots [164]-[173]:

    [164] LI  x10, 0          [165] JAL x0, +8        -- success: a0 = 0, skip
    [166] LI  x10, 1                                  -- fail: a0 = 1  (HB + 664)
    [167] LD  x1,  0(sp)      [168] LD x8,  8(sp)     [169] LD x9, 16(sp)
    [170] LD  x18, 24(sp)     [171] LD x19, 32(sp)
    [172] ADDI sp, sp, 64     [173] JALR x0, x1, 0    -- restore + return

  The success ([164]-[165]) and fail ([166]) entries converge on the register
  restore + return tail ([167]-[173]) (`hedEpilogueRet`).  The tail reloads the
  five callee-saved registers, pops the 64-byte frame, and returns to the saved
  `ra`.  `hedEpilogueSuccess` / `hedEpilogueFail` set `a0` and jump into the tail.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.HeaderExtendedDecodeCall

namespace EvmAsm.Codegen.HeaderExtendedDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP

/-- The saved-register / frame image on the stack at frame pointer `spF`
    (`= sp₀ − 64`): `ra` at `+0`, `s0` `+8`, `s1` `+16`, `s2` `+24`, `s3` `+32`. -/
def hedStackFrame (spF raSaved s0v s1v s2v s3v : Word) : Assertion :=
  ((spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0v) ** ((spF + 16) ↦ₘ s1v) **
    ((spF + 24) ↦ₘ s2v) ** ((spF + 32) ↦ₘ s3v))

set_option maxRecDepth 8000 in
/-- The register-restore + return tail ([167]-[173], `HB + 668` → `ra`): reload
    `ra`/`s0`/`s1`/`s2`/`s3` from the frame, pop 64 bytes of stack, and `ret`. -/
theorem hedEpilogueRet {Extra : Assertion} (spF raSaved s0v s1v s2v s3v v1o v8o v9o v18o v19o : Word)
    (hExtra : Extra.pcFree) :
    cpsTripleWithin 7 (HB + 668) (raSaved &&& ~~~(1 : Word)) fullCode
      (((.x2 : Reg) ↦ᵣ spF) ** ((.x1 : Reg) ↦ᵣ v1o) ** ((.x8 : Reg) ↦ᵣ v8o) **
        ((.x9 : Reg) ↦ᵣ v9o) ** ((.x18 : Reg) ↦ᵣ v18o) ** ((.x19 : Reg) ↦ᵣ v19o) **
        hedStackFrame spF raSaved s0v s1v s2v s3v ** Extra)
      (((.x1 : Reg) ↦ᵣ raSaved) ** ((.x8 : Reg) ↦ᵣ s0v) ** ((.x9 : Reg) ↦ᵣ s1v) **
        ((.x18 : Reg) ↦ᵣ s2v) ** ((.x19 : Reg) ↦ᵣ s3v) ** ((.x2 : Reg) ↦ᵣ (spF + 64)) **
        hedStackFrame spF raSaved s0v s1v s2v s3v ** Extra) := by
  unfold hedStackFrame
  -- [167] LD x1, 0(sp)
  have h1 := ld_spec_gen_within .x1 .x2 spF v1o raSaved (0 : BitVec 12) (HB + 668) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide, show spF + 0 = spF from by bv_omega,
    show (HB + 668) + 4 = HB + 672 from by bv_omega] at h1
  have h1L := cpsTripleWithin_extend_code
    ((fun a i h => hed_mono a i (CodeReq.ofProg_mem_at HB (HB + 668) headerExtendedDecode_prog 167 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))) h1
  have h1F := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ v8o) ** ((.x9 : Reg) ↦ᵣ v9o) ** ((.x18 : Reg) ↦ᵣ v18o) **
     ((.x19 : Reg) ↦ᵣ v19o) ** ((spF + 8) ↦ₘ s0v) ** ((spF + 16) ↦ₘ s1v) **
     ((spF + 24) ↦ₘ s2v) ** ((spF + 32) ↦ₘ s3v) ** Extra)
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) h1L
  -- [168] LD x8, 8(sp)
  have h8 := ld_spec_gen_within .x8 .x2 spF v8o s0v (8 : BitVec 12) (HB + 672) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show (HB + 672) + 4 = HB + 676 from by bv_omega] at h8
  have h8L := cpsTripleWithin_extend_code
    ((fun a i h => hed_mono a i (CodeReq.ofProg_mem_at HB (HB + 672) headerExtendedDecode_prog 168 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))) h8
  have h8F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raSaved) ** ((.x9 : Reg) ↦ᵣ v9o) ** ((.x18 : Reg) ↦ᵣ v18o) **
     ((.x19 : Reg) ↦ᵣ v19o) ** (spF ↦ₘ raSaved) ** ((spF + 16) ↦ₘ s1v) **
     ((spF + 24) ↦ₘ s2v) ** ((spF + 32) ↦ₘ s3v) ** Extra)
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) h8L
  -- [169] LD x9, 16(sp)
  have h9 := ld_spec_gen_within .x9 .x2 spF v9o s1v (16 : BitVec 12) (HB + 676) (by decide)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
    show (HB + 676) + 4 = HB + 680 from by bv_omega] at h9
  have h9L := cpsTripleWithin_extend_code
    ((fun a i h => hed_mono a i (CodeReq.ofProg_mem_at HB (HB + 676) headerExtendedDecode_prog 169 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))) h9
  have h9F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raSaved) ** ((.x8 : Reg) ↦ᵣ s0v) ** ((.x18 : Reg) ↦ᵣ v18o) **
     ((.x19 : Reg) ↦ᵣ v19o) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0v) **
     ((spF + 24) ↦ₘ s2v) ** ((spF + 32) ↦ₘ s3v) ** Extra)
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) h9L
  -- [170] LD x18, 24(sp)
  have h18 := ld_spec_gen_within .x18 .x2 spF v18o s2v (24 : BitVec 12) (HB + 680) (by decide)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
    show (HB + 680) + 4 = HB + 684 from by bv_omega] at h18
  have h18L := cpsTripleWithin_extend_code
    ((fun a i h => hed_mono a i (CodeReq.ofProg_mem_at HB (HB + 680) headerExtendedDecode_prog 170 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))) h18
  have h18F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raSaved) ** ((.x8 : Reg) ↦ᵣ s0v) ** ((.x9 : Reg) ↦ᵣ s1v) **
     ((.x19 : Reg) ↦ᵣ v19o) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0v) **
     ((spF + 16) ↦ₘ s1v) ** ((spF + 32) ↦ₘ s3v) ** Extra)
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) h18L
  -- [171] LD x19, 32(sp)
  have h19 := ld_spec_gen_within .x19 .x2 spF v19o s3v (32 : BitVec 12) (HB + 684) (by decide)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
    show (HB + 684) + 4 = HB + 688 from by bv_omega] at h19
  have h19L := cpsTripleWithin_extend_code
    ((fun a i h => hed_mono a i (CodeReq.ofProg_mem_at HB (HB + 684) headerExtendedDecode_prog 171 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))) h19
  have h19F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raSaved) ** ((.x8 : Reg) ↦ᵣ s0v) ** ((.x9 : Reg) ↦ᵣ s1v) **
     ((.x18 : Reg) ↦ᵣ s2v) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0v) **
     ((spF + 16) ↦ₘ s1v) ** ((spF + 24) ↦ₘ s2v) ** Extra)
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) h19L
  -- [172] ADDI sp, sp, 64
  have hadd := addi_spec_gen_same_within .x2 spF (64 : BitVec 12) (HB + 688) (by decide)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide,
    show (HB + 688) + 4 = HB + 692 from by bv_omega] at hadd
  have haddL := cpsTripleWithin_extend_code
    ((fun a i h => hed_mono a i (CodeReq.ofProg_mem_at HB (HB + 688) headerExtendedDecode_prog 172 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))) hadd
  have haddF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raSaved) ** ((.x8 : Reg) ↦ᵣ s0v) ** ((.x9 : Reg) ↦ᵣ s1v) **
     ((.x18 : Reg) ↦ᵣ s2v) ** ((.x19 : Reg) ↦ᵣ s3v) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0v) **
     ((spF + 16) ↦ₘ s1v) ** ((spF + 24) ↦ₘ s2v) ** ((spF + 32) ↦ₘ s3v) ** Extra)
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) haddL
  -- [173] JALR x0, x1, 0  (return to ra)
  have hret := jalr_x0_spec_gen_within .x1 raSaved (0 : BitVec 12) (HB + 692)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide, show raSaved + 0 = raSaved from by bv_omega] at hret
  have hretL := cpsTripleWithin_extend_code
    ((fun a i h => hed_mono a i (CodeReq.ofProg_mem_at HB (HB + 692) headerExtendedDecode_prog 173 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))) hret
  have hretF := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ s0v) ** ((.x9 : Reg) ↦ᵣ s1v) ** ((.x18 : Reg) ↦ᵣ s2v) **
     ((.x19 : Reg) ↦ᵣ s3v) ** ((.x2 : Reg) ↦ᵣ (spF + 64)) ** (spF ↦ₘ raSaved) ** ((spF + 8) ↦ₘ s0v) **
     ((spF + 16) ↦ₘ s1v) ** ((spF + 24) ↦ₘ s2v) ** ((spF + 32) ↦ₘ s3v) ** Extra)
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) hretL
  -- chain the seven straight-line steps.
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h1F h8F
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 h9F
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 h18F
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 h19F
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s4 haddF
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 hretF
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) s6)

#print axioms hedEpilogueRet

set_option maxRecDepth 8000 in
/-- The fail entry ([166], `HB + 664` → `ra`): set `a0 = 1`, then the restore
    tail.  This is the convergence point of every parse-failure short-circuit. -/
theorem hedEpilogueFail {Extra : Assertion} (spF raSaved s0v s1v s2v s3v v10o v1o v8o v9o v18o v19o : Word)
    (hExtra : Extra.pcFree) :
    cpsTripleWithin 8 (HB + 664) (raSaved &&& ~~~(1 : Word)) fullCode
      (((.x10 : Reg) ↦ᵣ v10o) ** ((.x2 : Reg) ↦ᵣ spF) ** ((.x1 : Reg) ↦ᵣ v1o) **
        ((.x8 : Reg) ↦ᵣ v8o) ** ((.x9 : Reg) ↦ᵣ v9o) ** ((.x18 : Reg) ↦ᵣ v18o) **
        ((.x19 : Reg) ↦ᵣ v19o) ** hedStackFrame spF raSaved s0v s1v s2v s3v ** Extra)
      (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x1 : Reg) ↦ᵣ raSaved) ** ((.x8 : Reg) ↦ᵣ s0v) **
        ((.x9 : Reg) ↦ᵣ s1v) ** ((.x18 : Reg) ↦ᵣ s2v) ** ((.x19 : Reg) ↦ᵣ s3v) **
        ((.x2 : Reg) ↦ᵣ (spF + 64)) ** hedStackFrame spF raSaved s0v s1v s2v s3v ** Extra) := by
  have mem : ∀ a i, CodeReq.singleton (HB + 664) (.LI .x10 (1 : Word)) a = some i → fullCode a = some i :=
    fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 664) headerExtendedDecode_prog 166 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h)
  have hli := li_spec_gen_within .x10 v10o (1 : Word) (HB + 664) (by decide)
  rw [show (HB + 664) + 4 = HB + 668 from by bv_omega] at hli
  have hliL := cpsTripleWithin_extend_code mem hli
  have hliF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ spF) ** ((.x1 : Reg) ↦ᵣ v1o) ** ((.x8 : Reg) ↦ᵣ v8o) **
     ((.x9 : Reg) ↦ᵣ v9o) ** ((.x18 : Reg) ↦ᵣ v18o) ** ((.x19 : Reg) ↦ᵣ v19o) **
     hedStackFrame spF raSaved s0v s1v s2v s3v ** Extra)
    (by unfold hedStackFrame; repeat' first | exact pcFree_regIs | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) hliL
  have hret := hedEpilogueRet (Extra := ((.x10 : Reg) ↦ᵣ (1 : Word)) ** Extra) spF raSaved s0v s1v s2v s3v v1o v8o v9o v18o v19o
    (by apply pcFree_sepConj; exact pcFree_regIs; exact hExtra)
  have hretF := hret
  have s := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hliF hretF
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) s)

#print axioms hedEpilogueFail

set_option maxRecDepth 8000 in
/-- The success entry ([164]-[165], `HB + 656` → `ra`): set `a0 = 0`, jump over
    the fail slot, then the restore tail. -/
theorem hedEpilogueSuccess {Extra : Assertion} (spF raSaved s0v s1v s2v s3v v10o v1o v8o v9o v18o v19o : Word)
    (hExtra : Extra.pcFree) :
    cpsTripleWithin 9 (HB + 656) (raSaved &&& ~~~(1 : Word)) fullCode
      (((.x10 : Reg) ↦ᵣ v10o) ** ((.x2 : Reg) ↦ᵣ spF) ** ((.x1 : Reg) ↦ᵣ v1o) **
        ((.x8 : Reg) ↦ᵣ v8o) ** ((.x9 : Reg) ↦ᵣ v9o) ** ((.x18 : Reg) ↦ᵣ v18o) **
        ((.x19 : Reg) ↦ᵣ v19o) ** hedStackFrame spF raSaved s0v s1v s2v s3v ** Extra)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raSaved) ** ((.x8 : Reg) ↦ᵣ s0v) **
        ((.x9 : Reg) ↦ᵣ s1v) ** ((.x18 : Reg) ↦ᵣ s2v) ** ((.x19 : Reg) ↦ᵣ s3v) **
        ((.x2 : Reg) ↦ᵣ (spF + 64)) ** hedStackFrame spF raSaved s0v s1v s2v s3v ** Extra) := by
  have memLI : ∀ a i, CodeReq.singleton (HB + 656) (.LI .x10 (0 : Word)) a = some i → fullCode a = some i :=
    fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 656) headerExtendedDecode_prog 164 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h)
  have memJAL : ∀ a i, CodeReq.singleton (HB + 660) (.JAL .x0 (8 : BitVec 21)) a = some i → fullCode a = some i :=
    fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 660) headerExtendedDecode_prog 165 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h)
  have hli := li_spec_gen_within .x10 v10o (0 : Word) (HB + 656) (by decide)
  rw [show (HB + 656) + 4 = HB + 660 from by bv_omega] at hli
  have hliL := cpsTripleWithin_extend_code memLI hli
  have hliF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ spF) ** ((.x1 : Reg) ↦ᵣ v1o) ** ((.x8 : Reg) ↦ᵣ v8o) **
     ((.x9 : Reg) ↦ᵣ v9o) ** ((.x18 : Reg) ↦ᵣ v18o) ** ((.x19 : Reg) ↦ᵣ v19o) **
     hedStackFrame spF raSaved s0v s1v s2v s3v ** Extra)
    (by unfold hedStackFrame; repeat' first | exact pcFree_regIs | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) hliL
  have hjal := jal_x0_spec_gen_within (8 : BitVec 21) (HB + 660)
  rw [show (HB + 660) + signExtend21 (8 : BitVec 21) = HB + 668 from by
    rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]; bv_omega] at hjal
  have hjalL := cpsTripleWithin_extend_code memJAL hjal
  have hjalF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ spF) ** ((.x1 : Reg) ↦ᵣ v1o) **
     ((.x8 : Reg) ↦ᵣ v8o) ** ((.x9 : Reg) ↦ᵣ v9o) ** ((.x18 : Reg) ↦ᵣ v18o) **
     ((.x19 : Reg) ↦ᵣ v19o) ** hedStackFrame spF raSaved s0v s1v s2v s3v ** Extra)
    (by unfold hedStackFrame; repeat' first | exact pcFree_regIs | exact pcFree_memIs | exact hExtra | apply pcFree_sepConj) hjalL
  rw [sepConj_emp_left'] at hjalF
  have hret := hedEpilogueRet (Extra := ((.x10 : Reg) ↦ᵣ (0 : Word)) ** Extra) spF raSaved s0v s1v s2v s3v v1o v8o v9o v18o v19o
    (by apply pcFree_sepConj; exact pcFree_regIs; exact hExtra)
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hliF hjalF
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hret
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) s2)

#print axioms hedEpilogueSuccess

end EvmAsm.Codegen.HeaderExtendedDecodeSpec
