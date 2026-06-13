/-
  EvmAsm.Codegen.Proofs.CreateDeployedCodeValidSpec

  The SECOND verdict-glue cpsTriple — `create_deployed_code_valid`
  (Codegen/Programs/CreateDeployedCodeValid.lean), the EIP-3541/EIP-7907 deployed
  code validity gate: `a0 := 1` (invalid) iff `len > 32768` OR
  `(len ≠ 0 ∧ code[0] = 0xEF)`, else `0`. Unlike cisv (a single two-exit branch),
  this is a 3-branch SHARED-EXIT DAG, proven by the `_same_cr` family over a
  common `CodeReq.ofProg base cdcvProgram` (the Exp bit-test block,
  Evm64/Exp/LimbSpec.lean, is the template). Per the operator's principle
  (bead evm-asm-tj9ts) the codegen emits exactly this `cdcvProgram` via
  `emitProgram` (deployment-connect, byte-identical + probe-verified), so the
  proof constrains the deployed gate. Axiom-clean.
-/
import EvmAsm.Codegen.Proofs.CreateInitcodeSizeValidSpec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Codegen.Programs.CreateDeployedCodeValid

namespace EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- The structured program the codegen emits (`EvmAsm.Codegen.cdcvProgram`, via
    `emitProgram`); the proof below is over exactly this deployed program. -/
abbrev cdcvProgram : List Instr := EvmAsm.Codegen.cdcvProgram

/-- The gate's full code map. -/
abbrev cdcvCode (base : Word) : CodeReq := CodeReq.ofProg base cdcvProgram

/-- Generic exit arm `li x10, c ;; ret` at `addr` (one of the two shared exits),
    lifted to the full gate code and framed with the rest of the live state. The
    scratch `x5/x6` are carried as `regOwn` (their values are path-dependent — the
    `len=0` path never runs the `lbu`/`li x5,0xEF`); the `regIs→regOwn`
    conversion happens at each merge from the branch's post. -/
private theorem cdcv_arm_at (base addr v11 v5 v6 x10old x1_init c dwordAddr wordVal : Word)
    (hli : ∀ a i, (CodeReq.singleton addr (.LI .x10 c)) a = some i → (cdcvCode base) a = some i)
    (hret : ∀ a i, (CodeReq.singleton (addr + 4) (.JALR .x0 .x1 0)) a = some i → (cdcvCode base) a = some i) :
    cpsTripleWithin 2 addr (x1_init &&& ~~~1) (cdcvCode base)
      ((.x10 ↦ᵣ x10old) ** (.x11 ↦ᵣ v11) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal))
      ((.x10 ↦ᵣ c) ** (.x11 ↦ᵣ v11) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)) := by
  have hLi := cpsTripleWithin_extend_code (h := li_spec_gen_within .x10 x10old c addr (by nofun))
    (hmono := hli)
  have hRet := cpsTripleWithin_extend_code (h := EvmAsm.Evm64.ret_spec_within' (addr + 4) x1_init)
    (hmono := hret)
  have hLiF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal))
    (by pcFree) hLi
  have hRetF := cpsTripleWithin_frameL
    ((.x10 ↦ᵣ c) ** (.x11 ↦ᵣ v11) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (dwordAddr ↦ₘ wordVal))
    (by pcFree) hRet
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hLiF hRetF)

/-- The two shared exit arms, specialised. -/
private theorem cdcv_val_arm (base v11 v5 v6 x10old x1_init dwordAddr wordVal : Word) :
    cpsTripleWithin 2 (base + 24) (x1_init &&& ~~~1) (cdcvCode base)
      ((.x10 ↦ᵣ x10old) ** (.x11 ↦ᵣ v11) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal))
      ((.x10 ↦ᵣ (0:Word)) ** (.x11 ↦ᵣ v11) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)) :=
  cdcv_arm_at base (base + 24) v11 v5 v6 x10old x1_init (0:Word) dwordAddr wordVal
    (CodeReq.ofProg_mono_sub base (base + 24) cdcvProgram [.LI .x10 (0:Word)] 6 (by bv_omega) (by decide) (by decide) (by decide))
    (CodeReq.ofProg_mono_sub base (base + 24 + 4) cdcvProgram [.JALR .x0 .x1 0] 7 (by bv_omega) (by decide) (by decide) (by decide))

private theorem cdcv_inv_arm (base v11 v5 v6 x10old x1_init dwordAddr wordVal : Word) :
    cpsTripleWithin 2 (base + 32) (x1_init &&& ~~~1) (cdcvCode base)
      ((.x10 ↦ᵣ x10old) ** (.x11 ↦ᵣ v11) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal))
      ((.x10 ↦ᵣ (1:Word)) ** (.x11 ↦ᵣ v11) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)) :=
  cdcv_arm_at base (base + 32) v11 v5 v6 x10old x1_init (1:Word) dwordAddr wordVal
    (CodeReq.ofProg_mono_sub base (base + 32) cdcvProgram [.LI .x10 (1:Word)] 8 (by bv_omega) (by decide) (by decide) (by decide))
    (CodeReq.ofProg_mono_sub base (base + 32 + 4) cdcvProgram [.JALR .x0 .x1 0] 9 (by bv_omega) (by decide) (by decide) (by decide))

/-- The 0xEF-check branch + its two arms merged: at `base+20`, `beq x6,x5` decides
    `x10 := if byte0 = 0xEF then 1 else 0`. -/
private theorem cdcv_block3branch (base codePtr len x1_init dwordAddr wordVal byte0 : Word) :
    cpsTripleWithin 3 (base + 20) (x1_init &&& ~~~1) (cdcvCode base)
      ((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ (0xEF:Word)) ** (.x10 ↦ᵣ codePtr) ** (.x11 ↦ᵣ len) **
        (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal))
      ((.x10 ↦ᵣ (if byte0 = (0xEF:Word) then (1:Word) else 0)) ** (.x11 ↦ᵣ len) **
        (.x5 ↦ᵣ (0xEF:Word)) ** (.x6 ↦ᵣ byte0) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)) := by
  have hbr0 := cpsBranchWithin_frameR
    ((.x10 ↦ᵣ codePtr) ** (.x11 ↦ᵣ len) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)) (by pcFree)
    (cpsBranchWithin_extend_code
      (h := beq_spec_gen_within .x6 .x5 (12:BitVec 13) byte0 (0xEF:Word) (base + 20))
      (hmono := CodeReq.ofProg_mono_sub base (base + 20) cdcvProgram [.BEQ .x6 .x5 (12:BitVec 13)] 5
        (by bv_omega) (by decide) (by decide) (by decide)))
  have he_t : (base + 20 : Word) + signExtend13 (12:BitVec 13) = base + 32 := by
    have : signExtend13 (12:BitVec 13) = (12:Word) := by decide
    rw [this]; bv_omega
  have he_f : (base + 20 : Word) + 4 = base + 24 := by bv_omega
  rw [he_t, he_f] at hbr0
  -- taken arm (byte0 = 0xEF) → invalid (x10:=1)
  have hT : cpsTripleWithin 2 (base + 32) (x1_init &&& ~~~1) (cdcvCode base)
      (((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ (0xEF:Word)) ** ⌜byte0 = (0xEF:Word)⌝) **
        ((.x10 ↦ᵣ codePtr) ** (.x11 ↦ᵣ len) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)))
      ((.x10 ↦ᵣ (if byte0 = (0xEF:Word) then (1:Word) else 0)) ** (.x11 ↦ᵣ len) **
        (.x5 ↦ᵣ (0xEF:Word)) ** (.x6 ↦ᵣ byte0) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by sep_perm hp)
      (fun h hq => by
        obtain ⟨hfact, hrest⟩ := (sepConj_pure_left h).mp hq
        rw [if_pos hfact]; sep_perm hrest)
      (cpsTripleWithin_frameL (⌜byte0 = (0xEF:Word)⌝) (by pcFree)
        (cdcv_inv_arm base len (0xEF:Word) byte0 codePtr x1_init dwordAddr wordVal))
  -- not-taken arm (byte0 ≠ 0xEF) → valid (x10:=0)
  have hF : cpsTripleWithin 2 (base + 24) (x1_init &&& ~~~1) (cdcvCode base)
      (((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ (0xEF:Word)) ** ⌜byte0 ≠ (0xEF:Word)⌝) **
        ((.x10 ↦ᵣ codePtr) ** (.x11 ↦ᵣ len) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)))
      ((.x10 ↦ᵣ (if byte0 = (0xEF:Word) then (1:Word) else 0)) ** (.x11 ↦ᵣ len) **
        (.x5 ↦ᵣ (0xEF:Word)) ** (.x6 ↦ᵣ byte0) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by sep_perm hp)
      (fun h hq => by
        obtain ⟨hfact, hrest⟩ := (sepConj_pure_left h).mp hq
        rw [if_neg hfact]; sep_perm hrest)
      (cpsTripleWithin_frameL (⌜byte0 ≠ (0xEF:Word)⌝) (by pcFree)
        (cdcv_val_arm base len (0xEF:Word) byte0 codePtr x1_init dwordAddr wordVal))
  have hm := cpsBranchWithin_merge_same_cr hbr0 hT hF
  exact cpsTripleWithin_weaken (fun _ hp => by sep_perm hp) (fun _ hp => hp) hm

/-- block3 (from `base+12`): `lbu x6,0(x10) ;; li x5,0xEF ;; block3branch`. Loads
    the first byte and decides the 0xEF check. -/
private theorem cdcv_block3 (base codePtr len v6old x1_init dwordAddr wordVal : Word)
    (halign : alignToDword (codePtr + signExtend12 (0:BitVec 12)) = dwordAddr)
    (hvalid : isValidByteAccess (codePtr + signExtend12 (0:BitVec 12)) = true) :
    cpsTripleWithin 5 (base + 12) (x1_init &&& ~~~1) (cdcvCode base)
      ((.x10 ↦ᵣ codePtr) ** (.x11 ↦ᵣ len) ** (.x5 ↦ᵣ (32768:Word)) ** (.x6 ↦ᵣ v6old) **
        (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal))
      ((.x10 ↦ᵣ (if (extractByte wordVal (byteOffset (codePtr + signExtend12 (0:BitVec 12)))).zeroExtend 64 = (0xEF:Word) then (1:Word) else 0)) **
        (.x11 ↦ᵣ len) ** (.x5 ↦ᵣ (0xEF:Word)) **
        (.x6 ↦ᵣ (extractByte wordVal (byteOffset (codePtr + signExtend12 (0:BitVec 12)))).zeroExtend 64) **
        (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)) := by
  set byte0 := (extractByte wordVal (byteOffset (codePtr + signExtend12 (0:BitVec 12)))).zeroExtend 64 with hbyte0
  have hlbu0 := cpsTripleWithin_extend_code
    (h := lbu_spec_gen_within .x6 .x10 codePtr v6old (0:BitVec 12) (base + 12) dwordAddr wordVal (by nofun) halign hvalid)
    (hmono := CodeReq.ofProg_mono_sub base (base + 12) cdcvProgram [.LBU .x6 .x10 (0:BitVec 12)] 3 (by bv_omega) (by decide) (by decide) (by decide))
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hlbu0
  have hlbuF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ len) ** (.x5 ↦ᵣ (32768:Word)) ** (.x1 ↦ᵣ x1_init)) (by pcFree) hlbu0
  have hli0 := cpsTripleWithin_extend_code
    (h := li_spec_gen_within .x5 (32768:Word) (0xEF:Word) (base + 16) (by nofun))
    (hmono := CodeReq.ofProg_mono_sub base (base + 16) cdcvProgram [.LI .x5 (0xEF:Word)] 4 (by bv_omega) (by decide) (by decide) (by decide))
  rw [show (base + 16 : Word) + 4 = base + 20 from by bv_omega] at hli0
  have hliF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ codePtr) ** (.x11 ↦ᵣ len) ** (.x6 ↦ᵣ byte0) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal))
    (by pcFree) hli0
  have hbb := cdcv_block3branch base codePtr len x1_init dwordAddr wordVal byte0
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlbuF hliF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by sep_perm hp)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by sep_perm hp) h12 hbb)

/-- block2 (from `base+8`): `beq x11,x0 ;; (valid | block3)`. Decides
    `x10 := if len = 0 then 0 else (block3 result)`. Scratch `x5/x6` join to
    `regOwn` here (the `len=0` path has `x5=32768/x6=v6old`, block3 has
    `x5=0xEF/x6=byte0`). -/
private theorem cdcv_block2 (base codePtr len v6old x1_init dwordAddr wordVal : Word)
    (halign : alignToDword (codePtr + signExtend12 (0:BitVec 12)) = dwordAddr)
    (hvalid : isValidByteAccess (codePtr + signExtend12 (0:BitVec 12)) = true) :
    cpsTripleWithin 6 (base + 8) (x1_init &&& ~~~1) (cdcvCode base)
      ((.x10 ↦ᵣ codePtr) ** (.x11 ↦ᵣ len) ** (.x5 ↦ᵣ (32768:Word)) ** (.x6 ↦ᵣ v6old) **
        (.x0 ↦ᵣ (0:Word)) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal))
      ((.x10 ↦ᵣ (if len = (0:Word) then (0:Word) else
          if (extractByte wordVal (byteOffset (codePtr + signExtend12 (0:BitVec 12)))).zeroExtend 64 = (0xEF:Word) then (1:Word) else 0)) **
        (.x11 ↦ᵣ len) ** regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0:Word)) **
        (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)) := by
  set byte0 := (extractByte wordVal (byteOffset (codePtr + signExtend12 (0:BitVec 12)))).zeroExtend 64 with hbyte0
  have hcp : (codePtr + signExtend12 (0:BitVec 12) : Word) = codePtr := by
    have h0 : signExtend12 (0:BitVec 12) = (0:Word) := by decide
    rw [h0]; bv_omega
  have hbr0 := cpsBranchWithin_frameR
    ((.x10 ↦ᵣ codePtr) ** (.x5 ↦ᵣ (32768:Word)) ** (.x6 ↦ᵣ v6old) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)) (by pcFree)
    (cpsBranchWithin_extend_code
      (h := beq_spec_gen_within .x11 .x0 (16:BitVec 13) len (0:Word) (base + 8))
      (hmono := CodeReq.ofProg_mono_sub base (base + 8) cdcvProgram [.BEQ .x11 .x0 (16:BitVec 13)] 2
        (by bv_omega) (by decide) (by decide) (by decide)))
  have he_t : (base + 8 : Word) + signExtend13 (16:BitVec 13) = base + 24 := by
    have : signExtend13 (16:BitVec 13) = (16:Word) := by decide
    rw [this]; bv_omega
  have he_f : (base + 8 : Word) + 4 = base + 12 := by bv_omega
  rw [he_t, he_f] at hbr0
  -- taken (len = 0) → valid arm (x10:=0)
  have hT : cpsTripleWithin 5 (base + 24) (x1_init &&& ~~~1) (cdcvCode base)
      (((.x11 ↦ᵣ len) ** (.x0 ↦ᵣ (0:Word)) ** ⌜len = (0:Word)⌝) **
        ((.x10 ↦ᵣ codePtr) ** (.x5 ↦ᵣ (32768:Word)) ** (.x6 ↦ᵣ v6old) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)))
      ((.x10 ↦ᵣ (if len = (0:Word) then (0:Word) else if byte0 = (0xEF:Word) then (1:Word) else 0)) **
        (.x11 ↦ᵣ len) ** regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0:Word)) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by sep_perm hp)
      (fun h hq => by
        obtain ⟨hfact, hrest⟩ := (sepConj_pure_left h).mp hq
        rw [if_pos hfact]
        have h1 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x5 (v := (32768:Word)))))) h hrest
        have h2 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x6 (v := v6old)))))) h h1
        sep_perm h2)
      (cpsTripleWithin_frameL (⌜len = (0:Word)⌝) (by pcFree)
        (cpsTripleWithin_frameR ((.x0 ↦ᵣ (0:Word)))  (by pcFree)
          (cpsTripleWithin_mono_nSteps (by omega)
            (cdcv_val_arm base len (32768:Word) v6old codePtr x1_init dwordAddr wordVal))))
  -- not-taken (len ≠ 0) → block3
  have hF : cpsTripleWithin 5 (base + 12) (x1_init &&& ~~~1) (cdcvCode base)
      (((.x11 ↦ᵣ len) ** (.x0 ↦ᵣ (0:Word)) ** ⌜len ≠ (0:Word)⌝) **
        ((.x10 ↦ᵣ codePtr) ** (.x5 ↦ᵣ (32768:Word)) ** (.x6 ↦ᵣ v6old) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)))
      ((.x10 ↦ᵣ (if len = (0:Word) then (0:Word) else if byte0 = (0xEF:Word) then (1:Word) else 0)) **
        (.x11 ↦ᵣ len) ** regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0:Word)) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by sep_perm hp)
      (fun h hq => by
        obtain ⟨hfact, hrest⟩ := (sepConj_pure_left h).mp hq
        rw [if_neg hfact, hbyte0, hcp]
        have h1 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x5 (v := (0xEF:Word)))))) h hrest
        have h2 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x6 (v := byte0)))))) h h1
        sep_perm h2)
      (cpsTripleWithin_frameL (⌜len ≠ (0:Word)⌝) (by pcFree)
        (cpsTripleWithin_frameR ((.x0 ↦ᵣ (0:Word))) (by pcFree)
          (cdcv_block3 base codePtr len v6old x1_init dwordAddr wordVal halign hvalid)))
  have hm := cpsBranchWithin_merge_same_cr hbr0 hT hF
  exact cpsTripleWithin_weaken (fun _ hp => by sep_perm hp) (fun _ hp => hp) hm

/-- block1 (from `base+4`): `bltu x5,x11 ;; (invalid | block2)`. Decides
    `x10 := if 32768 < len then 1 else (block2 result)`. -/
private theorem cdcv_block1 (base codePtr len v6old x1_init dwordAddr wordVal : Word)
    (halign : alignToDword (codePtr + signExtend12 (0:BitVec 12)) = dwordAddr)
    (hvalid : isValidByteAccess (codePtr + signExtend12 (0:BitVec 12)) = true) :
    cpsTripleWithin 7 (base + 4) (x1_init &&& ~~~1) (cdcvCode base)
      ((.x10 ↦ᵣ codePtr) ** (.x11 ↦ᵣ len) ** (.x5 ↦ᵣ (32768:Word)) ** (.x6 ↦ᵣ v6old) **
        (.x0 ↦ᵣ (0:Word)) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal))
      ((.x10 ↦ᵣ (if BitVec.ult (32768:Word) len then (1:Word) else
          if len = (0:Word) then (0:Word) else
          if (extractByte wordVal (byteOffset codePtr)).zeroExtend 64 = (0xEF:Word) then (1:Word) else 0)) **
        (.x11 ↦ᵣ len) ** regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0:Word)) **
        (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)) := by
  have hcp : (codePtr + signExtend12 (0:BitVec 12) : Word) = codePtr := by
    have h0 : signExtend12 (0:BitVec 12) = (0:Word) := by decide
    rw [h0]; bv_omega
  have hbr0 := cpsBranchWithin_frameR
    ((.x10 ↦ᵣ codePtr) ** (.x6 ↦ᵣ v6old) ** (.x0 ↦ᵣ (0:Word)) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)) (by pcFree)
    (cpsBranchWithin_extend_code
      (h := bltu_spec_gen_within .x5 .x11 (28:BitVec 13) (32768:Word) len (base + 4))
      (hmono := CodeReq.ofProg_mono_sub base (base + 4) cdcvProgram [.BLTU .x5 .x11 (28:BitVec 13)] 1
        (by bv_omega) (by decide) (by decide) (by decide)))
  have he_t : (base + 4 : Word) + signExtend13 (28:BitVec 13) = base + 32 := by
    have : signExtend13 (28:BitVec 13) = (28:Word) := by decide
    rw [this]; bv_omega
  have he_f : (base + 4 : Word) + 4 = base + 8 := by bv_omega
  rw [he_t, he_f] at hbr0
  -- taken (32768 < len) → invalid arm (x10:=1)
  have hT : cpsTripleWithin 6 (base + 32) (x1_init &&& ~~~1) (cdcvCode base)
      (((.x5 ↦ᵣ (32768:Word)) ** (.x11 ↦ᵣ len) ** ⌜BitVec.ult (32768:Word) len⌝) **
        ((.x10 ↦ᵣ codePtr) ** (.x6 ↦ᵣ v6old) ** (.x0 ↦ᵣ (0:Word)) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)))
      ((.x10 ↦ᵣ (if BitVec.ult (32768:Word) len then (1:Word) else
          if len = (0:Word) then (0:Word) else
          if (extractByte wordVal (byteOffset codePtr)).zeroExtend 64 = (0xEF:Word) then (1:Word) else 0)) **
        (.x11 ↦ᵣ len) ** regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0:Word)) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by sep_perm hp)
      (fun h hq => by
        obtain ⟨hfact, hrest⟩ := (sepConj_pure_left h).mp hq
        rw [if_pos hfact]
        have h1 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x5 (v := (32768:Word)))))) h hrest
        have h2 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x6 (v := v6old)))))) h h1
        sep_perm h2)
      (cpsTripleWithin_frameL (⌜BitVec.ult (32768:Word) len⌝) (by pcFree)
        (cpsTripleWithin_frameR ((.x0 ↦ᵣ (0:Word))) (by pcFree)
          (cpsTripleWithin_mono_nSteps (by omega)
            (cdcv_inv_arm base len (32768:Word) v6old codePtr x1_init dwordAddr wordVal))))
  -- not-taken (¬ 32768 < len) → block2
  have hF : cpsTripleWithin 6 (base + 8) (x1_init &&& ~~~1) (cdcvCode base)
      (((.x5 ↦ᵣ (32768:Word)) ** (.x11 ↦ᵣ len) ** ⌜¬ BitVec.ult (32768:Word) len⌝) **
        ((.x10 ↦ᵣ codePtr) ** (.x6 ↦ᵣ v6old) ** (.x0 ↦ᵣ (0:Word)) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)))
      ((.x10 ↦ᵣ (if BitVec.ult (32768:Word) len then (1:Word) else
          if len = (0:Word) then (0:Word) else
          if (extractByte wordVal (byteOffset codePtr)).zeroExtend 64 = (0xEF:Word) then (1:Word) else 0)) **
        (.x11 ↦ᵣ len) ** regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0:Word)) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by sep_perm hp)
      (fun h hq => by
        obtain ⟨hfact, hrest⟩ := (sepConj_pure_left h).mp hq
        rw [if_neg hfact]; rw [hcp] at hrest; sep_perm hrest)
      (cpsTripleWithin_frameL (⌜¬ BitVec.ult (32768:Word) len⌝) (by pcFree)
        (cdcv_block2 base codePtr len v6old x1_init dwordAddr wordVal halign hvalid))
  have hm := cpsBranchWithin_merge_same_cr hbr0 hT hF
  exact cpsTripleWithin_weaken (fun _ hp => by sep_perm hp) (fun _ hp => hp) hm

/-- The full `create_deployed_code_valid` gate as a cpsTriple over the structured
    `cdcvProgram` the codegen emits: `li x5,32768 ;; block1`. The deployed gate
    sets `a0 := 1` (invalid) iff `len > 32768` OR `(len ≠ 0 ∧ code[0] = 0xEF)`,
    else `0`. -/
theorem cdcv_spec (base codePtr len v5old v6old x1_init dwordAddr wordVal : Word)
    (halign : alignToDword (codePtr + signExtend12 (0:BitVec 12)) = dwordAddr)
    (hvalid : isValidByteAccess (codePtr + signExtend12 (0:BitVec 12)) = true) :
    cpsTripleWithin 8 base (x1_init &&& ~~~1) (cdcvCode base)
      ((.x10 ↦ᵣ codePtr) ** (.x11 ↦ᵣ len) ** (.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) **
        (.x0 ↦ᵣ (0:Word)) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal))
      ((.x10 ↦ᵣ (if BitVec.ult (32768:Word) len then (1:Word) else
          if len = (0:Word) then (0:Word) else
          if (extractByte wordVal (byteOffset codePtr)).zeroExtend 64 = (0xEF:Word) then (1:Word) else 0)) **
        (.x11 ↦ᵣ len) ** regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0:Word)) **
        (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal)) := by
  have hli0 := cpsTripleWithin_extend_code
    (h := li_spec_gen_within .x5 v5old (32768:Word) base (by nofun))
    (hmono := CodeReq.ofProg_mono_sub base base cdcvProgram [.LI .x5 (32768:Word)] 0 (by bv_omega) (by decide) (by decide) (by decide))
  have hliF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ codePtr) ** (.x11 ↦ᵣ len) ** (.x6 ↦ᵣ v6old) ** (.x0 ↦ᵣ (0:Word)) ** (.x1 ↦ᵣ x1_init) ** (dwordAddr ↦ₘ wordVal))
    (by pcFree) hli0
  have hb1 := cdcv_block1 base codePtr len v6old x1_init dwordAddr wordVal halign hvalid
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by sep_perm hp) hliF hb1)

end EvmAsm.Rv64
