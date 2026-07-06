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
    else `0`. Alternate formulation over `cdcvCode`; see `cdcv_spec` for the
    explicit-singleton form built on `cdcv_merge1`. -/
theorem cdcv_spec_via_blocks (base codePtr len v5old v6old x1_init dwordAddr wordVal : Word)
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

/-- The EIP-3541 `0xEF`-prefix byte-check branch of `create_deployed_code_valid`,
    at `base + 20`: `BEQ x6 x5` (x6 = loaded byte0, x5 = 239 = 0xEF) jumps to the
    invalid arm (`base + 32`, `LI x10 1; ret`) when equal, else falls to the valid
    arm (`base + 24`, `LI x10 0; ret`). Result `x10 := if byte0 = 239 then 1 else 0`.
    Mirrors `cisv_spec`'s branch merge (disjoint arms), with the extra `x6/x11/mem`
    carried in the frame. -/
theorem cdcv_byte_branch
    (base byte0 len ptrOld x1_init dwordAddr memVal : Word) :
    cpsTripleWithin 3 (base + 20) (x1_init &&& ~~~1)
      ((CodeReq.singleton (base + 20) (.BEQ .x6 .x5 (12 : BitVec 13))).union
        (((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union
            (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).union
         ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union
            (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0)))))
      ((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ (239 : Word)) ** (.x10 ↦ᵣ ptrOld) **
       (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ memVal) ** (.x1 ↦ᵣ x1_init))
      ((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ (239 : Word)) **
       (.x10 ↦ᵣ (if byte0 = (239 : Word) then (1 : Word) else 0)) **
       (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ memVal) ** (.x1 ↦ᵣ x1_init)) := by
  have armT : cpsTripleWithin 2 (base + 32) (x1_init &&& ~~~1)
      ((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union
        (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0)))
      (((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ (239 : Word)) ** ⌜byte0 = (239 : Word)⌝) **
        ((.x10 ↦ᵣ ptrOld) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ memVal) ** (.x1 ↦ᵣ x1_init)))
      ((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ (239 : Word)) **
       (.x10 ↦ᵣ (if byte0 = (239 : Word) then (1 : Word) else 0)) **
       (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ memVal) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by sep_perm hp)
      (fun h hq => by
        obtain ⟨heq, hrest⟩ := (sepConj_pure_left h).mp hq
        rw [if_pos heq]; sep_perm hrest)
      (cpsTripleWithin_frameL ⌜byte0 = (239 : Word)⌝ (by pcFree)
        (cpsTripleWithin_frameR ((.x6 ↦ᵣ byte0) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ memVal))
          (by pcFree)
          (cisv_arm (base + 32) (239 : Word) x1_init ptrOld (1 : Word))))
  have armF : cpsTripleWithin 2 (base + 24) (x1_init &&& ~~~1)
      ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union
        (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0)))
      (((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ (239 : Word)) ** ⌜byte0 ≠ (239 : Word)⌝) **
        ((.x10 ↦ᵣ ptrOld) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ memVal) ** (.x1 ↦ᵣ x1_init)))
      ((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ (239 : Word)) **
       (.x10 ↦ᵣ (if byte0 = (239 : Word) then (1 : Word) else 0)) **
       (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ memVal) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by sep_perm hp)
      (fun h hq => by
        obtain ⟨hne, hrest⟩ := (sepConj_pure_left h).mp hq
        rw [if_neg hne]; sep_perm hrest)
      (cpsTripleWithin_frameL ⌜byte0 ≠ (239 : Word)⌝ (by pcFree)
        (cpsTripleWithin_frameR ((.x6 ↦ᵣ byte0) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ memVal))
          (by pcFree)
          (cisv_arm (base + 24) (239 : Word) x1_init ptrOld (0 : Word))))
  have hbr0 := cpsBranchWithin_frameR
    ((.x10 ↦ᵣ ptrOld) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ memVal) ** (.x1 ↦ᵣ x1_init))
    (by pcFree)
    (generic_beq_spec_within .x6 .x5 (12 : BitVec 13) byte0 (239 : Word) (base + 20))
  have he_t : ((base + 20) + signExtend13 (12 : BitVec 13) : Word) = base + 32 := by
    have : signExtend13 (12 : BitVec 13) = (12 : Word) := by decide
    rw [this]; bv_omega
  have he_f : ((base + 20) + 4 : Word) = base + 24 := by bv_omega
  rw [he_t, he_f] at hbr0
  have hda : (CodeReq.singleton (base + 20) (.BEQ .x6 .x5 (12 : BitVec 13))).Disjoint
      (((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).union
       ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0)))) := by
    apply CodeReq.Disjoint.union_right <;> apply CodeReq.Disjoint.union_right <;>
      apply CodeReq.Disjoint.singleton <;> bv_omega
  have hdtf : ((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).Disjoint
      ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0))) := by
    apply CodeReq.Disjoint.union_left <;> apply CodeReq.Disjoint.union_right <;>
      apply CodeReq.Disjoint.singleton <;> bv_omega
  exact cpsTripleWithin_weaken (fun _ hp => by sep_perm hp) (fun _ hq => by sep_perm hq)
    (cpsBranchWithin_merge hda hdtf hbr0 armT armF)

/-- The byte-load segment of `create_deployed_code_valid`, at `base + 12`:
    `LBU x6, 0(x10)` (load code `byte0`), `LI x5, 239`, then the 0xEF byte-check
    branch (`cdcv_byte_branch`). Establishes `x10 := if byte0 = 239 then 1 else 0`
    where `byte0 = (extractByte wordVal (byteOffset ptrVal)).zeroExtend 64`. -/
theorem cdcv_seg3
    (base ptrVal oldByte oldT0 len x1_init dwordAddr wordVal : Word)
    (halign : alignToDword ptrVal = dwordAddr)
    (hvalid : isValidByteAccess ptrVal = true) :
    cpsTripleWithin 5 (base + 12) (x1_init &&& ~~~1)
      ((CodeReq.singleton (base + 12) (.LBU .x6 .x10 (0 : BitVec 12))).union
        ((CodeReq.singleton (base + 16) (.LI .x5 (239 : Word))).union
          ((CodeReq.singleton (base + 20) (.BEQ .x6 .x5 (12 : BitVec 13))).union
            (((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union
                (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).union
             ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union
                (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0)))))))
      ((.x6 ↦ᵣ oldByte) ** (.x5 ↦ᵣ oldT0) ** (.x10 ↦ᵣ ptrVal) **
       (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init))
      ((.x6 ↦ᵣ (extractByte wordVal (byteOffset ptrVal)).zeroExtend 64) **
       (.x5 ↦ᵣ (239 : Word)) **
       (.x10 ↦ᵣ (if (extractByte wordVal (byteOffset ptrVal)).zeroExtend 64 = (239 : Word)
                 then (1 : Word) else 0)) **
       (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)) := by
  have hz : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have h_lbu0 := generic_lbu_spec_within .x6 .x10 ptrVal oldByte (0 : BitVec 12)
    (base + 12) dwordAddr wordVal (by nofun)
    (by rw [hz]; simpa using halign) (by rw [hz]; simpa using hvalid)
  have haddr : ptrVal + signExtend12 (0 : BitVec 12) = ptrVal := by
    rw [hz]; exact BitVec.add_zero ptrVal
  rw [haddr] at h_lbu0
  have hx16 : (base + 12 + 4 : Word) = base + 16 := by bv_omega
  rw [hx16] at h_lbu0
  set byte0 := (extractByte wordVal (byteOffset ptrVal)).zeroExtend 64 with hb0
  have h_lbu : cpsTripleWithin 1 (base + 12) (base + 16)
      (CodeReq.singleton (base + 12) (.LBU .x6 .x10 (0 : BitVec 12)))
      ((.x6 ↦ᵣ oldByte) ** (.x5 ↦ᵣ oldT0) ** (.x10 ↦ᵣ ptrVal) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init))
      ((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ oldT0) ** (.x10 ↦ᵣ ptrVal) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_weaken (fun _ hp => by sep_perm hp) (fun _ hq => by sep_perm hq)
      (cpsTripleWithin_frameR ((.x5 ↦ᵣ oldT0) ** (.x11 ↦ᵣ len) ** (.x1 ↦ᵣ x1_init)) (by pcFree) h_lbu0)
  have h_li0 := li_spec_within .x5 oldT0 (239 : Word) (base + 16) (by nofun)
  have hx20 : (base + 16 + 4 : Word) = base + 20 := by bv_omega
  rw [hx20] at h_li0
  have h_li : cpsTripleWithin 1 (base + 16) (base + 20)
      (CodeReq.singleton (base + 16) (.LI .x5 (239 : Word)))
      ((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ oldT0) ** (.x10 ↦ᵣ ptrVal) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init))
      ((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ (239 : Word)) ** (.x10 ↦ᵣ ptrVal) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_weaken (fun _ hp => by sep_perm hp) (fun _ hq => by sep_perm hq)
      (cpsTripleWithin_frameR ((.x6 ↦ᵣ byte0) ** (.x10 ↦ᵣ ptrVal) ** (.x11 ↦ᵣ len) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init))
        (by pcFree) h_li0)
  have h_byte := cdcv_byte_branch base byte0 len ptrVal x1_init dwordAddr wordVal
  have hd_li_byte : (CodeReq.singleton (base + 16) (.LI .x5 (239 : Word))).Disjoint
      ((CodeReq.singleton (base + 20) (.BEQ .x6 .x5 (12 : BitVec 13))).union
        (((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).union
         ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0))))) := by
    apply CodeReq.Disjoint.union_right
    · apply CodeReq.Disjoint.singleton; bv_omega
    · apply CodeReq.Disjoint.union_right <;> apply CodeReq.Disjoint.union_right <;>
        apply CodeReq.Disjoint.singleton <;> bv_omega
  have hd_lbu_rest : (CodeReq.singleton (base + 12) (.LBU .x6 .x10 (0 : BitVec 12))).Disjoint
      ((CodeReq.singleton (base + 16) (.LI .x5 (239 : Word))).union
        ((CodeReq.singleton (base + 20) (.BEQ .x6 .x5 (12 : BitVec 13))).union
          (((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).union
           ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0)))))) := by
    apply CodeReq.Disjoint.union_right
    · apply CodeReq.Disjoint.singleton; bv_omega
    · apply CodeReq.Disjoint.union_right
      · apply CodeReq.Disjoint.singleton; bv_omega
      · apply CodeReq.Disjoint.union_right <;> apply CodeReq.Disjoint.union_right <;>
          apply CodeReq.Disjoint.singleton <;> bv_omega
  exact cpsTripleWithin_seq hd_lbu_rest h_lbu (cpsTripleWithin_seq hd_li_byte h_li h_byte)

/-- The empty-length-check branch of `create_deployed_code_valid`, at `base + 8`:
    `BEQ x11 x0` (x11 = len) jumps to the valid arm (`base + 24`, `LI x10 0; ret`)
    when `len = 0`, else falls to the byte-load segment (`base + 12`, `cdcv_seg3`).
    The two paths are merged over ONE shared `CodeReq` (the seg3 code already
    contains the valid arm at `base + 24`, reached as the byte-check fall arm), via
    `cpsBranchWithin_merge_same_cr`. Result
    `x10 := if len = 0 then 0 else if byte0 = 239 then 1 else 0`, with the
    path-dependent scratch regs `x5`/`x6` abstracted to `regOwn`. -/
theorem cdcv_merge2
    (base ptrVal oldByte oldT0 len x1_init dwordAddr wordVal : Word)
    (halign : alignToDword ptrVal = dwordAddr)
    (hvalid : isValidByteAccess ptrVal = true) :
    cpsTripleWithin 6 (base + 8) (x1_init &&& ~~~1)
      ((CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).union
        ((CodeReq.singleton (base + 12) (.LBU .x6 .x10 (0 : BitVec 12))).union
          ((CodeReq.singleton (base + 16) (.LI .x5 (239 : Word))).union
            ((CodeReq.singleton (base + 20) (.BEQ .x6 .x5 (12 : BitVec 13))).union
              (((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union
                  (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).union
               ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union
                  (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0))))))))
      ((.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** (.x6 ↦ᵣ oldByte) ** (.x5 ↦ᵣ oldT0) **
       (.x10 ↦ᵣ ptrVal) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init))
      ((regOwn .x6) ** (regOwn .x5) **
       (.x10 ↦ᵣ (if len = 0 then (0 : Word)
                 else if (extractByte wordVal (byteOffset ptrVal)).zeroExtend 64 = (239 : Word)
                      then (1 : Word) else 0)) **
       (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)) := by
  have hseg := cdcv_seg3 base ptrVal oldByte oldT0 len x1_init dwordAddr wordVal halign hvalid
  set byte0 := (extractByte wordVal (byteOffset ptrVal)).zeroExtend 64 with hb0
  set scode :=
    ((CodeReq.singleton (base + 12) (.LBU .x6 .x10 (0 : BitVec 12))).union
      ((CodeReq.singleton (base + 16) (.LI .x5 (239 : Word))).union
        ((CodeReq.singleton (base + 20) (.BEQ .x6 .x5 (12 : BitVec 13))).union
          (((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union
              (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).union
           ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union
              (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0))))))) with hsc
  -- {base+8} is disjoint from all of seg3's code.
  have hd8 : (CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).Disjoint scode := by
    rw [hsc]
    apply CodeReq.Disjoint.union_right
    · apply CodeReq.Disjoint.singleton; bv_omega
    · apply CodeReq.Disjoint.union_right
      · apply CodeReq.Disjoint.singleton; bv_omega
      · apply CodeReq.Disjoint.union_right
        · apply CodeReq.Disjoint.singleton; bv_omega
        · apply CodeReq.Disjoint.union_right <;> apply CodeReq.Disjoint.union_right <;>
            apply CodeReq.Disjoint.singleton <;> bv_omega
  -- seg3 lifted to the merged code (seg3's code is the left-biased tail).
  have hseg' := cpsTripleWithin_extend_code (CodeReq.mono_union_right hd8 (fun _ _ h => h)) hseg
  -- The valid arm's two addresses are inside seg3's code → inside the merged code.
  have hblk24 : ((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union
      (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))) (base + 24) = none := by
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24) ≠ (base + 32)))]
    exact CodeReq.singleton_miss (by bv_omega : (base + 24) ≠ (base + 32 + 4))
  have hblk28 : ((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union
      (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))) (base + 24 + 4) = none := by
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24 + 4) ≠ (base + 32)))]
    exact CodeReq.singleton_miss (by bv_omega : (base + 24 + 4) ≠ (base + 32 + 4))
  have hva24 : ((CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).union scode)
      (base + 24) = some (.LI .x10 (0 : Word)) := by
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24) ≠ (base + 8)))]
    rw [hsc]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24) ≠ (base + 12)))]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24) ≠ (base + 16)))]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24) ≠ (base + 20)))]
    rw [CodeReq.union_none_left hblk24]
    exact CodeReq.union_hit (CodeReq.singleton_get _ _)
  have hva28 : ((CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).union scode)
      (base + 24 + 4) = some (.JALR .x0 .x1 0) := by
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24 + 4) ≠ (base + 8)))]
    rw [hsc]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24 + 4) ≠ (base + 12)))]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24 + 4) ≠ (base + 16)))]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24 + 4) ≠ (base + 20)))]
    rw [CodeReq.union_none_left hblk28]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 24 + 4) ≠ (base + 24)))]
    exact CodeReq.singleton_get _ _
  have hvalid_mono := CodeReq.union_split_mono (CodeReq.singleton_mono hva24) (CodeReq.singleton_mono hva28)
  -- Taken arm (len = 0): the valid arm at base+24, x10 := 0.
  have h_t : cpsTripleWithin 5 (base + 24) (x1_init &&& ~~~1)
      ((CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).union scode)
      (((.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** ⌜len = (0 : Word)⌝) **
        ((.x6 ↦ᵣ oldByte) ** (.x5 ↦ᵣ oldT0) ** (.x10 ↦ᵣ ptrVal) **
          (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)))
      ((regOwn .x6) ** (regOwn .x5) **
       (.x10 ↦ᵣ (if len = (0 : Word) then (0 : Word) else if byte0 = (239 : Word) then (1 : Word) else 0)) **
       (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_extend_code hvalid_mono
      (cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken
          (fun _ hp => by sep_perm hp)
          (fun h hq => by
            obtain ⟨heq, hrest⟩ := (sepConj_pure_left h).mp hq
            rw [if_pos heq]
            have h1 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x5 oldT0))) h hrest
            have h2 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x6 oldByte)) h h1
            sep_perm h2)
          (cpsTripleWithin_frameL ⌜len = (0 : Word)⌝ (by pcFree)
            (cpsTripleWithin_frameR ((.x6 ↦ᵣ oldByte) ** (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** (dwordAddr ↦ₘ wordVal))
              (by pcFree)
              (cisv_arm (base + 24) oldT0 x1_init ptrVal (0 : Word))))))
  -- Fall arm (len ≠ 0): seg3, x10 := if byte0 = 239 then 1 else 0.
  have h_f : cpsTripleWithin 5 (base + 12) (x1_init &&& ~~~1)
      ((CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).union scode)
      (((.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** ⌜len ≠ (0 : Word)⌝) **
        ((.x6 ↦ᵣ oldByte) ** (.x5 ↦ᵣ oldT0) ** (.x10 ↦ᵣ ptrVal) **
          (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)))
      ((regOwn .x6) ** (regOwn .x5) **
       (.x10 ↦ᵣ (if len = (0 : Word) then (0 : Word) else if byte0 = (239 : Word) then (1 : Word) else 0)) **
       (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by sep_perm hp)
      (fun h hq => by
        obtain ⟨hne, hrest⟩ := (sepConj_pure_left h).mp hq
        rw [if_neg hne]
        have h1 := sepConj_mono_left (sepConj_mono_left (regIs_to_regOwn .x6 byte0)) h hrest
        have h2 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x5 (239 : Word)))) h h1
        sep_perm h2)
      (cpsTripleWithin_frameL ⌜len ≠ (0 : Word)⌝ (by pcFree)
        (cpsTripleWithin_frameR (.x0 ↦ᵣ 0) (by pcFree) hseg'))
  -- Branch: BEQ x11 x0, framing the non-branch state.
  have hbr0 := cpsBranchWithin_frameR
    ((.x6 ↦ᵣ oldByte) ** (.x5 ↦ᵣ oldT0) ** (.x10 ↦ᵣ ptrVal) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init))
    (by pcFree)
    (generic_beq_spec_within .x11 .x0 (16 : BitVec 13) len (0 : Word) (base + 8))
  have he_t : ((base + 8) + signExtend13 (16 : BitVec 13) : Word) = base + 24 := by
    have : signExtend13 (16 : BitVec 13) = (16 : Word) := by decide
    rw [this]; bv_omega
  have he_f : ((base + 8) + 4 : Word) = base + 12 := by bv_omega
  rw [he_t, he_f] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (@CodeReq.union_mono_left (CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))) scode) hbr0
  exact cpsTripleWithin_weaken (fun _ hp => by sep_perm hp) (fun _ hq => by sep_perm hq)
    (cpsBranchWithin_merge_same_cr hbr h_t h_f)

/-- The size-check branch of `create_deployed_code_valid`, at `base + 4`:
    `BGTU a1 t0` (≡ `BLTU x5 x11`, x5 = MAX = 32768, x11 = len) jumps to the invalid
    arm (`base + 32`, `LI x10 1; ret`) when `MAX < len`, else falls to the
    empty-length-check branch (`base + 8`, `cdcv_merge2`). Merges the two paths over
    ONE shared `CodeReq` (the invalid arm at `base + 32` already lives inside seg3's
    code), giving
    `x10 := if MAX < len then 1 else if len = 0 then 0 else if byte0 = 239 then 1 else 0`,
    `x5`/`x6` abstracted to `regOwn`. The prologue's `LI x5 32768` is assumed (x5 = 32768
    on entry); `cdcv_spec` will compose it. -/
theorem cdcv_merge1
    (base ptrVal oldByte len x1_init dwordAddr wordVal : Word)
    (halign : alignToDword ptrVal = dwordAddr)
    (hvalid : isValidByteAccess ptrVal = true) :
    cpsTripleWithin 7 (base + 4) (x1_init &&& ~~~1)
      ((CodeReq.singleton (base + 4) (.BLTU .x5 .x11 (28 : BitVec 13))).union
        ((CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).union
          ((CodeReq.singleton (base + 12) (.LBU .x6 .x10 (0 : BitVec 12))).union
            ((CodeReq.singleton (base + 16) (.LI .x5 (239 : Word))).union
              ((CodeReq.singleton (base + 20) (.BEQ .x6 .x5 (12 : BitVec 13))).union
                (((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union
                    (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).union
                 ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union
                    (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0)))))))))
      ((.x5 ↦ᵣ (32768 : Word)) ** (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** (.x6 ↦ᵣ oldByte) **
       (.x10 ↦ᵣ ptrVal) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init))
      ((regOwn .x6) ** (regOwn .x5) **
       (.x10 ↦ᵣ (if BitVec.ult (32768 : Word) len then (1 : Word)
                 else if len = 0 then (0 : Word)
                 else if (extractByte wordVal (byteOffset ptrVal)).zeroExtend 64 = (239 : Word)
                      then (1 : Word) else 0)) **
       (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)) := by
  have hm2 := cdcv_merge2 base ptrVal oldByte (32768 : Word) len x1_init dwordAddr wordVal halign hvalid
  set byte0 := (extractByte wordVal (byteOffset ptrVal)).zeroExtend 64 with hb0
  set scode :=
    ((CodeReq.singleton (base + 12) (.LBU .x6 .x10 (0 : BitVec 12))).union
      ((CodeReq.singleton (base + 16) (.LI .x5 (239 : Word))).union
        ((CodeReq.singleton (base + 20) (.BEQ .x6 .x5 (12 : BitVec 13))).union
          (((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union
              (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).union
           ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union
              (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0))))))) with hsc
  -- {base+4} is disjoint from merge2's code (the {base+8 BEQ} branch + seg3 code).
  have hd4 : (CodeReq.singleton (base + 4) (.BLTU .x5 .x11 (28 : BitVec 13))).Disjoint
      ((CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).union scode) := by
    rw [hsc]
    apply CodeReq.Disjoint.union_right
    · apply CodeReq.Disjoint.singleton; bv_omega
    · apply CodeReq.Disjoint.union_right
      · apply CodeReq.Disjoint.singleton; bv_omega
      · apply CodeReq.Disjoint.union_right
        · apply CodeReq.Disjoint.singleton; bv_omega
        · apply CodeReq.Disjoint.union_right
          · apply CodeReq.Disjoint.singleton; bv_omega
          · apply CodeReq.Disjoint.union_right <;> apply CodeReq.Disjoint.union_right <;>
              apply CodeReq.Disjoint.singleton <;> bv_omega
  -- merge2 lifted to the merged code (merge2's code is the left-biased tail).
  have hm2' := cpsTripleWithin_extend_code (CodeReq.mono_union_right hd4 (fun _ _ h => h)) hm2
  -- The invalid arm's two addresses are inside seg3's code → inside the merged code.
  have hinv32 : ((CodeReq.singleton (base + 4) (.BLTU .x5 .x11 (28 : BitVec 13))).union
      ((CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).union scode))
      (base + 32) = some (.LI .x10 (1 : Word)) := by
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 32) ≠ (base + 4)))]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 32) ≠ (base + 8)))]
    rw [hsc]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 32) ≠ (base + 12)))]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 32) ≠ (base + 16)))]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 32) ≠ (base + 20)))]
    exact CodeReq.union_hit (CodeReq.union_hit (CodeReq.singleton_get _ _))
  have hinv36 : ((CodeReq.singleton (base + 4) (.BLTU .x5 .x11 (28 : BitVec 13))).union
      ((CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).union scode))
      (base + 32 + 4) = some (.JALR .x0 .x1 0) := by
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 32 + 4) ≠ (base + 4)))]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 32 + 4) ≠ (base + 8)))]
    rw [hsc]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 32 + 4) ≠ (base + 12)))]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 32 + 4) ≠ (base + 16)))]
    rw [CodeReq.union_none_left (CodeReq.singleton_miss (by bv_omega : (base + 32 + 4) ≠ (base + 20)))]
    refine CodeReq.union_hit (CodeReq.union_skip (CodeReq.singleton_miss (by bv_omega : (base + 32 + 4) ≠ (base + 32))) ?_)
    exact CodeReq.singleton_get _ _
  have hinv_mono := CodeReq.union_split_mono (CodeReq.singleton_mono hinv32) (CodeReq.singleton_mono hinv36)
  -- Taken arm (MAX < len): the invalid arm at base+32, x10 := 1.
  have h_t : cpsTripleWithin 6 (base + 32) (x1_init &&& ~~~1)
      ((CodeReq.singleton (base + 4) (.BLTU .x5 .x11 (28 : BitVec 13))).union
        ((CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).union scode))
      (((.x5 ↦ᵣ (32768 : Word)) ** (.x11 ↦ᵣ len) ** ⌜BitVec.ult (32768 : Word) len⌝) **
        ((.x0 ↦ᵣ 0) ** (.x6 ↦ᵣ oldByte) ** (.x10 ↦ᵣ ptrVal) **
          (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)))
      ((regOwn .x6) ** (regOwn .x5) **
       (.x10 ↦ᵣ (if BitVec.ult (32768 : Word) len then (1 : Word)
                 else if len = 0 then (0 : Word) else if byte0 = (239 : Word) then (1 : Word) else 0)) **
       (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_extend_code hinv_mono
      (cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken
          (fun _ hp => by sep_perm hp)
          (fun h hq => by
            obtain ⟨hult, hrest⟩ := (sepConj_pure_left h).mp hq
            rw [if_pos hult]
            have h1 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x5 (32768 : Word)))) h hrest
            have h2 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x6 oldByte)) h h1
            sep_perm h2)
          (cpsTripleWithin_frameL ⌜BitVec.ult (32768 : Word) len⌝ (by pcFree)
            (cpsTripleWithin_frameR ((.x6 ↦ᵣ oldByte) ** (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** (dwordAddr ↦ₘ wordVal))
              (by pcFree)
              (cisv_arm (base + 32) (32768 : Word) x1_init ptrVal (1 : Word))))))
  -- Fall arm (MAX ≥ len): merge2 (empty-check + byte segment).
  have h_f : cpsTripleWithin 6 (base + 8) (x1_init &&& ~~~1)
      ((CodeReq.singleton (base + 4) (.BLTU .x5 .x11 (28 : BitVec 13))).union
        ((CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).union scode))
      (((.x5 ↦ᵣ (32768 : Word)) ** (.x11 ↦ᵣ len) ** ⌜¬ BitVec.ult (32768 : Word) len⌝) **
        ((.x0 ↦ᵣ 0) ** (.x6 ↦ᵣ oldByte) ** (.x10 ↦ᵣ ptrVal) **
          (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)))
      ((regOwn .x6) ** (regOwn .x5) **
       (.x10 ↦ᵣ (if BitVec.ult (32768 : Word) len then (1 : Word)
                 else if len = 0 then (0 : Word) else if byte0 = (239 : Word) then (1 : Word) else 0)) **
       (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by sep_perm hp)
      (fun h hq => by
        obtain ⟨hnu, hrest⟩ := (sepConj_pure_left h).mp hq
        rw [if_neg hnu]
        sep_perm hrest)
      (cpsTripleWithin_frameL ⌜¬ BitVec.ult (32768 : Word) len⌝ (by pcFree) hm2')
  -- Branch: BLTU x5 x11, framing the non-branch state.
  have hbr0 := cpsBranchWithin_frameR
    ((.x0 ↦ᵣ 0) ** (.x6 ↦ᵣ oldByte) ** (.x10 ↦ᵣ ptrVal) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init))
    (by pcFree)
    (generic_bltu_spec_within .x5 .x11 (28 : BitVec 13) (32768 : Word) len (base + 4))
  have he_t : ((base + 4) + signExtend13 (28 : BitVec 13) : Word) = base + 32 := by
    have : signExtend13 (28 : BitVec 13) = (28 : Word) := by decide
    rw [this]; bv_omega
  have he_f : ((base + 4) + 4 : Word) = base + 8 := by bv_omega
  rw [he_t, he_f] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (@CodeReq.union_mono_left (CodeReq.singleton (base + 4) (.BLTU .x5 .x11 (28 : BitVec 13)))
      ((CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).union scode)) hbr0
  exact cpsTripleWithin_weaken (fun _ hp => by sep_perm hp) (fun _ hq => by sep_perm hq)
    (cpsBranchWithin_merge_same_cr hbr h_t h_f)

/-- The full `create_deployed_code_valid` gate as a `cpsTriple`: the prologue
    `LI x5 32768` (set the MAX_CODE_SIZE constant) sequenced with the size-check
    branch tree (`cdcv_merge1`). 8 steps from `base`:
    `x10 := if MAX < len then 1 else if len = 0 then 0 else if byte0 = 239 then 1 else 0`
    (0 = valid/deploy, 1 = invalid), `x5`/`x6` abstracted to `regOwn`. This is the
    complete EIP-7907/EIP-3541 deployed-code validity logic. The deployment-connect
    (codegen emits this program byte-identically + the `zisk_create_deployed_code_valid`
    probe) is the follow-up. -/
theorem cdcv_spec
    (base ptrVal oldByte v5old len x1_init dwordAddr wordVal : Word)
    (halign : alignToDword ptrVal = dwordAddr)
    (hvalid : isValidByteAccess ptrVal = true) :
    cpsTripleWithin 8 base (x1_init &&& ~~~1)
      ((CodeReq.singleton base (.LI .x5 (32768 : Word))).union
        ((CodeReq.singleton (base + 4) (.BLTU .x5 .x11 (28 : BitVec 13))).union
          ((CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).union
            ((CodeReq.singleton (base + 12) (.LBU .x6 .x10 (0 : BitVec 12))).union
              ((CodeReq.singleton (base + 16) (.LI .x5 (239 : Word))).union
                ((CodeReq.singleton (base + 20) (.BEQ .x6 .x5 (12 : BitVec 13))).union
                  (((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union
                      (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).union
                   ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union
                      (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0))))))))))
      ((.x5 ↦ᵣ v5old) ** (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** (.x6 ↦ᵣ oldByte) **
       (.x10 ↦ᵣ ptrVal) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init))
      ((regOwn .x6) ** (regOwn .x5) **
       (.x10 ↦ᵣ (if BitVec.ult (32768 : Word) len then (1 : Word)
                 else if len = 0 then (0 : Word)
                 else if (extractByte wordVal (byteOffset ptrVal)).zeroExtend 64 = (239 : Word)
                      then (1 : Word) else 0)) **
       (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init)) := by
  have hm1 := cdcv_merge1 base ptrVal oldByte len x1_init dwordAddr wordVal halign hvalid
  -- Prologue: LI x5 32768 at base, base → base+4. Frame the rest (its post is
  -- exactly merge1's entry).
  have hpro := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ len) ** (.x0 ↦ᵣ 0) ** (.x6 ↦ᵣ oldByte) ** (.x10 ↦ᵣ ptrVal) **
      (dwordAddr ↦ₘ wordVal) ** (.x1 ↦ᵣ x1_init))
    (by pcFree)
    (li_spec_within .x5 v5old (32768 : Word) base (by nofun))
  have hd0 : (CodeReq.singleton base (.LI .x5 (32768 : Word))).Disjoint
      ((CodeReq.singleton (base + 4) (.BLTU .x5 .x11 (28 : BitVec 13))).union
        ((CodeReq.singleton (base + 8) (.BEQ .x11 .x0 (16 : BitVec 13))).union
          ((CodeReq.singleton (base + 12) (.LBU .x6 .x10 (0 : BitVec 12))).union
            ((CodeReq.singleton (base + 16) (.LI .x5 (239 : Word))).union
              ((CodeReq.singleton (base + 20) (.BEQ .x6 .x5 (12 : BitVec 13))).union
                (((CodeReq.singleton (base + 32) (.LI .x10 (1 : Word))).union
                    (CodeReq.singleton (base + 32 + 4) (.JALR .x0 .x1 0))).union
                 ((CodeReq.singleton (base + 24) (.LI .x10 (0 : Word))).union
                    (CodeReq.singleton (base + 24 + 4) (.JALR .x0 .x1 0))))))))) := by
    apply CodeReq.Disjoint.union_right
    · apply CodeReq.Disjoint.singleton; bv_omega
    · apply CodeReq.Disjoint.union_right
      · apply CodeReq.Disjoint.singleton; bv_omega
      · apply CodeReq.Disjoint.union_right
        · apply CodeReq.Disjoint.singleton; bv_omega
        · apply CodeReq.Disjoint.union_right
          · apply CodeReq.Disjoint.singleton; bv_omega
          · apply CodeReq.Disjoint.union_right
            · apply CodeReq.Disjoint.singleton; bv_omega
            · apply CodeReq.Disjoint.union_right <;> apply CodeReq.Disjoint.union_right <;>
                apply CodeReq.Disjoint.singleton <;> bv_omega
  exact cpsTripleWithin_seq hd0 hpro hm1

end EvmAsm.Rv64
