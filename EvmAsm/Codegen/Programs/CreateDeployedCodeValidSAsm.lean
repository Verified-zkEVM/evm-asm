/-
  EvmAsm.Codegen.Programs.CreateDeployedCodeValidSAsm

  `create_deployed_code_valid` via the **shared-return-tail forward join**
  (`EvmAsm/Rv64/SAsm/RetForwardJoin.lean`, bead evm-asm-k2f1x) — the
  acceptance consumer for the combinator.

  The gate is a 3-guard forward-join DAG over TWO shared return tails:

  ```
        li   t0, 32768
        bltu t0, a1, .invalid     -- guard 1: len > MAX_CODE_SIZE
        beqz a1,     .valid       -- guard 2: empty code is valid
        lbu  t1, 0(a0)
        li   t0, 0xEF
        beq  t1, t0, .invalid     -- guard 3: EIP-3541 0xEF prefix
  .valid:   li a0, 0 ; ret        -- ONE copy (guard 2 target + fallthrough)
  .invalid: li a0, 1 ; ret        -- ONE copy (guard 1 + guard 3 target)
  ```

  Each tail is proven ONCE (`sharedRetTail_spec`, a single `have` below)
  and reused at both guard stations that target it; each station is one
  `retJoinStation_spec`, receiving its branch fact as a hypothesis.  No
  tail bytes are duplicated — the port is byte-transparent: the verified
  `cdcvProgram` IS what the codegen emits (`createDeployedCodeValidFunction
  = emitProgram cdcvProgram`, kernel-checked below), so no guest-byte
  change and no A/B.

  Genuine post (the real EIP-7907/EIP-3541 predicate, 0 = valid/deploy,
  1 = invalid):
    `a0 = if 32768 <u len then 1
          else if len = 0 then 0
          else if code[0] = 0xEF then 1 else 0`.
-/

import EvmAsm.Rv64.SAsm.RetForwardJoin
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Codegen.Programs.CreateDeployedCodeValid

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace CreateDeployedCodeValidSAsm

/-- The gate's single code map: the emitted 10-instruction program. -/
abbrev cdcvCode (base : Word) : CodeReq := CodeReq.ofProg base cdcvProgram

-- Byte tie: the codegen emits exactly the verified program (no guest-byte
-- change — byte-transparent, no A/B needed).
#guard cdcvProgram.length = 10
theorem cdcv_emit_tie :
    createDeployedCodeValidFunction
      = "create_deployed_code_valid:\n" ++ emitProgram cdcvProgram := rfl

/-- **`create_deployed_code_valid` via the forward-join combinator.**
    8 steps from `base`; both shared tails proven once; genuine validity
    post. -/
theorem cdcvJoin_spec (base ret codePtr len v5old v6old dwordAddr wordVal : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (haptr : alignToDword (codePtr + signExtend12 (0 : BitVec 12)) = dwordAddr)
    (hvptr : isValidByteAccess (codePtr + signExtend12 (0 : BitVec 12)) = true) :
    cpsTripleWithin 8 base ret (cdcvCode base)
      ((.x10 ↦ᵣ codePtr) ** (.x11 ↦ᵣ len) ** (.x5 ↦ᵣ v5old) ** (.x6 ↦ᵣ v6old) **
        (.x0 ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret) ** (dwordAddr ↦ₘ wordVal))
      ((.x10 ↦ᵣ (if BitVec.ult (32768 : Word) len then (1 : Word)
                 else if len = (0 : Word) then (0 : Word)
                 else if (extractByte wordVal
                     (byteOffset (codePtr + signExtend12 (0 : BitVec 12)))).zeroExtend 64
                     = (0xEF : Word) then (1 : Word) else (0 : Word))) **
        (.x11 ↦ᵣ len) ** regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ ret) ** (dwordAddr ↦ₘ wordVal)) := by
  set byte0 := (extractByte wordVal
    (byteOffset (codePtr + signExtend12 (0 : BitVec 12)))).zeroExtend 64 with hbyte0
  -- ---- the two shared return tails, proven ONCE each ----
  -- The frame both tails see (scratch already released to ownership).
  set Ptail : Assertion := ((.x11 ↦ᵣ len) ** regOwn .x5 ** regOwn .x6 **
    (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) with hPtail
  have hPtailF : Ptail.pcFree := by rw [hPtail]; pcf
  have hvalTail := sharedRetTail_spec (cdcvCode base) (base + 24) ret .x10
    (0 : Word) codePtr Ptail hPtailF (by decide) halign
    (CodeReq.ofProg_mono_sub base (base + 24) cdcvProgram [.LI .x10 (0 : Word)] 6
      (by bv_omega) (by decide) (by decide) (by decide))
    (CodeReq.ofProg_mono_sub base (base + 24 + 4) cdcvProgram [.JALR .x0 .x1 0] 7
      (by bv_omega) (by decide) (by decide) (by decide))
  have hinvTail := sharedRetTail_spec (cdcvCode base) (base + 32) ret .x10
    (1 : Word) codePtr Ptail hPtailF (by decide) halign
    (CodeReq.ofProg_mono_sub base (base + 32) cdcvProgram [.LI .x10 (1 : Word)] 8
      (by bv_omega) (by decide) (by decide) (by decide))
    (CodeReq.ofProg_mono_sub base (base + 32 + 4) cdcvProgram [.JALR .x0 .x1 0] 9
      (by bv_omega) (by decide) (by decide) (by decide))
  -- ---- station 3: `beq x6, x5, +12` at base+20 (0xEF check) ----
  have hbr3 := cpsBranchWithin_frameR
    ((.x10 ↦ᵣ codePtr) ** (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)) **
      ((.x1 : Reg) ↦ᵣ ret) ** (dwordAddr ↦ₘ wordVal)) (by pcf)
    (cpsBranchWithin_extend_code
      (h := beq_spec_gen_within .x6 .x5 (12 : BitVec 13) byte0 (0xEF : Word) (base + 20))
      (hmono := CodeReq.ofProg_mono_sub base (base + 20) cdcvProgram
        [.BEQ .x6 .x5 (12 : BitVec 13)] 5 (by bv_omega) (by decide) (by decide) (by decide)))
  rw [show (base + 20 : Word) + signExtend13 (12 : BitVec 13) = base + 32 from by
        rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega,
      show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hbr3
  have hstation3 : cpsTripleWithin 3 (base + 20) ret (cdcvCode base)
      ((.x6 ↦ᵣ byte0) ** (.x5 ↦ᵣ (0xEF : Word)) ** (.x10 ↦ᵣ codePtr) **
        (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret) **
        (dwordAddr ↦ₘ wordVal))
      ((.x10 ↦ᵣ (if byte0 = (0xEF : Word) then (1 : Word) else (0 : Word))) **
        ((.x1 : Reg) ↦ᵣ ret) ** Ptail) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
      (retJoinStation_spec (PT := (.x5 ↦ᵣ (0xEF : Word)) ** (.x6 ↦ᵣ byte0) **
          (.x10 ↦ᵣ codePtr) ** ((.x1 : Reg) ↦ᵣ ret) ** (.x11 ↦ᵣ len) **
          (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
        (PF := (.x5 ↦ᵣ (0xEF : Word)) ** (.x6 ↦ᵣ byte0) **
          (.x10 ↦ᵣ codePtr) ** ((.x1 : Reg) ↦ᵣ ret) ** (.x11 ↦ᵣ len) **
          (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
        hbr3
        (fun h hq => by xperm_hyp hq)
        (fun h hq => by xperm_hyp hq)
        (fun hc => cpsTripleWithin_weaken
          (fun h hp => by
            rw [hPtail]
            have hp2 := sepConj_mono (regIs_to_regOwn .x5 _)
              (sepConj_mono (regIs_to_regOwn .x6 _) (fun _ hh => hh)) h hp
            xperm_hyp hp2)
          (fun h hq => by rw [if_pos hc]; rw [hPtail]; xperm_hyp hq)
          hinvTail)
        (fun hc => cpsTripleWithin_weaken
          (fun h hp => by
            rw [hPtail]
            have hp2 := sepConj_mono (regIs_to_regOwn .x5 _)
              (sepConj_mono (regIs_to_regOwn .x6 _) (fun _ hh => hh)) h hp
            xperm_hyp hp2)
          (fun h hq => by rw [if_neg hc]; rw [hPtail]; xperm_hyp hq)
          hvalTail))
  -- ---- the byte-check segment: `lbu x6, 0(x10) ; li x5, 0xEF` ----
  have hlbu := cpsTripleWithin_extend_code
    (h := lbu_spec_gen_within .x6 .x10 codePtr v6old (0 : BitVec 12) (base + 12)
      dwordAddr wordVal (by decide) haptr hvptr)
    (hmono := CodeReq.ofProg_mono_sub base (base + 12) cdcvProgram
      [.LBU .x6 .x10 (0 : BitVec 12)] 3 (by bv_omega) (by decide) (by decide) (by decide))
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hlbu
  have hlbuF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ len) ** (.x5 ↦ᵣ (32768 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      ((.x1 : Reg) ↦ᵣ ret)) (by pcf) hlbu
  have hli5 := cpsTripleWithin_extend_code
    (h := li_spec_gen_within .x5 (32768 : Word) (0xEF : Word) (base + 16) (by decide))
    (hmono := CodeReq.ofProg_mono_sub base (base + 16) cdcvProgram
      [.LI .x5 (0xEF : Word)] 4 (by bv_omega) (by decide) (by decide) (by decide))
  rw [show (base + 16 : Word) + 4 = base + 20 from by bv_omega] at hli5
  have hli5F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ codePtr) ** (.x11 ↦ᵣ len) ** (.x6 ↦ᵣ byte0) ** (.x0 ↦ᵣ (0 : Word)) **
      ((.x1 : Reg) ↦ᵣ ret) ** (dwordAddr ↦ₘ wordVal)) (by pcf) hli5
  have hseg := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hlbuF hli5F
  have hchain3 : cpsTripleWithin 5 (base + 12) ret (cdcvCode base)
      ((.x10 ↦ᵣ codePtr) ** (.x11 ↦ᵣ len) ** (.x5 ↦ᵣ (32768 : Word)) **
        (.x6 ↦ᵣ v6old) ** (.x0 ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret) **
        (dwordAddr ↦ₘ wordVal))
      ((.x10 ↦ᵣ (if byte0 = (0xEF : Word) then (1 : Word) else (0 : Word))) **
        ((.x1 : Reg) ↦ᵣ ret) ** Ptail) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
      (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
        hseg hstation3)
  -- ---- station 2: `beq x11, x0, +16` at base+8 (empty code is valid) ----
  have hbr2 := cpsBranchWithin_frameR
    ((.x10 ↦ᵣ codePtr) ** (.x5 ↦ᵣ (32768 : Word)) ** (.x6 ↦ᵣ v6old) **
      ((.x1 : Reg) ↦ᵣ ret) ** (dwordAddr ↦ₘ wordVal)) (by pcf)
    (cpsBranchWithin_extend_code
      (h := beq_spec_gen_within .x11 .x0 (16 : BitVec 13) len (0 : Word) (base + 8))
      (hmono := CodeReq.ofProg_mono_sub base (base + 8) cdcvProgram
        [.BEQ .x11 .x0 (16 : BitVec 13)] 2 (by bv_omega) (by decide) (by decide) (by decide)))
  rw [show (base + 8 : Word) + signExtend13 (16 : BitVec 13) = base + 24 from by
        rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
      show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at hbr2
  have hstation2 : cpsTripleWithin 6 (base + 8) ret (cdcvCode base)
      ((.x11 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ codePtr) **
        (.x5 ↦ᵣ (32768 : Word)) ** (.x6 ↦ᵣ v6old) ** ((.x1 : Reg) ↦ᵣ ret) **
        (dwordAddr ↦ₘ wordVal))
      ((.x10 ↦ᵣ (if len = (0 : Word) then (0 : Word)
                 else if byte0 = (0xEF : Word) then (1 : Word) else (0 : Word))) **
        ((.x1 : Reg) ↦ᵣ ret) ** Ptail) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
      (retJoinStation_spec (PT := (.x5 ↦ᵣ (32768 : Word)) ** (.x6 ↦ᵣ v6old) **
          (.x10 ↦ᵣ codePtr) ** ((.x1 : Reg) ↦ᵣ ret) ** (.x11 ↦ᵣ len) **
          (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
        (PF := (.x10 ↦ᵣ codePtr) ** (.x11 ↦ᵣ len) ** (.x5 ↦ᵣ (32768 : Word)) **
          (.x6 ↦ᵣ v6old) ** (.x0 ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret) **
          (dwordAddr ↦ₘ wordVal))
        hbr2
        (fun h hq => by xperm_hyp hq)
        (fun h hq => by xperm_hyp hq)
        (fun hc => cpsTripleWithin_mono_nSteps (by omega)
          (cpsTripleWithin_weaken
            (fun h hp => by
              rw [hPtail]
              have hp2 := sepConj_mono (regIs_to_regOwn .x5 _)
                (sepConj_mono (regIs_to_regOwn .x6 _) (fun _ hh => hh)) h hp
              xperm_hyp hp2)
            (fun h hq => by rw [if_pos hc]; rw [hPtail]; xperm_hyp hq)
            hvalTail))
        (fun hc => cpsTripleWithin_weaken
          (fun h hp => by xperm_hyp hp)
          (fun h hq => by rw [if_neg hc]; exact hq)
          hchain3))
  -- ---- station 1: `bltu x5, x11, +28` at base+4 (size gate) ----
  have hbr1 := cpsBranchWithin_frameR
    ((.x10 ↦ᵣ codePtr) ** (.x6 ↦ᵣ v6old) ** (.x0 ↦ᵣ (0 : Word)) **
      ((.x1 : Reg) ↦ᵣ ret) ** (dwordAddr ↦ₘ wordVal)) (by pcf)
    (cpsBranchWithin_extend_code
      (h := bltu_spec_gen_within .x5 .x11 (28 : BitVec 13) (32768 : Word) len (base + 4))
      (hmono := CodeReq.ofProg_mono_sub base (base + 4) cdcvProgram
        [.BLTU .x5 .x11 (28 : BitVec 13)] 1 (by bv_omega) (by decide) (by decide) (by decide)))
  rw [show (base + 4 : Word) + signExtend13 (28 : BitVec 13) = base + 32 from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega,
      show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hbr1
  have hstation1 : cpsTripleWithin 7 (base + 4) ret (cdcvCode base)
      ((.x5 ↦ᵣ (32768 : Word)) ** (.x11 ↦ᵣ len) ** (.x10 ↦ᵣ codePtr) **
        (.x6 ↦ᵣ v6old) ** (.x0 ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret) **
        (dwordAddr ↦ₘ wordVal))
      ((.x10 ↦ᵣ (if BitVec.ult (32768 : Word) len then (1 : Word)
                 else if len = (0 : Word) then (0 : Word)
                 else if byte0 = (0xEF : Word) then (1 : Word) else (0 : Word))) **
        ((.x1 : Reg) ↦ᵣ ret) ** Ptail) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
      (retJoinStation_spec (PT := (.x5 ↦ᵣ (32768 : Word)) ** (.x6 ↦ᵣ v6old) **
          (.x10 ↦ᵣ codePtr) ** ((.x1 : Reg) ↦ᵣ ret) ** (.x11 ↦ᵣ len) **
          (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
        (PF := (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ codePtr) **
          (.x5 ↦ᵣ (32768 : Word)) ** (.x6 ↦ᵣ v6old) ** ((.x1 : Reg) ↦ᵣ ret) **
          (dwordAddr ↦ₘ wordVal))
        hbr1
        (fun h hq => by xperm_hyp hq)
        (fun h hq => by xperm_hyp hq)
        (fun hc => cpsTripleWithin_mono_nSteps (by omega)
          (cpsTripleWithin_weaken
            (fun h hp => by
              rw [hPtail]
              have hp2 := sepConj_mono (regIs_to_regOwn .x5 _)
                (sepConj_mono (regIs_to_regOwn .x6 _) (fun _ hh => hh)) h hp
              xperm_hyp hp2)
            (fun h hq => by rw [if_pos hc]; rw [hPtail]; xperm_hyp hq)
            hinvTail))
        (fun hc => cpsTripleWithin_weaken
          (fun h hp => by xperm_hyp hp)
          (fun h hq => by rw [if_neg hc]; exact hq)
          hstation2))
  -- ---- prologue: `li x5, 32768` at base ----
  have hpro := cpsTripleWithin_extend_code
    (h := li_spec_gen_within .x5 v5old (32768 : Word) base (by decide))
    (hmono := CodeReq.ofProg_mono_sub base base cdcvProgram
      [.LI .x5 (32768 : Word)] 0 (by bv_omega) (by decide) (by decide) (by decide))
  have hproF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ codePtr) ** (.x11 ↦ᵣ len) ** (.x6 ↦ᵣ v6old) ** (.x0 ↦ᵣ (0 : Word)) **
      ((.x1 : Reg) ↦ᵣ ret) ** (dwordAddr ↦ₘ wordVal)) (by pcf) hpro
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hproF hstation1
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => ?_) hall
  rw [hPtail] at hq
  xperm_hyp hq

#print axioms cdcvJoin_spec
#print axioms EvmAsm.Rv64.SAsm.retJoinStation_spec
#print axioms EvmAsm.Rv64.SAsm.sharedRetTail_spec

end CreateDeployedCodeValidSAsm
end EvmAsm.Codegen
