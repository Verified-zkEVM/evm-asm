/-
  EvmAsm.Codegen.Programs.CallFrameBaseSAsm

  `frame_base` via the **structured-layer AUIPC bridge**
  (`EvmAsm/Rv64/SAsm/BlockAtBridge.lean`, bead evm-asm-4ch8f.56.7 /
  4ch8f.56.7.1) — the acceptance consumer.

  The emitted leaf is the 6-instruction block
  `[ADDI, LUI, MUL, AUIPC, ADDI, ADD]` + `ret`: the `AUIPC`/`ADDI` pair
  materializes `call_frame_arena` (the `la` idiom the PC-agnostic
  `blockOk`/`Stmt.sound` path cannot consume).  The block is proven through
  the PC-threaded `execBlockAt` engine via `blockAt_regs_spec`, with the
  materialized address PROVEN by `la_resolve` — the emitter-side
  `Codegen.laHi/laLo` immediates are kernel-checked equal to the psABI
  `Rv64.laHi/laLo` at this displacement, and only the decidable
  `laInRange` representability remains.

  **Genuine post** (`frameBase_spec`, at the `#guard`-tied
  `GuestAddrs.frame_base`): `a0 = call_frame_arena + (depth − 1) ·
  FRAME_STRIDE` — the real frame-base arithmetic of the call-frame layout
  (`FRAME_STRIDE = 0x39000`).  Byte-transparent: the spec is stated
  directly over the emitted `frameBase_prog`.
-/

import EvmAsm.Codegen.Programs.CallFrameBase
import EvmAsm.Rv64.SAsm.BlockAtBridge
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace CallFrameBaseSAsm

/-- The 5-instruction body (everything but the `ret`).

    ⚠️ Was six, with a leading `ADDI x5, x10, -1`.  The `depth-1` skew is gone: depth 0
    now indexes slot 0 (GH #10938 preparation), so the multiply takes `x10` directly and
    the `la` moved from PC offset 12 to 8.  Keep this in lockstep with
    `CallFrameBase.frameBase_prog`; the `rfl` tie below is what catches a drift. -/
def fbBlock : List Instr :=
  [ .LUI .x6 (25 : BitVec 20),
    .MUL .x5 .x10 .x6,
    .AUIPC .x6 (laHi GuestAddrs.call_frame_arena (GuestAddrs.frame_base + 8)),
    .ADDI .x6 .x6 (laLo GuestAddrs.call_frame_arena (GuestAddrs.frame_base + 8)),
    .ADD .x10 .x6 .x5 ]

/-- Byte tie (kernel-checked): the emitted program IS the bridged block
    plus the `ret`. -/
theorem frameBase_prog_tie :
    frameBase_prog = fbBlock ++ [.JALR .x0 .x1 (0 : BitVec 12)] := rfl

/-- The emitter's reloc immediates ARE the psABI `%pcrel_hi`/`%pcrel_lo`
    of the `la` resolution model at this pc/target (kernel-checked), so the
    materialized address is `la_resolve`-proven. -/
theorem fb_laHi_agree :
    laHi GuestAddrs.call_frame_arena (GuestAddrs.frame_base + 8)
      = EvmAsm.Rv64.laHi ((GuestAddrs.frame_base + 8) : Word) (GuestAddrs.call_frame_arena : Word) := by decide

theorem fb_laLo_agree :
    laLo GuestAddrs.call_frame_arena (GuestAddrs.frame_base + 8)
      = EvmAsm.Rv64.laLo ((GuestAddrs.frame_base + 8) : Word) (GuestAddrs.call_frame_arena : Word) := by decide

/-- The `AUIPC`/`ADDI` arithmetic, PROVEN via `la_resolve` (only the
    decidable `laInRange` representability is discharged). -/
theorem fb_la_resolved :
    ((GuestAddrs.frame_base + 8) : Word)
      + (((laHi GuestAddrs.call_frame_arena (GuestAddrs.frame_base + 8)).zeroExtend 32
          : BitVec 32) <<< 12).signExtend 64
      + signExtend12 (laLo GuestAddrs.call_frame_arena (GuestAddrs.frame_base + 8))
      = (GuestAddrs.call_frame_arena : Word) := by
  rw [fb_laHi_agree, fb_laLo_agree]
  exact la_resolve ((GuestAddrs.frame_base + 8) : Word) (GuestAddrs.call_frame_arena : Word) (by decide)

/-- Every exposed register except the argument/result `a0`. -/
def fbRest : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- **`frame_base` at its linked address** (genuine post): returns
    `a0 = call_frame_arena + depth · 0x19000`, the call-frame layout
    arithmetic, with the arena address `la_resolve`-proven. -/
theorem frameBase_spec (depth ret : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 6 (GuestAddrs.frame_base : Word) ret
      (CodeReq.ofProg (GuestAddrs.frame_base : Word) frameBase_prog)
      (((.x10 : Reg) ↦ᵣ depth) ** ((.x1 : Reg) ↦ᵣ ret) ** regOwns fbRest)
      (((.x10 : Reg) ↦ᵣ ((GuestAddrs.call_frame_arena : Word) + depth * (0x19000 : Word))) **
        ((.x1 : Reg) ↦ᵣ ret) ** regOwns fbRest) := by
  -- peel the scratch file
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns fbRest (by decide)
      (P := ((.x10 : Reg) ↦ᵣ depth) ** ((.x1 : Reg) ↦ᵣ ret)) (fun vf => ?_))
  -- the register file entering the block
  set rf : RegFile := (fun r => if r = .x10 then depth else vf r) with hrf
  -- ---- the 6-instruction block, through the PC-threaded bridge ----
  have hblk := cpsTripleWithin_extend_code
    (hmono := CodeReq.ofProg_mono_sub (GuestAddrs.frame_base : Word) (GuestAddrs.frame_base : Word)
      frameBase_prog fbBlock 0 (by decide) (by decide) (by decide) (by decide))
    (blockAt_regs_spec fbBlock rf (GuestAddrs.frame_base : Word)
      (by decide) (by decide) (by decide))
  rw [show (GuestAddrs.frame_base : Word) + BitVec.ofNat 64 (4 * fbBlock.length)
        = ((GuestAddrs.frame_base + 20) : Word) from by decide] at hblk
  -- ---- the engine image as an explicit set-chain ----
  set rf' := (execBlockAt Region.empty RwRegion.empty.base (GuestAddrs.frame_base : Word)
    rf [] fbBlock).1 with hrf'
  set s2 := rf.set .x6
    ((((25 : BitVec 20)).zeroExtend 32 <<< 12).signExtend 64) with hs2
  set s3 := s2.set .x5 (s2.get .x10 * s2.get .x6) with hs3
  set s4 := s3.set .x6 (((GuestAddrs.frame_base + 8) : Word)
    + (((laHi GuestAddrs.call_frame_arena (GuestAddrs.frame_base + 8)).zeroExtend 32
        : BitVec 32) <<< 12).signExtend 64) with hs4
  set s5 := s4.set .x6 (s4.get .x6
    + signExtend12 (laLo GuestAddrs.call_frame_arena (GuestAddrs.frame_base + 8))) with hs5
  set s6 := s5.set .x10 (s5.get .x6 + s5.get .x5) with hs6
  have hrf'eq : rf' = s6 := rfl
  -- arithmetic facts
  have hstride : (((25 : BitVec 20)).zeroExtend 32 <<< 12).signExtend 64
      = (0x19000 : Word) := by decide
  -- per-register values of the image
  have g10 : rf.get .x10 = depth := rfl
  have g10s2 : s2.get .x10 = depth := by
    rw [hs2, RegFile.get_set_ne _ _ _ _ (by decide), g10]
  have g6s2 : s2.get .x6
      = (((25 : BitVec 20)).zeroExtend 32 <<< 12).signExtend 64 := by
    rw [hs2, RegFile.get_set_self _ _ _ (by decide)]
  have g5s5 : s5.get .x5 = depth * (0x19000 : Word) := by
    rw [hs5, RegFile.get_set_ne _ _ _ _ (by decide), hs4,
      RegFile.get_set_ne _ _ _ _ (by decide), hs3,
      RegFile.get_set_self _ _ _ (by decide), g10s2, g6s2, hstride]
  have g6s5 : s5.get .x6 = (GuestAddrs.call_frame_arena : Word) := by
    rw [hs5, RegFile.get_set_self _ _ _ (by decide), hs4,
      RegFile.get_set_self _ _ _ (by decide)]
    exact fb_la_resolved
  have g10s6 : s6.get .x10
      = (GuestAddrs.call_frame_arena : Word) + depth * (0x19000 : Word) := by
    rw [hs6, RegFile.get_set_self _ _ _ (by decide), g6s5, g5s5]
  -- assemble the valuation equality over the exposed file
  have hvals : ∀ r ∈ exposedRegs, rf' r = ((fun r => if r = .x10 then (GuestAddrs.call_frame_arena : Word) + depth * (0x19000 : Word)
          else if r = .x5 then depth * (0x19000 : Word)
          else if r = .x6 then (GuestAddrs.call_frame_arena : Word)
          else vf r)) r := by
    have hraw : ∀ r : Reg, r ≠ .x0 → rf' r = rf'.get r := by
      intro r hr
      rw [RegFile.get, if_neg hr]
    intro r hr
    fin_cases hr
    · -- x5
      rw [hraw _ (by decide), hrf'eq, hs6,
        RegFile.get_set_ne _ _ _ _ (by decide)]
      exact g5s5
    · -- x6
      rw [hraw _ (by decide), hrf'eq, hs6,
        RegFile.get_set_ne _ _ _ _ (by decide)]
      exact g6s5
    · -- x7
      rw [hraw _ (by decide), hrf'eq, hs6,
        RegFile.get_set_ne _ _ _ _ (by decide), hs5,
        RegFile.get_set_ne _ _ _ _ (by decide), hs4,
        RegFile.get_set_ne _ _ _ _ (by decide), hs3,
        RegFile.get_set_ne _ _ _ _ (by decide), hs2,
        RegFile.get_set_ne _ _ _ _ (by decide)]
      rfl
    · -- x28
      rw [hraw _ (by decide), hrf'eq, hs6,
        RegFile.get_set_ne _ _ _ _ (by decide), hs5,
        RegFile.get_set_ne _ _ _ _ (by decide), hs4,
        RegFile.get_set_ne _ _ _ _ (by decide), hs3,
        RegFile.get_set_ne _ _ _ _ (by decide), hs2,
        RegFile.get_set_ne _ _ _ _ (by decide)]
      rfl
    · -- x29
      rw [hraw _ (by decide), hrf'eq, hs6,
        RegFile.get_set_ne _ _ _ _ (by decide), hs5,
        RegFile.get_set_ne _ _ _ _ (by decide), hs4,
        RegFile.get_set_ne _ _ _ _ (by decide), hs3,
        RegFile.get_set_ne _ _ _ _ (by decide), hs2,
        RegFile.get_set_ne _ _ _ _ (by decide)]
      rfl
    · -- x30
      rw [hraw _ (by decide), hrf'eq, hs6,
        RegFile.get_set_ne _ _ _ _ (by decide), hs5,
        RegFile.get_set_ne _ _ _ _ (by decide), hs4,
        RegFile.get_set_ne _ _ _ _ (by decide), hs3,
        RegFile.get_set_ne _ _ _ _ (by decide), hs2,
        RegFile.get_set_ne _ _ _ _ (by decide)]
      rfl
    · -- x31
      rw [hraw _ (by decide), hrf'eq, hs6,
        RegFile.get_set_ne _ _ _ _ (by decide), hs5,
        RegFile.get_set_ne _ _ _ _ (by decide), hs4,
        RegFile.get_set_ne _ _ _ _ (by decide), hs3,
        RegFile.get_set_ne _ _ _ _ (by decide), hs2,
        RegFile.get_set_ne _ _ _ _ (by decide)]
      rfl
    · -- x10
      rw [hraw _ (by decide), hrf'eq]
      exact g10s6
    · -- x11
      rw [hraw _ (by decide), hrf'eq, hs6,
        RegFile.get_set_ne _ _ _ _ (by decide), hs5,
        RegFile.get_set_ne _ _ _ _ (by decide), hs4,
        RegFile.get_set_ne _ _ _ _ (by decide), hs3,
        RegFile.get_set_ne _ _ _ _ (by decide), hs2,
        RegFile.get_set_ne _ _ _ _ (by decide)]
      rfl
    · -- x12
      rw [hraw _ (by decide), hrf'eq, hs6,
        RegFile.get_set_ne _ _ _ _ (by decide), hs5,
        RegFile.get_set_ne _ _ _ _ (by decide), hs4,
        RegFile.get_set_ne _ _ _ _ (by decide), hs3,
        RegFile.get_set_ne _ _ _ _ (by decide), hs2,
        RegFile.get_set_ne _ _ _ _ (by decide)]
      rfl
    · -- x13
      rw [hraw _ (by decide), hrf'eq, hs6,
        RegFile.get_set_ne _ _ _ _ (by decide), hs5,
        RegFile.get_set_ne _ _ _ _ (by decide), hs4,
        RegFile.get_set_ne _ _ _ _ (by decide), hs3,
        RegFile.get_set_ne _ _ _ _ (by decide), hs2,
        RegFile.get_set_ne _ _ _ _ (by decide)]
      rfl
    · -- x14
      rw [hraw _ (by decide), hrf'eq, hs6,
        RegFile.get_set_ne _ _ _ _ (by decide), hs5,
        RegFile.get_set_ne _ _ _ _ (by decide), hs4,
        RegFile.get_set_ne _ _ _ _ (by decide), hs3,
        RegFile.get_set_ne _ _ _ _ (by decide), hs2,
        RegFile.get_set_ne _ _ _ _ (by decide)]
      rfl
    · -- x15
      rw [hraw _ (by decide), hrf'eq, hs6,
        RegFile.get_set_ne _ _ _ _ (by decide), hs5,
        RegFile.get_set_ne _ _ _ _ (by decide), hs4,
        RegFile.get_set_ne _ _ _ _ (by decide), hs3,
        RegFile.get_set_ne _ _ _ _ (by decide), hs2,
        RegFile.get_set_ne _ _ _ _ (by decide)]
      rfl
    · -- x16
      rw [hraw _ (by decide), hrf'eq, hs6,
        RegFile.get_set_ne _ _ _ _ (by decide), hs5,
        RegFile.get_set_ne _ _ _ _ (by decide), hs4,
        RegFile.get_set_ne _ _ _ _ (by decide), hs3,
        RegFile.get_set_ne _ _ _ _ (by decide), hs2,
        RegFile.get_set_ne _ _ _ _ (by decide)]
      rfl
    · -- x17
      rw [hraw _ (by decide), hrf'eq, hs6,
        RegFile.get_set_ne _ _ _ _ (by decide), hs5,
        RegFile.get_set_ne _ _ _ _ (by decide), hs4,
        RegFile.get_set_ne _ _ _ _ (by decide), hs3,
        RegFile.get_set_ne _ _ _ _ (by decide), hs2,
        RegFile.get_set_ne _ _ _ _ (by decide)]
      rfl
  -- rewrite the engine post to the explicit valuation
  have hpost : regAtoms rf' exposedRegs
      = regAtomsOf ((fun r => if r = .x10 then (GuestAddrs.call_frame_arena : Word) + depth * (0x19000 : Word)
          else if r = .x5 then depth * (0x19000 : Word)
          else if r = .x6 then (GuestAddrs.call_frame_arena : Word)
          else vf r)) exposedRegs := by
    rw [regAtoms_eq_regAtomsOf rf' exposedRegs (by decide)]
    exact regAtomsOf_congr _ _ exposedRegs hvals
  rw [hpost] at hblk
  -- ---- the ret ----
  have hret := liftCode (cr' := CodeReq.ofProg (GuestAddrs.frame_base : Word) frameBase_prog)
    (EvmAsm.Evm64.ret_spec_within' ((GuestAddrs.frame_base + 20) : Word) ret)
    (by code_mem)
  rw [halign] at hret
  -- ---- frames + chain ----
  have hblkF := cpsTripleWithin_frameR (((.x1 : Reg) ↦ᵣ ret)) (by pcf) hblk
  have hretF := cpsTripleWithin_frameR
    (regAtomsOf ((fun r => if r = .x10 then (GuestAddrs.call_frame_arena : Word) + depth * (0x19000 : Word)
          else if r = .x5 then depth * (0x19000 : Word)
          else if r = .x6 then (GuestAddrs.call_frame_arena : Word)
          else vf r)) exposedRegs)
    (pcFree_regAtomsOf _ _) hret
  have hc := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hblkF hretF
  -- ---- final glue: pack the pre, unpack + own-ify the post ----
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hc
  · -- (x10 ↦ depth) ** (x1 ↦ ret) ** regAtomsOf vf fbRest
    --   → (regAtoms rf exposedRegs) ** (x1 ↦ ret)
    have hpre : regAtoms rf exposedRegs
        = regAtomsOf (fun r => if r = .x10 then depth else vf r) exposedRegs := by
      rw [regAtoms_eq_regAtomsOf rf exposedRegs (by decide)]
    rw [hpre]
    simp only [exposedRegs, fbRest, regAtomsOf_cons, regAtomsOf_nil,
      sepConj_emp_right'] at hp ⊢
    simp only [show (Reg.x5 = Reg.x10) = False from by simp,
      show (Reg.x6 = Reg.x10) = False from by simp,
      show (Reg.x7 = Reg.x10) = False from by simp,
      show (Reg.x28 = Reg.x10) = False from by simp,
      show (Reg.x29 = Reg.x10) = False from by simp,
      show (Reg.x30 = Reg.x10) = False from by simp,
      show (Reg.x31 = Reg.x10) = False from by simp,
      show (Reg.x11 = Reg.x10) = False from by simp,
      show (Reg.x12 = Reg.x10) = False from by simp,
      show (Reg.x13 = Reg.x10) = False from by simp,
      show (Reg.x14 = Reg.x10) = False from by simp,
      show (Reg.x15 = Reg.x10) = False from by simp,
      show (Reg.x16 = Reg.x10) = False from by simp,
      show (Reg.x17 = Reg.x10) = False from by simp,
      if_true, if_false] at hp ⊢
    xperm_hyp hp
  · -- engine-post atoms → (x10 ↦ result) ** (x1 ↦ ret) ** regOwns fbRest
    have hq1 : ((((.x10 : Reg) ↦ᵣ ((GuestAddrs.call_frame_arena : Word) + depth * (0x19000 : Word))) **
        ((.x1 : Reg) ↦ᵣ ret)) **
        regAtomsOf ((fun r => if r = .x10 then (GuestAddrs.call_frame_arena : Word) + depth * (0x19000 : Word)
          else if r = .x5 then depth * (0x19000 : Word)
          else if r = .x6 then (GuestAddrs.call_frame_arena : Word)
          else vf r)) fbRest) h := by
      simp only [exposedRegs, fbRest, regAtomsOf_cons, regAtomsOf_nil,
        sepConj_emp_right', reduceIte] at hq ⊢
      xperm_hyp hq
    have hq2 := sepConj_mono_right (regAtomsOf_to_regOwns _ fbRest) h hq1
    xperm_hyp hq2


end CallFrameBaseSAsm
end EvmAsm.Codegen
