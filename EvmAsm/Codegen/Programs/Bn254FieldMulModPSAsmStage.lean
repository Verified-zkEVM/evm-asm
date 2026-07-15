/-
  EvmAsm.Codegen.Programs.Bn254FieldMulModPSAsmStage

  Split out of `Bn254FieldMulModPSAsm.lean` (file-size guardrail): the
  staging infrastructure for `bnf_mul_mod_p` — the emitted routine
  (`mulBody`/`mulFrame`/`mulProg_tie`), its code map (`mulCr`), the two
  converter-callee focused adapters (`bnfBeToLeFlat_spec` /
  `bnfLeToBeFlat_spec`), the inline CSR-2050 arithMod step
  (`csrsStep_spec`), and the accumulated-splice `stageC_spec`.  The
  capstone `bnfMulModP_spec` lives in `Bn254FieldMulModPSAsm`, which
  imports this file.  See that file's header for the full design notes.
-/

import EvmAsm.Codegen.Programs.Bn254Field
import EvmAsm.Codegen.Programs.Bn254FieldConvSAsm
import EvmAsm.Codegen.Programs.Bn254FieldConvSAsmLeToBe
import EvmAsm.Rv64.SAsm.RwSubwindow
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.LaResolve
import EvmAsm.Crypto.PowLadder

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

namespace Bn254FieldMulModPSAsm

open Bn254FieldConvSAsm (bnfBeToLeFn bnfBeToLeFn_spec bnfLeToBeFn bnfLeToBeFn_spec)

/-- The arena base (`bnf_le_a`) and its 232-byte extent
    (`_a/_b/_d/_zero/_one/_p` 32-byte cells + the 40-byte `mul_params`). -/
def arenaB : Word := 0xa3000ee0

/-- The frame and body of the emitted routine. -/
def mulFrame : FrameDesc := [(.x1, 0), (.x8, 8), (.x9, 16)]

def mulBody : List Instr :=
  [ .MV .x8 .x11,
    .MV .x9 .x12,
    .AUIPC .x11 (laHi GuestAddrs.bnf_le_a (GuestAddrs.bnf_mul_mod_p + 24)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bnf_le_a (GuestAddrs.bnf_mul_mod_p + 24)),
    .JAL .x1 (jalOff GuestAddrs.bnf_be_to_le (GuestAddrs.bnf_mul_mod_p + 32)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bnf_le_b (GuestAddrs.bnf_mul_mod_p + 40)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bnf_le_b (GuestAddrs.bnf_mul_mod_p + 40)),
    .JAL .x1 (jalOff GuestAddrs.bnf_be_to_le (GuestAddrs.bnf_mul_mod_p + 48)),
    .AUIPC .x5 (laHi GuestAddrs.bnf_mul_params (GuestAddrs.bnf_mul_mod_p + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bnf_mul_params (GuestAddrs.bnf_mul_mod_p + 52)),
    .CSRS (2050 : BitVec 12) .x5,
    .AUIPC .x10 (laHi GuestAddrs.bnf_le_d (GuestAddrs.bnf_mul_mod_p + 64)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bnf_le_d (GuestAddrs.bnf_mul_mod_p + 64)),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.bnf_le_to_be (GuestAddrs.bnf_mul_mod_p + 76)),
    .LI .x10 (0 : Word) ]

/-- Byte tie (kernel-checked): the emitted routine IS the ABI frame over
    the body — byte-transparent, no A/B. -/
theorem mulProg_tie :
    abiFrameProg (-32 : BitVec 12) (32 : BitVec 12) mulFrame mulBody
      = bnfMulModP_prog := rfl

/-- The routine's single code map: its own program plus the two converter
    callees'. -/
def mulCr : CodeReq :=
  (CodeReq.ofProg (GuestAddrs.bnf_mul_mod_p : Word) bnfMulModP_prog).union
    ((CodeReq.ofProg (GuestAddrs.bnf_be_to_le : Word) bnfBeToLe_prog).union
      (CodeReq.ofProg (GuestAddrs.bnf_le_to_be : Word) bnfLeToBe_prog))

/-- The exposed registers the converter contracts clobber beyond `a0`/`a1`. -/
def convScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split2 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** regAtomsOf vf convScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [convScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_convScratch : (.x10 : Reg) ∉ convScratch := by decide
private theorem x11_notin_convScratch : (.x11 : Reg) ∉ convScratch := by decide

/-- **Flat contract for `bnf_be_to_le`** (adapter-derived, ∃-post: the
    written window's exact bytes are existential, its 256-bit LE decode is
    pinned to the input's BE value). -/
theorem bnfBeToLeFlat_spec (ret srci dsti : Word) (inb ob : List (BitVec 8))
    (hilen : inb.length = 32) (holen : ob.length = 32)
    (hwfR : Region.wf ⟨srci, inb⟩) (hrww : RwRegion.wf ⟨dsti, 32⟩)
    (hso : srci.toNat + 32 < 2 ^ 64) (hdo : dsti.toNat + 32 < 2 ^ 64)
    (hdisj : srci.toNat + 32 ≤ dsti.toNat ∨ dsti.toNat + 32 ≤ srci.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((bnfBeToLeFn srci dsti inb ob).body.steps + 1)
      (GuestAddrs.bnf_be_to_le : Word) ret mulCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ srci) ** (.x11 ↦ᵣ dsti)
        ** regOwns convScratch ** bytesRegion dsti ob ** bytesRegion srci inb)
      (fun hp => ∃ ws',
        ((⌜wsNat256 ws' 0 = beBytesToNat inb ∧ ws'.length = 32⌝
          ** ((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs
          ** bytesRegion dsti ws' ** bytesRegion srci inb)) hp) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns convScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ srci) ** (.x11 ↦ᵣ dsti)
        ** bytesRegion dsti ob ** bytesRegion srci inb)
      (fun vf => ?_))
  have had := Fn.retSpecFlat (bnfBeToLeFn srci dsti inb ob)
    (GuestAddrs.bnf_be_to_le : Word)
    (bnfBeToLeFn_spec srci dsti inb ob hwfR hrww hilen (GuestAddrs.bnf_be_to_le : Word))
    (by show 4 * (19 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then srci else if r = .x11 then dsti else vf r)
    ob
    (by show ob.length = 32; exact holen)
    (by
      refine ⟨?_, ?_, rfl, holen, hilen, hso, hdo, hdisj, rfl⟩
      · show RegFile.get _ .x10 = srci
        rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
        exact if_pos rfl
      · show RegFile.get _ .x11 = dsti
        rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
        rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
        exact if_pos rfl)
    (fun _ _ _ h => h.2.2)
    (Q := fun hp => ∃ ws',
      ((⌜wsNat256 ws' 0 = beBytesToNat inb ∧ ws'.length = 32⌝
        ** regOwns exposedRegs ** bytesRegion dsti ws')) hp)
    (fun rf' ws' hlen' hpost' hp hh => by
      refine ⟨ws', ?_⟩
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
      have hh2 := sepConj_mono_left
        (regAtomsOf_to_regOwns (fun r => rf' r) exposedRegs) hp hh
      have hpure : (⌜wsNat256 ws' 0 = beBytesToNat inb ∧ ws'.length = 32⌝
          ** (regOwns exposedRegs ** bytesRegion dsti ws')) hp :=
        (sepConj_pure_left hp).mpr ⟨⟨hpost'.1, hlen'⟩, hh2⟩
      xperm_hyp hpure)
  rw [show (bnfBeToLeFn srci dsti inb ob).programRet (GuestAddrs.bnf_be_to_le : Word)
      = bnfBeToLe_prog from rfl] at had
  have hadC := liftCode (cr' := mulCr) had (by code_mem)
  rw [show (bnfBeToLeFn srci dsti inb ob).region = (⟨srci, inb⟩ : Region) from rfl,
      show (bnfBeToLeFn srci dsti inb ob).rw.base = dsti from rfl] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split2,
    show (if (Reg.x10 : Reg) = .x10 then srci else
        if (Reg.x10 : Reg) = .x11 then dsti else vf .x10) = srci from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then srci else
        if (Reg.x11 : Reg) = .x11 then dsti else vf .x11) = dsti from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then srci else if r = .x11 then dsti else vf r)
      vf convScratch
      (fun r hr => by
        show (if r = .x10 then srci else if r = .x11 then dsti else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_convScratch (hc ▸ hr)),
            if_neg (fun (hc : r = .x11) => x11_notin_convScratch (hc ▸ hr))])]
    at hadC
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => ?_) hadC
  -- push the frame atoms inside the existential
  have hq1 : ((fun hp => ∃ ws',
      ((⌜wsNat256 ws' 0 = beBytesToNat inb ∧ ws'.length = 32⌝
        ** regOwns exposedRegs ** bytesRegion dsti ws')) hp)
      ** (((.x1 : Reg) ↦ᵣ ret) ** bytesRegion srci inb) : Assertion) h := by
    xperm_hyp hq
  obtain ⟨ws', hin⟩ := (sepConj_exists_left h).mp hq1
  exact ⟨ws', by xperm_hyp hin⟩

/-- **Flat contract for `bnf_le_to_be`** (adapter-derived, ∃-post: the
    output's BE decode is pinned to the LE staging window's value). -/
theorem bnfLeToBeFlat_spec (ret srci dsti : Word) (inb ob : List (BitVec 8))
    (hilen : inb.length = 32) (holen : ob.length = 32)
    (hwfR : Region.wf ⟨srci, inb⟩) (hrww : RwRegion.wf ⟨dsti, 32⟩)
    (hso : srci.toNat + 32 < 2 ^ 64) (hdo : dsti.toNat + 32 < 2 ^ 64)
    (hdisj : srci.toNat + 32 ≤ dsti.toNat ∨ dsti.toNat + 32 ≤ srci.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((bnfLeToBeFn srci dsti inb ob).body.steps + 1)
      (GuestAddrs.bnf_le_to_be : Word) ret mulCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ srci) ** (.x11 ↦ᵣ dsti)
        ** regOwns convScratch ** bytesRegion dsti ob ** bytesRegion srci inb)
      (fun hp => ∃ ws',
        ((⌜beBytesToNat ws' = wsNat256 inb 0 ∧ ws'.length = 32⌝
          ** ((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs
          ** bytesRegion dsti ws' ** bytesRegion srci inb)) hp) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns convScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ srci) ** (.x11 ↦ᵣ dsti)
        ** bytesRegion dsti ob ** bytesRegion srci inb)
      (fun vf => ?_))
  have had := Fn.retSpecFlat (bnfLeToBeFn srci dsti inb ob)
    (GuestAddrs.bnf_le_to_be : Word)
    (bnfLeToBeFn_spec srci dsti inb ob hwfR hrww hilen (GuestAddrs.bnf_le_to_be : Word))
    (by show 4 * (18 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then srci else if r = .x11 then dsti else vf r)
    ob
    (by show ob.length = 32; exact holen)
    (by
      refine ⟨?_, ?_, rfl, holen, hilen, hso, hdo, hdisj, rfl⟩
      · show RegFile.get _ .x10 = srci
        rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
        exact if_pos rfl
      · show RegFile.get _ .x11 = dsti
        rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
        rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
        exact if_pos rfl)
    (fun _ _ _ h => h.2.2)
    (Q := fun hp => ∃ ws',
      ((⌜beBytesToNat ws' = wsNat256 inb 0 ∧ ws'.length = 32⌝
        ** regOwns exposedRegs ** bytesRegion dsti ws')) hp)
    (fun rf' ws' hlen' hpost' hp hh => by
      refine ⟨ws', ?_⟩
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
      have hh2 := sepConj_mono_left
        (regAtomsOf_to_regOwns (fun r => rf' r) exposedRegs) hp hh
      have hpure : (⌜beBytesToNat ws' = wsNat256 inb 0 ∧ ws'.length = 32⌝
          ** (regOwns exposedRegs ** bytesRegion dsti ws')) hp :=
        (sepConj_pure_left hp).mpr ⟨⟨hpost'.1, hlen'⟩, hh2⟩
      xperm_hyp hpure)
  rw [show (bnfLeToBeFn srci dsti inb ob).programRet (GuestAddrs.bnf_le_to_be : Word)
      = bnfLeToBe_prog from rfl] at had
  have hadC := liftCode (cr' := mulCr) had (by code_mem)
  rw [show (bnfLeToBeFn srci dsti inb ob).region = (⟨srci, inb⟩ : Region) from rfl,
      show (bnfLeToBeFn srci dsti inb ob).rw.base = dsti from rfl] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split2,
    show (if (Reg.x10 : Reg) = .x10 then srci else
        if (Reg.x10 : Reg) = .x11 then dsti else vf .x10) = srci from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then srci else
        if (Reg.x11 : Reg) = .x11 then dsti else vf .x11) = dsti from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then srci else if r = .x11 then dsti else vf r)
      vf convScratch
      (fun r hr => by
        show (if r = .x10 then srci else if r = .x11 then dsti else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_convScratch (hc ▸ hr)),
            if_neg (fun (hc : r = .x11) => x11_notin_convScratch (hc ▸ hr))])]
    at hadC
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => ?_) hadC
  have hq1 : ((fun hp => ∃ ws',
      ((⌜beBytesToNat ws' = wsNat256 inb 0 ∧ ws'.length = 32⌝
        ** regOwns exposedRegs ** bytesRegion dsti ws')) hp)
      ** (((.x1 : Reg) ↦ᵣ ret) ** bytesRegion srci inb) : Assertion) h := by
    xperm_hyp hq
  obtain ⟨ws', hin⟩ := (sepConj_exists_left h).mp hq1
  exact ⟨ws', by xperm_hyp hin⟩

-- ============================================================================
-- The inline arithMod accelerator step (CSR 0x802 = 2050)
-- ============================================================================

/-- Exposed registers other than `t0` (the parameter-block pointer). -/
def csrsRest : List Reg :=
  [.x6, .x7, .x28, .x29, .x30, .x31,
   .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split5 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x5 ↦ᵣ vf .x5) ** regAtomsOf vf csrsRest) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [csrsRest, regAtomsOf_cons, regAtomsOf_nil]

private theorem x5_notin_csrsRest : (.x5 : Reg) ∉ csrsRest := by decide

/-- The one-step accelerator triple at atom granularity: `t0` points at the
    staged parameter block, the whole arena rides as ONE atom, and the `_d`
    subwindow becomes the `arith256Mod` result — nothing else (registers or
    other subwindows) moves. -/
theorem csrsStep_spec (img : List (BitVec 8))
    (hlen : img.length = 232)
    (hvalid : ∀ j, j < 232 → isValidMemAddr (arenaB + BitVec.ofNat 64 j) = true)
    (hpa : wsDword img 0xC0 = arenaB + BitVec.ofNat 64 0)
    (hpb : wsDword img 0xC8 = arenaB + BitVec.ofNat 64 0x20)
    (hpc : wsDword img 0xD0 = arenaB + BitVec.ofNat 64 0x60)
    (hpm : wsDword img 0xD8 = arenaB + BitVec.ofNat 64 0xA0)
    (hpd : wsDword img 0xE0 = arenaB + BitVec.ofNat 64 0x40)
    (hmne : wsNat256 img 0xA0 ≠ 0) :
    cpsTripleWithin 1 ((GuestAddrs.bnf_mul_mod_p + 60) : Word) ((GuestAddrs.bnf_mul_mod_p + 64) : Word) mulCr
      (((.x5 : Reg) ↦ᵣ (GuestAddrs.bnf_mul_params : Word)) ** regOwns csrsRest
        ** bytesRegion arenaB img)
      (((.x5 : Reg) ↦ᵣ (GuestAddrs.bnf_mul_params : Word)) ** regOwns csrsRest
        ** bytesRegion arenaB
          (setBytes img 0x40 (leBytes32 (Accel.arith256Mod
            (wsNat256 img 0) (wsNat256 img 0x20)
            (wsNat256 img 0x60) (wsNat256 img 0xA0))))) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns csrsRest (by decide)
      (P := ((.x5 : Reg) ↦ᵣ (GuestAddrs.bnf_mul_params : Word)) ** bytesRegion arenaB img)
      (fun vf => ?_))
  have hcs := csrs_arith256Mod_spec_within ((GuestAddrs.bnf_mul_mod_p + 60) : Word) .x5 (by decide)
    arenaB 232 img
    (fun r => if r = .x5 then (GuestAddrs.bnf_mul_params : Word) else vf r)
    hlen (by decide) hvalid
    0xC0 0 0x20 0x60 0xA0 0x40
    (by
      show RegFile.get _ .x5 = arenaB + BitVec.ofNat 64 0xC0
      rw [RegFile.get, if_neg (by decide : (Reg.x5 : Reg) ≠ .x0)]
      show (if (Reg.x5 : Reg) = .x5 then (GuestAddrs.bnf_mul_params : Word) else vf .x5) = _
      rw [if_pos rfl]
      decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hpa hpb hpc hpm hpd hmne
  have hcsC := liftCode (cr' := mulCr) hcs (by code_mem)
  rw [show ((GuestAddrs.bnf_mul_mod_p + 60) : Word) + 4 = ((GuestAddrs.bnf_mul_mod_p + 64) : Word) from by decide] at hcsC
  -- unpack the register file on both sides (same file — the step moves nothing)
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split5,
    show (if (Reg.x5 : Reg) = .x5 then (GuestAddrs.bnf_mul_params : Word) else vf .x5)
      = (GuestAddrs.bnf_mul_params : Word) from if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x5 then (GuestAddrs.bnf_mul_params : Word) else vf r) vf csrsRest
      (fun r hr => by
        show (if r = .x5 then (GuestAddrs.bnf_mul_params : Word) else vf r) = vf r
        rw [if_neg (fun (hc : r = .x5) => x5_notin_csrsRest (hc ▸ hr))])]
    at hcsC
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => ?_) hcsC
  have hq2 := sepConj_mono_left (sepConj_mono_right
    (regAtomsOf_to_regOwns vf csrsRest)) h hq
  xperm_hyp hq2


-- ============================================================================
-- The whole routine
-- ============================================================================

/-- Pull an atom out of an ∃-post (the written window stays inside). -/
theorem exists_pull {α : Sort _} {F : α → Assertion} {G : Assertion}
    (h : PartialState) (hin : ∃ a, (G ** F a) h) :
    (G ** (fun hp => ∃ a, F a hp) : Assertion) h := by
  obtain ⟨a, h1, h2, hd, hu, hG, hFa⟩ := hin
  exact ⟨h1, h2, hd, hu, hG, ⟨a, hFa⟩⟩

/-- A 256-bit window decode is bounded. -/
private theorem wsNat256_lt (ws : List (BitVec 8)) (k : Nat) :
    wsNat256 ws k < 2 ^ 256 := by
  unfold wsNat256 Accel.leLimbsToNat
  simp only [List.foldr_cons, List.foldr_nil]
  have h0 := (wsDword ws k).isLt
  have h1 := (wsDword ws (k + 8)).isLt
  have h2 := (wsDword ws (k + 16)).isLt
  have h3 := (wsDword ws (k + 24)).isLt
  set M : Nat := 2 ^ 64 with hM
  have e2 : (2 : Nat) ^ 256 = M * M * M * M := by rw [hM]; norm_num
  rw [e2]
  set d3 := (wsDword ws (k + 24)).toNat
  set d2 := (wsDword ws (k + 16)).toNat
  set d1 := (wsDword ws (k + 8)).toNat
  set d0 := (wsDword ws k).toNat
  clear_value M d3 d2 d1 d0
  have A1 : 0 * M + d3 < M := by omega
  have A2 : (0 * M + d3) * M + d2 < M * M := by
    calc (0 * M + d3) * M + d2 < (0 * M + d3) * M + M := by omega
      _ = ((0 * M + d3) + 1) * M := (Nat.succ_mul _ _).symm
      _ ≤ M * M := Nat.mul_le_mul_right M A1
  have A3 : ((0 * M + d3) * M + d2) * M + d1 < M * M * M := by
    calc ((0 * M + d3) * M + d2) * M + d1
        < ((0 * M + d3) * M + d2) * M + M := by omega
      _ = (((0 * M + d3) * M + d2) + 1) * M := (Nat.succ_mul _ _).symm
      _ ≤ (M * M) * M := Nat.mul_le_mul_right M A2
  calc (((0 * M + d3) * M + d2) * M + d1) * M + d0
      < (((0 * M + d3) * M + d2) * M + d1) * M + M := by omega
    _ = ((((0 * M + d3) * M + d2) * M + d1) + 1) * M := (Nat.succ_mul _ _).symm
    _ ≤ (M * M * M) * M := Nat.mul_le_mul_right M A3

/-- Exposed registers other than `a0` (the stage-C result register). -/
def outRest : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split10 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** regAtomsOf vf outRest) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [outRest, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem exists_push {α : Sort _} {F : α → Assertion} {G : Assertion}
    (h : PartialState) (hin : (G ** (fun hp => ∃ a, F a hp) : Assertion) h) :
    ∃ a, (G ** F a) h := by
  obtain ⟨h1, h2, hd, hu, hG, ⟨a, hFa⟩⟩ := hin
  exact ⟨a, h1, h2, hd, hu, hG, hFa⟩

private theorem ownsSplit10 :
    regOwns exposedRegs = (regOwn .x10 ** regOwns outRest) := by
  show regOwns
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [outRest, regOwns_cons, regOwns_nil]
  funext h
  exact propext ⟨fun hp => by xperm_hyp hp, fun hp => by xperm_hyp hp⟩

/-- **Stage C** (`la t0, params ; csrs ; la a0, _d ; a1 := s1 ;
    call bnf_le_to_be ; a0 := 0`): from the post-conversion arena image,
    run the accelerator over the staged operands and convert the `_d`
    subwindow (read-only focused) out to the caller's window. -/
theorem stageC_spec (aPtr bPtr outPtr : Word)
    (aBE bBE outOld img₂ : List (BitVec 8))
    (hilen : img₂.length = 232) (holen : outOld.length = 32)
    (hoal : outPtr.toNat % 8 = 0) (hoov : outPtr.toNat + 32 < 2 ^ 64)
    (hovalid : ∀ k, k < 32 → isValidMemAddr (outPtr + BitVec.ofNat 64 k) = true)
    (harval : ∀ j, j < 232 → isValidMemAddr (arenaB + BitVec.ofNat 64 j) = true)
    (hdO : (0xa3000f40 : Nat) ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ (0xa3000f20 : Nat))
    (hpa₂ : wsDword img₂ 0xC0 = arenaB + BitVec.ofNat 64 0)
    (hpb₂ : wsDword img₂ 0xC8 = arenaB + BitVec.ofNat 64 0x20)
    (hpc₂ : wsDword img₂ 0xD0 = arenaB + BitVec.ofNat 64 0x60)
    (hpm₂ : wsDword img₂ 0xD8 = arenaB + BitVec.ofNat 64 0xA0)
    (hpd₂ : wsDword img₂ 0xE0 = arenaB + BitVec.ofNat 64 0x40)
    (hmne₂ : wsNat256 img₂ 0xA0 ≠ 0) :
    cpsTripleWithin (7 + ((bnfLeToBeFn 0 0 [] []).body.steps + 1) + 1)
      ((GuestAddrs.bnf_mul_mod_p + 52) : Word) ((GuestAddrs.bnf_mul_mod_p + 84) : Word) mulCr
      (((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 52) : Word)) ** (.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr)
        ** regOwns exposedRegs
        ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
        ** bytesRegion outPtr outOld ** bytesRegion arenaB img₂)
      (fun hp => ∃ out',
        ((⌜beBytesToNat out'
            = Accel.arith256Mod (wsNat256 img₂ 0) (wsNat256 img₂ 0x20)
                (wsNat256 img₂ 0x60) (wsNat256 img₂ 0xA0)
          ∧ out'.length = 32⌝
          ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 80) : Word)) ** (.x8 ↦ᵣ bPtr)
          ** (.x9 ↦ᵣ outPtr) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwns outRest
          ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
          ** bytesRegion outPtr out'
          ** bytesRegion arenaB
            (setBytes img₂ 0x40 (leBytes32 (Accel.arith256Mod
              (wsNat256 img₂ 0) (wsNat256 img₂ 0x20)
              (wsNat256 img₂ 0x60) (wsNat256 img₂ 0xA0)))))) hp) := by
  set r := Accel.arith256Mod (wsNat256 img₂ 0) (wsNat256 img₂ 0x20)
    (wsNat256 img₂ 0x60) (wsNat256 img₂ 0xA0) with hr
  set img₃ := setBytes img₂ 0x40 (leBytes32 r) with himg₃
  have hrlt : r < 2 ^ 256 := by
    rw [hr]
    unfold Accel.arith256Mod
    exact lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hmne₂)) (wsNat256_lt img₂ 0xA0)
  have himg₃len : img₃.length = 232 := by
    rw [himg₃, length_setBytes]
    exact hilen
  -- the d-window of the accelerator image is the fresh LE result
  have hdwin : ((img₃.drop 0x40).take 32) = leBytes32 r := by
    rw [himg₃]
    have := window_readback img₂ (leBytes32 r) 0x40
      (by rw [length_leBytes32]; omega)
    rwa [length_leBytes32] at this
  -- ---- la t0, bnf_mul_params ----
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns exposedRegs (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 52) : Word)) ** (.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr)
        ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
        ** bytesRegion outPtr outOld ** bytesRegion arenaB img₂)
      (fun vf => ?_))
  have hla5 := la_materialize_within .x5 (vf .x5) ((GuestAddrs.bnf_mul_mod_p + 52) : Word)
    (GuestAddrs.bnf_mul_params : Word) (cr := mulCr) (by decide) (by decide)
    (by code_mem) (by code_mem)
  rw [show ((GuestAddrs.bnf_mul_mod_p + 52) : Word) + 8 = ((GuestAddrs.bnf_mul_mod_p + 60) : Word) from by decide] at hla5
  -- CSRS over the whole arena atom
  have hcsrs := csrsStep_spec img₂ hilen harval hpa₂ hpb₂ hpc₂ hpm₂ hpd₂ hmne₂
  rw [← hr, ← himg₃] at hcsrs
  -- the rest of the stage, from the CSRS exit, with the register file owned
  have hrest : cpsTripleWithin
      (4 + ((bnfLeToBeFn 0 0 [] []).body.steps + 1) + 1)
      ((GuestAddrs.bnf_mul_mod_p + 64) : Word) ((GuestAddrs.bnf_mul_mod_p + 84) : Word) mulCr
      (((.x5 : Reg) ↦ᵣ (GuestAddrs.bnf_mul_params : Word)) ** regOwns csrsRest
        ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 52) : Word)) ** (.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr)
        ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
        ** bytesRegion outPtr outOld ** bytesRegion arenaB img₃)
      (fun hp => ∃ out',
        ((⌜beBytesToNat out' = r ∧ out'.length = 32⌝
          ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 80) : Word)) ** (.x8 ↦ᵣ bPtr)
          ** (.x9 ↦ᵣ outPtr) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwns outRest
          ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
          ** bytesRegion outPtr out'
          ** bytesRegion arenaB img₃)) hp) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
      (cpsTripleWithin_peel_regOwns csrsRest (by decide)
        (P := ((.x5 : Reg) ↦ᵣ (GuestAddrs.bnf_mul_params : Word))
          ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 52) : Word)) ** (.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr)
          ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
          ** bytesRegion outPtr outOld ** bytesRegion arenaB img₃)
        (fun vg => ?_))
    -- la a0, bnf_le_d
    have hla10 := la_materialize_within .x10 (vg .x10) ((GuestAddrs.bnf_mul_mod_p + 64) : Word)
      (GuestAddrs.bnf_le_d : Word) (cr := mulCr) (by decide) (by decide)
      (by code_mem) (by code_mem)
    rw [show ((GuestAddrs.bnf_mul_mod_p + 64) : Word) + 8 = ((GuestAddrs.bnf_mul_mod_p + 72) : Word) from by decide] at hla10
    -- a1 := s1
    have hmv := liftCode (cr' := mulCr)
      (mv_spec_gen_within .x11 .x9 outPtr (vg .x11) ((GuestAddrs.bnf_mul_mod_p + 72) : Word) (by decide))
      (by code_mem)
    rw [show ((GuestAddrs.bnf_mul_mod_p + 72) : Word) + 4 = ((GuestAddrs.bnf_mul_mod_p + 76) : Word) from by decide] at hmv
    -- the final conversion call over the FOCUSED d-window
    have hflat := bnfLeToBeFlat_spec ((GuestAddrs.bnf_mul_mod_p + 80) : Word) (GuestAddrs.bnf_le_d : Word)
      outPtr (leBytes32 r) outOld (by rw [length_leBytes32]) holen
      (by
        refine ⟨?_, ?_, ?_⟩
        · show ((GuestAddrs.bnf_le_d : Word)).toNat % 8 = 0
          decide
        · show ((GuestAddrs.bnf_le_d : Word)).toNat + (leBytes32 r).length < 2 ^ 64
          rw [length_leBytes32]
          decide
        · intro k hk
          rw [length_leBytes32] at hk
          rw [show (GuestAddrs.bnf_le_d : Word) + BitVec.ofNat 64 k
              = arenaB + BitVec.ofNat 64 (0x40 + k) from by
            show _ = arenaB + BitVec.ofNat 64 (0x40 + k)
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
              BitVec.toNat_ofNat,
              show ((GuestAddrs.bnf_le_d : Word)).toNat = 0xa3000f20 from by decide,
              show (arenaB).toNat = 0xa3000ee0 from by decide]
            omega]
          exact harval (0x40 + k) (by omega))
      ⟨hoal, by omega, hovalid⟩
      (by decide) (by omega)
      (by
        have hsrc : ((GuestAddrs.bnf_le_d : Word)).toNat = 0xa3000f20 := by decide
        rcases hdO with h | h
        · left
          rw [hsrc]
          omega
        · right
          rw [hsrc]
          omega)
      (by decide)
    -- massage into callWithin shape: pull `ra` out of the ∃-post
    have hcallee : cpsTripleWithin ((bnfLeToBeFn (GuestAddrs.bnf_le_d : Word) outPtr
        (leBytes32 r) outOld).body.steps + 1)
        (GuestAddrs.bnf_le_to_be : Word) ((GuestAddrs.bnf_mul_mod_p + 80) : Word) mulCr
        (((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 80) : Word))
          ** ((.x10 ↦ᵣ (GuestAddrs.bnf_le_d : Word)) ** (.x11 ↦ᵣ outPtr)
            ** regOwns convScratch ** bytesRegion outPtr outOld
            ** bytesRegion (GuestAddrs.bnf_le_d : Word) (leBytes32 r)))
        (((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 80) : Word))
          ** (fun hp => ∃ ws',
            ((⌜beBytesToNat ws' = wsNat256 (leBytes32 r) 0 ∧ ws'.length = 32⌝
              ** regOwns exposedRegs ** bytesRegion outPtr ws'
              ** bytesRegion (GuestAddrs.bnf_le_d : Word) (leBytes32 r))) hp)) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun h hq => ?_) hflat
      obtain ⟨ws', hin⟩ := hq
      refine exists_pull h ⟨ws', ?_⟩
      xperm_hyp hin
    have hcall := callWithin_spec ((GuestAddrs.bnf_mul_mod_p + 76) : Word) (GuestAddrs.bnf_le_to_be : Word)
      ((GuestAddrs.bnf_mul_mod_p + 52) : Word)
      (jalOff GuestAddrs.bnf_le_to_be (GuestAddrs.bnf_mul_mod_p + 76))
      ((bnfLeToBeFn (GuestAddrs.bnf_le_d : Word) outPtr (leBytes32 r) outOld).body.steps + 1)
      (by decide) (by code_mem) (by pcf) hcallee
    rw [show ((GuestAddrs.bnf_mul_mod_p + 76) : Word) + 4 = ((GuestAddrs.bnf_mul_mod_p + 80) : Word) from by decide] at hcall
    rw [show (bnfLeToBeFn (GuestAddrs.bnf_le_d : Word) outPtr
        (leBytes32 r) outOld).body.steps
      = (bnfLeToBeFn 0 0 [] []).body.steps from rfl] at hcall
    -- a0 := 0
    have hli := liftCode (cr' := mulCr)
      (li_spec_gen_own_within .x10 (0 : Word) ((GuestAddrs.bnf_mul_mod_p + 80) : Word) (by decide))
      (by code_mem)
    rw [show ((GuestAddrs.bnf_mul_mod_p + 80) : Word) + 4 = ((GuestAddrs.bnf_mul_mod_p + 84) : Word) from by decide] at hli
    -- ---- frames + chain ----
    have hla10F := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ (GuestAddrs.bnf_mul_params : Word)) ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 52) : Word))
        ** (.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr) ** (.x11 ↦ᵣ vg .x11)
        ** (.x6 ↦ᵣ vg .x6) ** (.x7 ↦ᵣ vg .x7) ** (.x28 ↦ᵣ vg .x28)
        ** (.x29 ↦ᵣ vg .x29) ** (.x30 ↦ᵣ vg .x30) ** (.x31 ↦ᵣ vg .x31)
        ** (.x12 ↦ᵣ vg .x12) ** (.x13 ↦ᵣ vg .x13) ** (.x14 ↦ᵣ vg .x14)
        ** (.x15 ↦ᵣ vg .x15) ** (.x16 ↦ᵣ vg .x16) ** (.x17 ↦ᵣ vg .x17)
        ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
        ** bytesRegion outPtr outOld ** bytesRegion arenaB img₃)
      (by pcf) hla10
    have hmvF := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ (GuestAddrs.bnf_mul_params : Word)) ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 52) : Word))
        ** (.x8 ↦ᵣ bPtr) ** (.x10 ↦ᵣ (GuestAddrs.bnf_le_d : Word))
        ** (.x6 ↦ᵣ vg .x6) ** (.x7 ↦ᵣ vg .x7) ** (.x28 ↦ᵣ vg .x28)
        ** (.x29 ↦ᵣ vg .x29) ** (.x30 ↦ᵣ vg .x30) ** (.x31 ↦ᵣ vg .x31)
        ** (.x12 ↦ᵣ vg .x12) ** (.x13 ↦ᵣ vg .x13) ** (.x14 ↦ᵣ vg .x14)
        ** (.x15 ↦ᵣ vg .x15) ** (.x16 ↦ᵣ vg .x16) ** (.x17 ↦ᵣ vg .x17)
        ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
        ** bytesRegion outPtr outOld ** bytesRegion arenaB img₃)
      (by pcf) hmv
    have hcallF := cpsTripleWithin_frameR
      ((.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr)
        ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
        ** windowRest arenaB img₃ 0x40 32)
      (by
        exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj (bytesRegion_pcFree _ _)
            (pcFree_sepConj (bytesRegion_pcFree _ _)
              (pcFree_windowRest _ _ _ _))))) hcall
    have hchain1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hla10F hmvF
    have hchain2 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        -- split the accelerator image: focus the d-window (read-only src)
        rw [bytesRegion_window_focus arenaB img₃ 0x40 32 (by omega)
              (by norm_num) (by norm_num), hdwin,
            show arenaB + BitVec.ofNat 64 0x40 = (GuestAddrs.bnf_le_d : Word) from by decide]
          at hp
        -- release the scratch file to ownership for the callee
        have hp1 : ((.x6 ↦ᵣ vg .x6) ** (.x7 ↦ᵣ vg .x7) ** (.x28 ↦ᵣ vg .x28)
            ** (.x29 ↦ᵣ vg .x29) ** (.x30 ↦ᵣ vg .x30) ** (.x31 ↦ᵣ vg .x31)
            ** (.x12 ↦ᵣ vg .x12) ** (.x13 ↦ᵣ vg .x13) ** (.x14 ↦ᵣ vg .x14)
            ** (.x15 ↦ᵣ vg .x15) ** (.x16 ↦ᵣ vg .x16) ** (.x17 ↦ᵣ vg .x17)
            ** (((.x5 : Reg)) ↦ᵣ (GuestAddrs.bnf_mul_params : Word))
            ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 52) : Word)) ** (.x10 ↦ᵣ (GuestAddrs.bnf_le_d : Word))
              ** (.x11 ↦ᵣ outPtr) ** (.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr)
              ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
              ** bytesRegion outPtr outOld
              ** bytesRegion (GuestAddrs.bnf_le_d : Word) (leBytes32 r)
              ** windowRest arenaB img₃ 0x40 32)) h := by
          xperm_hyp hp
        have hp2 := sepConj_mono (regIs_to_regOwn .x6 _)
          (sepConj_mono (regIs_to_regOwn .x7 _)
            (sepConj_mono (regIs_to_regOwn .x28 _)
              (sepConj_mono (regIs_to_regOwn .x29 _)
                (sepConj_mono (regIs_to_regOwn .x30 _)
                  (sepConj_mono (regIs_to_regOwn .x31 _)
                    (sepConj_mono (regIs_to_regOwn .x12 _)
                      (sepConj_mono (regIs_to_regOwn .x13 _)
                        (sepConj_mono (regIs_to_regOwn .x14 _)
                          (sepConj_mono (regIs_to_regOwn .x15 _)
                            (sepConj_mono (regIs_to_regOwn .x16 _)
                              (sepConj_mono (regIs_to_regOwn .x17 _)
                                (sepConj_mono (regIs_to_regOwn .x5 _)
                                  (fun _ hh => hh))))))))))))) h hp1
        have hp3 : (regOwns convScratch **
            (((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 52) : Word)) ** (.x10 ↦ᵣ (GuestAddrs.bnf_le_d : Word))
              ** (.x11 ↦ᵣ outPtr) ** (.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr)
              ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
              ** bytesRegion outPtr outOld
              ** bytesRegion (GuestAddrs.bnf_le_d : Word) (leBytes32 r)
              ** windowRest arenaB img₃ 0x40 32)) h := by
          simp only [convScratch, regOwns_cons, regOwns_nil, sepConj_emp_right']
          xperm_hyp hp2
        xperm_hyp hp3) hchain1 hcallF
    -- run the epilogue `li a0, 0` under the existential
    have hchain2' := cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hq => by
        have hq1 : (((fun hp => ∃ ws',
            ((⌜beBytesToNat ws' = wsNat256 (leBytes32 r) 0 ∧ ws'.length = 32⌝
              ** regOwns exposedRegs ** bytesRegion outPtr ws'
              ** bytesRegion (GuestAddrs.bnf_le_d : Word) (leBytes32 r))) hp) : Assertion)
            ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 80) : Word)) ** (.x8 ↦ᵣ bPtr)
              ** (.x9 ↦ᵣ outPtr) ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
              ** windowRest arenaB img₃ 0x40 32)) h := by
          xperm_hyp hq
        exact (sepConj_exists_left h).mp hq1) hchain2
    have hcont : ∀ ws' : List (BitVec 8),
        cpsTripleWithin 1 ((GuestAddrs.bnf_mul_mod_p + 80) : Word) ((GuestAddrs.bnf_mul_mod_p + 84) : Word) mulCr
          ((⌜beBytesToNat ws' = wsNat256 (leBytes32 r) 0 ∧ ws'.length = 32⌝
            ** regOwns exposedRegs ** bytesRegion outPtr ws'
            ** bytesRegion (GuestAddrs.bnf_le_d : Word) (leBytes32 r))
            ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 80) : Word)) ** (.x8 ↦ᵣ bPtr)
              ** (.x9 ↦ᵣ outPtr) ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
              ** windowRest arenaB img₃ 0x40 32))
          (fun hp => ∃ out',
            ((⌜beBytesToNat out' = r ∧ out'.length = 32⌝
              ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 80) : Word)) ** (.x8 ↦ᵣ bPtr)
              ** (.x9 ↦ᵣ outPtr) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwns outRest
              ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
              ** bytesRegion outPtr out'
              ** bytesRegion arenaB img₃)) hp) := by
      intro ws'
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq)
        (cpsTripleWithin_pure_pre
          (P := beBytesToNat ws' = wsNat256 (leBytes32 r) 0 ∧ ws'.length = 32)
          (H := regOwns exposedRegs ** bytesRegion outPtr ws'
            ** bytesRegion (GuestAddrs.bnf_le_d : Word) (leBytes32 r)
            ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 80) : Word)) ** (.x8 ↦ᵣ bPtr)
              ** (.x9 ↦ᵣ outPtr) ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
              ** windowRest arenaB img₃ 0x40 32))
          (fun hfacts => ?_))
      have hliF := cpsTripleWithin_frameR
        (((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 80) : Word)) ** (.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr)
          ** regOwns outRest ** bytesRegion outPtr ws'
          ** bytesRegion (GuestAddrs.bnf_le_d : Word) (leBytes32 r)
          ** windowRest arenaB img₃ 0x40 32
          ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE)
        (by
          refine pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs (pcFree_sepConj (pcFree_regOwns _)
              (pcFree_sepConj (bytesRegion_pcFree _ _)
                (pcFree_sepConj (bytesRegion_pcFree _ _)
                  (pcFree_sepConj (pcFree_windowRest _ _ _ _)
                    (pcFree_sepConj (bytesRegion_pcFree _ _)
                      (bytesRegion_pcFree _ _)))))))))
        hli
      refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hliF
      · rw [ownsSplit10] at hp
        xperm_hyp hp
      · refine ⟨ws', ?_⟩
        have hval : beBytesToNat ws' = r := by
          rw [hfacts.1, wsNat256_leBytes32 r hrlt]
        have hq1 : ((⌜beBytesToNat ws' = r ∧ ws'.length = 32⌝ : Assertion)
            ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 80) : Word)) ** (.x8 ↦ᵣ bPtr)
              ** (.x9 ↦ᵣ outPtr) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwns outRest
              ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
              ** bytesRegion outPtr ws'
              ** (bytesRegion (arenaB + BitVec.ofNat 64 0x40)
                    ((img₃.drop 0x40).take 32)
                ** windowRest arenaB img₃ 0x40 32))) h := by
          refine (sepConj_pure_left h).mpr ⟨⟨hval, hfacts.2⟩, ?_⟩
          rw [hdwin, show arenaB + BitVec.ofNat 64 0x40 = (GuestAddrs.bnf_le_d : Word)
            from by decide]
          xperm_hyp hq
        rw [← bytesRegion_window_focus arenaB img₃ 0x40 32 (by omega)
              (by norm_num) (by norm_num)] at hq1
        xperm_hyp hq1
    refine cpsTripleWithin_weaken (fun _ hp => by
        simp only [csrsRest, regAtomsOf_cons, regAtomsOf_nil,
          sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun _ hq => hq)
      (cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_seq_exists_same_cr hchain2' hcont))
  -- ---- assemble stage C: la ; csrs ; rest ----
  have hla5F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 52) : Word)) ** (.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr)
      ** (.x6 ↦ᵣ vf .x6) ** (.x7 ↦ᵣ vf .x7) ** (.x28 ↦ᵣ vf .x28)
      ** (.x29 ↦ᵣ vf .x29) ** (.x30 ↦ᵣ vf .x30) ** (.x31 ↦ᵣ vf .x31)
      ** (.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** (.x12 ↦ᵣ vf .x12)
      ** (.x13 ↦ᵣ vf .x13) ** (.x14 ↦ᵣ vf .x14) ** (.x15 ↦ᵣ vf .x15)
      ** (.x16 ↦ᵣ vf .x16) ** (.x17 ↦ᵣ vf .x17)
      ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
      ** bytesRegion outPtr outOld ** bytesRegion arenaB img₂)
    (by pcf) hla5
  have hcsrsF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 52) : Word)) ** (.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr)
      ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE ** bytesRegion outPtr outOld)
    (by pcf) hcsrs
  have hc1 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      -- release the scratch file into `regOwns csrsRest` for the CSRS step
      have hp1 : ((.x6 ↦ᵣ vf .x6) ** (.x7 ↦ᵣ vf .x7) ** (.x28 ↦ᵣ vf .x28)
          ** (.x29 ↦ᵣ vf .x29) ** (.x30 ↦ᵣ vf .x30) ** (.x31 ↦ᵣ vf .x31)
          ** (.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** (.x12 ↦ᵣ vf .x12)
          ** (.x13 ↦ᵣ vf .x13) ** (.x14 ↦ᵣ vf .x14) ** (.x15 ↦ᵣ vf .x15)
          ** (.x16 ↦ᵣ vf .x16) ** (.x17 ↦ᵣ vf .x17)
          ** ((((.x5 : Reg)) ↦ᵣ (GuestAddrs.bnf_mul_params : Word))
            ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 52) : Word)) ** (.x8 ↦ᵣ bPtr)
            ** (.x9 ↦ᵣ outPtr)
            ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
            ** bytesRegion outPtr outOld
            ** bytesRegion arenaB img₂)) h := by
        xperm_hyp hp
      have hp2 := sepConj_mono (regIs_to_regOwn .x6 _)
        (sepConj_mono (regIs_to_regOwn .x7 _)
          (sepConj_mono (regIs_to_regOwn .x28 _)
            (sepConj_mono (regIs_to_regOwn .x29 _)
              (sepConj_mono (regIs_to_regOwn .x30 _)
                (sepConj_mono (regIs_to_regOwn .x31 _)
                  (sepConj_mono (regIs_to_regOwn .x10 _)
                    (sepConj_mono (regIs_to_regOwn .x11 _)
                      (sepConj_mono (regIs_to_regOwn .x12 _)
                        (sepConj_mono (regIs_to_regOwn .x13 _)
                          (sepConj_mono (regIs_to_regOwn .x14 _)
                            (sepConj_mono (regIs_to_regOwn .x15 _)
                              (sepConj_mono (regIs_to_regOwn .x16 _)
                                (sepConj_mono (regIs_to_regOwn .x17 _)
                                  (fun _ hh => hh)))))))))))))) h hp1
      have hp3 : ((((.x5 : Reg)) ↦ᵣ (GuestAddrs.bnf_mul_params : Word)) ** regOwns csrsRest
          ** bytesRegion arenaB img₂
          ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.bnf_mul_mod_p + 52) : Word)) ** (.x8 ↦ᵣ bPtr)
            ** (.x9 ↦ᵣ outPtr)
            ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
            ** bytesRegion outPtr outOld)) h := by
        simp only [csrsRest, regOwns_cons, regOwns_nil, sepConj_emp_right']
        xperm_hyp hp2
      xperm_hyp hp3) hla5F hcsrsF
  have hc2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc1 hrest
  exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [exposedRegs, regAtomsOf_cons, regAtomsOf_nil,
        sepConj_emp_right'] at hp
      xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_mono_nSteps (by omega) hc2)



end Bn254FieldMulModPSAsm

end EvmAsm.Codegen
