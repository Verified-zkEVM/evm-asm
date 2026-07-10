/-
  EvmAsm.Codegen.Programs.Secp256k1PointDoubleSAsmStage

  Staging infrastructure for `secp256k1_point_double` (bead
  evm-asm-4ch8f.38.5, the inline-CSRS half): the emitted routine
  (`pdBody`/`pdFrame`/`pdProg_tie`), its code map (`pdCr`), the four
  callee focused adapters (`secfIsZero32Flat_spec` / `secfZero32Flat_spec`
  / `secfBeToLeFlat_spec` / `secfLeToBeFlat_spec`), and the inline
  CSR-2052 curve tangent-doubling step (`curveStep_spec`).  The capstone
  `pointDouble_spec` lives in `Secp256k1PointDoubleSAsm`, which imports
  this file.  See that file's header for the full design notes.
-/

import EvmAsm.Codegen.Programs.Secp256k1Curve
import EvmAsm.Codegen.Programs.Secp256k1FieldConvSAsm
import EvmAsm.Codegen.Programs.Secp256k1FieldLeToBeSAsm
import EvmAsm.Codegen.Programs.Secp256k1FieldIsZeroSAsm
import EvmAsm.Codegen.Programs.Secp256k1FieldLeavesSAsm
import EvmAsm.Rv64.SAsm.RwSubwindow
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.LaResolve
import EvmAsm.Crypto.PowLadder

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

namespace Secp256k1PointDoubleSAsm

open Secp256k1FieldConvSAsm (secfBeToLeFn secfBeToLeFn_spec)
open Secp256k1FieldLeToBeSAsm (secfLeToBeFn secfLeToBeFn_spec)
open Secp256k1FieldIsZeroSAsm (secfIsZero32Fn secfIsZero32Fn_spec)
open Secp256k1FieldLeavesSAsm (secfZero32Fn secfZero32Fn_spec)
open EvmAsm.Rv64.SAsm.WhileBreakDemo (nlz nlz_le nlz_spec nlz_boundary)

-- Address anchors (routine, callees, and the LE staging point).
#guard GuestAddrs.secp256k1_point_double = 0x8002072c
#guard GuestAddrs.secf_is_zero32 = 0x8001ff50
#guard GuestAddrs.secf_zero32 = 0x8001fe7c
#guard GuestAddrs.secf_be_to_le = 0x8001fe90
#guard GuestAddrs.secf_le_to_be = 0x8001fee0
#guard GuestAddrs.secc_le_p1 = 0xa3c05618

/-- The staging-point base (`secc_le_p1`): a 64-byte LE point image
    `x || y`, four u64 limbs per coordinate. -/
def arenaB : Word := GuestAddrs.secc_le_p1

/-- The frame and body of the emitted routine. -/
def pdFrame : FrameDesc := [(.x1, 0), (.x8, 8), (.x9, 16)]

def pdBody : List Instr :=
  [ .MV .x8 .x10,
    .MV .x9 .x11,
    .ADDI .x10 .x8 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.secf_is_zero32 (GuestAddrs.secp256k1_point_double + 28)),
    .BEQ .x10 .x0 (28 : BitVec 13),
    .MV .x10 .x9,
    .JAL .x1 (jalOff GuestAddrs.secf_zero32 (GuestAddrs.secp256k1_point_double + 40)),
    .ADDI .x10 .x9 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.secf_zero32 (GuestAddrs.secp256k1_point_double + 48)),
    .LI .x10 (1 : Word),
    .JAL .x0 (92 : BitVec 21),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 64)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 64)),
    .JAL .x1 (jalOff GuestAddrs.secf_be_to_le (GuestAddrs.secp256k1_point_double + 72)),
    .ADDI .x10 .x8 (32 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 80)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 80)),
    .ADDI .x11 .x11 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.secf_be_to_le (GuestAddrs.secp256k1_point_double + 92)),
    .AUIPC .x5 (laHi GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 96)),
    .ADDI .x5 .x5 (laLo GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 96)),
    .CSRS (2052 : BitVec 12) .x5,
    .AUIPC .x10 (laHi GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 108)),
    .ADDI .x10 .x10 (laLo GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 108)),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.secf_le_to_be (GuestAddrs.secp256k1_point_double + 120)),
    .AUIPC .x10 (laHi GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 124)),
    .ADDI .x10 .x10 (laLo GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 124)),
    .ADDI .x10 .x10 (32 : BitVec 12),
    .ADDI .x11 .x9 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.secf_le_to_be (GuestAddrs.secp256k1_point_double + 140)),
    .LI .x10 (0 : Word) ]

/-- Byte tie (kernel-checked): the emitted routine IS the ABI frame over
    the body — byte-transparent, no A/B. -/
theorem pdProg_tie :
    abiFrameProg (-32 : BitVec 12) (32 : BitVec 12) pdFrame pdBody
      = secp256k1PointDouble_prog := rfl

/-- The routine's single code map: its own program plus the four callees'. -/
def pdCr : CodeReq :=
  (CodeReq.ofProg (GuestAddrs.secp256k1_point_double : Word) secp256k1PointDouble_prog).union
    ((CodeReq.ofProg (GuestAddrs.secf_is_zero32 : Word) secfIsZero32_prog).union
      ((CodeReq.ofProg (GuestAddrs.secf_zero32 : Word) secfZero32_prog).union
        ((CodeReq.ofProg (GuestAddrs.secf_be_to_le : Word) secfBeToLe_prog).union
          (CodeReq.ofProg (GuestAddrs.secf_le_to_be : Word) secfLeToBe_prog))))

/-- The exposed registers the converter contracts clobber beyond `a0`/`a1`. -/
def convScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x12, .x13, .x14, .x15, .x16, .x17]

/-- The exposed registers beyond `a0` (single-pointer callees). -/
def a0Rest : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split2 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** regAtomsOf vf convScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [convScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem exposedRegs_splitA0 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** regAtomsOf vf a0Rest) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [a0Rest, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_convScratch : (.x10 : Reg) ∉ convScratch := by decide
private theorem x11_notin_convScratch : (.x11 : Reg) ∉ convScratch := by decide
private theorem x10_notin_a0Rest : (.x10 : Reg) ∉ a0Rest := by decide

-- ============================================================================
-- Flat contract: secf_is_zero32 (read-only leaf, no rw window)
-- ============================================================================

/-- **Flat contract for `secf_is_zero32`** (adapter-derived, deterministic
    post: `a0 = 1` iff the 32 bytes are all zero). -/
theorem secfIsZero32Flat_spec (ret ptr : Word) (bs : List (BitVec 8))
    (hlen : bs.length = 32) (hwfR : Region.wf ⟨ptr, bs⟩)
    (hso : ptr.toNat + 32 < 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((secfIsZero32Fn ptr bs).body.steps + 1)
      (GuestAddrs.secf_is_zero32 : Word) ret pdCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ ptr) ** regOwns a0Rest
        ** bytesRegion ptr bs)
      (((.x1 : Reg) ↦ᵣ ret)
        ** (.x10 ↦ᵣ (if nlz bs 32 = 32 then (1 : Word) else (0 : Word)))
        ** regOwns a0Rest ** bytesRegion ptr bs) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns a0Rest (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ ptr) ** bytesRegion ptr bs)
      (fun vf => ?_))
  have had := Fn.retSpecFlat (secfIsZero32Fn ptr bs)
    (GuestAddrs.secf_is_zero32 : Word)
    (secfIsZero32Fn_spec ptr bs hwfR (GuestAddrs.secf_is_zero32 : Word))
    (by show 4 * (11 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then ptr else vf r)
    []
    (by show ([] : List (BitVec 8)).length = 0; rfl)
    (by
      refine ⟨?_, hlen, hso, rfl⟩
      show RegFile.get _ .x10 = ptr
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl)
    (fun _ _ _ h => h.2.2.2)
    (Q := (.x10 ↦ᵣ (if nlz bs 32 = 32 then (1 : Word) else (0 : Word)))
      ** regOwns a0Rest)
    (fun rf' ws' hlen' hpost' hp hh => by
      obtain rfl := List.eq_nil_of_length_eq_zero hlen'
      rw [show (secfIsZero32Fn ptr bs).rw.base = (0 : Word) from rfl,
        bytesRegion_nil, sepConj_emp_right'] at hh
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_splitA0,
        show (rf' Reg.x10 : Word)
            = (if nlz bs 32 = 32 then (1 : Word) else (0 : Word)) from by
          have h10 := hpost'.1
          rwa [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
            at h10] at hh
      exact sepConj_mono_right (regAtomsOf_to_regOwns (fun r => rf' r) a0Rest)
        hp hh)
  rw [show (secfIsZero32Fn ptr bs).programRet (GuestAddrs.secf_is_zero32 : Word)
      = secfIsZero32_prog from rfl] at had
  have hadC := liftCode (cr' := pdCr) had (by code_mem)
  rw [show (secfIsZero32Fn ptr bs).region = (⟨ptr, bs⟩ : Region) from rfl,
    show (secfIsZero32Fn ptr bs).rw.base = (0 : Word) from rfl,
    bytesRegion_nil, sepConj_emp_right'] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_splitA0,
    show (if (Reg.x10 : Reg) = .x10 then ptr else vf .x10) = ptr from if_pos rfl,
    regAtomsOf_congr (fun r => if r = .x10 then ptr else vf r) vf a0Rest
      (fun r hr => by
        show (if r = .x10 then ptr else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_a0Rest (hc ▸ hr))])]
    at hadC
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hadC

-- ============================================================================
-- Flat contract: secf_zero32 (write-only leaf, no read region)
-- ============================================================================

/-- **Flat contract for `secf_zero32`** (adapter-derived, deterministic
    post: the 32-byte window at `a0` becomes all-zero). -/
theorem secfZero32Flat_spec (ret dst : Word) (ob : List (BitVec 8))
    (holen : ob.length = 32) (hrww : RwRegion.wf ⟨dst, 32⟩)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((secfZero32Fn 0 []).body.steps + 1)
      (GuestAddrs.secf_zero32 : Word) ret pdCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ dst) ** regOwns a0Rest
        ** bytesRegion dst ob)
      (((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs
        ** bytesRegion dst (List.replicate 32 (0 : BitVec 8))) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns a0Rest (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ dst) ** bytesRegion dst ob)
      (fun vf => ?_))
  have had := Fn.retSpecFlat (secfZero32Fn dst ob)
    (GuestAddrs.secf_zero32 : Word)
    (secfZero32Fn_spec dst ob hrww (GuestAddrs.secf_zero32 : Word))
    (by show 4 * (4 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then dst else vf r)
    ob
    (by show ob.length = 32; exact holen)
    (by
      refine ⟨?_, rfl, holen, rfl⟩
      show RegFile.get _ .x10 = dst
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl)
    (fun _ _ _ h => h.2)
    (Q := regOwns exposedRegs ** bytesRegion dst (List.replicate 32 (0 : BitVec 8)))
    (fun rf' ws' hlen' hpost' hp hh => by
      rw [show (secfZero32Fn dst ob).rw.base = dst from rfl, hpost'.1] at hh
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
      exact sepConj_mono_left
        (regAtomsOf_to_regOwns (fun r => rf' r) exposedRegs) hp hh)
  rw [show (secfZero32Fn dst ob).programRet (GuestAddrs.secf_zero32 : Word)
      = secfZero32_prog from rfl] at had
  have hadC := liftCode (cr' := pdCr) had (by code_mem)
  rw [show (secfZero32Fn dst ob).region = Region.empty from rfl,
    show (Region.empty).bytes = ([] : List (BitVec 8)) from rfl,
    bytesRegion_nil, sepConj_emp_right', sepConj_emp_right',
    show (secfZero32Fn dst ob).rw.base = dst from rfl] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_splitA0,
    show (if (Reg.x10 : Reg) = .x10 then dst else vf .x10) = dst from if_pos rfl,
    regAtomsOf_congr (fun r => if r = .x10 then dst else vf r) vf a0Rest
      (fun r hr => by
        show (if r = .x10 then dst else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_a0Rest (hc ▸ hr))])]
    at hadC
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hadC

-- ============================================================================
-- Flat contracts: the two converters (as in bnf_mul_mod_p, #10069)
-- ============================================================================

/-- **Flat contract for `secf_be_to_le`** (adapter-derived, ∃-post: the
    written window's exact bytes are existential, its 256-bit LE decode is
    pinned to the input's BE value). -/
theorem secfBeToLeFlat_spec (ret srci dsti : Word) (inb ob : List (BitVec 8))
    (hilen : inb.length = 32) (holen : ob.length = 32)
    (hwfR : Region.wf ⟨srci, inb⟩) (hrww : RwRegion.wf ⟨dsti, 32⟩)
    (hso : srci.toNat + 32 < 2 ^ 64) (hdo : dsti.toNat + 32 < 2 ^ 64)
    (hdisj : srci.toNat + 32 ≤ dsti.toNat ∨ dsti.toNat + 32 ≤ srci.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((secfBeToLeFn srci dsti inb ob).body.steps + 1)
      (GuestAddrs.secf_be_to_le : Word) ret pdCr
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
  have had := Fn.retSpecFlat (secfBeToLeFn srci dsti inb ob)
    (GuestAddrs.secf_be_to_le : Word)
    (secfBeToLeFn_spec srci dsti inb ob hwfR hrww hilen (GuestAddrs.secf_be_to_le : Word))
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
  rw [show (secfBeToLeFn srci dsti inb ob).programRet (GuestAddrs.secf_be_to_le : Word)
      = secfBeToLe_prog from rfl] at had
  have hadC := liftCode (cr' := pdCr) had (by code_mem)
  rw [show (secfBeToLeFn srci dsti inb ob).region = (⟨srci, inb⟩ : Region) from rfl,
      show (secfBeToLeFn srci dsti inb ob).rw.base = dsti from rfl] at hadC
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
      ((⌜wsNat256 ws' 0 = beBytesToNat inb ∧ ws'.length = 32⌝
        ** regOwns exposedRegs ** bytesRegion dsti ws')) hp)
      ** (((.x1 : Reg) ↦ᵣ ret) ** bytesRegion srci inb) : Assertion) h := by
    xperm_hyp hq
  obtain ⟨ws', hin⟩ := (sepConj_exists_left h).mp hq1
  exact ⟨ws', by xperm_hyp hin⟩

/-- **Flat contract for `secf_le_to_be`** (adapter-derived, ∃-post: the
    output's BE decode is pinned to the LE staging window's value). -/
theorem secfLeToBeFlat_spec (ret srci dsti : Word) (inb ob : List (BitVec 8))
    (hilen : inb.length = 32) (holen : ob.length = 32)
    (hwfR : Region.wf ⟨srci, inb⟩) (hrww : RwRegion.wf ⟨dsti, 32⟩)
    (hso : srci.toNat + 32 < 2 ^ 64) (hdo : dsti.toNat + 32 < 2 ^ 64)
    (hdisj : srci.toNat + 32 ≤ dsti.toNat ∨ dsti.toNat + 32 ≤ srci.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((secfLeToBeFn srci dsti inb ob).body.steps + 1)
      (GuestAddrs.secf_le_to_be : Word) ret pdCr
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
  have had := Fn.retSpecFlat (secfLeToBeFn srci dsti inb ob)
    (GuestAddrs.secf_le_to_be : Word)
    (secfLeToBeFn_spec srci dsti inb ob hwfR hrww hilen (GuestAddrs.secf_le_to_be : Word))
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
      ((⌜beBytesToNat ws' = Accel.leLimbsToNat
          [wsDword inb 0, wsDword inb 8, wsDword inb 16, wsDword inb 24]
        ∧ ws'.length = 32⌝
        ** regOwns exposedRegs ** bytesRegion dsti ws')) hp)
    (fun rf' ws' hlen' hpost' hp hh => by
      refine ⟨ws', ?_⟩
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
      have hh2 := sepConj_mono_left
        (regAtomsOf_to_regOwns (fun r => rf' r) exposedRegs) hp hh
      have hpure : (⌜beBytesToNat ws' = Accel.leLimbsToNat
            [wsDword inb 0, wsDword inb 8, wsDword inb 16, wsDword inb 24]
          ∧ ws'.length = 32⌝
          ** (regOwns exposedRegs ** bytesRegion dsti ws')) hp :=
        (sepConj_pure_left hp).mpr ⟨⟨hpost'.1, hlen'⟩, hh2⟩
      xperm_hyp hpure)
  rw [show (secfLeToBeFn srci dsti inb ob).programRet (GuestAddrs.secf_le_to_be : Word)
      = secfLeToBe_prog from rfl] at had
  have hadC := liftCode (cr' := pdCr) had (by code_mem)
  rw [show (secfLeToBeFn srci dsti inb ob).region = (⟨srci, inb⟩ : Region) from rfl,
      show (secfLeToBeFn srci dsti inb ob).rw.base = dsti from rfl] at hadC
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
      ((⌜beBytesToNat ws' = Accel.leLimbsToNat
          [wsDword inb 0, wsDword inb 8, wsDword inb 16, wsDword inb 24]
        ∧ ws'.length = 32⌝
        ** regOwns exposedRegs ** bytesRegion dsti ws')) hp)
      ** (((.x1 : Reg) ↦ᵣ ret) ** bytesRegion srci inb) : Assertion) h := by
    xperm_hyp hq
  obtain ⟨ws', hin⟩ := (sepConj_exists_left h).mp hq1
  refine ⟨ws', ?_⟩
  have hval : beBytesToNat ws' = wsNat256 inb 0 := by
    have h1 := ((sepConj_pure_left _).mp (by xperm_hyp hin :
      ((⌜beBytesToNat ws' = Accel.leLimbsToNat
          [wsDword inb 0, wsDword inb 8, wsDword inb 16, wsDword inb 24]
        ∧ ws'.length = 32⌝ : Assertion)
        ** (regOwns exposedRegs ** bytesRegion dsti ws'
          ** ((.x1 : Reg) ↦ᵣ ret) ** bytesRegion srci inb)) h)).1
    rw [h1.1]
    rfl
  have hlen' : ws'.length = 32 := by
    have h1 := ((sepConj_pure_left _).mp (by xperm_hyp hin :
      ((⌜beBytesToNat ws' = Accel.leLimbsToNat
          [wsDword inb 0, wsDword inb 8, wsDword inb 16, wsDword inb 24]
        ∧ ws'.length = 32⌝ : Assertion)
        ** (regOwns exposedRegs ** bytesRegion dsti ws'
          ** ((.x1 : Reg) ↦ᵣ ret) ** bytesRegion srci inb)) h)).1
    exact h1.2
  have hin1 : ((⌜beBytesToNat ws' = Accel.leLimbsToNat
        [wsDword inb 0, wsDword inb 8, wsDword inb 16, wsDword inb 24]
      ∧ ws'.length = 32⌝ : Assertion)
      ** (regOwns exposedRegs ** bytesRegion dsti ws'
        ** ((.x1 : Reg) ↦ᵣ ret) ** bytesRegion srci inb)) h := by
    xperm_hyp hin
  obtain ⟨-, hrest⟩ := (sepConj_pure_left h).mp hin1
  have hfin : ((⌜beBytesToNat ws' = wsNat256 inb 0 ∧ ws'.length = 32⌝ : Assertion)
      ** (regOwns exposedRegs ** bytesRegion dsti ws'
        ** ((.x1 : Reg) ↦ᵣ ret) ** bytesRegion srci inb)) h :=
    (sepConj_pure_left h).mpr ⟨⟨hval, hlen'⟩, hrest⟩
  xperm_hyp hfin

-- ============================================================================
-- The inline curve tangent-doubling step (CSR 0x804 = 2052)
-- ============================================================================

/-- Exposed registers other than `t0` (the point pointer). -/
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
    staged LE point, the whole 64-byte staging window rides as ONE atom, and
    it becomes the `Accel.curveDbl` tangent-doubling result in place —
    nothing else (registers or other memory) moves.  Preconditions are
    exactly the accelerator's `csrsValid`: reduced coordinates and `y ≠ 0`. -/
theorem curveStep_spec (img : List (BitVec 8))
    (hlen : img.length = 64)
    (hvalid : ∀ j, j < 64 → isValidMemAddr (arenaB + BitVec.ofNat 64 j) = true)
    (hx : wsNat256 img 0 < Accel.secpP)
    (hy : wsNat256 img 0x20 < Accel.secpP)
    (hyne : wsNat256 img 0x20 ≠ 0) :
    cpsTripleWithin 1 ((GuestAddrs.secp256k1_point_double + 104) : Word) ((GuestAddrs.secp256k1_point_double + 108) : Word) pdCr
      (((.x5 : Reg) ↦ᵣ (GuestAddrs.secc_le_p1 : Word)) ** regOwns csrsRest
        ** bytesRegion arenaB img)
      (((.x5 : Reg) ↦ᵣ (GuestAddrs.secc_le_p1 : Word)) ** regOwns csrsRest
        ** bytesRegion arenaB
          (setBytes img 0 (pairBytes 4 (Accel.curveDbl Accel.secpP
            (wsNat256 img 0) (wsNat256 img 0x20))))) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns csrsRest (by decide)
      (P := ((.x5 : Reg) ↦ᵣ (GuestAddrs.secc_le_p1 : Word)) ** bytesRegion arenaB img)
      (fun vf => ?_))
  have hcs := csrs_curveDbl_spec_within .secp256k1 ((GuestAddrs.secp256k1_point_double + 104) : Word) .x5
    (by decide) arenaB 64 img
    (fun r => if r = .x5 then (GuestAddrs.secc_le_p1 : Word) else vf r)
    hlen (by decide) hvalid
    0
    (by
      show RegFile.get _ .x5 = arenaB + BitVec.ofNat 64 0
      rw [RegFile.get, if_neg (by decide : (Reg.x5 : Reg) ≠ .x0)]
      show (if (Reg.x5 : Reg) = .x5 then (GuestAddrs.secc_le_p1 : Word) else vf .x5) = _
      rw [if_pos rfl]
      decide)
    ⟨0, rfl⟩ (by decide)
    (by rw [show CurveId.nl .secp256k1 = 4 from rfl, wsNat_four]; exact hx)
    (by
      rw [show CurveId.nl .secp256k1 = 4 from rfl, wsNat_four,
        show (0 + 8 * 4 : Nat) = 0x20 from rfl]
      exact hy)
    (by
      rw [show CurveId.nl .secp256k1 = 4 from rfl, wsNat_four,
        show (0 + 8 * 4 : Nat) = 0x20 from rfl]
      exact hyne)
  have hcsC := liftCode (cr' := pdCr) hcs (by code_mem)
  rw [show ((GuestAddrs.secp256k1_point_double + 104) : Word) + 4 = ((GuestAddrs.secp256k1_point_double + 108) : Word) from by decide,
    show CurveId.p .secp256k1 = Accel.secpP from rfl,
    show CurveId.nl .secp256k1 = 4 from rfl,
    wsNat_four, show (0 + 8 * 4 : Nat) = 0x20 from rfl, wsNat_four] at hcsC
  -- unpack the register file on both sides (same file — the step moves nothing)
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split5,
    show (if (Reg.x5 : Reg) = .x5 then (GuestAddrs.secc_le_p1 : Word) else vf .x5)
      = (GuestAddrs.secc_le_p1 : Word) from if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x5 then (GuestAddrs.secc_le_p1 : Word) else vf r) vf csrsRest
      (fun r hr => by
        show (if r = .x5 then (GuestAddrs.secc_le_p1 : Word) else vf r) = vf r
        rw [if_neg (fun (hc : r = .x5) => x5_notin_csrsRest (hc ▸ hr))])]
    at hcsC
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => ?_) hcsC
  have hq2 := sepConj_mono_left (sepConj_mono_right
    (regAtomsOf_to_regOwns vf csrsRest)) h hq
  xperm_hyp hq2

end Secp256k1PointDoubleSAsm

end EvmAsm.Codegen
