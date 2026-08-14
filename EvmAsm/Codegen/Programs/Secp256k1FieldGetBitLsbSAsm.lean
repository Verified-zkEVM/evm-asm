import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Codegen.Programs.Secp256k1Field

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.Stmt

namespace Secp256k1FieldGetBitLsbSAsm

def secfGetBitLsbOffset (bitIdx : Word) : Word :=
  (31 : Word) - (bitIdx >>> 3)

def secfGetBitLsbResult (src : Word) (bs : List (BitVec 8)) (bitIdx : Word) : Word :=
  ((((Region.byteAt ⟨src, bs⟩ (src + secfGetBitLsbOffset bitIdx)).zeroExtend 64 : Word)
      >>> (((bitIdx &&& (7 : Word)).toNat) % 64)) &&& (1 : Word))

def secfGetBitLsbFn (src bitIdx : Word) (bs : List (BitVec 8)) : Fn where
  name := "secfGetBitLsb"
  region := ⟨src, bs⟩
  rw := RwRegion.empty
  pre := fun rf ws A =>
    rf.get .x10 = src ∧ rf.get .x11 = bitIdx ∧ ws = [] ∧ bs.length = 32 ∧
    Region.loadOk ⟨src, bs⟩ (src + secfGetBitLsbOffset bitIdx) 1 ∧ A = empAssertion
  post := fun rf ws A =>
    rf.get .x10 = secfGetBitLsbResult src bs bitIdx ∧ ws = [] ∧ A = empAssertion
  body := .block "body"
    [ .SRLI .x5 .x11 (3 : BitVec 6),
      .LI .x6 (31 : Word),
      .SUB .x5 .x6 .x5,
      .ADD .x5 .x10 .x5,
      .LBU .x6 .x5 (0 : BitVec 12),
      .ANDI .x7 .x11 (7 : BitVec 12),
      .SRL .x6 .x6 .x7,
      .ANDI .x10 .x6 (1 : BitVec 12) ]

theorem secfGetBitLsb_byte_tie :
    (secfGetBitLsbFn 0 0 []).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = secfGetBitLsb_prog := rfl

#guard ((secfGetBitLsbFn 0 0 []).body.flatten 0).length = 8
#guard (secfGetBitLsbFn 0 0 []).body.flatten 0 =
  (secfGetBitLsbFn 0 0 []).body.flatten 0x80000000

private theorem se12_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem se12_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
private theorem se12_7 : signExtend12 (7 : BitVec 12) = (7 : Word) := by decide

theorem secfGetBitLsbFn_spec (src bitIdx : Word) (bs : List (BitVec 8))
    (base : Word) (h_ro_wf : Region.wf ⟨src, bs⟩) :
    (secfGetBitLsbFn src bitIdx bs).Spec base := by
  vcgen
  case region => exact ⟨h_ro_wf, RwRegion.empty_wf⟩
  case secfGetBitLsb.body.mem =>
    rintro rf ws A h_ws h_pre
    obtain ⟨h_x10, h_x11, h_ws_eq, h_bs_len, h_load, h_A⟩ := h_pre
    subst ws
    simp only [secfGetBitLsbFn, secfGetBitLsbOffset, blockVCs, execInstrRF,
      aluSem, loadSem, storeSem, inRw, RwRegion.empty, RegFile.get_set_self,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, se12_0,
      h_x10, h_x11]
    refine ⟨trivial, trivial, trivial, trivial, ?_, trivial, trivial, trivial, trivial⟩
    simpa [secfGetBitLsbOffset] using h_load
  case secfGetBitLsb.post =>
    rintro rf' ws' A' ⟨rf₀, ws₀, h_ws₀, h_pre, rfl, rfl⟩
    obtain ⟨h_x10, h_x11, h_ws_eq, h_bs_len, h_load, h_A⟩ := h_pre
    subst ws'
    refine ⟨?_, rfl, h_A⟩
    simp only [secfGetBitLsbFn, secfGetBitLsbResult, secfGetBitLsbOffset,
      execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem, inRw,
      RwRegion.empty, RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
      reduceCtorEq, not_false_eq_true, se12_0, se12_1, se12_7, h_x10, h_x11]
    have h_no_rw (a : Word) : ¬ a.toNat + 1 ≤ ([] : List (BitVec 8)).length := by
      simp
    simp only [h_no_rw, if_false, RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
      reduceCtorEq, not_false_eq_true]
    simp [h_x11]

/-! ## Flat linked-entry contract

    The structured `Fn.Spec` above is the machine proof for the eight
    instructions.  This adapter is the whole-routine contract at the linked
    guest address: callers own `a0`/`a1`, the read-only 32-byte source region,
    and the remaining exposed registers, and get the selected low bit in `a0`.
    The adapter keeps the machine proof and the ABI-facing triple separate.
-/

def secfGetBitLsbCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.secf_get_bit_lsb : Word) secfGetBitLsb_prog

def secfGetBitLsbScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_getBit (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) **
          regAtomsOf vf secfGetBitLsbScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [secfGetBitLsbScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem getBit_args_notin_scratch :
    ∀ r ∈ secfGetBitLsbScratch, r ≠ (.x10 : Reg) ∧ r ≠ (.x11 : Reg) := by
  decide

theorem secfGetBitLsbFlat_spec (ret src bitIdx : Word)
    (bs : List (BitVec 8))
    (hwf : (Region.mk src bs).wf)
    (hlen : bs.length = 32)
    (hload : Region.loadOk (Region.mk src bs)
      (src + secfGetBitLsbOffset bitIdx) 1)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      ((secfGetBitLsbFn src bitIdx bs).body.steps + 1)
      (GuestAddrs.secf_get_bit_lsb : Word) ret secfGetBitLsbCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ src) ** (.x11 ↦ᵣ bitIdx) **
        regOwns secfGetBitLsbScratch ** bytesRegion src bs)
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ secfGetBitLsbResult src bs bitIdx) **
        regOwn .x11 ** regOwns secfGetBitLsbScratch ** bytesRegion src bs) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns secfGetBitLsbScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ src) **
        (.x11 ↦ᵣ bitIdx) ** bytesRegion src bs)
      (fun vf => ?_))
  have hpre : (secfGetBitLsbFn src bitIdx bs).pre
      (fun r => if r = .x10 then src else if r = .x11 then bitIdx else vf r)
      [] empAssertion := by
    refine ⟨?_, ?_, rfl, hlen, hload, rfl⟩
    · show RegFile.get _ .x10 = src
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = bitIdx
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
  have had := Fn.retSpecFlat
    (secfGetBitLsbFn src bitIdx bs)
    (GuestAddrs.secf_get_bit_lsb : Word)
    (secfGetBitLsbFn_spec src bitIdx bs
      (GuestAddrs.secf_get_bit_lsb : Word) hwf)
    (by show 4 * (8 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then src else if r = .x11 then bitIdx else vf r)
    ([] : List (BitVec 8)) rfl hpre
    (fun _ _ _ hpost => hpost.2.2)
    (Q := (.x10 ↦ᵣ secfGetBitLsbResult src bs bitIdx) **
      regOwn .x11 ** regOwns secfGetBitLsbScratch)
    (fun rf' ws' hlen' hpost' hp hh => by
      obtain ⟨hx10', hws_eq, -⟩ := hpost'
      subst ws'
      rw [show (secfGetBitLsbFn src bitIdx bs).rw = RwRegion.empty from rfl,
        bytesRegion_nil, sepConj_emp_right'] at hh
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_getBit,
        show rf' .x10 = secfGetBitLsbResult src bs bitIdx from by
          rw [show rf' .x10 = rf'.get .x10 from by
            rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]]
          exact hx10'] at hh
      have hh2 := sepConj_mono_right
        (sepConj_mono
          (regIs_to_regOwn .x11 (rf' .x11))
          (regAtomsOf_to_regOwns (fun r => rf' r) secfGetBitLsbScratch)) hp hh
      xperm_hyp hh2)
  rw [show (secfGetBitLsbFn src bitIdx bs).programRet
      (GuestAddrs.secf_get_bit_lsb : Word) = secfGetBitLsb_prog from rfl] at had
  have hadC := liftCode (cr' := secfGetBitLsbCr) had (by
    unfold secfGetBitLsbCr
    code_mem)
  rw [show (secfGetBitLsbFn src bitIdx bs).rw = RwRegion.empty from rfl,
    show (secfGetBitLsbFn src bitIdx bs).region = Region.mk src bs from rfl,
    bytesRegion_nil, sepConj_emp_right'] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_getBit,
    show (if (Reg.x10 : Reg) = .x10 then src else
        if (Reg.x10 : Reg) = .x11 then bitIdx else vf .x10) = src from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then src else
        if (Reg.x11 : Reg) = .x11 then bitIdx else vf .x11) = bitIdx from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then src else if r = .x11 then bitIdx else vf r)
      vf secfGetBitLsbScratch
      (fun r hr => by
        show (if r = .x10 then src else if r = .x11 then bitIdx else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) =>
              (getBit_args_notin_scratch r hr).1 hc),
            if_neg (fun (hc : r = .x11) =>
              (getBit_args_notin_scratch r hr).2 hc)])]
    at hadC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hadC

end Secp256k1FieldGetBitLsbSAsm

end EvmAsm.Codegen
