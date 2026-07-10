/-
  EvmAsm.Codegen.Programs.Secp256k1FieldMulModPSAsm

  `secf_mul_mod_p` via the **multi-RW-subwindow callee adapter**
  (`EvmAsm/Rv64/SAsm/RwSubwindow.lean`, bead evm-asm-4ch8f.38.5) — the
  acceptance consumer for the converter+arithMod crypto caller layer.

  The routine is an sp-frame (`ra`/`s0`/`s1`) around a SEQUENCE of callees
  that each write a different subwindow of the global LE staging arena
  (`secf_le_a` … `secf_mul_params`, one contiguous `.data` block):

  ```
    s0 := a1 ; s1 := a2
    la a1, secf_le_a      ; call secf_be_to_le   -- writes arena[0x00..0x20)
    a0 := s0
    la a1, secf_le_b      ; call secf_be_to_le   -- writes arena[0x20..0x40)
    la t0, secf_mul_params; csrs 2050, t0       -- writes arena[0x40..0x60)
    la a0, secf_le_d ; a1 := s1
    call secf_le_to_be                          -- reads _d, writes out
    a0 := 0
  ```

  Each call's write window is carved from the arena atom
  (`bytesRegion_window_focus`), handed to the callee as its whole `rw`
  (the converter contracts are `Fn.retSpecFlat`-derived, #9988), and
  merged back (`bytesRegion_window_update`) — the other subwindows
  (the zero addend, the modulus, the parameter block) PROVABLY ride
  through untouched (`wsNat256_setBytes_high` etc.), which is exactly what
  lets the inline `arithMod` accelerator step
  (`csrs_arith256Mod_spec_within`, CSR 0x802 = 2050) decode its operands
  from the accumulated arena image.  The `la`-materialized subwindow
  addresses are `la_resolve`-proven (#10059/#10064).

  **Genuine post** (`secfMulModP_spec`): with `m₀ = wsNat256 ws 0xA0` (the
  modulus staged in the arena — the guest data pins it to the secp256k1 prime)
  and the addend cell zero, the external output holds
  `beBytesToNat out' = (beBytesToNat aBE * beBytesToNat bBE + 0) % m₀`
  (`Accel.arith256Mod`), `sp`/`ra`/`s0`/`s1` restored to entry, inputs and
  non-written arena cells untouched.  Byte-transparent: the emitted
  `secfMulModP_prog` IS `abiFrameProg (-32)/(+32)` over the body
  (kernel-checked `rfl`), at the `#guard`-tied `GuestAddrs`.
-/

import EvmAsm.Codegen.Programs.Secp256k1Field
import EvmAsm.Codegen.Programs.Secp256k1FieldConvSAsm
import EvmAsm.Codegen.Programs.Secp256k1FieldLeToBeSAsm
import EvmAsm.Rv64.SAsm.RwSubwindow
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.LaResolve
import EvmAsm.Crypto.PowLadder
import EvmAsm.Codegen.Programs.Secp256k1FieldMulModPSAsmStage

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

namespace Secp256k1FieldMulModPSAsm

open Secp256k1FieldConvSAsm (secfBeToLeFn secfBeToLeFn_spec secfLeToBeFn secfLeToBeFn_spec)

#guard GuestAddrs.secf_mul_mod_p = 0x8002043c
#guard abiFrameProg (-32 : BitVec 12) (32 : BitVec 12) mulFrame mulBody = secfMulModP_prog

/-- Entry values of the saved registers. -/
def mulVals (ret v8 v9 : Word) : Reg → Word :=
  fun r => match r with
  | .x1 => ret | .x8 => v8 | .x9 => v9 | _ => 0

/-- Post-body values: `ra` holds the last call's link address, `s0`/`s1`
    the operand/output pointer copies. -/
def mulVals' (bPtr outPtr : Word) : Reg → Word :=
  fun r => match r with
  | .x1 => ((GuestAddrs.secf_mul_mod_p + 80) : Word) | .x8 => bPtr | .x9 => outPtr | _ => 0

/-- Exposed registers beyond the three pinned argument pointers. -/
def mulRest : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x13, .x14, .x15, .x16, .x17]

/-- The modular product the routine computes. -/
def mulResult (aBE bBE ws : List (BitVec 8)) : Nat :=
  Accel.arith256Mod (beBytesToNat aBE) (beBytesToNat bBE)
    (wsNat256 ws 0x60) (wsNat256 ws 0xA0)

private theorem ownsExposedSplit :
    regOwns exposedRegs = (regOwns [.x10, .x11] ** regOwns convScratch) := by
  show regOwns
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [convScratch, regOwns_cons, regOwns_nil, sepConj_emp_right']
  funext h
  exact propext ⟨fun hp => by xperm_hyp hp, fun hp => by xperm_hyp hp⟩

private theorem ownsConvSplit12 :
    regOwns convScratch = (regOwn .x12 ** regOwns mulRest) := by
  show regOwns
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [mulRest, regOwns_cons, regOwns_nil]
  funext h
  exact propext ⟨fun hp => by xperm_hyp hp, fun hp => by xperm_hyp hp⟩

private theorem ownsSplit1112 :
    regOwns outRest = (regOwn .x11 ** regOwn .x12 ** regOwns mulRest) := by
  show regOwns
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [mulRest, regOwns_cons, regOwns_nil]
  funext h
  exact propext ⟨fun hp => by xperm_hyp hp, fun hp => by xperm_hyp hp⟩

/-- Pull three data out of an ∃-post. -/
private theorem exists_pull3 {α β γ : Sort _} {F : α → β → γ → Assertion}
    {G : Assertion} (h : PartialState) (hin : ∃ a b c, (G ** F a b c) h) :
    (G ** (fun hp => ∃ a b c, F a b c hp) : Assertion) h := by
  obtain ⟨a, b, c, h1, h2, hd, hu, hG, hF⟩ := hin
  exact ⟨h1, h2, hd, hu, hG, ⟨a, b, c, hF⟩⟩

/-- `pcFree` for a triply-existential post. -/
private theorem pcFree_exists3 {α β γ : Sort _} {F : α → β → γ → Assertion}
    (h : ∀ a b c, (F a b c).pcFree) :
    Assertion.pcFree (fun hp => ∃ a b c, F a b c hp) := by
  rintro hp ⟨a, b, c, hF⟩
  exact h a b c hp hF

/-- **`secf_mul_mod_p` at its linked address** (genuine post): the external
    output window holds the big-endian encoding of
    `(beBytesToNat aBE * beBytesToNat bBE + c₀) mod m₀`, where `c₀`/`m₀`
    are the arena's staged addend/modulus cells (the guest data pins them
    to `0` / the secp256k1 prime); `sp`/`ra`/`s0`/`s1` restored to entry; the
    inputs and every non-written arena subwindow framed through. -/
theorem secfMulModP_spec (sp0 aPtr bPtr outPtr ret v8 v9 : Word)
    (aBE bBE outOld ws : List (BitVec 8))
    (halen : aBE.length = 32) (hblen : bBE.length = 32)
    (holen : outOld.length = 32) (hwslen : ws.length = 232)
    (hwfA : Region.wf ⟨aPtr, aBE⟩) (hwfB : Region.wf ⟨bPtr, bBE⟩)
    (hoal : outPtr.toNat % 8 = 0) (hoov : outPtr.toNat + 32 < 2 ^ 64)
    (hovalid : ∀ k, k < 32 → isValidMemAddr (outPtr + BitVec.ofNat 64 k) = true)
    (harval : ∀ j, j < 232 → isValidMemAddr (arenaS + BitVec.ofNat 64 j) = true)
    (hdA : aPtr.toNat + 32 ≤ (0xa3c053e8 : Nat) ∨ (0xa3c05408 : Nat) ≤ aPtr.toNat)
    (hdB : bPtr.toNat + 32 ≤ (0xa3c05408 : Nat) ∨ (0xa3c05428 : Nat) ≤ bPtr.toNat)
    (hdO : (0xa3c05448 : Nat) ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ (0xa3c05428 : Nat))
    (hpa : wsDword ws 0xC0 = arenaS + BitVec.ofNat 64 0)
    (hpb : wsDword ws 0xC8 = arenaS + BitVec.ofNat 64 0x20)
    (hpc : wsDword ws 0xD0 = arenaS + BitVec.ofNat 64 0x60)
    (hpm : wsDword ws 0xD8 = arenaS + BitVec.ofNat 64 0xA0)
    (hpd : wsDword ws 0xE0 = arenaS + BitVec.ofNat 64 0x40)
    (hmne : wsNat256 ws 0xA0 ≠ 0)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      (1 + mulFrame.length
        + (17 + ((secfBeToLeFn 0 0 [] []).body.steps + 1) * 2
            + ((secfLeToBeFn 0 0 [] []).body.steps + 1))
        + mulFrame.length + 1 + 1)
      (GuestAddrs.secf_mul_mod_p : Word) ret mulCr
      ((.x2 ↦ᵣ sp0) ** regsAt mulFrame (mulVals ret v8 v9)
        ** frameSlotsOwn mulFrame (sp0 + signExtend12 (-32 : BitVec 12))
        ** (((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr)
          ** ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns mulRest
          ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
          ** bytesRegion outPtr outOld ** bytesRegion arenaS ws))
      ((.x2 ↦ᵣ sp0) ** regsAt mulFrame (mulVals ret v8 v9)
        ** frameSlotsSaved mulFrame (sp0 + signExtend12 (-32 : BitVec 12))
            (mulVals ret v8 v9)
        ** (fun hp => ∃ ws₁ ws₂ out',
            ((⌜wsNat256 ws₁ 0 = beBytesToNat aBE ∧ ws₁.length = 32
              ∧ wsNat256 ws₂ 0 = beBytesToNat bBE ∧ ws₂.length = 32
              ∧ beBytesToNat out' = mulResult aBE bBE ws ∧ out'.length = 32⌝
              ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12
              ** regOwns mulRest
              ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
              ** bytesRegion outPtr out'
              ** bytesRegion arenaS
                (setBytes (setBytes (setBytes ws 0 ws₁) 0x20 ws₂) 0x40
                  (leBytes32 (mulResult aBE bBE ws))))) hp)) := by
  -- ---- the single-exit body triple, in `abiFrame_spec` shape ----
  have hbody : cpsTripleWithin
      (17 + ((secfBeToLeFn 0 0 [] []).body.steps + 1) * 2
        + ((secfLeToBeFn 0 0 [] []).body.steps + 1))
      ((GuestAddrs.secf_mul_mod_p : Word) + BitVec.ofNat 64 (4 * (1 + mulFrame.length)))
      ((GuestAddrs.secf_mul_mod_p : Word)
        + BitVec.ofNat 64 (4 * (1 + mulFrame.length + mulBody.length)))
      mulCr
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12)))
        ** regsAt mulFrame (mulVals ret v8 v9)
        ** frameSlotsSaved mulFrame (sp0 + signExtend12 (-32 : BitVec 12))
            (mulVals ret v8 v9)
        ** (((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr)
          ** ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns mulRest
          ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
          ** bytesRegion outPtr outOld ** bytesRegion arenaS ws))
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12)))
        ** regsAt mulFrame (mulVals' bPtr outPtr)
        ** frameSlotsSaved mulFrame (sp0 + signExtend12 (-32 : BitVec 12))
            (mulVals ret v8 v9)
        ** (fun hp => ∃ ws₁ ws₂ out',
            ((⌜wsNat256 ws₁ 0 = beBytesToNat aBE ∧ ws₁.length = 32
              ∧ wsNat256 ws₂ 0 = beBytesToNat bBE ∧ ws₂.length = 32
              ∧ beBytesToNat out' = mulResult aBE bBE ws ∧ out'.length = 32⌝
              ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12
              ** regOwns mulRest
              ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
              ** bytesRegion outPtr out'
              ** bytesRegion arenaS
                (setBytes (setBytes (setBytes ws 0 ws₁) 0x20 ws₂) 0x40
                  (leBytes32 (mulResult aBE bBE ws))))) hp)) := by
    have hentry : (GuestAddrs.secf_mul_mod_p : Word)
          + BitVec.ofNat 64 (4 * (1 + mulFrame.length))
        = ((GuestAddrs.secf_mul_mod_p + 16) : Word) := by decide
    have hexit : (GuestAddrs.secf_mul_mod_p : Word)
          + BitVec.ofNat 64 (4 * (1 + mulFrame.length + mulBody.length))
        = ((GuestAddrs.secf_mul_mod_p + 84) : Word) := by decide
    rw [hentry, hexit]
    -- ---- the continuation past the first call (per written `_a` window) ----
    have hB : ∀ ws₁ : List (BitVec 8),
        cpsTripleWithin
          ((4 + ((secfBeToLeFn 0 0 [] []).body.steps + 1))
            + (7 + ((secfLeToBeFn 0 0 [] []).body.steps + 1) + 1))
          ((GuestAddrs.secf_mul_mod_p + 36) : Word) ((GuestAddrs.secf_mul_mod_p + 84) : Word) mulCr
          (⌜wsNat256 ws₁ 0 = beBytesToNat aBE ∧ ws₁.length = 32⌝
            ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 36) : Word)) ** regOwns exposedRegs
            ** bytesRegion (0xa3c053e8 : Word) ws₁ ** bytesRegion aPtr aBE
            ** (.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr) ** bytesRegion bPtr bBE
            ** bytesRegion outPtr outOld ** windowRest arenaS ws 0 32)
          (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 80) : Word)) ** (.x8 ↦ᵣ bPtr)
            ** (.x9 ↦ᵣ outPtr)
            ** (fun hp => ∃ ws₁' ws₂' out',
              ((⌜wsNat256 ws₁' 0 = beBytesToNat aBE ∧ ws₁'.length = 32
                ∧ wsNat256 ws₂' 0 = beBytesToNat bBE ∧ ws₂'.length = 32
                ∧ beBytesToNat out' = mulResult aBE bBE ws ∧ out'.length = 32⌝
                ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12
                ** regOwns mulRest
                ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
                ** bytesRegion outPtr out'
                ** bytesRegion arenaS
                  (setBytes (setBytes (setBytes ws 0 ws₁') 0x20 ws₂') 0x40
                    (leBytes32 (mulResult aBE bBE ws))))) hp)) := by
      intro ws₁
      refine cpsTripleWithin_pure_pre (fun hfacts₁ => ?_)
      obtain ⟨hf1a, hf1b⟩ := hfacts₁
      -- ---- the stage-C continuation (per written `_b` window) ----
      have hC : ∀ ws₂ : List (BitVec 8),
          cpsTripleWithin (7 + ((secfLeToBeFn 0 0 [] []).body.steps + 1) + 1)
            ((GuestAddrs.secf_mul_mod_p + 52) : Word) ((GuestAddrs.secf_mul_mod_p + 84) : Word) mulCr
            (⌜wsNat256 ws₂ 0 = beBytesToNat bBE ∧ ws₂.length = 32⌝
              ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 52) : Word)) ** regOwns exposedRegs
              ** bytesRegion (0xa3c05408 : Word) ws₂ ** bytesRegion bPtr bBE
              ** (.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr) ** bytesRegion aPtr aBE
              ** bytesRegion outPtr outOld
              ** windowRest arenaS (setBytes ws 0 ws₁) 0x20 32)
            (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 80) : Word)) ** (.x8 ↦ᵣ bPtr)
              ** (.x9 ↦ᵣ outPtr)
              ** (fun hp => ∃ ws₁' ws₂' out',
                ((⌜wsNat256 ws₁' 0 = beBytesToNat aBE ∧ ws₁'.length = 32
                  ∧ wsNat256 ws₂' 0 = beBytesToNat bBE ∧ ws₂'.length = 32
                  ∧ beBytesToNat out' = mulResult aBE bBE ws
                  ∧ out'.length = 32⌝
                  ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12
                  ** regOwns mulRest
                  ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
                  ** bytesRegion outPtr out'
                  ** bytesRegion arenaS
                    (setBytes (setBytes (setBytes ws 0 ws₁') 0x20 ws₂') 0x40
                      (leBytes32 (mulResult aBE bBE ws))))) hp)) := by
        intro ws₂
        refine cpsTripleWithin_pure_pre (fun hfacts₂ => ?_)
        obtain ⟨hf2a, hf2b⟩ := hfacts₂
        -- decode the accumulated arena image at the accelerator operands
        have e0 : wsNat256 (setBytes (setBytes ws 0 ws₁) 0x20 ws₂) 0
            = beBytesToNat aBE := by
          rw [wsNat256_setBytes_low (by omega),
            wsNat256_setBytes_inside hf1b (by omega), hf1a]
        have e1 : wsNat256 (setBytes (setBytes ws 0 ws₁) 0x20 ws₂) 0x20
            = beBytesToNat bBE := by
          rw [wsNat256_setBytes_inside hf2b (by rw [length_setBytes]; omega),
            hf2a]
        have e2 : wsNat256 (setBytes (setBytes ws 0 ws₁) 0x20 ws₂) 0x60
            = wsNat256 ws 0x60 := by
          rw [wsNat256_setBytes_high (by omega),
            wsNat256_setBytes_high (by omega)]
        have e3 : wsNat256 (setBytes (setBytes ws 0 ws₁) 0x20 ws₂) 0xA0
            = wsNat256 ws 0xA0 := by
          rw [wsNat256_setBytes_high (by omega),
            wsNat256_setBytes_high (by omega)]
        have hstage := stageC_spec aPtr bPtr outPtr aBE bBE outOld
          (setBytes (setBytes ws 0 ws₁) 0x20 ws₂)
          (by rw [length_setBytes, length_setBytes]; exact hwslen)
          holen hoal hoov hovalid harval hdO
          (by
            rw [wsDword_setBytes_high (by omega),
              wsDword_setBytes_high (by omega)]
            exact hpa)
          (by
            rw [wsDword_setBytes_high (by omega),
              wsDword_setBytes_high (by omega)]
            exact hpb)
          (by
            rw [wsDword_setBytes_high (by omega),
              wsDword_setBytes_high (by omega)]
            exact hpc)
          (by
            rw [wsDword_setBytes_high (by omega),
              wsDword_setBytes_high (by omega)]
            exact hpm)
          (by
            rw [wsDword_setBytes_high (by omega),
              wsDword_setBytes_high (by omega)]
            exact hpd)
          (by
            rw [wsNat256_setBytes_high (by omega),
              wsNat256_setBytes_high (by omega)]
            exact hmne)
        have hcompute : Accel.arith256Mod
            (wsNat256 (setBytes (setBytes ws 0 ws₁) 0x20 ws₂) 0)
            (wsNat256 (setBytes (setBytes ws 0 ws₁) 0x20 ws₂) 0x20)
            (wsNat256 (setBytes (setBytes ws 0 ws₁) 0x20 ws₂) 0x60)
            (wsNat256 (setBytes (setBytes ws 0 ws₁) 0x20 ws₂) 0xA0)
            = mulResult aBE bBE ws := by
          rw [e0, e1, e2, e3]
          rfl
        rw [hcompute] at hstage
        refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hstage
        · -- reassemble the arena around the written `_b` window
          have hp1 : ((((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 52) : Word)) ** (.x8 ↦ᵣ bPtr)
              ** (.x9 ↦ᵣ outPtr) ** regOwns exposedRegs
              ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
              ** bytesRegion outPtr outOld
              ** (bytesRegion (arenaS + BitVec.ofNat 64 0x20) ws₂
                ** windowRest arenaS (setBytes ws 0 ws₁) 0x20 32))
              : Assertion) h := by
            rw [show arenaS + BitVec.ofNat 64 0x20 = (0xa3c05408 : Word)
              from by decide]
            xperm_hyp hp
          rw [← bytesRegion_window_update arenaS (setBytes ws 0 ws₁) ws₂ 0x20 32
            (by rw [length_setBytes]; omega) (by norm_num) (by norm_num)
            hf2b] at hp1
          xperm_hyp hp1
        · -- rebuild the whole-routine ∃-post from the stage-C witness
          obtain ⟨out', hin⟩ := hq
          obtain ⟨hf3, hrest⟩ := (sepConj_pure_left h).mp hin
          rw [ownsSplit1112] at hrest
          have hfin : ((⌜wsNat256 ws₁ 0 = beBytesToNat aBE ∧ ws₁.length = 32
              ∧ wsNat256 ws₂ 0 = beBytesToNat bBE ∧ ws₂.length = 32
              ∧ beBytesToNat out' = mulResult aBE bBE ws ∧ out'.length = 32⌝
              : Assertion)
              ** (((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12
                ** regOwns mulRest
                ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
                ** bytesRegion outPtr out'
                ** bytesRegion arenaS
                  (setBytes (setBytes (setBytes ws 0 ws₁) 0x20 ws₂) 0x40
                    (leBytes32 (mulResult aBE bBE ws)))
                ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 80) : Word)) ** (.x8 ↦ᵣ bPtr)
                ** (.x9 ↦ᵣ outPtr))) h :=
            (sepConj_pure_left h).mpr
              ⟨⟨hf1a, hf1b, hf2a, hf2b, hf3.1, hf3.2⟩, by xperm_hyp hrest⟩
          have hout : ((((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 80) : Word)) ** (.x8 ↦ᵣ bPtr)
              ** (.x9 ↦ᵣ outPtr))
              ** (fun hp => ∃ ws₁' ws₂' out'',
                ((⌜wsNat256 ws₁' 0 = beBytesToNat aBE ∧ ws₁'.length = 32
                  ∧ wsNat256 ws₂' 0 = beBytesToNat bBE ∧ ws₂'.length = 32
                  ∧ beBytesToNat out'' = mulResult aBE bBE ws
                  ∧ out''.length = 32⌝
                  ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12
                  ** regOwns mulRest
                  ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
                  ** bytesRegion outPtr out''
                  ** bytesRegion arenaS
                    (setBytes (setBytes (setBytes ws 0 ws₁') 0x20 ws₂') 0x40
                      (leBytes32 (mulResult aBE bBE ws))))) hp)
              : Assertion) h :=
            exists_pull3 h ⟨ws₁, ws₂, out', by xperm_hyp hfin⟩
          xperm_hyp hout
      -- ---- reassemble the `_a` splice, peel `a0`/`a1`, run mv/la/call ----
      refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
        (cpsTripleWithin_peel_regOwns [.x10, .x11] (by decide)
          (P := ((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 36) : Word)) ** regOwns convScratch
            ** bytesRegion aPtr aBE ** (.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr)
            ** bytesRegion bPtr bBE ** bytesRegion outPtr outOld
            ** bytesRegion arenaS (setBytes ws 0 ws₁))
          (fun vf => ?_))
      · rw [ownsExposedSplit] at hp
        have hp1 : ((((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 36) : Word)) ** regOwns [.x10, .x11]
            ** regOwns convScratch ** bytesRegion aPtr aBE ** (.x8 ↦ᵣ bPtr)
            ** (.x9 ↦ᵣ outPtr) ** bytesRegion bPtr bBE
            ** bytesRegion outPtr outOld
            ** (bytesRegion (arenaS + BitVec.ofNat 64 0) ws₁
              ** windowRest arenaS ws 0 32)) : Assertion) h := by
          rw [show arenaS + BitVec.ofNat 64 0 = (0xa3c053e8 : Word)
            from by decide]
          xperm_hyp hp
        rw [← bytesRegion_window_update arenaS ws ws₁ 0 32 (by omega)
          (by norm_num) (by norm_num) hf1b] at hp1
        xperm_hyp hp1
      · -- a0 := s0
        have hmv10 := liftCode (cr' := mulCr)
          (mv_spec_gen_within .x10 .x8 bPtr (vf .x10) ((GuestAddrs.secf_mul_mod_p + 36) : Word)
            (by decide))
          (by code_mem)
        rw [show ((GuestAddrs.secf_mul_mod_p + 36) : Word) + 4 = ((GuestAddrs.secf_mul_mod_p + 40) : Word) from by decide]
          at hmv10
        -- la a1, secf_le_b
        have hla11 := la_materialize_within .x11 (vf .x11) ((GuestAddrs.secf_mul_mod_p + 40) : Word)
          (0xa3c05408 : Word) (cr := mulCr) (by decide) (by decide)
          (by code_mem) (by code_mem)
        rw [show ((GuestAddrs.secf_mul_mod_p + 40) : Word) + 8 = ((GuestAddrs.secf_mul_mod_p + 48) : Word) from by decide]
          at hla11
        -- the second conversion call over the FOCUSED `_b` window
        have hflat2 := secfBeToLeFlat_spec ((GuestAddrs.secf_mul_mod_p + 52) : Word) bPtr
          (0xa3c05408 : Word) bBE (((setBytes ws 0 ws₁).drop 0x20).take 32)
          hblen
          (by
            rw [List.length_take, List.length_drop, length_setBytes, hwslen]
            omega)
          hwfB
          (by
            refine ⟨?_, ?_, ?_⟩
            · show ((0xa3c05408 : Word)).toNat % 8 = 0
              decide
            · show ((0xa3c05408 : Word)).toNat + 32 < 2 ^ 64
              decide
            · intro k hk
              have hk' : k < 32 := hk
              rw [show (0xa3c05408 : Word) + BitVec.ofNat 64 k
                  = arenaS + BitVec.ofNat 64 (0x20 + k) from by
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
                  BitVec.toNat_ofNat,
                  show ((0xa3c05408 : Word)).toNat = 0xa3c05408 from by decide,
                  show (arenaS).toNat = 0xa3c053e8 from by decide]
                omega]
              exact harval (0x20 + k) (by omega))
          (by
            have h := hwfB.2.1
            rwa [hblen] at h)
          (by decide)
          (by
            have hdst : ((0xa3c05408 : Word)).toNat = 0xa3c05408 := by decide
            rcases hdB with h | h
            · left
              rw [hdst]
              exact h
            · right
              rw [hdst]
              omega)
          (by decide)
        have hcallee2 : cpsTripleWithin
            ((secfBeToLeFn bPtr (0xa3c05408 : Word) bBE
              (((setBytes ws 0 ws₁).drop 0x20).take 32)).body.steps + 1)
            (GuestAddrs.secf_be_to_le : Word) ((GuestAddrs.secf_mul_mod_p + 52) : Word) mulCr
            (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 52) : Word))
              ** ((.x10 ↦ᵣ bPtr) ** (.x11 ↦ᵣ (0xa3c05408 : Word))
                ** regOwns convScratch
                ** bytesRegion (0xa3c05408 : Word)
                    (((setBytes ws 0 ws₁).drop 0x20).take 32)
                ** bytesRegion bPtr bBE))
            (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 52) : Word))
              ** (fun hp => ∃ ws',
                ((⌜wsNat256 ws' 0 = beBytesToNat bBE ∧ ws'.length = 32⌝
                  ** regOwns exposedRegs ** bytesRegion (0xa3c05408 : Word) ws'
                  ** bytesRegion bPtr bBE)) hp)) := by
          refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
            (fun h hq => ?_) hflat2
          obtain ⟨ws', hin⟩ := hq
          refine exists_pull h ⟨ws', ?_⟩
          xperm_hyp hin
        have hcall2 := callWithin_spec ((GuestAddrs.secf_mul_mod_p + 48) : Word) (GuestAddrs.secf_be_to_le : Word)
          ((GuestAddrs.secf_mul_mod_p + 36) : Word)
          (jalOff GuestAddrs.secf_be_to_le (GuestAddrs.secf_mul_mod_p + 48))
          ((secfBeToLeFn bPtr (0xa3c05408 : Word) bBE
            (((setBytes ws 0 ws₁).drop 0x20).take 32)).body.steps + 1)
          (by decide) (by code_mem) (by pcf) hcallee2
        rw [show ((GuestAddrs.secf_mul_mod_p + 48) : Word) + 4 = ((GuestAddrs.secf_mul_mod_p + 52) : Word) from by decide]
          at hcall2
        rw [show (secfBeToLeFn bPtr (0xa3c05408 : Word) bBE
            (((setBytes ws 0 ws₁).drop 0x20).take 32)).body.steps
          = (secfBeToLeFn 0 0 [] []).body.steps from rfl] at hcall2
        -- ---- frames + chain ----
        have hmv10F := cpsTripleWithin_frameR
          (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 36) : Word)) ** (.x11 ↦ᵣ vf .x11)
            ** regOwns convScratch ** bytesRegion aPtr aBE ** (.x9 ↦ᵣ outPtr)
            ** bytesRegion bPtr bBE ** bytesRegion outPtr outOld
            ** bytesRegion arenaS (setBytes ws 0 ws₁))
          (by pcf) hmv10
        have hla11F := cpsTripleWithin_frameR
          (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 36) : Word)) ** (.x8 ↦ᵣ bPtr)
            ** (.x9 ↦ᵣ outPtr) ** (.x10 ↦ᵣ bPtr) ** regOwns convScratch
            ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
            ** bytesRegion outPtr outOld
            ** bytesRegion arenaS (setBytes ws 0 ws₁))
          (by pcf) hla11
        have hcall2F := cpsTripleWithin_frameR
          ((.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr) ** bytesRegion aPtr aBE
            ** bytesRegion outPtr outOld
            ** windowRest arenaS (setBytes ws 0 ws₁) 0x20 32)
          (by
            exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj (bytesRegion_pcFree _ _)
                (pcFree_sepConj (bytesRegion_pcFree _ _)
                  (pcFree_windowRest _ _ _ _))))) hcall2
        have hd1 := cpsTripleWithin_seq_perm_same_cr
          (fun _ hp => by xperm_hyp hp) hmv10F hla11F
        have hd2 := cpsTripleWithin_seq_perm_same_cr
          (fun h hp => by
            rw [bytesRegion_window_focus arenaS (setBytes ws 0 ws₁) 0x20 32
                  (by rw [length_setBytes]; omega) (by norm_num) (by norm_num),
                show arenaS + BitVec.ofNat 64 0x20 = (0xa3c05408 : Word)
                  from by decide] at hp
            xperm_hyp hp) hd1 hcall2F
        have hd2' : cpsTripleWithin
            (4 + ((secfBeToLeFn 0 0 [] []).body.steps + 1))
            ((GuestAddrs.secf_mul_mod_p + 36) : Word) ((GuestAddrs.secf_mul_mod_p + 52) : Word) mulCr
            ((((.x8 : Reg) ↦ᵣ bPtr) ** (.x10 ↦ᵣ vf .x10))
              ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 36) : Word)) ** (.x11 ↦ᵣ vf .x11)
                ** regOwns convScratch ** bytesRegion aPtr aBE
                ** (.x9 ↦ᵣ outPtr) ** bytesRegion bPtr bBE
                ** bytesRegion outPtr outOld
                ** bytesRegion arenaS (setBytes ws 0 ws₁)))
            (fun hp => ∃ ws₂,
              ((⌜wsNat256 ws₂ 0 = beBytesToNat bBE ∧ ws₂.length = 32⌝
                ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 52) : Word)) ** regOwns exposedRegs
                ** bytesRegion (0xa3c05408 : Word) ws₂ ** bytesRegion bPtr bBE
                ** (.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr) ** bytesRegion aPtr aBE
                ** bytesRegion outPtr outOld
                ** windowRest arenaS (setBytes ws 0 ws₁) 0x20 32)) hp) := by
          refine cpsTripleWithin_mono_nSteps (by omega)
            (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
              (fun h hq => ?_) hd2)
          have hq1 : ((fun hp => ∃ ws',
              ((⌜wsNat256 ws' 0 = beBytesToNat bBE ∧ ws'.length = 32⌝
                ** regOwns exposedRegs ** bytesRegion (0xa3c05408 : Word) ws'
                ** bytesRegion bPtr bBE)) hp)
              ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 52) : Word)) ** (.x8 ↦ᵣ bPtr)
                ** (.x9 ↦ᵣ outPtr) ** bytesRegion aPtr aBE
                ** bytesRegion outPtr outOld
                ** windowRest arenaS (setBytes ws 0 ws₁) 0x20 32)
              : Assertion) h := by
            xperm_hyp hq
          obtain ⟨ws₂, hin⟩ := (sepConj_exists_left h).mp hq1
          exact ⟨ws₂, by xperm_hyp hin⟩
        refine cpsTripleWithin_weaken (fun _ hp => by
            simp only [regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right']
              at hp
            xperm_hyp hp)
          (fun _ hq => hq)
          (cpsTripleWithin_seq_exists_same_cr hd2' hC)
    -- ---- stage A: mv s0,a1 ; mv s1,a2 ; la a1,_a ; call secf_be_to_le ----
    have hm1 := liftCode (cr' := mulCr)
      (mv_spec_gen_within .x8 .x11 bPtr v8 ((GuestAddrs.secf_mul_mod_p + 16) : Word) (by decide))
      (by code_mem)
    rw [show ((GuestAddrs.secf_mul_mod_p + 16) : Word) + 4 = ((GuestAddrs.secf_mul_mod_p + 20) : Word) from by decide] at hm1
    have hm2 := liftCode (cr' := mulCr)
      (mv_spec_gen_within .x9 .x12 outPtr v9 ((GuestAddrs.secf_mul_mod_p + 20) : Word) (by decide))
      (by code_mem)
    rw [show ((GuestAddrs.secf_mul_mod_p + 20) : Word) + 4 = ((GuestAddrs.secf_mul_mod_p + 24) : Word) from by decide] at hm2
    have hla := la_materialize_within .x11 bPtr ((GuestAddrs.secf_mul_mod_p + 24) : Word)
      (0xa3c053e8 : Word) (cr := mulCr) (by decide) (by decide)
      (by code_mem) (by code_mem)
    rw [show ((GuestAddrs.secf_mul_mod_p + 24) : Word) + 8 = ((GuestAddrs.secf_mul_mod_p + 32) : Word) from by decide] at hla
    have hflat1 := secfBeToLeFlat_spec ((GuestAddrs.secf_mul_mod_p + 36) : Word) aPtr
      (0xa3c053e8 : Word) aBE ((ws.drop 0).take 32)
      halen
      (by
        rw [List.length_take, List.length_drop, hwslen]
        omega)
      hwfA
      (by
        refine ⟨?_, ?_, ?_⟩
        · show ((0xa3c053e8 : Word)).toNat % 8 = 0
          decide
        · show ((0xa3c053e8 : Word)).toNat + 32 < 2 ^ 64
          decide
        · intro k hk
          have hk' : k < 32 := hk
          rw [show (0xa3c053e8 : Word) = arenaS from by decide]
          exact harval k (by omega))
      (by
        have h := hwfA.2.1
        rwa [halen] at h)
      (by decide)
      (by
        have hdst : ((0xa3c053e8 : Word)).toNat = 0xa3c053e8 := by decide
        rcases hdA with h | h
        · left
          rw [hdst]
          exact h
        · right
          rw [hdst]
          omega)
      (by decide)
    have hcallee1 : cpsTripleWithin
        ((secfBeToLeFn aPtr (0xa3c053e8 : Word) aBE
          ((ws.drop 0).take 32)).body.steps + 1)
        (GuestAddrs.secf_be_to_le : Word) ((GuestAddrs.secf_mul_mod_p + 36) : Word) mulCr
        (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 36) : Word))
          ** ((.x10 ↦ᵣ aPtr) ** (.x11 ↦ᵣ (0xa3c053e8 : Word))
            ** regOwns convScratch
            ** bytesRegion (0xa3c053e8 : Word) ((ws.drop 0).take 32)
            ** bytesRegion aPtr aBE))
        (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 36) : Word))
          ** (fun hp => ∃ ws',
            ((⌜wsNat256 ws' 0 = beBytesToNat aBE ∧ ws'.length = 32⌝
              ** regOwns exposedRegs ** bytesRegion (0xa3c053e8 : Word) ws'
              ** bytesRegion aPtr aBE)) hp)) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun h hq => ?_) hflat1
      obtain ⟨ws', hin⟩ := hq
      refine exists_pull h ⟨ws', ?_⟩
      xperm_hyp hin
    have hcall1 := callWithin_spec ((GuestAddrs.secf_mul_mod_p + 32) : Word) (GuestAddrs.secf_be_to_le : Word) ret
      (jalOff GuestAddrs.secf_be_to_le (GuestAddrs.secf_mul_mod_p + 32))
      ((secfBeToLeFn aPtr (0xa3c053e8 : Word) aBE
        ((ws.drop 0).take 32)).body.steps + 1)
      (by decide) (by code_mem) (by pcf) hcallee1
    rw [show ((GuestAddrs.secf_mul_mod_p + 32) : Word) + 4 = ((GuestAddrs.secf_mul_mod_p + 36) : Word) from by decide]
      at hcall1
    rw [show (secfBeToLeFn aPtr (0xa3c053e8 : Word) aBE
        ((ws.drop 0).take 32)).body.steps
      = (secfBeToLeFn 0 0 [] []).body.steps from rfl] at hcall1
    -- ---- frames + chain ----
    have hm1F := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ ret) ** (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ aPtr)
        ** (.x12 ↦ᵣ outPtr) ** regOwns mulRest
        ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
        ** bytesRegion outPtr outOld ** bytesRegion arenaS ws)
      (by pcf) hm1
    have hm2F := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ ret) ** (.x8 ↦ᵣ bPtr) ** (.x10 ↦ᵣ aPtr)
        ** (.x11 ↦ᵣ bPtr) ** regOwns mulRest
        ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
        ** bytesRegion outPtr outOld ** bytesRegion arenaS ws)
      (by pcf) hm2
    have hlaF := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ ret) ** (.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr)
        ** (.x10 ↦ᵣ aPtr) ** (.x12 ↦ᵣ outPtr) ** regOwns mulRest
        ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
        ** bytesRegion outPtr outOld ** bytesRegion arenaS ws)
      (by pcf) hla
    have hcall1F := cpsTripleWithin_frameR
      ((.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr) ** bytesRegion bPtr bBE
        ** bytesRegion outPtr outOld ** windowRest arenaS ws 0 32)
      (by
        exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj (bytesRegion_pcFree _ _)
            (pcFree_sepConj (bytesRegion_pcFree _ _)
              (pcFree_windowRest _ _ _ _))))) hcall1
    have ha1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hm1F hm2F
    have ha2 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) ha1 hlaF
    have ha3 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        rw [bytesRegion_window_focus arenaS ws 0 32 (by omega) (by norm_num)
              (by norm_num),
            show arenaS + BitVec.ofNat 64 0 = (0xa3c053e8 : Word)
              from by decide] at hp
        have hp1 : ((.x12 ↦ᵣ outPtr)
            ** (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ aPtr)
              ** (.x11 ↦ᵣ (0xa3c053e8 : Word)) ** regOwns mulRest
              ** bytesRegion (0xa3c053e8 : Word) ((ws.drop 0).take 32)
              ** bytesRegion aPtr aBE ** (.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr)
              ** bytesRegion bPtr bBE ** bytesRegion outPtr outOld
              ** windowRest arenaS ws 0 32)) h := by
          xperm_hyp hp
        have hp2 := sepConj_mono (regIs_to_regOwn .x12 outPtr)
          (fun _ hh => hh) h hp1
        have hp3 : (regOwns convScratch
            ** (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ aPtr)
              ** (.x11 ↦ᵣ (0xa3c053e8 : Word))
              ** bytesRegion (0xa3c053e8 : Word) ((ws.drop 0).take 32)
              ** bytesRegion aPtr aBE ** (.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr)
              ** bytesRegion bPtr bBE ** bytesRegion outPtr outOld
              ** windowRest arenaS ws 0 32)) h := by
          rw [ownsConvSplit12]
          xperm_hyp hp2
        xperm_hyp hp3) ha2 hcall1F
    have ha3' : cpsTripleWithin (5 + ((secfBeToLeFn 0 0 [] []).body.steps + 1))
        ((GuestAddrs.secf_mul_mod_p + 16) : Word) ((GuestAddrs.secf_mul_mod_p + 36) : Word) mulCr
        ((((.x11 : Reg) ↦ᵣ bPtr) ** (.x8 ↦ᵣ v8))
          ** (((.x1 : Reg) ↦ᵣ ret) ** (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ aPtr)
            ** (.x12 ↦ᵣ outPtr) ** regOwns mulRest
            ** bytesRegion aPtr aBE ** bytesRegion bPtr bBE
            ** bytesRegion outPtr outOld ** bytesRegion arenaS ws))
        (fun hp => ∃ ws₁,
          ((⌜wsNat256 ws₁ 0 = beBytesToNat aBE ∧ ws₁.length = 32⌝
            ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 36) : Word)) ** regOwns exposedRegs
            ** bytesRegion (0xa3c053e8 : Word) ws₁ ** bytesRegion aPtr aBE
            ** (.x8 ↦ᵣ bPtr) ** (.x9 ↦ᵣ outPtr) ** bytesRegion bPtr bBE
            ** bytesRegion outPtr outOld ** windowRest arenaS ws 0 32)) hp)
        := by
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun h hq => ?_) ha3)
      have hq1 : ((fun hp => ∃ ws',
          ((⌜wsNat256 ws' 0 = beBytesToNat aBE ∧ ws'.length = 32⌝
            ** regOwns exposedRegs ** bytesRegion (0xa3c053e8 : Word) ws'
            ** bytesRegion aPtr aBE)) hp)
          ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.secf_mul_mod_p + 36) : Word)) ** (.x8 ↦ᵣ bPtr)
            ** (.x9 ↦ᵣ outPtr) ** bytesRegion bPtr bBE
            ** bytesRegion outPtr outOld
            ** windowRest arenaS ws 0 32) : Assertion) h := by
        xperm_hyp hq
      obtain ⟨ws₁, hin⟩ := (sepConj_exists_left h).mp hq1
      exact ⟨ws₁, by xperm_hyp hin⟩
    have hcore := cpsTripleWithin_seq_exists_same_cr ha3' hB
    have hcoreF := cpsTripleWithin_frameR
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12)))
        ** ((sp0 + signExtend12 (-32 : BitVec 12)
              + signExtend12 (0 : BitVec 12)) ↦ₘ ret)
        ** ((sp0 + signExtend12 (-32 : BitVec 12)
              + signExtend12 (8 : BitVec 12)) ↦ₘ v8)
        ** ((sp0 + signExtend12 (-32 : BitVec 12)
              + signExtend12 (16 : BitVec 12)) ↦ₘ v9))
      (by pcf) hcore
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun h hq => ?_)
      (cpsTripleWithin_mono_nSteps (by omega) hcoreF)
    · simp only [mulFrame, regsAt, frameSlotsSaved, mulVals,
        List.foldr_cons, List.foldr_nil, sepConj_emp_right'] at hp
      xperm_hyp hp
    · simp only [mulFrame, regsAt, frameSlotsSaved, mulVals, mulVals',
        List.foldr_cons, List.foldr_nil, sepConj_emp_right']
      xperm_hyp hq
  -- ---- wrap the body with the ABI frame ----
  exact abiFrame_spec
    (posImm := (32 : BitVec 12))
    (hframe := rfl)
    (hne := by decide)
    (hbound := by decide)
    (hprogBound := by decide)
    (hret := rfl)
    (halign := halign)
    (hframeRestore := sext_frameRestore _ _ _ (by decide))
    (hcpF := by pcf)
    (hcpF' := pcFree_exists3 (fun ws₁ ws₂ out' => by pcf))
    (hsub := by code_mem)
    (hbody := hbody)

#print axioms secfBeToLeFlat_spec
#print axioms secfLeToBeFlat_spec
#print axioms csrsStep_spec
#print axioms secfMulModP_spec

end Secp256k1FieldMulModPSAsm

end EvmAsm.Codegen
