/-
  EvmAsm.Codegen.Proofs.CallFrameForwardGasFlatEntry

  The flat whole-routine contract for `call_frame_forward_gas` at its
  linked guest address (#12988) — derived from the structured
  `callFrameForwardGasFn_spec` by the existing `Fn.retSpecFlat` adapter.
  Lives outside the SAsm module so the (rebuild-heavy) `GuestAddrs`
  dependency stays out of the derivation's import cone, mirroring
  `MptWitnessIndexFlatEntry.lean`.
-/

import EvmAsm.Codegen.Programs.CallFrameForwardGasSAsm
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.FnFlat

namespace EvmAsm.Codegen.CallFrameForwardGasSAsm

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

/-! ## The flat whole-routine contract at the guest entry (#12988)

    Derived from `callFrameForwardGasFn_spec` by the existing
    `Fn.retSpecFlat` adapter — the allowlist's stated blocker ("no flat
    whole-routine `cpsTripleWithin` exists … until the `Fn.retSpecFlat`
    lift is derived") was an un-instantiated adapter, not missing
    machinery.  Register-only leaf, so both the read-only region and the
    writable window collapse. -/

/-- The exposed registers the routine's contract does not pin on entry. -/
def cffgScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x13, .x14, .x15, .x16, .x17]

/-- On return `a2` is no longer pinned either. -/
def cffgScratchPost : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x12, .x13, .x14, .x15, .x16, .x17]

private theorem cffg_split_pre (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** (.x12 ↦ᵣ vf .x12) **
          regAtomsOf vf cffgScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [cffgScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem cffg_split_post (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) **
          regAtomsOf vf cffgScratchPost) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [cffgScratchPost, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_cffgScratch : (.x10 : Reg) ∉ cffgScratch := by decide
private theorem x11_notin_cffgScratch : (.x11 : Reg) ∉ cffgScratch := by decide
private theorem x12_notin_cffgScratch : (.x12 : Reg) ∉ cffgScratch := by decide

/-- ⭐ **`call_frame_forward_gas` at its linked guest address.**  Entered
    with `a0 = gas_left`, `a1 = requested`, `a2 = value_nonzero` and an
    aligned return address, it returns `a1 = cffgCap requested gas_left`
    (the EIP-150 cap) and `a0 = cap + stipend value_nonzero`. -/
theorem callFrameForwardGasFlat_spec (gl rq vn ret : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((callFrameForwardGasFn gl rq vn).body.steps + 1)
      (GuestAddrs.call_frame_forward_gas : Word) ret
      (CodeReq.ofProg (GuestAddrs.call_frame_forward_gas : Word)
        callFrameForwardGas_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ gl) ** (.x11 ↦ᵣ rq) **
        (.x12 ↦ᵣ vn) ** regOwns cffgScratch)
      (((.x1 : Reg) ↦ᵣ ret) **
        (.x10 ↦ᵣ (cffgCap rq gl + MessageCallGasSAsm.stipend vn)) **
        (.x11 ↦ᵣ cffgCap rq gl) ** regOwns cffgScratchPost) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns cffgScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ gl) ** (.x11 ↦ᵣ rq) **
        (.x12 ↦ᵣ vn))
      (fun vf => ?_))
  have had := Fn.retSpecFlat (callFrameForwardGasFn gl rq vn)
    (GuestAddrs.call_frame_forward_gas : Word)
    (callFrameForwardGasFn_spec gl rq vn
      (GuestAddrs.call_frame_forward_gas : Word))
    (by show 4 * (11 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then gl else if r = .x11 then rq
      else if r = .x12 then vn else vf r)
    ([] : List (BitVec 8))
    rfl
    (by
      refine ⟨⟨?_, ?_, ?_⟩, rfl⟩
      · show RegFile.get _ .x10 = gl
        rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
        exact if_pos rfl
      · show RegFile.get _ .x11 = rq
        rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
        rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
        exact if_pos rfl
      · show RegFile.get _ .x12 = vn
        rw [RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
        rw [if_neg (by decide : (Reg.x12 : Reg) ≠ .x10),
          if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
        exact if_pos rfl)
    (fun _ _ _ h => h.2)
    (Q := (.x10 ↦ᵣ (cffgCap rq gl + MessageCallGasSAsm.stipend vn)) **
      (.x11 ↦ᵣ cffgCap rq gl) ** regOwns cffgScratchPost)
    (fun rf' ws' hws' hpost' hp hh => by
      obtain ⟨⟨hx10', hx11'⟩, -⟩ := hpost'
      obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hws'
      rw [show (callFrameForwardGasFn gl rq vn).rw.base
            = RwRegion.empty.base from rfl,
        bytesRegion_nil, sepConj_emp_right'] at hh
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        cffg_split_post,
        show rf' .x10 = cffgCap rq gl + MessageCallGasSAsm.stipend vn from by
          rw [show rf' .x10 = rf'.get .x10 from by
            rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]]
          exact hx10',
        show rf' .x11 = cffgCap rq gl from by
          rw [show rf' .x11 = rf'.get .x11 from by
            rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]]
          exact hx11'] at hh
      have hh2 := sepConj_mono_right (sepConj_mono_right
        (regAtomsOf_to_regOwns (fun r => rf' r) cffgScratchPost)) hp hh
      xperm_hyp hh2)
  rw [show (callFrameForwardGasFn gl rq vn).programRet
        (GuestAddrs.call_frame_forward_gas : Word)
      = callFrameForwardGas_prog from rfl] at had
  rw [show (callFrameForwardGasFn gl rq vn).rw = RwRegion.empty from rfl,
    show (callFrameForwardGasFn gl rq vn).region = Region.empty from rfl,
    show (Region.empty).bytes = ([] : List (BitVec 8)) from rfl] at had
  simp only [bytesRegion_nil, sepConj_emp_right'] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    cffg_split_pre] at had
  rw [show (if (Reg.x10 : Reg) = .x10 then gl else if (Reg.x10 : Reg) = .x11
        then rq else if (Reg.x10 : Reg) = .x12 then vn else vf .x10) = gl
      from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then gl else if (Reg.x11 : Reg) = .x11
        then rq else if (Reg.x11 : Reg) = .x12 then vn else vf .x11) = rq
      from by rw [if_neg (by decide)]; exact if_pos rfl,
    show (if (Reg.x12 : Reg) = .x10 then gl else if (Reg.x12 : Reg) = .x11
        then rq else if (Reg.x12 : Reg) = .x12 then vn else vf .x12) = vn
      from by rw [if_neg (by decide), if_neg (by decide)]; exact if_pos rfl,
    regAtomsOf_congr (fun r => if r = .x10 then gl else if r = .x11 then rq
        else if r = .x12 then vn else vf r) vf cffgScratch
      (fun r hr => by
        show (if r = .x10 then gl else if r = .x11 then rq
          else if r = .x12 then vn else vf r) = vf r
        rw [if_neg (fun hc => x10_notin_cffgScratch
              (by rw [← hc]; exact hr)),
          if_neg (fun hc => x11_notin_cffgScratch
              (by rw [← hc]; exact hr)),
          if_neg (fun hc => x12_notin_cffgScratch
              (by rw [← hc]; exact hr))])] at had
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

end EvmAsm.Codegen.CallFrameForwardGasSAsm
