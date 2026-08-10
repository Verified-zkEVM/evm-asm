/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakCsrs

  Framed `CSRS 0x800, x10` for the keccak wrapper: peels exposed-register
  ownership around `csrs_keccak_spec_within` (which wants `regFileIs`).
  Callee-saved ambient stays outside the pack.
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakDword
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.AssertionSpec
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

set_option maxRecDepth 8000

/-- Exposed regs except `x10` (the CSRS pointer). -/
def keccakCsrsRest : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem keccakCsrsRest_nodup : keccakCsrsRest.Nodup := by decide

private theorem keccakCsrsRest_x0_free : Reg.x0 ∉ keccakCsrsRest := by decide

private theorem keccakCsrsRest_x10_free : Reg.x10 ∉ keccakCsrsRest := by decide

private theorem exposed_split_x10 :
    (∀ r, r ∈ exposedRegs ↔ r ∈ (.x10 :: keccakCsrsRest)) := by
  intro r; cases r <;> simp [exposedRegs, keccakCsrsRest]

/-- Build `RegFile` with `x10 = B` and rest from `vf`. -/
private def rfOfX10 (B : Word) (vf : Reg → Word) : RegFile :=
  fun r => if r = .x10 then B else vf r

private theorem rfOfX10_get_x10 (B : Word) (vf : Reg → Word) :
    (rfOfX10 B vf).get .x10 = B := by
  simp only [RegFile.get, rfOfX10, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
  rfl

private theorem rfOfX10_get_ne_x10 (B : Word) (vf : Reg → Word) {r : Reg}
    (hr : r ≠ .x10) (hx0 : r ≠ .x0) :
    (rfOfX10 B vf).get r = vf r := by
  simp only [RegFile.get, rfOfX10, if_neg hx0, if_neg hr]

/-- `regFileOn` agrees with `regAtomsOf` when values match on `rs`. -/
private theorem regFileOn_eq_regAtomsOf (rs : List Reg) (rf : RegFile)
    (vf : Reg → Word) (hnd : rs.Nodup)
    (hvals : ∀ r ∈ rs, rf.get r = vf r) (hx0 : Reg.x0 ∉ rs) :
    regFileOn rs rf = regAtomsOf vf rs := by
  induction rs with
  | nil =>
    simp only [regFileOn_nil, regAtomsOf_nil]
  | cons r rs ih =>
    have hr_notin : r ∉ rs := (List.nodup_cons.mp hnd).1
    have hx0' : Reg.x0 ∉ rs := fun h => hx0 (List.mem_cons_of_mem _ h)
    have hnd' : rs.Nodup := (List.nodup_cons.mp hnd).2
    have hvals' : ∀ r' ∈ rs, rf.get r' = vf r' := fun r' hr' =>
      hvals r' (List.mem_cons_of_mem _ hr')
    rw [regFileOn_cons r rs rf hr_notin, regAtomsOf_cons,
      hvals r (List.mem_cons_self ..),
      ih hnd' hvals' hx0']

/-- Pack: `regFileIs (rfOfX10 B vf) = (x10 ↦ B) ** regAtomsOf vf rest`. -/
private theorem pack_x10_rest (B : Word) (vf : Reg → Word) :
    regFileIs (rfOfX10 B vf) =
      ((.x10 ↦ᵣ B) ** regAtomsOf vf keccakCsrsRest) := by
  rw [regFileIs_eq_regFileOn,
    regFileOn_perm exposedRegs (.x10 :: keccakCsrsRest) (rfOfX10 B vf)
      exposed_split_x10,
    regFileOn_cons .x10 keccakCsrsRest (rfOfX10 B vf) keccakCsrsRest_x10_free,
    rfOfX10_get_x10]
  congr 1
  exact regFileOn_eq_regAtomsOf keccakCsrsRest (rfOfX10 B vf) vf
    keccakCsrsRest_nodup
    (fun r hr => by
      have hne : r ≠ .x10 := fun h => by subst h; exact keccakCsrsRest_x10_free hr
      have hx0 : r ≠ .x0 := fun h => by subst h; exact keccakCsrsRest_x0_free hr
      exact rfOfX10_get_ne_x10 B vf hne hx0)
    keccakCsrsRest_x0_free

/-- Framed CSRS: only `x10` is concrete; other exposed regs are owned. -/
theorem csrs_keccak_x10_own_framed
    (entry : Word) (B : Word) (ws : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (hws : ws.length = 200)
    (hb8 : B.toNat % 8 = 0)
    (hvalid : ∀ j, j < 200 → isValidMemAddr (B + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 1 entry (entry + 4)
      (CodeReq.singleton entry (.CSRS 0x800 .x10))
      (((.x10 ↦ᵣ B) ** bytesRegion B ws ** A) ** regOwns keccakCsrsRest)
      (((.x10 ↦ᵣ B) **
          bytesRegion B (setBytes ws 0 (keccakBytes ws 0)) ** A) **
        regOwns keccakCsrsRest) := by
  refine cpsTripleWithin_peel_regOwns keccakCsrsRest keccakCsrsRest_nodup
    (P := ((.x10 ↦ᵣ B) ** bytesRegion B ws ** A))
    (Q := (((.x10 ↦ᵣ B) **
        bytesRegion B (setBytes ws 0 (keccakBytes ws 0)) ** A) **
      regOwns keccakCsrsRest))
    (fun vf => ?_)
  -- Concrete rest values: pack to regFileIs, run CSRS, drop atoms → owns.
  have hp0 : (rfOfX10 B vf).get .x10 = B + BitVec.ofNat 64 0 := by
    rw [rfOfX10_get_x10, show BitVec.ofNat 64 0 = (0 : Word) from rfl]
    bv_omega
  have hcsrs :=
    csrs_keccak_spec_within entry .x10 (by decide) B 200 ws (rfOfX10 B vf)
      hws hb8 hvalid 0 hp0 (by decide : 8 ∣ 0) (by omega : 0 + 200 ≤ 200)
  have hcsrsF := cpsTripleWithin_frameR A hA hcsrs
  refine cpsTripleWithin_weaken
    (fun _ hp' => by
      -- goal P = (regFileIs**bytes)**A; hp' = (x10**bytes**A)**atoms
      rw [pack_x10_rest B vf]
      xperm_hyp hp')
    (fun h hq' => by
      -- goal Q' = ((x10 ** (bytes' ** A)) ** owns); hq' = (regFileIs**bytes')**A
      rw [pack_x10_rest B vf] at hq'
      -- hq' : (((x10 ** atoms) ** bytes') ** A)
      have hq1 :
          (((.x10 ↦ᵣ B) **
              bytesRegion B (setBytes ws 0 (keccakBytes ws 0)) ** A) **
            regAtomsOf vf keccakCsrsRest) h := by
        xperm_hyp hq'
      exact sepConj_mono_right
        (regAtomsOf_to_regOwns vf keccakCsrsRest) h hq1)
    hcsrsF

/-- Flattened association form used by absorb compose. -/
theorem csrs_keccak_x10_own_flat
    (entry : Word) (B : Word) (ws : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (hws : ws.length = 200)
    (hb8 : B.toNat % 8 = 0)
    (hvalid : ∀ j, j < 200 → isValidMemAddr (B + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 1 entry (entry + 4)
      (CodeReq.singleton entry (.CSRS 0x800 .x10))
      ((.x10 ↦ᵣ B) ** regOwns keccakCsrsRest ** bytesRegion B ws ** A)
      ((.x10 ↦ᵣ B) ** regOwns keccakCsrsRest **
        bytesRegion B (setBytes ws 0 (keccakBytes ws 0)) ** A) := by
  have h := csrs_keccak_x10_own_framed entry B ws A hA hws hb8 hvalid
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) h

end EvmAsm.Codegen.Proofs
