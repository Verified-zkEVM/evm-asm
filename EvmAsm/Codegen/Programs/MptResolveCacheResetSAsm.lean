/- Byte-identical SAsm verification of `mpt_resolve_cache_reset`. -/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.LaResolve
import EvmAsm.Codegen.Programs.MptSetAcc

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace MptResolveCacheResetSAsm

#guard GuestAddrs.mpt_resolve_cache_reset = 0x800063d0
#guard GuestAddrs.mset_res_cache_valid = 0xa3c672e0

def zeroWindow (orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  List.replicate (8 * i) (0 : BitVec 8) ++ orig.drop (8 * i)

theorem zeroWindow_zero (orig : List (BitVec 8)) : zeroWindow orig 0 = orig := by
  simp [zeroWindow]

theorem zeroWindow_done (orig : List (BitVec 8)) (h : orig.length = 32768) :
    zeroWindow orig 4096 = List.replicate 32768 (0 : BitVec 8) := by
  simp only [zeroWindow, Nat.reduceMul,
    List.drop_eq_nil_of_le (by omega : orig.length ≤ 32768), List.append_nil]

theorem length_zeroWindow (orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 32768) (hi : i ≤ 4096) : (zeroWindow orig i).length = 32768 := by
  simp only [zeroWindow, List.length_append, List.length_replicate, List.length_drop, h]
  omega

theorem zeroWindow_step (orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 32768) (hi : i < 4096) :
    setBytes (zeroWindow orig i) (8 * i) (dwordBytes (0 : Word)) =
      zeroWindow orig (i + 1) := by
  rw [zeroWindow]
  rw [setBytes_append_right _ _ _ _ (by simp)]
  simp only [List.length_replicate, Nat.sub_self]
  have hsuf : (orig.drop (8 * i)).length = 32768 - 8 * i := by simp [h]
  have hfit : 0 + (dwordBytes (0 : Word)).length ≤ (orig.drop (8 * i)).length := by
    rw [length_dwordBytes, hsuf]
    omega
  have hslot := setBytes_slot (orig.drop (8 * i)) (dwordBytes (0 : Word)) 0 hfit
  rw [List.drop_zero, length_dwordBytes] at hslot
  have hdrop : (setBytes (orig.drop (8 * i)) 0 (dwordBytes (0 : Word))).drop 8 =
      (orig.drop (8 * i)).drop 8 := by
    simpa [length_dwordBytes] using
      (setBytes_drop_of_le (dwordBytes (0 : Word)) (orig.drop (8 * i)) 0 8 (by
        rw [length_dwordBytes]))
  have hset : setBytes (List.drop (8 * i) orig) 0 (dwordBytes (0 : Word)) =
      dwordBytes (0 : Word) ++ (List.drop (8 * i) orig).drop 8 := by
    conv_lhs =>
      rw [← List.take_append_drop 8
        (setBytes (List.drop (8 * i) orig) 0 (dwordBytes 0))]
    rw [hslot, hdrop]
  rw [hset]
  rw [show (List.drop (8 * i) orig).drop 8 = orig.drop (8 * (i + 1)) from by
    rw [List.drop_drop]
    congr 1]
  rw [show dwordBytes (0 : Word) = List.replicate 8 (0 : BitVec 8) from by decide]
  simp only [zeroWindow]
  rw [← List.append_assoc]
  congr 1
  rw [List.replicate_append_replicate]
  congr

def zeroStepBlock : List Instr :=
  [.SD .x5 .x0 (0 : BitVec 12),
   .ADDI .x5 .x5 (8 : BitVec 12),
   .ADDI .x6 .x6 (-1 : BitVec 12)]

def zeroStepRf (rf : RegFile) : RegFile :=
  let r1 := rf.set .x5 (rf.get .x5 + signExtend12 (8 : BitVec 12))
  r1.set .x6 (r1.get .x6 + signExtend12 (-1 : BitVec 12))

theorem zeroStepRf_get_x5 (rf : RegFile) :
    (zeroStepRf rf).get .x5 = rf.get .x5 + signExtend12 (8 : BitVec 12) := by
  unfold zeroStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem zeroStepRf_get_x6 (rf : RegFile) :
    (zeroStepRf rf).get .x6 = rf.get .x6 + signExtend12 (-1 : BitVec 12) := by
  unfold zeroStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem zero_engine (reg : Region) (dst : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Nat) (hi : i < 4096)
    (hx5 : rf.get .x5 = dst + BitVec.ofNat 64 (8 * i)) :
    execBlock reg dst rf ws zeroStepBlock =
      (zeroStepRf rf, setBytes ws (8 * i) (dwordBytes (0 : Word))) := by
  have haddr : (rf.get .x5 + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * i := by
    rw [hx5, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  apply Prod.ext
  · rfl
  · show setBytes ws ((rf.get .x5 + signExtend12 (0 : BitVec 12) - dst).toNat)
        (dwordBytes (rf.get .x0)) = setBytes ws (8 * i) (dwordBytes (0 : Word))
    rw [haddr, RegFile.get_x0]

def zeroInv (dst : Word) (orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws A =>
    rf.get .x5 = dst + BitVec.ofNat 64 (8 * i) ∧
    rf.get .x6 = BitVec.ofNat 64 (4096 - i) ∧
    i ≤ 4096 ∧ orig.length = 32768 ∧ ws = zeroWindow orig i ∧ A = empAssertion

def cacheResetBody (orig : List (BitVec 8)) : Stmt :=
  .block "init" [.LUI .x6 (1 : BitVec 20)] ;;;
  .while "loop" (.bne .x6 .x0) 4096
    (zeroInv (GuestAddrs.mset_res_cache_valid : Word) orig)
    (.block "zero" zeroStepBlock) ;;;
  .block "done" []

def cacheResetFn (orig : List (BitVec 8)) : Fn where
  name := "mptResolveCacheReset"
  rw := ⟨GuestAddrs.mset_res_cache_valid, 32768⟩
  pre := fun rf ws A =>
    rf.get .x5 = GuestAddrs.mset_res_cache_valid ∧ ws = orig ∧
      orig.length = 32768 ∧ A = empAssertion
  post := fun _ ws A =>
    ws = List.replicate 32768 (0 : BitVec 8) ∧ A = empAssertion
  body := cacheResetBody orig

theorem cacheReset_byte_tie :
    [.AUIPC .x5 (laHi GuestAddrs.mset_res_cache_valid
        (GuestAddrs.mpt_resolve_cache_reset + 0)),
     .ADDI .x5 .x5 (laLo GuestAddrs.mset_res_cache_valid
        (GuestAddrs.mpt_resolve_cache_reset + 0))] ++
    (cacheResetBody []).flatten (GuestAddrs.mpt_resolve_cache_reset + 8) ++
      [.JALR .x0 .x1 (0 : BitVec 12)] = mptResolveCacheReset_prog := by
  rfl

theorem cacheResetFn_spec (orig : List (BitVec 8))
    (hwf : RwRegion.wf ⟨GuestAddrs.mset_res_cache_valid, 32768⟩) :
    (cacheResetFn orig).Spec (GuestAddrs.mpt_resolve_cache_reset + 8) := by
  have hbase : (cacheResetFn orig).rw.base = GuestAddrs.mset_res_cache_valid := rfl
  vcgen
  case region => exact ⟨Region.empty_wf, hwf⟩
  case mptResolveCacheReset.loop.inv_init =>
    rintro rf' ws' A' h
    rcases h with ⟨rf0, ws0, -, hpre, rfl, rfl⟩
    rcases hpre with ⟨hx5, hws0, hlen, hA⟩
    simp only [hbase]
    refine ⟨?_, ?_, by omega, hlen, ?_, hA⟩
    · simp only [cacheResetFn, cacheResetBody, execBlock_cons, execBlock_nil,
        execInstrRF, aluSem, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, hx5]
      simp
    · simp only [cacheResetFn, cacheResetBody, execBlock_cons, execBlock_nil,
        execInstrRF, aluSem, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true]
      rfl
    · exact hws0.trans (zeroWindow_zero orig).symm
  case mptResolveCacheReset.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf0, ws0, -, ⟨⟨hx5, hx6, hle, hlen, hws0, hA⟩, hcond⟩,
      rfl, rfl⟩
    simp only [hbase]
    have hlt : i < 4096 := by
      by_contra hnot
      have hi4096 : i = 4096 := by omega
      subst hi4096
      exact hcond (by simp [hx6])
    rw [zero_engine _ GuestAddrs.mset_res_cache_valid rf0 ws0 i hlt hx5]
    refine ⟨?_, ?_, by omega, hlen, ?_, hA⟩
    · rw [zeroStepRf_get_x5, hx5,
        show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
        show (8 : Word).toNat = 8 from by decide]
      omega
    · rw [zeroStepRf_get_x6, hx6,
        show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      bv_omega
    · rw [hws0, zeroWindow_step orig i hlen hlt]
  case mptResolveCacheReset.loop.exhausted =>
    rintro rf ws A ⟨-, hx6, -, -, -, -⟩
    simp [Cond.holds, hx6]
  case mptResolveCacheReset.loop.body.zero.mem =>
    rintro rf ws A hlen ⟨i, hi, ⟨hx5, hx6, hle, horiglen, hws, hA⟩, hcond⟩
    have hlt : i < 4096 := by
      by_contra hnot
      have hi4096 : i = 4096 := by omega
      subst hi4096
      exact hcond (by simp [hx6])
    have haddr : (rf.get .x5 + signExtend12 (0 : BitVec 12) -
        GuestAddrs.mset_res_cache_valid).toNat = 8 * i := by
      rw [hx5, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      bv_omega
    have hlen32768 : ws.length = 32768 := by
      change ws.length = 32768 at hlen
      exact hlen
    simp only [zeroStepBlock, blockVCs, loadSem, storeSem, inRw, hbase, haddr,
      hlen32768, and_true]
    constructor
    · omega
    · exact Nat.dvd_mul_right 8 i
  case mptResolveCacheReset.post =>
    rintro rf ws A ⟨rf0, ws0, -, ⟨⟨i, hi, hx5, hx6, hle, hlen, hws, hA⟩, hncond⟩,
      rfl, rfl⟩
    have hi4096 : i = 4096 := by
      simp only [Cond.holds, hx6, RegFile.get_x0, not_not] at hncond
      change BitVec.ofNat 64 (4096 - i) = (0 : Word) at hncond
      have hzero := congrArg BitVec.toNat hncond
      change (4096 - i) % 2 ^ 64 = 0 at hzero
      rw [Nat.mod_eq_of_lt (by omega : 4096 - i < 2 ^ 64)] at hzero
      omega
    subst hi4096
    constructor
    · rw [hws, zeroWindow_done orig hlen]
    · exact hA

def cacheResetCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.mpt_resolve_cache_reset : Word) mptResolveCacheReset_prog

def cacheScratch : List Reg :=
  [.x6, .x7, .x28, .x29, .x30, .x31,
   .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split (vf : Reg → Word) :
    regAtomsOf vf exposedRegs = ((.x5 ↦ᵣ vf .x5) ** regAtomsOf vf cacheScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [cacheScratch, regAtomsOf_cons, regAtomsOf_nil]

private theorem x5_notin_scratch : (.x5 : Reg) ∉ cacheScratch := by decide

set_option linter.constructorNameAsVariable false in
private theorem cacheResetTail_spec (retAddr : Word) (orig : List (BitVec 8))
    (hlen : orig.length = 32768)
    (hwf : RwRegion.wf ⟨GuestAddrs.mset_res_cache_valid, 32768⟩)
    (halign : (retAddr &&& ~~~(1 : Word)) = retAddr) :
    cpsTripleWithin ((cacheResetFn orig).body.steps + 1)
      (GuestAddrs.mpt_resolve_cache_reset + 8 : Word) retAddr cacheResetCr
      (((.x1 : Reg) ↦ᵣ retAddr) **
        ((.x5 : Reg) ↦ᵣ (GuestAddrs.mset_res_cache_valid : Word)) **
        regOwns cacheScratch ** bytesRegion GuestAddrs.mset_res_cache_valid orig)
      (((.x1 : Reg) ↦ᵣ retAddr) ** regOwn .x5 ** regOwns cacheScratch **
        bytesRegion GuestAddrs.mset_res_cache_valid
          (List.replicate 32768 (0 : BitVec 8))) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns cacheScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ retAddr) **
        ((.x5 : Reg) ↦ᵣ (GuestAddrs.mset_res_cache_valid : Word)) **
        bytesRegion GuestAddrs.mset_res_cache_valid orig)
      (fun vf => ?_))
  have had := Fn.retSpecFlat (cacheResetFn orig)
    (GuestAddrs.mpt_resolve_cache_reset + 8 : Word)
    (cacheResetFn_spec orig hwf)
    (by change 4 * (6 + 1) ≤ 2 ^ 64; decide)
    retAddr halign
    (fun r => if r = .x5 then (GuestAddrs.mset_res_cache_valid : Word) else vf r)
    orig hlen
    (by
      refine ⟨?_, rfl, hlen, rfl⟩
      show RegFile.get
          (fun r => if r = .x5 then (GuestAddrs.mset_res_cache_valid : Word) else vf r)
          .x5 = GuestAddrs.mset_res_cache_valid
      rw [RegFile.get, if_neg (by decide : (Reg.x5 : Reg) ≠ .x0)]
      exact if_pos rfl)
    (fun _ _ _ h => h.2)
    (Q := regOwn .x5 ** regOwns cacheScratch **
      bytesRegion GuestAddrs.mset_res_cache_valid
        (List.replicate 32768 (0 : BitVec 8)))
    (fun rf' ws' _ hpost hp hh => by
      obtain ⟨rfl, -⟩ := hpost
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split] at hh
      rw [show (cacheResetFn orig).rw.base = GuestAddrs.mset_res_cache_valid from rfl] at hh
      have hh2 : (((regOwn .x5 ** regOwns cacheScratch) **
          bytesRegion GuestAddrs.mset_res_cache_valid
            (List.replicate 32768 (0 : BitVec 8))) hp) :=
        sepConj_mono
          (sepConj_mono (regIs_to_regOwn .x5 (rf' .x5))
            (regAtomsOf_to_regOwns (fun r => rf' r) cacheScratch))
          (fun _ h => h) hp hh
      xperm_hyp hh2)
  rw [show (cacheResetFn orig).programRet
      (GuestAddrs.mpt_resolve_cache_reset + 8 : Word) =
      mptResolveCacheReset_prog.drop 2 from rfl] at had
  have hadC := liftCode (cr' := cacheResetCr) had
    (by unfold cacheResetCr; code_mem)
  rw [show (cacheResetFn orig).region = Region.empty from rfl,
    show bytesRegion Region.empty.base Region.empty.bytes = empAssertion from
      bytesRegion_nil _, sepConj_emp_right', sepConj_emp_right'] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split,
    show (if (Reg.x5 : Reg) = .x5 then (GuestAddrs.mset_res_cache_valid : Word)
      else vf .x5) = GuestAddrs.mset_res_cache_valid from if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x5 then (GuestAddrs.mset_res_cache_valid : Word) else vf r)
      vf cacheScratch
      (fun r hr => by
        show (if r = .x5 then (GuestAddrs.mset_res_cache_valid : Word) else vf r) = vf r
        exact if_neg (by
          intro hc
          subst r
          exact x5_notin_scratch hr)),
    show (cacheResetFn orig).rw.base = GuestAddrs.mset_res_cache_valid from rfl] at hadC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hadC

/-- Whole linked routine: materialize the cache-valid base, zero all 4096
    dwords, and return with the save-area bytes exactly zero. -/
theorem mptResolveCacheReset_spec (old5 retAddr : Word) (orig : List (BitVec 8))
    (hlen : orig.length = 32768)
    (hwf : RwRegion.wf ⟨GuestAddrs.mset_res_cache_valid, 32768⟩)
    (halign : (retAddr &&& ~~~(1 : Word)) = retAddr) :
    cpsTripleWithin (2 + ((cacheResetFn orig).body.steps + 1))
      (GuestAddrs.mpt_resolve_cache_reset : Word) retAddr cacheResetCr
      (((.x5 : Reg) ↦ᵣ old5) ** ((.x1 : Reg) ↦ᵣ retAddr) **
        regOwns cacheScratch ** bytesRegion GuestAddrs.mset_res_cache_valid orig)
      (((.x1 : Reg) ↦ᵣ retAddr) ** regOwn .x5 ** regOwns cacheScratch **
        bytesRegion GuestAddrs.mset_res_cache_valid
          (List.replicate 32768 (0 : BitVec 8))) := by
  have hla := la_materialize_within .x5 old5
    (GuestAddrs.mpt_resolve_cache_reset : Word)
    (GuestAddrs.mset_res_cache_valid : Word)
    (cr := cacheResetCr) (by decide) (by decide)
    (by unfold cacheResetCr; code_mem) (by unfold cacheResetCr; code_mem)
  rw [show (GuestAddrs.mpt_resolve_cache_reset : Word) + 8 =
      (GuestAddrs.mpt_resolve_cache_reset + 8 : Word) from by decide] at hla
  have hlaF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ retAddr) ** regOwns cacheScratch **
      bytesRegion GuestAddrs.mset_res_cache_valid orig) (by pcf) hla
  have htail := cacheResetTail_spec retAddr orig hlen hwf halign
  have hall := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hlaF htail
  exact hall

#print axioms cacheResetFn_spec
#print axioms mptResolveCacheReset_spec

end MptResolveCacheResetSAsm
end EvmAsm.Codegen
