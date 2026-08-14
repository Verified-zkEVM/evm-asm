import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Blake2f
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.FnFlat

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace Blake2fStoreLe64SAsm

def storeWin (value : Word) (orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  (dwordBytes value).take i ++ orig.drop i

theorem storeWin_zero (value : Word) (orig : List (BitVec 8)) :
    storeWin value orig 0 = orig := by
  simp [storeWin]

theorem storeWin_8_eq (value : Word) (orig : List (BitVec 8)) (h_orig : orig.length = 8) :
    storeWin value orig 8 = dwordBytes value := by
  rw [storeWin, List.take_of_length_le (by rw [length_dwordBytes]),
    List.drop_eq_nil_of_le (by omega), List.append_nil]

theorem length_storeWin (value : Word) (orig : List (BitVec 8)) (i : Nat)
    (h_orig : orig.length = 8) (h_i : i ≤ 8) :
    (storeWin value orig i).length = 8 := by
  simp only [storeWin, List.length_append, List.length_take, List.length_drop,
    length_dwordBytes, h_orig]
  omega

private theorem byteOfShift_eq_dwordByte (value : Word) (i : Nat) (h_i : i < 8) :
    ((value >>> (8 * i)) &&& (255 : Word)).truncate 8 =
      (dwordBytes value).getD i 0 := by
  have h_mask (x : Word) : (x &&& (255 : Word)).truncate 8 = x.truncate 8 := by
    rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_and]
    change BitVec.setWidth 8 x &&& BitVec.setWidth 8 (255 : Word) = BitVec.setWidth 8 x
    rw [show BitVec.setWidth 8 (255 : Word) = BitVec.allOnes 8 by decide]
    rw [BitVec.and_allOnes]
  rw [h_mask]
  interval_cases i <;> simp [dwordBytes, extractByte]

private theorem shiftRight8_step (value : Word) (i : Nat) :
    (value >>> (8 * (i + 1))) >>> 8 = value >>> (8 * (i + 1 + 1)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j
  simp [BitVec.getLsbD_ushiftRight]
  intro _h_j
  congr 1
  omega

theorem storeWin_step (value : Word) (orig : List (BitVec 8)) (i : Nat)
    (h_orig : orig.length = 8) (h_i : i < 8) :
    setBytes (storeWin value orig i) i
      [((value >>> (8 * i)) &&& (255 : Word)).truncate 8] =
    storeWin value orig (i + 1) := by
  have h_prefix_len : ((dwordBytes value).take i).length = i := by
    simp only [List.length_take, length_dwordBytes]
    omega
  have h_payload :
      [((value >>> (8 * i)) &&& (255 : Word)).truncate 8] =
        [(dwordBytes value).getD i 0] := by
    rw [byteOfShift_eq_dwordByte value i h_i]
  rw [h_payload]
  rw [storeWin]
  rw [setBytes_append_right _ _ _ _ (by rw [h_prefix_len])]
  rw [h_prefix_len, Nat.sub_self]
  have h_tail_len : (orig.drop i).length = 8 - i := by
    simp [h_orig]
  have h_fit : 0 + [(dwordBytes value).getD i 0].length ≤ (orig.drop i).length := by
    simp [h_tail_len]
    omega
  have h_slot := setBytes_slot (orig.drop i) [(dwordBytes value).getD i 0] 0 h_fit
  have h_slot_one : List.take 1 (setBytes (orig.drop i) 0 [(dwordBytes value).getD i 0]) =
      [(dwordBytes value).getD i 0] := by
    simpa using h_slot
  have h_drop : (setBytes (orig.drop i) 0 [(dwordBytes value).getD i 0]).drop 1 =
      (orig.drop i).drop 1 := by
    simpa using setBytes_drop_of_le [(dwordBytes value).getD i 0] (orig.drop i) 0 1 (by simp)
  have h_set : setBytes (orig.drop i) 0 [(dwordBytes value).getD i 0] =
      [(dwordBytes value).getD i 0] ++ (orig.drop i).drop 1 := by
    conv_lhs =>
      rw [← List.take_append_drop 1
        (setBytes (orig.drop i) 0 [(dwordBytes value).getD i 0])]
    rw [h_slot_one, h_drop]
  rw [h_set]
  rw [show (orig.drop i).drop 1 = orig.drop (i + 1) by
    rw [List.drop_drop]]
  simp only [storeWin]
  rw [← List.append_assoc]
  congr 1
  interval_cases i <;> simp [dwordBytes]

def storeStepBlock : List Instr :=
  [.ANDI .x11 .x5 (255 : BitVec 12),
   .SB .x6 .x11 (0 : BitVec 12),
   .SRLI .x5 .x5 (8 : BitVec 6),
   .ADDI .x6 .x6 (1 : BitVec 12),
   .ADDI .x7 .x7 (-1 : BitVec 12)]

def storeStepRf (rf : RegFile) : RegFile :=
  let r1 := rf.set .x11 (rf.get .x5 &&& signExtend12 (255 : BitVec 12))
  let r2 := r1.set .x5 (r1.get .x5 >>> (8 : BitVec 6).toNat)
  let r3 := r2.set .x6 (r2.get .x6 + signExtend12 (1 : BitVec 12))
  r3.set .x7 (r3.get .x7 + signExtend12 (-1 : BitVec 12))

theorem storeStepRf_get_x5 (rf : RegFile) :
    (storeStepRf rf).get .x5 = rf.get .x5 >>> 8 := by
  unfold storeStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]
  rw [show (8 : BitVec 6).toNat = 8 from by decide]

theorem storeStepRf_get_x6 (rf : RegFile) :
    (storeStepRf rf).get .x6 = rf.get .x6 + signExtend12 (1 : BitVec 12) := by
  unfold storeStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem storeStepRf_get_x7 (rf : RegFile) :
    (storeStepRf rf).get .x7 = rf.get .x7 + signExtend12 (-1 : BitVec 12) := by
  unfold storeStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem store_engine (reg : Region) (dst value : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Nat) (h_i : i < 8)
    (h_x5 : rf.get .x5 = value >>> (8 * i))
    (h_x6 : rf.get .x6 = dst + BitVec.ofNat 64 i) :
    execBlock reg dst rf ws storeStepBlock =
      (storeStepRf rf,
       setBytes ws i [((value >>> (8 * i)) &&& (255 : Word)).truncate 8]) := by
  have h_se0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have h_se255 : signExtend12 (255 : BitVec 12) = (255 : Word) := by decide
  have h_addr : (((rf.set .x11 (rf.get .x5 &&& signExtend12 (255 : BitVec 12))).get .x6
      + signExtend12 (0 : BitVec 12)) - dst).toNat = i := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x11), h_x6, h_se0]
    bv_omega
  rw [show storeStepBlock = [.ANDI .x11 .x5 (255 : BitVec 12), .SB .x6 .x11 0,
      .SRLI .x5 .x5 8, .ADDI .x6 .x6 1, .ADDI .x7 .x7 (-1 : BitVec 12)] from rfl]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  rw [execInstrRF_sb_byte _ _ _ _ _ _ _ i h_addr]
  rw [h_se255, h_x5]
  dsimp only
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  unfold storeStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true, h_se255]
  rw [h_x5]

def storeInv (dst value : Word) (orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws A =>
    rf.get .x5 = value >>> (8 * (i + 1)) ∧
    rf.get .x6 = dst + BitVec.ofNat 64 (i + 1) ∧
    rf.get .x7 = BitVec.ofNat 64 (8 - (i + 1)) ∧
    i < 8 ∧ orig.length = 8 ∧ ws = storeWin value orig (i + 1) ∧ A = empAssertion

def blk2StLe64Body (dst value : Word) (orig : List (BitVec 8)) : Stmt :=
  .block "init" [.MV .x5 .x11, .MV .x6 .x10, .LI .x7 (8 : Word)] ;;;
  .doWhile "loop" (.bne .x7 .x0) 8 (storeInv dst value orig)
    (.block "store" storeStepBlock)

def blk2StLe64Fn (dst value : Word) (orig : List (BitVec 8)) : Fn where
  name := "blk2StLe64"
  rw := ⟨dst, 8⟩
  pre := fun rf ws A => rf.get .x10 = dst ∧ rf.get .x11 = value ∧ ws = orig ∧ orig.length = 8 ∧ A = empAssertion
  post := fun _ ws A => ws = dwordBytes value ∧ A = empAssertion
  body := blk2StLe64Body dst value orig

def blk2StLe64_verified : Program :=
  (blk2StLe64Body 0 0 []).flatten 0

#guard (blk2StLe64_verified : List Instr).length = 9
#guard (blk2StLe64Body 0 0 []).flatten 0 =
  (blk2StLe64Body 0 0 []).flatten 0x80000000
#guard (blk2StLe64Body 0 0 []).flatten 0 ++ [Instr.JALR .x0 .x1 0] = blk2StLe64_prog

theorem blk2StLe64Fn_spec (dst value : Word) (orig : List (BitVec 8))
    (h_wf : RwRegion.wf ⟨dst, 8⟩) (base : Word) :
    (blk2StLe64Fn dst value orig).Spec base := by
  have h_base : (blk2StLe64Fn dst value orig).rw.base = dst := rfl
  vcgen
  case region => exact ⟨Region.empty_wf, h_wf⟩
  case blk2StLe64.loop.inv_init =>
    rintro rf' ws' A' h
    rcases h with ⟨rf0, ws0, -, hreach, rfl, rfl⟩
    rcases hreach with ⟨rfInit, wsInit, -, hpre, rfl, rfl⟩
    rcases hpre with ⟨h_x10, h_x11, rfl, h_len, hA⟩
    simp only [h_base]
    have h_x5_init : (execBlock (blk2StLe64Fn dst value ws0).region dst rfInit ws0
        [.MV .x5 .x11, .MV .x6 .x10, .LI .x7 8]).1.get .x5 = value := by
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, h_x11]
    have h_x6_init : (execBlock (blk2StLe64Fn dst value ws0).region dst rfInit ws0
        [.MV .x5 .x11, .MV .x6 .x10, .LI .x7 8]).1.get .x6 = dst := by
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, h_x10]
    rw [store_engine _ dst value _ ws0 0 (by omega) (by simpa using h_x5_init)
      (by simpa using h_x6_init)]
    refine ⟨?_, ?_, ?_, by omega, h_len, ?_, hA⟩
    · rw [storeStepRf_get_x5, h_x5_init]
    · rw [storeStepRf_get_x6, h_x6_init, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      bv_omega
    · rw [storeStepRf_get_x7]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
      decide
    · change setBytes ws0 0 [((value >>> (8 * 0)) &&& (255 : Word)).truncate 8] =
        storeWin value ws0 (0 + 1)
      simpa [storeWin_zero] using storeWin_step value ws0 0 h_len (by omega)
  case blk2StLe64.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, ⟨⟨h_x5, h_x6, h_x7, h_lt, h_len, h_ws, hA⟩, h_cond⟩, rfl, rfl⟩
    simp only [h_base]
    have h_cond_nonzero : rf₀.get .x7 ≠ 0 := by
      simpa [Cond.holds, h_x7, RegFile.get_x0] using h_cond
    have h_i1 : i + 1 < 8 := by
      interval_cases i <;> first | contradiction | omega
    rw [store_engine _ dst value rf₀ ws₀ (i + 1) h_i1 h_x5 h_x6]
    refine ⟨?_, ?_, ?_, by omega, h_len, ?_, hA⟩
    · rw [storeStepRf_get_x5, h_x5]
      rw [shiftRight8_step]
    · rw [storeStepRf_get_x6, h_x6, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from by decide]
      omega
    · rw [storeStepRf_get_x7, h_x7, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      interval_cases i <;> first | contradiction | decide
    · rw [h_ws, storeWin_step value orig (i + 1) h_len h_i1]
  case blk2StLe64.loop.exhausted =>
    rintro rf ws A ⟨-, -, h_x7, -, -, -, -⟩
    simp only [Cond.holds, h_x7, not_not, RegFile.get_x0]
    decide
  case blk2StLe64.loop.body.store.mem =>
    rintro rf ws A h_len (hpre | hloop)
    · rcases hpre with ⟨rfInit, wsInit, -, ⟨h_x10, h_x11, rfl, h_orig_len, hA⟩, rfl, rfl⟩
      have h_len8 : ws.length = 8 := by simpa [blk2StLe64Fn] using h_len
      have h_addr0 : (dst + signExtend12 (0 : BitVec 12) - dst).toNat = 0 := by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega
      simp only [storeStepBlock, blockVCs, execInstrRF, aluSem, loadSem, storeSem,
        inRw, h_base, execBlock_cons, execBlock_nil, RegFile.get_set_ne, ne_eq,
        reduceCtorEq, not_false_eq_true, h_x10, h_x11, h_len8, and_true]
      change True ∧ (dst + signExtend12 (0 : BitVec 12) - dst).toNat + 1 ≤ 8 ∧
        1 ∣ (dst + signExtend12 (0 : BitVec 12) - dst).toNat
      rw [h_addr0]
      exact ⟨trivial, by omega, Nat.dvd_zero 1⟩
    · rcases hloop with ⟨i, hi, ⟨h_x5, h_x6, h_x7, h_lt, h_orig_len, h_ws, hA⟩, h_cond⟩
      have h_cond_nonzero : rf.get .x7 ≠ 0 := by
        simpa [Cond.holds, h_x7, RegFile.get_x0] using h_cond
      have h_i1 : i + 1 < 8 := by
        interval_cases i <;> first | contradiction | omega
      have h_addr : (rf.get .x6 + signExtend12 (0 : BitVec 12) - dst).toNat = i + 1 := by
        rw [h_x6, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega
      have h_len8 : ws.length = 8 := by simpa [blk2StLe64Fn] using h_len
      simp only [storeStepBlock, blockVCs, loadSem, storeSem, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, inRw, h_base, h_len8, and_true]
      change True ∧ (rf.get .x6 + signExtend12 (0 : BitVec 12) - dst).toNat + 1 ≤ 8 ∧
        1 ∣ (rf.get .x6 + signExtend12 (0 : BitVec 12) - dst).toNat
      rw [h_addr]
      exact ⟨trivial, by omega, Nat.one_dvd (i + 1)⟩
  case blk2StLe64.post =>
    rintro rf ws A ⟨⟨i, h_le, h_x5, h_x6, h_x7, h_lt, h_len, h_ws, hA⟩, h_not_cond⟩
    have h_i : i = 7 := by
      simp only [Cond.holds, h_x7, RegFile.get_x0, not_not] at h_not_cond
      interval_cases i <;> try contradiction
      rfl
    subst h_i
    rw [h_ws, storeWin_8_eq value orig h_len]
    exact ⟨rfl, hA⟩

/-! ## Flat linked-entry contract -/

def blk2StLe64Cr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.blk2_st_le64 : Word) blk2StLe64_prog

def blk2StLe64Scratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_store (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) **
          regAtomsOf vf blk2StLe64Scratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [blk2StLe64Scratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem store_args_notin_scratch :
    ∀ r ∈ blk2StLe64Scratch, r ≠ (.x10 : Reg) ∧ r ≠ (.x11 : Reg) := by
  decide

theorem blk2StLe64Flat_spec (ret dst value : Word) (orig : List (BitVec 8))
    (hwf : RwRegion.wf ⟨dst, 8⟩)
    (hlen : orig.length = 8)
    (hsz : 4 * ((blk2StLe64Fn dst value orig).body.size + 1) ≤ 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      ((blk2StLe64Fn dst value orig).body.steps + 1)
      (GuestAddrs.blk2_st_le64 : Word) ret blk2StLe64Cr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ dst) ** (.x11 ↦ᵣ value) **
        regOwns blk2StLe64Scratch ** bytesRegion dst orig)
      (((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs **
        bytesRegion dst (dwordBytes value)) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns blk2StLe64Scratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ dst) ** (.x11 ↦ᵣ value) **
        bytesRegion dst orig)
      (fun vf => ?_))
  have hpre : (blk2StLe64Fn dst value orig).pre
      (fun r => if r = .x10 then dst else if r = .x11 then value else vf r)
      orig empAssertion := by
    refine ⟨?_, ?_, rfl, hlen, rfl⟩
    · show RegFile.get _ .x10 = dst
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = value
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
  have had := Fn.retSpecFlatAmbient
    (blk2StLe64Fn dst value orig)
    (GuestAddrs.blk2_st_le64 : Word)
    (blk2StLe64Fn_spec dst value orig hwf
      (GuestAddrs.blk2_st_le64 : Word))
    (by simpa [blk2StLe64Fn] using hsz) ret halign
    (fun r => if r = .x10 then dst else if r = .x11 then value else vf r)
    orig empAssertion pcFree_emp (by simpa [blk2StLe64Fn] using hlen) hpre
    (fun _ _ _ hpost => hpost.2)
    (Q := regOwns exposedRegs ** bytesRegion dst (dwordBytes value))
    (fun rf' ws' hlen' hpost' hp hh => by
      obtain ⟨hws', -⟩ := hpost'
      rw [hws', show (blk2StLe64Fn dst value orig).rw.base = dst from rfl] at hh
      simp only [sepConj_emp_right'] at hh
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
      exact sepConj_mono_left
        (regAtomsOf_to_regOwns (fun r => rf' r) exposedRegs) hp hh)
  rw [show (blk2StLe64Fn dst value orig).programRet
      (GuestAddrs.blk2_st_le64 : Word) = blk2StLe64_prog from rfl] at had
  have hadC := had
  rw [show (blk2StLe64Fn dst value orig).region = Region.empty from rfl,
    show Region.empty.bytes = ([] : List (BitVec 8)) from rfl,
    bytesRegion_nil, sepConj_emp_right'] at hadC
  simp only [sepConj_emp_right'] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_store,
    show (if (Reg.x10 : Reg) = .x10 then dst else
        if (Reg.x10 : Reg) = .x11 then value else vf .x10) = dst from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then dst else
        if (Reg.x11 : Reg) = .x11 then value else vf .x11) = value from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then dst else if r = .x11 then value else vf r)
      vf blk2StLe64Scratch
      (fun r hr => by
        show (if r = .x10 then dst else if r = .x11 then value else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) =>
              (store_args_notin_scratch r hr).1 hc),
            if_neg (fun (hc : r = .x11) =>
              (store_args_notin_scratch r hr).2 hc)])] at hadC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hadC

end Blake2fStoreLe64SAsm

end EvmAsm.Codegen
