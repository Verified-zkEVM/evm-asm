import EvmAsm.Codegen.Programs.RlpFieldToU256BeSetupSAsm
import EvmAsm.Codegen.Programs.P256CopyNSAsm

namespace EvmAsm.Codegen.RlpFieldToU256BeSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

def copyByte (bytes : List (BitVec 8)) (offset i : Nat) : BitVec 8 :=
  bytes.getD (offset + i) 0

def copyWin (bytes : List (BitVec 8)) (offset len i : Nat) : List (BitVec 8) :=
  List.replicate (32 - len) 0 ++
    (List.range i).map (copyByte bytes offset) ++
    List.replicate (len - i) 0

theorem copyWin_zero (bytes : List (BitVec 8)) (offset len : Nat)
    (hfit : len ≤ 32) : copyWin bytes offset len 0 = List.replicate 32 0 := by
  rw [show 32 = (32 - len) + len by omega, List.replicate_add]
  simp [copyWin]

theorem length_copyWin (bytes : List (BitVec 8)) (offset len i : Nat)
    (hfit : len ≤ 32) (hi : i ≤ len) :
    (copyWin bytes offset len i).length = 32 := by
  simp only [copyWin, List.length_append, List.length_replicate,
    List.length_map, List.length_range]
  omega

theorem copyWin_step (bytes : List (BitVec 8)) (offset len i : Nat)
    (hfit : len ≤ 32) (hi : i < len) :
    setBytes (copyWin bytes offset len i) (32 - len + i)
      [copyByte bytes offset i] = copyWin bytes offset len (i + 1) := by
  rw [setBytes_singleton]
  simp only [copyWin, List.range_succ, List.map_append, List.map_cons,
    List.map_nil, List.singleton_append, List.append_assoc]
  rw [List.set_append_right (h := by simp)]
  congr 1
  simp only [List.length_replicate]
  rw [show 32 - len + i - (32 - len) = i by omega]
  rw [List.set_append_right (h := by simp)]
  simp only [List.length_map, List.length_range, Nat.sub_self]
  congr 1
  rw [show len - i = 1 + (len - (i + 1)) by omega,
    List.replicate_add, List.replicate_one]
  simp

theorem copyWin_done (bytes : List (BitVec 8)) (offset len : Nat)
    (hfit : len ≤ 32) (hbound : offset + len ≤ bytes.length) :
    copyWin bytes offset len len =
      List.replicate (32 - len) 0 ++ (bytes.drop offset).take len := by
  simp only [copyWin, Nat.sub_self, List.replicate_zero, List.append_nil]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take,
      List.length_drop]
    omega
  · intro i hi1 hi2
    simp only [List.length_map, List.length_range] at hi1
    simp only [List.getElem_map, List.getElem_range, copyByte,
      List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show offset + i < bytes.length by omega),
      Option.getD_some]

def copyStepBlock : List Instr :=
  [.LBU .x30 .x28 0, .SB .x29 .x30 0,
   .ADDI .x28 .x28 1, .ADDI .x29 .x29 1,
   .ADDI .x6 .x6 (-1 : BitVec 12)]

def copyInv (listBase outputPtr : Word) (bytes : List (BitVec 8))
    (offset len : Nat) : Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws _ =>
    rf.get .x28 = listBase + BitVec.ofNat 64 (offset + i) ∧
    rf.get .x29 = outputPtr + BitVec.ofNat 64 (32 - len + i) ∧
    rf.get .x6 = BitVec.ofNat 64 (len - i) ∧
    i ≤ len ∧ len ≤ 32 ∧ offset + len ≤ bytes.length ∧
    listBase.toNat + bytes.length < 2 ^ 64 ∧
    outputPtr.toNat + 32 < 2 ^ 64 ∧
    (listBase.toNat + bytes.length ≤ outputPtr.toNat ∨
      outputPtr.toNat + 32 ≤ listBase.toNat) ∧
    ws = copyWin bytes offset len i

def copyBody (listBase outputPtr : Word) (bytes : List (BitVec 8))
    (offset len : Nat) : Stmt :=
  .«while» "copy" (.bne .x6 .x0) len
    (copyInv listBase outputPtr bytes offset len)
    (.block "byte" copyStepBlock)

def copyFn (listBase outputPtr : Word) (bytes : List (BitVec 8))
    (offset len : Nat) : Fn where
  name := "rlpFieldToU256BeCopy"
  region := ⟨listBase, bytes⟩
  rw := ⟨outputPtr, 32⟩
  pre := fun rf ws _ =>
    rf.get .x28 = listBase + BitVec.ofNat 64 offset ∧
    rf.get .x29 = outputPtr + BitVec.ofNat 64 (32 - len) ∧
    rf.get .x6 = BitVec.ofNat 64 len ∧
    ws = List.replicate 32 0 ∧ len ≤ 32 ∧
    offset + len ≤ bytes.length ∧
    listBase.toNat + bytes.length < 2 ^ 64 ∧
    outputPtr.toNat + 32 < 2 ^ 64 ∧
    (listBase.toNat + bytes.length ≤ outputPtr.toNat ∨
      outputPtr.toNat + 32 ≤ listBase.toNat)
  post := fun _ ws _ =>
    ws = List.replicate (32 - len) 0 ++ (bytes.drop offset).take len
  body := copyBody listBase outputPtr bytes offset len

theorem copyBody_byte_tie :
    (copyBody 0 0 [] 0 0).flatten 0 = (rlpFieldToU256Be_prog.drop 27).take 7 := by
  rfl

#guard ((copyBody 0 0 [] 0 0).flatten 0 : List Instr).length = 7

def copyStepRf (rf : RegFile) (b : BitVec 8) : RegFile :=
  let r1 := rf.set .x30 (b.zeroExtend 64)
  let r2 := r1.set .x28 (r1.get .x28 + signExtend12 (1 : BitVec 12))
  let r3 := r2.set .x29 (r2.get .x29 + signExtend12 (1 : BitVec 12))
  r3.set .x6 (r3.get .x6 + signExtend12 (-1 : BitVec 12))

theorem copyStepRf_get_x28 (rf : RegFile) (b : BitVec 8) :
    (copyStepRf rf b).get .x28 = rf.get .x28 + signExtend12 (1 : BitVec 12) := by
  unfold copyStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x6),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x29),
    RegFile.get_set_self _ _ _ (by decide : Reg.x28 ≠ .x0),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x30)]

theorem copyStepRf_get_x29 (rf : RegFile) (b : BitVec 8) :
    (copyStepRf rf b).get .x29 = rf.get .x29 + signExtend12 (1 : BitVec 12) := by
  unfold copyStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x6),
    RegFile.get_set_self _ _ _ (by decide : Reg.x29 ≠ .x0),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30)]

theorem copyStepRf_get_x6 (rf : RegFile) (b : BitVec 8) :
    (copyStepRf rf b).get .x6 = rf.get .x6 + signExtend12 (-1 : BitVec 12) := by
  unfold copyStepRf
  rw [RegFile.get_set_self _ _ _ (by decide : Reg.x6 ≠ .x0),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x30)]

theorem copy_step_engine (listBase outputPtr : Word)
    (bytes : List (BitVec 8)) (offset len i : Nat)
    (rf : RegFile) (ws : List (BitVec 8))
    (hx28 : rf.get .x28 = listBase + BitVec.ofNat 64 (offset + i))
    (hx29 : rf.get .x29 = outputPtr + BitVec.ofNat 64 (32 - len + i))
    (hi : i < len) (hbound : offset + len ≤ bytes.length)
    (hsrc : listBase.toNat + bytes.length < 2 ^ 64)
    (hdst : outputPtr.toNat + 32 < 2 ^ 64)
    (hdisj : listBase.toNat + bytes.length ≤ outputPtr.toNat ∨
      outputPtr.toNat + 32 ≤ listBase.toNat)
    (hws : ws.length = 32) :
    execBlock ⟨listBase, bytes⟩ outputPtr rf ws copyStepBlock =
      (copyStepRf rf (copyByte bytes offset i),
        setBytes ws (32 - len + i) [copyByte bytes offset i]) := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hidx : (BitVec.ofNat 64 (offset + i)).toNat = offset + i := by
    rw [BitVec.toNat_ofNat]; omega
  have hload : rf.get .x28 + signExtend12 (0 : BitVec 12) =
      listBase + BitVec.ofNat 64 (offset + i) := by rw [hx28, hse0]; simp
  have hnr : ¬ inRw outputPtr ws
      (rf.get .x28 + signExtend12 (0 : BitVec 12)) 1 := by
    rw [hload]
    unfold inRw
    rw [hws]
    have hd : (listBase + BitVec.ofNat 64 (offset + i) - outputPtr).toNat =
        (listBase.toNat + (offset + i) + (2 ^ 64 - outputPtr.toNat)) % 2 ^ 64 := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hidx]; congr 1; omega
    rw [hd]
    rcases hdisj with h | h <;> omega
  have hval : (Region.byteAt ⟨listBase, bytes⟩
      (rf.get .x28 + signExtend12 (0 : BitVec 12))) = copyByte bytes offset i := by
    rw [hload]
    show bytes.getD ((listBase + BitVec.ofNat 64 (offset + i) - listBase).toNat) 0 =
      copyByte bytes offset i
    rw [show (listBase + BitVec.ofNat 64 (offset + i) - listBase).toNat =
        offset + i by rw [BitVec.toNat_sub, BitVec.toNat_add, hidx]; omega]
    rfl
  have hstore : (rf.get .x29 + signExtend12 (0 : BitVec 12) - outputPtr).toNat =
      32 - len + i := by rw [hx29, hse0]; bv_omega
  rw [show copyStepBlock =
      [.LBU .x30 .x28 0, .SB .x29 .x30 0, .ADDI .x28 .x28 1,
       .ADDI .x29 .x29 1, .ADDI .x6 .x6 (-1 : BitVec 12)] from rfl]
  rw [execBlock_cons, EvmAsm.Codegen.P256CopyNSAsm.execInstrRF_lbu_ro
    _ _ _ _ _ _ _ hnr]
  dsimp only
  rw [hval, execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ (32 - len + i)
    (by rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30)]; exact hstore)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  unfold copyStepRf
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x30)]
  rw [setBytes_singleton]

theorem copyFn_spec (listBase outputPtr : Word) (bytes : List (BitVec 8))
    (offset len : Nat) (hwf : (Region.mk listBase bytes).wf)
    (hrw : RwRegion.wf ⟨outputPtr, 32⟩) (base : Word) :
    (copyFn listBase outputPtr bytes offset len).Spec base := by
  have hse1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hsem1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  vcgen
  case region => exact ⟨hwf, hrw⟩
  case rlpFieldToU256BeCopy.copy.inv_init =>
    rintro rf ws A ⟨hx28, hx29, hx6, rfl, hfit, hbound, hsrc, hdst, hdisj⟩
    refine ⟨?_, ?_, ?_, by omega, hfit, hbound, hsrc, hdst, hdisj, ?_⟩
    · simpa using hx28
    · simpa using hx29
    · simpa using hx6
    · exact (copyWin_zero bytes offset len hfit).symm
  case rlpFieldToU256BeCopy.copy.inv_step =>
    rintro i hi rf' ws' A' ⟨rf0, ws0, -,
      ⟨⟨hx28, hx29, hx6, hile, hfit, hbound, hsrc, hdst, hdisj, hwin⟩, -⟩,
      rfl, rfl⟩
    have hwslen : ws0.length = 32 := by
      rw [hwin]
      exact length_copyWin bytes offset len i hfit (by omega)
    simp only [show (copyFn listBase outputPtr bytes offset len).rw.base = outputPtr from rfl,
      show (copyFn listBase outputPtr bytes offset len).region = ⟨listBase, bytes⟩ from rfl]
    rw [copy_step_engine listBase outputPtr bytes offset len i rf0 ws0 hx28 hx29 hi
      hbound hsrc hdst hdisj hwslen]
    refine ⟨?_, ?_, ?_, by omega, hfit, hbound, hsrc, hdst, hdisj, ?_⟩
    · rw [copyStepRf_get_x28, hx28, hse1]
      have h1 : (BitVec.ofNat 64 (offset + i)).toNat = offset + i := by
        rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (offset + (i + 1))).toNat = offset + (i + 1) := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [copyStepRf_get_x29, hx29, hse1]
      have h1 : (BitVec.ofNat 64 (32 - len + i)).toNat = 32 - len + i := by
        rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (32 - len + (i + 1))).toNat = 32 - len + (i + 1) := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [copyStepRf_get_x6, hx6, hsem1]
      have h1 : (BitVec.ofNat 64 (len - i)).toNat = len - i := by
        rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (len - (i + 1))).toNat = len - (i + 1) := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [hwin, copyWin_step bytes offset len i hfit hi]
  case rlpFieldToU256BeCopy.copy.exhausted =>
    rintro rf ws A ⟨-, -, hx6, hile, -, -, -, -, -, -⟩
    simp only [Cond.holds, not_not]
    rw [hx6]
    rw [show BitVec.ofNat 64 (len - len) = (0 : Word) by
      rw [show len - len = 0 by omega]; rfl]
    rfl
  case rlpFieldToU256BeCopy.copy.body.byte.mem =>
    rintro rf ws A hwslen ⟨i, hi,
      ⟨hx28, hx29, hx6, hile, hfit, hbound, hsrc, hdst, hdisj, hwin⟩, -⟩
    change ws.length = 32 at hwslen
    have hoff : offset + i < bytes.length := by omega
    have hidx : (BitVec.ofNat 64 (offset + i)).toNat = offset + i := by
      rw [BitVec.toNat_ofNat]; omega
    have hload : rf.get .x28 + signExtend12 (0 : BitVec 12) =
        listBase + BitVec.ofNat 64 (offset + i) := by rw [hx28, hse0]; simp
    have hnr : ¬ inRw outputPtr ws
        (rf.get .x28 + signExtend12 (0 : BitVec 12)) 1 := by
      rw [hload]
      unfold inRw
      rw [hwslen]
      have hd : (listBase + BitVec.ofNat 64 (offset + i) - outputPtr).toNat =
          (listBase.toNat + (offset + i) + (2 ^ 64 - outputPtr.toNat)) % 2 ^ 64 := by
        rw [BitVec.toNat_sub, BitVec.toNat_add, hidx]; congr 1; omega
      rw [hd]
      rcases hdisj with h | h <;> omega
    have hloadok : (listBase + BitVec.ofNat 64 (offset + i) - listBase).toNat =
        offset + i := by rw [BitVec.toNat_sub, BitVec.toNat_add, hidx]; omega
    have hstore : (rf.get .x29 + signExtend12 (0 : BitVec 12) - outputPtr).toNat =
        32 - len + i := by rw [hx29, hse0]; bv_omega
    rw [show copyStepBlock =
        [.LBU .x30 .x28 0, .SB .x29 .x30 0, .ADDI .x28 .x28 1,
         .ADDI .x29 .x29 1, .ADDI .x6 .x6 (-1 : BitVec 12)] from rfl,
      show (copyFn listBase outputPtr bytes offset len).region = ⟨listBase, bytes⟩ from rfl,
      show (copyFn listBase outputPtr bytes offset len).rw.base = outputPtr from rfl]
    refine ⟨?_, ?_⟩
    · simp only [loadSem]
      rw [if_neg hnr]
      unfold Region.loadOk
      rw [hload, hloadok]
      refine ⟨Nat.one_dvd _, ?_⟩
      change offset + i + 1 ≤ bytes.length
      omega
    · rw [EvmAsm.Codegen.P256CopyNSAsm.execInstrRF_lbu_ro _ _ _ _ _ _ _ hnr]
      refine ⟨?_, trivial, trivial, trivial, trivial⟩
      dsimp only [storeSem]
      refine ⟨?_, ?_⟩
      · unfold inRw
        rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30), hwslen, hstore]
        omega
      · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30), hstore]
        exact Nat.one_dvd _
  case rlpFieldToU256BeCopy.post =>
    rintro rf ws A ⟨⟨i, hile, hx28, hx29, hx6, hle, hfit, hbound,
      hsrc, hdst, hdisj, hwin⟩, hncond⟩
    have hi_len : i = len := by
      simp only [Cond.holds, not_not] at hncond
      rw [hx6] at hncond
      have hz : rf.get .x0 = 0 := rfl
      rw [hz] at hncond
      have h : (BitVec.ofNat 64 (len - i)).toNat = (0 : Word).toNat := by rw [hncond]
      rw [show (0 : Word).toNat = 0 from rfl, BitVec.toNat_ofNat] at h
      omega
    subst i
    change ws = List.replicate (32 - len) 0 ++ (bytes.drop offset).take len
    rw [hwin, copyWin_done bytes offset len hfit hbound]

#print axioms copyFn_spec

end EvmAsm.Codegen.RlpFieldToU256BeSAsm
