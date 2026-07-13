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

/-! ## Partial-register bridge for the inline caller composition -/

/-- One emitted copy body (instructions 28--32), stated at separation-logic
    register granularity so the K35 caller need not regain unrelated
    caller-clobbered registers after K20. -/
theorem copyBody_spec_within
    (listBase outputPtr old30 count : Word) (bytes out : List (BitVec 8))
    (offset len i : Nat)
    (hsalign : listBase.toNat % 8 = 0)
    (hdalign : outputPtr.toNat % 8 = 0)
    (hi : i < len) (hfit : len ≤ 32)
    (hbound : offset + len ≤ bytes.length)
    (hsrc : listBase.toNat + bytes.length < 2 ^ 64)
    (hdst : outputPtr.toNat + 32 < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (houtvalid : ∀ k, k < 32 →
      isValidByteAccess (outputPtr + BitVec.ofNat 64 k) = true)
    (hout : out.length = 32) :
    cpsTripleWithin 5 (B + 112) (B + 132) code
      ((.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (offset + i))) **
       (.x29 ↦ᵣ (outputPtr + BitVec.ofNat 64 (32 - len + i))) **
       (.x30 ↦ᵣ old30) ** (.x6 ↦ᵣ count) **
       bytesRegion listBase bytes ** bytesRegion outputPtr out)
      ((.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (offset + i + 1))) **
       (.x29 ↦ᵣ (outputPtr + BitVec.ofNat 64 (32 - len + i + 1))) **
       (.x30 ↦ᵣ (copyByte bytes offset i).zeroExtend 64) **
       (.x6 ↦ᵣ (count + signExtend12 (-1 : BitVec 12))) **
       bytesRegion listBase bytes **
       bytesRegion outputPtr (out.set (32 - len + i) (copyByte bytes offset i))) := by
  have hsi : offset + i < bytes.length := by omega
  have hdi : 32 - len + i < out.length := by rw [hout]; omega
  have hsov : listBase.toNat + (offset + i) < 2 ^ 64 := by omega
  have hdov : outputPtr.toNat + (32 - len + i) < 2 ^ 64 := by omega
  have hl := bytesRegion_lbu_within .x30 .x28 listBase old30 (B + 112)
    bytes (offset + i) (by decide) hsalign hsi hsov (hvalid _ hsi)
  have hbyte : bytes[offset + i]'hsi = copyByte bytes offset i := by
    simp [copyByte, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hsi]
  rw [hbyte] at hl
  have hl' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 112) rlpFieldToU256Be_prog 28
      (.LBU .x30 .x28 (0 : BitVec 12)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hl
  have hs := bytesRegion_sb_within .x29 .x30 outputPtr
    ((copyByte bytes offset i).zeroExtend 64 : Word) (B + 116) out
    (32 - len + i) hdalign hdi hdov (houtvalid _ (by omega))
  rw [show ((copyByte bytes offset i).zeroExtend 64).truncate 8 =
      copyByte bytes offset i by simp] at hs
  have hs' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 116) rlpFieldToU256Be_prog 29
      (.SB .x29 .x30 (0 : BitVec 12)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hs
  have h28 := addi_spec_gen_same_within .x28
    (listBase + BitVec.ofNat 64 (offset + i)) (1 : BitVec 12) (B + 120)
    (by decide)
  rw [show listBase + BitVec.ofNat 64 (offset + i) +
      signExtend12 (1 : BitVec 12) =
      listBase + BitVec.ofNat 64 (offset + i + 1) by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) by decide]
        bv_omega] at h28
  have h28' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 120) rlpFieldToU256Be_prog 30
      (.ADDI .x28 .x28 (1 : BitVec 12)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) h28
  have h29 := addi_spec_gen_same_within .x29
    (outputPtr + BitVec.ofNat 64 (32 - len + i)) (1 : BitVec 12) (B + 124)
    (by decide)
  rw [show outputPtr + BitVec.ofNat 64 (32 - len + i) +
      signExtend12 (1 : BitVec 12) =
      outputPtr + BitVec.ofNat 64 (32 - len + i + 1) by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) by decide]
        bv_omega] at h29
  have h29' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 124) rlpFieldToU256Be_prog 31
      (.ADDI .x29 .x29 (1 : BitVec 12)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) h29
  have h6 := addi_spec_gen_same_within .x6 count (-1 : BitVec 12)
    (B + 128) (by decide)
  have h6' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 128) rlpFieldToU256Be_prog 32
      (.ADDI .x6 .x6 (-1 : BitVec 12)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) h6
  have s0 := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ (outputPtr + BitVec.ofNat 64 (32 - len + i))) **
      (.x6 ↦ᵣ count) ** bytesRegion outputPtr out) (by pcf) hl'
  have s1 := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (offset + i))) **
      (.x6 ↦ᵣ count) ** bytesRegion listBase bytes) (by pcf) hs'
  have s2 := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ (outputPtr + BitVec.ofNat 64 (32 - len + i))) **
      (.x30 ↦ᵣ (copyByte bytes offset i).zeroExtend 64) ** (.x6 ↦ᵣ count) **
      bytesRegion listBase bytes **
      bytesRegion outputPtr (out.set (32 - len + i) (copyByte bytes offset i)))
    (by pcf) h28'
  have s3 := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (offset + i + 1))) **
      (.x30 ↦ᵣ (copyByte bytes offset i).zeroExtend 64) ** (.x6 ↦ᵣ count) **
      bytesRegion listBase bytes **
      bytesRegion outputPtr (out.set (32 - len + i) (copyByte bytes offset i)))
    (by pcf) h29'
  have s4 := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (offset + i + 1))) **
      (.x29 ↦ᵣ (outputPtr + BitVec.ofNat 64 (32 - len + i + 1))) **
      (.x30 ↦ᵣ (copyByte bytes offset i).zeroExtend 64) **
      bytesRegion listBase bytes **
      bytesRegion outputPtr (out.set (32 - len + i) (copyByte bytes offset i)))
    (by pcf) h6'
  have s01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s0 s1
  have s012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s01 s2
  have s0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s012 s3
  have sall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s0123 s4
  exact cpsTripleWithin_extend_code (fun a ins hi => wrapperCode_mono a ins hi)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp) sall)

#print axioms copyBody_spec_within

/-- Exact bounded closure of K35's top-tested copy loop (instructions 27--33).
    The post exposes the genuine right-aligned byte window. -/
theorem copyLoop_spec_within
    (listBase outputPtr old30 : Word) (bytes : List (BitVec 8))
    (offset len : Nat)
    (hsalign : listBase.toNat % 8 = 0)
    (hdalign : outputPtr.toNat % 8 = 0)
    (hfit : len ≤ 32) (hbound : offset + len ≤ bytes.length)
    (hsrc : listBase.toNat + bytes.length < 2 ^ 64)
    (hdst : outputPtr.toNat + 32 < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (houtvalid : ∀ k, k < 32 →
      isValidByteAccess (outputPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * len + 1) (B + 108) (B + 136) code
      ((.x6 ↦ᵣ BitVec.ofNat 64 len) **
       (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 offset)) **
       (.x29 ↦ᵣ (outputPtr + BitVec.ofNat 64 (32 - len))) **
       (.x30 ↦ᵣ old30) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes **
       bytesRegion outputPtr (List.replicate 32 0))
      ((.x6 ↦ᵣ (0 : Word)) **
       (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (offset + len))) **
       (.x29 ↦ᵣ (outputPtr + BitVec.ofNat 64 32)) ** regOwn .x30 **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
       bytesRegion outputPtr (rightAligned32 bytes
         (BitVec.ofNat 64 offset) (BitVec.ofNat 64 len))) := by
  have hbmono : ∀ a ins, CodeReq.singleton (B + 108)
      (.BEQ .x6 .x0 (28 : BitVec 13)) a = some ins → code a = some ins := by
    intro a ins hi
    exact wrapperCode_mono a ins (CodeReq.ofProg_mem_at B (B + 108)
      rlpFieldToU256Be_prog 27 (.BEQ .x6 .x0 (28 : BitVec 13))
      (by bv_omega) (by rw [program_length]; decide) rfl
      (by rw [program_length]; decide) a ins hi)
  have htgt : B + 108 + signExtend13 (28 : BitVec 13) = B + 136 := by decide
  have hfall : B + 108 + 4 = B + 112 := by bv_omega
  have hback : B + 132 + signExtend21 (-24 : BitVec 21) = B + 108 := by decide
  have loopAux : ∀ (n i : Nat) (v30 : Word), i + n = len →
      cpsTripleWithin (7 * n + 1) (B + 108) (B + 136) code
        ((.x6 ↦ᵣ BitVec.ofNat 64 n) **
         (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (offset + i))) **
         (.x29 ↦ᵣ (outputPtr + BitVec.ofNat 64 (32 - len + i))) **
         (.x30 ↦ᵣ v30) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion listBase bytes ** bytesRegion outputPtr
           (copyWin bytes offset len i))
        ((.x6 ↦ᵣ (0 : Word)) **
         (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (offset + len))) **
         (.x29 ↦ᵣ (outputPtr + BitVec.ofNat 64 32)) ** regOwn .x30 **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
         bytesRegion outputPtr (copyWin bytes offset len len)) := by
    intro n
    induction n with
    | zero =>
        intro i v30 hsum
        have hb := beq_spec_gen_within .x6 .x0 (28 : BitVec 13)
          (BitVec.ofNat 64 0) (0 : Word) (B + 108)
        rw [htgt, hfall] at hb
        have hbF := cpsBranchWithin_frameR
          ((.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (offset + i))) **
           (.x29 ↦ᵣ (outputPtr + BitVec.ofNat 64 (32 - len + i))) **
           (.x30 ↦ᵣ v30) ** bytesRegion listBase bytes **
           bytesRegion outputPtr (copyWin bytes offset len i)) (by pcf) hb
        have ht := cpsBranchWithin_takenPath
          (cpsBranchWithin_extend_code hbmono hbF) (fun hp hq => by
            obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hq
            exact ((sepConj_pure_right _).1 h_pure).2 (by decide))
        have hi_eq : i = len := by omega
        subst i
        rw [show (0#64 : Word) = 0 by decide] at ht
        simpa only [Nat.zero_add, Nat.add_zero, show (0#64 : Word) = 0 by decide]
          using cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
            (fun h hp => by
              let Rest : Assertion :=
                (.x6 ↦ᵣ (0 : Word)) **
                (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (offset + len))) **
                (.x29 ↦ᵣ (outputPtr + (32 : Word))) **
                (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
                bytesRegion outputPtr (copyWin bytes offset len len)
              have hp0 : (((.x30 ↦ᵣ v30) ** Rest) h) := by
                unfold Rest
                have hnat : 32 - len + len = 32 := by omega
                have hword : BitVec.ofNat 64 (32 - len + len) = (32 : Word) := by
                  rw [hnat]
                  decide
                rw [hword] at hp
                let Fr : Assertion :=
                  (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (offset + len))) **
                  (.x29 ↦ᵣ (outputPtr + (32 : Word))) **
                  (.x30 ↦ᵣ v30) ** bytesRegion listBase bytes **
                  bytesRegion outputPtr (copyWin bytes offset len len)
                have hp' : ((((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
                    Fr) h) := by
                  obtain ⟨g1, g2, gd, gu, hleft, hfr⟩ := hp
                  exact ⟨g1, g2, gd, gu,
                    sepConj_mono_right
                      (fun h' hh => ((sepConj_pure_right h').1 hh).1)
                      g1 hleft, hfr⟩
                unfold Fr at hp'
                xperm_hyp hp'
              have hp1 := sepConj_mono (regIs_implies_regOwn .x30)
                (fun _ hh => hh) h hp0
              unfold Rest at hp1
              rw [show BitVec.ofNat 64 32 = (32 : Word) by decide]
              xperm_hyp hp1) ht
    | succ k ih =>
        intro i v30 hsum
        have hi : i < len := by omega
        have hb := beq_spec_gen_within .x6 .x0 (28 : BitVec 13)
          (BitVec.ofNat 64 (k + 1)) (0 : Word) (B + 108)
        rw [htgt, hfall] at hb
        have hbF := cpsBranchWithin_frameR
          ((.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (offset + i))) **
           (.x29 ↦ᵣ (outputPtr + BitVec.ofNat 64 (32 - len + i))) **
           (.x30 ↦ᵣ v30) ** bytesRegion listBase bytes **
           bytesRegion outputPtr (copyWin bytes offset len i)) (by pcf) hb
        have hk64 : k + 1 < 2 ^ 64 := by omega
        have hne : BitVec.ofNat 64 (k + 1) ≠ (0 : Word) := by
          intro h_eq
          have ht := congrArg BitVec.toNat h_eq
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at ht
          simp at ht
        have hf := cpsBranchWithin_ntakenPath
          (cpsBranchWithin_extend_code hbmono hbF) (fun hp hq => by
            obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hq
            exact hne ((sepConj_pure_right _).1 h_pure).2)
        have hf' : cpsTripleWithin 1 (B + 108) (B + 112) code
            (((.x6 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word))) **
              ((.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (offset + i))) **
               (.x29 ↦ᵣ (outputPtr + BitVec.ofNat 64 (32 - len + i))) **
               (.x30 ↦ᵣ v30) ** bytesRegion listBase bytes **
               bytesRegion outputPtr (copyWin bytes offset len i)))
            ((.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (offset + i))) **
             (.x29 ↦ᵣ (outputPtr + BitVec.ofNat 64 (32 - len + i))) **
             (.x30 ↦ᵣ v30) ** (.x6 ↦ᵣ BitVec.ofNat 64 (k + 1)) **
             bytesRegion listBase bytes **
             bytesRegion outputPtr (copyWin bytes offset len i) **
             (.x0 ↦ᵣ (0 : Word))) := cpsTripleWithin_weaken (fun _ hp => hp)
          (fun h hp => by
            have hp' := sepConj_mono_left
              (sepConj_mono_right (fun h' hh => ((sepConj_pure_right h').1 hh).1)) h hp
            xperm_hyp hp') hf
        have hbody := copyBody_spec_within listBase outputPtr v30
          (BitVec.ofNat 64 (k + 1)) bytes (copyWin bytes offset len i)
          offset len i hsalign hdalign hi hfit hbound hsrc hdst hvalid
          houtvalid (length_copyWin bytes offset len i hfit (by omega))
        have hdec : BitVec.ofNat 64 (k + 1) + signExtend12 (-1 : BitVec 12) =
            BitVec.ofNat 64 k := by
          rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) by decide]
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hk64]
          simp only [show (-1 : Word).toNat = 2 ^ 64 - 1 by decide]
          omega
        have hwin : (copyWin bytes offset len i).set (32 - len + i)
            (copyByte bytes offset i) = copyWin bytes offset len (i + 1) := by
          rw [← setBytes_singleton, copyWin_step bytes offset len i hfit hi]
        rw [hdec, hwin] at hbody
        rw [show offset + i + 1 = offset + (i + 1) by omega,
          show 32 - len + i + 1 = 32 - len + (i + 1) by omega] at hbody
        have hbody0 := cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf) hbody
        have hj := jal_x0_spec_gen_within (-24 : BitVec 21) (B + 132)
        rw [hback] at hj
        have hj' := cpsTripleWithin_extend_code (cr' := code) (fun a ins hmem =>
          wrapperCode_mono a ins (CodeReq.ofProg_mem_at B (B + 132)
            rlpFieldToU256Be_prog 33 (.JAL .x0 (-24 : BitVec 21))
            (by bv_omega) (by rw [program_length]; decide) rfl
            (by rw [program_length]; decide) a ins hmem)) hj
        let R : Assertion :=
          (.x6 ↦ᵣ BitVec.ofNat 64 k) **
          (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 (offset + (i + 1)))) **
          (.x29 ↦ᵣ (outputPtr + BitVec.ofNat 64 (32 - len + (i + 1)))) **
          (.x30 ↦ᵣ (copyByte bytes offset i).zeroExtend 64) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
          bytesRegion outputPtr (copyWin bytes offset len (i + 1))
        have hjF := cpsTripleWithin_frameR R (by unfold R; pcf) hj'
        have hjS : cpsTripleWithin 1 (B + 132) (B + 108) code R R :=
          cpsTripleWithin_weaken
            (fun h hp => by simpa only [sepConj_emp_left'] using hp)
            (fun h hp => by simpa only [sepConj_emp_left'] using hp) hjF
        have htail := ih (i + 1)
          ((copyByte bytes offset i).zeroExtend 64) (by omega)
        have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
          hf' hbody0
        have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
          s1 hjS
        have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
          s2 htail
        rw [show 7 * (k + 1) + 1 = 1 + 5 + 1 + (7 * k + 1) by ring]
        exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hp => hp) s3
  have h0 := loopAux len 0 old30 (by omega)
  rw [copyWin_zero bytes offset len hfit] at h0
  have hdone := copyWin_done bytes offset len hfit hbound
  have hlen64 : len < 2 ^ 64 := by omega
  have hoff64 : offset < 2 ^ 64 := by omega
  unfold rightAligned32 selectedBytes
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64,
    Nat.mod_eq_of_lt hoff64]
  rw [hdone] at h0
  simpa only [Nat.zero_add, show 32 - len + len = 32 by omega] using h0

#print axioms copyLoop_spec_within

end EvmAsm.Codegen.RlpFieldToU256BeSAsm
