/-
  Verified SAsm port of `header_extract_logs_bloom` (K153).

  The wrapper selects header field 6 through the strict K20 list selector,
  checks the selected field's length, and copies its 256-byte payload.
-/

import EvmAsm.Codegen.Programs.Bloom
import EvmAsm.Codegen.Programs.RlpListNthItemSAsm
import EvmAsm.Rv64.SAsm.GlobalData
import EvmAsm.Rv64.SAsm.MultiDword

namespace EvmAsm.Codegen.HeaderExtractLogsBloomSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt
open EvmAsm.EL.RLP

abbrev B : Word := (GuestAddrs.header_extract_logs_bloom : Word)
abbrev K20B : Word := (GuestAddrs.rlp_list_nth_item : Word)
abbrev offsetCell : Word := (GuestAddrs.helb_offset : Word)
abbrev lengthCell : Word := (GuestAddrs.helb_length : Word)

theorem program_length : headerExtractLogsBloom_prog.length = 46 := by decide

def wrapperCode : CodeReq :=
  CodeReq.ofProg B headerExtractLogsBloom_prog

def code : CodeReq :=
  wrapperCode.union EvmAsm.Codegen.RlpListNthItemSAsm.code

theorem wrapper_list_disjoint :
    wrapperCode.Disjoint EvmAsm.Codegen.RlpListNthItemSAsm.code := by
  unfold wrapperCode EvmAsm.Codegen.RlpListNthItemSAsm.code B
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [program_length]
    decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]
    decide
  · rw [program_length, EvmAsm.Codegen.RlpListNthItemSAsm.total_length]
    decide

theorem headerExtractLogsBloom_body_eq_prog :
    headerExtractLogsBloom_prog = headerExtractLogsBloom_prog := rfl

#guard headerExtractLogsBloom_prog.length = 46

/-! The semantic result of K153.  Failure and wrong-length outcomes preserve
    the caller's output bytes; success returns the selected 256-byte payload. -/

inductive Result (bytes : List (BitVec 8)) (base : Word)
    (listLen index : Nat) (oldOut : List (BitVec 8)) :
    Word → List (BitVec 8) → Prop
  | listFailure
      (hfail : EvmAsm.Codegen.RlpListNthItemSAsm.Failure
        bytes base listLen index) :
      Result bytes base listLen index oldOut 1 oldOut
  | wrongLength (offset len : Word)
      (hok : EvmAsm.Codegen.RlpListNthItemSAsm.Success
        bytes base listLen index offset len)
      (hlen : len.toNat ≠ 256) :
      Result bytes base listLen index oldOut 2 oldOut
  | success (offset : Word)
      (hok : EvmAsm.Codegen.RlpListNthItemSAsm.Success
        bytes base listLen index offset (256 : Word)) :
      Result bytes base listLen index oldOut 0
        ((bytes.drop offset.toNat).take 256)

/-! ## The 32-dword copy loop

The loop uses `x28`/`x29` as source/destination cursors, `x30` as the
remaining dword count, and `x31` as the temporary load register. -/

def copyWin (srcBytes outBytes : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  srcBytes.take (8 * i) ++ outBytes.drop (8 * i)

theorem copyWin_zero (srcBytes outBytes : List (BitVec 8)) :
    copyWin srcBytes outBytes 0 = outBytes := by
  simp [copyWin]

theorem copyWin_full (srcBytes outBytes : List (BitVec 8))
    (hs : srcBytes.length = 256) (ho : outBytes.length = 256) :
    copyWin srcBytes outBytes 32 = srcBytes := by
  simp only [copyWin, Nat.reduceMul]
  rw [List.take_of_length_le (by omega), List.drop_eq_nil_of_le (by omega),
    List.append_nil]

theorem copyWin_length (srcBytes outBytes : List (BitVec 8)) (i : Nat)
    (hs : srcBytes.length = 256) (ho : outBytes.length = 256) (hi : i ≤ 32) :
    (copyWin srcBytes outBytes i).length = 256 := by
  simp only [copyWin, List.length_append, List.length_take, List.length_drop,
    hs, ho]
  omega

theorem copyWin_step (srcBytes outBytes : List (BitVec 8)) (i : Nat)
    (hs : srcBytes.length = 256) (ho : outBytes.length = 256) (hi : i < 32) :
    setBytes (copyWin srcBytes outBytes i) (8 * i)
      (dwordBytes (packBytes ((srcBytes.drop (8 * i)).take 8))) =
      copyWin srcBytes outBytes (i + 1) := by
  have htake : (srcBytes.take (8 * i)).length = 8 * i := by
    simp only [List.length_take, hs]
    have hbound : 8 * i ≤ 256 := by omega
    simp [Nat.min_eq_left hbound]
  have hseglen : ((srcBytes.drop (8 * i)).take 8).length = 8 := by
    simp only [List.length_take, List.length_drop, hs]
    omega
  have hpayload : dwordBytes (packBytes ((srcBytes.drop (8 * i)).take 8)) =
      (srcBytes.drop (8 * i)).take 8 := dwordBytes_packBytes _ hseglen
  rw [hpayload, copyWin, setBytes_append_right _ _ _ _ (by rw [htake]), htake,
    Nat.sub_self]
  have hfit : 0 + ((srcBytes.drop (8 * i)).take 8).length ≤
      (outBytes.drop (8 * i)).length := by
    rw [hseglen]
    simp only [List.length_drop, ho]
    omega
  have hslot := setBytes_slot (outBytes.drop (8 * i))
    ((srcBytes.drop (8 * i)).take 8) 0 hfit
  rw [List.drop_zero, hseglen] at hslot
  have hdrop : (setBytes (outBytes.drop (8 * i)) 0
      ((srcBytes.drop (8 * i)).take 8)).drop 8 =
      (outBytes.drop (8 * i)).drop 8 := by
    simpa [hseglen] using
      (setBytes_drop_of_le ((srcBytes.drop (8 * i)).take 8)
        (outBytes.drop (8 * i)) 0 8 (by rw [hseglen]))
  have hset : setBytes (outBytes.drop (8 * i)) 0
      ((srcBytes.drop (8 * i)).take 8) =
      (srcBytes.drop (8 * i)).take 8 ++ (outBytes.drop (8 * i)).drop 8 := by
    conv_lhs =>
      rw [← List.take_append_drop 8
        (setBytes (outBytes.drop (8 * i)) 0
          ((srcBytes.drop (8 * i)).take 8))]
    rw [hslot, hdrop]
  rw [hset, show (outBytes.drop (8 * i)).drop 8 =
      outBytes.drop (8 * (i + 1)) by rw [List.drop_drop]; congr 1]
  simp only [copyWin]
  rw [← List.append_assoc]
  congr 1
  rw [show srcBytes.take (8 * i) ++ (srcBytes.drop (8 * i)).take 8 =
      srcBytes.take (8 * (i + 1)) by rw [← List.take_add]; congr 1]

def copyStepBlock : List Instr :=
  [.LD .x31 .x28 (0 : BitVec 12),
   .SD .x29 .x31 (0 : BitVec 12),
   .ADDI .x28 .x28 (8 : BitVec 12),
   .ADDI .x29 .x29 (8 : BitVec 12),
   .ADDI .x30 .x30 (-1 : BitVec 12)]

def copyStepRf (rf : RegFile) (v : Word) : RegFile :=
  let r1 := rf.set .x31 v
  let r2 := r1.set .x28 (r1.get .x28 + signExtend12 (8 : BitVec 12))
  let r3 := r2.set .x29 (r2.get .x29 + signExtend12 (8 : BitVec 12))
  r3.set .x30 (r3.get .x30 + signExtend12 (-1 : BitVec 12))

theorem copyStepRf_get_x28 (rf : RegFile) (v : Word) :
    (copyStepRf rf v).get .x28 = rf.get .x28 + signExtend12 (8 : BitVec 12) := by
  unfold copyStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem copyStepRf_get_x29 (rf : RegFile) (v : Word) :
    (copyStepRf rf v).get .x29 = rf.get .x29 + signExtend12 (8 : BitVec 12) := by
  unfold copyStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem copyStepRf_get_x30 (rf : RegFile) (v : Word) :
    (copyStepRf rf v).get .x30 = rf.get .x30 + signExtend12 (-1 : BitVec 12) := by
  unfold copyStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

def copyInv (src dst : Word) (srcBytes outBytes : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws _ =>
    rf.get .x10 = src ∧ rf.get .x11 = dst ∧
    rf.get .x28 = src + BitVec.ofNat 64 (8 * i) ∧
    rf.get .x29 = dst + BitVec.ofNat 64 (8 * i) ∧
    rf.get .x30 = BitVec.ofNat 64 (32 - i) ∧
    i ≤ 32 ∧ srcBytes.length = 256 ∧ outBytes.length = 256 ∧
    src.toNat + 256 < 2 ^ 64 ∧ dst.toNat + 256 < 2 ^ 64 ∧
    (src.toNat + 256 ≤ dst.toNat ∨ dst.toNat + 256 ≤ src.toNat) ∧
    ws = copyWin srcBytes outBytes i

private theorem ld_ro_miss (reg : Region) (rwb : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (hmiss : ¬ inRw rwb ws (rf.get rs1 + signExtend12 ofs) 8) :
    execInstrRF reg rwb rf ws (.LD rd rs1 ofs) =
      (rf.set rd (reg.dwordAt (rf.get rs1 + signExtend12 ofs)), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg hmiss]

private theorem src_miss (src dst : Word) (ws : List (BitVec 8)) (i : Nat)
    (hi : i < 32) (hws : ws.length = 256)
    (hsrc : src.toNat + 256 < 2 ^ 64) (hdst : dst.toNat + 256 < 2 ^ 64)
    (hdisj : src.toNat + 256 ≤ dst.toNat ∨ dst.toNat + 256 ≤ src.toNat) :
    ¬ inRw dst ws (src + BitVec.ofNat 64 (8 * i)) 8 := by
  unfold inRw
  rw [hws]
  rcases hdisj with h | h <;> bv_omega

private theorem src_dword (src : Word) (srcBytes : List (BitVec 8)) (i : Nat)
    (hi : i < 32) :
    Region.dwordAt ⟨src, srcBytes⟩ (src + BitVec.ofNat 64 (8 * i)) =
      packBytes ((srcBytes.drop (8 * i)).take 8) := by
  unfold Region.dwordAt
  rw [show (src + BitVec.ofNat 64 (8 * i) - src).toNat = 8 * i by
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega]

private theorem copy_engine (src dst : Word) (srcBytes : List (BitVec 8))
    (rf : RegFile) (ws : List (BitVec 8)) (i : Nat) (hi : i < 32)
    (hx28 : rf.get .x28 = src + BitVec.ofNat 64 (8 * i))
    (hx29 : rf.get .x29 = dst + BitVec.ofNat 64 (8 * i))
    (hws : ws.length = 256)
    (hsrc : src.toNat + 256 < 2 ^ 64) (hdst : dst.toNat + 256 < 2 ^ 64)
    (hdisj : src.toNat + 256 ≤ dst.toNat ∨ dst.toNat + 256 ≤ src.toNat) :
    execBlock ⟨src, srcBytes⟩ dst rf ws copyStepBlock =
      (copyStepRf rf (packBytes ((srcBytes.drop (8 * i)).take 8)),
       setBytes ws (8 * i)
         (dwordBytes (packBytes ((srcBytes.drop (8 * i)).take 8)))) := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hload : rf.get .x28 + signExtend12 (0 : BitVec 12) =
      src + BitVec.ofNat 64 (8 * i) := by rw [hx28, hse0]; simp
  have hmiss : ¬ inRw dst ws (rf.get .x28 + signExtend12 (0 : BitVec 12)) 8 := by
    rw [hload]
    exact src_miss src dst ws i hi hws hsrc hdst hdisj
  have hstore :
      ((rf.set .x31 (packBytes ((srcBytes.drop (8 * i)).take 8))).get .x29
        + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * i := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x31), hx29, hse0]
    bv_omega
  rw [show copyStepBlock = [.LD .x31 .x28 0, .SD .x29 .x31 0,
      .ADDI .x28 .x28 8, .ADDI .x29 .x29 8,
      .ADDI .x30 .x30 (-1 : BitVec 12)] from rfl]
  rw [execBlock_cons, ld_ro_miss _ _ _ _ .x31 .x28 (0 : BitVec 12) hmiss,
    hload, src_dword src srcBytes i hi]
  dsimp only
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ (8 * i) hstore]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide : Reg.x31 ≠ .x0)]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  unfold copyStepRf
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x31),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x31),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x30 ≠ .x31),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x30 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x30 ≠ .x29)]

private theorem copy_blockVCs (src dst : Word) (srcBytes : List (BitVec 8))
    (rf : RegFile) (ws : List (BitVec 8)) (i : Nat) (hi : i < 32)
    (hx28 : rf.get .x28 = src + BitVec.ofNat 64 (8 * i))
    (hx29 : rf.get .x29 = dst + BitVec.ofNat 64 (8 * i))
    (hws : ws.length = 256) (hs : srcBytes.length = 256)
    (hsrc : src.toNat + 256 < 2 ^ 64) (hdst : dst.toNat + 256 < 2 ^ 64)
    (hdisj : src.toNat + 256 ≤ dst.toNat ∨ dst.toNat + 256 ≤ src.toNat) :
    blockVCs ⟨src, srcBytes⟩ dst rf ws copyStepBlock := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hload : rf.get .x28 + signExtend12 (0 : BitVec 12) =
      src + BitVec.ofNat 64 (8 * i) := by rw [hx28, hse0]; simp
  have hmiss : ¬ inRw dst ws (rf.get .x28 + signExtend12 (0 : BitVec 12)) 8 := by
    rw [hload]
    exact src_miss src dst ws i hi hws hsrc hdst hdisj
  have hstore :
      ((rf.set .x31 (Region.dwordAt ⟨src, srcBytes⟩
        (rf.get .x28 + signExtend12 (0 : BitVec 12)))).get .x29
        + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * i := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x31), hx29, hse0]
    bv_omega
  have hsrcOff : (src + BitVec.ofNat 64 (8 * i) - src).toNat = 8 * i := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [show copyStepBlock = [.LD .x31 .x28 0, .SD .x29 .x31 0,
      .ADDI .x28 .x28 8, .ADDI .x29 .x29 8,
      .ADDI .x30 .x30 (-1 : BitVec 12)] from rfl]
  refine ⟨?_, ?_⟩
  · show (if inRw dst ws (rf.get .x28 + signExtend12 0) 8 then _
      else Region.loadOk ⟨src, srcBytes⟩
        (rf.get .x28 + signExtend12 0) 8)
    rw [if_neg hmiss, hload]
    unfold Region.loadOk
    constructor
    · rw [hsrcOff]
      exact Nat.dvd_mul_right 8 i
    · rw [hsrcOff, hs]
      omega
  · rw [ld_ro_miss _ _ _ _ .x31 .x28 (0 : BitVec 12) hmiss]
    simp only [blockVCs, loadSem, storeSem]
    refine ⟨?_, ?_⟩
    · unfold inRw
      rw [hstore, hws]
      omega
    · exact ⟨trivial, trivial, trivial, trivial⟩

def copyBody (src dst : Word) (srcBytes outBytes : List (BitVec 8)) : Stmt :=
  .block "init" [.MV .x28 .x10, .MV .x29 .x11, .LI .x30 (32 : Word)] ;;;
  .«while» "loop" (.bne .x30 .x0) 32 (copyInv src dst srcBytes outBytes)
    (.block "copy" copyStepBlock)

def copyFn (src dst : Word) (srcBytes outBytes : List (BitVec 8)) : Fn where
  name := "headerLogsBloomCopy"
  region := ⟨src, srcBytes⟩
  rw := ⟨dst, 256⟩
  pre := fun rf ws _ =>
    rf.get .x10 = src ∧ rf.get .x11 = dst ∧ ws = outBytes ∧
    srcBytes.length = 256 ∧ outBytes.length = 256 ∧
    src.toNat + 256 < 2 ^ 64 ∧ dst.toNat + 256 < 2 ^ 64 ∧
    (src.toNat + 256 ≤ dst.toNat ∨ dst.toNat + 256 ≤ src.toNat)
  post := fun rf ws _ => rf.get .x10 = src ∧ rf.get .x11 = dst ∧ ws = srcBytes
  body := copyBody src dst srcBytes outBytes

theorem copyFn_spec (src dst : Word) (srcBytes outBytes : List (BitVec 8))
    (hwf : (Region.mk src srcBytes).wf)
    (hrww : RwRegion.wf ⟨dst, 256⟩) (base : Word) :
    (copyFn src dst srcBytes outBytes).Spec base := by
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case headerLogsBloomCopy.loop.inv_init =>
    rintro rf' ws' A' ⟨rf₀, ws₀, -, ⟨hx10, hx11, hws, hs, ho, hsrc, hdst, hdisj⟩,
      rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, by omega, hs, ho, hsrc, hdst, hdisj, ?_⟩
    · exact hx10
    · exact hx11
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, hx10, hx11]
      simp
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, hx10, hx11]
      simp
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true]
      rfl
    · exact hws.trans (copyWin_zero srcBytes outBytes).symm
  case headerLogsBloomCopy.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, 
      ⟨⟨hx10, hx11, hx28, hx29, hx30, hile, hs, ho, hsrc, hdst, hdisj, hwin⟩, hcond⟩,
      rfl, rfl⟩
    simp only [show (copyFn src dst srcBytes outBytes).region =
      (⟨src, srcBytes⟩ : Region) from rfl,
      show (copyFn src dst srcBytes outBytes).rw.base = dst from rfl]
    have hwslen : ws₀.length = 256 := by
      rw [hwin]
      exact copyWin_length srcBytes outBytes i hs ho hile
    rw [copy_engine src dst srcBytes rf₀ ws₀ i hi hx28 hx29 hwslen hsrc hdst hdisj]
    refine ⟨hx10, hx11, ?_, ?_, ?_, by omega, hs, ho, hsrc, hdst, hdisj, ?_⟩
    · rw [copyStepRf_get_x28, hx28,
        show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      bv_omega
    · rw [copyStepRf_get_x29, hx29,
        show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      bv_omega
    · rw [copyStepRf_get_x30, hx30,
        show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      interval_cases i <;> decide
    · rw [hwin, copyWin_step srcBytes outBytes i hs ho hi]
  case headerLogsBloomCopy.loop.exhausted =>
    rintro rf ws A ⟨hx10, hx11, hx28, hx29, hx30, hile, hs, ho, hsrc, hdst, hdisj, hwin⟩
    simp only [Cond.holds, hx30, RegFile.get_x0, not_not]
    have hi32 : (32 - 32 : Nat) = 0 := rfl
    simp only [hi32] at hx30
    exact by decide
  case headerLogsBloomCopy.loop.body.copy.mem =>
    rintro rf ws A hlen
      ⟨i, hi, ⟨hx10, hx11, hx28, hx29, hx30, hile, hs, ho, hsrc, hdst, hdisj, hwin⟩, hcond⟩
    simp only [show (copyFn src dst srcBytes outBytes).region =
      (⟨src, srcBytes⟩ : Region) from rfl,
      show (copyFn src dst srcBytes outBytes).rw.base = dst from rfl]
    change ws.length = 256 at hlen
    exact copy_blockVCs src dst srcBytes rf ws i hi hx28 hx29 hlen hs hsrc hdst hdisj
  case headerLogsBloomCopy.post =>
    rintro rf ws A hsp
    simp only [copyFn, copyBody] at hsp ⊢
    simp [Stmt.sp] at hsp
    obtain ⟨⟨i, hi, hInv⟩, hncond⟩ := hsp
    obtain ⟨hx10, hx11, hx28, hx29, hx30, hile, hs, ho, hsrc, hdst, hdisj, hwin⟩ := hInv
    have hi32 : i = 32 := by
      simp only [Cond.holds, hx30, RegFile.get_x0, not_not] at hncond
      have hnat := congrArg BitVec.toNat hncond
      rw [BitVec.toNat_ofNat] at hnat
      have hlt : 32 - i < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hlt] at hnat
      have hzero : 32 - i = 0 := hnat
      omega
    subst hi32
    exact ⟨hx10, hx11, by simpa [copyWin_full srcBytes outBytes hs ho] using hwin⟩

def copyLoopBody (src dst : Word) (srcBytes outBytes : List (BitVec 8)) : Stmt :=
  .«while» "loop" (.bne .x30 .x0) 32 (copyInv src dst srcBytes outBytes)
    (.block "copy" copyStepBlock)

def copyLoopFn (src dst : Word) (srcBytes outBytes : List (BitVec 8)) : Fn where
  name := "headerLogsBloomCopyLoop"
  region := ⟨src, srcBytes⟩
  rw := ⟨dst, 256⟩
  pre := fun rf ws A => copyInv src dst srcBytes outBytes 0 rf ws A
  post := fun rf ws _ => rf.get .x10 = src ∧ rf.get .x11 = dst ∧ ws = srcBytes
  body := copyLoopBody src dst srcBytes outBytes

theorem copyLoopFn_spec (src dst : Word) (srcBytes outBytes : List (BitVec 8))
    (hwf : (Region.mk src srcBytes).wf)
    (hrww : RwRegion.wf ⟨dst, 256⟩) (base : Word) :
    (copyLoopFn src dst srcBytes outBytes).Spec base := by
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case headerLogsBloomCopyLoop.loop.inv_init =>
    rintro rf ws A ⟨hx10, hx11, hx28, hx29, hx30, hile, hs, ho, hsrc, hdst,
      hdisj, hwin⟩
    exact ⟨hx10, hx11, hx28, hx29, hx30, hile, hs, ho, hsrc, hdst, hdisj, hwin⟩
  case headerLogsBloomCopyLoop.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, 
      ⟨⟨hx10, hx11, hx28, hx29, hx30, hile, hs, ho, hsrc, hdst, hdisj, hwin⟩,
        hcond⟩, rfl, rfl⟩
    simp only [show (copyLoopFn src dst srcBytes outBytes).region =
      (⟨src, srcBytes⟩ : Region) from rfl,
      show (copyLoopFn src dst srcBytes outBytes).rw.base = dst from rfl]
    have hwslen : ws₀.length = 256 := by
      rw [hwin]
      exact copyWin_length srcBytes outBytes i hs ho hile
    rw [copy_engine src dst srcBytes rf₀ ws₀ i hi hx28 hx29 hwslen hsrc hdst hdisj]
    refine ⟨hx10, hx11, ?_, ?_, ?_, by omega, hs, ho, hsrc, hdst, hdisj, ?_⟩
    · rw [copyStepRf_get_x28, hx28,
        show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      bv_omega
    · rw [copyStepRf_get_x29, hx29,
        show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      bv_omega
    · rw [copyStepRf_get_x30, hx30,
        show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      interval_cases i <;> decide
    · rw [hwin, copyWin_step srcBytes outBytes i hs ho hi]
  case headerLogsBloomCopyLoop.loop.exhausted =>
    rintro rf ws A ⟨hx10, hx11, hx28, hx29, hx30, hile, hs, ho, hsrc, hdst,
      hdisj, hwin⟩
    simp only [Cond.holds, hx30, RegFile.get_x0, not_not]
    decide
  case headerLogsBloomCopyLoop.loop.body.copy.mem =>
    rintro rf ws A hlen
      ⟨i, hi, ⟨hx10, hx11, hx28, hx29, hx30, hile, hs, ho, hsrc, hdst,
        hdisj, hwin⟩, hcond⟩
    simp only [show (copyLoopFn src dst srcBytes outBytes).region =
      (⟨src, srcBytes⟩ : Region) from rfl,
      show (copyLoopFn src dst srcBytes outBytes).rw.base = dst from rfl]
    change ws.length = 256 at hlen
    exact copy_blockVCs src dst srcBytes rf ws i hi hx28 hx29 hlen hs hsrc hdst hdisj
  case headerLogsBloomCopyLoop.post =>
    rintro rf ws A hsp
    simp only [copyLoopFn, copyLoopBody] at hsp ⊢
    simp [Stmt.sp] at hsp
    obtain ⟨⟨i, hi, hInv⟩, hncond⟩ := hsp
    obtain ⟨hx10, hx11, hx28, hx29, hx30, hile, hs, ho, hsrc, hdst, hdisj, hwin⟩ := hInv
    simp only [Cond.holds, hx30, RegFile.get_x0, not_not] at hncond
    have hnat := congrArg BitVec.toNat hncond
    rw [BitVec.toNat_ofNat] at hnat
    have hlt : 32 - i < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hlt] at hnat
    have hzero : 32 - i = 0 := by simpa using hnat
    have hi32 : i = 32 := by omega
    subst hi32
    exact ⟨hx10, hx11, by simpa [copyWin_full srcBytes outBytes hs ho] using hwin⟩

/-! The wrapper keeps `x10`/`x11` occupied by the ABI result while the copy
    loop runs.  This is the same loop invariant without those two callee
    inputs; keeping it as a separate Fn avoids pretending that the status and
    list-length registers are the source and destination pointers. -/

def copyInvNoAbi (src dst : Word) (srcBytes outBytes : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws _ =>
    rf.get .x28 = src + BitVec.ofNat 64 (8 * i) ∧
    rf.get .x29 = dst + BitVec.ofNat 64 (8 * i) ∧
    rf.get .x30 = BitVec.ofNat 64 (32 - i) ∧
    i ≤ 32 ∧ srcBytes.length = 256 ∧ outBytes.length = 256 ∧
    src.toNat + 256 < 2 ^ 64 ∧ dst.toNat + 256 < 2 ^ 64 ∧
    (src.toNat + 256 ≤ dst.toNat ∨ dst.toNat + 256 ≤ src.toNat) ∧
    ws = copyWin srcBytes outBytes i

def copyLoopNoAbiFn (src dst : Word) (srcBytes outBytes : List (BitVec 8)) : Fn where
  name := "headerLogsBloomCopyLoopNoAbi"
  region := ⟨src, srcBytes⟩
  rw := ⟨dst, 256⟩
  pre := fun rf ws A => copyInvNoAbi src dst srcBytes outBytes 0 rf ws A
  post := fun rf ws _ =>
    rf.get .x28 = src + BitVec.ofNat 64 256 ∧
    rf.get .x29 = dst + BitVec.ofNat 64 256 ∧
    rf.get .x30 = 0 ∧ ws = srcBytes
  body := .«while» "loop" (.bne .x30 .x0) 32
    (copyInvNoAbi src dst srcBytes outBytes) (.block "copy" copyStepBlock)

theorem copyLoopNoAbiFn_spec (src dst : Word) (srcBytes outBytes : List (BitVec 8))
    (hwf : (Region.mk src srcBytes).wf)
    (hrww : RwRegion.wf ⟨dst, 256⟩) (base : Word) :
    (copyLoopNoAbiFn src dst srcBytes outBytes).Spec base := by
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case headerLogsBloomCopyLoopNoAbi.loop.inv_init =>
    rintro rf ws A ⟨hx28, hx29, hx30, hile, hs, ho, hsrc, hdst, hdisj, hwin⟩
    exact ⟨hx28, hx29, hx30, hile, hs, ho, hsrc, hdst, hdisj, hwin⟩
  case headerLogsBloomCopyLoopNoAbi.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, 
      ⟨⟨hx28, hx29, hx30, hile, hs, ho, hsrc, hdst, hdisj, hwin⟩,
        hcond⟩, rfl, rfl⟩
    simp only [show (copyLoopNoAbiFn src dst srcBytes outBytes).region =
      (⟨src, srcBytes⟩ : Region) from rfl,
      show (copyLoopNoAbiFn src dst srcBytes outBytes).rw.base = dst from rfl]
    have hwslen : ws₀.length = 256 := by
      rw [hwin]
      exact copyWin_length srcBytes outBytes i hs ho hile
    rw [copy_engine src dst srcBytes rf₀ ws₀ i hi hx28 hx29 hwslen hsrc hdst hdisj]
    refine ⟨?_, ?_, ?_, by omega, hs, ho, hsrc, hdst, hdisj, ?_⟩
    · rw [copyStepRf_get_x28, hx28,
        show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      bv_omega
    · rw [copyStepRf_get_x29, hx29,
        show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      bv_omega
    · rw [copyStepRf_get_x30, hx30,
        show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      interval_cases i <;> decide
    · rw [hwin, copyWin_step srcBytes outBytes i hs ho hi]
  case headerLogsBloomCopyLoopNoAbi.loop.exhausted =>
    rintro rf ws A ⟨hx28, hx29, hx30, hile, hs, ho, hsrc, hdst, hdisj, hwin⟩
    simp only [Cond.holds, hx30, RegFile.get_x0, not_not]
    decide
  case headerLogsBloomCopyLoopNoAbi.loop.body.copy.mem =>
    rintro rf ws A hlen
      ⟨i, hi, ⟨hx28, hx29, hx30, hile, hs, ho, hsrc, hdst, hdisj, hwin⟩, hcond⟩
    simp only [show (copyLoopNoAbiFn src dst srcBytes outBytes).region =
      (⟨src, srcBytes⟩ : Region) from rfl,
      show (copyLoopNoAbiFn src dst srcBytes outBytes).rw.base = dst from rfl]
    change ws.length = 256 at hlen
    exact copy_blockVCs src dst srcBytes rf ws i hi hx28 hx29 hlen hs hsrc hdst hdisj
  case headerLogsBloomCopyLoopNoAbi.post =>
    rintro rf ws A hsp
    simp only [copyLoopNoAbiFn] at hsp ⊢
    simp [Stmt.sp] at hsp
    obtain ⟨⟨i, hi, hInv⟩, hncond⟩ := hsp
    obtain ⟨hx28, hx29, hx30, hile, hs, ho, hsrc, hdst, hdisj, hwin⟩ := hInv
    simp only [Cond.holds, hx30, RegFile.get_x0, not_not] at hncond
    have hnat := congrArg BitVec.toNat hncond
    rw [BitVec.toNat_ofNat] at hnat
    have hlt : 32 - i < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hlt] at hnat
    have hzero : 32 - i = 0 := by simpa using hnat
    have hi32 : i = 32 := by omega
    subst hi32
    have hws : ws = srcBytes := by
      rw [hwin, copyWin_full srcBytes outBytes hs ho]
    have hx28' : rf.get .x28 = src + BitVec.ofNat 64 256 := by
      simpa [Nat.reduceMul] using hx28
    have hx29' : rf.get .x29 = dst + BitVec.ofNat 64 256 := by
      simpa [Nat.reduceMul] using hx29
    have hx30' : rf.get .x30 = 0 := by
      simpa using hx30
    exact ⟨hx28', hx29', hx30', hws⟩

theorem copyLoopNoAbiFn_code_spec (src dst : Word)
    (srcBytes outBytes : List (BitVec 8))
    (hwf : (Region.mk src srcBytes).wf)
    (hrww : RwRegion.wf ⟨dst, 256⟩) :
    cpsTripleWithin (copyLoopNoAbiFn src dst srcBytes outBytes).body.steps
      (B + 112)
      (B + 112 + BitVec.ofNat 64
        (4 * (copyLoopNoAbiFn src dst srcBytes outBytes).body.size))
      code
      (asrtM (copyLoopNoAbiFn src dst srcBytes outBytes).region
        (copyLoopNoAbiFn src dst srcBytes outBytes).rw
        (copyLoopNoAbiFn src dst srcBytes outBytes).pre)
      (asrtM (copyLoopNoAbiFn src dst srcBytes outBytes).region
        (copyLoopNoAbiFn src dst srcBytes outBytes).rw
        (copyLoopNoAbiFn src dst srcBytes outBytes).post) := by
  have h := copyLoopNoAbiFn_spec src dst srcBytes outBytes hwf hrww (B + 112)
  have hmono : ∀ a i,
      CodeReq.ofProg (B + 112)
          ((copyLoopNoAbiFn src dst srcBytes outBytes).body.flatten (B + 112))
          a = some i → code a = some i := by
    intro a i hi
    unfold copyLoopNoAbiFn at hi
    let seg : List Instr := [.BEQ .x30 .x0 (28 : BitVec 13)] ++ copyStepBlock ++
      [.JAL .x0 (-24 : BitVec 21)]
    have hbase := CodeReq.ofProg_mono_sub B (B + 112) headerExtractLogsBloom_prog
      seg 28 (by bv_omega) (by decide) (by decide)
      (by rw [program_length]; decide)
      a i (by simpa [seg] using hi)
    unfold code
    exact CodeReq.union_mono_left a i hbase
  exact cpsTripleWithin_extend_code hmono h

/-! ## K153's ABI frame and entry setup -/

structure Saved where
  ra : Word
  s0 : Word
  s1 : Word
  s2 : Word
  s3 : Word
  s4 : Word
  s5 : Word

def frame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24)]

def savedVals (saved : Saved) : Reg → Word
  | .x1 => saved.ra
  | .x8 => saved.s0
  | .x9 => saved.s1
  | .x18 => saved.s2
  | _ => 0

def savedFrame (newSp : Word) (saved : Saved) : Assertion :=
  (newSp ↦ₘ saved.ra) ** ((newSp + 8) ↦ₘ saved.s0) **
  ((newSp + 16) ↦ₘ saved.s1) ** ((newSp + 24) ↦ₘ saved.s2)

theorem regsAt_frame (saved : Saved) :
    regsAt frame (savedVals saved) =
      ((.x1 ↦ᵣ saved.ra) ** (.x8 ↦ᵣ saved.s0) **
       (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2)) := by
  simp [frame, regsAt, savedVals, sepConj_emp_right']

theorem frameSlotsSaved_frame (newSp : Word) (saved : Saved) :
    frameSlotsSaved frame newSp (savedVals saved) = savedFrame newSp saved := by
  simp [frame, frameSlotsSaved, savedFrame, savedVals, sepConj_emp_right',
    signExtend12]

theorem setupPrologue
    (sp0 newSp : Word) (saved : Saved) (F : Assertion)
    (hnewSp : newSp = sp0 + signExtend12 (-32 : BitVec 12))
    (hF : F.pcFree) :
    cpsTripleWithin 5 B (B + 20) code
      ((.x2 ↦ᵣ sp0) ** regsAt frame (savedVals saved) **
       frameSlotsOwn frame newSp ** F)
      ((.x2 ↦ᵣ newSp) ** regsAt frame (savedVals saved) **
       savedFrame newSp saved ** F) := by
  have ha0 := addi_spec_gen_same_within .x2 sp0 (-32 : BitVec 12) B (by decide)
  rw [← hnewSp] at ha0
  have ha := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B B headerExtractLogsBloom_prog 0
      (.ADDI .x2 .x2 (-32 : BitVec 12)) rfl (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) ha0
  have haF := cpsTripleWithin_frameR
    (regsAt frame (savedVals saved) ** frameSlotsOwn frame newSp ** F)
    (pcFree_sepConj (pcFree_regsAt _ _)
      (pcFree_sepConj (pcFree_frameSlotsOwn _ _) hF)) ha
  have hs0 := storeSeq_spec frame newSp (savedVals saved) (B + 4) (by decide)
  have hstoreMono : ∀ a i,
      CodeReq.ofProg (B + 4) (storeProg frame) a = some i →
        wrapperCode a = some i := by
    intro a i hi
    exact CodeReq.ofProg_mono_sub B (B + 4) headerExtractLogsBloom_prog
      (storeProg frame) 1 (by bv_omega) (by rfl)
      (by rw [program_length]; simp [frame])
      (by rw [program_length]; decide) a i hi
  have hs := cpsTripleWithin_extend_code hstoreMono hs0
  have hflen : 4 * frame.length = 16 := by simp [frame]
  rw [hflen]
    at hs
  rw [show B + 4 + BitVec.ofNat 64 16 = B + 20 by decide] at hs
  rw [frameSlotsSaved_frame] at hs
  have hsF := cpsTripleWithin_frameR F hF hs
  have hlocal := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    haF hsF
  have hlocal''0 : cpsTripleWithin (1 + frame.length) B (B + 20) wrapperCode
      ((.x2 ↦ᵣ sp0) ** regsAt frame (savedVals saved) **
       frameSlotsOwn frame newSp ** F)
      ((.x2 ↦ᵣ newSp) ** regsAt frame (savedVals saved) **
       savedFrame newSp saved ** F) := by
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => by simpa only [sepConj_assoc'] using hq) hlocal
  have hlocal'' : cpsTripleWithin 5 B (B + 20) wrapperCode
      ((.x2 ↦ᵣ sp0) ** regsAt frame (savedVals saved) **
       frameSlotsOwn frame newSp ** F)
      ((.x2 ↦ᵣ newSp) ** regsAt frame (savedVals saved) **
       savedFrame newSp saved ** F) := by
    simpa [frame] using hlocal''0
  exact cpsTripleWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) hlocal''

theorem setupMoves
    (listBase listLen outputPtr old8 old9 old18 : Word) (F : Assertion)
    (hF : F.pcFree) :
    cpsTripleWithin 3 (B + 20) (B + 32) code
      (((regIs .x8 old8) ** (regIs .x9 old9) ** (regIs .x18 old18) **
        (regIs .x10 listBase) ** (regIs .x11 listLen) ** (regIs .x12 outputPtr)) ** F)
      (((regIs .x8 listBase) ** (regIs .x9 listLen) ** (regIs .x18 outputPtr) **
        (regIs .x10 listBase) ** (regIs .x11 listLen) ** (regIs .x12 outputPtr)) ** F) := by
  have h0 := mv_spec_gen_within .x8 .x10 listBase old8 (B + 20) (by decide)
  have h0' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 20) headerExtractLogsBloom_prog 5
      (.MV .x8 .x10) (by bv_omega) (by rw [program_length]; decide) rfl
      (by rw [program_length]; decide)) h0
  have h1 := mv_spec_gen_within .x9 .x11 listLen old9 (B + 24) (by decide)
  have h1' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 24) headerExtractLogsBloom_prog 6
      (.MV .x9 .x11) (by bv_omega) (by rw [program_length]; decide) rfl
      (by rw [program_length]; decide)) h1
  have h2 := mv_spec_gen_within .x18 .x12 outputPtr old18 (B + 28) (by decide)
  have h2' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 28) headerExtractLogsBloom_prog 7
      (.MV .x18 .x12) (by bv_omega) (by rw [program_length]; decide) rfl
      (by rw [program_length]; decide)) h2
  have h0F := cpsTripleWithin_frameR
    ((regIs .x9 old9) ** (regIs .x18 old18) ** (regIs .x11 listLen) **
      (regIs .x12 outputPtr)) (by pcf) h0'
  have h1F := cpsTripleWithin_frameR
    ((regIs .x8 listBase) ** (regIs .x10 listBase) ** (regIs .x18 old18) **
      (regIs .x12 outputPtr)) (by pcf) h1'
  have h2F := cpsTripleWithin_frameR
    ((regIs .x8 listBase) ** (regIs .x9 listLen) ** (regIs .x10 listBase) **
      (regIs .x11 listLen)) (by pcf) h2'
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 h2F
  have hlocal := cpsTripleWithin_weaken
    (P' := (regIs .x8 old8) ** (regIs .x9 old9) ** (regIs .x18 old18) **
      (regIs .x10 listBase) ** (regIs .x11 listLen) ** (regIs .x12 outputPtr))
    (Q' := (regIs .x8 listBase) ** (regIs .x9 listLen) ** (regIs .x18 outputPtr) **
      (regIs .x10 listBase) ** (regIs .x11 listLen) ** (regIs .x12 outputPtr))
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h012
  have hframed := cpsTripleWithin_frameR F hF hlocal
  exact cpsTripleWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) hframed

/-! The K20 call is exposed in the same flat existential shape as the
    reusable list-item caller contracts. -/

def listOtherSaved (saved : RlpListNthItemSAsm.Saved) : Assertion :=
  (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
  (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5)

def listSavedRegs (saved : RlpListNthItemSAsm.Saved) : Assertion :=
  (.x8 ↦ᵣ saved.s0) ** listOtherSaved saved

def listCallRest (sp0 listBase offsetPtr lenPtr : Word)
    (saved : RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (offset len v11 v12 : Word) : Assertion :=
  (.x2 ↦ᵣ sp0) ** listSavedRegs saved ** stackFree sp0 8 **
  (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x11 ↦ᵣ v11) **
   (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
   regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** bytesRegion listBase bytes **
   (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len))

def listCallCore (sp0 listBase offsetPtr lenPtr : Word)
    (saved : RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (status offset len v11 v12 : Word) : Assertion :=
  (.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) **
  listCallRest sp0 listBase offsetPtr lenPtr saved bytes offset len v11 v12

def listCallResult (sp0 listBase offsetPtr lenPtr : Word)
    (saved : RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (oldOffset oldLen : Word) : Assertion :=
  fun h => ∃ status offset len v11 v12,
    (listCallCore sp0 listBase offsetPtr lenPtr saved bytes status offset len v11 v12 **
      ⌜RlpListNthItemSAsm.Result bytes listBase listLen index
        oldOffset oldLen status offset len⌝) h

def listSelected (sp0 listBase offsetPtr lenPtr : Word)
    (saved : RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v11 v12,
    (listCallCore sp0 listBase offsetPtr lenPtr saved bytes 0 offset len v11 v12 **
      ⌜RlpListNthItemSAsm.Success bytes listBase listLen index offset len⌝) h

def listFailed (sp0 listBase offsetPtr lenPtr : Word)
    (saved : RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (oldOffset oldLen : Word) : Assertion :=
  fun h => ∃ v11 v12,
    (listCallCore sp0 listBase offsetPtr lenPtr saved bytes 1 oldOffset oldLen v11 v12 **
      ⌜RlpListNthItemSAsm.Failure bytes listBase listLen index⌝) h

theorem listResult_cases
    {bytes : List (BitVec 8)} {listBase : Word} {listLen index : Nat}
    {oldOffset oldLen status offset len : Word}
    (h : RlpListNthItemSAsm.Result bytes listBase listLen index
      oldOffset oldLen status offset len) :
    (status = 0 ∧ RlpListNthItemSAsm.Success bytes listBase listLen index offset len) ∨
    (status = 1 ∧ offset = oldOffset ∧ len = oldLen ∧
      RlpListNthItemSAsm.Failure bytes listBase listLen index) := by
  cases h with
  | ok offset len h_ok => exact Or.inl ⟨rfl, h_ok⟩
  | fail h_fail => exact Or.inr ⟨rfl, rfl, rfl, h_fail⟩

theorem listCallResult_cases
    (sp0 listBase offsetPtr lenPtr : Word) (saved : RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) (oldOffset oldLen : Word) : ∀ h,
    listCallResult sp0 listBase offsetPtr lenPtr saved bytes listLen index oldOffset oldLen h →
    listSelected sp0 listBase offsetPtr lenPtr saved bytes listLen index h ∨
    listFailed sp0 listBase offsetPtr lenPtr saved bytes listLen index oldOffset oldLen h := by
  intro h hq
  unfold listCallResult at hq
  obtain ⟨status, offset, len, v11, v12, hq⟩ := hq
  extract_pure_deep hq
  obtain ⟨hcore, hresult⟩ := hq
  rcases listResult_cases hresult with ⟨rfl, h_ok⟩ | ⟨rfl, rfl, rfl, h_fail⟩
  · left
    exact ⟨offset, len, v11, v12, (sepConj_pure_right h).2 ⟨hcore, h_ok⟩⟩
  · right
    exact ⟨v11, v12, (sepConj_pure_right h).2 ⟨hcore, h_fail⟩⟩

theorem pcFree_listCallRest (sp0 listBase offsetPtr lenPtr : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (offset len v11 v12 : Word) :
    (listCallRest sp0 listBase offsetPtr lenPtr saved bytes offset len v11 v12).pcFree := by
  unfold listCallRest listSavedRegs listOtherSaved
  pcf

theorem listCalleeCallContract
    (sp0 listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (listLen index : Nat)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64) (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hret : saved.ra &&& ~~~(1 : Word) = saved.ra) :
    cpsTripleWithin
      ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)
      K20B saved.ra code
      ((.x1 ↦ᵣ saved.ra) **
       ((.x2 ↦ᵣ sp0) ** listSavedRegs saved ** stackFree sp0 8 **
        RlpListNthItemSAsm.entryRest listBase listLenW indexW
          offsetPtr lenPtr oldOffset oldLen bytes))
      ((.x1 ↦ᵣ saved.ra) **
       listCallResult sp0 listBase offsetPtr lenPtr saved bytes listLen index
         oldOffset oldLen) := by
  have hflat := RlpListNthItemSAsm.rlpListNthItem_flat_spec_within
    sp0 listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen saved bytes
    listLen index hlistLenW hindexW hindex hsalign hslack hover hvalid hret
  have hcode := cpsTripleWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.mono_union_right wrapper_list_disjoint (fun _ _ h => h) a i hi) hflat
  rw [RlpListNthItemSAsm.regsAt_listNthFrame] at hcode
  refine cpsTripleWithin_weaken
    (P' := ((.x1 ↦ᵣ saved.ra) **
      ((.x2 ↦ᵣ sp0) ** listSavedRegs saved ** stackFree sp0 8 **
       RlpListNthItemSAsm.entryRest listBase listLenW indexW
         offsetPtr lenPtr oldOffset oldLen bytes)))
    (Q' := ((.x1 ↦ᵣ saved.ra) **
      listCallResult sp0 listBase offsetPtr lenPtr saved bytes listLen index
        oldOffset oldLen))
    (fun h hp => by
    unfold listSavedRegs listOtherSaved at hp
    xperm_hyp hp) (fun h hq => ?_) hcode
  unfold RlpListNthItemSAsm.flatReturnResult at hq
  obtain ⟨status, offset, len, v11, v12, hq⟩ := hq
  have hfixed : ((.x1 ↦ᵣ saved.ra) **
      (listCallCore sp0 listBase offsetPtr lenPtr saved bytes
        status offset len v11 v12 **
       ⌜RlpListNthItemSAsm.Result bytes listBase listLen index
         oldOffset oldLen status offset len⌝)) h := by
    rw [RlpListNthItemSAsm.regsAt_listNthFrame] at hq
    unfold listCallCore listCallRest listSavedRegs listOtherSaved
    xperm_hyp hq
  obtain ⟨hRa, hRest, hd, hu, hra, hrest⟩ := hfixed
  refine ⟨hRa, hRest, hd, hu, hra, ?_⟩
  unfold listCallResult
  exact ⟨status, offset, len, v11, v12, hrest⟩

theorem callListNth
    (sp0 listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen vOld : Word)
    (s0 s1 s2 s3 s4 s5 : Word) (bytes : List (BitVec 8))
    (listLen index : Nat)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64) (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let saved : RlpListNthItemSAsm.Saved :=
      { ra := B + 64, s0 := s0, s1 := s1, s2 := s2, s3 := s3,
        s4 := s4, s5 := s5 }
    cpsTripleWithin
      (1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9))
      (B + 60) (B + 64) code
      ((.x1 ↦ᵣ vOld) **
       ((.x2 ↦ᵣ sp0) ** listSavedRegs saved ** stackFree sp0 8 **
        RlpListNthItemSAsm.entryRest listBase listLenW indexW
          offsetPtr lenPtr oldOffset oldLen bytes))
      ((.x1 ↦ᵣ (B + 64)) **
       listCallResult sp0 listBase offsetPtr lenPtr saved bytes listLen index
         oldOffset oldLen) := by
  dsimp
  let saved : RlpListNthItemSAsm.Saved :=
    { ra := B + 64, s0 := s0, s1 := s1, s2 := s2, s3 := s3,
      s4 := s4, s5 := s5 }
  have hret : saved.ra &&& ~~~(1 : Word) = saved.ra := by
    dsimp [saved, B]
    decide
  have hcallee := listCalleeCallContract sp0 listBase listLenW indexW offsetPtr
    lenPtr oldOffset oldLen saved bytes listLen index hlistLenW hindexW hindex
    hsalign hslack hover hvalid hret
  have htarget : (B + 60) + signExtend21
      (jalOff GuestAddrs.rlp_list_nth_item
        (GuestAddrs.header_extract_logs_bloom + 60)) = K20B := by
    unfold B K20B
    decide
  have hmem : ∀ a i, CodeReq.singleton (B + 60)
      (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item
        (GuestAddrs.header_extract_logs_bloom + 60))) a = some i →
      code a = some i := by
    intro a i hi
    unfold code
    apply CodeReq.union_mono_left
    exact CodeReq.ofProg_mem_at B (B + 60) headerExtractLogsBloom_prog 15
      (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item
        (GuestAddrs.header_extract_logs_bloom + 60))) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide) a i hi
  have hcall := callWithin_spec (B + 60) K20B vOld
    (jalOff GuestAddrs.rlp_list_nth_item
      (GuestAddrs.header_extract_logs_bloom + 60))
    ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)
    htarget hmem (by
      unfold listSavedRegs listOtherSaved
      pcf) hcallee
  dsimp [saved] at hcall
  exact hcall

theorem branchSelected
    (sp0 listBase offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (listLen index : Nat) :
    cpsBranchWithin 1 (B + 64) code
      (listSelected sp0 listBase offsetPtr lenPtr saved bytes listLen index)
      (B + 148)
        (listFailed sp0 listBase offsetPtr lenPtr saved bytes listLen index
          oldOffset oldLen)
      (B + 68)
        (listSelected sp0 listBase offsetPtr lenPtr saved bytes listLen index) := by
  unfold listSelected
  refine cpsBranchWithin_exists_pre (fun offset => ?_)
  refine cpsBranchWithin_exists_pre (fun len => ?_)
  refine cpsBranchWithin_exists_pre (fun v11 => ?_)
  refine cpsBranchWithin_exists_pre (fun v12 => ?_)
  refine cpsBranchWithin_pure_pre_right (fun h_ok => ?_)
  have hb0 := bne_spec_gen_within .x10 .x0 (84 : BitVec 13)
    (0 : Word) (0 : Word) (B + 64)
  rw [show B + 64 + signExtend13 (84 : BitVec 13) = B + 148 from by decide,
    show B + 64 + 4 = B + 68 from by bv_omega] at hb0
  have hb1 := cpsBranchWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 64) headerExtractLogsBloom_prog 16
      (.BNE .x10 .x0 (84 : BitVec 13)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hb0
  let R : Assertion :=
    listCallRest sp0 listBase offsetPtr lenPtr saved bytes offset len v11 v12 **
    ⌜RlpListNthItemSAsm.Success bytes listBase listLen index offset len⌝
  have hbF := cpsBranchWithin_frameR R
    (pcFree_sepConj (pcFree_listCallRest _ _ _ _ _ _ _ _ _ _)
      (by pcf)) hb1
  have hbC := cpsBranchWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) hbF
  refine cpsBranchWithin_weaken (fun h hp => by
      unfold listCallCore at hp
      unfold R
      xperm_pure hp) (fun h hp => by
      extract_pure_deep hp
      obtain ⟨h_ne, -⟩ := hp
      exact False.elim (h_ne rfl)) (fun h hp => ?_) hbC
  extract_pure_deep hp
  obtain ⟨-, hstate⟩ := hp
  refine ⟨offset, len, v11, v12, ?_⟩
  unfold R at hstate
  unfold listCallCore
  xperm_pure hstate

theorem branchFailed
    (sp0 listBase offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (listLen index : Nat) :
    cpsBranchWithin 1 (B + 64) code
      (listFailed sp0 listBase offsetPtr lenPtr saved bytes listLen index
        oldOffset oldLen)
      (B + 148)
        (listFailed sp0 listBase offsetPtr lenPtr saved bytes listLen index
          oldOffset oldLen)
      (B + 68)
        (listSelected sp0 listBase offsetPtr lenPtr saved bytes listLen index) := by
  unfold listFailed
  refine cpsBranchWithin_exists_pre (fun v11 => ?_)
  refine cpsBranchWithin_exists_pre (fun v12 => ?_)
  refine cpsBranchWithin_pure_pre_right (fun h_fail => ?_)
  have hb0 := bne_spec_gen_within .x10 .x0 (84 : BitVec 13)
    (1 : Word) (0 : Word) (B + 64)
  rw [show B + 64 + signExtend13 (84 : BitVec 13) = B + 148 from by decide,
    show B + 64 + 4 = B + 68 from by bv_omega] at hb0
  have hb1 := cpsBranchWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 64) headerExtractLogsBloom_prog 16
      (.BNE .x10 .x0 (84 : BitVec 13)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hb0
  let R : Assertion :=
    listCallRest sp0 listBase offsetPtr lenPtr saved bytes oldOffset oldLen v11 v12 **
    ⌜RlpListNthItemSAsm.Failure bytes listBase listLen index⌝
  have hbF := cpsBranchWithin_frameR R
    (pcFree_sepConj (pcFree_listCallRest _ _ _ _ _ _ _ _ _ _)
      (by pcf)) hb1
  have hbC := cpsBranchWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) hbF
  refine cpsBranchWithin_weaken (fun h hp => by
      unfold listCallCore at hp
      unfold R
      xperm_pure hp) (fun h hp => ?_) (fun h hp => by
      extract_pure_deep hp
      obtain ⟨h_eq, -⟩ := hp
      have h_ne : (1 : Word) ≠ 0 := by decide
      exact False.elim (h_ne h_eq)) hbC
  extract_pure_deep hp
  obtain ⟨-, hstate⟩ := hp
  refine ⟨v11, v12, ?_⟩
  unfold R at hstate
  unfold listCallCore
  xperm_pure hstate

theorem listResultBranch
    (sp0 listBase offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (listLen index : Nat) :
    cpsBranchWithin 1 (B + 64) code
      (listCallResult sp0 listBase offsetPtr lenPtr saved bytes listLen index
        oldOffset oldLen)
      (B + 148)
        (listFailed sp0 listBase offsetPtr lenPtr saved bytes listLen index
          oldOffset oldLen)
      (B + 68)
        (listSelected sp0 listBase offsetPtr lenPtr saved bytes listLen index) := by
  have hs := branchSelected sp0 listBase offsetPtr lenPtr oldOffset oldLen saved
    bytes listLen index
  have hf := branchFailed sp0 listBase offsetPtr lenPtr oldOffset oldLen saved
    bytes listLen index
  have hor := cpsBranchWithin_pre_or hs hf
  exact cpsBranchWithin_weaken
    (fun h hp => listCallResult_cases sp0 listBase offsetPtr lenPtr saved
      bytes listLen index oldOffset oldLen h hp)
    (fun _ hq => hq) (fun _ hq => hq) hor

theorem setupArgs
    (listBase listLen outputPtr : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 3 (B + 32) (B + 44) code
      (((regIs .x8 listBase) ** (regIs .x9 listLen) **
        (regIs .x18 outputPtr) ** (regIs .x10 listBase) **
        (regIs .x11 listLen) ** (regIs .x12 outputPtr)) ** F)
      (((regIs .x8 listBase) ** (regIs .x9 listLen) **
        (regIs .x18 outputPtr) ** (regIs .x10 listBase) **
        (regIs .x11 listLen) ** (regIs .x12 (6 : Word))) ** F) := by
  have h0 := mv_spec_gen_within .x10 .x8 listBase listBase (B + 32) (by decide)
  have h0' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 32) headerExtractLogsBloom_prog 8
      (.MV .x10 .x8) (by bv_omega) (by rw [program_length]; decide) rfl
      (by rw [program_length]; decide)) h0
  have h1 := mv_spec_gen_within .x11 .x9 listLen listLen (B + 36) (by decide)
  have h1' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 36) headerExtractLogsBloom_prog 9
      (.MV .x11 .x9) (by bv_omega) (by rw [program_length]; decide) rfl
      (by rw [program_length]; decide)) h1
  have h2 := li_spec_gen_within .x12 outputPtr (6 : Word) (B + 40) (by decide)
  have h2' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 40) headerExtractLogsBloom_prog 10
      (.LI .x12 6) (by bv_omega) (by rw [program_length]; decide) rfl
      (by rw [program_length]; decide)) h2
  have h0F := cpsTripleWithin_frameR
    ((regIs .x9 listLen) ** (regIs .x18 outputPtr) **
      (regIs .x11 listLen) ** (regIs .x12 outputPtr)) (by pcf) h0'
  have h1F := cpsTripleWithin_frameR
    ((regIs .x8 listBase) ** (regIs .x18 outputPtr) **
      (regIs .x10 listBase) ** (regIs .x12 outputPtr)) (by pcf) h1'
  have h2F := cpsTripleWithin_frameR
    ((regIs .x8 listBase) ** (regIs .x9 listLen) **
      (regIs .x18 outputPtr) ** (regIs .x10 listBase) **
      (regIs .x11 listLen)) (by pcf) h2'
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 h2F
  have hlocal := cpsTripleWithin_weaken
    (P' := (regIs .x8 listBase) ** (regIs .x9 listLen) **
      (regIs .x18 outputPtr) ** (regIs .x10 listBase) **
      (regIs .x11 listLen) ** (regIs .x12 outputPtr))
    (Q' := (regIs .x8 listBase) ** (regIs .x9 listLen) **
      (regIs .x18 outputPtr) ** (regIs .x10 listBase) **
      (regIs .x11 listLen) ** (regIs .x12 (6 : Word)))
    (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) h012
  have hframed := cpsTripleWithin_frameR F hF hlocal
  exact cpsTripleWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) hframed

theorem setupGlobals
    (old13 old14 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (B + 44) (B + 60) code
      (((regIs .x13 old13) ** (regIs .x14 old14)) ** F)
      (((regIs .x13 offsetCell) ** (regIs .x14 lengthCell)) ** F) := by
  have hau0 := CodeReq.ofProg_mem_at B (B + 44) headerExtractLogsBloom_prog 11
    (.AUIPC .x13 (laHi GuestAddrs.helb_offset
      (GuestAddrs.header_extract_logs_bloom + 44)))
    (by bv_omega) (by rw [program_length]; decide) rfl
    (by rw [program_length]; decide)
  have had0 := CodeReq.ofProg_mem_at B (B + 48) headerExtractLogsBloom_prog 12
    (.ADDI .x13 .x13 (laLo GuestAddrs.helb_offset
      (GuestAddrs.header_extract_logs_bloom + 44)))
    (by bv_omega) (by rw [program_length]; decide) rfl
    (by rw [program_length]; decide)
  have ho := la_materialize_within .x13 old13 (B + 44) offsetCell
    (by decide) (by unfold B offsetCell; decide) hau0 had0
  have hau1 := CodeReq.ofProg_mem_at B (B + 52) headerExtractLogsBloom_prog 13
    (.AUIPC .x14 (laHi GuestAddrs.helb_length
      (GuestAddrs.header_extract_logs_bloom + 52)))
    (by bv_omega) (by rw [program_length]; decide) rfl
    (by rw [program_length]; decide)
  have had1 := CodeReq.ofProg_mem_at B (B + 56) headerExtractLogsBloom_prog 14
    (.ADDI .x14 .x14 (laLo GuestAddrs.helb_length
      (GuestAddrs.header_extract_logs_bloom + 52)))
    (by bv_omega) (by rw [program_length]; decide) rfl
    (by rw [program_length]; decide)
  have hl := la_materialize_within .x14 old14 (B + 52) lengthCell
    (by decide) (by unfold B lengthCell; decide) hau1 had1
  have hoF := cpsTripleWithin_frameR (regIs .x14 old14) (by pcf) ho
  have hlF := cpsTripleWithin_frameR (regIs .x13 offsetCell) (by pcf) hl
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hoF hlF
  have hlocal := cpsTripleWithin_weaken
    (P' := (regIs .x13 old13) ** (regIs .x14 old14))
    (Q' := (regIs .x13 offsetCell) ** (regIs .x14 lengthCell))
    (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hseq
  have hsF := cpsTripleWithin_frameR F hF hlocal
  exact cpsTripleWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) hsF

theorem selectedLengthExact
    (len old5 old6 old7 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (B + 68) (B + 84) code
      (((regIs .x5 old5) ** (regIs .x6 old6) ** (regIs .x7 old7) **
        (lengthCell ↦ₘ len)) ** F)
      (((regIs .x5 lengthCell) ** (regIs .x6 len) **
        (regIs .x7 (256 : Word)) ** (lengthCell ↦ₘ len)) ** F) := by
  have hau := CodeReq.ofProg_mem_at B (B + 68) headerExtractLogsBloom_prog 17
    (.AUIPC .x5 (laHi GuestAddrs.helb_length
      (GuestAddrs.header_extract_logs_bloom + 68))) (by bv_omega)
    (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have had := CodeReq.ofProg_mem_at B (B + 72) headerExtractLogsBloom_prog 18
    (.ADDI .x5 .x5 (laLo GuestAddrs.helb_length
      (GuestAddrs.header_extract_logs_bloom + 68))) (by bv_omega)
    (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have h0 := la_materialize_within .x5 old5 (B + 68) lengthCell
    (by decide) (by unfold B lengthCell; decide) hau had
  have h1 := ld_spec_gen_within .x6 .x5 lengthCell old6 len
    (0 : BitVec 12) (B + 76) (by decide)
  rw [show lengthCell + signExtend12 (0 : BitVec 12) = lengthCell from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h1
  have h1' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 76) headerExtractLogsBloom_prog 19
      (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) h1
  have h2 := li_spec_gen_within .x7 old7 (256 : Word) (B + 80) (by decide)
  have h2' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 80) headerExtractLogsBloom_prog 20
      (.LI .x7 (256 : Word)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) h2
  have h0F := cpsTripleWithin_frameR
    ((regIs .x6 old6) ** (regIs .x7 old7) ** (lengthCell ↦ₘ len)) (by pcf) h0
  have h1F := cpsTripleWithin_frameR (regIs .x7 old7) (by pcf) h1'
  have h2F := cpsTripleWithin_frameR
    ((regIs .x5 lengthCell) ** (regIs .x6 len) ** (lengthCell ↦ₘ len))
    (by pcf) h2'
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have hs := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 h2F
  have hs' := cpsTripleWithin_weaken
    (P' := (regIs .x5 old5) ** (regIs .x6 old6) ** (regIs .x7 old7) **
      (lengthCell ↦ₘ len))
    (Q' := (regIs .x5 lengthCell) ** (regIs .x6 len) **
      (regIs .x7 (256 : Word)) ** (lengthCell ↦ₘ len))
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hs
  exact cpsTripleWithin_frameR F hF
    (cpsTripleWithin_extend_code (cr' := code) (fun a i hi => by
      unfold code
      exact CodeReq.union_mono_left a i hi) hs')

def selectedPathCarry (sp0 listBase : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (v11 v12 : Word) : Assertion :=
  (.x2 ↦ᵣ sp0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) **
  (.x19 ↦ᵣ saved.s3) ** (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) **
  stackFree sp0 8 ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) **
  (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x30 **
  regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes

theorem pcFree_selectedPathCarry (sp0 listBase : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (v11 v12 : Word) :
    (selectedPathCarry sp0 listBase saved bytes v11 v12).pcFree := by
  unfold selectedPathCarry
  pcf

def lengthReady (sp0 listBase : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v11 v12,
    (((((.x5 ↦ᵣ lengthCell) ** (.x6 ↦ᵣ len) **
       (.x7 ↦ᵣ (256 : Word)) ** (regIs .x8 listBase) ** regOwn .x28 **
       regOwn .x29 ** (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len)) **
      selectedPathCarry sp0 listBase saved bytes v11 v12) **
     ⌜RlpListNthItemSAsm.Success bytes listBase listLen index offset len⌝)) h

theorem selectedLength
    (sp0 listBase : Word) (saved : RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (hs0 : saved.s0 = listBase) :
    cpsTripleWithin 4 (B + 68) (B + 84) code
      (listSelected sp0 listBase offsetCell lengthCell saved bytes listLen index)
      (lengthReady sp0 listBase saved bytes listLen index) := by
  unfold listSelected
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun offset => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun len => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v11 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v12 => ?_)
  refine cpsTripleWithin_weaken (fun h hp => by xperm_pure hp)
    (fun _ hp => hp) (cpsTripleWithin_pure_pre
      (P := RlpListNthItemSAsm.Success bytes listBase listLen index offset len)
      (H := listCallCore sp0 listBase offsetCell lengthCell saved bytes 0
        offset len v11 v12) (fun h_ok => ?_))
  let R0 : Assertion :=
    ((regIs .x8 listBase) ** regOwn .x28 ** regOwn .x29 **
      (offsetCell ↦ₘ offset)) **
    selectedPathCarry sp0 listBase saved bytes v11 v12 **
    ⌜RlpListNthItemSAsm.Success bytes listBase listLen index offset len⌝
  let R : Assertion := (lengthCell ↦ₘ len) ** R0
  have h7 (old5 old6 : Word) :=
    cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7)
      (P := (R ** (regIs .x5 old5)) ** (regIs .x6 old6))
      (Q := lengthReady sp0 listBase saved bytes listLen index)
      (fun old7 => by
        have hs := selectedLengthExact len old5 old6 old7 R0 (by
          unfold R0 selectedPathCarry
          pcf)
        refine cpsTripleWithin_weaken (fun h hp => by
            unfold R R0 at hp
            xperm_hyp hp) (fun h hq => ?_) hs
        unfold lengthReady
        refine ⟨offset, len, v11, v12, ?_⟩
        unfold R0 at hq
        xperm_hyp hq)
  have h6 (old5 : Word) :=
    cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
      (P := (R ** regOwn .x7) ** (regIs .x5 old5))
      (Q := lengthReady sp0 listBase saved bytes listLen index)
      (fun old6 => cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun _ hp => hp) (h7 old5 old6))
  have howned := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
    (P := (R ** regOwn .x6) ** regOwn .x7)
    (Q := lengthReady sp0 listBase saved bytes listLen index)
    (fun old5 => cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ hp => hp) (h6 old5))
  refine cpsTripleWithin_weaken
    (P' := listCallCore sp0 listBase offsetCell lengthCell saved bytes 0
      offset len v11 v12)
    (Q' := lengthReady sp0 listBase saved bytes listLen index)
    (fun h hp => by
      unfold listCallCore listCallRest listSavedRegs listOtherSaved at hp
      unfold R R0 selectedPathCarry
      rw [hs0] at hp
      xperm_pure hp) (fun _ hp => hp) howned

def lengthRest (sp0 listBase offset len : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (listLen index : Nat) (v11 v12 : Word) : Assertion :=
  (regIs .x5 lengthCell) ** (regIs .x8 listBase) ** regOwn .x28 **
  regOwn .x29 ** (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) **
  selectedPathCarry sp0 listBase saved bytes v11 v12 **
  ⌜RlpListNthItemSAsm.Success bytes listBase listLen index offset len⌝

theorem pcFree_lengthRest (sp0 listBase offset len : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (listLen index : Nat) (v11 v12 : Word) :
    (lengthRest sp0 listBase offset len saved bytes listLen index v11 v12).pcFree := by
  unfold lengthRest
  pcf

def lengthTooLong (sp0 listBase : Word) (saved : RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v11 v12,
    (((regIs .x6 len) ** (regIs .x7 (256 : Word)) **
      lengthRest sp0 listBase offset len saved bytes listLen index v11 v12) **
      ⌜len ≠ (256 : Word)⌝) h

def lengthFits (sp0 listBase : Word) (saved : RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v11 v12,
    (((regIs .x6 len) ** (regIs .x7 (256 : Word)) **
      lengthRest sp0 listBase offset len saved bytes listLen index v11 v12) **
      ⌜len = (256 : Word)⌝) h

private theorem lengthBranchCase
    (sp0 listBase offset len v11 v12 : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (listLen index : Nat) :
    cpsBranchWithin 1 (B + 84) code
      ((regIs .x6 len) ** (regIs .x7 (256 : Word)) **
        lengthRest sp0 listBase offset len saved bytes listLen index v11 v12)
      (B + 156) (lengthTooLong sp0 listBase saved bytes listLen index)
      (B + 88) (lengthFits sp0 listBase saved bytes listLen index) := by
  have hb0 := bne_spec_gen_within .x6 .x7 (72 : BitVec 13)
    len (256 : Word) (B + 84)
  rw [show B + 84 + signExtend13 (72 : BitVec 13) = B + 156 from by decide,
    show B + 84 + 4 = B + 88 from by bv_omega] at hb0
  have hb1 := cpsBranchWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 84) headerExtractLogsBloom_prog 21
      (.BNE .x6 .x7 (72 : BitVec 13)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hb0
  let R : Assertion := lengthRest sp0 listBase offset len saved bytes listLen index v11 v12
  have hbF := cpsBranchWithin_frameR R
    (pcFree_lengthRest _ _ _ _ _ _ _ _ _ _ ) hb1
  have hbC := cpsBranchWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) hbF
  refine cpsBranchWithin_weaken (fun _ hp => by
      unfold R
      xperm_hyp hp) (fun h hp => ?_) (fun h hp => ?_) hbC
  · extract_pure_deep hp
    obtain ⟨h_ne, hp⟩ := hp
    unfold lengthTooLong
    refine ⟨offset, len, v11, v12, ?_⟩
    apply (sepConj_pure_right h).2
    exact ⟨(by unfold R at hp; xperm_hyp hp), h_ne⟩
  · extract_pure_deep hp
    obtain ⟨h_eq, hp⟩ := hp
    unfold lengthFits
    refine ⟨offset, len, v11, v12, ?_⟩
    apply (sepConj_pure_right h).2
    exact ⟨(by unfold R at hp; xperm_hyp hp), h_eq⟩

theorem lengthBranch
    (sp0 listBase : Word) (saved : RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsBranchWithin 1 (B + 84) code
      (lengthReady sp0 listBase saved bytes listLen index)
      (B + 156) (lengthTooLong sp0 listBase saved bytes listLen index)
      (B + 88) (lengthFits sp0 listBase saved bytes listLen index) := by
  unfold lengthReady
  refine cpsBranchWithin_exists_pre (fun offset => ?_)
  refine cpsBranchWithin_exists_pre (fun len => ?_)
  refine cpsBranchWithin_exists_pre (fun v11 => ?_)
  refine cpsBranchWithin_exists_pre (fun v12 => ?_)
  exact cpsBranchWithin_weaken (fun _ hp => by
      unfold lengthRest
      xperm_hyp hp) (fun _ hp => hp) (fun _ hp => hp)
    (lengthBranchCase sp0 listBase offset len v11 v12 saved bytes listLen index)

theorem cursorSetupExact
    (listBase outputPtr offset old6 old5 old28 old29 old30 : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 6 (B + 88) (B + 112) code
      (((regIs .x5 old5) ** (regIs .x6 old6) ** (regIs .x7 (256 : Word)) **
        (regIs .x8 listBase) ** (regIs .x18 outputPtr) **
        (regIs .x28 old28) ** (regIs .x29 old29) ** (regIs .x30 old30) **
        (offsetCell ↦ₘ offset)) ** F)
      (((regIs .x5 offsetCell) ** (regIs .x6 offset) **
        (regIs .x7 (256 : Word)) ** (regIs .x8 listBase) **
        (regIs .x18 outputPtr) **
        (regIs .x28 (listBase + offset)) ** (regIs .x29 outputPtr) **
        (regIs .x30 (32 : Word)) ** (offsetCell ↦ₘ offset)) ** F) := by
  have hau := CodeReq.ofProg_mem_at B (B + 88) headerExtractLogsBloom_prog 22
    (.AUIPC .x5 (laHi GuestAddrs.helb_offset
      (GuestAddrs.header_extract_logs_bloom + 88))) (by bv_omega)
    (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have had := CodeReq.ofProg_mem_at B (B + 92) headerExtractLogsBloom_prog 23
    (.ADDI .x5 .x5 (laLo GuestAddrs.helb_offset
      (GuestAddrs.header_extract_logs_bloom + 88))) (by bv_omega)
    (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have h0 := la_materialize_within .x5 old5 (B + 88) offsetCell
    (by decide) (by unfold B offsetCell; decide) hau had
  have h1 := ld_spec_gen_within .x6 .x5 offsetCell old6 offset
    (0 : BitVec 12) (B + 96) (by decide)
  rw [show offsetCell + signExtend12 (0 : BitVec 12) = offsetCell from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h1
  have h1' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 96) headerExtractLogsBloom_prog 24
      (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) h1
  have h2 := add_spec_gen_within .x28 .x8 .x6 listBase offset old28
    (B + 100) (by decide)
  have h2' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 100) headerExtractLogsBloom_prog 25
      (.ADD .x28 .x8 .x6) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) h2
  have h3 := mv_spec_gen_within .x29 .x18 outputPtr old29 (B + 104) (by decide)
  have h3' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 104) headerExtractLogsBloom_prog 26
      (.MV .x29 .x18) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) h3
  have h4 := li_spec_gen_within .x30 old30 (32 : Word) (B + 108) (by decide)
  have h4' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 108) headerExtractLogsBloom_prog 27
      (.LI .x30 32) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) h4
  have h0F := cpsTripleWithin_frameR
    ((regIs .x6 old6) ** (regIs .x7 (256 : Word)) **
      (regIs .x8 listBase) ** (regIs .x18 outputPtr) ** (regIs .x28 old28) **
      (regIs .x29 old29) ** (regIs .x30 old30) ** (offsetCell ↦ₘ offset))
    (by pcf) h0
  have h1F := cpsTripleWithin_frameR
    ((regIs .x7 (256 : Word)) **
      (regIs .x8 listBase) ** (regIs .x18 outputPtr) ** (regIs .x28 old28) **
      (regIs .x29 old29) ** (regIs .x30 old30))
    (by pcf) h1'
  have h2F := cpsTripleWithin_frameR
    ((regIs .x5 offsetCell) ** (regIs .x7 (256 : Word)) **
      (regIs .x18 outputPtr) ** (regIs .x29 old29) ** (regIs .x30 old30) **
      (offsetCell ↦ₘ offset))
    (by pcf) h2'
  have h3F := cpsTripleWithin_frameR
    ((regIs .x5 offsetCell) ** (regIs .x6 offset) ** (regIs .x7 (256 : Word)) **
      (regIs .x8 listBase) ** (regIs .x28 (listBase + offset)) **
      (regIs .x30 old30) ** (offsetCell ↦ₘ offset)) (by pcf) h3'
  have h4F := cpsTripleWithin_frameR
    ((regIs .x5 offsetCell) ** (regIs .x6 offset) ** (regIs .x7 (256 : Word)) **
      (regIs .x8 listBase) ** (regIs .x18 outputPtr) **
      (regIs .x28 (listBase + offset)) ** (regIs .x29 outputPtr) **
      (offsetCell ↦ₘ offset)) (by pcf) h4'
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 h2F
  have h0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h012 h3F
  have hs := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0123 h4F
  have hs' := cpsTripleWithin_weaken
    (P' := (regIs .x5 old5) ** (regIs .x6 old6) ** (regIs .x7 (256 : Word)) **
      (regIs .x8 listBase) ** (regIs .x18 outputPtr) ** (regIs .x28 old28) **
      (regIs .x29 old29) ** (regIs .x30 old30) ** (offsetCell ↦ₘ offset))
    (Q' := (regIs .x5 offsetCell) ** (regIs .x6 offset) **
      (regIs .x7 (256 : Word)) ** (regIs .x8 listBase) **
      (regIs .x18 outputPtr) ** (regIs .x28 (listBase + offset)) **
      (regIs .x29 outputPtr) ** (regIs .x30 (32 : Word)) **
      (offsetCell ↦ₘ offset))
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hs
  exact cpsTripleWithin_frameR F hF
    (cpsTripleWithin_extend_code (cr' := code) (fun a i hi => by
      unfold code
      exact CodeReq.union_mono_left a i hi) hs')

end EvmAsm.Codegen.HeaderExtractLogsBloomSAsm
