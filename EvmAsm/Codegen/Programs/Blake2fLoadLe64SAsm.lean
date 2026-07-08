import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Blake2f

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace Blake2fLoadLe64SAsm

def leByte (bytes : List (BitVec 8)) (i : Nat) : Word :=
  (bytes.getD i 0).zeroExtend 64

def leU64 (bytes : List (BitVec 8)) : Word :=
  let a1 := leByte bytes 7
  let a2 := (a1 <<< 8) ||| leByte bytes 6
  let a3 := (a2 <<< 8) ||| leByte bytes 5
  let a4 := (a3 <<< 8) ||| leByte bytes 4
  let a5 := (a4 <<< 8) ||| leByte bytes 3
  let a6 := (a5 <<< 8) ||| leByte bytes 2
  let a7 := (a6 <<< 8) ||| leByte bytes 1
  (a7 <<< 8) ||| leByte bytes 0

/-- Accumulator value after `i` descending byte-load iterations. -/
def loadAccum (bytes : List (BitVec 8)) : Nat → Word
  | 0 => 0
  | 1 => leByte bytes 7
  | 2 => (leByte bytes 7 <<< 8) ||| leByte bytes 6
  | 3 => ((leByte bytes 7 <<< 8) ||| leByte bytes 6) <<< 8 ||| leByte bytes 5
  | 4 => (((leByte bytes 7 <<< 8) ||| leByte bytes 6) <<< 8 ||| leByte bytes 5) <<< 8 ||| leByte bytes 4
  | 5 => ((((leByte bytes 7 <<< 8) ||| leByte bytes 6) <<< 8 ||| leByte bytes 5) <<< 8 ||| leByte bytes 4) <<< 8 ||| leByte bytes 3
  | 6 => (((((leByte bytes 7 <<< 8) ||| leByte bytes 6) <<< 8 ||| leByte bytes 5) <<< 8 ||| leByte bytes 4) <<< 8 ||| leByte bytes 3) <<< 8 ||| leByte bytes 2
  | 7 => ((((((leByte bytes 7 <<< 8) ||| leByte bytes 6) <<< 8 ||| leByte bytes 5) <<< 8 ||| leByte bytes 4) <<< 8 ||| leByte bytes 3) <<< 8 ||| leByte bytes 2) <<< 8 ||| leByte bytes 1
  | _ => leU64 bytes

theorem loadAccum_zero (bytes : List (BitVec 8)) : loadAccum bytes 0 = 0 := rfl

theorem loadAccum_8_eq (bytes : List (BitVec 8)) : loadAccum bytes 8 = leU64 bytes := rfl

/-- Value carried in `x6` after the `(i+1)`th loop iteration. -/
def loadX6Offset : Nat → Word
  | 0 => 6
  | 1 => 5
  | 2 => 4
  | 3 => 3
  | 4 => 2
  | 5 => 1
  | 6 => 0
  | _ => -1

theorem loadX6Offset_load_addr (i : Nat) (h_i : i + 1 < 8) :
    loadX6Offset i = BitVec.ofNat 64 (7 - (i + 1)) := by
  have h_lt : i < 7 := by omega
  interval_cases i <;> rfl

theorem loadX6Offset_next (i : Nat) (h_i : i + 1 < 8) :
    loadX6Offset i + signExtend12 (-1 : BitVec 12) = loadX6Offset (i + 1) := by
  have h_lt : i < 7 := by omega
  interval_cases i <;> decide

theorem loadX6Offset_next_with_src (src : Word) (i : Nat) (h_i : i + 1 < 8) :
    src + loadX6Offset i + signExtend12 (-1 : BitVec 12) =
      src + loadX6Offset (i + 1) := by
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
  have h_lt : i < 7 := by omega
  interval_cases i <;> simp [loadX6Offset] <;> bv_omega

private theorem shift_or_byte_step (bytes : List (BitVec 8)) (i : Nat) (h_i : i < 8) :
    (loadAccum bytes i <<< 8) ||| (bytes.getD (7 - i) 0).zeroExtend 64 =
      loadAccum bytes (i + 1) := by
  interval_cases i <;> simp [loadAccum, leU64, leByte]

def loadStepBlock : List Instr :=
  [.SLLI .x5 .x5 (8 : BitVec 6),
   .LBU .x10 .x6 (0 : BitVec 12),
   .OR .x5 .x5 .x10,
   .ADDI .x6 .x6 (-1 : BitVec 12),
   .ADDI .x7 .x7 (-1 : BitVec 12)]

def loadStepRf (rf : RegFile) (b : BitVec 8) : RegFile :=
  let r1 := rf.set .x5 (rf.get .x5 <<< (8 : BitVec 6).toNat)
  let r2 := r1.set .x10 (b.zeroExtend 64 : Word)
  let r3 := r2.set .x5 (r2.get .x5 ||| r2.get .x10)
  let r4 := r3.set .x6 (r3.get .x6 + signExtend12 (-1 : BitVec 12))
  r4.set .x7 (r4.get .x7 + signExtend12 (-1 : BitVec 12))

theorem loadStepRf_get_x5 (rf : RegFile) (b : BitVec 8) :
    (loadStepRf rf b).get .x5 = (rf.get .x5 <<< 8) ||| (b.zeroExtend 64 : Word) := by
  unfold loadStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]
  rw [show (8 : BitVec 6).toNat = 8 from by decide]

theorem loadStepRf_get_x6 (rf : RegFile) (b : BitVec 8) :
    (loadStepRf rf b).get .x6 = rf.get .x6 + signExtend12 (-1 : BitVec 12) := by
  unfold loadStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem loadStepRf_get_x7 (rf : RegFile) (b : BitVec 8) :
    (loadStepRf rf b).get .x7 = rf.get .x7 + signExtend12 (-1 : BitVec 12) := by
  unfold loadStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]


private theorem execInstrRF_lbu_ro (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (hnot : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 1) :
    execInstrRF ro rwBase rf ws (.LBU rd rs1 ofs) =
      (rf.set rd ((ro.byteAt (rf.get rs1 + signExtend12 ofs)).zeroExtend 64), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg hnot]

private theorem load_engine (src : Word) (bytes : List (BitVec 8)) (rf : RegFile)
    (i : Nat) (h_i : i < 8)
    (h_x6 : rf.get .x6 = src + BitVec.ofNat 64 (7 - i)) :
    execBlock ⟨src, bytes⟩ 0 rf [] loadStepBlock =
      (loadStepRf rf (bytes.getD (7 - i) 0), []) := by
  have h_se0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have h_addr : (rf.get .x6 + signExtend12 (0 : BitVec 12) - src).toNat = 7 - i := by
    rw [h_x6, h_se0]
    bv_omega
  have h_addr_after_slli : (((rf.set .x5 (rf.get .x5 <<< (8 : BitVec 6).toNat)).get .x6 +
      signExtend12 (0 : BitVec 12)) - src).toNat = 7 - i := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5)]
    exact h_addr
  rw [show loadStepBlock = [.SLLI .x5 .x5 8, .LBU .x10 .x6 0, .OR .x5 .x5 .x10,
      .ADDI .x6 .x6 (-1 : BitVec 12), .ADDI .x7 .x7 (-1 : BitVec 12)] from rfl]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  have hnot : ¬ inRw 0 [] ((rf.set .x5 (rf.get .x5 <<< (8 : BitVec 6).toNat)).get .x6 +
      signExtend12 (0 : BitVec 12)) 1 := by
    simp [inRw]
  rw [execInstrRF_lbu_ro (⟨src, bytes⟩ : Region) 0
    (rf.set .x5 (rf.get .x5 <<< (8 : BitVec 6).toNat)) [] .x10 .x6
    (0 : BitVec 12) hnot]
  have h_byte : Region.byteAt ⟨src, bytes⟩
      ((rf.set .x5 (rf.get .x5 <<< (8 : BitVec 6).toNat)).get .x6 +
        signExtend12 (0 : BitVec 12)) = bytes.getD (7 - i) 0 := by
    unfold Region.byteAt
    rw [h_addr_after_slli]
  rw [h_byte]
  dsimp only
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  unfold loadStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

def loadInv (src : Word) (bytes : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws _ =>
    rf.get .x5 = loadAccum bytes (i + 1) ∧
    rf.get .x6 = src + loadX6Offset i ∧
    rf.get .x7 = BitVec.ofNat 64 (8 - (i + 1)) ∧
    i < 8 ∧ 8 ≤ bytes.length ∧ ws = []

def blk2LdLe64Body (src : Word) (bytes : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (0 : Word), .ADDI .x6 .x10 (7 : BitVec 12), .LI .x7 (8 : Word)] ;;;
  .doWhile "loop" (.bne .x7 .x0) 8 (loadInv src bytes)
    (.block "load" loadStepBlock) ;;;
  .block "ret" [.MV .x10 .x5]

def blk2LdLe64Fn (src : Word) (bytes : List (BitVec 8)) : Fn where
  name := "blk2LdLe64"
  region := ⟨src, bytes⟩
  pre := fun rf ws _ => rf.get .x10 = src ∧ 8 ≤ bytes.length ∧ ws = []
  post := fun rf ws _ => rf.get .x10 = leU64 bytes ∧ ws = []
  body := blk2LdLe64Body src bytes

def blk2LdLe64_verified : Program :=
  (blk2LdLe64Body 0 []).flatten 0

#guard (blk2LdLe64_verified : List Instr).length = 10
#guard (blk2LdLe64Body 0 []).flatten 0 = (blk2LdLe64Body 0 []).flatten 0x80000000
#guard (blk2LdLe64Body 0 []).flatten 0 ++ [Instr.JALR .x0 .x1 0] = blk2LdLe64_prog

theorem blk2LdLe64Fn_spec (src : Word) (bytes : List (BitVec 8))
    (h_wf : (Region.mk src bytes).wf) (base : Word) :
    (blk2LdLe64Fn src bytes).Spec base := by
  vcgen
  case region => exact ⟨h_wf, RwRegion.empty_wf⟩
  case blk2LdLe64.loop.inv_init =>
    rintro rf' ws' A' h
    rcases h with ⟨rf0, ws0, h_ws0, hreach, rfl, rfl⟩
    rcases hreach with ⟨rfInit, wsInit, h_ws_init, hpre, rfl, rfl⟩
    rcases hpre with ⟨h_x10, h_len, h_ws_empty⟩
    subst h_ws_empty
    have h_x5_init : (execBlock (blk2LdLe64Fn src bytes).region 0 rfInit []
        [.LI .x5 0, .ADDI .x6 .x10 7, .LI .x7 8]).1.get .x5 = 0 := by
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true]
    have h_x6_init : (execBlock (blk2LdLe64Fn src bytes).region 0 rfInit []
        [.LI .x5 0, .ADDI .x6 .x10 7, .LI .x7 8]).1.get .x6 = src + 7 := by
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, h_x10]
      rw [show signExtend12 (7 : BitVec 12) = (7 : Word) from by decide]
    simp only [blk2LdLe64Fn] at h_x5_init h_x6_init
    simp only [blk2LdLe64Fn, RwRegion.empty]
    rw [load_engine src bytes _ 0 (by omega) (by simpa using h_x6_init)]
    refine ⟨?_, ?_, ?_, by omega, h_len, rfl⟩
    · rw [loadStepRf_get_x5, h_x5_init]
      simp [loadAccum, leByte]
    · rw [loadStepRf_get_x6, h_x6_init]
      rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      simp [loadX6Offset]
      bv_omega
    · rw [loadStepRf_get_x7]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
      decide
  case blk2LdLe64.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, ⟨⟨h_x5, h_x6, h_x7, h_lt, h_len, h_ws⟩, h_cond⟩, rfl, rfl⟩
    subst h_ws
    have h_cond_nonzero : rf₀.get .x7 ≠ 0 := by
      simpa [Cond.holds, h_x7, RegFile.get_x0] using h_cond
    have h_i1 : i + 1 < 8 := by
      interval_cases i <;> first | contradiction | omega
    simp only [blk2LdLe64Fn, RwRegion.empty]
    have h_x6_load : rf₀.get .x6 = src + BitVec.ofNat 64 (7 - (i + 1)) := by
      rw [h_x6, loadX6Offset_load_addr i h_i1]
    rw [load_engine src bytes rf₀ (i + 1) h_i1 h_x6_load]
    refine ⟨?_, ?_, ?_, by omega, h_len, rfl⟩
    · rw [loadStepRf_get_x5, h_x5, shift_or_byte_step bytes (i + 1) h_i1]
    · rw [loadStepRf_get_x6, h_x6, loadX6Offset_next_with_src src i h_i1]
    · rw [loadStepRf_get_x7, h_x7, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      interval_cases i <;> first | contradiction | bv_omega
  case blk2LdLe64.loop.exhausted =>
    rintro rf ws A ⟨-, -, h_x7, -, -, -⟩
    simp only [Cond.holds, h_x7, not_not, RegFile.get_x0]
    decide
  case blk2LdLe64.loop.body.load.mem =>
    rintro rf ws A h_ws (hpre | hloop)
    · rcases hpre with ⟨rfInit, wsInit, h_ws_init, ⟨h_x10, h_len, h_ws_empty⟩, rfl, rfl⟩
      obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero h_ws
      have h_addr :
          (((execBlock ({ base := src, bytes := bytes } : Region) 0 rfInit []
                [.LI .x5 0, .ADDI .x6 .x10 7, .LI .x7 8]).1.get .x6 +
              signExtend12 (0 : BitVec 12) - src).toNat = 7) := by
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
          RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
          not_false_eq_true, h_x10]
        rw [show signExtend12 (7 : BitVec 12) = (7 : Word) from by decide,
          show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega
      simp only [blk2LdLe64Fn, RwRegion.empty, loadStepBlock, blockVCs, execInstrRF, aluSem, loadSem, storeSem,
        Region.loadOk, inRw, List.length_nil, Nat.le_zero, RegFile.get_set_ne,
        ne_eq, reduceCtorEq, not_false_eq_true]
      rw [h_addr]
      exact ⟨trivial, ⟨Nat.one_dvd 7, by omega⟩, trivial, trivial, trivial, trivial⟩
    · rcases hloop with ⟨i, hi, ⟨h_x5, h_x6, h_x7, h_lt, h_len, h_ws_empty⟩, h_cond⟩
      obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero h_ws
      have h_cond_nonzero : rf.get .x7 ≠ 0 := by
        simpa [Cond.holds, h_x7, RegFile.get_x0] using h_cond
      have h_i1 : i + 1 < 8 := by
        interval_cases i <;> first | contradiction | omega
      have h_addr : (rf.get .x6 + signExtend12 (0 : BitVec 12) - src).toNat = 7 - (i + 1) := by
        rw [h_x6, loadX6Offset_load_addr i h_i1, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega
      simp only [blk2LdLe64Fn, RwRegion.empty, loadStepBlock, blockVCs, execInstrRF, aluSem, loadSem, storeSem,
        Region.loadOk, inRw, List.length_nil, Nat.le_zero, RegFile.get_set_ne,
        ne_eq, reduceCtorEq, not_false_eq_true]
      rw [h_addr]
      exact ⟨trivial, ⟨Nat.one_dvd (7 - (i + 1)), by omega⟩, trivial, trivial, trivial, trivial⟩
  case blk2LdLe64.post =>
    rintro rf' ws' A' h
    rcases h with ⟨rfLoop, wsLoop, h_ws_loop, hreach, hrfRet, hwsRet⟩
    rcases hreach with ⟨⟨i, h_le, h_x5, h_x6, h_x7, h_lt, h_len, h_ws_loop_empty⟩, h_not_cond⟩
    subst hwsRet
    subst h_ws_loop_empty
    have h_i : i = 7 := by
      simp only [Cond.holds, h_x7, RegFile.get_x0, not_not] at h_not_cond
      interval_cases i <;> try contradiction
      rfl
    subst h_i
    constructor
    · subst hrfRet
      simp only [blk2LdLe64Fn, RwRegion.empty, execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide : Reg.x10 ≠ Reg.x0), h_x5, loadAccum_8_eq]
    · rfl

end Blake2fLoadLe64SAsm

end EvmAsm.Codegen
