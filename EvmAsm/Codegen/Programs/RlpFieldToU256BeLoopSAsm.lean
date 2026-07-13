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

end EvmAsm.Codegen.RlpFieldToU256BeSAsm
