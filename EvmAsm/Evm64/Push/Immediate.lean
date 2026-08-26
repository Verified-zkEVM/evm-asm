/-
  EvmAsm.Evm64.Push.Immediate

  Executable PUSH immediate-byte bridge for GH #101.
-/

module

public import EvmAsm.Evm64.Push.Spec

@[expose] public section

namespace EvmAsm.Evm64
namespace PushImmediate

open EvmAsm.Rv64

/-- Read one EVM code byte, returning zero past EOF. PUSH immediates use the
    same executable-spec convention as calldata windows: bytes outside the
    available buffer are zero-padded. -/
def codeByteAt (code : List (BitVec 8)) (idx : Nat) : BitVec 8 :=
  if h : idx < code.length then code[idx] else 0

/-- The `i`th immediate byte consumed by a PUSHn opcode whose opcode byte is at
    `pc`. Immediate bytes start at `pc + 1`. -/
def pushImmediateByteAt (code : List (BitVec 8)) (pc i : Nat) : BitVec 8 :=
  codeByteAt code (pc + 1 + i)

/-- Executable-spec word assembled from the bytes following a PUSHn opcode.
    This reuses the existing big-endian/right-aligned `pushImmediateWord`
    assembler, with `codeByteAt` supplying EOF zero-padding. -/
def pushImmediateWordFromCode
    (code : List (BitVec 8)) (pc n : Nat) : EvmWord :=
  pushImmediateWord n (pushImmediateByteAt code pc)

/-- EVM PC after executing a PUSHn opcode. -/
def pcAfterPush (pc n : Nat) : Nat :=
  pc + 1 + n

theorem codeByteAt_of_lt {code : List (BitVec 8)} {idx : Nat}
    (h : idx < code.length) :
    codeByteAt code idx = code[idx] := by
  simp [codeByteAt, h]

theorem codeByteAt_of_ge {code : List (BitVec 8)} {idx : Nat}
    (h : code.length ≤ idx) :
    codeByteAt code idx = 0 := by
  simp [codeByteAt, show ¬idx < code.length from by omega]

@[simp] theorem codeByteAt_nil (idx : Nat) :
    codeByteAt [] idx = 0 := by
  exact codeByteAt_of_ge (code := []) (idx := idx) (by simp)

theorem pushImmediateByteAt_of_lt {code : List (BitVec 8)} {pc i : Nat}
    (h : pc + 1 + i < code.length) :
    pushImmediateByteAt code pc i = code[pc + 1 + i] := by
  simp [pushImmediateByteAt, codeByteAt_of_lt h]

theorem pushImmediateByteAt_of_ge {code : List (BitVec 8)} {pc i : Nat}
    (h : code.length ≤ pc + 1 + i) :
    pushImmediateByteAt code pc i = 0 := by
  simp [pushImmediateByteAt, codeByteAt_of_ge h]

@[simp] theorem pushImmediateByteAt_nil (pc i : Nat) :
    pushImmediateByteAt [] pc i = 0 := by
  simp [pushImmediateByteAt]

theorem pushImmediateWordFromCode_eq
    (code : List (BitVec 8)) (pc n : Nat) :
    pushImmediateWordFromCode code pc n =
      pushImmediateWord n (fun i => codeByteAt code (pc + 1 + i)) := by
  rfl

theorem pushImmediateWordFromCode_getLimbN_0
    (code : List (BitVec 8)) (pc n : Nat) :
    (pushImmediateWordFromCode code pc n).getLimbN 0 =
      pushImmediateLimb n (pushImmediateByteAt code pc) 0 := by
  unfold pushImmediateWordFromCode
  exact pushImmediateWord_getLimbN_0 n (pushImmediateByteAt code pc)

theorem pushImmediateWordFromCode_getLimbN_1
    (code : List (BitVec 8)) (pc n : Nat) :
    (pushImmediateWordFromCode code pc n).getLimbN 1 =
      pushImmediateLimb n (pushImmediateByteAt code pc) 1 := by
  unfold pushImmediateWordFromCode
  exact pushImmediateWord_getLimbN_1 n (pushImmediateByteAt code pc)

theorem pushImmediateWordFromCode_getLimbN_2
    (code : List (BitVec 8)) (pc n : Nat) :
    (pushImmediateWordFromCode code pc n).getLimbN 2 =
      pushImmediateLimb n (pushImmediateByteAt code pc) 2 := by
  unfold pushImmediateWordFromCode
  exact pushImmediateWord_getLimbN_2 n (pushImmediateByteAt code pc)

theorem pushImmediateWordFromCode_getLimbN_3
    (code : List (BitVec 8)) (pc n : Nat) :
    (pushImmediateWordFromCode code pc n).getLimbN 3 =
      pushImmediateLimb n (pushImmediateByteAt code pc) 3 := by
  unfold pushImmediateWordFromCode
  exact pushImmediateWord_getLimbN_3 n (pushImmediateByteAt code pc)

theorem pushImmediateWordFromCode_evmWordIs_fold
    (code : List (BitVec 8)) (pc n : Nat) (sp : Word) :
    ((sp ↦ₘ pushImmediateLimb n (pushImmediateByteAt code pc) 0) **
      ((sp + 8) ↦ₘ pushImmediateLimb n (pushImmediateByteAt code pc) 1) **
      ((sp + 16) ↦ₘ pushImmediateLimb n (pushImmediateByteAt code pc) 2) **
      ((sp + 24) ↦ₘ pushImmediateLimb n (pushImmediateByteAt code pc) 3)) =
    evmWordIs sp (pushImmediateWordFromCode code pc n) := by
  unfold pushImmediateWordFromCode
  exact pushImmediateWord_evmWordIs_fold sp n (pushImmediateByteAt code pc)

@[simp] theorem pcAfterPush_zero (pc : Nat) :
    pcAfterPush pc 0 = pc + 1 := by
  simp [pcAfterPush]

theorem pcAfterPush_eq (pc n : Nat) :
    pcAfterPush pc n = pc + 1 + n := rfl

theorem pcAfterPush_succ (pc n : Nat) :
    pcAfterPush pc (n + 1) = pcAfterPush pc n + 1 := by
  unfold pcAfterPush
  omega

theorem pc_lt_pcAfterPush_of_width_pos {pc n : Nat} (h_pos : 0 < n) :
    pc < pcAfterPush pc n := by
  unfold pcAfterPush
  omega

-- ============================================================================
-- Concrete tests (GH #101, bead evm-asm-f0f5.11)
-- ============================================================================

/-- PUSH1 0x42 pushes the value 0x42 (EvmWord = BitVec.ofNat 256 0x42). -/
theorem pushImmediateWordFromCode_push1_0x42 :
    pushImmediateWordFromCode [0x60, 0x42] 0 1 = BitVec.ofNat 256 0x42 := by decide

/-- PUSH2 0xABCD pushes the big-endian 2-byte value 0xABCD. -/
theorem pushImmediateWordFromCode_push2_0xABCD :
    pushImmediateWordFromCode [0x61, 0xAB, 0xCD] 0 2 = BitVec.ofNat 256 0xABCD := by decide

/-- PUSH32 with bytes 0x01..0x20 assembles the full 256-bit big-endian value. -/
theorem pushImmediateWordFromCode_push32_seq :
    pushImmediateWordFromCode
      (0x7F :: (List.range 32).map (fun i => BitVec.ofNat 8 (i + 1)))
      0 32 =
      BitVec.ofNat 256
        0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 := by
  decide

/-- PUSH1 with EOF zero-padding: missing bytes default to 0x00. -/
theorem pushImmediateWordFromCode_push1_eof :
    pushImmediateWordFromCode [0x60] 0 1 = BitVec.ofNat 256 0 := by decide

/-- PUSH1 advances EVM PC by 2 (opcode + 1 immediate byte). -/
theorem pcAfterPush_push1 (pc : Nat) : pcAfterPush pc 1 = pc + 2 := by simp [pcAfterPush]

/-- PUSH32 advances EVM PC by 33 (opcode + 32 immediate bytes). -/
theorem pcAfterPush_push32 (pc : Nat) : pcAfterPush pc 32 = pc + 33 := by simp [pcAfterPush]

end PushImmediate
end EvmAsm.Evm64
