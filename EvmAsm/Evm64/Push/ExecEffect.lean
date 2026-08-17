/-
  EvmAsm.Evm64.Push.ExecEffect

  Executable PUSH opcode effect bridge for GH #101.
-/

import EvmAsm.Evm64.Push.Immediate
import EvmAsm.Evm64.Push.Width

namespace EvmAsm.Evm64
namespace PushExecEffect

/-- Compact executable effect of a PUSHn opcode. -/
structure Effect where
  word : EvmWord
  pc : Nat
  stack : List EvmWord
  deriving Repr

/-- PUSH1..PUSH32 pop no stack arguments. -/
def stackArgumentCount : Nat := 0

/-- PUSH1..PUSH32 push one result word. -/
def resultCount : Nat := 1

/-- The word pushed by executable PUSHn decoding at `pc`.
    Distinctive token: PushExecEffect.pushedWordFromCode. -/
def pushedWordFromCode (code : List (BitVec 8)) (pc n : Nat) : EvmWord :=
  PushImmediate.pushImmediateWordFromCode code pc n

/-- The program counter after executing a PUSHn opcode. -/
def pcAfterPushFromCode (_code : List (BitVec 8)) (pc n : Nat) : Nat :=
  PushImmediate.pcAfterPush pc n

/-- PUSH stack effect: prepend the decoded immediate word to the old stack.
    Distinctive token: PushExecEffect.stackAfterPush. -/
def stackAfterPush
    (code : List (BitVec 8)) (pc n : Nat) (stack : List EvmWord) :
    List EvmWord :=
  pushedWordFromCode code pc n :: stack

/-- Bundle the executable PUSHn word, next PC, and stack result. -/
def effectFromCode
    (code : List (BitVec 8)) (pc n : Nat) (stack : List EvmWord) : Effect :=
  { word := pushedWordFromCode code pc n
    pc := pcAfterPushFromCode code pc n
    stack := stackAfterPush code pc n stack }

@[simp] theorem stackAfterPush_length
    (code : List (BitVec 8)) (pc n : Nat) (stack : List EvmWord) :
    (stackAfterPush code pc n stack).length = stack.length + 1 := by
  simp [stackAfterPush]

/--
The executable PUSH effect stack is exactly its decoded word consed onto the
input stack.

Distinctive token: PushExecEffect.effectFromCode_stack_eq_word_cons #101 #107.
-/
theorem effectFromCode_stack_eq_word_cons
    (code : List (BitVec 8)) (pc n : Nat) (stack : List EvmWord) :
    (effectFromCode code pc n stack).stack =
      (effectFromCode code pc n stack).word :: stack := rfl

@[simp] theorem effectFromCode_stack_length
    (code : List (BitVec 8)) (pc n : Nat) (stack : List EvmWord) :
    (effectFromCode code pc n stack).stack.length = stack.length + 1 := by
  simp [effectFromCode, stackAfterPush]

@[simp] theorem pushedWordFromCode_nil (pc n : Nat) :
    pushedWordFromCode [] pc n = PushImmediate.pushImmediateWordFromCode [] pc n := rfl

/-- Distinctive token: PushExecEffect.effectFromCode_pc_le_pc_plus_33 #101. -/
theorem effectFromCode_pc_le_pc_plus_33_of_validWidth
    {code : List (BitVec 8)} {pc n : Nat} {stack : List EvmWord}
    (h_valid : PushWidth.validWidth n) :
    (effectFromCode code pc n stack).pc ≤ pc + 33 := by
  exact PushWidth.pcAfterPush_le_pc_plus_33 h_valid

end PushExecEffect
end EvmAsm.Evm64
