/-
  EvmAsm.Evm64.Termination

  Pure terminating-status helpers for GH #113.
-/

module

public import EvmAsm.Evm64.EvmState

@[expose] public section

namespace EvmAsm.Evm64
namespace EvmState

/-- STOP terminates without returndata. -/
def stop (state : EvmState) : EvmState :=
  state.withStatus .stopped

/-- RETURN terminates successfully with returndata bytes. -/
def returnWith (state : EvmState) (data : List (BitVec 8)) : EvmState :=
  state.withStatus (.returned data)

/-- REVERT terminates with revert data. -/
def revertWith (state : EvmState) (data : List (BitVec 8)) : EvmState :=
  state.withStatus (.reverted data)

/-- INVALID terminates with an error status. -/
def invalid (state : EvmState) : EvmState :=
  state.withStatus .error

@[simp] theorem stop_status (state : EvmState) :
    state.stop.status = .stopped := rfl

@[simp] theorem returnWith_status (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).status = .returned data := rfl

@[simp] theorem revertWith_status (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).status = .reverted data := rfl

@[simp] theorem invalid_status (state : EvmState) :
    state.invalid.status = .error := rfl

theorem stop_status_tag (state : EvmState) :
    state.stop.status.tag = 1 := rfl

theorem returnWith_status_tag (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).status.tag = 2 := rfl

theorem revertWith_status_tag (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).status.tag = 3 := rfl

theorem invalid_status_tag (state : EvmState) :
    state.invalid.status.tag = 4 := rfl

@[simp] theorem stop_pc (state : EvmState) :
    state.stop.pc = state.pc := rfl

@[simp] theorem returnWith_pc (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).pc = state.pc := rfl

@[simp] theorem revertWith_pc (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).pc = state.pc := rfl

@[simp] theorem invalid_pc (state : EvmState) :
    state.invalid.pc = state.pc := rfl

@[simp] theorem stop_stack (state : EvmState) :
    state.stop.stack = state.stack := rfl

@[simp] theorem returnWith_stack (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).stack = state.stack := rfl

@[simp] theorem revertWith_stack (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).stack = state.stack := rfl

@[simp] theorem invalid_stack (state : EvmState) :
    (state.invalid).stack = state.stack := rfl

/-! ### Structural preservation lemmas

The terminating helpers only update the `status` field; gas, memory, code, and
environment fields are preserved untouched. Frame-side reasoning for the
upcoming RETURN/REVERT/STOP/INVALID handler specs and the interpreter-loop
termination proofs needs each preservation fact as a `simp` lemma. -/

@[simp] theorem stop_gas (state : EvmState) :
    state.stop.gas = state.gas := rfl

@[simp] theorem stop_memoryCells (state : EvmState) :
    state.stop.memoryCells = state.memoryCells := rfl

@[simp] theorem stop_memory (state : EvmState) :
    state.stop.memory = state.memory := rfl

@[simp] theorem stop_memSize (state : EvmState) :
    state.stop.memSize = state.memSize := rfl

@[simp] theorem stop_code (state : EvmState) :
    state.stop.code = state.code := rfl

@[simp] theorem stop_codeLen (state : EvmState) :
    state.stop.codeLen = state.codeLen := rfl

@[simp] theorem stop_env (state : EvmState) :
    state.stop.env = state.env := rfl

theorem stop_codeLenMatches
    (state : EvmState) (h_codeLen : state.codeLenMatches) :
    state.stop.codeLenMatches := by
  unfold EvmState.codeLenMatches at h_codeLen ⊢
  simp [h_codeLen]

@[simp] theorem returnWith_gas (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).gas = state.gas := rfl

@[simp] theorem returnWith_memoryCells (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).memoryCells = state.memoryCells := rfl

@[simp] theorem returnWith_memory (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).memory = state.memory := rfl

@[simp] theorem returnWith_memSize (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).memSize = state.memSize := rfl

@[simp] theorem returnWith_code (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).code = state.code := rfl

@[simp] theorem returnWith_codeLen (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).codeLen = state.codeLen := rfl

@[simp] theorem returnWith_env (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).env = state.env := rfl

@[simp] theorem revertWith_gas (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).gas = state.gas := rfl

@[simp] theorem revertWith_memoryCells (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).memoryCells = state.memoryCells := rfl

@[simp] theorem revertWith_memory (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).memory = state.memory := rfl

@[simp] theorem revertWith_memSize (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).memSize = state.memSize := rfl

@[simp] theorem revertWith_code (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).code = state.code := rfl

@[simp] theorem revertWith_codeLen (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).codeLen = state.codeLen := rfl

@[simp] theorem revertWith_env (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).env = state.env := rfl

@[simp] theorem invalid_gas (state : EvmState) :
    state.invalid.gas = state.gas := rfl

@[simp] theorem invalid_memoryCells (state : EvmState) :
    state.invalid.memoryCells = state.memoryCells := rfl

@[simp] theorem invalid_memory (state : EvmState) :
    state.invalid.memory = state.memory := rfl

@[simp] theorem invalid_memSize (state : EvmState) :
    state.invalid.memSize = state.memSize := rfl

@[simp] theorem invalid_code (state : EvmState) :
    state.invalid.code = state.code := rfl

@[simp] theorem invalid_codeLen (state : EvmState) :
    state.invalid.codeLen = state.codeLen := rfl

@[simp] theorem invalid_env (state : EvmState) :
    state.invalid.env = state.env := rfl

theorem invalid_codeLenMatches
    (state : EvmState) (h_codeLen : state.codeLenMatches) :
    state.invalid.codeLenMatches := by
  unfold EvmState.codeLenMatches at h_codeLen ⊢
  simp [h_codeLen]

end EvmState
end EvmAsm.Evm64
