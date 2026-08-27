/-
  EvmAsm.Evm64.InterpreterExecutableFetchBridge

  Connect executable-spec opcode bytes to the pure interpreter fetch/decode
  surface (GH #109).
-/

module

public import EvmAsm.Evm64.ExecutableSpecOpcodeBridge
public import EvmAsm.Evm64.InterpreterLoop

public section

namespace EvmAsm.Evm64

namespace InterpreterExecutableFetchBridge

/--
If the byte fetched from `state.code[state.pc]` decodes to an opcode, the
interpreter's current-opcode decoder returns that opcode.

Distinctive token: InterpreterExecutableFetchBridge.decodeCurrentOpcode?_of_execSpecByte #109.
-/
theorem decodeCurrentOpcode?_of_execSpecByte
    {state : EvmState} {byte : BitVec 8} {opcode : EvmOpcode}
    (h_pc : state.pc < state.code.length)
    (h_code : state.code[state.pc] = byte)
    (h_decode : EvmOpcode.decodeByte? byte.toNat = some opcode) :
    InterpreterLoop.decodeCurrentOpcode? state = some opcode := by
  simp [InterpreterLoop.decodeCurrentOpcode?, InterpreterLoop.fetchOpcodeByte?,
    h_pc, h_code, h_decode]

theorem stepWithHandler_of_execSpecByte
    (handler : InterpreterLoop.Handler)
    {state : EvmState} {byte : BitVec 8} {opcode : EvmOpcode}
    (h_pc : state.pc < state.code.length)
    (h_code : state.code[state.pc] = byte)
    (h_decode : EvmOpcode.decodeByte? byte.toNat = some opcode) :
    InterpreterLoop.stepWithHandler handler state = handler opcode state := by
  exact InterpreterLoop.stepWithHandler_of_decode handler
    (decodeCurrentOpcode?_of_execSpecByte h_pc h_code h_decode)

theorem decodeCurrentOpcode?_of_roundtrip
    {state : EvmState} {byte : BitVec 8} {opcode : EvmOpcode}
    (h_pc : state.pc < state.code.length)
    (h_code : state.code[state.pc] = byte)
    (h_roundtrip :
      EvmOpcode.byte? opcode = some byte.toNat ∧
        EvmOpcode.decodeByte? byte.toNat = some opcode) :
    InterpreterLoop.decodeCurrentOpcode? state = some opcode := by
  exact decodeCurrentOpcode?_of_execSpecByte h_pc h_code h_roundtrip.2

theorem stepWithHandler_of_roundtrip
    (handler : InterpreterLoop.Handler)
    {state : EvmState} {byte : BitVec 8} {opcode : EvmOpcode}
    (h_pc : state.pc < state.code.length)
    (h_code : state.code[state.pc] = byte)
    (h_roundtrip :
      EvmOpcode.byte? opcode = some byte.toNat ∧
        EvmOpcode.decodeByte? byte.toNat = some opcode) :
    InterpreterLoop.stepWithHandler handler state = handler opcode state := by
  exact stepWithHandler_of_execSpecByte handler h_pc h_code h_roundtrip.2

/--
Parameterized executable-spec bridge for `PUSH1` through `PUSH32`.

Distinctive token:
InterpreterExecutableFetchBridge.decodeCurrentOpcode?_of_execSpecPushByte #109 #101.
-/
theorem decodeCurrentOpcode?_of_execSpecPushByte
    {state : EvmState} {n : Nat}
    (h_low : 1 ≤ n) (h_high : n ≤ 32)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.execSpecPushByte n : BitVec 8)) :
    InterpreterLoop.decodeCurrentOpcode? state = some (EvmOpcode.PUSH n) := by
  have h_byte :
      (ExecutableSpecOpcodeBridge.execSpecPushByte n : BitVec 8).toNat =
        ExecutableSpecOpcodeBridge.execSpecPushByte n := by
    unfold ExecutableSpecOpcodeBridge.execSpecPushByte
    interval_cases n <;> rfl
  exact decodeCurrentOpcode?_of_execSpecByte h_pc h_code
    (by
      rw [h_byte]
      exact (ExecutableSpecOpcodeBridge.roundtrip_execSpecPush_of_valid
        h_low h_high).2)

theorem stepWithHandler_of_execSpecPushByte
    (handler : InterpreterLoop.Handler)
    {state : EvmState} {n : Nat}
    (h_low : 1 ≤ n) (h_high : n ≤ 32)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.execSpecPushByte n : BitVec 8)) :
    InterpreterLoop.stepWithHandler handler state =
      handler (EvmOpcode.PUSH n) state := by
  exact InterpreterLoop.stepWithHandler_of_decode handler
    (decodeCurrentOpcode?_of_execSpecPushByte h_low h_high h_pc h_code)

/--
Parameterized executable-spec bridge for `LOG0` through `LOG4`.

Distinctive token:
InterpreterExecutableFetchBridge.decodeCurrentOpcode?_of_execSpecLogByte #109 #112.
-/
theorem decodeCurrentOpcode?_of_execSpecLogByte
    {state : EvmState} (kind : LogArgs.Kind)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.execSpecLogByte kind : BitVec 8)) :
    InterpreterLoop.decodeCurrentOpcode? state = some (EvmOpcode.LOG kind) := by
  have h_byte :
      (ExecutableSpecOpcodeBridge.execSpecLogByte kind : BitVec 8).toNat =
        ExecutableSpecOpcodeBridge.execSpecLogByte kind := by
    cases kind <;> rfl
  exact decodeCurrentOpcode?_of_execSpecByte h_pc h_code
    (by
      rw [h_byte]
      exact (ExecutableSpecOpcodeBridge.roundtrip_execSpecLog kind).2)

theorem stepWithHandler_of_execSpecLogByte
    (handler : InterpreterLoop.Handler)
    {state : EvmState} (kind : LogArgs.Kind)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.execSpecLogByte kind : BitVec 8)) :
    InterpreterLoop.stepWithHandler handler state =
      handler (EvmOpcode.LOG kind) state := by
  exact InterpreterLoop.stepWithHandler_of_decode handler
    (decodeCurrentOpcode?_of_execSpecLogByte kind h_pc h_code)

theorem decodeCurrentOpcode?_of_execSpec_SDIV
    {state : EvmState}
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] = (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8)) :
    InterpreterLoop.decodeCurrentOpcode? state = some EvmOpcode.SDIV := by
  exact decodeCurrentOpcode?_of_execSpecByte h_pc h_code (by
    simp [ExecutableSpecOpcodeBridge.Ops.SDIV, EvmOpcode.decodeByte?])

theorem stepWithHandler_of_execSpec_SDIV
    (handler : InterpreterLoop.Handler)
    {state : EvmState}
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] = (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8)) :
    InterpreterLoop.stepWithHandler handler state =
      handler EvmOpcode.SDIV state := by
  exact InterpreterLoop.stepWithHandler_of_decode handler
    (decodeCurrentOpcode?_of_execSpec_SDIV h_pc h_code)

theorem decodeCurrentOpcode?_of_execSpec_SMOD
    {state : EvmState}
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] = (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8)) :
    InterpreterLoop.decodeCurrentOpcode? state = some EvmOpcode.SMOD := by
  exact decodeCurrentOpcode?_of_execSpecByte h_pc h_code (by
    simp [ExecutableSpecOpcodeBridge.Ops.SMOD, EvmOpcode.decodeByte?])

theorem stepWithHandler_of_execSpec_SMOD
    (handler : InterpreterLoop.Handler)
    {state : EvmState}
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] = (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8)) :
    InterpreterLoop.stepWithHandler handler state =
      handler EvmOpcode.SMOD state := by
  exact InterpreterLoop.stepWithHandler_of_decode handler
    (decodeCurrentOpcode?_of_execSpec_SMOD h_pc h_code)

theorem decodeCurrentOpcode?_of_execSpec_CALL
    {state : EvmState}
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] = (ExecutableSpecOpcodeBridge.Ops.CALL : BitVec 8)) :
    InterpreterLoop.decodeCurrentOpcode? state = some EvmOpcode.CALL := by
  exact decodeCurrentOpcode?_of_execSpecByte h_pc h_code (by
    simp [ExecutableSpecOpcodeBridge.Ops.CALL, EvmOpcode.decodeByte?])

theorem decodeCurrentOpcode?_of_execSpec_CREATE
    {state : EvmState}
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] = (ExecutableSpecOpcodeBridge.Ops.CREATE : BitVec 8)) :
    InterpreterLoop.decodeCurrentOpcode? state = some EvmOpcode.CREATE := by
  exact decodeCurrentOpcode?_of_execSpecByte h_pc h_code (by
    simp [ExecutableSpecOpcodeBridge.Ops.CREATE, EvmOpcode.decodeByte?])

theorem decodeCurrentOpcode?_of_execSpec_RETURN
    {state : EvmState}
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] = (ExecutableSpecOpcodeBridge.Ops.RETURN : BitVec 8)) :
    InterpreterLoop.decodeCurrentOpcode? state = some EvmOpcode.RETURN := by
  exact decodeCurrentOpcode?_of_execSpecByte h_pc h_code (by
    simp [ExecutableSpecOpcodeBridge.Ops.RETURN, EvmOpcode.decodeByte?])

theorem decodeCurrentOpcode?_of_execSpec_REVERT
    {state : EvmState}
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] = (ExecutableSpecOpcodeBridge.Ops.REVERT : BitVec 8)) :
    InterpreterLoop.decodeCurrentOpcode? state = some EvmOpcode.REVERT := by
  exact decodeCurrentOpcode?_of_execSpecByte h_pc h_code (by
    simp [ExecutableSpecOpcodeBridge.Ops.REVERT, EvmOpcode.decodeByte?])

theorem decodeCurrentOpcode?_of_execSpec_INVALID
    {state : EvmState}
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] = (ExecutableSpecOpcodeBridge.Ops.INVALID : BitVec 8)) :
    InterpreterLoop.decodeCurrentOpcode? state = some EvmOpcode.INVALID := by
  exact decodeCurrentOpcode?_of_execSpecByte h_pc h_code (by
    simp [ExecutableSpecOpcodeBridge.Ops.INVALID, EvmOpcode.decodeByte?])

end InterpreterExecutableFetchBridge

end EvmAsm.Evm64
