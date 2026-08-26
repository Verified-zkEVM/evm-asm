/-
  EvmAsm.Evm64.HandlerTableByte

  Byte-level (raw 0..255) dispatch surface for `HandlerTable`, sitting
  on top of `EvmOpcode.decodeByte?` and threading undecoded opcode
  bytes through to the INVALID/error step on `EvmState`.

  This is layer (b) of GH #106 slice 4 (beads `evm-asm-3ho93`): for any
  opcode byte with `EvmOpcode.decodeByte? = none`, dispatching through
  the byte surface must drive the EVM state into the error status, so
  that the future RV64 dispatch program (slice 3, `evm-asm-afkny`)
  composed with the JALR-to-invalidHandler default jump (slice 1's
  `dispatchTableIs` × layer (a)'s `jumpTableOfOpcodes`) lands in a
  well-defined invalid state.

  Layer (a) — the `Fin 256 → Word` table with `invalidHandler` default —
  already lives in `EvmAsm/Evm64/JumpTable.lean` as `jumpTableOfOpcodes`
  with the byte-level `_decode_none` / `_decode_some` projections. This
  file is the matching semantic surface on `HandlerTable`.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

module

public import EvmAsm.Evm64.HandlerTable
public import EvmAsm.Evm64.Dispatch
public import EvmAsm.Evm64.Termination

@[expose] public section

namespace EvmAsm.Evm64
namespace HandlerTable

/-- Byte-level dispatch: decode the raw opcode byte, dispatch the
    resulting `EvmOpcode` through `table`, and on undecoded bytes
    fall through to the INVALID/error step on `EvmState`.

    Distinctive token: `HandlerTable.dispatchByte #106-slice4`. -/
def dispatchByte (table : HandlerTable) (b : Fin 256)
    (state : EvmState) : EvmState :=
  match EvmOpcode.decodeByte? b.val with
  | some opcode => HandlerTable.dispatchOpcode table opcode state
  | none => state.invalid

@[simp] theorem dispatchByte_decoded
    (table : HandlerTable) (b : Fin 256) (opcode : EvmOpcode)
    (state : EvmState)
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode) :
    dispatchByte table b state =
      HandlerTable.dispatchOpcode table opcode state := by
  simp [dispatchByte, h_decode]

theorem dispatchByte_decoded_status
    (table : HandlerTable) (b : Fin 256) (opcode : EvmOpcode)
    (state : EvmState)
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode) :
    (dispatchByte table b state).status =
      (HandlerTable.dispatchOpcode table opcode state).status := by
  rw [dispatchByte_decoded table b opcode state h_decode]

@[simp] theorem dispatchByte_undecoded
    (table : HandlerTable) (b : Fin 256) (state : EvmState)
    (h_decode : EvmOpcode.decodeByte? b.val = none) :
    dispatchByte table b state = state.invalid := by
  simp [dispatchByte, h_decode]

theorem dispatchByte_decoded_lookup
    {table : HandlerTable} {b : Fin 256} {opcode : EvmOpcode}
    {handler : OpcodeHandler} (state : EvmState)
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup : table opcode = some handler) :
    dispatchByte table b state = handler state := by
  rw [dispatchByte_decoded table b opcode state h_decode]
  exact HandlerTable.dispatchOpcode_some h_lookup state

theorem dispatchByte_decoded_lookup_status
    {table : HandlerTable} {b : Fin 256} {opcode : EvmOpcode}
    {handler : OpcodeHandler} (state : EvmState)
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup : table opcode = some handler) :
    (dispatchByte table b state).status = (handler state).status := by
  rw [dispatchByte_decoded_lookup state h_decode h_lookup]

/--
If the decoded opcode byte looks up a status-preserving handler, byte-level
dispatch preserves the incoming interpreter status.

Distinctive token:
HandlerTable.dispatchByte_decoded_lookup_preserves_status #106 #107.
-/
theorem dispatchByte_decoded_lookup_preserves_status
    {table : HandlerTable} {b : Fin 256} {opcode : EvmOpcode}
    {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup : table opcode = some handler)
    (h_status : ∀ state : EvmState, (handler state).status = state.status)
    (state : EvmState) :
    (dispatchByte table b state).status = state.status := by
  rw [dispatchByte_decoded_lookup_status state h_decode h_lookup]
  exact h_status state

/--
If the decoded opcode byte looks up a handler that preserves
`codeLenMatches`, byte-level dispatch preserves `codeLenMatches`.

Distinctive token:
HandlerTable.dispatchByte_decoded_lookup_preserves_codeLenMatches #106 #107.
-/
theorem dispatchByte_decoded_lookup_preserves_codeLenMatches
    {table : HandlerTable} {b : Fin 256} {opcode : EvmOpcode}
    {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup : table opcode = some handler)
    (h_codeLen : ∀ state : EvmState,
      state.codeLenMatches → (handler state).codeLenMatches)
    (state : EvmState) (h_state : state.codeLenMatches) :
    (dispatchByte table b state).codeLenMatches := by
  rw [dispatchByte_decoded_lookup state h_decode h_lookup]
  exact h_codeLen state h_state

theorem dispatchByte_decoded_missing
    {table : HandlerTable} {b : Fin 256} {opcode : EvmOpcode}
    (state : EvmState)
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup : table opcode = none) :
    dispatchByte table b state = state.invalid := by
  rw [dispatchByte_decoded table b opcode state h_decode]
  exact HandlerTable.dispatchOpcode_none h_lookup state

theorem dispatchByte_undecoded_status
    (table : HandlerTable) (b : Fin 256) (state : EvmState)
    (h_decode : EvmOpcode.decodeByte? b.val = none) :
    (dispatchByte table b state).status = .error := by
  rw [dispatchByte_undecoded table b state h_decode]
  exact EvmState.invalid_status state

theorem dispatchByte_decoded_missing_status
    {table : HandlerTable} {b : Fin 256} {opcode : EvmOpcode}
    (state : EvmState)
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup : table opcode = none) :
    (dispatchByte table b state).status = .error := by
  rw [dispatchByte_decoded_missing state h_decode h_lookup]
  exact EvmState.invalid_status state

/-- Empty handler table dispatches every byte to the INVALID step. -/
@[simp] theorem dispatchByte_empty (b : Fin 256) (state : EvmState) :
    dispatchByte HandlerTable.empty b state = state.invalid := by
  unfold dispatchByte
  cases h : EvmOpcode.decodeByte? b.val with
  | none => rfl
  | some opcode =>
    simp [HandlerTable.dispatchOpcode, HandlerTable.dispatchOpcode?,
      HandlerTable.empty]

/-- Status after empty-table byte dispatch is always `.error`. -/
theorem dispatchByte_empty_status (b : Fin 256) (state : EvmState) :
    (dispatchByte HandlerTable.empty b state).status = .error := by
  rw [dispatchByte_empty b state]
  exact EvmState.invalid_status state

end HandlerTable
end EvmAsm.Evm64
