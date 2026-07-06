/-
  EvmAsm.Stateless.VM

  Umbrella for the EVM interpreter subtree of the stateless guest.
  Mirrors `forks/amsterdam/vm/` (interpreter.py + instructions/ +
  memory.py + stack.py + precompiled_contracts/ + gas.py).

  ## Subtree

  - `Interpreter.lean`  — top-level `execute_message` dispatch loop.
                          Reuses the M5b dispatch table at
                          `EvmAsm/Codegen/Programs.lean` (256-entry
                          jump table) as the concrete dispatcher.
  - `Message.lean`      — message frame record (caller / callee /
                          value / data / depth, gas).
  - `Memory.lean`       — EVM memory model (MLOAD/MSTORE/MSTORE8
                          dispatch already covered by `Evm64/MLoad`,
                          `Evm64/MStore`, `Evm64/MStore8`; this
                          file is the per-frame book-keeping shim).
  - `Stack.lean`        — EVM value stack (POP/PUSH/DUP/SWAP
                          opcodes already in `Evm64/{Pop, Push,
                          Dup, Swap}`; this file binds them into
                          a frame).
  - `Precompiles.lean`  — dispatch/framing surface for precompile
                          addresses 0x01..0x14 plus P256VERIFY
                          at 0x100. Unsupported calls still route
                          to `unimplemented_exit`; implemented
                          slices expose pure return-data framing
                          before they are wired into the concrete
                          CALL/STATICCALL path.
  - `Spec.lean`         — cpsTriple placeholders.

  All sub-files are scaffolds in PR-K12.
-/

import EvmAsm.Stateless.VM.Interpreter
import EvmAsm.Stateless.VM.Message
import EvmAsm.Stateless.VM.Memory
import EvmAsm.Stateless.VM.Stack
import EvmAsm.Stateless.VM.Precompiles
import EvmAsm.Stateless.VM.Spec
