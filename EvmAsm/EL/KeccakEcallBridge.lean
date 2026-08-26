/-
  EvmAsm.EL.KeccakEcallBridge

  Pure zkVM KECCAK accelerator ECALL surface (GH #111).
-/

module

public import EvmAsm.EL.KeccakInputBridge
public import EvmAsm.EL.KeccakResultBridge
public import EvmAsm.Evm64.Accelerators.Status
public import EvmAsm.Evm64.Accelerators.SyscallIds

@[expose] public section

namespace EvmAsm.EL

namespace KeccakEcallBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

/-- Selector reserved for the KECCAK256 accelerator ECALL surface. This is the
historical surface selector mirroring the EVM opcode byte (`0x20`). -/
def keccakSelector : BitVec 64 := 0x20

/-- zkVM accelerator syscall ID for `zkvm_keccak256`, as pinned by
`EvmAsm.Accelerators.SyscallId.keccak256`. This is the `t0` selector value the
guest places before issuing ECALL; the host dispatcher uses it to route to the
KECCAK accelerator implementation. -/
def keccakSyscallId : BitVec 64 := BitVec.ofNat 64 EvmAsm.Accelerators.SyscallId.keccak256

/-- The pinned syscall ID for KECCAK matches the accelerator table. -/
@[simp] theorem keccakSyscallId_eq :
    keccakSyscallId = BitVec.ofNat 64 EvmAsm.Accelerators.SyscallId.keccak256 := rfl

/-- ECALL request passed to the zkVM KECCAK accelerator. -/
structure KeccakRequest where
  selector : BitVec 64
  input : KeccakInputBridge.AcceleratorInput
  deriving Repr

/-- ECALL result returned by the zkVM KECCAK accelerator.

`status` mirrors the C `zkvm_status` enum returned by `zkvm_keccak256` in
`EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators/zkvm_accelerators.h`.
The success path used everywhere else in this module pins it to
`ZkvmStatus.eok`; failure-path support is reserved for follow-on slices. -/
structure KeccakResult where
  output : KeccakResultBridge.AcceleratorOutput
  status : ZkvmStatus := .eok

/-- Build the KECCAK accelerator request from already-loaded input bytes. -/
def requestFromInput (input : KeccakInputBridge.AcceleratorInput) : KeccakRequest :=
  { selector := keccakSelector, input := input }

/-- Stack word exposed by a successful KECCAK accelerator result. -/
def stackWordFromResult (result : KeccakResult) : EvmWord :=
  KeccakResultBridge.stackWordFromAcceleratorOutput result.output

/-- RV64 `a0` return-register `Word` value carrying this result's status. -/
def statusWordFromResult (result : KeccakResult) : BitVec 64 :=
  EvmAsm.Rv64.zkvmStatusToWord result.status

/-- Boolean predicate identifying successful KECCAK results. -/
def isOk (result : KeccakResult) : Bool := result.status.isOk

/--
Pure execution boundary for the KECCAK ECALL. The hash computation itself is
supplied by the accelerator model; this bridge fixes the request/result shape
and the stack word extracted from the returned output buffer. The status is
pinned to `ZkvmStatus.eok` on this success path; a failure-path constructor is
reserved for a follow-on slice once host-side error reporting is modeled.

Distinctive token: KeccakEcallBridge.executeKeccakEcall #111.
-/
def executeKeccakEcall
    (accelerator : KeccakInputBridge.AcceleratorInput →
      KeccakResultBridge.AcceleratorOutput)
    (request : KeccakRequest) : KeccakResult :=
  { output := accelerator request.input, status := .eok }

theorem requestFromInput_selector (input : KeccakInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = keccakSelector := rfl

theorem requestFromInput_input (input : KeccakInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl

theorem executeKeccakEcall_output
    (accelerator : KeccakInputBridge.AcceleratorInput →
      KeccakResultBridge.AcceleratorOutput)
    (request : KeccakRequest) :
    (executeKeccakEcall accelerator request).output = accelerator request.input := rfl

/-- The success-path ECALL surface always returns `ZkvmStatus.eok` in the
`status` field. -/
@[simp] theorem executeKeccakEcall_status
    (accelerator : KeccakInputBridge.AcceleratorInput →
      KeccakResultBridge.AcceleratorOutput)
    (request : KeccakRequest) :
    (executeKeccakEcall accelerator request).status = .eok := rfl

/-- The success-path ECALL surface is recognised as OK. -/
@[simp] theorem executeKeccakEcall_isOk
    (accelerator : KeccakInputBridge.AcceleratorInput →
      KeccakResultBridge.AcceleratorOutput)
    (request : KeccakRequest) :
    isOk (executeKeccakEcall accelerator request) = true := rfl

/-- The `a0` return-register word for any successful KECCAK ECALL is the
canonical `ZKVM_EOK` constant. -/
@[simp] theorem executeKeccakEcall_statusWord
    (accelerator : KeccakInputBridge.AcceleratorInput →
      KeccakResultBridge.AcceleratorOutput)
    (request : KeccakRequest) :
    statusWordFromResult (executeKeccakEcall accelerator request) =
      EvmAsm.Rv64.zkvmStatusEokWord := rfl

theorem executeKeccakEcall_stackWord
    (accelerator : KeccakInputBridge.AcceleratorInput →
      KeccakResultBridge.AcceleratorOutput)
    (request : KeccakRequest) :
    stackWordFromResult (executeKeccakEcall accelerator request) =
      KeccakResultBridge.stackWordFromAcceleratorOutput
        (accelerator request.input) := rfl

theorem executeKeccakEcall_fromArgs_stackWord
    (accelerator : KeccakInputBridge.AcceleratorInput →
      KeccakResultBridge.AcceleratorOutput)
    (memory : KeccakInputBridge.MemoryReader)
    (args : EvmAsm.Evm64.KeccakArgs.Args) :
    stackWordFromResult
        (executeKeccakEcall accelerator
          (requestFromInput (KeccakInputBridge.acceleratorInputFromArgs memory args))) =
      KeccakResultBridge.stackWordFromAcceleratorOutput
        (accelerator (KeccakInputBridge.acceleratorInputFromArgs memory args)) := rfl

end KeccakEcallBridge

end EvmAsm.EL
