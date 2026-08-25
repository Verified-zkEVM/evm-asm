/-
  EvmAsm.EL.CreateArgsBridge

  Bridge from EVM CREATE-family stack arguments to EL creation requests
  (GH #115).
-/

module

public import EvmAsm.EL.Create
public import EvmAsm.Evm64.CreateArgs

@[expose] public section

namespace EvmAsm.EL

namespace CreateArgsBridge

abbrev InitcodeRange := EvmAsm.Evm64.CreateArgs.InitcodeRange
abbrev CreateArgs := EvmAsm.Evm64.CreateArgs.Create
abbrev Create2Args := EvmAsm.Evm64.CreateArgs.Create2

def gasNat (gas : EvmAsm.Evm64.EvmWord) : Nat :=
  gas.toNat

def createInitcodeRange (args : CreateArgs) : InitcodeRange :=
  args.initcode

def create2InitcodeRange (args : Create2Args) : InitcodeRange :=
  args.initcode

/-- CREATE stack arguments become an EL creation request once the initcode
    memory slice has been loaded into bytes. -/
def createRequest
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) : CreateRequest :=
  CreateRequest.forCreate creator args.value initcode (gasNat gas)

/-- CREATE2 stack arguments become an EL creation request once the initcode
    memory slice has been loaded into bytes. -/
def create2Request
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) : CreateRequest :=
  CreateRequest.forCreate2 creator args.value initcode (gasNat gas) args.salt

theorem createRequestKind
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) :
    (createRequest creator initcode gas args).kind = .create := rfl

theorem create2RequestKind
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) :
    (create2Request creator initcode gas args).kind = .create2 := rfl

theorem createRequestValue
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) :
    (createRequest creator initcode gas args).value = args.value := rfl

theorem create2RequestValue
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) :
    (create2Request creator initcode gas args).value = args.value := rfl

theorem createRequestInitcode
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) :
    (createRequest creator initcode gas args).initcode = initcode := rfl

theorem create2RequestInitcode
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) :
    (create2Request creator initcode gas args).initcode = initcode := rfl

theorem createRequestGas
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) :
    (createRequest creator initcode gas args).gas = gasNat gas := rfl

theorem create2RequestGas
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) :
    (create2Request creator initcode gas args).gas = gasNat gas := rfl

theorem createRequestSalt?
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) :
    (createRequest creator initcode gas args).salt? = none := rfl

theorem create2RequestSalt?
    (creator : Address) (initcode : List Byte) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) :
    (create2Request creator initcode gas args).salt? = some args.salt := rfl

theorem createInitcodeRange_eq
    (args : CreateArgs) :
    createInitcodeRange args =
      { offset := args.initcode.offset, size := args.initcode.size } := by
  obtain ⟨value, initcode⟩ := args
  cases initcode
  rfl

theorem create2InitcodeRange_eq
    (args : Create2Args) :
    create2InitcodeRange args =
      { offset := args.initcode.offset, size := args.initcode.size } := by
  obtain ⟨value, initcode, salt⟩ := args
  cases initcode
  rfl

end CreateArgsBridge

end EvmAsm.EL
