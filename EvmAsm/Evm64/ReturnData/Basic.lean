/-
  EvmAsm.Evm64.ReturnData.Basic

  Pure returndata helpers for RETURNDATACOPY executable-spec bridges
  (GH #107 / GH #114).
-/

-- (No `import EvmAsm.Evm64.Basic`: this module only uses `BitVec 8`,
-- not anything from `Evm64.Basic`; dropped per shake hygiene, slice of #1045.)

module

@[expose] public section
namespace EvmAsm.Evm64
namespace ReturnData

/-- Read one returndata byte, returning zero past the end of the buffer. -/
def byte (data : List (BitVec 8)) (idx : Nat) : BitVec 8 :=
  if h : idx < data.length then data[idx] else 0

/-- Bytes written by RETURNDATACOPY:
    `size` bytes from `data` starting at `dataOffset`, with out-of-bounds
    reads producing zero. Distinctive token: ReturnData.copyBytes #107 #114. -/
def copyBytes
    (data : List (BitVec 8)) (dataOffset size : Nat) : List (BitVec 8) :=
  (List.range size).map (fun i => byte data (dataOffset + i))

theorem byte_of_lt {data : List (BitVec 8)} {idx : Nat}
    (h : idx < data.length) :
    byte data idx = data[idx] := by
  simp [byte, h]

theorem byte_of_ge {data : List (BitVec 8)} {idx : Nat}
    (h : data.length ≤ idx) :
    byte data idx = 0 := by
  simp [byte, show ¬idx < data.length from by omega]

@[simp] theorem byte_nil (idx : Nat) :
    byte [] idx = 0 := by
  exact byte_of_ge (data := []) (idx := idx) (by simp)

@[simp] theorem copyBytes_length
    (data : List (BitVec 8)) (dataOffset size : Nat) :
    (copyBytes data dataOffset size).length = size := by
  simp [copyBytes]

@[simp] theorem copyBytes_zero
    (data : List (BitVec 8)) (dataOffset : Nat) :
    copyBytes data dataOffset 0 = [] := by
  simp [copyBytes]

theorem copyBytes_get
    {data : List (BitVec 8)} {dataOffset size i : Nat}
    (h : i < size) :
    (copyBytes data dataOffset size)[i]'(by
      simpa [copyBytes_length] using h)
      = byte data (dataOffset + i) := by
  simp [copyBytes]

theorem copyBytes_get_of_in_bounds
    {data : List (BitVec 8)} {dataOffset size i : Nat}
    (h : i < size)
    (hsrc : dataOffset + i < data.length) :
    (copyBytes data dataOffset size)[i]'(by
      simpa [copyBytes_length] using h)
      = data[dataOffset + i] := by
  rw [copyBytes_get h, byte_of_lt hsrc]

theorem copyBytes_get_of_out_of_bounds
    {data : List (BitVec 8)} {dataOffset size i : Nat}
    (h : i < size)
    (hsrc : data.length ≤ dataOffset + i) :
    (copyBytes data dataOffset size)[i]'(by
      simpa [copyBytes_length] using h)
      = 0 := by
  rw [copyBytes_get h, byte_of_ge hsrc]

@[simp] theorem copyBytes_nil (dataOffset size : Nat) :
    copyBytes [] dataOffset size = List.replicate size 0 := by
  simp [copyBytes, List.map_const']

end ReturnData
end EvmAsm.Evm64
