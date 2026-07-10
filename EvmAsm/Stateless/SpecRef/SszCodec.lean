/-
  EvmAsm.Stateless.SpecRef.SszCodec

  A generic, executable SSZ engine for the stateless-guest reference port:
  a value model (`SszValue`), a type descriptor for type-directed decoding
  (`SszType`), and the three operations the Python shell depends on:

  * `serialize`      — `remerkleable`'s `.encode_bytes()`
  * `deserialize`    — `remerkleable`'s `.decode_bytes(ty, …)`
  * `hashTreeRoot`   — `remerkleable`'s `.hash_tree_root()`

  Nothing pure-Lean for this existed in the repo (only SAsm emitters and
  doc-only contracts under `EvmAsm/Stateless/SSZ/`), so this is a fresh
  port of the SSZ spec
  (https://github.com/ethereum/consensus-specs/blob/dev/ssz/simple-serialize.md),
  built on the sha256 in `Crypto.lean`.

  Recursion over the (finite, shallow) SSZ schema uses the repo's explicit
  fuel convention (cf. `powModAux` in `EvmAsm/Rv64/ZiskAccel.lean`): the
  fuel bounds *type-nesting depth* (not element count), so a small constant
  budget is always sufficient and the definitions stay kernel-reducible.
-/

import EvmAsm.Stateless.SpecRef.Types

namespace EvmAsm.Stateless.SpecRef

/-- Depth budget for SSZ recursion. The deepest schema
    (`SszStatelessInput`) nests ~7 levels; 64 is comfortably safe. -/
def sszFuel : Nat := 64

/-- SSZ length-offset width (`BYTES_PER_LENGTH_OFFSET`). -/
def sszOffsetSize : Nat := 4

/-! ## Value and type models -/

/-- An SSZ value. `byteVector` carries its bytes (its length is implicit);
    `list` carries `elemBasicSize = some sz` when its elements are a basic
    type (packed during merkleization) or `none` for composite elements
    (one Merkle root per element). -/
inductive SszValue where
  | uint (width : Nat) (val : Nat)
  | bool (b : Bool)
  | byteVector (data : Bytes)
  | byteList (limit : Nat) (data : Bytes)
  | container (fields : List SszValue)
  | list (limit : Nat) (elemBasicSize : Option Nat) (elems : List SszValue)
  deriving Repr, Inhabited

/-- An SSZ type descriptor, used to drive `deserialize`. -/
inductive SszType where
  | uint (width : Nat)
  | bool
  | byteVector (len : Nat)
  | byteList (limit : Nat)
  | container (fields : List SszType)
  | list (elem : SszType) (limit : Nat)
  deriving Repr, Inhabited

/-! ## Structural predicates on types -/

/-- Whether an SSZ type is variable-size. Fuel bounds type-nesting depth. -/
def SszType.isVariableAux : Nat → SszType → Bool
  | 0, _ => false
  | _ + 1, .uint _ => false
  | _ + 1, .bool => false
  | _ + 1, .byteVector _ => false
  | _ + 1, .byteList _ => true
  | _ + 1, .list _ _ => true
  | f + 1, .container fields => fields.any (fun t => SszType.isVariableAux f t)

def SszType.isVariable (t : SszType) : Bool := SszType.isVariableAux sszFuel t

/-- Fixed byte size of a fixed-size SSZ type (meaningless for variable
    types, where the offset slot size `sszOffsetSize` is used instead). -/
def SszType.fixedSizeAux : Nat → SszType → Nat
  | 0, _ => 0
  | _ + 1, .uint w => w
  | _ + 1, .bool => 1
  | _ + 1, .byteVector n => n
  | _ + 1, .byteList _ => 0
  | _ + 1, .list _ _ => 0
  | f + 1, .container fields =>
      (fields.map (fun t =>
        if SszType.isVariableAux f t then sszOffsetSize
        else SszType.fixedSizeAux f t)).foldl (· + ·) 0

def SszType.fixedSize (t : SszType) : Nat := SszType.fixedSizeAux sszFuel t

/-- The basic-type element size, if `t` is a basic type (`uint`/`bool`). -/
def SszType.basicSize? : SszType → Option Nat
  | .uint w => some w
  | .bool => some 1
  | _ => none

/-! ## Serialization (`encode_bytes`) -/

/-- Whether a value is variable-size (for offset layout). -/
def SszValue.isVariableAux : Nat → SszValue → Bool
  | 0, _ => false
  | _ + 1, .uint _ _ => false
  | _ + 1, .bool _ => false
  | _ + 1, .byteVector _ => false
  | _ + 1, .byteList _ _ => true
  | _ + 1, .list _ _ _ => true
  | f + 1, .container fields => fields.any (fun v => SszValue.isVariableAux f v)

def SszValue.isVariable (v : SszValue) : Bool := SszValue.isVariableAux sszFuel v

/-- Serialize a value. Fuel bounds nesting depth. -/
def SszValue.serializeAux : Nat → SszValue → Bytes
  | 0, _ => []
  | _ + 1, .uint width val => natToBytesLE width val
  | _ + 1, .bool b => [if b then (1 : Byte) else 0]
  | _ + 1, .byteVector data => data
  | _ + 1, .byteList _ data => data
  | f + 1, .container fields => serializeSeq f fields
  | f + 1, .list _ _ elems => serializeSeq f elems
where
  /-- Serialize a heterogeneous element sequence with the SSZ fixed part
      (values + 4-byte offsets) followed by the concatenated variable
      parts. -/
  serializeSeq (f : Nat) (elems : List SszValue) : Bytes :=
    let parts : List (Bool × Bytes) :=
      elems.map (fun e => (SszValue.isVariable e, SszValue.serializeAux f e))
    let fixedLen :=
      (parts.map (fun p => if p.1 then sszOffsetSize else p.2.length)).foldl (· + ·) 0
    let fixedRegion : Bytes :=
      (parts.foldl (fun (acc : Bytes × Nat) p =>
        if p.1 then (acc.1 ++ natToBytesLE sszOffsetSize acc.2, acc.2 + p.2.length)
        else (acc.1 ++ p.2, acc.2)) ([], fixedLen)).1
    let varRegion : Bytes :=
      (parts.filterMap (fun p => if p.1 then some p.2 else none)).flatten
    fixedRegion ++ varRegion

def SszValue.serialize (v : SszValue) : Bytes := SszValue.serializeAux sszFuel v

/-! ## Deserialization (`decode_bytes`) -/

/-- `data[start .. stop)` (clamped). -/
def sliceBytes (data : Bytes) (start stop : Nat) : Bytes :=
  (data.drop start).take (stop - start)

/-- Read a little-endian offset (`sszOffsetSize` bytes) at `pos`. -/
def readOffset (data : Bytes) (pos : Nat) : Nat :=
  bytesLEtoNat ((data.drop pos).take sszOffsetSize)

/-- Ceil-div by 32 (chunk count for `len` bytes). -/
def chunkCount (len : Nat) : Nat := (len + 31) / 32

/-- One field parsed from a container's fixed region: either its raw
    fixed bytes (`Sum.inl`) or its variable-part offset (`Sum.inr`). -/
abbrev Head := SszType × (Bytes ⊕ Nat)

/-- Walk the fixed region collecting per-field fixed bytes or offsets. -/
def collectHeads (data : Bytes) : List SszType → Nat → List Head
  | [], _ => []
  | t :: rest, cur =>
    if t.isVariable then
      (t, Sum.inr (readOffset data cur)) :: collectHeads data rest (cur + sszOffsetSize)
    else
      let sz := t.fixedSize
      (t, Sum.inl (sliceBytes data cur (cur + sz))) :: collectHeads data rest (cur + sz)

/-- Assign each head its byte slice; variable heads span from their offset
    to the next variable offset (or end of `data`). -/
def headsToSegments (data : Bytes) : List Head → List Nat → List (SszType × Bytes)
  | [], _ => []
  | (t, Sum.inl b) :: rest, stops => (t, b) :: headsToSegments data rest stops
  | (t, Sum.inr off) :: rest, stop :: stops =>
      (t, sliceBytes data off stop) :: headsToSegments data rest stops
  | (t, Sum.inr off) :: rest, [] =>
      (t, sliceBytes data off data.length) :: headsToSegments data rest []

/-- SSZ offsets must be nondecreasing. -/
def offsetsNondecreasing : List Nat → Bool
  | [] | [_] => true
  | a :: b :: rest => a ≤ b && offsetsNondecreasing (b :: rest)

/-- Deserialize a value of type `t` from exactly `data`. Fuel bounds
    type-nesting depth. -/
def deserializeAux : Nat → SszType → Bytes → Except SpecError SszValue
  | 0, _, _ => .error (.sszError "ssz decode fuel exhausted")
  | f + 1, t, data =>
    match t with
    | .uint w =>
        if data.length = w then .ok (.uint w (bytesLEtoNat data))
        else .error (.sszError s!"uint{w} wrong length {data.length}")
    | .bool =>
        match data with
        | [b] =>
            if b.toNat ≤ 1 then .ok (.bool (b.toNat = 1))
            else .error (.sszError "boolean out of range")
        | _ => .error (.sszError "boolean wrong length")
    | .byteVector n =>
        if data.length = n then .ok (.byteVector data)
        else .error (.sszError s!"byte vector wrong length {data.length} ≠ {n}")
    | .byteList lim =>
        if data.length ≤ lim then .ok (.byteList lim data)
        else .error (.sszError "byte list over limit")
    | .container fields =>
        let fixedLen := t.fixedSize
        if data.length < fixedLen then
          .error (.sszError "container shorter than fixed section")
        else
          let heads := collectHeads data fields 0
          let varOffsets := heads.filterMap (fun h =>
            match h.2 with | Sum.inr o => some o | _ => none)
          if varOffsets.any (fun off => off < fixedLen || data.length < off)
              || !offsetsNondecreasing varOffsets
              || (varOffsets != [] && varOffsets.getD 0 fixedLen != fixedLen) then
            .error (.sszError "invalid container offsets")
          else
            let stops := varOffsets.drop 1 ++ [data.length]
            let segs := headsToSegments data heads stops
            (segs.mapM (fun s => deserializeAux f s.1 s.2)).map SszValue.container
    | .list elem lim =>
        if elem.isVariable then
          match data with
          | [] => .ok (.list lim elem.basicSize? [])
          | _ =>
              let firstOff := readOffset data 0
              let count := firstOff / sszOffsetSize
              let offsets := (List.range count).map (fun i => readOffset data (i * sszOffsetSize))
              if firstOff = 0 || firstOff % sszOffsetSize != 0 || data.length < firstOff
                  || count > lim || offsets.getD 0 firstOff != firstOff
                  || offsets.any (fun off => off < firstOff || data.length < off)
                  || !offsetsNondecreasing offsets then
                .error (.sszError "invalid variable-list offsets")
              else
                let stops := offsets.drop 1 ++ [data.length]
                let segs := (offsets.zip stops).map (fun p => sliceBytes data p.1 p.2)
                (segs.mapM (fun b => deserializeAux f elem b)).map
                  (fun vs => .list lim elem.basicSize? vs)
        else
          let sz := elem.fixedSize
          if sz = 0 then .error (.sszError "zero-size list element")
          else
            let count := data.length / sz
            if data.length % sz != 0 then .error (.sszError "fixed-list trailing bytes")
            else if count > lim then .error (.sszError "list over limit")
            else
              let segs := (List.range count).map (fun i => sliceBytes data (i * sz) (i * sz + sz))
              (segs.mapM (fun b => deserializeAux f elem b)).map
                (fun vs => .list lim elem.basicSize? vs)

def deserialize (t : SszType) (data : Bytes) : Except SpecError SszValue :=
  deserializeAux sszFuel t data

/-! ## Merkleization (`hash_tree_root`) -/

/-- The all-zero 32-byte chunk (`Z_0`). -/
def zeroChunk : Bytes := List.replicate 32 (0 : Byte)

/-- Pack bytes into right-zero-padded 32-byte chunks. -/
def packBytesAux : Nat → Bytes → List Bytes
  | 0, _ => []
  | _, [] => []
  | fuel + 1, data =>
      let chunk := data.take 32
      (chunk ++ List.replicate (32 - chunk.length) (0 : Byte)) :: packBytesAux fuel (data.drop 32)

def packBytes (data : Bytes) : List Bytes := packBytesAux (data.length + 1) data

/-- SSZ zero hash at depth `d`: `Z_0 = 0…0`, `Z_{i+1} = sha256(Z_i ‖ Z_i)`.
    Lets merkleization skip all-zero padding subtrees in `O(depth)` instead
    of materializing `2^depth` leaves (essential — real SSZ capacities reach
    `2^24`). -/
def zeroHash : Nat → Bytes
  | 0 => zeroChunk
  | d + 1 => let z := zeroHash d; sha256Pair z z

/-- Ceil log2: smallest `d` with `2^d ≥ n` (with `ceilLog2 0 = 0`). -/
def ceilLog2Aux : Nat → Nat → Nat → Nat
  | 0, _, d => d
  | f + 1, n, d => if 2 ^ d ≥ n then d else ceilLog2Aux f n (d + 1)

def ceilLog2 (n : Nat) : Nat := ceilLog2Aux 64 (max n 1) 0

/-- Pair-hash adjacent chunks once (halving a power-of-two-length list). -/
def pairReduce : List Bytes → List Bytes
  | [] => []
  | [a] => [a]
  | a :: b :: rest => sha256Pair a b :: pairReduce rest

/-- Reduce a power-of-two leaf list to its Merkle root. -/
def merkleizeReduce : Nat → List Bytes → Bytes
  | 0, leaves => leaves.headD zeroChunk
  | _, [] => zeroChunk
  | _, [x] => x
  | f + 1, leaves => merkleizeReduce f (pairReduce leaves)

/-- Lift `partial` (root of a populated subtree at `cur` depth) up to
    `target` depth by pair-hashing with the zero-subtree root at each level
    (the right sibling above the populated region is all zeros = `Z_d`). -/
def liftToDepth : Nat → Bytes → Nat → Nat → Bytes
  | 0, part, _, _ => part
  | f + 1, part, cur, target =>
      if cur ≥ target then part
      else liftToDepth f (sha256Pair part (zeroHash cur)) (cur + 1) target

/-- SSZ `merkleize(chunks, limit)`: the root of a depth-`ceil(log2 limit)`
    perfect tree whose first `chunks.length` leaves are `chunks` and the rest
    are zero. Only the populated part is materialized; the zero upper region
    is folded in via `zeroHash` (`O(n + log limit)`). -/
def merkleize (chunks : List Bytes) (limitChunks : Nat) : Bytes :=
  let target := max (ceilLog2 limitChunks) (ceilLog2 chunks.length)
  match chunks with
  | [] => zeroHash target
  | _ =>
      let pd := ceilLog2 chunks.length
      let padded := chunks ++ List.replicate (2 ^ pd - chunks.length) zeroChunk
      let part := merkleizeReduce (2 ^ pd + 1) padded
      liftToDepth (target + 1) part pd target

/-- SSZ `mix_in_length(root, length)`. -/
def mixInLength (root : Bytes) (length : Nat) : Bytes :=
  sha256Pair root (natToBytesLE 32 length)

/-- `hash_tree_root(value)`. Fuel bounds nesting depth. -/
def SszValue.hashTreeRootAux : Nat → SszValue → Bytes
  | 0, _ => zeroChunk
  | _ + 1, .uint _ val => natToBytesLE 32 val
  | _ + 1, .bool b => (if b then (1 : Byte) else 0) :: List.replicate 31 (0 : Byte)
  | _ + 1, .byteVector data => merkleize (packBytes data) (chunkCount data.length)
  | _ + 1, .byteList lim data =>
      mixInLength (merkleize (packBytes data) (chunkCount lim)) data.length
  | f + 1, .container fields =>
      merkleize (fields.map (fun v => SszValue.hashTreeRootAux f v)) fields.length
  | f + 1, .list lim elemBasicSize elems =>
      match elemBasicSize with
      | some sz =>
          -- basic-element list: pack serialized elements, mix in the count
          let packed := packBytes (elems.flatMap SszValue.serialize)
          mixInLength (merkleize packed (chunkCount (lim * sz))) elems.length
      | none =>
          -- composite-element list: one root per element, mix in the count
          mixInLength (merkleize (elems.map (fun v => SszValue.hashTreeRootAux f v)) lim)
            elems.length

def SszValue.hashTreeRoot (v : SszValue) : Bytes := SszValue.hashTreeRootAux sszFuel v

end EvmAsm.Stateless.SpecRef
