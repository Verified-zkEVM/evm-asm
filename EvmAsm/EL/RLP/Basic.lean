/-
  EvmAsm.EL.RLP.Basic

  Core RLP (Recursive Length Prefix) types and encoding.
  Reference: Ethereum Yellow Paper, Appendix B.
-/

namespace EvmAsm.EL.RLP

abbrev Byte := BitVec 8

/-- An RLP item is either a byte string or a list of RLP items. -/
inductive RLPItem where
  | bytes : List Byte → RLPItem
  | list  : List RLPItem → RLPItem
  deriving Repr, BEq

mutual
private def RLPItem.decEq : (a b : RLPItem) → Decidable (a = b)
  | .bytes as, .bytes bs =>
    if h : as = bs then isTrue (by subst h; rfl)
    else isFalse (fun h' => h (RLPItem.bytes.inj h'))
  | .list as, .list bs =>
    match RLPItem.decEqList as bs with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (fun h' => h (RLPItem.list.inj h'))
  | .bytes _, .list _ => isFalse (fun h => by cases h)
  | .list _, .bytes _ => isFalse (fun h => by cases h)

private def RLPItem.decEqList : (a b : List RLPItem) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => by cases h)
  | _ :: _, [] => isFalse (fun h => by cases h)
  | a :: as, b :: bs =>
    match RLPItem.decEq a b, RLPItem.decEqList as bs with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h, _ => isFalse (fun h' => h (List.cons.inj h' |>.1))
    | _, isFalse h => isFalse (fun h' => h (List.cons.inj h' |>.2))
end

instance : DecidableEq RLPItem := RLPItem.decEq

/-! ## Big-endian natural number encoding -/

/-- Encode a natural number as minimal big-endian bytes. Zero maps to `[]`. -/
def Nat.toBytesBE : Nat → List Byte
  | 0 => []
  | n + 1 =>
    have : (n + 1) / 256 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by omega)
    Nat.toBytesBE ((n + 1) / 256) ++ [BitVec.ofNat 8 ((n + 1) % 256)]

/-- Decode big-endian bytes to a natural number. -/
def Nat.fromBytesBE : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat * 256 ^ bs.length + Nat.fromBytesBE bs

/-! ## RLP Encoding -/

/-- Encode the prefix and data for a byte string. -/
def encodeBytes (data : List Byte) : List Byte :=
  match data with
  | [b] =>
    if b.toNat < 0x80 then [b]
    else [BitVec.ofNat 8 0x81, b]
  | _ =>
    let len := data.length
    if len ≤ 55 then
      [BitVec.ofNat 8 (0x80 + len)] ++ data
    else
      let lenBytes := Nat.toBytesBE len
      [BitVec.ofNat 8 (0xB7 + lenBytes.length)] ++ lenBytes ++ data

/-- Encode an RLP item to bytes. -/
def encode : RLPItem → List Byte
  | .bytes data => encodeBytes data
  | .list items =>
    let payload := encodeItems items
    let len := payload.length
    if len ≤ 55 then
      [BitVec.ofNat 8 (0xC0 + len)] ++ payload
    else
      let lenBytes := Nat.toBytesBE len
      [BitVec.ofNat 8 (0xF7 + lenBytes.length)] ++ lenBytes ++ payload
where
  encodeItems : List RLPItem → List Byte
    | [] => []
    | item :: rest => encode item ++ encodeItems rest

end EvmAsm.EL.RLP
