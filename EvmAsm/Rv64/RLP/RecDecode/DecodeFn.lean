/-
  EvmAsm.Rv64.RLP.RecDecode.DecodeFn

  The recursive RLP decoder (#12419 fresh-tree track): one machine routine
  `rlp_decode(x10 = ptr, x11 = len, x12 = budget, x13 = fp)` mirroring the
  reference recursion of `ethereum_rlp` 0.1.6 as budgeted by
  `EL.RLP.Ref.decodeD`:

  * dispatch on the first byte (`decode`);
  * byte-string arms inline (`decode_to_bytes`: exact fit, canonicality,
    long-form length via the `rlp_read_be` leaf);
  * list arms: nesting-budget check, list-header frame checks
    (`decode_to_sequence`), then an in-place cursor loop over the payload
    (`decode_joined_encodings`) that computes each item's header length
    (`decode_item_length`) and **re-enters `rlp_decode` itself** on the
    item window at the decremented budget.

  Result: `x10 = 0` iff `decodeD budget (win bs off len)` accepts, else
  `x10 = 1`; `x13` restored.  The nesting budget is a runtime register and
  a ghost index — the cap is a parameter of the program and every theorem.

  Stack: one 32-byte frame per activation
  (`[ra][next-cursor][end][budget]`), so the arena for budget `d` is
  `32 * (d + 1)` bytes — constant once the cap is fixed, which is the
  constant-memory property the depth cap exists to provide.

  The routine is a *family* over ghosts `(bs, inBase, d, fp, off, len, v)`
  and two abstract callee handles (`beS`: the BE reader; `childS`: itself
  at budget `d - 1`, frame `fp + 32`); the flattened code is the same for
  every instantiation (`#guard`s below).
-/

import EvmAsm.Rv64.RLP.RecDecode.ReadBe
import EvmAsm.EL.RLP.RefDecodeStatus

namespace EvmAsm.Rv64
namespace SAsm
namespace RecDecode

open Stmt
open EvmAsm.EL.RLP (Byte)
open EvmAsm.EL.RLP.Ref (decodeD decodeJoinedEncodingsD win)

/-- Entry of the decoder. -/
def decEntry : Word := 0x1000

/-- Entry of the sibling-loop routine (`decode_joined_encodings`). -/
def itemsEntry : Word := 0x1400

/-- Entry of the BE length-field reader leaf. -/
def rdbeEntry : Word := 0x1800

/-- The status the machine reports for a window at a budget. -/
def decStatus (bs : List Byte) (off len d : Nat) : Word :=
  if (decodeD d (win bs off len)).isSome then 0 else 1

/-- The status of a joined-encodings window (the loop's exit value). -/
def itemsStatus (bs : List Byte) (off len d : Nat) : Word :=
  if (decodeJoinedEncodingsD d (win bs off len)).isSome then 0 else 1

/-- Long-form item header, byte-string base (`0xB8 ≤ cb ≤ 0xBF`): on
    success leaves `x17 = 1 + ll + value` with the fit against the remaining
    window pre-checked (so the add cannot wrap); on failure poisons
    (`x14 := 1`, `x15 := x16`).  Labels are literals — `vcgen`'s VC-spine
    whnf cannot afford `String.append` label expressions. -/
def itemLongFormB (beS : FnHandleS) : Stmt :=
  .block "ibll" [.ADDI .x7 .x5 (-0xB7)] ;;;
  .ite "ibtr" (.bltu .x7 .x6)
    (.block "ibb1" [.LBU .x31 .x15 1] ;;;
     .ite "ibz" (.beq .x31 .x0)
       (.block "ibpz" [.LI .x14 1, .MV .x15 .x16])
       (.block "ibargs" [.ADDI .x29 .x15 1, .MV .x30 .x7,
          .LI .x28 (0x1800 : Word)] ;;;
        .callRegS "ibbe" .x28 [beS] ;;;
        .block "ibrem" [.ADDI .x6 .x6 (-1), .SUB .x6 .x6 .x7] ;;;
        .ite "ibfit" (.bltu .x6 .x31)
          (.block "ibpf" [.LI .x14 1, .MV .x15 .x16])
          (.block "ibL" [.ADDI .x17 .x7 1, .ADD .x17 .x17 .x31])))
    (.block "ibpt" [.LI .x14 1, .MV .x15 .x16])

/-- Long-form item header, list base (`0xF8 ≤ cb`). -/
def itemLongFormL (beS : FnHandleS) : Stmt :=
  .block "illl" [.ADDI .x7 .x5 (-0xF7)] ;;;
  .ite "iltr" (.bltu .x7 .x6)
    (.block "ilb1" [.LBU .x31 .x15 1] ;;;
     .ite "ilz" (.beq .x31 .x0)
       (.block "ilpz" [.LI .x14 1, .MV .x15 .x16])
       (.block "ilargs" [.ADDI .x29 .x15 1, .MV .x30 .x7,
          .LI .x28 (0x1800 : Word)] ;;;
        .callRegS "ilbe" .x28 [beS] ;;;
        .block "ilrem" [.ADDI .x6 .x6 (-1), .SUB .x6 .x6 .x7] ;;;
        .ite "ilfit" (.bltu .x6 .x31)
          (.block "ilpf" [.LI .x14 1, .MV .x15 .x16])
          (.block "ilL" [.ADDI .x17 .x7 1, .ADD .x17 .x17 .x31])))
    (.block "ilpt" [.LI .x14 1, .MV .x15 .x16])

/-- The item-length cascade (`decode_item_length`): classifies the header
    byte at the cursor and leaves `x17 = L` (or poisons). -/
def itemLenCascade (beS : FnHandleS) : Stmt :=
  .block "ib0" [.LBU .x5 .x15 0, .SUB .x6 .x16 .x15, .LI .x7 0x80] ;;;
  .ite "i1" (.bltu .x5 .x7)
    (.block "iL1" [.LI .x17 1])
    (.block "ic1" [.LI .x7 0xB8] ;;;
     .ite "i2" (.bltu .x5 .x7)
       (.block "iL2" [.ADDI .x17 .x5 (-0x7F)])
       (.block "ic2" [.LI .x7 0xC0] ;;;
        .ite "i3" (.bltu .x5 .x7)
          (itemLongFormB beS)
          (.block "ic3" [.LI .x7 0xF8] ;;;
           .ite "i4" (.bltu .x5 .x7)
             (.block "iL4" [.ADDI .x17 .x5 (-0xBF)])
             (itemLongFormL beS))))

/-- The guarded tail of a loop iteration: fit check, recursive call on the
    item window, advance. -/
def itemCallTail (childS : FnHandleS) : Stmt :=
  .ite "pz" (.beq .x14 .x0)
    (.block "fit0" [.SUB .x6 .x16 .x15] ;;;
     .ite "ifit" (.bltu .x6 .x17)
       (.block "st_unfit" [.LI .x14 1, .MV .x15 .x16])
       (.block "spill" [.ADD .x7 .x15 .x17, .SD .x13 .x7 8,
          .SD .x13 .x16 16, .SD .x13 .x12 24, .MV .x10 .x15,
          .MV .x11 .x17, .ADDI .x13 .x13 32,
          .LI .x28 (0x1000 : Word)] ;;;
        .callRegS "child" .x28 [childS] ;;;
        .block "reload" [.ADDI .x13 .x13 (-32), .LD .x15 .x13 8,
          .LD .x16 .x13 16, .LD .x12 .x13 24] ;;;
        .ite "chst" (.beq .x10 .x0)
          (.block "chok" [.LI .x14 0])
          (.block "st_child" [.LI .x14 1, .MV .x15 .x16])))
    (.block "nopz" [])

/-- One iteration of the sibling loop. -/
def itemsBodyStmt (beS childS : FnHandleS) : Stmt :=
  itemLenCascade beS ;;; itemCallTail childS

/-- The sibling-loop routine's body (`decode_joined_encodings`): enter with
    `x15` = payload start pointer, `x16` = payload end pointer, `x12` =
    budget, `x13` = own frame pointer.  Exits with `x10` = 0 (all items
    accepted, cursor at end) or `x10` = 1. -/
def itemsBody (fuel : Nat)
    (inv : Nat → RegFile → List (BitVec 8) → Assertion → Prop)
    (beS childS : FnHandleS) : Stmt :=
  .block "linit" [.LI .x14 0] ;;;
  .«while» "iloop" (.bltu .x15 .x16) fuel inv (itemsBodyStmt beS childS) ;;;
  .block "iret" [.MV .x10 .x14]

/-- Single-byte sub-arm (`b0 < 0x80`): accept iff the window is exactly
    one byte. -/
def byteSingleArm : Stmt :=
  .block "chk1" [.LI .x6 1] ;;;
  .ite "len1" (.beq .x11 .x6)
    (.block "st_ok1" [.LI .x14 0])
    (.block "st_bad1" [.LI .x14 1])

/-- Short byte-string sub-arm (`0x80 ≤ b0 ≤ 0xB7`): exact fit and the
    single-byte canonicality re-check. -/
def byteShortArm : Stmt :=
  .block "sb" [.ADDI .x7 .x5 (-0x80), .ADDI .x6 .x7 1] ;;;
  .ite "sbfit" (.beq .x6 .x11)
    (.block "sb1" [.LI .x6 1] ;;;
     .ite "sbcanon" (.beq .x7 .x6)
       (.block "sbb1" [.LBU .x6 .x10 1, .LI .x7 0x80] ;;;
        .ite "sbc2" (.bltu .x6 .x7)
          (.block "st_noncanon" [.LI .x14 1])
          (.block "st_ok2" [.LI .x14 0]))
       (.block "st_ok3" [.LI .x14 0]))
    (.block "st_bad2" [.LI .x14 1])

/-- Long byte-string sub-arm (`0xB8 ≤ b0 ≤ 0xBF`): length-of-length in
    range, nonzero first length byte, value via the leaf, canonical and
    exact fit. -/
def byteLongArm (beS : FnHandleS) : Stmt :=
  .block "lb" [.ADDI .x7 .x5 (-0xB7)] ;;;
  .ite "lbtr" (.bltu .x7 .x11)
    (.block "lbb1" [.LBU .x6 .x10 1] ;;;
     .ite "lbz" (.beq .x6 .x0)
       (.block "st_lz" [.LI .x14 1])
       (.block "lbargs" [.ADDI .x29 .x10 1, .MV .x30 .x7,
          .LI .x28 (0x1800 : Word)] ;;;
        .callRegS "lbbe" .x28 [beS] ;;;
        .block "lbc" [.LI .x6 0x38] ;;;
        .ite "lbsmall" (.bltu .x31 .x6)
          (.block "st_small" [.LI .x14 1])
          (.block "lbfit" [.ADDI .x6 .x11 (-1), .SUB .x6 .x6 .x7] ;;;
           .ite "lbfit2" (.beq .x31 .x6)
             (.block "st_okL" [.LI .x14 0])
             (.block "st_badL" [.LI .x14 1]))))
    (.block "st_tr" [.LI .x14 1])

/-- All byte-string arms (`b0 ≤ 0xBF`). -/
def bytesArm (beS : FnHandleS) : Stmt :=
  .block "c80" [.LI .x6 0x80] ;;;
  .ite "single" (.bltu .x5 .x6)
    byteSingleArm
    (.block "cB8" [.LI .x6 0xB8] ;;;
     .ite "shortb" (.bltu .x5 .x6)
       byteShortArm
       (byteLongArm beS))

/-- Short list header (`0xC0 ≤ b0 ≤ 0xF7`): on exact fit, set the payload
    window (`x15`/`x16`) and clear the status; otherwise poison. -/
def listShortHdr : Stmt :=
  .block "sl" [.ADDI .x7 .x5 (-0xC0), .ADDI .x6 .x7 1] ;;;
  .ite "slfit" (.beq .x6 .x11)
    (.block "slgo" [.ADDI .x15 .x10 1, .ADD .x16 .x15 .x7, .LI .x14 0])
    (.block "st_badSL" [.LI .x14 1])

/-- Long list header (`0xF8 ≤ b0`): length-of-length in range, nonzero
    first length byte, value via the leaf, canonical, exact fit; on
    success set the payload window and clear the status. -/
def listLongHdr (beS : FnHandleS) : Stmt :=
  .block "ll" [.ADDI .x7 .x5 (-0xF7)] ;;;
  .ite "lltr" (.bltu .x7 .x11)
    (.block "llb1" [.LBU .x6 .x10 1] ;;;
     .ite "llz" (.beq .x6 .x0)
       (.block "st_llz" [.LI .x14 1])
       (.block "llargs" [.ADDI .x29 .x10 1, .MV .x30 .x7,
          .LI .x28 (0x1800 : Word)] ;;;
        .callRegS "llbe" .x28 [beS] ;;;
        .block "llc" [.LI .x6 0x38] ;;;
        .ite "llsmall" (.bltu .x31 .x6)
          (.block "st_llsmall" [.LI .x14 1])
          (.block "llfit" [.ADDI .x6 .x11 (-1), .SUB .x6 .x6 .x7] ;;;
           .ite "llfit2" (.beq .x31 .x6)
             (.block "llgo" [.ADDI .x15 .x10 1, .ADD .x15 .x15 .x7,
                .ADD .x16 .x15 .x31, .LI .x14 0])
             (.block "st_badLL" [.LI .x14 1]))))
    (.block "st_lltr" [.LI .x14 1])

/-- All list arms (`b0 ≥ 0xC0`): budget first, then frame checks, then —
    if the header was accepted — call the sibling-loop routine on the
    payload window at the decremented budget. -/
def listArm (itemsS : FnHandleS) (beS : FnHandleS) : Stmt :=
  (Stmt.ite "bud" (.beq .x12 .x0)
    (.block "st_deep" [.LI .x14 1])
    (.block "budm" [.ADDI .x12 .x12 (-1), .LI .x6 0xF8] ;;;
     .ite "listd" (.bltu .x5 .x6)
       listShortHdr
       (listLongHdr beS))) ;;;
  .ite "lgo" (.beq .x14 .x0)
    (.block "goitems" [.ADDI .x13 .x13 8, .LI .x28 (0x1400 : Word)] ;;;
     .callRegS "items" .x28 [itemsS] ;;;
     .block "backitems" [.MV .x14 .x10, .ADDI .x13 .x13 (-8)])
    (.block "nol" [])

/-- The decoder body (statement tree); status accumulates in `x14`, moved
    to `x10` at the single exit. -/
def decBody (beS itemsS : FnHandleS) : Stmt :=
  (Stmt.ite "empty" (.beq .x11 .x0)
    (.block "st_empty" [.LI .x14 1])
    (.block "b0" [.LBU .x5 .x10 0, .LI .x6 0xC0] ;;;
     .ite "disp" (.bltu .x5 .x6)
       (bytesArm beS)
       (listArm itemsS beS))) ;;;
  .block "ret" [.MV .x10 .x14]

/-- A dead handle shaped like a callee at the given regions (for the
    budget-0 instantiation, where the recursive call site is unreachable,
    and for pinning the flattened code). -/
def deadHandleS (reg : Region) (rw : RwRegion) : FnHandleS where
  entry := decEntry
  code := CodeReq.empty
  nSteps := 0
  region := reg
  rw := rw
  pre := fun _ _ _ => False
  post := fun _ _ _ _ _ _ => False
  sound := fun _ _ _ _ _ hpre => hpre.elim

def decFnPin : Fn where
  name := "rlpdec"
  region := Region.empty
  rw := RwRegion.empty
  pre := fun _ _ _ => True
  post := fun _ _ _ => True
  body := decBody (deadHandleS Region.empty RwRegion.empty)
    (deadHandleS Region.empty RwRegion.empty)

def itemsFnPin : Fn where
  name := "rlpitems"
  region := Region.empty
  rw := RwRegion.empty
  pre := fun _ _ _ => True
  post := fun _ _ _ => True
  body := itemsBody 0 (fun _ _ _ _ => True)
    (deadHandleS Region.empty RwRegion.empty)
    (deadHandleS Region.empty RwRegion.empty)

/-- The decoder's program (`ra` spilled at `x13+0`), placed at `decEntry`. -/
def decProg : Program := decFnPin.programRetR .x13 0 decEntry

/-- The loop routine's program, placed at `itemsEntry`. -/
def itemsProg : Program := itemsFnPin.programRetR .x13 0 itemsEntry

#guard decProg.length = 106
#guard itemsProg.length = 93
#guard 0x1000 + 4 * decProg.length ≤ 0x1400
#guard 0x1400 + 4 * itemsProg.length ≤ 0x1800

/-- The leaf's program, placed at `rdbeEntry`. -/
def rdbeProg : Program :=
  (readBeFn 0 [] 0 0).programRet rdbeEntry

#guard rdbeProg.length = 9

/-- The ambient code requirement: decoder at `0x1000`, sibling loop at
    `0x1400`, leaf at `0x1800`. -/
def decCr : CodeReq :=
  ((CodeReq.ofProg decEntry decProg).union
    (CodeReq.ofProg itemsEntry itemsProg)).union
    (CodeReq.ofProg rdbeEntry rdbeProg)

end RecDecode
end SAsm
end EvmAsm.Rv64
