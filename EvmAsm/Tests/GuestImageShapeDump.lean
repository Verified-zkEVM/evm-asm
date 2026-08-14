/-
  EvmAsm.Tests.GuestImageShapeDump

  Dumps the control-flow shape of every routine in the guest image `CodeReq`,
  read from the **Lean `Program`s themselves** — `guestImageEntries`, the same
  (address, `_prog`) pairs that define `guestImageCodeReq`.

  ## Why this exists rather than reusing `scripts/shape-census.py`

  That census parses the emitted `*Function : String` defs as assembly text, and
  it is **structurally blind to every converted routine**. A routine's `Function`
  string is literal asm only while it is UNCONVERTED:

      -- unconverted: asm text the census can read
      def precompileSharedSelectPriceFunction : String :=
        "precompile_shared_select_price:\n" ++
        "  la t0, precompile_shared_selector\n  sd zero, 0(t0)\n" ++ …

      -- converted: no asm text at all, just a label plus a Program reference
      def secfEq32Function : String :=
        "secf_eq32:\n" ++ emitProgram secfEq32_prog

  Conversion is exactly what earns a routine a Lean `Program`, hence a
  `guestImageEntries` pairing, hence linkage into the image. So the census can
  only see the shape of routines that CANNOT carry a row, and is blind to every
  routine that can. Measured on this tree: of 984 emitted `*Function` defs, 565
  parse to ZERO instructions, and of the 449 linked symbols exactly **one** has
  readable asm text.

  ⚠️ That also makes a zero-instruction body indistinguishable from a
  branch-free one: no instructions means no branches, so the census files it as a
  "flat block". Any shape claim about IN-IMAGE routines taken from that tool is
  unfounded — including population figures derived from it.

  Output is TSV on stdout, one line per entry, consumed by
  `scripts/callee-composition-queue.py`:

      <entryAddrHex>\t<numInstrs>\t<numBackEdges>\t<callTargetHex,…>

  A back-edge is a branch or `JAL` whose signed byte offset is negative (a
  target at or before the transferring instruction) — i.e. a loop. A call is a
  `JAL` whose resolved target lies OUTSIDE this routine's own extent; a `JAL`
  landing inside the routine is intra-routine control flow, not a callee.
-/

import EvmAsm.Codegen.Proofs.GuestImageEntries

namespace EvmAsm.Tests.GuestImageShapeDump

open EvmAsm.Rv64
open EvmAsm.Codegen

/-- Signed byte displacement of a control-transfer instruction, if it has one.
    `JALR` is deliberately `none`: its target is a register value, not a
    displacement, so it is neither a resolvable call nor a decidable back-edge
    here. Routines containing one are reported with a call target of `?` by the
    consumer rather than silently treated as straight-line. -/
def transferOffset : Instr → Option Int
  | .BEQ  _ _ off => some off.toInt
  | .BNE  _ _ off => some off.toInt
  | .BLT  _ _ off => some off.toInt
  | .BGE  _ _ off => some off.toInt
  | .BLTU _ _ off => some off.toInt
  | .BGEU _ _ off => some off.toInt
  | .JAL  _   off => some off.toInt
  | _             => none

/-- Is this a `JAL` (the call/jump form whose target we can resolve)? -/
def isJal : Instr → Bool
  | .JAL _ _ => true
  | _        => false

/-- Does this routine contain a GENUINELY indirect jump — one whose target is not
    statically known from the `Program` alone?

    ⚠️ `JALR x0 x1 0` is excluded: that is `ret`, and every routine in the image
    ends with one, so counting it would mark all 449 entries indirect and make the
    flag useless. A first run of this dump did exactly that. The remaining `JALR`s
    are real computed jumps (jump tables, dispatch on a loaded pointer). -/
def isRet : Instr → Bool
  | .JALR .x0 .x1 off => off == 0
  | _                 => false

def hasIndirect (prog : Program) : Bool :=
  prog.any fun i => match i with
    | .JALR _ _ _ => !isRet i
    | _           => false

/-- Shape of one image entry: instruction count, back-edge count, resolved
    out-of-extent `JAL` targets, and whether an indirect jump is present. -/
def shapeOf (entryAddr : Nat) (prog : Program) :
    Nat × Nat × List Nat × Bool :=
  let n := prog.length
  let extentEnd := entryAddr + 4 * n
  let step : (Nat × Nat × List Nat) → Instr → (Nat × Nat × List Nat) :=
    fun (idx, back, calls) instr =>
      let pc := entryAddr + 4 * idx
      match transferOffset instr with
      | none => (idx + 1, back, calls)
      | some off =>
        -- `JAL rd off` and the branches all set PC := pc + signExtend off.
        let tgt : Int := (pc : Int) + off
        let back' := if off < 0 then back + 1 else back
        let calls' :=
          if isJal instr && (tgt < (entryAddr : Int) || tgt ≥ (extentEnd : Int))
          then (if tgt ≥ 0 then tgt.toNat :: calls else calls)
          else calls
        (idx + 1, back', calls')
  let (_, back, calls) := prog.foldl step (0, 0, [])
  (n, back, calls.reverse, hasIndirect prog)

/-- One TSV line per image entry. -/
def dumpLine (e : Nat × Program) : String :=
  let (n, back, calls, indirect) := shapeOf e.1 e.2
  let callStr := String.intercalate "," (calls.map fun a => toString a)
  s!"{e.1}\t{n}\t{back}\t{if indirect then "1" else "0"}\t{callStr}"

def dump : String :=
  String.intercalate "\n" (guestImageEntries.map dumpLine)

end EvmAsm.Tests.GuestImageShapeDump
