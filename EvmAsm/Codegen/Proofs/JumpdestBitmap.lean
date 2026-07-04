/-
  EvmAsm.Codegen.Proofs.JumpdestBitmap

  The jumpdest-bitmap prologue's build loop (bead `evm-asm-cfjzu`, child of
  `.49.2`).  The dispatcher precomputes, once before the main loop, a bit per
  code byte marking the valid JUMPDEST positions (`emitJumpdestBitmapBuild`,
  `Dispatch.lean:142-206`); JUMP/JUMPI then test one bit in O(1).

  This module proves the loop's triple against the SpecRef anchor
  `validJumpDestinations` (EvmAsm/Stateless/SpecRef/Runtime.lean): the built
  bitmap's bit `idx` is set iff `idx` is a valid jump destination.

  L3 (the bit/byte layer) lives here: `bitmapBit` reads the logical bit `idx`
  out of the byte-list `ws`, `bitmapBit_setBit` is the read-modify-write step
  (`lbu; or; sb` sets exactly bit `pc`), and `bitmapBit_replicate_zero` is the
  loader-zeroed initial state.  The spec-side boundary-walk layer (L1) is in
  `SpecRef.Runtime` (`walkFrom`, `Reaches`, `vjd_lt_step`).
-/

import EvmAsm.Rv64.MemRegionWriteWide
import EvmAsm.Rv64.SAsm.LoopFuel
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Stateless.SpecRef.Runtime

namespace EvmAsm.Codegen.Proofs.JumpdestBitmap

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt EvmAsm.Stateless.SpecRef

/-! ## L3 — the bitmap bit/byte layer

The bitmap is a `List (BitVec 8)`; logical bit `idx` is bit `idx % 8` of byte
`idx / 8`. -/

/-- Logical bit `idx` of a byte-list bitmap: bit `idx % 8` of byte `idx / 8`. -/
def bitmapBit (ws : List (BitVec 8)) (idx : Nat) : Bool :=
  (ws.getD (idx / 8) 0).getLsbD (idx % 8)

private theorem getD_set_self {l : List (BitVec 8)} {i : Nat} {b d : BitVec 8}
    (h : i < l.length) : (l.set i b).getD i d = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]; rfl

private theorem getD_set_ne {l : List (BitVec 8)} {i j : Nat} {b d : BitVec 8}
    (h : i ≠ j) : (l.set i b).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h, List.getD_eq_getElem?_getD]

/-- The single-bit mask `1 <<< k` has bit `j` set iff `j = k` (for `j < 8`). -/
private theorem mask_getLsbD (j k : Nat) (hj : j < 8) :
    ((1 : BitVec 8) <<< k).getLsbD j = decide (j = k) := by
  rw [BitVec.getLsbD_shiftLeft]; simp only [hj, decide_true, Bool.true_and]
  by_cases h : j < k <;> simp [h] <;> omega

/-- **L3 — the read-modify-write step.**  The `lbu; or; sb` sequence at code
    position `pc` (load byte `pc / 8`, or in bit `pc % 8`, store back) sets
    exactly logical bit `pc` of the bitmap and leaves every other bit alone. -/
theorem bitmapBit_setBit (ws : List (BitVec 8)) (pc idx : Nat)
    (hlen : pc / 8 < ws.length) :
    bitmapBit (ws.set (pc / 8) (ws.getD (pc / 8) 0 ||| ((1 : BitVec 8) <<< (pc % 8)))) idx
      = (decide (idx = pc)) || bitmapBit ws idx := by
  unfold bitmapBit
  by_cases hbyte : idx / 8 = pc / 8
  · rw [hbyte, getD_set_self hlen, BitVec.getLsbD_or,
      mask_getLsbD _ _ (Nat.mod_lt _ (by omega))]
    have hd : (idx = pc) ↔ (idx % 8 = pc % 8) := by omega
    cases (ws.getD (pc / 8) 0).getLsbD (idx % 8) <;> simp [hd, Bool.or_comm]
  · have hne : idx ≠ pc := by omega
    rw [getD_set_ne (Ne.symm hbyte)]; simp [hne]

/-- The loader-zeroed bitmap has every logical bit clear. -/
theorem bitmapBit_replicate_zero (n idx : Nat) :
    bitmapBit (List.replicate n 0) idx = false := by
  simp only [bitmapBit, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  by_cases h : idx / 8 < n <;> simp [h]

/-! ## The scan loop

`bitmapBytes`/`bitmapCap` mirror `Dispatch.jumpdestBitmapBytes` (16384) and
`jumpdestBitmapCodeCapacity` (131072); `.49.d` ties them to the emitted
constants.  The loop is proved for the input class that covers all pre-EIP-8024
bytecode:

* `code.length ≤ bitmapCap` — so the EIP-3860 capacity clamp is a no-op
  (`clampLen = code.length`); the `> capacity` clamp path is a documented child.
* no EIP-8024 opcode (`0xe6`/`0xe7`/`0xe8`) — so the DUPN/SWAPN/EXCHANGE arms
  never fire; those arms are a documented child.

Under these, the pushdata-aware `PUSH` arm is still load-bearing and the post is
the full `validJumpDestinations` set. -/

/-- Byte size of the bitmap region (`= Dispatch.jumpdestBitmapBytes`). -/
def bitmapBytes : Nat := 16384

/-- EIP-3860 code-scan capacity (`= Dispatch.jumpdestBitmapCodeCapacity`). -/
def bitmapCap : Nat := 131072

/-- The read-modify-write JUMPDEST arm: set bit `idx = x5 - x21` of the bitmap
    at `x7`, then advance the scan pointer. -/
def jdSetArm : Stmt :=
  .block "jdset"
    [ .SUB .x28 .x5 .x30,        -- x8 = idx (= pc)
      .ANDI .x29 .x28 7,          -- x9 = idx & 7  (bit position)
      .SRLI .x28 .x28 3,          -- x8 = idx >> 3 (byte index)
      .ADD .x28 .x7 .x28,         -- x8 = &bitmap[idx >> 3]
      .LI .x11 1,
      .SLL .x11 .x11 .x29,       -- x11 = 1 << (idx & 7)
      .LBU .x29 .x28 0,           -- x9 = old byte (RMW read from rw)
      .OR .x29 .x29 .x11,
      .SB .x28 .x29 0,            -- bitmap[idx >> 3] |= 1 << (idx & 7)
      .ADDI .x5 .x5 1 ]

/-- Advance the scan pointer by one byte (plain opcode / invalid / non-listed). -/
def plainArm : Stmt := .block "plain" [.ADDI .x5 .x5 1]

/-- `PUSHn`: advance past the opcode and its `n` immediate bytes
    (`x5 += x8 - 0x5e`, where `x8` holds the opcode). -/
def pushArm : Stmt :=
  .block "push" [.ADDI .x28 .x28 (-94 : BitVec 12), .ADD .x5 .x5 .x28]

/-- One iteration of the scan (EIP-8024-free input): load the code byte, then
    dispatch JUMPDEST / plain-below-`0x60` / `PUSHn` / plain-`≥0x80`. -/
def scanBody : Stmt :=
  .block "load" [.LBU .x28 .x5 0] ;;;
  .block "c5b" [.LI .x29 0x5b] ;;;
  .ite "jd" (.beq .x28 .x29)
    jdSetArm
    ( .block "c60" [.LI .x29 0x60] ;;;
      .ite "plo" (.bltu .x28 .x29)
        plainArm
        ( .block "c80" [.LI .x29 0x80] ;;;
          .ite "phi" (.bltu .x28 .x29)
            pushArm
            plainArm ) )

/-- Loop invariant: `x5` sits at an instruction boundary `pc` (reachable from
    `0`), the pinned end/base registers, `pc ≥ i` (variant), the bitmap length,
    and the bitmap encodes exactly the valid destinations below `pc`. -/
def scanInv (codeBase bitmapBase : Word) (code : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws _ =>
    ∃ pc, rf.get .x5 = codeBase + BitVec.ofNat 64 pc
      ∧ rf.get .x6 = codeBase + BitVec.ofNat 64 code.length
      ∧ rf.get .x7 = bitmapBase
      ∧ rf.get .x30 = codeBase
      ∧ i ≤ pc
      ∧ Reaches code 0 pc
      ∧ ws.length = bitmapBytes
      ∧ ∀ idx, bitmapBit ws idx
          = decide (idx ∈ validJumpDestinations code ∧ idx < pc)

/-- The jumpdest-bitmap build loop as an SAsm function.  `pre` is the state
    after the (elided, straight-line) prologue that seeds `x5`/`x6`/`x7`/`x21`
    from the env and zeroes the bitmap — matching how `.49.d` invokes it. -/
def scanFn (codeBase bitmapBase : Word) (code : List (BitVec 8)) : Fn where
  name := "jdbmScan"
  region := ⟨codeBase, code⟩
  rw := ⟨bitmapBase, bitmapBytes⟩
  pre := fun rf ws _ =>
    rf.get .x5 = codeBase
    ∧ rf.get .x6 = codeBase + BitVec.ofNat 64 code.length
    ∧ rf.get .x7 = bitmapBase
    ∧ rf.get .x30 = codeBase
    ∧ ws = List.replicate bitmapBytes 0
  post := fun _ ws _ =>
    ∀ idx, idx < code.length →
      bitmapBit ws idx = decide (idx ∈ validJumpDestinations code)
  body := .«while» "scan" (.bltu .x5 .x6) code.length (scanInv codeBase bitmapBase code) scanBody

/-! ## Triple (assembly in progress — bead `evm-asm-cfjzu`)

`scanFn_spec` — `(scanFn codeBase bitmapBase code).Spec base` under
`code.length ≤ bitmapCap`, no EIP-8024 opcode, region wf, and code/bitmap
disjointness (`.49.d` discharges the last from
`RegionMap.guestRegionMap_pairwise_disjoint`).  Landed pieces of the proof:
the `region`/`inv_init`/`exhausted`/`post`/`flat`/`.ok` VCs, the RO-code
`load.mem` routing (`¬ inRw` via disjointness → `region.loadOk`), and the
unsigned-compare bridges (`ult_ge`/`lt_of_ult`/`ult_of_lt`).  Remaining: the
`.«while».inv_step` 4-leaf `execBlock` computation (JUMPDEST via
`bitmapBit_setBit` + `vjd_lt_step`; the plain/PUSH arms via `vjd_lt_step`,
`code[pc] ≠ 0x5b`) and the `jdset.mem` read-modify-write address VC (bitmap
`inRw` from `pc / 8 < bitmapBytes`).  Both need a `jdSetArm` `execBlock`
engine lemma to resolve the nested `inRw` conditionals. -/

end EvmAsm.Codegen.Proofs.JumpdestBitmap
