/-
  EvmAsm.Codegen.AsmReloc

  Relocation helpers for the asm→`Program` conversion (bead evm-asm-4ch8f.9.3).

  The hand-written guest asm uses two *symbolic* forms that only acquire a
  concrete immediate once the guest is linked:

    * `la reg, symbol`            — load a `.data`/`.text` symbol address.
    * `jal ra, callee` (or `j …`) — a cross-function jump/call.

  In the non-PIC static link that GNU-as emits for the guest, `la reg, symbol`
  expands to the PC-relative pair

      auipc reg, %pcrel_hi(symbol)      -- reg := pc + (hi20 <<< 12) sign-extended
      addi  reg, reg, %pcrel_lo(1b)     -- reg := reg + sign_extend(lo12)

  where both relocations are measured from the **auipc's own address** `pc`:

      delta = symbol − pc
      hi20  = ((delta + 0x800) >>> 12) &&& 0xfffff     (20-bit auipc field)
      lo12  =  delta &&& 0xfff                          (sign-interpreted addi imm)

  A cross-function `jal` becomes an ordinary PC-relative jump with byte offset
  `callee − pc` (`.text` is ~0.36 MiB, comfortably inside JAL's ±1 MiB reach).

  These helpers compute exactly those fields from a *symbol address* and the
  instruction's own *absolute pc* (both `Nat`, supplied via `GuestAddrs`), so
  the per-function `_prog` defs read e.g.

      .AUIPC .x12 (laHi GuestAddrs.foo_scratch (GuestAddrs.foo + 148))
      .ADDI  .x12 .x12 (laLo GuestAddrs.foo_scratch (GuestAddrs.foo + 148))
      .JAL   .x1  (jalOff GuestAddrs.callee (GuestAddrs.foo + 156))

  and stay textually stable across relayouts (only `GuestAddrs.lean` churns).

  **Churn containment / `Int` handling.** `delta` can be negative (`la` to a
  lower address, backward `jal`), so the subtraction is done over `Int` and
  truncated to two's complement via `BitVec.ofInt`. Every guest `.text`/`.data`
  delta fits a signed 32-bit integer (`.text` @ `0x80000000`, `.data` ends
  below `0xc0000000`, so `|delta| < 2^31`), which makes the 32-bit two's
  complement below exact and lets the `auipc`/`addi` field extraction match
  GNU-as bit-for-bit. The whole-guest byte-identity gate is the arbiter that
  this expansion reproduces what the hand-written `la`/`jal` assembled to.

  Emission is a one-way output channel and carries no proofs; correctness of the
  produced binary is established offline by the assemble+`cmp` byte-identity
  gates, not by any theorem here.
-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

/-- Two's-complement 32-bit `symbol − pc` delta.  Exact for every guest
    `.text`/`.data` reference (`|delta| < 2^31`). -/
def laDelta (sym pc : Nat) : BitVec 32 :=
  BitVec.ofInt 32 ((sym : Int) - (pc : Int))

/-- `%pcrel_hi(symbol)` — the 20-bit `auipc` upper-immediate for
    `la reg, symbol`, where `pc` is the `auipc`'s own absolute address:
    `((symbol − pc + 0x800) >>> 12) &&& 0xfffff`. -/
def laHi (sym pc : Nat) : BitVec 20 :=
  ((laDelta sym pc + 0x800) >>> (12 : Nat)).setWidth 20

/-- `%pcrel_lo(1b)` — the sign-interpreted 12-bit `addi` immediate that
    completes `la reg, symbol`; `pc` is the paired `auipc`'s address (the
    relocation anchor `1b`, **not** the `addi`'s address): `(symbol − pc) &&& 0xfff`. -/
def laLo (sym pc : Nat) : BitVec 12 :=
  (laDelta sym pc).setWidth 12

/-- Cross-function `jal`/`j` byte offset: `callee − pc` as a signed 21-bit
    PC-relative displacement (`pc` = the jump's own absolute address). -/
def jalOff (target pc : Nat) : BitVec 21 :=
  BitVec.ofInt 21 ((target : Int) - (pc : Int))

/-- Intra-function conditional-branch byte offset: `target − pc` as a signed
    13-bit PC-relative displacement (`pc` = the branch's own absolute address).
    Prefer this over a bare `BitVec 13` literal when the target is a named
    epilogue/join point — hardcoded distances drift when the body moves (#11510). -/
def brOff (target pc : Nat) : BitVec 13 :=
  BitVec.ofInt 13 ((target : Int) - (pc : Int))

/-! Reduction sanity checks: the helpers must evaluate under the kernel so the
    per-function `#guard` length/prefix pins (which force `emitProgram`) hold.
    Positive, negative, and boundary deltas.  (Real-address correctness is the
    byte-identity gate's job, not these.) -/

-- Forward `la`: delta = 0x2000 ⇒ hi20 = 0x2, lo12 = 0.
example : laHi 0x2000 0 = (0x2 : BitVec 20) := by decide
example : laLo 0x2000 0 = (0 : BitVec 12) := by decide
-- Low-12 carry into hi20: delta = 0x800 rounds the hi field up, lo12 = -2048.
example : laHi 0x800 0 = (1 : BitVec 20) := by decide
example : laLo 0x800 0 = (-2048 : BitVec 12) := by decide
-- Small backward `la`: delta = -4 ⇒ hi20 = 0 (the sign-extended lo12 reaches
-- back on its own), lo12 = -4.
example : laHi 0 4 = (0 : BitVec 20) := by decide
example : laLo 0 4 = (-4 : BitVec 12) := by decide
-- Large backward `la`: delta = -0x1000 ⇒ hi20 = 0xfffff (−1 upper), lo12 = 0.
example : laHi 0 0x1000 = (0xfffff : BitVec 20) := by decide
example : laLo 0 0x1000 = (0 : BitVec 12) := by decide
-- `jal` offsets, forward and backward.
example : jalOff 0x100 0 = (0x100 : BitVec 21) := by decide
example : jalOff 0 0x100 = (-0x100 : BitVec 21) := by decide
example : brOff 0x100 0 = (0x100 : BitVec 13) := by decide
example : brOff 0 0x100 = (-0x100 : BitVec 13) := by decide

end EvmAsm.Codegen
