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

  A `jal` (cross-function or same-function) becomes an ordinary PC-relative
  jump with byte offset `target − pc` (`.text` is ~0.36 MiB, comfortably inside
  JAL's ±1 MiB reach).

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

/-- `jal`/`j` byte offset: `target − pc` as a signed 21-bit PC-relative
    displacement (`pc` = the jump's own absolute address).  The same helper is
    used for cross-function calls and long same-function jumps. -/
def jalOff (target pc : Nat) : BitVec 21 :=
  BitVec.ofInt 21 ((target : Int) - (pc : Int))

/-- Range hyp for `jalOff_correct`: signed 21-bit JAL displacement fits
    (`|target − pc| < 2^20`). Strict `<` excludes the lone edge `−2^20`
    (still representable) so `toInt_ofInt_eq_self` applies directly. -/
@[inline] def jalOffInRange (target pc : Nat) : Prop :=
  Int.natAbs ((target : Int) - (pc : Int)) < 2 ^ 20

instance (target pc : Nat) : Decidable (jalOffInRange target pc) :=
  inferInstanceAs (Decidable (Int.natAbs ((target : Int) - (pc : Int)) < 2 ^ 20))

private theorem jalOff_s_bounds {target pc : Nat} (h : jalOffInRange target pc) :
    -((2 : Int) ^ 20) ≤ ((target : Int) - (pc : Int)) ∧
      ((target : Int) - (pc : Int)) < (2 : Int) ^ 20 := by
  let s : Int := (target : Int) - (pc : Int)
  have habs : (Int.natAbs s : Int) < (2 : Int) ^ 20 := by
    have h' : Int.natAbs s < 2 ^ 20 := by
      simpa [s, jalOffInRange] using h
    exact (Int.ofNat_lt (n := Int.natAbs s) (m := 2 ^ 20)).mpr h'
  have hle : s ≤ (Int.natAbs s : Int) := Int.le_natAbs
  have hge : - (Int.natAbs s : Int) ≤ s := by
    have h1 := Int.le_natAbs (a := -s)
    rw [Int.natAbs_neg] at h1
    -- h1 : -s ≤ ↑(natAbs s); negate both sides
    have h2 := Int.neg_le_neg h1
    -- h2 : -↑(natAbs s) ≤ -(-s)
    simpa only [Int.neg_neg] using h2
  refine ⟨?_, ?_⟩
  · -- -2^20 ≤ s
    have : -((2 : Int) ^ 20) ≤ - (Int.natAbs s : Int) := by
      have : (Int.natAbs s : Int) ≤ (2 : Int) ^ 20 := Int.le_of_lt habs
      exact Int.neg_le_neg this
    exact Int.le_trans this hge
  · -- s < 2^20
    exact Int.lt_of_le_of_lt hle habs

/-- PC-relative JAL lands on `target`:
    `(pc : Word) + signExtend21 (jalOff target pc) = (target : Word)`.

    Retires the 21 ad-hoc `rw [show (AB+N) + signExtend21 (jalOff …) = … from by decide]`
    sites that re-elaborate whenever `GuestAddrs` move (#12091 class). Proof is
    pure Int/`toInt` normalization — no `bv_decide`/`native_decide`/`maxRecDepth`. -/
theorem jalOff_correct (target pc : Nat) (h : jalOffInRange target pc) :
    (BitVec.ofNat 64 pc) + EvmAsm.Rv64.signExtend21 (jalOff target pc) =
      BitVec.ofNat 64 target := by
  let s : Int := (target : Int) - (pc : Int)
  have hs : (target : Int) - (pc : Int) = s := rfl
  obtain ⟨hge, hlt⟩ := jalOff_s_bounds (target := target) (pc := pc) h
  -- rewrite bounds onto s (hs : target - pc = s)
  have hge' : -((2 : Int) ^ 20) ≤ s := hs ▸ hge
  have hlt' : s < (2 : Int) ^ 20 := hs ▸ hlt
  -- ofInt 21 recovers s on the signed range
  have htoInt21 : (BitVec.ofInt 21 s).toInt = s :=
    BitVec.toInt_ofInt_eq_self (by decide : 0 < 21) hge' hlt'
  -- sign-extend 21→64 preserves toInt
  have hse : (EvmAsm.Rv64.signExtend21 (BitVec.ofInt 21 s)).toInt = s := by
    unfold EvmAsm.Rv64.signExtend21
    rw [BitVec.toInt_signExtend_of_le (by decide : 21 ≤ 64), htoInt21]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_add, jalOff, hs, hse, BitVec.toInt_ofNat', BitVec.toInt_ofNat']
  -- ((pc).bmod M + s).bmod M = (target).bmod M, and s = target - pc
  have hcongr :
      (pc : Int).bmod (2 ^ 64) + s =
        (target : Int) + ((pc : Int).bmod (2 ^ 64) - (pc : Int)) := by
    -- s = target - pc
    omega
  rw [hcongr]
  rw [Int.bmod_eq_bmod_iff_bmod_sub_eq_zero]
  have hsub :
      (target : Int) + ((pc : Int).bmod (2 ^ 64) - (pc : Int)) - (target : Int) =
        (pc : Int).bmod (2 ^ 64) - (pc : Int) := by
    omega
  rw [hsub, ← Int.dvd_iff_bmod_eq_zero]
  exact Int.dvd_bmod_sub_self (x := (pc : Int)) (m := 2 ^ 64)

-- Concrete KATs (split, no maxRecDepth): forward, backward, guest-scale.
example : jalOffInRange 0x100 0 := by decide
example : BitVec.ofNat 64 0 + EvmAsm.Rv64.signExtend21 (jalOff 0x100 0) =
    BitVec.ofNat 64 0x100 := jalOff_correct 0x100 0 (by decide)
example : jalOffInRange 0 0x100 := by decide
example : BitVec.ofNat 64 0x100 + EvmAsm.Rv64.signExtend21 (jalOff 0 0x100) =
    BitVec.ofNat 64 0 := jalOff_correct 0 0x100 (by decide)
example : BitVec.ofNat 64 0x80000000 + EvmAsm.Rv64.signExtend21 (jalOff 0x80000100 0x80000000) =
    BitVec.ofNat 64 0x80000100 :=
  jalOff_correct 0x80000100 0x80000000 (by decide)

/-- Same-function branch byte offset: `target − pc` as a signed 13-bit
    PC-relative displacement (`pc` = the branch's own absolute address).
    Prefer `brOff (entry + tgtOff) (entry + pcOff)` over a bare
    `(N : BitVec 13)` when `|N| ≥ 64` so a body edit that shifts the
    epilogue cannot silently retarget a fail arm mid-restore (#11510 / #11512). -/
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
-- `brOff` offsets, forward and backward.
example : brOff 0x100 0 = (0x100 : BitVec 13) := by decide
example : brOff 0 0x100 = (-0x100 : BitVec 13) := by decide

end EvmAsm.Codegen
