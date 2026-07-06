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
import EvmAsm.Rv64.SAsm.MultiDword
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
      = (decide (idx = pc) || bitmapBit ws idx) := by
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

/-- The JUMPDEST-arm instruction list (`idx = x5 - x21`; set bit `idx` of the
    bitmap at `x7`; advance the scan pointer). -/
def jdsetInstrs : List Instr :=
  [ .SUB .x28 .x5 .x30,        -- x28 = idx (= pc)
    .ANDI .x29 .x28 7,          -- x29 = idx & 7  (bit position)
    .SRLI .x28 .x28 3,          -- x28 = idx >> 3 (byte index)
    .ADD .x28 .x7 .x28,         -- x28 = &bitmap[idx >> 3]
    .LI .x11 1,
    .SLL .x11 .x11 .x29,       -- x11 = 1 << (idx & 7)
    .LBU .x29 .x28 0,           -- x29 = old byte (RMW read from rw)
    .OR .x29 .x29 .x11,
    .SB .x28 .x29 0,            -- bitmap[idx >> 3] |= 1 << (idx & 7)
    .ADDI .x5 .x5 1 ]

/-- The read-modify-write JUMPDEST arm. -/
def jdSetArm : Stmt := .block "jdset" jdsetInstrs

/-- Advance the scan pointer by one byte (plain opcode / invalid / non-listed). -/
def plainArm : Stmt := .block "plain" [.ADDI .x5 .x5 1]

/-- `PUSHn`: advance past the opcode and its `n` immediate bytes
    (`x5 += x8 - 0x5e`, where `x8` holds the opcode). -/
def pushArm : Stmt :=
  .block "push" [.ADDI .x28 .x28 (-94 : BitVec 12), .ADD .x5 .x5 .x28]

/-- EIP-8024 immediate-skip: advance the scan pointer by two bytes (opcode +
    the one-byte operand). -/
def skipEip8024ImmArm : Stmt := .block "skipEip8024Imm" [.ADDI .x5 .x5 2]

/-- Shared shape of the EIP-8024 `DUPN`/`SWAPN`/`EXCHANGE` immediate-skip
    test, parameterized by the invalid-immediate lower threshold (`0x5b` for
    `DUPN`/`SWAPN`, `0x52` for `EXCHANGE`): if `pc+1` is past the scan end,
    or the byte there is `< thresh`, or it is `≥ 0x80`, skip two bytes
    (`skipEip8024ImmArm`); otherwise (`thresh ≤ code[pc+1] < 0x80`, the
    *invalid* immediate range) the byte stays an instruction boundary
    (`plainArm`) — mirrors `Dispatch.lean`'s `.jdbm_dupn_swapn`/
    `.jdbm_exchange` and `jdAdvance`'s `0xe6`/`0xe7`/`0xe8` arms. -/
def eip8024ImmArm (thresh : Word) : Stmt :=
  .block "dsBound" [.ADDI .x29 .x5 1] ;;;
  .ite "dsBoundCk" (.bgeu .x29 .x6)
    skipEip8024ImmArm
    ( .block "dsLoad" [.LBU .x29 .x5 1, .LI .x11 thresh] ;;;
      .ite "dsLo" (.bltu .x29 .x11)
        skipEip8024ImmArm
        ( .block "dsHi" [.LI .x11 0x80] ;;;
          .ite "dsHiCk" (.bltu .x29 .x11)
            plainArm
            skipEip8024ImmArm ) )

/-- `DUPN`/`SWAPN` (`0xe6`/`0xe7`): invalid immediate range `0x5b..0x7f`. -/
def dupnSwapnArm : Stmt := eip8024ImmArm 0x5b

/-- `EXCHANGE` (`0xe8`): invalid immediate range `0x52..0x7f`. -/
def exchangeArm : Stmt := eip8024ImmArm 0x52

/-- One iteration of the scan (EIP-8024-free input): load the code byte, then
    dispatch JUMPDEST / plain-below-`0x60` / `PUSHn` / plain-`≥0x80`.
    `eip8024ImmArm`/`dupnSwapnArm`/`exchangeArm` above give the general
    (EIP-8024-aware) per-step engine `eip8024ImmArm_step` (fully proved) that a
    follow-up wires into this cascade in place of `plainArm`'s final arm,
    matching `Dispatch.lean`'s full `.jdbm_not_jumpdest` cascade — see bead
    `evm-asm-cfjzu.2`. -/
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
/-! ## Unsigned-compare bridges for the scan pointer (no address wraparound) -/

/-- `x5 <u x6` fails once the scan pointer reaches the code end. -/
private theorem ult_ge (cb : Word) (a b : Nat) (hb : cb.toNat + b < 2 ^ 64)
    (ha : cb.toNat + a < 2 ^ 64) (hab : b ≤ a) :
    ¬ BitVec.ult (cb + BitVec.ofNat 64 a) (cb + BitVec.ofNat 64 b) = true := by
  simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `x5 <u x6` holding forces the pointer below the code end. -/
private theorem lt_of_ult (cb : Word) (a b : Nat) (hb : cb.toNat + b < 2 ^ 64)
    (ha : cb.toNat + a < 2 ^ 64)
    (h : BitVec.ult (cb + BitVec.ofNat 64 a) (cb + BitVec.ofNat 64 b) = true) : a < b := by
  simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at h
  omega

/-- Below the code end, `x5 <u x6` holds. -/
private theorem ult_of_lt (cb : Word) (a b : Nat) (ha : cb.toNat + a < 2 ^ 64)
    (hb : cb.toNat + b < 2 ^ 64) (hab : a < b) :
    BitVec.ult (cb + BitVec.ofNat 64 a) (cb + BitVec.ofNat 64 b) = true := by
  simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ## The JUMPDEST-arm `execBlock` engine -/

private theorem truncate_zext_or (a : BitVec 8) (b : BitVec 64) :
    BitVec.truncate 8 (a.zeroExtend 64 ||| b) = a ||| BitVec.truncate 8 b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases h : (i : Nat) < 8 <;>
    simp [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, h]

/-- The JUMPDEST arm's `execBlock`: it sets exactly bit `pc` of the bitmap
    (`ws.set (pc/8) (old ||| 1<<<(pc%8))`), advances `x5`, and leaves
    `x6`/`x7`/`x30` untouched.  Resolves the RMW load's `inRw` routing (the
    bitmap byte `pc/8` is in the writable window, from `pc/8 < ws.length`). -/
theorem jdset_engine (codeBase bitmapBase : Word) (code ws : List (BitVec 8))
    (rf : RegFile) (pc : Nat)
    (hx5 : rf.get .x5 = codeBase + BitVec.ofNat 64 pc) (hx7 : rf.get .x7 = bitmapBase)
    (hx30 : rf.get .x30 = codeBase) (hbnd : pc / 8 < ws.length) (hpc : pc < 2 ^ 64) :
    (execBlock (Region.mk codeBase code) bitmapBase rf ws jdsetInstrs).2
        = ws.set (pc / 8) (ws.getD (pc / 8) 0 ||| ((1 : BitVec 8) <<< (pc % 8)))
      ∧ (execBlock (Region.mk codeBase code) bitmapBase rf ws jdsetInstrs).1.get .x5
        = codeBase + BitVec.ofNat 64 (pc + 1)
      ∧ (execBlock (Region.mk codeBase code) bitmapBase rf ws jdsetInstrs).1.get .x6 = rf.get .x6
      ∧ (execBlock (Region.mk codeBase code) bitmapBase rf ws jdsetInstrs).1.get .x7 = bitmapBase
      ∧ (execBlock (Region.mk codeBase code) bitmapBase rf ws jdsetInstrs).1.get .x30 = codeBase := by
  have hsub : codeBase + BitVec.ofNat 64 pc - codeBase = BitVec.ofNat 64 pc := by bv_omega
  have hsh : ((BitVec.ofNat 64 pc) >>> (3 : Nat)).toNat = pc / 8 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpc,
      Nat.shiftRight_eq_div_pow]
  have hand : (BitVec.ofNat 64 pc &&& (7 : BitVec 64)).toNat % 64 = pc % 8 := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, show ((7 : BitVec 64).toNat) = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd pc (Nat.pow_dvd_pow 2 (by omega))]; omega
  have haddr : bitmapBase + (BitVec.ofNat 64 pc) >>> (3 : Nat) + 0 - bitmapBase
      = (BitVec.ofNat 64 pc) >>> (3 : Nat) := by bv_omega
  have htr : BitVec.truncate 8 ((1 : BitVec 64) <<< (pc % 8)) = (1 : BitVec 8) <<< (pc % 8) := by
    apply BitVec.eq_of_getLsbD_eq; intro i; simp [BitVec.getLsbD_shiftLeft]
  have hinrw : inRw bitmapBase ws (bitmapBase + (BitVec.ofNat 64 pc) >>> (3 : Nat) + 0) 1 := by
    show ((bitmapBase + (BitVec.ofNat 64 pc) >>> (3 : Nat) + 0) - bitmapBase).toNat + 1 ≤ ws.length
    rw [haddr, hsh]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [jdsetInstrs, execBlock, execInstrRF, aluSem, loadSem, storeSem,
      RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true,
      hx5, hx7, hx30, hsub, show ((3 : BitVec 6).toNat) = 3 from rfl,
      show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show signExtend12 (7 : BitVec 12) = (7 : Word) from by decide,
      show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
      if_pos hinrw, hand, Region.byteAt, haddr, hsh]
  · rw [truncate_zext_or, htr, setBytes_singleton]
  · bv_omega

/-- Uniform invariant step for every NON-JUMPDEST arm: the bitmap is unchanged
    and `x5` advances by `jdAdvance`.  `code[pc] ≠ 0x5b` makes `vjd_lt_step`'s
    right disjunct vanish, so the valid-dest set below `pc + jdAdvance` equals
    the set below `pc`. -/
theorem nonjd_step (codeBase bitmapBase : Word) (code ws0 : List (BitVec 8)) (A' : Assertion)
    (i pc : Nat) (rf' : RegFile)
    (hcode : (code.getD pc 0).toNat ≠ 0x5b)
    (hile : i ≤ pc) (hreach : Reaches code 0 pc) (hpclt : pc < code.length)
    (hwslen : ws0.length = bitmapBytes)
    (hbit : ∀ idx, bitmapBit ws0 idx = decide (idx ∈ validJumpDestinations code ∧ idx < pc))
    (hx5' : rf'.get .x5 = codeBase + BitVec.ofNat 64 (pc + jdAdvance code pc))
    (hx6' : rf'.get .x6 = codeBase + BitVec.ofNat 64 code.length)
    (hx7' : rf'.get .x7 = bitmapBase) (hx30' : rf'.get .x30 = codeBase) :
    scanInv codeBase bitmapBase code (i + 1) rf' ws0 A' := by
  refine ⟨pc + jdAdvance code pc, hx5', hx6', hx7', hx30', ?_, hreach.extend hpclt, hwslen, ?_⟩
  · have := jdAdvance_pos code pc; omega
  · intro idx
    rw [hbit idx]
    have hstep := vjd_lt_step hreach hpclt idx
    have hiff : (idx ∈ validJumpDestinations code ∧ idx < pc)
        ↔ (idx ∈ validJumpDestinations code ∧ idx < pc + jdAdvance code pc) := by
      rw [hstep]; constructor
      · exact fun h => Or.inl h
      · rintro (h | ⟨h5, _⟩); exact h; exact absurd h5 hcode
    exact decide_eq_decide.mpr hiff

/-- `execBlock` of the plain arm (over an abstract entry `rf`), so the leaves
    apply it without unfolding the block over a deeply-nested register file. -/
theorem plainArm_exec (reg : Region) (rwB : Word) (rf : RegFile) (ws : List (BitVec 8)) :
    execBlock reg rwB rf ws [.ADDI .x5 .x5 1] = (rf.set .x5 (rf.get .x5 + signExtend12 1), ws) := by
  simp only [execBlock, execInstrRF, aluSem]

/-- `execBlock` of the `PUSHn` arm (over an abstract entry `rf`). -/
theorem pushArm_exec (reg : Region) (rwB : Word) (rf : RegFile) (ws : List (BitVec 8)) :
    execBlock reg rwB rf ws [.ADDI .x28 .x28 (-94), .ADD .x5 .x5 .x28]
      = ((rf.set .x28 (rf.get .x28 + signExtend12 (-94))).set .x5
          (rf.get .x5 + (rf.get .x28 + signExtend12 (-94))), ws) := by
  simp only [execBlock, execInstrRF, aluSem, RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
    reduceCtorEq, not_false_eq_true]

/-- `execBlock` of the EIP-8024 immediate-skip arm (over an abstract entry
    `rf`). -/
theorem skipEip8024ImmArm_exec (reg : Region) (rwB : Word) (rf : RegFile) (ws : List (BitVec 8)) :
    execBlock reg rwB rf ws [.ADDI .x5 .x5 2] = (rf.set .x5 (rf.get .x5 + signExtend12 2), ws) := by
  simp only [execBlock, execInstrRF, aluSem]

/-- **The shared EIP-8024 immediate-skip engine.**  `eip8024ImmArm thresh`
    (the `DUPN`/`SWAPN`/`EXCHANGE` shape, parameterized by the invalid-range
    threshold) advances `x5` by exactly `jdAdvance code pc`, leaves
    `x6`/`x7`/`x30`/the bitmap untouched, and reads at most `code[pc+1]` —
    justified by `hdisj1` exactly like the main scan load, since the
    `dsBoundCk` branch only reaches the load when `pc+1 < code.length ≤ x6`'s
    scan bound.  `hadvEq` is the arm's own bound/threshold case split,
    restated as an equation against `jdAdvance` — trivial to discharge at
    each call site from `jdAdvance`'s definition (mirrors how the JUMPDEST
    and PUSH arms establish their own `jdAdvance` facts). -/
theorem eip8024ImmArm_step (thresh : Word) (reach : Reach)
    (codeBase bitmapBase : Word) (code ws0 : List (BitVec 8)) (A0 : Assertion) (pc : Nat)
    (hentail : ∀ rf ws A, reach rf ws A →
      rf.get .x5 = codeBase + BitVec.ofNat 64 pc
      ∧ rf.get .x6 = codeBase + BitVec.ofNat 64 code.length
      ∧ rf.get .x7 = bitmapBase ∧ rf.get .x30 = codeBase
      ∧ ws = ws0 ∧ A = A0)
    (hpclt : pc < code.length) (hpc64 : pc < 2 ^ 64)
    (hnowrap : codeBase.toNat + (code.length + 32) < 2 ^ 64)
    (hwslen : ws0.length = bitmapBytes)
    (hdisj1 : bitmapBytes ≤ (codeBase + BitVec.ofNat 64 (pc + 1) - bitmapBase).toNat)
    (hadvEq : jdAdvance code pc =
      if pc + 1 < code.length ∧ thresh.toNat ≤ (code.getD (pc + 1) 0).toNat
          ∧ (code.getD (pc + 1) 0).toNat ≤ 0x7f
        then 1 else 2) :
    ∀ rf' ws' A', Stmt.sp (Region.mk codeBase code) ⟨bitmapBase, bitmapBytes⟩ (eip8024ImmArm thresh)
        reach rf' ws' A' →
      ws' = ws0 ∧ A' = A0
      ∧ rf'.get .x5 = codeBase + BitVec.ofNat 64 (pc + jdAdvance code pc)
      ∧ rf'.get .x6 = codeBase + BitVec.ofNat 64 code.length
      ∧ rf'.get .x7 = bitmapBase ∧ rf'.get .x30 = codeBase := by
  have hse1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hse2 : signExtend12 (2 : BitVec 12) = (2 : Word) := by decide
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  -- The `dsBound` block always runs first: `x29 := x5 + 1`, everything else
  -- unchanged.  Every one of the four leaves below starts from this state.
  have hR1 : ∀ rf1 ws1 A1, Stmt.sp (Region.mk codeBase code) ⟨bitmapBase, bitmapBytes⟩
      (.block "dsBound" [.ADDI .x29 .x5 1]) reach rf1 ws1 A1 →
        rf1.get .x29 = codeBase + BitVec.ofNat 64 (pc + 1)
        ∧ rf1.get .x5 = codeBase + BitVec.ofNat 64 pc
        ∧ rf1.get .x6 = codeBase + BitVec.ofNat 64 code.length
        ∧ rf1.get .x7 = bitmapBase ∧ rf1.get .x30 = codeBase
        ∧ ws1 = ws0 ∧ A1 = A0 := by
    rintro rf1 ws1 A1 ⟨rfa, wsX, hlena, hex, hrf1e, hws1e⟩
    obtain ⟨hax5, hax6, hax7, hax30, hwsae, hAe⟩ := hentail rfa wsX A1 hex
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hAe⟩
    · rw [hrf1e]
      simp only [execBlock, execInstrRF, aluSem, RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true, hax5, hse1]
      bv_omega
    · rw [hrf1e]
      simp only [execBlock, execInstrRF, aluSem, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, hax5]
    · rw [hrf1e]
      simp only [execBlock, execInstrRF, aluSem, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, hax6]
    · rw [hrf1e]
      simp only [execBlock, execInstrRF, aluSem, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, hax7]
    · rw [hrf1e]
      simp only [execBlock, execInstrRF, aluSem, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, hax30]
    · rw [hws1e, hwsae]
      simp only [execBlock, execInstrRF, aluSem]
  -- The `dsLoad` block, run from any entry with the known `x29` value.
  have hLoad : ∀ (rfa : RegFile) (wsX : List (BitVec 8)),
      rfa.get .x5 = codeBase + BitVec.ofNat 64 pc →
      ¬ inRw bitmapBase wsX (codeBase + BitVec.ofNat 64 (pc + 1)) 1 →
      execBlock (Region.mk codeBase code) bitmapBase rfa wsX [.LBU .x29 .x5 1, .LI .x11 thresh]
        = ((rfa.set .x29 ((code.getD (pc + 1) 0).zeroExtend 64)).set .x11 thresh, wsX) := by
    intro rfa wsX hax5 hbnd
    have hax5d : rfa.get .x5 + signExtend12 (1 : BitVec 12) = codeBase + BitVec.ofNat 64 (pc + 1) := by
      rw [hax5, hse1]; bv_omega
    simp only [execBlock, execInstrRF, aluSem, loadSem, Region.byteAt, hax5d, if_neg hbnd]
    rw [show codeBase + BitVec.ofNat 64 (pc + 1) - codeBase
          = BitVec.ofNat 64 (pc + 1) from by bv_omega,
      show (BitVec.ofNat 64 (pc + 1)).toNat = pc + 1 from by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]]
  rintro rf' ws' A' hsp
  simp only [eip8024ImmArm] at hsp
  rcases hsp with ha | hb | hc | hd
  · -- `dsBoundCk` taken: `pc + 1 ≥ code.length` (past the scan end) → skip
    obtain ⟨rfa, wsX, hlena, hcase, hrfe, hwse⟩ := ha
    obtain ⟨hR1', hbgeu⟩ := hcase
    obtain ⟨ha29, ha5, ha6, ha7, ha30, hwsae, hAe⟩ := hR1 rfa wsX A' hR1'
    rw [hrfe, hwse, skipEip8024ImmArm_exec]
    simp only [Cond.holds] at hbgeu
    rw [ha29, ha6] at hbgeu
    have hge : ¬ pc + 1 < code.length := by
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hbgeu
      omega
    have hadv : jdAdvance code pc = 2 := by rw [hadvEq, if_neg (fun h => hge h.1)]
    refine ⟨hwsae, hAe, ?_, ?_, ?_, ?_⟩ <;>
      simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true,
        ha5, ha6, ha7, ha30, hadv, hse2]
    bv_omega
  · -- `dsBoundCk` not taken, `dsLo` taken: `code[pc+1] < thresh` → skip
    obtain ⟨rfb, wsb, hlenb, hcase, hrfe, hwse⟩ := hb
    obtain ⟨hR2, hbltu⟩ := hcase
    obtain ⟨rfa, wsX, hlena, hcase2, hrfbe, hwsbe⟩ := hR2
    obtain ⟨hR1', hnbgeu⟩ := hcase2
    obtain ⟨ha29, ha5, ha6, ha7, ha30, hwsae, hAe⟩ := hR1 rfa wsX A' hR1'
    simp only [Cond.holds] at hnbgeu
    have hbnd : ¬ inRw bitmapBase wsX (codeBase + BitVec.ofNat 64 (pc + 1)) 1 := by
      show ¬ (codeBase + BitVec.ofNat 64 (pc + 1) - bitmapBase).toNat + 1 ≤ wsX.length
      rw [hwsae]; bv_omega
    have hge : pc + 1 < code.length := by
      by_contra hge
      apply hnbgeu
      rw [ha29, ha6]
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [hLoad rfa wsX ha5 hbnd] at hrfbe hwsbe
    simp only [] at hrfbe hwsbe
    rw [hrfbe] at hbltu
    simp only [Cond.holds, RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true] at hbltu
    have hlt : (code.getD (pc + 1) 0).toNat < thresh.toNat := by
      simp only [BitVec.ult, decide_eq_true_eq] at hbltu
      rwa [toNat_zeroExtend_byte] at hbltu
    have hadv : jdAdvance code pc = 2 := by
      rw [hadvEq, if_neg (fun h => absurd h.2.1 (by omega))]
    rw [hrfe, hwse, hrfbe, hwsbe, skipEip8024ImmArm_exec]
    refine ⟨hwsae, hAe, ?_, ?_, ?_, ?_⟩ <;>
      simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true,
        ha5, ha6, ha7, ha30, hadv, hse2]
    bv_omega
  · -- `dsHiCk` taken: `thresh ≤ code[pc+1] < 0x80` → stays a boundary (plain)
    obtain ⟨rfc, wsc, hlenc, hcase, hrfe, hwse⟩ := hc
    obtain ⟨hR3, hbltu2⟩ := hcase
    obtain ⟨rfb, wsb, hlenb, hcase2, hrfce, hwsce⟩ := hR3
    obtain ⟨hR2, hnbltu⟩ := hcase2
    obtain ⟨rfa, wsX, hlena, hcase3, hrfbe, hwsbe⟩ := hR2
    obtain ⟨hR1', hnbgeu⟩ := hcase3
    obtain ⟨ha29, ha5, ha6, ha7, ha30, hwsae, hAe⟩ := hR1 rfa wsX A' hR1'
    simp only [Cond.holds] at hnbgeu
    have hbnd : ¬ inRw bitmapBase wsX (codeBase + BitVec.ofNat 64 (pc + 1)) 1 := by
      show ¬ (codeBase + BitVec.ofNat 64 (pc + 1) - bitmapBase).toNat + 1 ≤ wsX.length
      rw [hwsae]; bv_omega
    have hge : pc + 1 < code.length := by
      by_contra hge
      apply hnbgeu
      rw [ha29, ha6]
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [hLoad rfa wsX ha5 hbnd] at hrfbe hwsbe
    simp only [] at hrfbe hwsbe
    rw [hrfbe] at hnbltu
    simp only [Cond.holds, RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true] at hnbltu
    have hge2 : thresh.toNat ≤ (code.getD (pc + 1) 0).toNat := by
      simp only [BitVec.ult, decide_eq_true_eq, not_lt] at hnbltu
      rwa [toNat_zeroExtend_byte] at hnbltu
    have hli : execBlock (Region.mk codeBase code) bitmapBase
        ((rfa.set .x29 ((code.getD (pc + 1) 0).zeroExtend 64)).set .x11 thresh) wsX
        [.LI .x11 0x80]
        = (((rfa.set .x29 ((code.getD (pc + 1) 0).zeroExtend 64)).set .x11 thresh).set .x11 0x80,
            wsX) := by
      simp only [execBlock, execInstrRF, aluSem]
    rw [hrfce, hrfbe, hwsbe, hli] at hbltu2
    simp only [Cond.holds, RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true] at hbltu2
    have hlt80 : (code.getD (pc + 1) 0).toNat < 0x80 := by
      simp only [BitVec.ult, decide_eq_true_eq] at hbltu2
      rwa [toNat_zeroExtend_byte] at hbltu2
    have hadv : jdAdvance code pc = 1 := by
      rw [hadvEq, if_pos ⟨hge, hge2, by omega⟩]
    rw [hrfe, hwse, hrfce, hwsce, hrfbe, hwsbe, plainArm_exec, hli]
    refine ⟨hwsae, hAe, ?_, ?_, ?_, ?_⟩ <;>
      simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true,
        ha5, ha6, ha7, ha30, hadv, hse1]
    bv_omega
  · -- `dsHiCk` not taken: `code[pc+1] ≥ 0x80` → skip
    obtain ⟨rfc, wsc, hlenc, hcase, hrfe, hwse⟩ := hd
    obtain ⟨hR3, hnbltu2⟩ := hcase
    obtain ⟨rfb, wsb, hlenb, hcase2, hrfce, hwsce⟩ := hR3
    obtain ⟨hR2, hnbltu⟩ := hcase2
    obtain ⟨rfa, wsX, hlena, hcase3, hrfbe, hwsbe⟩ := hR2
    obtain ⟨hR1', hnbgeu⟩ := hcase3
    obtain ⟨ha29, ha5, ha6, ha7, ha30, hwsae, hAe⟩ := hR1 rfa wsX A' hR1'
    simp only [Cond.holds] at hnbgeu
    have hbnd : ¬ inRw bitmapBase wsX (codeBase + BitVec.ofNat 64 (pc + 1)) 1 := by
      show ¬ (codeBase + BitVec.ofNat 64 (pc + 1) - bitmapBase).toNat + 1 ≤ wsX.length
      rw [hwsae]; bv_omega
    have hge : pc + 1 < code.length := by
      by_contra hge
      apply hnbgeu
      rw [ha29, ha6]
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [hLoad rfa wsX ha5 hbnd] at hrfbe hwsbe
    simp only [] at hrfbe hwsbe
    rw [hrfbe] at hnbltu
    simp only [Cond.holds, RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true] at hnbltu
    have hge2 : thresh.toNat ≤ (code.getD (pc + 1) 0).toNat := by
      simp only [BitVec.ult, decide_eq_true_eq, not_lt] at hnbltu
      rwa [toNat_zeroExtend_byte] at hnbltu
    have hli : execBlock (Region.mk codeBase code) bitmapBase
        ((rfa.set .x29 ((code.getD (pc + 1) 0).zeroExtend 64)).set .x11 thresh) wsX
        [.LI .x11 0x80]
        = (((rfa.set .x29 ((code.getD (pc + 1) 0).zeroExtend 64)).set .x11 thresh).set .x11 0x80,
            wsX) := by
      simp only [execBlock, execInstrRF, aluSem]
    rw [hrfce, hrfbe, hwsbe, hli] at hnbltu2
    simp only [Cond.holds, RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true] at hnbltu2
    have hge80 : 0x80 ≤ (code.getD (pc + 1) 0).toNat := by
      simp only [BitVec.ult, decide_eq_true_eq, not_lt] at hnbltu2
      rwa [toNat_zeroExtend_byte] at hnbltu2
    have hadv : jdAdvance code pc = 2 := by
      rw [hadvEq, if_neg (fun h => absurd h.2.2 (by omega))]
    rw [hrfe, hwse, hrfce, hwsce, hrfbe, hwsbe, skipEip8024ImmArm_exec, hli]
    refine ⟨hwsae, hAe, ?_, ?_, ?_, ?_⟩ <;>
      simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true,
        ha5, ha6, ha7, ha30, hadv, hse2]
    bv_omega

theorem scanFn_inv_step (codeBase bitmapBase : Word) (code : List (BitVec 8))
    (hcap : code.length ≤ bitmapCap)
    (hnowrap : codeBase.toNat + (code.length + 32) < 2 ^ 64)
    (hNoEip : ∀ k, k < code.length →
      (code.getD k 0).toNat ≠ 0xe6 ∧ (code.getD k 0).toNat ≠ 0xe7 ∧ (code.getD k 0).toNat ≠ 0xe8)
    (hdisj : ∀ k, k ≤ code.length →
      bitmapBytes ≤ (codeBase + BitVec.ofNat 64 k - bitmapBase).toNat)
    (i : Nat) (hi : i < code.length) (rf' : RegFile) (ws' : List (BitVec 8)) (A' : Assertion)
    (hsp : sp (scanFn codeBase bitmapBase code).region (scanFn codeBase bitmapBase code).rw scanBody
      (fun rf ws A => scanInv codeBase bitmapBase code i rf ws A ∧ (Cond.bltu Reg.x5 Reg.x6).holds rf)
      rf' ws' A') :
    scanInv codeBase bitmapBase code (i + 1) rf' ws' A' := by
    rcases hsp with h | h
    · -- JUMPDEST arm
      obtain ⟨rfB, wsB, hwsBlen, hR2jd, hrfe, hwse⟩ := h
      obtain ⟨hR2, hjdc⟩ := hR2jd
      obtain ⟨rfA, wsA, hwsAlen, hRload, hrfBe, hwsBe⟩ := hR2
      obtain ⟨rf0, ws0, hws0len, hreach0, hrfAe, hwsAe⟩ := hRload
      obtain ⟨hinv, hguard⟩ := hreach0
      obtain ⟨pc, hx5, hx6, hx7, hx30, hile, hreach, hwslen, hbit⟩ := hinv
      have hreg : (scanFn codeBase bitmapBase code).region = Region.mk codeBase code := rfl
      have hrwb : (scanFn codeBase bitmapBase code).rw.base = bitmapBase := rfl
      rw [hreg, hrwb] at hrfe hwse hrfBe hwsBe hrfAe hwsAe
      simp only [Cond.holds, hx5, hx6] at hguard
      have hpc := EvmAsm.Stateless.SpecRef.Reaches_zero_le hreach
      have hcap' : code.length ≤ 131072 := by simpa [bitmapCap] using hcap
      have hpclt : pc < code.length := lt_of_ult codeBase pc code.length (by omega) (by omega) hguard
      have hpc64 : pc < 2 ^ 64 := by omega
      have hbnd' : pc / 8 < ws0.length := by rw [hwslen]; simp only [bitmapBytes]; omega
      have hnorw : ¬ inRw bitmapBase ws0 (rf0.get .x5 + signExtend12 0) 1 := by
        show ¬ (rf0.get .x5 + signExtend12 0 - bitmapBase).toNat + 1 ≤ ws0.length
        rw [hx5, hwslen, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        have := hdisj pc (by omega); bv_omega
      have hload : execBlock (Region.mk codeBase code) bitmapBase rf0 ws0 [.LBU .x28 .x5 0]
          = (rf0.set .x28 ((code.getD pc 0).zeroExtend 64), ws0) := by
        simp only [execBlock, execInstrRF, aluSem, loadSem, if_neg hnorw, Region.byteAt]
        rw [show rf0.get .x5 + signExtend12 0 - codeBase = BitVec.ofNat 64 pc from by
              rw [hx5, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
          show (BitVec.ofNat 64 pc).toNat = pc from by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpc64]]
      have hc5b : ∀ rf : RegFile,
          execBlock (Region.mk codeBase code) bitmapBase rf ws0 [.LI .x29 91]
          = (rf.set .x29 91, ws0) := by intro rf; simp only [execBlock, execInstrRF, aluSem]
      -- collapse the load and c5b blocks into an explicit entry state for jdset
      have hwsA0 : wsA = ws0 := by rw [hwsAe, hload]
      have hrfAv : rfA = rf0.set .x28 ((code.getD pc 0).zeroExtend 64) := by rw [hrfAe, hload]
      rw [hwsA0, hrfAv, hc5b] at hrfBe hwsBe
      simp only [] at hrfBe hwsBe
      -- code[pc] = 0x5b from the jd condition
      have hcode : (code.getD pc 0).toNat = 0x5b := by
        rw [hrfBe] at hjdc
        simp only [Cond.holds, RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
          reduceCtorEq, not_false_eq_true] at hjdc
        have h2 := congrArg BitVec.toNat hjdc
        rwa [toNat_zeroExtend_byte, show (91 : Word).toNat = 91 from by decide] at h2
      have hadv1 : jdAdvance code pc = 1 := by simp only [jdAdvance]; rw [if_pos hcode]
      have hb5 : rfB.get .x5 = codeBase + BitVec.ofNat 64 pc := by
        rw [hrfBe, RegFile.get_set_ne _ _ _ _ (by decide),
          RegFile.get_set_ne _ _ _ _ (by decide), hx5]
      have hb7 : rfB.get .x7 = bitmapBase := by
        rw [hrfBe, RegFile.get_set_ne _ _ _ _ (by decide),
          RegFile.get_set_ne _ _ _ _ (by decide), hx7]
      have hb30 : rfB.get .x30 = codeBase := by
        rw [hrfBe, RegFile.get_set_ne _ _ _ _ (by decide),
          RegFile.get_set_ne _ _ _ _ (by decide), hx30]
      obtain ⟨hwsr, hx5r, hx6r, hx7r, hx30r⟩ :=
        jdset_engine codeBase bitmapBase code ws0 rfB pc hb5 hb7 hb30 hbnd' hpc64
      rw [hrfe, hwse, hwsBe]
      refine ⟨pc + 1, ?_, ?_, ?_, ?_, by omega, hadv1 ▸ hreach.extend hpclt, ?_, ?_⟩
      · rw [hx5r]
      · rw [hx6r, hrfBe, RegFile.get_set_ne _ _ _ _ (by decide),
          RegFile.get_set_ne _ _ _ _ (by decide), hx6]
      · rw [hx7r]
      · rw [hx30r]
      · rw [hwsr, List.length_set]; exact hwslen
      · intro idx
        rw [hwsr, bitmapBit_setBit ws0 pc idx hbnd', hbit idx]
        have hstep := vjd_lt_step hreach hpclt idx
        rw [hadv1] at hstep
        simp only [hcode, true_and] at hstep
        rw [decide_eq_decide.mpr hstep, Bool.decide_or, Bool.or_comm]
    · -- NON-JUMPDEST arms (plain-<0x60 / PUSHn / plain-≥0x80)
      have hreg : (scanFn codeBase bitmapBase code).region = Region.mk codeBase code := rfl
      have hrwb : (scanFn codeBase bitmapBase code).rw.base = bitmapBase := rfl
      have hli : ∀ (r : RegFile) (w : List (BitVec 8)) (v : Word),
          execBlock (Region.mk codeBase code) bitmapBase r w [.LI .x29 v] = (r.set .x29 v, w) := by
        intro r w v; simp only [execBlock, execInstrRF, aluSem]
      rcases h with hplo | hplE
      · -- plain, code[pc] < 0x60
        obtain ⟨rf5, ws5, _, ⟨hR3, hcond⟩, hrfe, hwse⟩ := hplo
        obtain ⟨rf4, ws4, _, ⟨hR1, hnjd⟩, hrf5e, hws5e⟩ := hR3
        obtain ⟨rf3, ws3, _, hRload, hrf4e, hws4e⟩ := hR1
        obtain ⟨rf0, ws0, _, ⟨hinv, hguard⟩, hrf3e, hws3e⟩ := hRload
        obtain ⟨pc, hx5, hx6, hx7, hx30, hile, hreach, hwslen, hbit⟩ := hinv
        rw [hreg, hrwb] at hrfe hwse hrf5e hws5e hrf4e hws4e hrf3e hws3e
        simp only [Cond.holds, hx5, hx6] at hguard
        have hcap' : code.length ≤ 131072 := by simpa [bitmapCap] using hcap
        have hpc := EvmAsm.Stateless.SpecRef.Reaches_zero_le hreach
        have hpclt : pc < code.length :=
          lt_of_ult codeBase pc code.length (by omega) (by omega) hguard
        have hpc64 : pc < 2 ^ 64 := by omega
        have hnorw : ¬ inRw bitmapBase ws0 (rf0.get .x5 + signExtend12 0) 1 := by
          show ¬ (rf0.get .x5 + signExtend12 0 - bitmapBase).toNat + 1 ≤ ws0.length
          rw [hx5, hwslen, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
          have := hdisj pc (by omega); bv_omega
        have hload : execBlock (Region.mk codeBase code) bitmapBase rf0 ws0 [.LBU .x28 .x5 0]
            = (rf0.set .x28 ((code.getD pc 0).zeroExtend 64), ws0) := by
          simp only [execBlock, execInstrRF, aluSem, loadSem, if_neg hnorw, Region.byteAt]
          rw [show rf0.get .x5 + signExtend12 0 - codeBase = BitVec.ofNat 64 pc from by
                rw [hx5, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
            show (BitVec.ofNat 64 pc).toNat = pc from by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpc64]]
        rw [hrf3e, hws3e, hload] at hrf4e hws4e
        simp only [] at hrf4e hws4e
        rw [hli] at hrf4e hws4e
        simp only [] at hrf4e hws4e
        rw [hrf4e, hws4e, hli] at hrf5e hws5e
        simp only [] at hrf5e hws5e
        rw [hrf5e] at hcond
        rw [hrf5e, hws5e] at hrfe hwse
        have hcodeNe : (code.getD pc 0).toNat ≠ 0x5b := by
          rw [hrf4e] at hnjd
          simp only [Cond.holds, RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
            reduceCtorEq, not_false_eq_true] at hnjd
          intro h; apply hnjd; apply BitVec.eq_of_toNat_eq
          rw [toNat_zeroExtend_byte, h]; decide
        have hlt60 : (code.getD pc 0).toNat < 0x60 := by
          simp only [Cond.holds, BitVec.ult, RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, decide_eq_true_eq] at hcond
          rw [toNat_zeroExtend_byte] at hcond
          simpa using hcond
        have hadv : jdAdvance code pc = 1 := by
          simp only [jdAdvance]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        rw [hwse]
        refine nonjd_step codeBase bitmapBase code ws0 A' i pc _ hcodeNe hile hreach hpclt
          hwslen hbit ?_ ?_ ?_ ?_
        · rw [hrfe]; simp only [execBlock, execInstrRF, aluSem, RegFile.get_set_self,
            RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hadv, hx5]
          rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega
        · rw [hrfe]; simp only [execBlock, execInstrRF, aluSem, RegFile.get_set_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, hx6]
        · rw [hrfe]; simp only [execBlock, execInstrRF, aluSem, RegFile.get_set_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, hx7]
        · rw [hrfe]; simp only [execBlock, execInstrRF, aluSem, RegFile.get_set_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, hx30]
      · rcases hplE with hpush | hplHi
        · -- PUSHn, 0x60 ≤ code[pc] < 0x80
          obtain ⟨rf6, ws6, _, ⟨hR'', hphi⟩, hrfe, hwse⟩ := hpush
          obtain ⟨rf5, ws5, _, ⟨hR3, hnplo⟩, hrf6e, hws6e⟩ := hR''
          obtain ⟨rf4, ws4, _, ⟨hR1, hnjd⟩, hrf5e, hws5e⟩ := hR3
          obtain ⟨rf3, ws3, _, hRload, hrf4e, hws4e⟩ := hR1
          obtain ⟨rf0, ws0, _, ⟨hinv, hguard⟩, hrf3e, hws3e⟩ := hRload
          obtain ⟨pc, hx5, hx6, hx7, hx30, hile, hreach, hwslen, hbit⟩ := hinv
          rw [hreg, hrwb] at hrfe hwse hrf6e hws6e hrf5e hws5e hrf4e hws4e hrf3e hws3e
          simp only [Cond.holds, hx5, hx6] at hguard
          have hcap' : code.length ≤ 131072 := by simpa [bitmapCap] using hcap
          have hpc := EvmAsm.Stateless.SpecRef.Reaches_zero_le hreach
          have hpclt : pc < code.length :=
            lt_of_ult codeBase pc code.length (by omega) (by omega) hguard
          have hpc64 : pc < 2 ^ 64 := by omega
          have hnorw : ¬ inRw bitmapBase ws0 (rf0.get .x5 + signExtend12 0) 1 := by
            show ¬ (rf0.get .x5 + signExtend12 0 - bitmapBase).toNat + 1 ≤ ws0.length
            rw [hx5, hwslen, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
            have := hdisj pc (by omega); bv_omega
          have hload : execBlock (Region.mk codeBase code) bitmapBase rf0 ws0 [.LBU .x28 .x5 0]
              = (rf0.set .x28 ((code.getD pc 0).zeroExtend 64), ws0) := by
            simp only [execBlock, execInstrRF, aluSem, loadSem, if_neg hnorw, Region.byteAt]
            rw [show rf0.get .x5 + signExtend12 0 - codeBase = BitVec.ofNat 64 pc from by
                  rw [hx5, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
              show (BitVec.ofNat 64 pc).toNat = pc from by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpc64]]
          rw [hrf3e, hws3e, hload] at hrf4e hws4e
          simp only [] at hrf4e hws4e
          rw [hli] at hrf4e hws4e; simp only [] at hrf4e hws4e
          rw [hrf4e, hws4e, hli] at hrf5e hws5e; simp only [] at hrf5e hws5e
          rw [hrf5e, hws5e, hli] at hrf6e hws6e; simp only [] at hrf6e hws6e
          rw [hrf6e] at hphi
          have hcodeNe : (code.getD pc 0).toNat ≠ 0x5b := by
            rw [hrf4e] at hnjd
            simp only [Cond.holds, RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
              reduceCtorEq, not_false_eq_true] at hnjd
            intro h; apply hnjd; apply BitVec.eq_of_toNat_eq
            rw [toNat_zeroExtend_byte, h]; decide
          have hge60 : 0x60 ≤ (code.getD pc 0).toNat := by
            rw [hrf5e] at hnplo
            simp only [Cond.holds, BitVec.ult, RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
              reduceCtorEq, not_false_eq_true, decide_eq_true_eq, not_lt] at hnplo
            rw [toNat_zeroExtend_byte] at hnplo; simpa using hnplo
          have hlt80 : (code.getD pc 0).toNat < 0x80 := by
            simp only [Cond.holds, BitVec.ult, RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
              reduceCtorEq, not_false_eq_true, decide_eq_true_eq] at hphi
            rw [toNat_zeroExtend_byte] at hphi; simpa using hphi
          have hadv : jdAdvance code pc = (code.getD pc 0).toNat - 0x5e := by
            simp only [jdAdvance]; rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]; omega
          have hcb : (code.getD pc 0).zeroExtend 64 = BitVec.ofNat 64 (code.getD pc 0).toNat := by
            apply BitVec.eq_of_toNat_eq
            rw [toNat_zeroExtend_byte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hsig : BitVec.signExtend 64 (-94 : BitVec 12) = -(94 : Word) := by
            have h1 : (-94 : BitVec 12).toNat = 4002 := by decide
            have h2 : (-94 : BitVec 12).msb = true := by decide
            have h3 : (94 : Word).toNat = 94 := by decide
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_signExtend, if_pos h2, BitVec.toNat_setWidth, h1, BitVec.toNat_neg, h3]
          -- keep rf6 abstract; register facts proved shallowly from hrf6e
          have hr6x5 : rf6.get .x5 = codeBase + BitVec.ofNat 64 pc := by
            rw [hrf6e]; simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx5]
          have hr6x6 : rf6.get .x6 = codeBase + BitVec.ofNat 64 code.length := by
            rw [hrf6e]; simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx6]
          have hr6x7 : rf6.get .x7 = bitmapBase := by
            rw [hrf6e]; simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx7]
          have hr6x28 : rf6.get .x28 = (code.getD pc 0).zeroExtend 64 := by
            rw [hrf6e]; simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
          have hr6x30 : rf6.get .x30 = codeBase := by
            rw [hrf6e]; simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx30]
          have hws' : ws' = ws0 := by rw [hwse, pushArm_exec, hws6e]
          rw [hws']
          refine nonjd_step codeBase bitmapBase code ws0 A' i pc _ hcodeNe hile hreach hpclt
            hwslen hbit ?_ ?_ ?_ ?_
          · rw [hrfe, pushArm_exec, hadv]
            simp only [RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true,
              hr6x5, hr6x28, hcb, signExtend12, hsig]
            bv_omega
          · rw [hrfe, pushArm_exec]; simp only [RegFile.get_set_ne, ne_eq,
              reduceCtorEq, not_false_eq_true, hr6x6]
          · rw [hrfe, pushArm_exec]; simp only [RegFile.get_set_ne, ne_eq,
              reduceCtorEq, not_false_eq_true, hr6x7]
          · rw [hrfe, pushArm_exec]; simp only [RegFile.get_set_ne, ne_eq,
              reduceCtorEq, not_false_eq_true, hr6x30]
        · -- plain, code[pc] ≥ 0x80 (EIP-8024-free)
          obtain ⟨rf6, ws6, _, ⟨hR'', hnphi⟩, hrfe, hwse⟩ := hplHi
          obtain ⟨rf5, ws5, _, ⟨hR3, hnplo⟩, hrf6e, hws6e⟩ := hR''
          obtain ⟨rf4, ws4, _, ⟨hR1, hnjd⟩, hrf5e, hws5e⟩ := hR3
          obtain ⟨rf3, ws3, _, hRload, hrf4e, hws4e⟩ := hR1
          obtain ⟨rf0, ws0, _, ⟨hinv, hguard⟩, hrf3e, hws3e⟩ := hRload
          obtain ⟨pc, hx5, hx6, hx7, hx30, hile, hreach, hwslen, hbit⟩ := hinv
          rw [hreg, hrwb] at hrfe hwse hrf6e hws6e hrf5e hws5e hrf4e hws4e hrf3e hws3e
          simp only [Cond.holds, hx5, hx6] at hguard
          have hcap' : code.length ≤ 131072 := by simpa [bitmapCap] using hcap
          have hpc := EvmAsm.Stateless.SpecRef.Reaches_zero_le hreach
          have hpclt : pc < code.length :=
            lt_of_ult codeBase pc code.length (by omega) (by omega) hguard
          have hpc64 : pc < 2 ^ 64 := by omega
          have hnorw : ¬ inRw bitmapBase ws0 (rf0.get .x5 + signExtend12 0) 1 := by
            show ¬ (rf0.get .x5 + signExtend12 0 - bitmapBase).toNat + 1 ≤ ws0.length
            rw [hx5, hwslen, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
            have := hdisj pc (by omega); bv_omega
          have hload : execBlock (Region.mk codeBase code) bitmapBase rf0 ws0 [.LBU .x28 .x5 0]
              = (rf0.set .x28 ((code.getD pc 0).zeroExtend 64), ws0) := by
            simp only [execBlock, execInstrRF, aluSem, loadSem, if_neg hnorw, Region.byteAt]
            rw [show rf0.get .x5 + signExtend12 0 - codeBase = BitVec.ofNat 64 pc from by
                  rw [hx5, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
              show (BitVec.ofNat 64 pc).toNat = pc from by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpc64]]
          rw [hrf3e, hws3e, hload] at hrf4e hws4e
          simp only [] at hrf4e hws4e
          rw [hli] at hrf4e hws4e; simp only [] at hrf4e hws4e
          rw [hrf4e, hws4e, hli] at hrf5e hws5e; simp only [] at hrf5e hws5e
          rw [hrf5e, hws5e, hli] at hrf6e hws6e; simp only [] at hrf6e hws6e
          rw [hrf6e] at hnphi
          have hcodeNe : (code.getD pc 0).toNat ≠ 0x5b := by
            rw [hrf4e] at hnjd
            simp only [Cond.holds, RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
              reduceCtorEq, not_false_eq_true] at hnjd
            intro h; apply hnjd; apply BitVec.eq_of_toNat_eq
            rw [toNat_zeroExtend_byte, h]; decide
          have hge80 : 0x80 ≤ (code.getD pc 0).toNat := by
            simp only [Cond.holds, BitVec.ult, RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
              reduceCtorEq, not_false_eq_true, decide_eq_true_eq, not_lt] at hnphi
            rw [toNat_zeroExtend_byte] at hnphi; simpa using hnphi
          have hNe := hNoEip pc hpclt
          have hadv : jdAdvance code pc = 1 := by
            simp only [jdAdvance]
            rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          have hr6x5 : rf6.get .x5 = codeBase + BitVec.ofNat 64 pc := by
            rw [hrf6e]; simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx5]
          have hr6x6 : rf6.get .x6 = codeBase + BitVec.ofNat 64 code.length := by
            rw [hrf6e]; simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx6]
          have hr6x7 : rf6.get .x7 = bitmapBase := by
            rw [hrf6e]; simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx7]
          have hr6x30 : rf6.get .x30 = codeBase := by
            rw [hrf6e]; simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx30]
          have hws' : ws' = ws0 := by rw [hwse, plainArm_exec, hws6e]
          rw [hws']
          refine nonjd_step codeBase bitmapBase code ws0 A' i pc _ hcodeNe hile hreach hpclt
            hwslen hbit ?_ ?_ ?_ ?_
          · rw [hrfe, plainArm_exec, hadv]
            simp only [RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true, hr6x5,
              show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
            bv_omega
          · rw [hrfe, plainArm_exec]; simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true, hr6x6]
          · rw [hrfe, plainArm_exec]; simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true, hr6x7]
          · rw [hrfe, plainArm_exec]; simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true, hr6x30]


theorem scanFn_spec (codeBase bitmapBase : Word) (code : List (BitVec 8))
    (hcap : code.length ≤ bitmapCap)
    (hnowrap : codeBase.toNat + (code.length + 32) < 2 ^ 64)
    (hNoEip : ∀ k, k < code.length →
      (code.getD k 0).toNat ≠ 0xe6 ∧ (code.getD k 0).toNat ≠ 0xe7 ∧ (code.getD k 0).toNat ≠ 0xe8)
    (hwf : (Region.mk codeBase code).wf ∧ RwRegion.wf ⟨bitmapBase, bitmapBytes⟩)
    (hdisj : ∀ k, k ≤ code.length →
      bitmapBytes ≤ (codeBase + BitVec.ofNat 64 k - bitmapBase).toNat)
    (base : Word) :
    (scanFn codeBase bitmapBase code).Spec base := by
  vcgen
  case region => exact hwf
  case jdbmScan.scan.inv_init =>
    rintro rf ws A ⟨hx5, hx6, hx7, hx21, rfl⟩
    refine ⟨0, ?_, hx6, hx7, hx21, Nat.zero_le _, .refl _, ?_, ?_⟩
    · rw [hx5]; simp
    · exact List.length_replicate ..
    · intro idx
      rw [bitmapBit_replicate_zero]; simp
  case jdbmScan.scan.exhausted =>
    rintro rf ws A ⟨pc, hx5, hx6, -, -, hle, hreach, -, -⟩
    have hpc : pc ≤ code.length + 32 := EvmAsm.Stateless.SpecRef.Reaches_zero_le hreach
    simp only [Cond.holds, hx5, hx6]
    exact ult_ge codeBase pc code.length (by omega) (by omega) hle
  case jdbmScan.post =>
    rintro rf ws A ⟨⟨i, hile, pc, hx5, hx6, -, -, -, hreach, hwslen, hbit⟩, hncond⟩
    intro idx hidx
    have hpc : pc ≤ code.length + 32 := EvmAsm.Stateless.SpecRef.Reaches_zero_le hreach
    have hge : code.length ≤ pc := by
      simp only [Cond.holds, hx5, hx6] at hncond
      by_contra hlt
      exact hncond (ult_of_lt codeBase pc code.length (by omega) (by omega) (by omega))
    rw [hbit idx]
    have : (idx ∈ validJumpDestinations code ∧ idx < pc) ↔ idx ∈ validJumpDestinations code := by
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, by omega⟩
    simp [this]
  case jdbmScan.scan.body.load.mem =>
    rintro rf ws A hwslen ⟨i, hi, ⟨pc, hx5, hx6, hx7, hx30, hile, hreach, hwslen2, hbit⟩, hcond⟩
    have hpc := EvmAsm.Stateless.SpecRef.Reaches_zero_le hreach
    simp only [Cond.holds, hx5, hx6] at hcond
    have hpclt : pc < code.length := lt_of_ult codeBase pc code.length (by omega) (by omega) hcond
    have hd := hdisj pc (by omega)
    have hnorw : ¬ inRw (scanFn codeBase bitmapBase code).rw.base ws
        (rf.get .x5 + signExtend12 0) 1 := by
      show ¬ (rf.get .x5 + signExtend12 0 - bitmapBase).toNat + 1 ≤ ws.length
      rw [hx5, hwslen2, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      bv_omega
    simp only [blockVCs, loadSem]
    rw [if_neg hnorw]
    refine ⟨⟨one_dvd _, ?_⟩, trivial⟩
    show (rf.get .x5 + signExtend12 0 - codeBase).toNat + 1 ≤ code.length
    rw [hx5, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    have hpcv : (codeBase + BitVec.ofNat 64 pc + 0 - codeBase).toNat = pc := by bv_omega
    rw [hpcv]; omega
  case jdbmScan.scan.body.jd.t.jdset.mem =>
    rintro rf ws A hwslen ⟨hR, hjdc⟩
    obtain ⟨rfA, wsA, _, hRload, hrfe, hwse⟩ := hR
    obtain ⟨rf0, ws0, _, ⟨i, hi, hinv, hguard⟩, hrfAe, hwsAe⟩ := hRload
    obtain ⟨pc, hx5, hx6, hx7, hx30, hile, hreach, hwslen0, hbit⟩ := hinv
    have hreg : (scanFn codeBase bitmapBase code).region = Region.mk codeBase code := rfl
    have hrwb : (scanFn codeBase bitmapBase code).rw.base = bitmapBase := rfl
    rw [hreg, hrwb] at hrfe hwse hrfAe hwsAe
    simp only [Cond.holds, hx5, hx6] at hguard
    have hcap' : code.length ≤ 131072 := by simpa [bitmapCap] using hcap
    have hpc := EvmAsm.Stateless.SpecRef.Reaches_zero_le hreach
    have hpclt : pc < code.length := lt_of_ult codeBase pc code.length (by omega) (by omega) hguard
    have hpc64 : pc < 2 ^ 64 := by omega
    have hbnd' : pc / 8 < ws0.length := by rw [hwslen0]; simp only [bitmapBytes]; omega
    have hnorw : ¬ inRw bitmapBase ws0 (rf0.get .x5 + signExtend12 0) 1 := by
      show ¬ (rf0.get .x5 + signExtend12 0 - bitmapBase).toNat + 1 ≤ ws0.length
      rw [hx5, hwslen0, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      have := hdisj pc (by omega); bv_omega
    have hload : execBlock (Region.mk codeBase code) bitmapBase rf0 ws0 [.LBU .x28 .x5 0]
        = (rf0.set .x28 ((code.getD pc 0).zeroExtend 64), ws0) := by
      simp only [execBlock, execInstrRF, aluSem, loadSem, if_neg hnorw, Region.byteAt]
      rw [show rf0.get .x5 + signExtend12 0 - codeBase = BitVec.ofNat 64 pc from by
            rw [hx5, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
        show (BitVec.ofNat 64 pc).toNat = pc from by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpc64]]
    have hc5b : ∀ rf : RegFile,
        execBlock (Region.mk codeBase code) bitmapBase rf ws0 [.LI .x29 91]
        = (rf.set .x29 91, ws0) := by intro rf; simp only [execBlock, execInstrRF, aluSem]
    have hwsA0 : wsA = ws0 := by rw [hwsAe, hload]
    have hrfAv : rfA = rf0.set .x28 ((code.getD pc 0).zeroExtend 64) := by rw [hrfAe, hload]
    rw [hwsA0, hrfAv, hc5b] at hrfe hwse
    simp only [] at hrfe hwse
    have hsh : ((BitVec.ofNat 64 pc) >>> (3 : Nat)).toNat = pc / 8 := by
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpc64,
        Nat.shiftRight_eq_div_pow]
    have haddr : bitmapBase + (BitVec.ofNat 64 pc) >>> (3 : Nat) + 0 - bitmapBase
        = (BitVec.ofNat 64 pc) >>> (3 : Nat) := by bv_omega
    have hinrw : inRw bitmapBase ws0 (bitmapBase + (BitVec.ofNat 64 pc) >>> (3 : Nat) + 0) 1 := by
      show ((bitmapBase + (BitVec.ofNat 64 pc) >>> (3 : Nat) + 0) - bitmapBase).toNat + 1 ≤ ws0.length
      rw [haddr, hsh, hwslen0]; simp only [bitmapBytes]; omega
    rw [hreg, hrwb, hrfe, hwse]
    simp only [jdsetInstrs, blockVCs, execInstrRF, aluSem, loadSem, storeSem,
      RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true,
      hx5, hx7, hx30,
      show codeBase + BitVec.ofNat 64 pc - codeBase = BitVec.ofNat 64 pc from by bv_omega,
      show ((3 : BitVec 6).toNat) = 3 from rfl,
      show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      if_pos hinrw, Region.loadOk, haddr, hsh, true_and, and_true]
    exact ⟨⟨one_dvd _, by rw [hwslen0]; simp only [bitmapBytes]; omega⟩, hinrw, one_dvd _⟩
  case jdbmScan.scan.inv_step =>
    exact fun i hi rf' ws' A' hsp =>
      scanFn_inv_step codeBase bitmapBase code hcap hnowrap hNoEip hdisj i hi rf' ws' A' hsp

end EvmAsm.Codegen.Proofs.JumpdestBitmap
