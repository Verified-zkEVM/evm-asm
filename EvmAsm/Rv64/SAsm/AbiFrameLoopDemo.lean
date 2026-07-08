/-
  EvmAsm.Rv64.SAsm.AbiFrameLoopDemo

  End-to-end regression witness that the ABI-frame construct (`abiFrame_spec`,
  bead evm-asm-4ch8f.76) composes with an internal, fall-through loop whose
  accumulators live in *callee-saved* `s`-registers, discharged with a real
  loop invariant via the register-agnostic `countdownLoop_spec` bridge.

  A synthetic single-loop leaf routine — software multiply by repeated
  addition — with a standard C-ABI frame:

      addi sp, sp, -32       -- allocate frame
      sd   ra, 0(sp)         -- save ra
      sd   s0, 8(sp)         -- save s0 (callee-saved; used as accumulator)
      sd   s1, 16(sp)        -- save s1 (callee-saved; used as counter)
      li   s0, 0             -- body: acc  := 0        (s0 = LOCAL)
      mv   s1, a2            -- body: cnt  := a2 (= kw) (s1 = LOCAL)
    loop:
      beq  s1, x0, done      -- exit when the counter reaches 0
      add  s0, s0, a1        -- acc += a1 (= inc)
      addi s1, s1, -1        -- cnt -= 1
      jal  x0, loop          -- back-edge (fall-through loop, internal to body)
    done:
      sd   a0 <- s0          -- store acc to the caller's rw dword at [a0]
      ld   ra, 0(sp)         -- restore ra
      ld   s0, 8(sp)         -- restore s0
      ld   s1, 16(sp)        -- restore s1
      addi sp, sp, +32       -- deallocate frame
      ret

  The loop computes `acc = inc * kw` (mod 2^64) by adding `inc` exactly `kw`
  times.  The invariant carried through `countdownLoop_spec` is, at remaining
  count `n`, `s0 = inc * (K - n)` (with `K = kw.toNat`) — a genuine, nonvacuous
  loop invariant, NOT a `decide`-away shortcut.

  The post proves the whole ABI contract: on return `sp`, `ra`, `s0`, `s1` all
  equal their ENTRY values (the body clobbered `s0`/`s1` but the caller sees
  them preserved — preservation *derived* by `abiFrame_spec`'s frame rule),
  while the routine's real effect — the rw dword at `[a0]` now holds
  `inc * kw` — holds.

  Byte-transparency: `#guard`/`rfl` tie the `abiFrameProg` flatten to the
  spelled-out 16-instruction program.
-/

import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.AbiFrameLoop
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.Tactics.XSimp
import Mathlib.Data.BitVec

namespace EvmAsm.Rv64
namespace SAsm
namespace AbiFrameLoopDemo

open EvmAsm.Rv64.Tactics

/-- The 3-slot demo frame: `ra` at 0, `s0` at 8, `s1` at 16. -/
def mulFrame : FrameDesc := [(.x1, 0), (.x8, 8), (.x9, 16)]

/-- Body: software multiply by repeated addition, with `s0`/`s1` as loop-local
    accumulator/counter and an internal fall-through loop. -/
def mulBody : List Instr :=
  [ .LI .x8 (0 : Word),            -- s0 := 0        (acc)
    .MV .x9 .x12,                  -- s1 := a2       (counter = kw)
    .BEQ .x9 .x0 (16 : BitVec 13), -- loop header: exit when counter = 0
    .ADD .x8 .x8 .x11,             -- acc += a1      (inc)
    .ADDI .x9 .x9 (-1 : BitVec 12),-- counter -= 1
    .JAL .x0 (-12 : BitVec 21),    -- back-edge to header
    .SD .x10 .x8 (0 : BitVec 12) ] -- store acc to [a0]

/-- The full frame routine (16 instructions), as an `abiFrameProg`. -/
def mulProg : List Instr :=
  abiFrameProg (-32 : BitVec 12) (32 : BitVec 12) mulFrame mulBody

/-- The same 16 instructions spelled out (used for the routine `CodeReq`). -/
def mulProgList : List Instr :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .LI .x8 (0 : Word),
    .MV .x9 .x12,
    .BEQ .x9 .x0 (16 : BitVec 13),
    .ADD .x8 .x8 .x11,
    .ADDI .x9 .x9 (-1 : BitVec 12),
    .JAL .x0 (-12 : BitVec 21),
    .SD .x10 .x8 (0 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

-- Byte-transparency: the frame routine is exactly prologue ++ body ++
-- epilogue ++ ret, spelled out.
#guard mulProg = mulProgList

/-- Byte-transparency as a `rfl`-checked theorem (kernel-verified). -/
theorem mulProg_eq : mulProg = mulProgList := rfl

/-- The routine CodeReq: exactly the flattened routine at `0x1000`. -/
def mulCr : CodeReq := CodeReq.ofProg 0x1000 mulProgList

-- ============================================================================
-- Arithmetic helpers for the loop invariant `s0 = inc * (K - n)`.
-- ============================================================================

/-- `ofNat a + ofNat b = ofNat (a + b)` (pure wrap-around BitVec arithmetic). -/
private theorem ofNat_add (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The accumulator step: `inc * (K - (n+1)) + inc = inc * (K - n)` when `n < K`. -/
private theorem acc_step (inc : Word) (K n : Nat) (hn : n < K) :
    inc * BitVec.ofNat 64 (K - (n + 1)) + inc = inc * BitVec.ofNat 64 (K - n) := by
  have h1 : BitVec.ofNat 64 (K - (n + 1)) + 1 = BitVec.ofNat 64 (K - n) := by
    rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, ofNat_add,
        show K - (n + 1) + 1 = K - n from by omega]
  calc inc * BitVec.ofNat 64 (K - (n + 1)) + inc
      = inc * (BitVec.ofNat 64 (K - (n + 1)) + 1) := by
        rw [mul_add, mul_one]
    _ = inc * BitVec.ofNat 64 (K - n) := by rw [h1]

/-- The counter step: `ofNat (n+1) + sext(-1) = ofNat n`. -/
private theorem cnt_step (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  have e1 : BitVec.ofNat 64 (n + 1) = BitVec.ofNat 64 n + 1 := by
    rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, ofNat_add]
  rw [e1, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide,
      BitVec.add_assoc, show (1 : Word) + (-1 : Word) = 0 from by decide, add_zero]

-- ============================================================================
-- The loop invariant and the per-iteration body triple.
-- ============================================================================

/-- Loop invariant at remaining count `n`: `s0 = inc * (K - n)`, plus the stable
    `inc` (`a1`) and out-pointer (`a0`). -/
def mulInv (inc outPtr : Word) (K : Nat) (n : Nat) : Assertion :=
  (.x8 ↦ᵣ (inc * BitVec.ofNat 64 (K - n))) ** (.x11 ↦ᵣ inc) ** (.x10 ↦ᵣ outPtr)

theorem pcFree_mulInv (inc outPtr : Word) (K n : Nat) : (mulInv inc outPtr K n).pcFree :=
  pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs pcFree_regIs)

/-- **The per-iteration loop body** (`add ; addi ; jal-back`, `0x101C → 0x1018`):
    `acc += inc`, `cnt -= 1`, back-edge to the header.  Discharges the loop's
    `hbody` obligation. -/
theorem mulLoopBody_spec (inc outPtr : Word) (K n : Nat) (hn : n < K) :
    cpsTripleWithin 3 (0x101C : Word) (0x1018 : Word) mulCr
      ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (Reg.x0 ↦ᵣ (0 : Word)) ** mulInv inc outPtr K (n + 1))
      ((.x9 ↦ᵣ BitVec.ofNat 64 n) ** (Reg.x0 ↦ᵣ (0 : Word)) ** mulInv inc outPtr K n) := by
  simp only [mulInv, mulCr, mulProgList, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right]
  -- ADD s0, s0, a1  (acc += inc), at 0x101C.
  have hadd := add_spec_gen_rd_eq_rs1_within .x8 .x11
    (inc * BitVec.ofNat 64 (K - (n + 1))) inc (0x101C : Word) (by decide)
  rw [acc_step inc K n hn] at hadd
  -- ADDI s1, s1, -1  (cnt -= 1), at 0x1020.
  have haddi := addi_spec_gen_same_within .x9 (BitVec.ofNat 64 (n + 1)) (-1 : BitVec 12)
    (0x1020 : Word) (by decide)
  rw [cnt_step n] at haddi
  -- JAL x0, -12  (back-edge), at 0x1024 → 0x1018.
  have hjal := jal_x0_spec_gen_within (-12 : BitVec 21) (0x1024 : Word)
  rw [show (0x1024 : Word) + signExtend21 (-12 : BitVec 21) = (0x1018 : Word) from by decide] at hjal
  runBlock hadd haddi hjal

/-- **The loop** (`0x1018 → 0x1028`): counter drains from `K` to `0`, leaving
    `s0 = inc * K = inc * kw`.  Instantiates the register-agnostic
    `countdownLoop_spec` with the `s`-register counter `s1` and the
    `s0`-accumulator invariant. -/
theorem mulLoop_spec (inc outPtr kw : Word) :
    cpsTripleWithin (kw.toNat * (3 + 1) + 1) (0x1018 : Word) (0x1028 : Word) mulCr
      ((.x9 ↦ᵣ BitVec.ofNat 64 kw.toNat) ** (Reg.x0 ↦ᵣ (0 : Word)) ** mulInv inc outPtr kw.toNat kw.toNat)
      ((.x9 ↦ᵣ BitVec.ofNat 64 0) ** (Reg.x0 ↦ᵣ (0 : Word)) ** mulInv inc outPtr kw.toNat 0) := by
  countdown_loop (16 : BitVec 13) (fun n hn => mulLoopBody_spec inc outPtr kw.toNat n hn)

/-- **The prefix** (`li s0,0 ; mv s1,a2`, `0x1010 → 0x1018`): initialize the
    accumulator and load the counter. -/
theorem mulPrefix_spec (kw arb8 arb9 : Word) :
    cpsTripleWithin 2 (0x1010 : Word) (0x1018 : Word) mulCr
      ((.x8 ↦ᵣ arb8) ** (.x9 ↦ᵣ arb9) ** (.x12 ↦ᵣ kw))
      ((.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ kw) ** (.x12 ↦ᵣ kw)) := by
  simp only [mulCr, mulProgList, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right]
  have hli := li_spec_gen_within .x8 arb8 (0 : Word) (0x1010 : Word) (by decide)
  have hmv := mv_spec_gen_within .x9 .x12 kw arb9 (0x1014 : Word) (by decide)
  runBlock hli hmv

/-- **The suffix** (`sd a0 <- s0`, `0x1028 → 0x102C`): store the accumulator to
    the caller's rw dword at `[a0]`. -/
theorem mulSuffix_spec (data outPtr oldD : Word) :
    cpsTripleWithin 1 (0x1028 : Word) (0x102C : Word) mulCr
      ((.x10 ↦ᵣ outPtr) ** (.x8 ↦ᵣ data) ** (outPtr ↦ₘ oldD))
      ((.x10 ↦ᵣ outPtr) ** (.x8 ↦ᵣ data) ** (outPtr ↦ₘ data)) := by
  simp only [mulCr, mulProgList, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right]
  have hsd := sd_spec_gen_within .x10 .x8 outPtr data oldD (0 : BitVec 12) (0x1028 : Word)
  rw [show outPtr + signExtend12 (0 : BitVec 12) = outPtr from by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide, add_zero]] at hsd
  runBlock hsd

/-- **The full body core** (`0x1010 → 0x102C`): prefix · loop · suffix, over the
    working set with the callee-saved `s`-registers `s0`/`s1` EXPOSED as owned
    `↦ᵣ` atoms.  On exit `s0 = inc * kw`, `s1 = 0`, and the rw dword at `[a0]`
    holds `inc * kw`. -/
theorem mulCore_spec (inc kw outPtr arb8 arb9 oldD : Word) :
    cpsTripleWithin (2 + (kw.toNat * (3 + 1) + 1) + 1) (0x1010 : Word) (0x102C : Word) mulCr
      ((.x8 ↦ᵣ arb8) ** (.x9 ↦ᵣ arb9) ** (.x12 ↦ᵣ kw) ** (.x11 ↦ᵣ inc)
        ** (.x10 ↦ᵣ outPtr) ** (Reg.x0 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ oldD))
      ((.x8 ↦ᵣ (inc * kw)) ** (.x9 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ kw) ** (.x11 ↦ᵣ inc)
        ** (.x10 ↦ᵣ outPtr) ** (Reg.x0 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ (inc * kw))) := by
  have hkw : BitVec.ofNat 64 kw.toNat = kw := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt kw.isLt]
  -- Prefix, framed with the loop/store inputs.
  have hpre := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ inc) ** (.x10 ↦ᵣ outPtr) ** (Reg.x0 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ oldD))
    (by pcFree) (mulPrefix_spec kw arb8 arb9)
  -- Loop, framed with the stable a2 (kw) and the untouched rw dword.
  have hloop0 := mulLoop_spec inc outPtr kw
  simp only [mulInv] at hloop0
  -- Present the loop's endpoints with concrete `kw`, `0`, and `inc*kw`.
  have e0 : inc * BitVec.ofNat 64 (kw.toNat - kw.toNat) = (0 : Word) := by
    rw [Nat.sub_self, show BitVec.ofNat 64 0 = (0 : Word) from rfl, mul_zero]
  have eK : inc * BitVec.ofNat 64 (kw.toNat - 0) = inc * kw := by
    rw [Nat.sub_zero, hkw]
  rw [hkw, e0, eK, show BitVec.ofNat 64 0 = (0 : Word) from rfl] at hloop0
  have hloop := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ kw) ** (outPtr ↦ₘ oldD)) (by pcFree) hloop0
  -- Suffix, framed with the untouched registers.
  have hsuf := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ inc) ** (Reg.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ kw))
    (by pcFree) (mulSuffix_spec (inc * kw) outPtr oldD)
  -- Chain prefix ; loop ; suffix.
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hpre hloop
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hsuf
  refine cpsTripleWithin_weaken ?_ ?_ (cpsTripleWithin_mono_nSteps (by omega) s2)
  · intro h hp; xperm_hyp hp
  · intro h hp; xperm_hyp hp

-- ============================================================================
-- The whole-routine ABI contract, derived from `abiFrame_spec`.
-- ============================================================================

/-- Entry register values: `ra ↦ ret`, `s0 ↦ arb8`, `s1 ↦ arb9` (the caller's
    callee-saved values, arbitrary — the body clobbers `s0`/`s1`). -/
def mulVals (ret arb8 arb9 : Word) : Reg → Word := fun r =>
  match r with | .x1 => ret | .x8 => arb8 | .x9 => arb9 | _ => 0

/-- Post-body register values: `ra` untouched (`ret`), `s0 ↦ inc*kw`, `s1 ↦ 0`. -/
def mulVals' (ret inc kw : Word) : Reg → Word := fun r =>
  match r with | .x1 => ret | .x8 => inc * kw | .x9 => (0 : Word) | _ => 0

/-- Caller footprint before the body: `a0` (out ptr), `a1` (inc), `a2` (kw =
    count), the zero register, and the rw dword (arbitrary contents `oldD`). -/
def mulCallerPre (inc kw outPtr oldD : Word) : Assertion :=
  (.x10 ↦ᵣ outPtr) ** (.x11 ↦ᵣ inc) ** (.x12 ↦ᵣ kw) ** (Reg.x0 ↦ᵣ (0 : Word))
    ** (outPtr ↦ₘ oldD)

/-- Caller footprint after the body: the rw dword now holds `inc * kw`. -/
def mulCallerPost (inc kw outPtr : Word) : Assertion :=
  (.x10 ↦ᵣ outPtr) ** (.x11 ↦ᵣ inc) ** (.x12 ↦ᵣ kw) ** (Reg.x0 ↦ᵣ (0 : Word))
    ** (outPtr ↦ₘ (inc * kw))

/-- **The ABI-frame contract for the software-multiply leaf, derived from
    `abiFrame_spec`.**  Running the whole routine from entry `0x1000` returns to
    `ret` with `sp`, `ra`, `s0`, `s1` all restored to their entry values (the
    body used `s0`/`s1` as loop-locals; preservation is *derived* by the frame
    rule) and the rw dword at `[a0]` (`outPtr`) holding `inc * kw` — the genuine
    software-multiply result computed by the internal counting loop. -/
theorem mulFrame_spec (ret inc kw outPtr arb8 arb9 oldD : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (1 + mulFrame.length + (2 + (kw.toNat * (3 + 1) + 1) + 1)
        + mulFrame.length + 1 + 1) 0x1000 ret mulCr
      ((.x2 ↦ᵣ (0x30000 : Word)) ** regsAt mulFrame (mulVals ret arb8 arb9)
        ** frameSlotsOwn mulFrame ((0x30000 : Word) + signExtend12 (-32 : BitVec 12))
        ** mulCallerPre inc kw outPtr oldD)
      ((.x2 ↦ᵣ (0x30000 : Word)) ** regsAt mulFrame (mulVals ret arb8 arb9)
        ** frameSlotsSaved mulFrame ((0x30000 : Word) + signExtend12 (-32 : BitVec 12))
            (mulVals ret arb8 arb9)
        ** mulCallerPost inc kw outPtr) := by
  set newSp := (0x30000 : Word) + signExtend12 (-32 : BitVec 12) with hNS
  have hns : newSp = (0x2FFE0 : Word) := by rw [hNS]; decide
  have hbody :
      cpsTripleWithin (2 + (kw.toNat * (3 + 1) + 1) + 1)
        ((0x1000 : Word) + BitVec.ofNat 64 (4 * (1 + mulFrame.length)))
        ((0x1000 : Word) + BitVec.ofNat 64 (4 * (1 + mulFrame.length + mulBody.length)))
        mulCr
        ((.x2 ↦ᵣ newSp) ** regsAt mulFrame (mulVals ret arb8 arb9)
          ** frameSlotsSaved mulFrame newSp (mulVals ret arb8 arb9)
          ** mulCallerPre inc kw outPtr oldD)
        ((.x2 ↦ᵣ newSp) ** regsAt mulFrame (mulVals' ret inc kw)
          ** frameSlotsSaved mulFrame newSp (mulVals ret arb8 arb9)
          ** mulCallerPost inc kw outPtr) := by
    have hentry : (0x1000 : Word) + BitVec.ofNat 64 (4 * (1 + mulFrame.length))
        = (0x1010 : Word) := by decide
    have hexit : (0x1000 : Word) + BitVec.ofNat 64 (4 * (1 + mulFrame.length + mulBody.length))
        = (0x102C : Word) := by decide
    rw [hentry, hexit, hns]
    simp only [mulFrame, regsAt, frameSlotsSaved, mulVals, mulVals',
      mulCallerPre, mulCallerPost, List.foldr_cons, List.foldr_nil, sepConj_emp_right']
    rw [show (0x2FFE0 : Word) + signExtend12 (0 : BitVec 12) = (0x2FFE0 : Word) from by decide,
        show (0x2FFE0 : Word) + signExtend12 (8 : BitVec 12) = (0x2FFE8 : Word) from by decide,
        show (0x2FFE0 : Word) + signExtend12 (16 : BitVec 12) = (0x2FFF0 : Word) from by decide]
    -- Frame `sp`, `ra`, and the (untouched) save slots around the exposed body core.
    have hframed := cpsTripleWithin_frameR
      ((.x2 ↦ᵣ (0x2FFE0 : Word)) ** (.x1 ↦ᵣ ret)
        ** ((0x2FFE0 : Word) ↦ₘ ret) ** ((0x2FFE8 : Word) ↦ₘ arb8) ** ((0x2FFF0 : Word) ↦ₘ arb9))
      (by pcFree) (mulCore_spec inc kw outPtr arb8 arb9 oldD)
    exact cpsTripleWithin_weaken (by xsimp) (by xsimp) hframed
  abi_frame (32 : BitVec 12) halign hbody

#print axioms countdownLoop_spec
#print axioms mulFrame_spec

end AbiFrameLoopDemo
end SAsm
end EvmAsm.Rv64
