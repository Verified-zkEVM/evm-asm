/-
  EvmAsm.Rv64.SAsm.AbiFrameDemo

  End-to-end witness for the ABI-frame construct (bead evm-asm-4ch8f.76),
  mirroring `DoWhileBreakDemo.lean`.

  A synthetic leaf routine with a standard C-ABI frame:

      addi sp, sp, -24      -- allocate frame
      sd   ra, 0(sp)        -- save ra
      sd   s0, 8(sp)        -- save s0 (callee-saved)
      sd   s1, 16(sp)       -- save s1 (callee-saved)
      add  s0, a0, a1       -- body: s0 := a0 + a1   (s0 used as a LOCAL)
      add  s1, s0, a0       -- body: s1 := s0 + a0   (s1 clobbered, uses s0)
      sd   a2, s0 -> [a2]   -- body: store s0 to the caller's rw dword
      ld   ra, 0(sp)        -- restore ra
      ld   s0, 8(sp)        -- restore s0
      ld   s1, 16(sp)       -- restore s1
      addi sp, sp, +24      -- deallocate frame
      ret

  The post proves the ABI contract: on return `sp`, `ra`, `s0`, `s1` all equal
  their ENTRY values (the body clobbered `s0`/`s1` but the caller sees them
  preserved), while the routine's real effect — the rw dword at `[a2]` now
  holds `a0 + a1` — holds.  Preservation is derived from the frame rule (the
  save slots sit in the `cpsTripleWithin` frame during the body), never
  assumed.
-/

import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.Fn
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64
namespace SAsm
namespace AbiFrameDemo

open EvmAsm.Rv64.Tactics

/-- Body: use the callee-saved registers as locals and write the result to the
    caller's rw dword (held in `a2`). -/
def demoBody : List Instr :=
  [ .ADD .x8 .x10 .x11,     -- s0 := a0 + a1
    .ADD .x9 .x8 .x10,      -- s1 := s0 + a0
    .SD .x12 .x8 0 ]        -- store s0 to [a2]

/-- The straight-line part (prologue ++ body ++ epilogue, no `ret`). -/
def blockProg : List Instr :=
  framePrologue (-24 : BitVec 12) ++ demoBody ++ frameEpilogue (24 : BitVec 12)

/-- The full frame routine (12 instructions). -/
def demoProg : List Instr :=
  abiFrameProg (-24 : BitVec 12) (24 : BitVec 12) demoBody

/-- `demoProg` is the straight-line block followed by the `ret`. -/
theorem demoProg_eq : demoProg = blockProg ++ [.JALR .x0 .x1 0] := rfl

theorem blockProg_length : blockProg.length = 11 := rfl

/-- The code requirement: each of the 12 instructions of `demoProg` sits at its
    address (`0x1000 + 4*k`), spelled as a `union` chain of singletons — the
    shape the block engine consumes.  Faithful to `demoProg` by construction
    (same instructions, same addresses; see the `#guard` above). -/
def demoCr : CodeReq :=
  (CodeReq.singleton 0x1000 (.ADDI .x2 .x2 (-24 : BitVec 12))).union <|
  (CodeReq.singleton 0x1004 (.SD .x2 .x1 0)).union <|
  (CodeReq.singleton 0x1008 (.SD .x2 .x8 8)).union <|
  (CodeReq.singleton 0x100C (.SD .x2 .x9 16)).union <|
  (CodeReq.singleton 0x1010 (.ADD .x8 .x10 .x11)).union <|
  (CodeReq.singleton 0x1014 (.ADD .x9 .x8 .x10)).union <|
  (CodeReq.singleton 0x1018 (.SD .x12 .x8 0)).union <|
  (CodeReq.singleton 0x101C (.LD .x1 .x2 0)).union <|
  (CodeReq.singleton 0x1020 (.LD .x8 .x2 8)).union <|
  (CodeReq.singleton 0x1024 (.LD .x9 .x2 16)).union <|
  (CodeReq.singleton 0x1028 (.ADDI .x2 .x2 (24 : BitVec 12))).union
  (CodeReq.singleton 0x102C (.JALR .x0 .x1 0))


-- Byte-transparency: the frame routine is exactly prologue ++ body ++
-- epilogue ++ ret, spelled out.
#guard demoProg =
  [ .ADDI .x2 .x2 (-24 : BitVec 12),
    .SD .x2 .x1 0,
    .SD .x2 .x8 8,
    .SD .x2 .x9 16,
    .ADD .x8 .x10 .x11,
    .ADD .x9 .x8 .x10,
    .SD .x12 .x8 0,
    .LD .x1 .x2 0,
    .LD .x8 .x2 8,
    .LD .x9 .x2 16,
    .ADDI .x2 .x2 (24 : BitVec 12),
    .JALR .x0 .x1 0 ]

-- Concrete layout: code at 0x1000, stack pointer 0x30000, rw target 0x31000.
-- (Symbolic register/memory *values* are parameters; only addresses are fixed
--  so the frame-slot alignment/validity is decidable.)

/-- The straight-line part (prologue ++ body ++ epilogue, 11 instructions),
    from entry `0x1000` to `0x1000 + 44`. -/
theorem demoBlock_spec (ret v0 v1 va0 va1 j0 j8 j16 jt : Word) :
    cpsTripleWithin 11 0x1000 (0x1000 + 44)
      demoCr
      ((.x2 ↦ᵣ (0x30000 : Word)) ** (.x1 ↦ᵣ ret) ** ((0x2FFE8 : Word) ↦ₘ j0) **
        (.x8 ↦ᵣ v0) ** ((0x2FFF0 : Word) ↦ₘ j8) ** (.x9 ↦ᵣ v1) ** ((0x2FFF8 : Word) ↦ₘ j16) **
        (.x10 ↦ᵣ va0) ** (.x11 ↦ᵣ va1) ** (.x12 ↦ᵣ (0x31000 : Word)) **
        ((0x31000 : Word) ↦ₘ jt))
      ((.x2 ↦ᵣ (0x30000 : Word)) ** (.x1 ↦ᵣ ret) ** ((0x2FFE8 : Word) ↦ₘ ret) **
        (.x8 ↦ᵣ v0) ** ((0x2FFF0 : Word) ↦ₘ v0) ** (.x9 ↦ᵣ v1) ** ((0x2FFF8 : Word) ↦ₘ v1) **
        (.x10 ↦ᵣ va0) ** (.x11 ↦ᵣ va1) ** (.x12 ↦ᵣ (0x31000 : Word)) **
        ((0x31000 : Word) ↦ₘ (va0 + va1)))
      := by
  simp only [demoCr]
  have hneg : (0x30000 : Word) + signExtend12 (-24 : BitVec 12) = (0x2FFE8 : Word) := by decide
  have hpos : (0x2FFE8 : Word) + signExtend12 (24 : BitVec 12) = (0x30000 : Word) := by decide
  have s1 := addi_spec_gen_same_within .x2 (0x30000 : Word) (-24 : BitVec 12) 0x1000 (by decide)
  rw [hneg] at s1
  have s2 := sd_spec_gen_within .x2 .x1 (0x2FFE8 : Word) ret j0 0 0x1004
  have s3 := sd_spec_gen_within .x2 .x8 (0x2FFE8 : Word) v0 j8 8 0x1008
  have s4 := sd_spec_gen_within .x2 .x9 (0x2FFE8 : Word) v1 j16 16 0x100C
  have s5 := add_spec_gen_within .x8 .x10 .x11 va0 va1 v0 0x1010 (by decide)
  have s6 := add_spec_gen_within .x9 .x8 .x10 (va0 + va1) va0 v1 0x1014 (by decide)
  have s7 := sd_spec_gen_within .x12 .x8 (0x31000 : Word) (va0 + va1) jt 0 0x1018
  have s8 := ld_spec_gen_within .x1 .x2 (0x2FFE8 : Word) ret ret 0 0x101C (by decide)
  have s9 := ld_spec_gen_within .x8 .x2 (0x2FFE8 : Word) (va0 + va1) v0 8 0x1020 (by decide)
  have s10 := ld_spec_gen_within .x9 .x2 (0x2FFE8 : Word) ((va0 + va1) + va0) v1 16 0x1024 (by decide)
  have s11 := addi_spec_gen_same_within .x2 (0x2FFE8 : Word) (24 : BitVec 12) 0x1028 (by decide)
  rw [hpos] at s11
  -- reduce each store/load cell address `sp + signExtend12 ofs` to its numeral
  have ea : (0x2FFE8 : Word) + signExtend12 (0 : BitVec 12) = (0x2FFE8 : Word) := by decide
  have eb : (0x2FFE8 : Word) + signExtend12 (8 : BitVec 12) = (0x2FFF0 : Word) := by decide
  have ec : (0x2FFE8 : Word) + signExtend12 (16 : BitVec 12) = (0x2FFF8 : Word) := by decide
  have ed : (0x31000 : Word) + signExtend12 (0 : BitVec 12) = (0x31000 : Word) := by decide
  rw [ea] at s2
  rw [ea] at s8
  rw [eb] at s3
  rw [eb] at s9
  rw [ec] at s4
  rw [ec] at s10
  rw [ed] at s7
  runBlock s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11

/-- **The ABI-frame contract, proven end-to-end.**  Running the whole routine
    (prologue, body, epilogue, `ret`) from entry `0x1000` returns to `ret`
    within 12 steps with:

    * `sp` (x2), `ra` (x1), and the callee-saved `s0` (x8), `s1` (x9) **all
      equal to their entry values** — the body clobbered `s0`/`s1` (and used
      them as locals) but the caller sees them preserved;
    * the routine's real effect held: the caller's rw dword at `[a2]` (`0x31000`)
      now holds `a0 + a1`;
    * the frame slots below the entry `sp` hold the saved values (frame
      released — the caller regains the stack space, contents known).

    Callee-saved preservation is *derived*, never assumed: the prologue writes
    the entry `ra`/`s0`/`s1` into the frame slots; the body runs with those
    slots in the `cpsTripleWithin` frame (untouched by its scratch use of the
    `s`-registers); the epilogue reads the entry values straight back. -/
theorem demoFrame_spec (ret v0 v1 va0 va1 j0 j8 j16 jt : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 12 0x1000 ret demoCr
      ((.x2 ↦ᵣ (0x30000 : Word)) ** (.x1 ↦ᵣ ret) ** ((0x2FFE8 : Word) ↦ₘ j0) **
        (.x8 ↦ᵣ v0) ** ((0x2FFF0 : Word) ↦ₘ j8) ** (.x9 ↦ᵣ v1) ** ((0x2FFF8 : Word) ↦ₘ j16) **
        (.x10 ↦ᵣ va0) ** (.x11 ↦ᵣ va1) ** (.x12 ↦ᵣ (0x31000 : Word)) **
        ((0x31000 : Word) ↦ₘ jt))
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ (0x30000 : Word)) ** ((0x2FFE8 : Word) ↦ₘ ret) **
        (.x8 ↦ᵣ v0) ** ((0x2FFF0 : Word) ↦ₘ v0) ** (.x9 ↦ᵣ v1) ** ((0x2FFF8 : Word) ↦ₘ v1) **
        (.x10 ↦ᵣ va0) ** (.x11 ↦ᵣ va1) ** (.x12 ↦ᵣ (0x31000 : Word)) **
        ((0x31000 : Word) ↦ₘ (va0 + va1))) := by
  have block := demoBlock_spec ret v0 v1 va0 va1 j0 j8 j16 jt
  have jalr := Fn.jalr_ret_spec (0x1000 + 44) ret halign
    (P := (.x2 ↦ᵣ (0x30000 : Word)) ** ((0x2FFE8 : Word) ↦ₘ ret) **
      (.x8 ↦ᵣ v0) ** ((0x2FFF0 : Word) ↦ₘ v0) ** (.x9 ↦ᵣ v1) ** ((0x2FFF8 : Word) ↦ₘ v1) **
      (.x10 ↦ᵣ va0) ** (.x11 ↦ᵣ va1) ** (.x12 ↦ᵣ (0x31000 : Word)) **
      ((0x31000 : Word) ↦ₘ (va0 + va1))) (by pcFree)
  have jalr' := cpsTripleWithin_extend_code
    (CodeReq.singleton_mono (cr := demoCr) (by simp only [demoCr]; decide)) jalr
  exact cpsTripleWithin_seq_perm_same_cr (by xsimp) block jalr'

#print axioms demoBlock_spec
#print axioms demoFrame_spec

end AbiFrameDemo
end SAsm
end EvmAsm.Rv64
