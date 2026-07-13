/-
  EvmAsm.Codegen.Programs.Bn254Field

  Codegen-only BN254 (alt_bn128) base-field helpers for the 0x06/0x07/0x08
  EVM precompiles (EIP-196/EIP-197). Values are 32-byte big-endian field
  elements over

    p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
      = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47

  The modular multiply and add are backed by the ziskemu `Arith256Mod`
  accelerator (`csrs 0x802` with a parameter-block pointer, emitted as a
  pre-encoded `.4byte 0x8022a073` so the plain `rv64imac` toolchain
  assembles it — the same route as `Secp256k1Field`'s `secf_mul_mod_p`):

    * mul: d = (a*b + 0) mod p  (params block `bnf_mul_params`)
    * add: d = (a*1 + b) mod p  (params block `bnf_add_params`)

  Both run with exact 512-bit intermediate math, so unreduced 256-bit
  inputs are accepted and outputs are always fully reduced. Inputs convert
  between the 32-byte big-endian call surface and the accelerator's
  little-endian u64-limb format via `bnf_be_to_le` / `bnf_le_to_be`.

  All helpers are `bnf_`-prefixed so closures can link this chain next to
  the secp256k1 (`secf_`) chain without label clashes, and the chain is
  fully self-contained (no `u256_*` dependencies).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Rv64.SAsm.WhileBreakDemo

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.WhileBreakDemo
open EvmAsm.Rv64.SAsm.Stmt

/-- BN254 base-field data labels WITHOUT a `.section .data` header, for
    appending to an existing data section (the runtime dispatcher data
    core). `bn254FieldDataSection` adds the header for standalone probes. -/
def bn254FieldDataFragment : String :=
  ".balign 8\n" ++
  "bnf_p_be:\n" ++
  "  .byte 0x30,0x64,0x4e,0x72,0xe1,0x31,0xa0,0x29\n" ++
  "  .byte 0xb8,0x50,0x45,0xb6,0x81,0x81,0x58,0x5d\n" ++
  "  .byte 0x97,0x81,0x6a,0x91,0x68,0x71,0xca,0x8d\n" ++
  "  .byte 0x3c,0x20,0x8c,0x16,0xd8,0x7c,0xfd,0x47\n" ++
  -- Curve constant b = 3 (y^2 = x^3 + 3), as a 32-byte BE field element.
  "bnf_b_be:\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x03\n" ++
  -- Little-endian 4x-u64-limb staging for the ziskemu `Arith256Mod`
  -- accelerator (`d = (a*b + c) mod module`), plus its two static parameter
  -- blocks: mul uses c = 0 (`bnf_le_zero`), add uses b = 1 (`bnf_le_one`)
  -- with the addend in the c slot (`bnf_le_b`).
  ".balign 8\n" ++
  "bnf_le_a:\n" ++
  "  .fill 32, 1, 0\n" ++
  "bnf_le_b:\n" ++
  "  .fill 32, 1, 0\n" ++
  "bnf_le_d:\n" ++
  "  .fill 32, 1, 0\n" ++
  "bnf_le_zero:\n" ++
  "  .fill 32, 1, 0\n" ++
  "bnf_le_one:\n" ++
  "  .quad 1, 0, 0, 0\n" ++
  "bnf_le_p:\n" ++
  "  .quad 0x3C208C16D87CFD47, 0x97816A916871CA8D\n" ++
  "  .quad 0xB85045B68181585D, 0x30644E72E131A029\n" ++
  "bnf_mul_params:\n" ++
  "  .quad bnf_le_a, bnf_le_b, bnf_le_zero, bnf_le_p, bnf_le_d\n" ++
  "bnf_add_params:\n" ++
  "  .quad bnf_le_a, bnf_le_one, bnf_le_b, bnf_le_p, bnf_le_d\n"

/-- Standalone `.data` section for focused probes. -/
def bn254FieldDataSection : String :=
  ".section .data\n" ++ bn254FieldDataFragment

/-- Convert a 32-byte big-endian buffer (`a0`, byte-addressed, any
    alignment) into four little-endian u64 limbs (`a1`, 8-aligned),
    least-significant limb first. Leaf helper; clobbers only `t` regs. -/
def bnfBeToLe_prog : Program :=
  [ .LI .x5 (0 : Word),
    .LI .x6 (24 : Word),
    .SLLI .x7 .x5 (3 : BitVec 6),
    .SUB .x6 .x6 .x7,
    .ADD .x6 .x10 .x6,
    .LI .x28 (0 : Word),
    .LI .x29 (8 : Word),
    .SLLI .x28 .x28 (8 : BitVec 6),
    .LBU .x30 .x6 (0 : BitVec 12),
    .OR .x28 .x28 .x30,
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .BNE .x29 .x0 (-20 : BitVec 13),
    .SLLI .x7 .x5 (3 : BitVec 6),
    .ADD .x7 .x11 .x7,
    .SD .x7 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .LI .x6 (4 : Word),
    .BNE .x5 .x6 (-68 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bn254FieldBeToLeFunction : String :=
  "bnf_be_to_le:\n" ++ emitProgram bnfBeToLe_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bnfBeToLe_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254FieldBeToLeFunction_eq_prog :
    bn254FieldBeToLeFunction = "bnf_be_to_le:\n" ++ emitProgram bnfBeToLe_prog := rfl

#guard bn254FieldBeToLeFunction.startsWith "bnf_be_to_le:\n"
#guard bnfBeToLe_prog.length = 20
/-- Convert four little-endian u64 limbs (`a0`, 8-aligned) into a 32-byte
    big-endian buffer (`a1`, byte-addressed, any alignment). Inverse of
    `bnf_be_to_le`. Leaf helper; clobbers only `t` regs. -/
def bnfLeToBe_prog : Program :=
  [ .LI .x5 (0 : Word),
    .SLLI .x6 .x5 (3 : BitVec 6),
    .ADD .x7 .x10 .x6,
    .LD .x28 .x7 (0 : BitVec 12),
    .LI .x6 (31 : Word),
    .SLLI .x7 .x5 (3 : BitVec 6),
    .SUB .x6 .x6 .x7,
    .ADD .x6 .x11 .x6,
    .LI .x29 (8 : Word),
    .ANDI .x30 .x28 (255 : BitVec 12),
    .SB .x6 .x30 (0 : BitVec 12),
    .SRLI .x28 .x28 (8 : BitVec 6),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .BNE .x29 .x0 (-20 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .LI .x6 (4 : Word),
    .BNE .x5 .x6 (-64 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bn254FieldLeToBeFunction : String :=
  "bnf_le_to_be:\n" ++ emitProgram bnfLeToBe_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bnfLeToBe_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254FieldLeToBeFunction_eq_prog :
    bn254FieldLeToBeFunction = "bnf_le_to_be:\n" ++ emitProgram bnfLeToBe_prog := rfl

#guard bn254FieldLeToBeFunction.startsWith "bnf_le_to_be:\n"
#guard bnfLeToBe_prog.length = 19
/-! ## bnf_is_zero32 — verified drop-in (two-exit scan via single-exit whileBreak)

    The emitted `bnfIsZero32_prog` is a two-exit byte scan (top `BEQ x5,x0`
    completion guard + mid `BNE x7,x0` break-on-nonzero), where the two exits
    jump to *different* result blocks (`LI x10,1` / `LI x10,0`). Plain
    `Stmt.whileBreak` flattens both its guard-fail and its break to a single
    `Lend`, so it cannot byte-match a two-distinct-target routine.

    Per the drop-in policy, we model it as a **single-exit `whileBreak`** whose
    body scans 32 bytes (break on first nonzero), followed by a post-loop block
    that derives the result from the **counter** `x5` (`x5 = 0` ⟺ all 32 bytes
    scanned without breaking ⟺ all-zero). The re-emitted `_prog` is this
    verified body's flatten (same 12-instruction length as the original, so no
    downstream offset shift). The EEST A/B run is the drop-in gate that
    replaces byte-identity (guest bytes move, but semantics are preserved). -/


/-- Loop invariant at header evaluation `i`: counter `x5 = 32-i`, cursor
    `x6 = ptr+i`, the first `i` bytes are all zero (`i ≤ nlz bs 32`). -/
def bnfIsZeroScanInv (ptr : Word) (bs : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf _ _ =>
    rf.get .x5 = BitVec.ofNat 64 (32 - i) ∧
    rf.get .x6 = ptr + BitVec.ofNat 64 i ∧
    i ≤ nlz bs 32 ∧ 32 ≤ bs.length ∧ ptr.toNat + 32 < 2 ^ 64

/-- `whileBreak` post (at the single `Lend`): the scan stopped at index `nlz`;
    `x5 = 32 - nlz` (so `x5 = 0` ⟺ `nlz = 32` ⟺ all bytes zero). -/
def bnfIsZeroScanPost (ptr : Word) (bs : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ =>
    rf.get .x5 = BitVec.ofNat 64 (32 - nlz bs 32) ∧
    rf.get .x6 = ptr + BitVec.ofNat 64 (nlz bs 32) ∧
    32 ≤ bs.length ∧ ptr.toNat + 32 < 2 ^ 64

/-- `bnf_is_zero32` body: init counter/cursor, scan-and-break, then derive the
    result from the counter (`LI x10,1`; clear to 0 if `x5≠0`). -/
def bnfIsZero32Body (ptr : Word) (bs : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (32 : Word), .MV .x6 .x10] ;;;
  .«whileBreak» "scan" (.bne .x5 .x0) 32
    (bnfIsZeroScanInv ptr bs) (bnfIsZeroScanPost ptr bs)
    (.block "load" [.LBU .x7 .x6 (0 : BitVec 12)]) (.bne .x7 .x0)
    (.block "next" [.ADDI .x6 .x6 (1 : BitVec 12), .ADDI .x5 .x5 (-1 : BitVec 12)]) ;;;
  .block "res1" [.LI .x10 (1 : Word)] ;;;
  .when "clr" (.bne .x5 .x0) (.block "clr0" [.LI .x10 (0 : Word)])

/-- `mset_memcpy`-style verified `Fn`: `x10 := if (the 32 bytes at `a0` are all
    zero) then 1 else 0`. Single read-only region ⟨ptr, bs⟩; no writes. -/
def bnfIsZero32Fn (ptr : Word) (bs : List (BitVec 8)) : Fn where
  name := "bnfIsZero32"
  region := ⟨ptr, bs⟩
  pre := fun rf _ _ => rf.get .x10 = ptr ∧ bs.length = 32 ∧ ptr.toNat + 32 < 2 ^ 64
  post := fun rf _ _ =>
    (rf.get .x10 = if nlz bs 32 = 32 then (1 : Word) else (0 : Word)) ∧
    32 ≤ bs.length ∧ ptr.toNat + 32 < 2 ^ 64
  body := bnfIsZero32Body ptr bs

/-- Return a0 = 1 iff the 32-byte buffer at a0 is all-zero. Leaf helper.

    Re-emitted drop-in: the verified `bnfIsZero32Body` flatten + `ret` (12
    instrs, same length as the pre-drop-in hand-written routine). -/
def bnfIsZero32_prog : Program :=
  (bnfIsZero32Body 0 []).flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]

def bn254FieldIsZeroFunction : String :=
  "bnf_is_zero32:\n" ++ emitProgram bnfIsZero32_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bnfIsZero32_prog` (the re-emitted drop-in) rendered under its label. -/
theorem bn254FieldIsZeroFunction_eq_prog :
    bn254FieldIsZeroFunction = "bnf_is_zero32:\n" ++ emitProgram bnfIsZero32_prog := rfl

#guard bn254FieldIsZeroFunction.startsWith "bnf_is_zero32:\n"
#guard bnfIsZero32_prog.length = 12
-- The drop-in is position-independent (no PC-relative instruction).
#guard (bnfIsZero32Body 0 []).flatten 0 = (bnfIsZero32Body 0 []).flatten 0x80000000

theorem bnfIsZero32Fn_spec (ptr : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk ptr bs).wf) (base : Word) :
    (bnfIsZero32Fn ptr bs).Spec base := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hse1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hsem1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case bnfIsZero32.scan.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, hws₀, ⟨hx10, hlen, hpl⟩, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
    refine ⟨?_, ?_, Nat.zero_le _, (by omega : 32 ≤ bs.length), hpl⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide)]
      decide
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hx10]
      simp
  case bnfIsZero32.scan.inv_step =>
    rintro i hi rf' ws' A' hsp
    obtain ⟨rfa, wsa, hwsa, ⟨hspbb, hnbreak⟩, hrf', -⟩ := hsp
    obtain ⟨rfb, wsb, hwsb, ⟨hinv, hg⟩, hrfa, -⟩ := hspbb
    obtain ⟨hx5, hx6, hle, hlen, hpl⟩ := hinv
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    have hilt : i < 32 := by
      rcases Nat.lt_or_ge i 32 with h | h
      · exact h
      · exfalso; apply hg
        show rfb.get .x5 = rfb.get .x0
        rw [hx5, show 32 - i = 0 from by omega]; rfl
    have hbyte : (bnfIsZero32Fn ptr bs).region.byteAt (rfb.get .x6 + signExtend12 0)
        = bs.getD i 0 := by
      unfold Region.byteAt
      rw [show (bnfIsZero32Fn ptr bs).region.bytes = bs from rfl,
          show (bnfIsZero32Fn ptr bs).region.base = ptr from rfl, hx6, hse0]
      congr 1
      have hti : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    have hrfa6 : rfa.get .x6 = rfb.get .x6 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7)]
    have hrfa5 : rfa.get .x5 = rfb.get .x5 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7)]
    have hrfa7 : rfa.get .x7 = BitVec.zeroExtend 64 (bs.getD i 0) := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x7 : Reg) ≠ .x0)]
      rw [hbyte]
    -- ¬ breakCond ⇒ byte is zero
    have hz : bs.getD i 0 = 0 := by
      have hne : rfa.get .x7 = rfa.get .x0 := by
        by_contra h; exact hnbreak h
      rw [hrfa7, show rfa.get .x0 = 0 from rfl] at hne
      bv_omega
    refine ⟨?_, ?_, nlz_continue bs 32 i hilt hlen hz hle, hlen, hpl⟩
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x5 : Reg) ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6)]
      rw [hrfa5, hx5, hsem1]
      have h1 : (BitVec.ofNat 64 (32 - i)).toNat = 32 - i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (32 - (i + 1))).toNat = 32 - (i + 1) := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5),
        RegFile.get_set_self _ _ _ (by decide : (Reg.x6 : Reg) ≠ .x0)]
      rw [hrfa6, hx6, hse1]
      have h1 : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
  case bnfIsZero32.scan.exhausted =>
    rintro rf ws A ⟨hx5, -, -, -, -⟩
    intro hc
    apply hc
    rw [hx5, show 32 - 32 = 0 from by omega]; rfl
  case bnfIsZero32.scan.guard_exit =>
    rintro i hile rf ws A ⟨hx5, hx6, hle, hlen, hpl⟩ hng
    have hil : i = 32 := by
      by_contra hne
      apply hng
      show rf.get .x5 ≠ rf.get .x0
      rw [hx5, show rf.get .x0 = 0 from rfl]
      intro h
      have := congrArg (fun w : Word => w.toNat) h
      simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this
      omega
    have hnlz : nlz bs 32 = 32 := by
      have := nlz_le bs 32; omega
    refine ⟨?_, ?_, hlen, hpl⟩
    · rw [hx5, hnlz, hil]
    · rw [hx6, hnlz, hil]
  case bnfIsZero32.scan.break =>
    rintro i hi rf' ws' A' hsp hbreak
    obtain ⟨rfb, wsb, hwsb, ⟨hinv, hg⟩, hrf', -⟩ := hsp
    obtain ⟨hx5, hx6, hle, hlen, hpl⟩ := hinv
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    have hbyte : (bnfIsZero32Fn ptr bs).region.byteAt (rfb.get .x6 + signExtend12 0)
        = bs.getD i 0 := by
      unfold Region.byteAt
      rw [show (bnfIsZero32Fn ptr bs).region.bytes = bs from rfl,
          show (bnfIsZero32Fn ptr bs).region.base = ptr from rfl, hx6, hse0]
      congr 1
      have hti : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    have hrf7 : rf'.get .x7 = BitVec.zeroExtend 64 (bs.getD i 0) := by
      rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x7 : Reg) ≠ .x0)]
      rw [hbyte]
    have hrf5 : rf'.get .x5 = rfb.get .x5 := by
      rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7)]
    have hrf6 : rf'.get .x6 = rfb.get .x6 := by
      rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7)]
    have hnz : bs.getD i 0 ≠ 0 := by
      have hne : rf'.get .x7 ≠ rf'.get .x0 := hbreak
      rw [hrf7, show rf'.get .x0 = 0 from rfl] at hne
      intro hz
      exact hne (by rw [hz]; rfl)
    have hieq : i = nlz bs 32 := nlz_break bs 32 i hle hnz
    refine ⟨?_, ?_, hlen, hpl⟩
    · rw [hrf5, hx5, hieq]
    · rw [hrf6, hx6, hieq]
  case bnfIsZero32.scan.before.load.mem =>
    rintro rf ws A hws ⟨i, hi, ⟨hx5, hx6, hle, hlen, hpl⟩, hg⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    have hilt : i < 32 := by
      rcases Nat.lt_or_ge i 32 with h | h
      · exact h
      · exfalso; apply hg
        rw [hx5, show 32 - i = 0 from by omega]; rfl
    simp only [blockVCs, loadSem]
    refine ⟨⟨one_dvd _, ?_⟩, trivial⟩
    show ((rf.get .x6 + signExtend12 (0 : BitVec 12)) - ptr).toNat + 1 ≤ bs.length
    rw [hse0, hx6]
    have hti : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
    have haddr : ((ptr + BitVec.ofNat 64 i + 0) - ptr).toNat = i := by bv_omega
    rw [haddr]; omega
  case bnfIsZero32.post =>
    rintro rf ws A hpost
    -- sp(body) = sp(when clr)(sp(res1)(sp(whileBreak)(sp(init)(pre)))).
    -- sp(whileBreak) = scanPost (definitionally); split the `when`.
    rcases hpost with
      ⟨rf₁, ws₁, hws₁, ⟨hres1, hcond⟩, hrf1, rfl⟩ | ⟨hres1, hnc⟩
    · -- x5 ≠ 0 branch (`clr0` ran): x10 = 0; nlz ≠ 32.
      obtain rfl := List.eq_nil_of_length_eq_zero hws₁
      obtain ⟨rfa, wsa, hwsa, hscanPost, hrf1eq, -⟩ := hres1
      obtain rfl := List.eq_nil_of_length_eq_zero hwsa
      obtain ⟨hx5a, -, hle, hpl⟩ := hscanPost
      have hx10rf : rf.get .x10 = (0 : Word) := by
        rw [hrf1]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_self _ _ _ (by decide : (Reg.x10 : Reg) ≠ .x0)]
      have hr1x5 : rf₁.get .x5 = rfa.get .x5 := by
        rw [hrf1eq]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x10)]
      have hne : nlz bs 32 ≠ 32 := by
        dsimp only [Cond.holds] at hcond
        intro heq
        apply hcond
        rw [hr1x5, hx5a, heq]; rfl
      refine ⟨?_, hle, hpl⟩
      rw [hx10rf]
      by_cases h : nlz bs 32 = 32
      · rw [if_pos h]; exact False.elim (hne h)
      · rw [if_neg h]
    · -- x5 = 0 branch (skip `clr0`): x10 = 1; nlz = 32.
      obtain ⟨rfa, wsa, hwsa, hscanPost, hrfeq, -⟩ := hres1
      obtain rfl := List.eq_nil_of_length_eq_zero hwsa
      obtain ⟨hx5a, -, hle, hpl⟩ := hscanPost
      have hx10rf : rf.get .x10 = (1 : Word) := by
        rw [hrfeq]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_self _ _ _ (by decide : (Reg.x10 : Reg) ≠ .x0)]
      have hrfx5 : rf.get .x5 = rfa.get .x5 := by
        rw [hrfeq]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x10)]
      dsimp only [Cond.holds] at hnc
      have heq : nlz bs 32 = 32 := by
        have hrfeq5 : rf.get .x5 = BitVec.ofNat 64 (32 - nlz bs 32) := by
          rw [hrfx5, hx5a]
        have h0 : rf.get .x5 = (0 : Word) := by
          by_contra hne
          exact hnc hne
        rw [hrfeq5] at h0
        have hT : (BitVec.ofNat 64 (32 - nlz bs 32)).toNat = (32 - nlz bs 32) % 2 ^ 64 :=
          BitVec.toNat_ofNat ..
        have hz : (0 : Word).toNat = 0 := rfl
        have hmod : (32 - nlz bs 32) % 2 ^ 64 = 0 := by
          have := congrArg BitVec.toNat h0
          rw [hT, hz] at this
          exact this
        have hle : nlz bs 32 ≤ 32 := nlz_le bs 32
        omega
      refine ⟨?_, hle, hpl⟩
      rw [hx10rf, if_pos heq]
/-! ## bnf_eq32 — verified drop-in (two-exit byte comparison via single-exit whileBreak)

    The emitted `bnfEq32_prog` is a two-exit byte comparison (top `BEQ x5,x0`
    completion + mid `BNE x28,x29` break-on-mismatch), where the two exits
    jump to *different* result blocks (`LI x10,1` / `LI x10,0`).

    Per the drop-in policy (same technique as `bnfIsZero32`), the scaffold
    below models it as a **single-exit `whileBreak`** whose body scans 32
    bytes (break on first mismatch), followed by a post-loop block that derives
    the result from the **counter** `x5` (`x5 = 0` ⟺ all 32 bytes matched ⟺
    buffers equal).

    This PR re-emits `bnfEq32_prog` from the verified body; the drop-in gate is
    the `bnfEq32Fn_spec` proof plus EEST A/B parity. -/


/-- Loop invariant at header evaluation `i`: counter `x5 = 32-i`, cursors
    `x6 = ptr1+i`, `x7 = ptr2+i`, and the first `i` bytes are pairwise
    equal (`∀ j < i, bs1.getD j 0 = bs2.getD j 0`). -/
def bnfEqScanInv (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf _ A =>
    rf.get .x5 = BitVec.ofNat 64 (32 - i) ∧
    rf.get .x6 = ptr1 + BitVec.ofNat 64 i ∧
    rf.get .x7 = ptr2 + BitVec.ofNat 64 i ∧
    rf.get .x11 = ptr2 ∧
    (∀ j, j < i → bs1.getD j 0 = bs2.getD j 0) ∧
    bs1.length = 32 ∧ bs2.length = 32 ∧
    ptr1.toNat + 32 < 2 ^ 64 ∧ ptr2.toNat + 32 < 2 ^ 64 ∧
    (ptr1.toNat + 32 ≤ ptr2.toNat ∨ ptr2.toNat + 32 ≤ ptr1.toNat) ∧
    A = bytesRegion ptr2 bs2

/-- Number of consecutive matching bytes from the front of `bs1`/`bs2`
    (up to `n`).  Returns `n` if all match, else the first mismatch index. -/
def firstDiff (bs1 bs2 : List (BitVec 8)) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      if firstDiff bs1 bs2 n < n then firstDiff bs1 bs2 n
      else if bs1.getD n 0 ≠ bs2.getD n 0 then n
      else n + 1

@[simp] theorem firstDiff_zero (bs1 bs2 : List (BitVec 8)) :
    firstDiff bs1 bs2 0 = 0 := rfl

@[simp] theorem firstDiff_succ (bs1 bs2 : List (BitVec 8)) (n : Nat) :
    firstDiff bs1 bs2 (n + 1) =
      (if firstDiff bs1 bs2 n < n then firstDiff bs1 bs2 n
       else if bs1.getD n 0 ≠ bs2.getD n 0 then n else n + 1) := by
  conv_lhs => rw [firstDiff]

theorem firstDiff_le (bs1 bs2 : List (BitVec 8)) : ∀ n, firstDiff bs1 bs2 n ≤ n
  | 0 => Nat.zero_le _
  | n + 1 => by
    rw [firstDiff_succ]
    by_cases h : firstDiff bs1 bs2 n < n
    · rw [if_pos h]; exact Nat.le_succ_of_le (firstDiff_le bs1 bs2 n)
    · rw [if_neg h]; split <;> omega

theorem firstDiff_all_eq (bs1 bs2 : List (BitVec 8)) (n : Nat)
    (h : ∀ j, j < n → bs1.getD j 0 = bs2.getD j 0) :
    firstDiff bs1 bs2 n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [firstDiff_succ, ih (fun j hj => h j (by omega)), if_neg (Nat.lt_irrefl _)]
    by_cases hne : bs1.getD n 0 ≠ bs2.getD n 0
    · exact absurd hne (fun h2 => h2 (h n (by omega)))
    · rw [if_neg hne]

theorem firstDiff_ne (bs1 bs2 : List (BitVec 8)) (i : Nat)
    (hprev : ∀ j, j < i → bs1.getD j 0 = bs2.getD j 0)
    (hne : bs1.getD i 0 ≠ bs2.getD i 0) :
    firstDiff bs1 bs2 (i + 1) = i := by
  rw [firstDiff_succ, firstDiff_all_eq _ _ _ hprev, if_neg (Nat.lt_irrefl _), if_pos hne]

theorem firstDiff_ne_of_lt (bs1 bs2 : List (BitVec 8)) (i n : Nat)
    (hi : i < n)
    (hprev : ∀ j, j < i → bs1.getD j 0 = bs2.getD j 0)
    (hne : bs1.getD i 0 ≠ bs2.getD i 0) :
    firstDiff bs1 bs2 n = i := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hlt : i < n
    · have hih := ih hlt
      rw [firstDiff_succ, hih, if_pos hlt]
    · have hin : i = n := by omega
      subst i
      exact firstDiff_ne bs1 bs2 n hprev hne

/-- `whileBreak` post (at the single `Lend`): the scan stopped at index
    `firstDiff`; `x5 = 32 - firstDiff` (so `x5 = 0` ⟺ all 32 bytes matched). -/
def bnfEqScanPost (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf _ A =>
    rf.get .x5 = BitVec.ofNat 64 (32 - firstDiff bs1 bs2 32) ∧
    rf.get .x6 = ptr1 + BitVec.ofNat 64 (firstDiff bs1 bs2 32) ∧
    rf.get .x7 = ptr2 + BitVec.ofNat 64 (firstDiff bs1 bs2 32) ∧
    rf.get .x11 = ptr2 ∧
    bs1.length = 32 ∧ bs2.length = 32 ∧
    ptr1.toNat + 32 < 2 ^ 64 ∧ ptr2.toNat + 32 < 2 ^ 64 ∧
    (ptr1.toNat + 32 ≤ ptr2.toNat ∨ ptr2.toNat + 32 ≤ ptr1.toNat) ∧
    A = bytesRegion ptr2 bs2

/-- Focus relation for the second read-only input: `x11` remains the stable
    base pointer for `bs2`, while the loop body may load through cursor `x7`. -/
def bnfEqReadA1 (ptr2 : Word) (bs2 : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ rob rest => rf.get .x11 = ptr2 ∧ rob = bs2 ∧ rest = empAssertion

/-- `bnf_eq32` body: init counter/cursors, scan-and-break, then derive
    the result from the counter (`LI x10,1`; clear to 0 if `x5≠0`). -/
def bnfEq32Body (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (32 : Word), .MV .x6 .x10, .MV .x7 .x11] ;;;
  .«whileBreak» "scan" (.bne .x5 .x0) 32
    (bnfEqScanInv ptr1 ptr2 bs1 bs2) (bnfEqScanPost ptr1 ptr2 bs1 bs2)
    (.block "load1" [.LBU .x28 .x6 (0 : BitVec 12)] ;;;
     .readAt "load2" .x11 (bnfEqReadA1 ptr2 bs2) [.LBU .x29 .x7 (0 : BitVec 12)])
    (.bne .x28 .x29)
    (.block "next" [.ADDI .x6 .x6 (1 : BitVec 12), .ADDI .x7 .x7 (1 : BitVec 12),
                    .ADDI .x5 .x5 (-1 : BitVec 12)]) ;;;
  .block "res1" [.LI .x10 (1 : Word)] ;;;
  .when "clr" (.bne .x5 .x0) (.block "clr0" [.LI .x10 (0 : Word)])

/-- Verified `Fn`: `x10 := if (the 32 bytes at `a0` equal the 32 bytes at
    `a1`) then 1 else 0`. -/
def bnfEq32Fn (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) : Fn where
  name := "bnfEq32"
  region := ⟨ptr1, bs1⟩
  pre := fun rf _ A =>
    rf.get .x10 = ptr1 ∧ rf.get .x11 = ptr2 ∧
    bs1.length = 32 ∧ bs2.length = 32 ∧
    ptr1.toNat + 32 < 2 ^ 64 ∧ ptr2.toNat + 32 < 2 ^ 64 ∧
    (ptr1.toNat + 32 ≤ ptr2.toNat ∨ ptr2.toNat + 32 ≤ ptr1.toNat) ∧
    A = bytesRegion ptr2 bs2
  post := fun rf _ A =>
    (rf.get .x10 = if firstDiff bs1 bs2 32 = 32 then (1 : Word) else (0 : Word)) ∧
    bs1.length = 32 ∧ bs2.length = 32 ∧
    ptr1.toNat + 32 < 2 ^ 64 ∧ ptr2.toNat + 32 < 2 ^ 64 ∧
    A = bytesRegion ptr2 bs2
  body := bnfEq32Body ptr1 ptr2 bs1 bs2

/-- Re-emitted drop-in: the verified `bnfEq32Body` flatten + `ret`. -/
def bnfEq32_prog : Program :=
  (bnfEq32Body 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]

def bn254FieldEq32Function : String :=
  "bnf_eq32:\n" ++ emitProgram bnfEq32_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bnfEq32_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254FieldEq32Function_eq_prog :
    bn254FieldEq32Function = "bnf_eq32:\n" ++ emitProgram bnfEq32_prog := rfl

#guard bn254FieldEq32Function.startsWith "bnf_eq32:\n"
#guard bnfEq32_prog.length = 15
-- The drop-in is position-independent (no PC-relative instruction).
#guard (bnfEq32Body 0 0 [] []).flatten 0 = (bnfEq32Body 0 0 [] []).flatten 0x80000000

theorem bnfEq32Fn_spec (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8))
    (hwf1 : (Region.mk ptr1 bs1).wf) (hwf2 : (Region.mk ptr2 bs2).wf) (base : Word) :
    (bnfEq32Fn ptr1 ptr2 bs1 bs2).Spec base := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hse1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hsem1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  vcgen
  case region => exact ⟨hwf1, RwRegion.empty_wf⟩
  case bnfEq32.scan.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, hws₀, ⟨hx10, hx11, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide)]
      decide
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hx10]
      simp
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]
      simp
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5)]
      exact hx11
    · intro j hj; omega
  case bnfEq32.scan.exhausted =>
    rintro rf ws A ⟨hx5, -, -, -, -, -, -, -, -, -, -⟩
    intro hc
    apply hc
    rw [hx5, show 32 - 32 = 0 from by omega]; rfl
  case bnfEq32.scan.guard_exit =>
    rintro i hile rf ws A ⟨hx5, hx6, hx7, hx11, hpref, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩ hng
    have hil : i = 32 := by
      by_contra hne
      apply hng
      show rf.get .x5 ≠ rf.get .x0
      rw [hx5, show rf.get .x0 = 0 from rfl]
      intro h
      have := congrArg (fun w : Word => w.toNat) h
      simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this
      omega
    have hfd : firstDiff bs1 bs2 32 = 32 := by
      apply firstDiff_all_eq
      intro j hj
      exact hpref j (by omega)
    refine ⟨?_, ?_, ?_, ?_, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩
    · rw [hx5, hfd, hil]
    · rw [hx6, hfd, hil]
    · rw [hx7, hfd, hil]
    · exact hx11

  case bnfEq32.scan.before.load1.mem =>
    rintro rf ws A hws ⟨i, hi, ⟨hx5, hx6, hx7, hx11, hpref, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩, hg⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    have hilt : i < 32 := by
      rcases Nat.lt_or_ge i 32 with h | h
      · exact h
      · exfalso; apply hg
        rw [hx5, show 32 - i = 0 from by omega]; rfl
    simp only [blockVCs, loadSem]
    refine ⟨⟨one_dvd _, ?_⟩, trivial⟩
    show ((rf.get .x6 + signExtend12 (0 : BitVec 12)) - ptr1).toNat + 1 ≤ bs1.length
    rw [hse0, hx6]
    have haddr : ((ptr1 + BitVec.ofNat 64 i + 0) - ptr1).toNat = i := by bv_omega
    rw [haddr]; omega
  case bnfEq32.scan.before.load2.focus =>
    rintro rf ws A hreach hApc hp hhp
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv, hg⟩, hrf, hws⟩ := hreach
    obtain ⟨hx5, hx6, hx7, hx11, hpref, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩ := hinv
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    have hx11' : rf.get .x11 = ptr2 := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem, inRw]
      exact hx11
    refine ⟨bs2, empAssertion, ⟨hx11', rfl, rfl⟩, ?_, pcFree_emp, ?_⟩
    · rw [hx11', sepConj_emp_right']
      rw [hA] at hhp
      exact hhp
    · rw [hx11']
      exact hwf2

  case bnfEq32.scan.before.load2.mem =>
    rintro rf ws A robytes rest hws hreach hro hsat
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv, hg⟩, hrf, hwsrf⟩ := hreach
    obtain ⟨hx5, hx6, hx7, hx11, hpref, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩ := hinv
    obtain ⟨hptr, hrob, hrest⟩ := hro
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    have hx7' : rf.get .x7 = ptr2 + BitVec.ofNat 64 i := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem, inRw]
      exact hx7
    have hx11' : rf.get .x11 = ptr2 := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem, inRw]
      exact hx11
    simp only [blockVCs, loadSem]
    refine ⟨⟨one_dvd _, ?_⟩, trivial⟩
    show ((rf.get .x7 + signExtend12 (0 : BitVec 12)) - rf.get .x11).toNat + 1 ≤ robytes.length
    rw [hse0, hx7', hx11', hrob]
    have haddr : ((ptr2 + BitVec.ofNat 64 i + 0) - ptr2).toNat = i := by bv_omega
    rw [haddr]; omega

  case bnfEq32.scan.inv_step =>
    rintro i hi rf' ws' A' hsp
    obtain ⟨rfa, wsa, hwsa, ⟨hload, hnbreak⟩, hrf', hws'⟩ := hsp
    obtain ⟨rf1, ws1, A1, robytes, rest, hlenRead, hsp1, hsat, hro, hrfa, hwsaEq, hAeq⟩ := hload
    obtain ⟨rfb, wsb, hwsb, ⟨hinv, hg⟩, hrf1, hws1⟩ := hsp1
    obtain ⟨hx5, hx6, hx7, hx11, hpref, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩ := hinv
    obtain ⟨hptr, hrob, hrest⟩ := hro
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    have hws1len0 : ws1.length = 0 := by simpa [bnfEq32Fn, RwRegion.empty] using hlenRead
    obtain rfl := List.eq_nil_of_length_eq_zero hws1len0
    have hbyte1 : (bnfEq32Fn ptr1 ptr2 bs1 bs2).region.byteAt (rfb.get .x6 + signExtend12 0)
        = bs1.getD i 0 := by
      unfold Region.byteAt
      rw [show (bnfEq32Fn ptr1 ptr2 bs1 bs2).region.bytes = bs1 from rfl,
          show (bnfEq32Fn ptr1 ptr2 bs1 bs2).region.base = ptr1 from rfl, hx6, hse0]
      congr 1
      bv_omega
    have hrf1x5 : rf1.get .x5 = rfb.get .x5 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x28)]
    have hrf1x6 : rf1.get .x6 = rfb.get .x6 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28)]
    have hrf1x7 : rf1.get .x7 = rfb.get .x7 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28)]
    have hrf1x11 : rf1.get .x11 = rfb.get .x11 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x28)]
    have hrf1x28 : rf1.get .x28 = BitVec.zeroExtend 64 (bs1.getD i 0) := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x28 : Reg) ≠ .x0)]
      rw [hbyte1]
    have hbyte2 : ({ base := rf1.get .x11, bytes := robytes } : Region).byteAt
        (rf1.get .x7 + signExtend12 0) = bs2.getD i 0 := by
      unfold Region.byteAt
      rw [hrob, hrf1x7, hrf1x11, hx7, hx11, hse0]
      congr 1
      bv_omega
    have hrfa5 : rfa.get .x5 = rfb.get .x5 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x29)]
      exact hrf1x5
    have hrfa6 : rfa.get .x6 = rfb.get .x6 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29)]
      exact hrf1x6
    have hrfa7 : rfa.get .x7 = rfb.get .x7 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x29)]
      exact hrf1x7
    have hrfa11 : rfa.get .x11 = rfb.get .x11 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x29)]
      exact hrf1x11
    have hrfa28 : rfa.get .x28 = BitVec.zeroExtend 64 (bs1.getD i 0) := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x29)]
      exact hrf1x28
    have hrfa29 : rfa.get .x29 = BitVec.zeroExtend 64 (bs2.getD i 0) := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x29 : Reg) ≠ .x0)]
      rw [hbyte2]
    have heqByte : bs1.getD i 0 = bs2.getD i 0 := by
      have hne : rfa.get .x28 = rfa.get .x29 := by
        by_contra h; exact hnbreak h
      rw [hrfa28, hrfa29] at hne
      bv_omega
    refine ⟨?_, ?_, ?_, ?_, ?_, hlen1, hlen2, hpl1, hpl2, hdisj, ?_⟩
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x5 : Reg) ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6)]
      rw [hrfa5, hx5, hsem1]
      bv_omega
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
        RegFile.get_set_self _ _ _ (by decide : (Reg.x6 : Reg) ≠ .x0)]
      rw [hrfa6, hx6, hse1]
      bv_omega
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x5),
        RegFile.get_set_self _ _ _ (by decide : (Reg.x7 : Reg) ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x6)]
      rw [hrfa7, hx7, hse1]
      bv_omega
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6)]
      rw [hrfa11, hx11]
    · intro j hj
      by_cases hji : j < i
      · exact hpref j hji
      · have hji' : j = i := by omega
        rw [hji']; exact heqByte
    · rw [hAeq, hptr, hrob, hrest, sepConj_emp_right']
  case bnfEq32.scan.break =>
    rintro i hi rf' ws' A' hload hbreak
    obtain ⟨rf1, ws1, A1, robytes, rest, hlenRead, hsp1, hsat, hro, hrfLoad, hwsaEq, hAeq⟩ := hload
    obtain ⟨rfb, wsb, hwsb, ⟨hinv, hg⟩, hrf1, hws1⟩ := hsp1
    obtain ⟨hx5, hx6, hx7, hx11, hpref, hlen1, hlen2, hpl1, hpl2, hdisj, hA⟩ := hinv
    obtain ⟨hptr, hrob, hrest⟩ := hro
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    have hws1len0 : ws1.length = 0 := by simpa [bnfEq32Fn, RwRegion.empty] using hlenRead
    obtain rfl := List.eq_nil_of_length_eq_zero hws1len0
    have hbyte1 : (bnfEq32Fn ptr1 ptr2 bs1 bs2).region.byteAt (rfb.get .x6 + signExtend12 0)
        = bs1.getD i 0 := by
      unfold Region.byteAt
      rw [show (bnfEq32Fn ptr1 ptr2 bs1 bs2).region.bytes = bs1 from rfl,
          show (bnfEq32Fn ptr1 ptr2 bs1 bs2).region.base = ptr1 from rfl, hx6, hse0]
      congr 1
      bv_omega
    have hrf1x5 : rf1.get .x5 = rfb.get .x5 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x28)]
    have hrf1x6 : rf1.get .x6 = rfb.get .x6 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28)]
    have hrf1x7 : rf1.get .x7 = rfb.get .x7 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28)]
    have hrf1x11 : rf1.get .x11 = rfb.get .x11 := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x28)]
    have hrf1x28 : rf1.get .x28 = BitVec.zeroExtend 64 (bs1.getD i 0) := by
      rw [hrf1]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x28 : Reg) ≠ .x0)]
      rw [hbyte1]
    have hbyte2 : ({ base := rf1.get .x11, bytes := robytes } : Region).byteAt
        (rf1.get .x7 + signExtend12 0) = bs2.getD i 0 := by
      unfold Region.byteAt
      rw [hrob, hrf1x7, hrf1x11, hx7, hx11, hse0]
      congr 1
      bv_omega
    have hrfa5 : rf'.get .x5 = rfb.get .x5 := by
      rw [hrfLoad]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x29)]
      exact hrf1x5
    have hrfa6 : rf'.get .x6 = rfb.get .x6 := by
      rw [hrfLoad]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29)]
      exact hrf1x6
    have hrfa7 : rf'.get .x7 = rfb.get .x7 := by
      rw [hrfLoad]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x29)]
      exact hrf1x7
    have hrfa11 : rf'.get .x11 = rfb.get .x11 := by
      rw [hrfLoad]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x29)]
      exact hrf1x11
    have hrfa28 : rf'.get .x28 = BitVec.zeroExtend 64 (bs1.getD i 0) := by
      rw [hrfLoad]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x29)]
      exact hrf1x28
    have hrfa29 : rf'.get .x29 = BitVec.zeroExtend 64 (bs2.getD i 0) := by
      rw [hrfLoad]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x29 : Reg) ≠ .x0)]
      rw [hbyte2]
    have hneByte : bs1.getD i 0 ≠ bs2.getD i 0 := by
      have hne : rf'.get .x28 ≠ rf'.get .x29 := hbreak
      rw [hrfa28, hrfa29] at hne
      intro heq
      exact hne (by rw [heq])
    have hfd : firstDiff bs1 bs2 32 = i := firstDiff_ne_of_lt bs1 bs2 i 32 hi hpref hneByte
    refine ⟨?_, ?_, ?_, ?_, hlen1, hlen2, hpl1, hpl2, hdisj, ?_⟩
    · rw [hrfa5, hx5, hfd]
    · rw [hrfa6, hx6, hfd]
    · rw [hrfa7, hx7, hfd]
    · rw [hrfa11, hx11]
    · rw [hAeq, hptr, hrob, hrest, sepConj_emp_right']
  case bnfEq32.post =>
    rintro rf ws A hpost
    rcases hpost with
      ⟨rf₁, ws₁, hws₁, ⟨hres1, hcond⟩, hrf1, rfl⟩ | ⟨hres1, hnc⟩
    · obtain rfl := List.eq_nil_of_length_eq_zero hws₁
      obtain ⟨rfa, wsa, hwsa, hscanPost, hrf1eq, -⟩ := hres1
      obtain rfl := List.eq_nil_of_length_eq_zero hwsa
      obtain ⟨hx5a, -, -, -, hlen1, hlen2, hpl1, hpl2, -, hA⟩ := hscanPost
      have hx10rf : rf.get .x10 = (0 : Word) := by
        rw [hrf1]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_self _ _ _ (by decide : (Reg.x10 : Reg) ≠ .x0)]
      have hr1x5 : rf₁.get .x5 = rfa.get .x5 := by
        rw [hrf1eq]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x10)]
      have hne : firstDiff bs1 bs2 32 ≠ 32 := by
        dsimp only [Cond.holds] at hcond
        intro heq
        apply hcond
        rw [hr1x5, hx5a, heq]
        rfl
      refine ⟨?_, hlen1, hlen2, hpl1, hpl2, hA⟩
      rw [hx10rf]
      by_cases h : firstDiff bs1 bs2 32 = 32
      · rw [if_pos h]
        exact False.elim (hne h)
      · rw [if_neg h]
    · obtain ⟨rfa, wsa, hwsa, hscanPost, hrfeq, -⟩ := hres1
      obtain rfl := List.eq_nil_of_length_eq_zero hwsa
      obtain ⟨hx5a, -, -, -, hlen1, hlen2, hpl1, hpl2, -, hA⟩ := hscanPost
      have hx10rf : rf.get .x10 = (1 : Word) := by
        rw [hrfeq]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_self _ _ _ (by decide : (Reg.x10 : Reg) ≠ .x0)]
      have hrfx5 : rf.get .x5 = rfa.get .x5 := by
        rw [hrfeq]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x10)]
      dsimp only [Cond.holds] at hnc
      have heq : firstDiff bs1 bs2 32 = 32 := by
        have hrfeq5 : rf.get .x5 = BitVec.ofNat 64 (32 - firstDiff bs1 bs2 32) := by
          rw [hrfx5, hx5a]
        have h0 : rf.get .x5 = (0 : Word) := by
          by_contra hne
          exact hnc hne
        rw [hrfeq5] at h0
        have hT : (BitVec.ofNat 64 (32 - firstDiff bs1 bs2 32)).toNat =
            (32 - firstDiff bs1 bs2 32) % 2 ^ 64 := BitVec.toNat_ofNat ..
        have hz : (0 : Word).toNat = 0 := rfl
        have hmod : (32 - firstDiff bs1 bs2 32) % 2 ^ 64 = 0 := by
          have := congrArg BitVec.toNat h0
          rw [hT, hz] at this
          exact this
        have hle : firstDiff bs1 bs2 32 ≤ 32 := firstDiff_le bs1 bs2 32
        omega
      refine ⟨?_, hlen1, hlen2, hpl1, hpl2, hA⟩
      rw [hx10rf, if_pos heq]

/-- Return a0 = 1 iff the 32-byte big-endian integer at a0 is `< p`
    (the EIP-196 coordinate range check). Leaf helper. -/
def bnfLtP_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.bnf_p_be (GuestAddrs.bnf_lt_p + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bnf_p_be (GuestAddrs.bnf_lt_p + 0)),
    .LI .x6 (32 : Word),
    .MV .x7 .x10,
    .BEQ .x6 .x0 (44 : BitVec 13),
    .LBU .x28 .x7 (0 : BitVec 12),
    .LBU .x29 .x5 (0 : BitVec 12),
    .BLTU .x28 .x29 (24 : BitVec 13),
    .BLTU .x29 .x28 (28 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bnfLtP_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bnfLtP_relocs : RelocTable :=
  [ (0, .la .x5 "bnf_p_be") ]

def bn254FieldLtPFunction : String :=
  "bnf_lt_p:\n" ++ emitProgramR bnfLtP_prog bnfLtP_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bnfLtP_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bn254FieldLtPFunction_eq_prog :
    bn254FieldLtPFunction = "bnf_lt_p:\n" ++ emitProgramR bnfLtP_prog bnfLtP_relocs := rfl

#guard bn254FieldLtPFunction.startsWith "bnf_lt_p:\n"
#guard bnfLtP_prog.length = 17
/-- Multiply two field elements modulo p via the ziskemu `Arith256Mod`
    accelerator: `d = (a*b + 0) mod p`. a0/a1 = 32-byte BE inputs,
    a2 = 32-byte BE output. Always returns a0 = 0. -/
def bnfMulModP_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x11,
    .MV .x9 .x12,
    .AUIPC .x11 (laHi GuestAddrs.bnf_le_a (GuestAddrs.bnf_mul_mod_p + 24)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bnf_le_a (GuestAddrs.bnf_mul_mod_p + 24)),
    .JAL .x1 (jalOff GuestAddrs.bnf_be_to_le (GuestAddrs.bnf_mul_mod_p + 32)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bnf_le_b (GuestAddrs.bnf_mul_mod_p + 40)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bnf_le_b (GuestAddrs.bnf_mul_mod_p + 40)),
    .JAL .x1 (jalOff GuestAddrs.bnf_be_to_le (GuestAddrs.bnf_mul_mod_p + 48)),
    .AUIPC .x5 (laHi GuestAddrs.bnf_mul_params (GuestAddrs.bnf_mul_mod_p + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bnf_mul_params (GuestAddrs.bnf_mul_mod_p + 52)),
    .CSRS (2050 : BitVec 12) .x5,
    .AUIPC .x10 (laHi GuestAddrs.bnf_le_d (GuestAddrs.bnf_mul_mod_p + 64)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bnf_le_d (GuestAddrs.bnf_mul_mod_p + 64)),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.bnf_le_to_be (GuestAddrs.bnf_mul_mod_p + 76)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bnfMulModP_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bnfMulModP_relocs : RelocTable :=
  [ (6, .la .x11 "bnf_le_a"),
    (8, .jal .x1 "bnf_be_to_le"),
    (10, .la .x11 "bnf_le_b"),
    (12, .jal .x1 "bnf_be_to_le"),
    (13, .la .x5 "bnf_mul_params"),
    (16, .la .x10 "bnf_le_d"),
    (19, .jal .x1 "bnf_le_to_be") ]

def bn254FieldMulFunction : String :=
  "bnf_mul_mod_p:\n" ++ emitProgramR bnfMulModP_prog bnfMulModP_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bnfMulModP_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bn254FieldMulFunction_eq_prog :
    bn254FieldMulFunction = "bnf_mul_mod_p:\n" ++ emitProgramR bnfMulModP_prog bnfMulModP_relocs := rfl

#guard bn254FieldMulFunction.startsWith "bnf_mul_mod_p:\n"
#guard bnfMulModP_prog.length = 26
/-- Add two field elements modulo p via the same accelerator with the
    `bnf_add_params` block: `d = (a*1 + b) mod p`. a0/a1 = 32-byte BE
    inputs, a2 = 32-byte BE output. Always returns a0 = 0. -/
def bnfAddModP_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x11,
    .MV .x9 .x12,
    .AUIPC .x11 (laHi GuestAddrs.bnf_le_a (GuestAddrs.bnf_add_mod_p + 24)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bnf_le_a (GuestAddrs.bnf_add_mod_p + 24)),
    .JAL .x1 (jalOff GuestAddrs.bnf_be_to_le (GuestAddrs.bnf_add_mod_p + 32)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bnf_le_b (GuestAddrs.bnf_add_mod_p + 40)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bnf_le_b (GuestAddrs.bnf_add_mod_p + 40)),
    .JAL .x1 (jalOff GuestAddrs.bnf_be_to_le (GuestAddrs.bnf_add_mod_p + 48)),
    .AUIPC .x5 (laHi GuestAddrs.bnf_add_params (GuestAddrs.bnf_add_mod_p + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bnf_add_params (GuestAddrs.bnf_add_mod_p + 52)),
    .CSRS (2050 : BitVec 12) .x5,
    .AUIPC .x10 (laHi GuestAddrs.bnf_le_d (GuestAddrs.bnf_add_mod_p + 64)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bnf_le_d (GuestAddrs.bnf_add_mod_p + 64)),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.bnf_le_to_be (GuestAddrs.bnf_add_mod_p + 76)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bnfAddModP_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bnfAddModP_relocs : RelocTable :=
  [ (6, .la .x11 "bnf_le_a"),
    (8, .jal .x1 "bnf_be_to_le"),
    (10, .la .x11 "bnf_le_b"),
    (12, .jal .x1 "bnf_be_to_le"),
    (13, .la .x5 "bnf_add_params"),
    (16, .la .x10 "bnf_le_d"),
    (19, .jal .x1 "bnf_le_to_be") ]

def bn254FieldAddFunction : String :=
  "bnf_add_mod_p:\n" ++ emitProgramR bnfAddModP_prog bnfAddModP_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bnfAddModP_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bn254FieldAddFunction_eq_prog :
    bn254FieldAddFunction = "bnf_add_mod_p:\n" ++ emitProgramR bnfAddModP_prog bnfAddModP_relocs := rfl

#guard bn254FieldAddFunction.startsWith "bnf_add_mod_p:\n"
#guard bnfAddModP_prog.length = 26
/-- The full BN254 base-field helper suite (self-contained). -/
def bn254FieldCommonFunctions : String :=
  bn254FieldBeToLeFunction ++ "\n" ++
  bn254FieldLeToBeFunction ++ "\n" ++
  bn254FieldIsZeroFunction ++ "\n" ++
  bn254FieldEq32Function ++ "\n" ++
  bn254FieldLtPFunction ++ "\n" ++
  bn254FieldMulFunction ++ "\n" ++
  bn254FieldAddFunction

end EvmAsm.Codegen
