/-
  EvmAsm.Rv64.Basic

  A simplified RV64IM machine model for macro assembly verification.
  64-bit variant of EvmAsm.Basic (which models RV32IM).
-/

namespace EvmAsm.Rv64

-- ============================================================================
-- Registers
-- ============================================================================

/-- The 32 RISC-V integer registers. -/
inductive Reg where
  | x0  -- zero (hardwired zero)
  | x1  -- ra (return address)
  | x2  -- sp (stack pointer)
  | x3  -- gp (global pointer)
  | x4  -- tp (thread pointer)
  | x5  -- t0
  | x6  -- t1
  | x7  -- t2
  | x8  -- s0/fp (frame pointer)
  | x9  -- s1
  | x10 -- a0
  | x11 -- a1
  | x12 -- a2
  | x13 -- a3
  | x14 -- a4
  | x15 -- a5
  | x16 -- a6
  | x17 -- a7
  | x18 -- s2
  | x19 -- s3
  | x20 -- s4
  | x21 -- s5
  | x22 -- s6
  | x23 -- s7
  | x24 -- s8
  | x25 -- s9
  | x26 -- s10
  | x27 -- s11
  | x28 -- t3
  | x29 -- t4
  | x30 -- t5
  | x31 -- t6
  deriving DecidableEq, BEq, Repr, Hashable

instance : LawfulBEq Reg where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

namespace Reg

def toNat : Reg → Nat
  | x0  => 0
  | x1  => 1
  | x2  => 2
  | x3  => 3
  | x4  => 4
  | x5  => 5
  | x6  => 6
  | x7  => 7
  | x8  => 8
  | x9  => 9
  | x10 => 10
  | x11 => 11
  | x12 => 12
  | x13 => 13
  | x14 => 14
  | x15 => 15
  | x16 => 16
  | x17 => 17
  | x18 => 18
  | x19 => 19
  | x20 => 20
  | x21 => 21
  | x22 => 22
  | x23 => 23
  | x24 => 24
  | x25 => 25
  | x26 => 26
  | x27 => 27
  | x28 => 28
  | x29 => 29
  | x30 => 30
  | x31 => 31

instance : ToString Reg where
  toString r := s!"x{r.toNat}"

end Reg

-- ============================================================================
-- Word type (64-bit bitvectors)
-- ============================================================================

/-- We use 64-bit words as our machine word size.
    Defined as `notation` (not `abbrev`) so the elaborator always produces `BitVec 64`
    in Expr output, giving identical Expr.hash regardless of whether `Word` or `BitVec 64`
    was written in source. This is required for the xperm AC reflection fast path. -/
notation "Word" => BitVec 64

-- Note: Addr was previously a separate abbrev but has been unified with Word
-- to avoid Expr.hash mismatches in the xperm tactic (Addr vs Word vs BitVec 64).

-- ============================================================================
-- Instructions (RV64IM)
-- ============================================================================

/-- A single RISC-V 64-bit instruction. -/
inductive Instr where
  -- RV64I ALU register-register
  /-- ADD rd, rs1, rs2 : rd := rs1 + rs2 -/
  | ADD  (rd rs1 rs2 : Reg)
  /-- SUB rd, rs1, rs2 : rd := rs1 - rs2 -/
  | SUB  (rd rs1 rs2 : Reg)
  /-- SLL rd, rs1, rs2 : rd := rs1 << rs2[5:0] (shift left logical) -/
  | SLL  (rd rs1 rs2 : Reg)
  /-- SRL rd, rs1, rs2 : rd := rs1 >>> rs2[5:0] (shift right logical) -/
  | SRL  (rd rs1 rs2 : Reg)
  /-- SRA rd, rs1, rs2 : rd := rs1 >>s rs2[5:0] (shift right arithmetic) -/
  | SRA  (rd rs1 rs2 : Reg)
  /-- AND rd, rs1, rs2 : rd := rs1 &&& rs2 -/
  | AND  (rd rs1 rs2 : Reg)
  /-- OR rd, rs1, rs2 : rd := rs1 ||| rs2 -/
  | OR   (rd rs1 rs2 : Reg)
  /-- XOR rd, rs1, rs2 : rd := rs1 ^^^ rs2 -/
  | XOR  (rd rs1 rs2 : Reg)
  /-- SLT rd, rs1, rs2 : rd := (rs1 <s rs2) ? 1 : 0 (signed) -/
  | SLT  (rd rs1 rs2 : Reg)
  /-- SLTU rd, rs1, rs2 : rd := (rs1 <u rs2) ? 1 : 0 (unsigned) -/
  | SLTU (rd rs1 rs2 : Reg)
  -- RV64I ALU immediate
  /-- ADDI rd, rs1, imm : rd := rs1 + sext(imm) -/
  | ADDI (rd rs1 : Reg) (imm : BitVec 12)
  /-- ANDI rd, rs1, imm : rd := rs1 &&& sext(imm) -/
  | ANDI (rd rs1 : Reg) (imm : BitVec 12)
  /-- ORI rd, rs1, imm : rd := rs1 ||| sext(imm) -/
  | ORI  (rd rs1 : Reg) (imm : BitVec 12)
  /-- XORI rd, rs1, imm : rd := rs1 ^^^ sext(imm) -/
  | XORI (rd rs1 : Reg) (imm : BitVec 12)
  /-- SLTI rd, rs1, imm : rd := (rs1 <s sext(imm)) ? 1 : 0 -/
  | SLTI (rd rs1 : Reg) (imm : BitVec 12)
  /-- SLTIU rd, rs1, imm : rd := (rs1 <u sext(imm)) ? 1 : 0 -/
  | SLTIU (rd rs1 : Reg) (imm : BitVec 12)
  /-- SLLI rd, rs1, shamt : rd := rs1 << shamt (6-bit shift amount for RV64) -/
  | SLLI (rd rs1 : Reg) (shamt : BitVec 6)
  /-- SRLI rd, rs1, shamt : rd := rs1 >>> shamt (logical, 6-bit) -/
  | SRLI (rd rs1 : Reg) (shamt : BitVec 6)
  /-- SRAI rd, rs1, shamt : rd := rs1 >>s shamt (arithmetic, 6-bit) -/
  | SRAI (rd rs1 : Reg) (shamt : BitVec 6)
  -- RV64I upper immediate
  /-- LUI rd, imm : rd := sext(imm << 12) (sign-extended to 64-bit in RV64) -/
  | LUI  (rd : Reg) (imm : BitVec 20)
  /-- AUIPC rd, imm : rd := PC + sext(imm << 12) -/
  | AUIPC (rd : Reg) (imm : BitVec 20)
  -- RV64I doubleword memory
  /-- LD rd, offset(rs1) : rd := mem64[rs1 + sext(offset)] -/
  | LD   (rd rs1 : Reg) (offset : BitVec 12)
  /-- SD rs2, offset(rs1) : mem64[rs1 + sext(offset)] := rs2 -/
  | SD   (rs1 rs2 : Reg) (offset : BitVec 12)
  -- RV64I word memory
  /-- LW rd, offset(rs1) : rd := sext(mem32[rs1 + sext(offset)]) (sign-extends in RV64) -/
  | LW   (rd rs1 : Reg) (offset : BitVec 12)
  /-- LWU rd, offset(rs1) : rd := zext(mem32[rs1 + sext(offset)]) -/
  | LWU  (rd rs1 : Reg) (offset : BitVec 12)
  /-- SW rs2, offset(rs1) : mem32[rs1 + sext(offset)] := rs2[31:0] -/
  | SW   (rs1 rs2 : Reg) (offset : BitVec 12)
  -- RV64I sub-word memory
  /-- LB rd, offset(rs1) : rd := sext(mem_byte[rs1 + sext(offset)]) -/
  | LB   (rd rs1 : Reg) (offset : BitVec 12)
  /-- LH rd, offset(rs1) : rd := sext(mem_halfword[rs1 + sext(offset)]) -/
  | LH   (rd rs1 : Reg) (offset : BitVec 12)
  /-- LBU rd, offset(rs1) : rd := zext(mem_byte[rs1 + sext(offset)]) -/
  | LBU  (rd rs1 : Reg) (offset : BitVec 12)
  /-- LHU rd, offset(rs1) : rd := zext(mem_halfword[rs1 + sext(offset)]) -/
  | LHU  (rd rs1 : Reg) (offset : BitVec 12)
  /-- SB rs2, offset(rs1) : mem_byte[rs1 + sext(offset)] := rs2[7:0] -/
  | SB   (rs1 rs2 : Reg) (offset : BitVec 12)
  /-- SH rs2, offset(rs1) : mem_halfword[rs1 + sext(offset)] := rs2[15:0] -/
  | SH   (rs1 rs2 : Reg) (offset : BitVec 12)
  -- RV64I branches
  /-- BEQ rs1, rs2, offset : branch if rs1 = rs2 (B-type, byte offset) -/
  | BEQ  (rs1 rs2 : Reg) (offset : BitVec 13)
  /-- BNE rs1, rs2, offset : branch if rs1 ≠ rs2 (B-type, byte offset) -/
  | BNE  (rs1 rs2 : Reg) (offset : BitVec 13)
  /-- BLT rs1, rs2, offset : branch if rs1 <s rs2 (signed) -/
  | BLT  (rs1 rs2 : Reg) (offset : BitVec 13)
  /-- BGE rs1, rs2, offset : branch if rs1 >=s rs2 (signed) -/
  | BGE  (rs1 rs2 : Reg) (offset : BitVec 13)
  /-- BLTU rs1, rs2, offset : branch if rs1 <u rs2 (unsigned) -/
  | BLTU (rs1 rs2 : Reg) (offset : BitVec 13)
  /-- BGEU rs1, rs2, offset : branch if rs1 >=u rs2 (unsigned) -/
  | BGEU (rs1 rs2 : Reg) (offset : BitVec 13)
  -- RV64I jumps
  /-- JAL rd, offset : jump and link (J-type, byte offset) -/
  | JAL  (rd : Reg) (offset : BitVec 21)
  /-- JALR rd, rs1, offset : jump and link register (I-type) -/
  | JALR (rd rs1 : Reg) (offset : BitVec 12)
  -- RV64I pseudo-instructions
  /-- MV rd, rs (pseudo: ADDI rd, rs, 0) -/
  | MV   (rd rs : Reg)
  /-- LI rd, imm (pseudo: load 64-bit immediate) -/
  | LI   (rd : Reg) (imm : Word)
  /-- NOP (pseudo: ADDI x0, x0, 0) -/
  | NOP
  -- RV64I *W instructions (word-size operations on lower 32 bits)
  /-- ADDIW rd, rs1, imm : rd := sext((rs1 + sext(imm))[31:0]) -/
  | ADDIW (rd rs1 : Reg) (imm : BitVec 12)
  -- RV64I system
  /-- ECALL: environment call -/
  | ECALL
  /-- FENCE: memory ordering fence (NOP in single-hart zkVM) -/
  | FENCE
  /-- EBREAK: breakpoint trap -/
  | EBREAK
  -- RV64M multiply
  /-- MUL rd, rs1, rs2 : rd := (rs1 * rs2)[63:0] -/
  | MUL  (rd rs1 rs2 : Reg)
  /-- MULH rd, rs1, rs2 : rd := (sext(rs1) * sext(rs2))[127:64] -/
  | MULH (rd rs1 rs2 : Reg)
  /-- MULHSU rd, rs1, rs2 : rd := (sext(rs1) * zext(rs2))[127:64] -/
  | MULHSU (rd rs1 rs2 : Reg)
  /-- MULHU rd, rs1, rs2 : rd := (zext(rs1) * zext(rs2))[127:64] -/
  | MULHU (rd rs1 rs2 : Reg)
  -- RV64M divide
  /-- DIV rd, rs1, rs2 : rd := rs1 /s rs2 (signed division) -/
  | DIV  (rd rs1 rs2 : Reg)
  /-- DIVU rd, rs1, rs2 : rd := rs1 /u rs2 (unsigned division) -/
  | DIVU (rd rs1 rs2 : Reg)
  /-- REM rd, rs1, rs2 : rd := rs1 %s rs2 (signed remainder) -/
  | REM  (rd rs1 rs2 : Reg)
  /-- REMU rd, rs1, rs2 : rd := rs1 %u rs2 (unsigned remainder) -/
  | REMU (rd rs1 rs2 : Reg)
  deriving Repr, DecidableEq

-- ============================================================================
-- Memory constraints
-- ============================================================================

/-- Valid memory region start. -/
def MEM_START : Nat := 0x20

/-- Valid memory region end. -/
def MEM_END : Nat := 0x78000000

/-- Address is 8-byte aligned (doubleword). -/
def isAligned8 (addr : Word) : Bool := addr.toNat % 8 == 0

/-- Address is 4-byte aligned. -/
def isAligned4 (addr : Word) : Bool := addr.toNat % 4 == 0

/-- Address is in valid memory range. -/
def isValidMemAddr (addr : Word) : Bool :=
  decide (MEM_START ≤ addr.toNat) && decide (addr.toNat ≤ MEM_END)

/-- Valid doubleword memory access: in range AND 8-byte aligned. -/
def isValidDwordAccess (addr : Word) : Bool :=
  isValidMemAddr addr && isAligned8 addr

/-- Valid word-size memory access: in range AND 4-byte aligned. -/
def isValidMemAccess (addr : Word) : Bool :=
  isValidMemAddr addr && isAligned4 addr

@[simp] theorem isValidDwordAccess_eq {addr : Word} :
    isValidDwordAccess addr = (isValidMemAddr addr && isAligned8 addr) := rfl

@[simp] theorem isValidMemAccess_eq {addr : Word} :
    isValidMemAccess addr = (isValidMemAddr addr && isAligned4 addr) := rfl

@[simp] theorem isValidMemAddr_eq {addr : Word} :
    isValidMemAddr addr = (decide (MEM_START ≤ addr.toNat) && decide (addr.toNat ≤ MEM_END)) := rfl

@[simp] theorem isAligned8_eq (addr : Word) :
    isAligned8 addr = (addr.toNat % 8 == 0) := rfl

@[simp] theorem isAligned4_eq (addr : Word) :
    isAligned4 addr = (addr.toNat % 4 == 0) := rfl

/-- Address is 2-byte aligned. -/
def isAligned2 (addr : Word) : Bool := addr.toNat % 2 == 0

/-- Valid halfword memory access: in range AND 2-byte aligned. -/
def isValidHalfwordAccess (addr : Word) : Bool :=
  isValidMemAddr addr && isAligned2 addr

/-- Valid byte memory access: in range (bytes need no alignment). -/
def isValidByteAccess (addr : Word) : Bool :=
  isValidMemAddr addr

@[simp] theorem isAligned2_eq (addr : Word) :
    isAligned2 addr = (addr.toNat % 2 == 0) := rfl

@[simp] theorem isValidHalfwordAccess_eq {addr : Word} :
    isValidHalfwordAccess addr = (isValidMemAddr addr && isAligned2 addr) := rfl

@[simp] theorem isValidByteAccess_eq {addr : Word} :
    isValidByteAccess addr = isValidMemAddr addr := rfl

/-- ValidMemRange addr n holds when n consecutive doubleword-aligned memory accesses
    starting at addr are all valid. -/
def ValidMemRange (addr : Word) (n : Nat) : Prop :=
  ∀ (i : Nat), i < n → isValidDwordAccess (addr + BitVec.ofNat 64 (8 * i)) = true

/-- Extract a single validity fact from ValidMemRange. -/
theorem ValidMemRange.get {addr : Word} {n : Nat}
    (h : ValidMemRange addr n) {i : Nat} (hi : i < n) :
    isValidDwordAccess (addr + BitVec.ofNat 64 (8 * i)) = true := h i hi

/-- Extract a single validity fact from ValidMemRange with address normalization. -/
theorem ValidMemRange.fetch {addr : Word} {n : Nat}
    (h : ValidMemRange addr n) (i : Nat) (target : Word)
    (hi : i < n)
    (haddr : addr + BitVec.ofNat 64 (8 * i) = target) :
    isValidDwordAccess target = true := by
  rw [← haddr]; exact h i hi

/-- Extract a byte from a 64-bit word at position 0-7. -/
def extractByte (w : Word) (pos : Nat) : BitVec 8 :=
  (w >>> (pos * 8)).truncate 8

/-- Extract a halfword from a 64-bit word at position 0-3 (in halfword units). -/
def extractHalfword (w : Word) (pos : Nat) : BitVec 16 :=
  (w >>> (pos * 16)).truncate 16

/-- Extract a 32-bit word from a 64-bit word at position 0-1 (in word units). -/
def extractWord32 (w : Word) (pos : Nat) : BitVec 32 :=
  (w >>> (pos * 32)).truncate 32

/-- Replace a byte in a 64-bit word at position 0-7. -/
def replaceByte (w : Word) (pos : Nat) (b : BitVec 8) : Word :=
  let mask : Word := ~~~(0xFF#64 <<< (pos * 8))
  (w &&& mask) ||| ((b.zeroExtend 64) <<< (pos * 8))

/-- Replace a halfword in a 64-bit word at position 0-3 (in halfword units). -/
def replaceHalfword (w : Word) (pos : Nat) (h : BitVec 16) : Word :=
  let mask : Word := ~~~(0xFFFF#64 <<< (pos * 16))
  (w &&& mask) ||| ((h.zeroExtend 64) <<< (pos * 16))

/-- Replace a 32-bit word in a 64-bit word at position 0-1 (in word units). -/
def replaceWord32 (w : Word) (pos : Nat) (v : BitVec 32) : Word :=
  let mask : Word := ~~~(0xFFFFFFFF#64 <<< (pos * 32))
  (w &&& mask) ||| ((v.zeroExtend 64) <<< (pos * 32))

/-- Align an address down to the nearest 8-byte boundary. -/
def alignToDword (addr : Word) : Word := addr &&& ~~~7#64

/-- Get the byte offset within a doubleword (0-7). -/
def byteOffset (addr : Word) : Nat := (addr &&& 7#64).toNat

-- ============================================================================
-- Machine State
-- ============================================================================

/-- The machine state: a register file, memory, code memory, and program counter.
    Memory is doubleword-addressable (8-byte aligned addresses map to 64-bit words). -/
structure MachineState where
  /-- Register file: maps register to its value -/
  regs : Reg → Word
  /-- Doubleword-addressable memory -/
  mem  : Word → Word
  /-- Code memory: maps addresses to instructions -/
  code : Word → Option Instr := fun _ => none
  /-- Program counter -/
  pc   : Word
  /-- Committed public outputs (a0, a1) from COMMIT syscalls -/
  committed : List (Word × Word) := []
  /-- Accumulated public values from WRITE syscalls (flat byte stream) -/
  publicValues : List (BitVec 8) := []
  /-- Private input stream (flat byte list, consumed by HINT_READ) -/
  privateInput : List (BitVec 8) := []

namespace MachineState

/-- Read a register (x0 always returns 0). -/
def getReg (s : MachineState) (r : Reg) : Word :=
  match r with
  | .x0 => 0#64
  | _   => s.regs r

/-- Write a register (writes to x0 are silently dropped). -/
def setReg (s : MachineState) (r : Reg) (v : Word) : MachineState :=
  match r with
  | .x0 => s
  | _   => { s with regs := fun r' => if r' == r then v else s.regs r' }

/-- Read memory at an address. -/
def getMem (s : MachineState) (a : Word) : Word :=
  s.mem a

/-- Write memory at an address. -/
def setMem (s : MachineState) (a : Word) (v : Word) : MachineState :=
  { s with mem := fun a' => if a' == a then v else s.mem a' }

/-- Set the program counter. -/
def setPC (s : MachineState) (v : Word) : MachineState :=
  { s with pc := v }

/-- Append a committed public output pair. -/
def appendCommit (s : MachineState) (a0 a1 : Word) : MachineState :=
  { s with committed := s.committed ++ [(a0, a1)] }

/-- Read n consecutive doublewords from memory starting at base address. -/
def readWords (s : MachineState) (base : Word) : Nat → List Word
  | 0 => []
  | n + 1 => s.getMem base :: readWords s (base + 8) n

/-- Write n consecutive doublewords to memory starting at base address. -/
def writeWords (s : MachineState) (base : Word) : List Word → MachineState
  | [] => s
  | w :: ws => (s.setMem base w).writeWords (base + 8) ws

/-- Append bytes to the public values stream. -/
def appendPublicValues (s : MachineState) (bytes : List (BitVec 8)) : MachineState :=
  { s with publicValues := s.publicValues ++ bytes }

/-- Read a byte from memory at an arbitrary byte address.
    Reads the containing doubleword and extracts the appropriate byte. -/
def getByte (s : MachineState) (addr : Word) : BitVec 8 :=
  extractByte (s.getMem (alignToDword addr)) (byteOffset addr)

/-- Read a halfword from memory at a 2-byte aligned address. -/
def getHalfword (s : MachineState) (addr : Word) : BitVec 16 :=
  extractHalfword (s.getMem (alignToDword addr)) ((byteOffset addr) / 2)

/-- Read a 32-bit word from memory at a 4-byte aligned address. -/
def getWord32 (s : MachineState) (addr : Word) : BitVec 32 :=
  extractWord32 (s.getMem (alignToDword addr)) ((byteOffset addr) / 4)

/-- Write a byte to memory at an arbitrary byte address. -/
def setByte (s : MachineState) (addr : Word) (b : BitVec 8) : MachineState :=
  let wa := alignToDword addr
  let pos := byteOffset addr
  s.setMem wa (replaceByte (s.getMem wa) pos b)

/-- Write a halfword to memory at a 2-byte aligned address. -/
def setHalfword (s : MachineState) (addr : Word) (h : BitVec 16) : MachineState :=
  let wa := alignToDword addr
  let pos := (byteOffset addr) / 2
  s.setMem wa (replaceHalfword (s.getMem wa) pos h)

/-- Write a 32-bit word to memory at a 4-byte aligned address. -/
def setWord32 (s : MachineState) (addr : Word) (v : BitVec 32) : MachineState :=
  let wa := alignToDword addr
  let pos := (byteOffset addr) / 4
  s.setMem wa (replaceWord32 (s.getMem wa) pos v)

/-- Read n consecutive bytes from memory starting at base byte address. -/
def readBytes (s : MachineState) (base : Word) : Nat → List (BitVec 8)
  | 0 => []
  | n + 1 => s.getByte base :: readBytes s (base + 1) n

end MachineState

/-- Convert up to 8 bytes (little-endian) into a 64-bit word, zero-padding if fewer than 8. -/
def bytesToWordLE (bs : List (BitVec 8)) : Word :=
  let b0 : Word := (bs[0]?.getD 0).zeroExtend 64
  let b1 : Word := (bs[1]?.getD 0).zeroExtend 64
  let b2 : Word := (bs[2]?.getD 0).zeroExtend 64
  let b3 : Word := (bs[3]?.getD 0).zeroExtend 64
  let b4 : Word := (bs[4]?.getD 0).zeroExtend 64
  let b5 : Word := (bs[5]?.getD 0).zeroExtend 64
  let b6 : Word := (bs[6]?.getD 0).zeroExtend 64
  let b7 : Word := (bs[7]?.getD 0).zeroExtend 64
  b0 ||| (b1 <<< (8 : Word)) ||| (b2 <<< (16 : Word)) ||| (b3 <<< (24 : Word)) |||
  (b4 <<< (32 : Word)) ||| (b5 <<< (40 : Word)) ||| (b6 <<< (48 : Word)) ||| (b7 <<< (56 : Word))

namespace MachineState

/-- Write a byte stream as consecutive LE doublewords to memory. -/
def writeBytesAsWords (s : MachineState) (base : Word) : List (BitVec 8) → MachineState
  | [] => s
  | b :: bs =>
    let chunk := (b :: bs).take 8
    let rest := (b :: bs).drop 8
    (s.setMem base (bytesToWordLE chunk)).writeBytesAsWords (base + 8) rest
termination_by l => l.length

-- ============================================================================
-- Simp lemmas
-- ============================================================================

@[simp] theorem pc_setReg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).pc = s.pc := by cases r <;> rfl

@[simp] theorem pc_setMem (s : MachineState) (a : Word) (v : Word) :
    (s.setMem a v).pc = s.pc := by simp [setMem]

@[simp] theorem pc_setByte (s : MachineState) (addr : Word) (b : BitVec 8) :
    (s.setByte addr b).pc = s.pc := by simp [setByte]

@[simp] theorem pc_setHalfword (s : MachineState) (addr : Word) (h : BitVec 16) :
    (s.setHalfword addr h).pc = s.pc := by simp [setHalfword]

@[simp] theorem pc_setWord32 (s : MachineState) (addr : Word) (v : BitVec 32) :
    (s.setWord32 addr v).pc = s.pc := by simp [setWord32]

@[simp] theorem code_setReg {s : MachineState} {r : Reg} {v : Word} :
    (s.setReg r v).code = s.code := by cases r <;> rfl

@[simp] theorem code_setMem {s : MachineState} {a : Word} {v : Word} :
    (s.setMem a v).code = s.code := by simp [setMem]

@[simp] theorem code_setPC {s : MachineState} {v : Word} :
    (s.setPC v).code = s.code := by simp [setPC]

@[simp] theorem code_setByte {s : MachineState} {addr : Word} {b : BitVec 8} :
    (s.setByte addr b).code = s.code := by simp [setByte]

@[simp] theorem code_setHalfword {s : MachineState} {addr : Word} {h : BitVec 16} :
    (s.setHalfword addr h).code = s.code := by simp [setHalfword]

@[simp] theorem code_setWord32 {s : MachineState} {addr : Word} {v : BitVec 32} :
    (s.setWord32 addr v).code = s.code := by simp [setWord32]

@[simp] theorem code_appendCommit {s : MachineState} {a0 a1 : Word} :
    (s.appendCommit a0 a1).code = s.code := by simp [appendCommit]

@[simp] theorem code_appendPublicValues {s : MachineState} {bytes : List (BitVec 8)} :
    (s.appendPublicValues bytes).code = s.code := by simp [appendPublicValues]

@[simp] theorem code_writeWords {s : MachineState} {base : Word} {words : List Word} :
    (s.writeWords base words).code = s.code := by
  induction words generalizing s base with
  | nil => rfl
  | cons w ws ih => simp [writeWords, ih]

@[simp] theorem getReg_setPC (s : MachineState) (v : Word) (r : Reg) :
    (s.setPC v).getReg r = s.getReg r := by cases r <;> rfl

theorem getReg_setReg_ne (s : MachineState) (r r' : Reg) (v : Word)
    (h : r ≠ r') : (s.setReg r v).getReg r' = s.getReg r' := by
  cases r <;> cases r' <;> first | exact absurd rfl h | rfl

theorem getReg_setReg_eq (s : MachineState) (r : Reg) (v : Word)
    (h : r ≠ .x0) : (s.setReg r v).getReg r = v := by
  cases r <;> first | exact absurd rfl h | rfl

@[simp] theorem getMem_setMem_eq (s : MachineState) (a : Word) (v : Word) :
    (s.setMem a v).getMem a = v := by simp [getMem, setMem]

@[simp] theorem getMem_setMem_ne (s : MachineState) (a a' : Word) (v : Word)
    (h : a' ≠ a) : (s.setMem a v).getMem a' = s.getMem a' := by
  simp [getMem, setMem, h]

@[simp] theorem getMem_setReg (s : MachineState) (r : Reg) (v : Word) (a : Word) :
    (s.setReg r v).getMem a = s.getMem a := by
  cases r <;> simp [getMem, setReg]

@[simp] theorem getMem_setPC (s : MachineState) (v : Word) (a : Word) :
    (s.setPC v).getMem a = s.getMem a := by simp [getMem, setPC]

@[simp] theorem committed_setReg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).committed = s.committed := by cases r <;> rfl

@[simp] theorem committed_setMem (s : MachineState) (a : Word) (v : Word) :
    (s.setMem a v).committed = s.committed := by simp [setMem]

@[simp] theorem committed_setByte (s : MachineState) (addr : Word) (b : BitVec 8) :
    (s.setByte addr b).committed = s.committed := by simp [setByte]

@[simp] theorem committed_setHalfword (s : MachineState) (addr : Word) (h : BitVec 16) :
    (s.setHalfword addr h).committed = s.committed := by simp [setHalfword]

@[simp] theorem committed_setPC (s : MachineState) (v : Word) :
    (s.setPC v).committed = s.committed := by simp [setPC]

@[simp] theorem publicValues_setReg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).publicValues = s.publicValues := by cases r <;> rfl

@[simp] theorem publicValues_setMem (s : MachineState) (a : Word) (v : Word) :
    (s.setMem a v).publicValues = s.publicValues := by simp [setMem]

@[simp] theorem publicValues_setByte (s : MachineState) (addr : Word) (b : BitVec 8) :
    (s.setByte addr b).publicValues = s.publicValues := by simp [setByte]

@[simp] theorem publicValues_setHalfword (s : MachineState) (addr : Word) (h : BitVec 16) :
    (s.setHalfword addr h).publicValues = s.publicValues := by simp [setHalfword]

@[simp] theorem publicValues_setPC (s : MachineState) (v : Word) :
    (s.setPC v).publicValues = s.publicValues := by simp [setPC]

@[simp] theorem publicValues_appendCommit (s : MachineState) (a0 a1 : Word) :
    (s.appendCommit a0 a1).publicValues = s.publicValues := by simp [appendCommit]

@[simp] theorem privateInput_setReg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).privateInput = s.privateInput := by cases r <;> rfl

@[simp] theorem privateInput_setMem (s : MachineState) (a : Word) (v : Word) :
    (s.setMem a v).privateInput = s.privateInput := by simp [setMem]

@[simp] theorem privateInput_setByte (s : MachineState) (addr : Word) (b : BitVec 8) :
    (s.setByte addr b).privateInput = s.privateInput := by simp [setByte]

@[simp] theorem privateInput_setHalfword (s : MachineState) (addr : Word) (h : BitVec 16) :
    (s.setHalfword addr h).privateInput = s.privateInput := by simp [setHalfword]

@[simp] theorem privateInput_setPC (s : MachineState) (v : Word) :
    (s.setPC v).privateInput = s.privateInput := by simp [setPC]

@[simp] theorem privateInput_appendCommit (s : MachineState) (a0 a1 : Word) :
    (s.appendCommit a0 a1).privateInput = s.privateInput := by simp [appendCommit]

@[simp] theorem privateInput_appendPublicValues (s : MachineState) (bytes : List (BitVec 8)) :
    (s.appendPublicValues bytes).privateInput = s.privateInput := by simp [appendPublicValues]

-- appendCommit preservation lemmas

@[simp] theorem getReg_appendCommit (s : MachineState) (a0 a1 : Word) (r : Reg) :
    (s.appendCommit a0 a1).getReg r = s.getReg r := by cases r <;> rfl

@[simp] theorem getMem_appendCommit (s : MachineState) (a0 a1 : Word) (a : Word) :
    (s.appendCommit a0 a1).getMem a = s.getMem a := by simp [appendCommit, getMem]

@[simp] theorem pc_appendCommit (s : MachineState) (a0 a1 : Word) :
    (s.appendCommit a0 a1).pc = s.pc := by simp [appendCommit]

@[simp] theorem committed_appendCommit (s : MachineState) (a0 a1 : Word) :
    (s.appendCommit a0 a1).committed = s.committed ++ [(a0, a1)] := by simp [appendCommit]

-- appendPublicValues preservation lemmas

@[simp] theorem getReg_appendPublicValues (s : MachineState) (bytes : List (BitVec 8)) (r : Reg) :
    (s.appendPublicValues bytes).getReg r = s.getReg r := by cases r <;> rfl

@[simp] theorem getMem_appendPublicValues (s : MachineState) (bytes : List (BitVec 8)) (a : Word) :
    (s.appendPublicValues bytes).getMem a = s.getMem a := by simp [appendPublicValues, getMem]

@[simp] theorem pc_appendPublicValues (s : MachineState) (bytes : List (BitVec 8)) :
    (s.appendPublicValues bytes).pc = s.pc := by simp [appendPublicValues]

@[simp] theorem committed_appendPublicValues (s : MachineState) (bytes : List (BitVec 8)) :
    (s.appendPublicValues bytes).committed = s.committed := by simp [appendPublicValues]

@[simp] theorem publicValues_appendPublicValues (s : MachineState) (bytes : List (BitVec 8)) :
    (s.appendPublicValues bytes).publicValues = s.publicValues ++ bytes := by
  simp [appendPublicValues]

-- readWords / writeWords simp lemmas

@[simp] theorem readWords_zero (s : MachineState) (base : Word) :
    s.readWords base 0 = [] := rfl

@[simp] theorem readWords_succ (s : MachineState) (base : Word) (n : Nat) :
    s.readWords base (n + 1) = s.getMem base :: s.readWords (base + 8) n := rfl

@[simp] theorem writeWords_nil (s : MachineState) (base : Word) :
    s.writeWords base [] = s := rfl

@[simp] theorem writeWords_cons (s : MachineState) (base : Word) (w : Word) (ws : List Word) :
    s.writeWords base (w :: ws) = (s.setMem base w).writeWords (base + 8) ws := rfl

@[simp] theorem pc_writeWords (s : MachineState) (base : Word) (words : List Word) :
    (s.writeWords base words).pc = s.pc := by
  induction words generalizing s base with
  | nil => rfl
  | cons w ws ih => simp [writeWords, ih]

@[simp] theorem committed_writeWords (s : MachineState) (base : Word) (words : List Word) :
    (s.writeWords base words).committed = s.committed := by
  induction words generalizing s base with
  | nil => rfl
  | cons w ws ih => simp [writeWords, ih]

@[simp] theorem publicValues_writeWords (s : MachineState) (base : Word) (words : List Word) :
    (s.writeWords base words).publicValues = s.publicValues := by
  induction words generalizing s base with
  | nil => rfl
  | cons w ws ih => simp [writeWords, ih]

@[simp] theorem privateInput_writeWords (s : MachineState) (base : Word) (words : List Word) :
    (s.writeWords base words).privateInput = s.privateInput := by
  induction words generalizing s base with
  | nil => rfl
  | cons w ws ih => simp [writeWords, ih]

@[simp] theorem getReg_writeWords (s : MachineState) (base : Word) (words : List Word) (r : Reg) :
    (s.writeWords base words).getReg r = s.getReg r := by
  induction words generalizing s base with
  | nil => rfl
  | cons w ws ih =>
    simp [writeWords, ih]
    cases r <;> simp [getReg, setMem]

-- readBytes simp lemmas

@[simp] theorem readBytes_zero (s : MachineState) (base : Word) :
    s.readBytes base 0 = [] := rfl

@[simp] theorem readBytes_succ (s : MachineState) (base : Word) (n : Nat) :
    s.readBytes base (n + 1) = s.getByte base :: s.readBytes (base + 1) n := rfl

-- writeBytesAsWords simp lemmas

@[simp] theorem writeBytesAsWords_nil (s : MachineState) (base : Word) :
    s.writeBytesAsWords base [] = s := by unfold writeBytesAsWords; rfl

@[simp] theorem pc_writeBytesAsWords (s : MachineState) (base : Word) (bytes : List (BitVec 8)) :
    (s.writeBytesAsWords base bytes).pc = s.pc := by
  match bytes with
  | [] => unfold writeBytesAsWords; rfl
  | _ :: _ =>
    unfold writeBytesAsWords
    rw [pc_writeBytesAsWords]
    simp
termination_by bytes.length
decreasing_by simp [List.length_drop]; omega

@[simp] theorem code_writeBytesAsWords (s : MachineState) (base : Word) (bytes : List (BitVec 8)) :
    (s.writeBytesAsWords base bytes).code = s.code := by
  match bytes with
  | [] => unfold writeBytesAsWords; rfl
  | _ :: _ =>
    unfold writeBytesAsWords
    rw [code_writeBytesAsWords]
    simp
termination_by bytes.length
decreasing_by simp [List.length_drop]; omega

@[simp] theorem committed_writeBytesAsWords (s : MachineState) (base : Word) (bytes : List (BitVec 8)) :
    (s.writeBytesAsWords base bytes).committed = s.committed := by
  match bytes with
  | [] => unfold writeBytesAsWords; rfl
  | _ :: _ =>
    unfold writeBytesAsWords
    rw [committed_writeBytesAsWords]
    simp
termination_by bytes.length
decreasing_by simp [List.length_drop]; omega

@[simp] theorem publicValues_writeBytesAsWords (s : MachineState) (base : Word) (bytes : List (BitVec 8)) :
    (s.writeBytesAsWords base bytes).publicValues = s.publicValues := by
  match bytes with
  | [] => unfold writeBytesAsWords; rfl
  | _ :: _ =>
    unfold writeBytesAsWords
    rw [publicValues_writeBytesAsWords]
    simp
termination_by bytes.length
decreasing_by simp [List.length_drop]; omega

@[simp] theorem privateInput_writeBytesAsWords (s : MachineState) (base : Word) (bytes : List (BitVec 8)) :
    (s.writeBytesAsWords base bytes).privateInput = s.privateInput := by
  match bytes with
  | [] => unfold writeBytesAsWords; rfl
  | _ :: _ =>
    unfold writeBytesAsWords
    rw [privateInput_writeBytesAsWords]
    simp
termination_by bytes.length
decreasing_by simp [List.length_drop]; omega

@[simp] theorem getReg_writeBytesAsWords (s : MachineState) (base : Word) (bytes : List (BitVec 8)) (r : Reg) :
    (s.writeBytesAsWords base bytes).getReg r = s.getReg r := by
  match bytes with
  | [] => unfold writeBytesAsWords; rfl
  | _ :: _ =>
    unfold writeBytesAsWords
    rw [getReg_writeBytesAsWords]
    cases r <;> simp [getReg, setMem]
termination_by bytes.length
decreasing_by simp [List.length_drop]; omega

/-- Predicate asserting the committed output stream equals a given list. -/
def committedIs (vals : List (Word × Word)) (s : MachineState) : Prop :=
  s.committed = vals

/-- Predicate asserting the public values stream equals a given list. -/
def publicValuesIs (vals : List (BitVec 8)) (s : MachineState) : Prop :=
  s.publicValues = vals

/-- Predicate asserting the private input stream equals a given list. -/
def privateInputIs (vals : List (BitVec 8)) (s : MachineState) : Prop :=
  s.privateInput = vals

end MachineState

end EvmAsm.Rv64
