/-
  EvmAsm.Rv32.Basic

  A simplified RISC-V machine model for macro assembly verification,
  inspired by "Coq: The world's best macro assembler?" (Kennedy et al., 2013).

  We model a small subset of RV32I: enough to demonstrate verified macro
  assembly with separation logic specifications.
-/

namespace EvmAsm

-- ============================================================================
-- Registers
-- ============================================================================

/-- A small subset of RISC-V integer registers. -/
inductive Reg where
  | x0  -- hardwired zero
  | x1  -- ra
  | x2  -- sp
  | x5  -- t0
  | x6  -- t1
  | x7  -- t2
  | x10 -- a0
  | x11 -- a1
  | x12 -- a2
  deriving DecidableEq, BEq, Repr, Hashable

instance : LawfulBEq Reg where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

namespace Reg

def toNat : Reg → Nat
  | x0  => 0
  | x1  => 1
  | x2  => 2
  | x5  => 5
  | x6  => 6
  | x7  => 7
  | x10 => 10
  | x11 => 11
  | x12 => 12

instance : ToString Reg where
  toString r := s!"x{r.toNat}"

end Reg

-- ============================================================================
-- Word type (32-bit bitvectors)
-- ============================================================================

/-- We use 32-bit words as our machine word size. -/
abbrev Word := BitVec 32

/-- Memory addresses are words. -/
abbrev Addr := Word

-- ============================================================================
-- Instructions (RV32IM)
-- ============================================================================

/-- A single RISC-V instruction. -/
inductive Instr where
  -- RV32I ALU register-register
  /-- ADD rd, rs1, rs2 : rd := rs1 + rs2 -/
  | ADD  (rd rs1 rs2 : Reg)
  /-- SUB rd, rs1, rs2 : rd := rs1 - rs2 -/
  | SUB  (rd rs1 rs2 : Reg)
  /-- SLL rd, rs1, rs2 : rd := rs1 << rs2[4:0] (shift left logical) -/
  | SLL  (rd rs1 rs2 : Reg)
  /-- SRL rd, rs1, rs2 : rd := rs1 >>> rs2[4:0] (shift right logical) -/
  | SRL  (rd rs1 rs2 : Reg)
  /-- SRA rd, rs1, rs2 : rd := rs1 >>s rs2[4:0] (shift right arithmetic) -/
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
  -- RV32I ALU immediate
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
  /-- SLLI rd, rs1, shamt : rd := rs1 << shamt -/
  | SLLI (rd rs1 : Reg) (shamt : BitVec 5)
  /-- SRLI rd, rs1, shamt : rd := rs1 >>> shamt (logical) -/
  | SRLI (rd rs1 : Reg) (shamt : BitVec 5)
  /-- SRAI rd, rs1, shamt : rd := rs1 >>s shamt (arithmetic) -/
  | SRAI (rd rs1 : Reg) (shamt : BitVec 5)
  -- RV32I upper immediate
  /-- LUI rd, imm : rd := imm << 12 -/
  | LUI  (rd : Reg) (imm : BitVec 20)
  /-- AUIPC rd, imm : rd := PC + (imm << 12) -/
  | AUIPC (rd : Reg) (imm : BitVec 20)
  -- RV32I word memory
  /-- LW rd, offset(rs1) : rd := mem[rs1 + sext(offset)] -/
  | LW   (rd rs1 : Reg) (offset : BitVec 12)
  /-- SW rs2, offset(rs1) : mem[rs1 + sext(offset)] := rs2 -/
  | SW   (rs1 rs2 : Reg) (offset : BitVec 12)
  -- RV32I sub-word memory
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
  -- RV32I branches
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
  -- RV32I jumps
  /-- JAL rd, offset : jump and link (J-type, byte offset) -/
  | JAL  (rd : Reg) (offset : BitVec 21)
  /-- JALR rd, rs1, offset : jump and link register (I-type) -/
  | JALR (rd rs1 : Reg) (offset : BitVec 12)
  -- RV32I pseudo-instructions
  /-- MV rd, rs (pseudo: ADDI rd, rs, 0) -/
  | MV   (rd rs : Reg)
  /-- LI rd, imm (pseudo: load immediate) -/
  | LI   (rd : Reg) (imm : Word)
  /-- NOP (pseudo: ADDI x0, x0, 0) -/
  | NOP
  -- RV32I system
  /-- ECALL: environment call (syscall ID in t0/x5, args in a0-a2).
      Following SP1 convention, t0 = 0 signals HALT with exit code in a0. -/
  | ECALL
  /-- FENCE: memory ordering fence (NOP in single-hart zkVM) -/
  | FENCE
  /-- EBREAK: breakpoint trap -/
  | EBREAK
  -- RV32M multiply
  /-- MUL rd, rs1, rs2 : rd := (rs1 * rs2)[31:0] -/
  | MUL  (rd rs1 rs2 : Reg)
  /-- MULH rd, rs1, rs2 : rd := (sext(rs1) * sext(rs2))[63:32] -/
  | MULH (rd rs1 rs2 : Reg)
  /-- MULHSU rd, rs1, rs2 : rd := (sext(rs1) * zext(rs2))[63:32] -/
  | MULHSU (rd rs1 rs2 : Reg)
  /-- MULHU rd, rs1, rs2 : rd := (zext(rs1) * zext(rs2))[63:32] -/
  | MULHU (rd rs1 rs2 : Reg)
  -- RV32M divide
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
-- SP1 memory constraints
-- ============================================================================

/-- SP1 valid memory region start (addresses 0x0–0x1F are reserved for registers). -/
def SP1_MEM_START : Nat := 0x20

/-- SP1 valid memory region end. -/
def SP1_MEM_END : Nat := 0x78000000

/-- Address is 4-byte aligned. -/
def isAligned4 (addr : Addr) : Bool := addr.toNat % 4 == 0

/-- Address is in valid SP1 memory range [0x20, 0x78000000]. -/
def isValidMemAddr (addr : Addr) : Bool :=
  decide (SP1_MEM_START ≤ addr.toNat) && decide (addr.toNat ≤ SP1_MEM_END)

/-- Valid word-size memory access: in range AND 4-byte aligned. -/
def isValidMemAccess (addr : Addr) : Bool :=
  isValidMemAddr addr && isAligned4 addr

@[simp] theorem isValidMemAccess_eq (addr : Addr) :
    isValidMemAccess addr = (isValidMemAddr addr && isAligned4 addr) := rfl

/-- ValidMemRange addr n holds when n consecutive word-aligned memory accesses
    starting at addr are all valid. -/
def ValidMemRange (addr : Addr) (n : Nat) : Prop :=
  ∀ (i : Nat), i < n → isValidMemAccess (addr + BitVec.ofNat 32 (4 * i)) = true

/-- Extract a single validity fact from ValidMemRange. -/
theorem ValidMemRange.get {addr : Addr} {n : Nat}
    (h : ValidMemRange addr n) {i : Nat} (hi : i < n) :
    isValidMemAccess (addr + BitVec.ofNat 32 (4 * i)) = true := h i hi

/-- Split a ValidMemRange into two halves. -/
theorem ValidMemRange.split {addr : Addr} {n1 n2 : Nat}
    (h : ValidMemRange addr (n1 + n2)) :
    ValidMemRange addr n1 ∧
    ValidMemRange (addr + BitVec.ofNat 32 (4 * n1)) n2 := by
  constructor
  · intro i hi; exact h i (by omega)
  · intro i hi
    have h_main := h (n1 + i) (by omega)
    have haddr : addr + BitVec.ofNat 32 (4 * (n1 + i))
               = addr + BitVec.ofNat 32 (4 * n1) + BitVec.ofNat 32 (4 * i) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rwa [haddr] at h_main

/-- Extract a single validity fact from ValidMemRange with address normalization. -/
theorem ValidMemRange.fetch {addr : Addr} {n : Nat}
    (h : ValidMemRange addr n) (i : Nat) (target : Addr)
    (hi : i < n)
    (haddr : addr + BitVec.ofNat 32 (4 * i) = target) :
    isValidMemAccess target = true := by
  rw [← haddr]; exact h i hi

@[simp] theorem isValidMemAddr_eq (addr : Addr) :
    isValidMemAddr addr = (decide (SP1_MEM_START ≤ addr.toNat) && decide (addr.toNat ≤ SP1_MEM_END)) := rfl

@[simp] theorem isAligned4_eq (addr : Addr) :
    isAligned4 addr = (addr.toNat % 4 == 0) := rfl

-- ============================================================================
-- Sub-word memory access helpers
-- ============================================================================

/-- Address is 2-byte aligned. -/
def isAligned2 (addr : Addr) : Bool := addr.toNat % 2 == 0

/-- Valid halfword memory access: in range AND 2-byte aligned. -/
def isValidHalfwordAccess (addr : Addr) : Bool :=
  isValidMemAddr addr && isAligned2 addr

/-- Valid byte memory access: in range (bytes need no alignment). -/
def isValidByteAccess (addr : Addr) : Bool :=
  isValidMemAddr addr

@[simp] theorem isAligned2_eq (addr : Addr) :
    isAligned2 addr = (addr.toNat % 2 == 0) := rfl

@[simp] theorem isValidHalfwordAccess_eq (addr : Addr) :
    isValidHalfwordAccess addr = (isValidMemAddr addr && isAligned2 addr) := rfl

@[simp] theorem isValidByteAccess_eq (addr : Addr) :
    isValidByteAccess addr = isValidMemAddr addr := rfl

/-- Extract a byte from a 32-bit word at position 0-3. -/
def extractByte (w : Word) (pos : Nat) : BitVec 8 :=
  (w >>> (pos * 8)).truncate 8

/-- Extract a halfword from a 32-bit word at position 0-1 (in halfword units). -/
def extractHalfword (w : Word) (pos : Nat) : BitVec 16 :=
  (w >>> (pos * 16)).truncate 16

/-- Replace a byte in a 32-bit word at position 0-3. -/
def replaceByte (w : Word) (pos : Nat) (b : BitVec 8) : Word :=
  let mask : Word := ~~~(0xFF#32 <<< (pos * 8))
  (w &&& mask) ||| ((b.zeroExtend 32) <<< (pos * 8))

/-- Replace a halfword in a 32-bit word at position 0-1 (in halfword units). -/
def replaceHalfword (w : Word) (pos : Nat) (h : BitVec 16) : Word :=
  let mask : Word := ~~~(0xFFFF#32 <<< (pos * 16))
  (w &&& mask) ||| ((h.zeroExtend 32) <<< (pos * 16))

/-- Align an address down to the nearest 4-byte boundary. -/
def alignToWord (addr : Addr) : Addr := addr &&& ~~~3#32

/-- Get the byte offset within a word (0-3). -/
def byteOffset (addr : Addr) : Nat := (addr &&& 3#32).toNat

-- ============================================================================
-- Machine State
-- ============================================================================

/-- The machine state: a register file, memory, code memory, and program counter. -/
structure MachineState where
  /-- Register file: maps register to its value -/
  regs : Reg → Word
  /-- Byte-addressable memory (simplified: word-addressable for now) -/
  mem  : Addr → Word
  /-- Code memory: maps addresses to instructions -/
  code : Addr → Option Instr := fun _ => none
  /-- Program counter -/
  pc   : Word
  /-- Committed public outputs (a0, a1) from COMMIT syscalls -/
  committed : List (Word × Word) := []
  /-- Accumulated public values from WRITE syscalls (flat byte stream, matching SP1) -/
  publicValues : List (BitVec 8) := []
  /-- Private input stream (flat byte list, consumed by HINT_READ, matching SP1) -/
  privateInput : List (BitVec 8) := []

namespace MachineState

/-- Read a register (x0 always returns 0). -/
def getReg (s : MachineState) (r : Reg) : Word :=
  match r with
  | .x0 => 0#32
  | _   => s.regs r

/-- Write a register (writes to x0 are silently dropped). -/
def setReg (s : MachineState) (r : Reg) (v : Word) : MachineState :=
  match r with
  | .x0 => s
  | _   => { s with regs := fun r' => if r' == r then v else s.regs r' }

/-- Read memory at an address. -/
def getMem (s : MachineState) (a : Addr) : Word :=
  s.mem a

/-- Write memory at an address. -/
def setMem (s : MachineState) (a : Addr) (v : Word) : MachineState :=
  { s with mem := fun a' => if a' == a then v else s.mem a' }

/-- Set the program counter. -/
def setPC (s : MachineState) (v : Word) : MachineState :=
  { s with pc := v }

/-- Append a committed public output pair. -/
def appendCommit (s : MachineState) (a0 a1 : Word) : MachineState :=
  { s with committed := s.committed ++ [(a0, a1)] }

/-- Read n consecutive words from memory starting at base address. -/
def readWords (s : MachineState) (base : Addr) : Nat → List Word
  | 0 => []
  | n + 1 => s.getMem base :: readWords s (base + 4) n

/-- Write n consecutive words to memory starting at base address. -/
def writeWords (s : MachineState) (base : Addr) : List Word → MachineState
  | [] => s
  | w :: ws => (s.setMem base w).writeWords (base + 4) ws

/-- Append bytes to the public values stream. -/
def appendPublicValues (s : MachineState) (bytes : List (BitVec 8)) : MachineState :=
  { s with publicValues := s.publicValues ++ bytes }

/-- Read a byte from memory at an arbitrary byte address.
    Reads the containing word and extracts the appropriate byte. -/
def getByte (s : MachineState) (addr : Addr) : BitVec 8 :=
  extractByte (s.getMem (alignToWord addr)) (byteOffset addr)

/-- Read a halfword from memory at a 2-byte aligned address.
    Reads the containing word and extracts the appropriate halfword. -/
def getHalfword (s : MachineState) (addr : Addr) : BitVec 16 :=
  extractHalfword (s.getMem (alignToWord addr)) ((byteOffset addr) / 2)

/-- Write a byte to memory at an arbitrary byte address.
    Reads the containing word, replaces the byte, writes back. -/
def setByte (s : MachineState) (addr : Addr) (b : BitVec 8) : MachineState :=
  let wa := alignToWord addr
  let pos := byteOffset addr
  s.setMem wa (replaceByte (s.getMem wa) pos b)

/-- Write a halfword to memory at a 2-byte aligned address.
    Reads the containing word, replaces the halfword, writes back. -/
def setHalfword (s : MachineState) (addr : Addr) (h : BitVec 16) : MachineState :=
  let wa := alignToWord addr
  let pos := (byteOffset addr) / 2
  s.setMem wa (replaceHalfword (s.getMem wa) pos h)

/-- Read n consecutive bytes from memory starting at base byte address.
    Each byte is extracted from the containing word using getByte. -/
def readBytes (s : MachineState) (base : Addr) : Nat → List (BitVec 8)
  | 0 => []
  | n + 1 => s.getByte base :: readBytes s (base + 1) n

end MachineState

/-- Convert up to 4 bytes (little-endian) into a 32-bit word, zero-padding if fewer than 4. -/
def bytesToWordLE (bs : List (BitVec 8)) : Word :=
  let b0 : Word := (bs[0]?.getD 0).zeroExtend 32
  let b1 : Word := (bs[1]?.getD 0).zeroExtend 32
  let b2 : Word := (bs[2]?.getD 0).zeroExtend 32
  let b3 : Word := (bs[3]?.getD 0).zeroExtend 32
  b0 ||| (b1 <<< (8 : Word)) ||| (b2 <<< (16 : Word)) ||| (b3 <<< (24 : Word))

namespace MachineState

/-- Write a byte stream as consecutive LE words to memory, starting at base (word-aligned).
    Chunks the byte list into groups of 4, zero-pads the last chunk if needed. -/
def writeBytesAsWords (s : MachineState) (base : Addr) : List (BitVec 8) → MachineState
  | [] => s
  | b :: bs =>
    let chunk := (b :: bs).take 4
    let rest := (b :: bs).drop 4
    (s.setMem base (bytesToWordLE chunk)).writeBytesAsWords (base + 4) rest
termination_by l => l.length

end MachineState

/-- Convert a byte list into a word list by chunking into groups of 4 (LE), zero-padding the last chunk. -/
def bytesToWords : List (BitVec 8) → List Word
  | [] => []
  | b :: bs => bytesToWordLE ((b :: bs).take 4) :: bytesToWords ((b :: bs).drop 4)
termination_by bytes => bytes.length
decreasing_by simp [List.length_drop]; omega

@[simp]
theorem bytesToWords_nil : bytesToWords [] = [] := by
  unfold bytesToWords; rfl

theorem bytesToWords_length (bytes : List (BitVec 8)) (h4 : 4 ∣ bytes.length) :
    (bytesToWords bytes).length * 4 = bytes.length := by
  match bytes with
  | [] => simp
  | b :: bs =>
    unfold bytesToWords
    simp only [List.length_cons, Nat.add_one]
    have hlen : (b :: bs).length ≥ 4 := by
      obtain ⟨k, hk⟩ := h4; simp [List.length_cons] at hk ⊢; omega
    have hdrop_len : ((b :: bs).drop 4).length = bs.length + 1 - 4 := by
      simp [List.length_drop]
    have hmod : 4 ∣ ((b :: bs).drop 4).length := by
      rw [hdrop_len]
      obtain ⟨k, hk⟩ := h4; simp [List.length_cons] at hk
      exact ⟨k - 1, by omega⟩
    have ih := bytesToWords_length _ hmod
    simp [List.length_cons] at hlen
    rw [hdrop_len] at ih; omega
termination_by bytes.length
decreasing_by simp [List.length_drop]; omega

namespace MachineState

-- Lemmas for reasoning about register file operations

/-- setReg does not affect the program counter. -/
@[simp]
theorem pc_setReg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).pc = s.pc := by
  cases r <;> rfl

/-- setMem does not affect the program counter. -/
@[simp]
theorem pc_setMem (s : MachineState) (a : Addr) (v : Word) :
    (s.setMem a v).pc = s.pc := by
  simp [setMem]

/-- setByte does not affect the program counter (delegates to setMem). -/
@[simp]
theorem pc_setByte (s : MachineState) (addr : Addr) (b : BitVec 8) :
    (s.setByte addr b).pc = s.pc := by
  simp [setByte]

/-- setHalfword does not affect the program counter (delegates to setMem). -/
@[simp]
theorem pc_setHalfword (s : MachineState) (addr : Addr) (h : BitVec 16) :
    (s.setHalfword addr h).pc = s.pc := by
  simp [setHalfword]

-- code field preservation through existing setters

@[simp]
theorem code_setReg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).code = s.code := by
  cases r <;> rfl

@[simp]
theorem code_setMem (s : MachineState) (a : Addr) (v : Word) :
    (s.setMem a v).code = s.code := by
  simp [setMem]

@[simp]
theorem code_setPC (s : MachineState) (v : Word) :
    (s.setPC v).code = s.code := by
  simp [setPC]

@[simp]
theorem code_setByte (s : MachineState) (addr : Addr) (b : BitVec 8) :
    (s.setByte addr b).code = s.code := by
  simp [setByte]

@[simp]
theorem code_setHalfword (s : MachineState) (addr : Addr) (h : BitVec 16) :
    (s.setHalfword addr h).code = s.code := by
  simp [setHalfword]

@[simp]
theorem code_appendCommit (s : MachineState) (a0 a1 : Word) :
    (s.appendCommit a0 a1).code = s.code := by
  simp [appendCommit]

@[simp]
theorem code_appendPublicValues (s : MachineState) (bytes : List (BitVec 8)) :
    (s.appendPublicValues bytes).code = s.code := by
  simp [appendPublicValues]

@[simp]
theorem code_writeWords (s : MachineState) (base : Addr) (words : List Word) :
    (s.writeWords base words).code = s.code := by
  induction words generalizing s base with
  | nil => rfl
  | cons w ws ih => simp [writeWords, ih]

@[simp]
theorem code_writeBytesAsWords (s : MachineState) (base : Addr) (bytes : List (BitVec 8)) :
    (s.writeBytesAsWords base bytes).code = s.code := by
  match bytes with
  | [] => unfold writeBytesAsWords; rfl
  | _ :: _ =>
    unfold writeBytesAsWords
    rw [code_writeBytesAsWords]
    simp
termination_by bytes.length
decreasing_by simp [List.length_drop]; omega

/-- setPC does not affect register reads. -/
@[simp]
theorem getReg_setPC (s : MachineState) (v : Word) (r : Reg) :
    (s.setPC v).getReg r = s.getReg r := by
  cases r <;> rfl

/-- Setting register r and reading register r' ≠ r gives the old value. -/
theorem getReg_setReg_ne (s : MachineState) (r r' : Reg) (v : Word)
    (h : r ≠ r') : (s.setReg r v).getReg r' = s.getReg r' := by
  cases r <;> cases r' <;> first | exact absurd rfl h | rfl

/-- Setting register r (≠ x0) and reading it back gives the new value. -/
theorem getReg_setReg_eq (s : MachineState) (r : Reg) (v : Word)
    (h : r ≠ .x0) : (s.setReg r v).getReg r = v := by
  cases r <;> first | exact absurd rfl h | rfl

-- Lemmas for reasoning about memory through state operations

@[simp] theorem getMem_setMem_eq (s : MachineState) (a : Addr) (v : Word) :
    (s.setMem a v).getMem a = v := by
  simp [getMem, setMem]

@[simp] theorem getMem_setMem_ne (s : MachineState) (a a' : Addr) (v : Word)
    (h : a' ≠ a) : (s.setMem a v).getMem a' = s.getMem a' := by
  simp [getMem, setMem, h]

@[simp] theorem getMem_setReg (s : MachineState) (r : Reg) (v : Word) (a : Addr) :
    (s.setReg r v).getMem a = s.getMem a := by
  cases r <;> simp [getMem, setReg]

@[simp] theorem getMem_setPC (s : MachineState) (v : Word) (a : Addr) :
    (s.setPC v).getMem a = s.getMem a := by
  simp [getMem, setPC]

-- Committed field preservation through existing setters

@[simp]
theorem committed_setReg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).committed = s.committed := by
  cases r <;> rfl

@[simp]
theorem committed_setMem (s : MachineState) (a : Addr) (v : Word) :
    (s.setMem a v).committed = s.committed := by
  simp [setMem]

@[simp]
theorem committed_setByte (s : MachineState) (addr : Addr) (b : BitVec 8) :
    (s.setByte addr b).committed = s.committed := by
  simp [setByte]

@[simp]
theorem committed_setHalfword (s : MachineState) (addr : Addr) (h : BitVec 16) :
    (s.setHalfword addr h).committed = s.committed := by
  simp [setHalfword]

@[simp]
theorem committed_setPC (s : MachineState) (v : Word) :
    (s.setPC v).committed = s.committed := by
  simp [setPC]

-- publicValues field preservation through existing setters

@[simp]
theorem publicValues_setReg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).publicValues = s.publicValues := by
  cases r <;> rfl

@[simp]
theorem publicValues_setMem (s : MachineState) (a : Addr) (v : Word) :
    (s.setMem a v).publicValues = s.publicValues := by
  simp [setMem]

@[simp]
theorem publicValues_setByte (s : MachineState) (addr : Addr) (b : BitVec 8) :
    (s.setByte addr b).publicValues = s.publicValues := by
  simp [setByte]

@[simp]
theorem publicValues_setHalfword (s : MachineState) (addr : Addr) (h : BitVec 16) :
    (s.setHalfword addr h).publicValues = s.publicValues := by
  simp [setHalfword]

@[simp]
theorem publicValues_setPC (s : MachineState) (v : Word) :
    (s.setPC v).publicValues = s.publicValues := by
  simp [setPC]

@[simp]
theorem publicValues_appendCommit (s : MachineState) (a0 a1 : Word) :
    (s.appendCommit a0 a1).publicValues = s.publicValues := by
  simp [appendCommit]

-- privateInput field preservation through existing setters

@[simp]
theorem privateInput_setReg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).privateInput = s.privateInput := by
  cases r <;> rfl

@[simp]
theorem privateInput_setMem (s : MachineState) (a : Addr) (v : Word) :
    (s.setMem a v).privateInput = s.privateInput := by
  simp [setMem]

@[simp]
theorem privateInput_setByte (s : MachineState) (addr : Addr) (b : BitVec 8) :
    (s.setByte addr b).privateInput = s.privateInput := by
  simp [setByte]

@[simp]
theorem privateInput_setHalfword (s : MachineState) (addr : Addr) (h : BitVec 16) :
    (s.setHalfword addr h).privateInput = s.privateInput := by
  simp [setHalfword]

@[simp]
theorem privateInput_setPC (s : MachineState) (v : Word) :
    (s.setPC v).privateInput = s.privateInput := by
  simp [setPC]

@[simp]
theorem privateInput_appendCommit (s : MachineState) (a0 a1 : Word) :
    (s.appendCommit a0 a1).privateInput = s.privateInput := by
  simp [appendCommit]

@[simp]
theorem privateInput_appendPublicValues (s : MachineState) (bytes : List (BitVec 8)) :
    (s.appendPublicValues bytes).privateInput = s.privateInput := by
  simp [appendPublicValues]

-- appendCommit preservation lemmas

@[simp]
theorem getReg_appendCommit (s : MachineState) (a0 a1 : Word) (r : Reg) :
    (s.appendCommit a0 a1).getReg r = s.getReg r := by
  cases r <;> rfl

@[simp]
theorem getMem_appendCommit (s : MachineState) (a0 a1 : Word) (a : Addr) :
    (s.appendCommit a0 a1).getMem a = s.getMem a := by
  simp [appendCommit, getMem]

@[simp]
theorem pc_appendCommit (s : MachineState) (a0 a1 : Word) :
    (s.appendCommit a0 a1).pc = s.pc := by
  simp [appendCommit]

@[simp]
theorem committed_appendCommit (s : MachineState) (a0 a1 : Word) :
    (s.appendCommit a0 a1).committed = s.committed ++ [(a0, a1)] := by
  simp [appendCommit]

-- appendPublicValues preservation lemmas

@[simp]
theorem getReg_appendPublicValues (s : MachineState) (bytes : List (BitVec 8)) (r : Reg) :
    (s.appendPublicValues bytes).getReg r = s.getReg r := by
  cases r <;> rfl

@[simp]
theorem getMem_appendPublicValues (s : MachineState) (bytes : List (BitVec 8)) (a : Addr) :
    (s.appendPublicValues bytes).getMem a = s.getMem a := by
  simp [appendPublicValues, getMem]

@[simp]
theorem pc_appendPublicValues (s : MachineState) (bytes : List (BitVec 8)) :
    (s.appendPublicValues bytes).pc = s.pc := by
  simp [appendPublicValues]

@[simp]
theorem committed_appendPublicValues (s : MachineState) (bytes : List (BitVec 8)) :
    (s.appendPublicValues bytes).committed = s.committed := by
  simp [appendPublicValues]

@[simp]
theorem publicValues_appendPublicValues (s : MachineState) (bytes : List (BitVec 8)) :
    (s.appendPublicValues bytes).publicValues = s.publicValues ++ bytes := by
  simp [appendPublicValues]

-- readWords simp lemmas

@[simp]
theorem readWords_zero (s : MachineState) (base : Addr) :
    s.readWords base 0 = [] := rfl

@[simp]
theorem readWords_succ (s : MachineState) (base : Addr) (n : Nat) :
    s.readWords base (n + 1) = s.getMem base :: s.readWords (base + 4) n := rfl

theorem readWords_length (s : MachineState) (base : Addr) (n : Nat) :
    (s.readWords base n).length = n := by
  induction n generalizing base with
  | zero => rfl
  | succ k ih => simp [readWords, ih]

-- writeWords simp lemmas

@[simp]
theorem writeWords_nil (s : MachineState) (base : Addr) :
    s.writeWords base [] = s := rfl

@[simp]
theorem writeWords_cons (s : MachineState) (base : Addr) (w : Word) (ws : List Word) :
    s.writeWords base (w :: ws) = (s.setMem base w).writeWords (base + 4) ws := rfl

-- writeWords preservation lemmas

@[simp]
theorem pc_writeWords (s : MachineState) (base : Addr) (words : List Word) :
    (s.writeWords base words).pc = s.pc := by
  induction words generalizing s base with
  | nil => rfl
  | cons w ws ih => simp [writeWords, ih]

@[simp]
theorem committed_writeWords (s : MachineState) (base : Addr) (words : List Word) :
    (s.writeWords base words).committed = s.committed := by
  induction words generalizing s base with
  | nil => rfl
  | cons w ws ih => simp [writeWords, ih]

@[simp]
theorem publicValues_writeWords (s : MachineState) (base : Addr) (words : List Word) :
    (s.writeWords base words).publicValues = s.publicValues := by
  induction words generalizing s base with
  | nil => rfl
  | cons w ws ih => simp [writeWords, ih]

@[simp]
theorem privateInput_writeWords (s : MachineState) (base : Addr) (words : List Word) :
    (s.writeWords base words).privateInput = s.privateInput := by
  induction words generalizing s base with
  | nil => rfl
  | cons w ws ih => simp [writeWords, ih]

@[simp]
theorem getReg_writeWords (s : MachineState) (base : Addr) (words : List Word) (r : Reg) :
    (s.writeWords base words).getReg r = s.getReg r := by
  induction words generalizing s base with
  | nil => rfl
  | cons w ws ih =>
    simp [writeWords, ih]
    cases r <;> simp [getReg, setMem]

-- readBytes simp lemmas

@[simp]
theorem readBytes_zero (s : MachineState) (base : Addr) :
    s.readBytes base 0 = [] := rfl

@[simp]
theorem readBytes_succ (s : MachineState) (base : Addr) (n : Nat) :
    s.readBytes base (n + 1) = s.getByte base :: s.readBytes (base + 1) n := rfl

-- writeBytesAsWords simp lemmas

@[simp]
theorem writeBytesAsWords_nil (s : MachineState) (base : Addr) :
    s.writeBytesAsWords base [] = s := by
  unfold writeBytesAsWords; rfl

-- writeBytesAsWords preservation lemmas

@[simp]
theorem pc_writeBytesAsWords (s : MachineState) (base : Addr) (bytes : List (BitVec 8)) :
    (s.writeBytesAsWords base bytes).pc = s.pc := by
  match bytes with
  | [] => unfold writeBytesAsWords; rfl
  | _ :: _ =>
    unfold writeBytesAsWords
    rw [pc_writeBytesAsWords]
    simp
termination_by bytes.length
decreasing_by simp [List.length_drop]; omega

@[simp]
theorem committed_writeBytesAsWords (s : MachineState) (base : Addr) (bytes : List (BitVec 8)) :
    (s.writeBytesAsWords base bytes).committed = s.committed := by
  match bytes with
  | [] => unfold writeBytesAsWords; rfl
  | _ :: _ =>
    unfold writeBytesAsWords
    rw [committed_writeBytesAsWords]
    simp
termination_by bytes.length
decreasing_by simp [List.length_drop]; omega

@[simp]
theorem publicValues_writeBytesAsWords (s : MachineState) (base : Addr) (bytes : List (BitVec 8)) :
    (s.writeBytesAsWords base bytes).publicValues = s.publicValues := by
  match bytes with
  | [] => unfold writeBytesAsWords; rfl
  | _ :: _ =>
    unfold writeBytesAsWords
    rw [publicValues_writeBytesAsWords]
    simp
termination_by bytes.length
decreasing_by simp [List.length_drop]; omega

@[simp]
theorem privateInput_writeBytesAsWords (s : MachineState) (base : Addr) (bytes : List (BitVec 8)) :
    (s.writeBytesAsWords base bytes).privateInput = s.privateInput := by
  match bytes with
  | [] => unfold writeBytesAsWords; rfl
  | _ :: _ =>
    unfold writeBytesAsWords
    rw [privateInput_writeBytesAsWords]
    simp
termination_by bytes.length
decreasing_by simp [List.length_drop]; omega

@[simp]
theorem getReg_writeBytesAsWords (s : MachineState) (base : Addr) (bytes : List (BitVec 8)) (r : Reg) :
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

end EvmAsm
