/-
  EvmAsm.Evm64.Push.Program

  256-bit EVM PUSH1..PUSH32: read `n` immediate bytes from the EVM code
  region, zero-extend them (right-aligned, big-endian) into a 256-bit
  EvmWord, push the result onto the EVM stack.

  Calling convention for PUSH (slice 2 of #101):
    x10  — EVM code pointer (pointing at the PUSHn opcode byte; the
           immediate bytes live at +1 .. +n)
    x12  — EVM stack pointer (decremented by 32 to allocate the new top
           slot, in line with the rest of the Evm64 opcode subroutines)
    x0   — hardwired zero, used by SD to zero the four limbs in one go
    x7   — temporary, holds the LBU'd byte before the SB

  The PC advance for `x10` is intentionally NOT added in this slice;
  the design note (`docs/push-opcode-design.md`) defers the EVM-level
  "PC advances by 1+n" claim to the spec slices (#101 slice 4).

  Total RISC-V instructions: 5 + 2 * n.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

module

public import EvmAsm.Rv64.Program
public import EvmAsm.Rv64.SepLogic

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Source byte offset for immediate byte `i` of a PUSHn instruction. The
    opcode itself is at offset 0, so immediates start at offset 1. -/
def pushByteSrcOffset (i : Nat) : Nat :=
  1 + i

/-- Destination byte offset in the newly allocated stack word for immediate
    byte `i` of PUSH width `n`. PUSH immediates are big-endian, while the
    stack word is stored little-endian in memory, so byte `i` lands at
    offset `n - 1 - i`. -/
def pushByteDstOffset (n i : Nat) : Nat :=
  n - 1 - i

theorem pushByteSrcOffset_pos (i : Nat) :
    0 < pushByteSrcOffset i := by
  unfold pushByteSrcOffset
  omega

theorem pushByteSrcOffset_le_32_of_lt {n i : Nat}
    (hn : n ≤ 32) (hi : i < n) :
    pushByteSrcOffset i ≤ 32 := by
  unfold pushByteSrcOffset
  omega

theorem pushByteDstOffset_lt_32_of_lt {n i : Nat}
    (hn : n ≤ 32) (hi : i < n) :
    pushByteDstOffset n i < 32 := by
  unfold pushByteDstOffset
  omega

theorem pushByteDstOffset_lt_width_of_lt {n i : Nat} (hi : i < n) :
    pushByteDstOffset n i < n := by
  unfold pushByteDstOffset
  omega

theorem pushByteOffsets_valid_of_lt {n i : Nat}
    (hn : n ≤ 32) (hi : i < n) :
    0 < pushByteSrcOffset i ∧
      pushByteSrcOffset i ≤ 32 ∧
      pushByteDstOffset n i < 32 ∧
      pushByteDstOffset n i < n := by
  exact ⟨pushByteSrcOffset_pos i,
    pushByteSrcOffset_le_32_of_lt hn hi,
    pushByteDstOffset_lt_32_of_lt hn hi,
    pushByteDstOffset_lt_width_of_lt hi⟩

/-- Read one immediate byte and store it into the new EVM stack slot.

    `n` is the PUSH width (1..32) and `i` is the byte index in
    `[0, n)` counted from the most-significant byte of the immediate.
    The big-endian semantics mean immediate byte `i` (which lives at
    `code[pc + 1 + i]`) is the byte at integer position `n - 1 - i`,
    so it goes into memory offset `n - 1 - i` from the new stack
    pointer (which holds limb 0's LSB at offset 0). -/
def push_one_byte (n i : Nat) : Program :=
  LBU .x7 .x10 (BitVec.ofNat 12 (pushByteSrcOffset i)) ;;
  SB .x12 .x7 (BitVec.ofNat 12 (pushByteDstOffset n i))

/-- Sequence `push_one_byte n 0 ;; push_one_byte n 1 ;; ... ;; push_one_byte n (k-1)`.

    Defined by recursion on `k` so `evm_push n` can be expressed for
    arbitrary symbolic `n` while keeping the per-byte block uniform. -/
def push_bytes (n : Nat) : Nat → Program
  | 0     => prog_skip
  | k + 1 => push_bytes n k ;; push_one_byte n k

theorem push_one_byte_length (n i : Nat) :
    (push_one_byte n i).length = 2 := by
  unfold push_one_byte LBU SB single seq
  rfl

theorem push_bytes_length (n k : Nat) :
    (push_bytes n k).length = 2 * k := by
  induction k with
  | zero =>
      unfold push_bytes prog_skip
      rfl
  | succ k ih =>
      unfold push_bytes
      unfold seq
      unfold Program at *
      rw [List.length_append, ih, push_one_byte_length]
      omega

theorem push_bytes_byte_slice (n k i : Nat) (hi : i < k) :
    ((push_bytes n k : List Instr).drop (2 * i)).take 2 =
      (push_one_byte n i : List Instr) := by
  induction k with
  | zero =>
      omega
  | succ k ih =>
      unfold push_bytes
      unfold seq
      by_cases h_i : i < k
      · unfold Program at *
        rw [List.drop_append]
        rw [push_bytes_length]
        rw [show 2 * i - 2 * k = 0 by omega]
        simp only [List.drop_zero]
        rw [List.take_append_of_le_length
          (l₁ := (push_bytes n k).drop (2 * i)) (l₂ := push_one_byte n k) (i := 2)
          (by
            rw [List.length_drop, push_bytes_length]
            omega)]
        exact ih h_i
      · have h_eq : i = k := by omega
        subst i
        unfold Program at *
        rw [List.drop_append]
        rw [push_bytes_length]
        rw [show 2 * k - 2 * k = 0 by omega]
        simp only [List.drop_zero]
        rw [show (push_bytes n k).drop (2 * k) = [] by
          exact List.drop_eq_nil_of_le (by rw [push_bytes_length]; omega)]
        simp only [List.nil_append]
        rw [List.take_of_length_le (by rw [push_one_byte_length]; omega)]

/-- Generic PUSHn program.

    Layout (5 + 2n instructions):
      1. `ADDI x12, x12, -32`       — allocate a new 32-byte stack slot
      2. four `SD x12, x0, 8*j`    — zero-fill the four 64-bit limbs
      3. n × (LBU + SB) pairs       — copy immediate bytes into place

    For PUSH1 through PUSH32 the offsets stay below 2^11, so the
    `BitVec.ofNat 12` casts in the helpers behave like the natural
    encoding (no sign-extension surprises). -/
def evm_push (n : Nat) : Program :=
  ADDI .x12 .x12 (-32) ;;
  SD .x12 .x0 0 ;; SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24 ;;
  push_bytes n n

theorem evm_push_length (n : Nat) :
    (evm_push n).length = 5 + 2 * n := by
  unfold evm_push ADDI SD single seq
  simp only [Program.length_append, List.length_cons, List.length_nil,
    push_bytes_length]
  omega

/-- The `i`th PUSH byte-copy pair is the two-instruction slice beginning at
    instruction offset `5 + 2 * i` of the generic `evm_push n` program. -/
theorem evm_push_byte_slice {n i : Nat} (hi : i < n) :
    ((evm_push n).drop (5 + 2 * i)).take 2 =
      (LBU .x7 .x10 (BitVec.ofNat 12 (pushByteSrcOffset i)) ;;
       SB .x12 .x7 (BitVec.ofNat 12 (pushByteDstOffset n i))) := by
  unfold evm_push ADDI SD single seq
  unfold Program at *
  simp only [List.singleton_append]
  rw [show 5 + 2 * i = Nat.succ (4 + 2 * i) by omega]
  simp only [List.drop_succ_cons]
  rw [show 4 + 2 * i = Nat.succ (3 + 2 * i) by omega]
  simp only [List.drop_succ_cons]
  rw [show 3 + 2 * i = Nat.succ (2 + 2 * i) by omega]
  simp only [List.drop_succ_cons]
  rw [show 2 + 2 * i = Nat.succ (1 + 2 * i) by omega]
  simp only [List.drop_succ_cons]
  rw [show 1 + 2 * i = Nat.succ (2 * i) by omega]
  simp only [List.drop_succ_cons]
  repeat rw [List.drop_succ_cons]
  rw [push_bytes_byte_slice n n i hi]
  unfold push_one_byte LBU SB single seq
  rfl

theorem evm_push1_length : (evm_push 1).length = 7 := by
  rw [evm_push_length]

theorem evm_push2_length : (evm_push 2).length = 9 := by
  rw [evm_push_length]

theorem evm_push32_length : (evm_push 32).length = 69 := by
  rw [evm_push_length]

/-- CodeReq for `evm_push n`.

    Symbolic `n` prevents `CodeReq.ofProg` from fully reducing, but for
    this slice (program-only) we only need a buildable definition. The
    spec slices (#101 slices 3-4) may refactor this into an explicit
    `CodeReq.singleton` union chain mirroring `evm_dup_code` if proofs
    require it. -/
abbrev evm_push_code (base : Word) (n : Nat) : CodeReq :=
  CodeReq.ofProg base (evm_push n)

/-- Concrete byte length of `evm_push n` when placed in RV64 code memory. -/
theorem evm_push_byte_length (n : Nat) :
    4 * (evm_push n).length = 20 + 8 * n := by
  rw [evm_push_length]
  omega

/-- Byte offset of the PUSH stack-slot allocation instruction. -/
theorem evm_push_alloc_byte_off : 4 * 0 = 0 := by
  rfl

/-- Byte offset of the first PUSH zero-fill store. -/
theorem evm_push_zero_limb0_store_byte_off : 4 * 1 = 4 := by
  rfl

/-- Byte offset of the second PUSH zero-fill store. -/
theorem evm_push_zero_limb1_store_byte_off : 4 * 2 = 8 := by
  rfl

/-- Byte offset of the third PUSH zero-fill store. -/
theorem evm_push_zero_limb2_store_byte_off : 4 * 3 = 12 := by
  rfl

/-- Byte offset of the fourth PUSH zero-fill store. -/
theorem evm_push_zero_limb3_store_byte_off : 4 * 4 = 16 := by
  rfl

/-- Byte offset of the LBU instruction for immediate byte `i`. -/
theorem evm_push_byte_lbu_byte_off (i : Nat) :
    4 * (5 + 2 * i) = 20 + 8 * i := by
  omega

/-- Byte offset of the SB instruction for immediate byte `i`. -/
theorem evm_push_byte_store_byte_off (i : Nat) :
    4 * (5 + 2 * i + 1) = 24 + 8 * i := by
  omega

/-- Byte offset immediately after the full PUSHn program. -/
theorem evm_push_end_byte_off (n : Nat) :
    4 * (5 + 2 * n) = 20 + 8 * n := by
  omega

end EvmAsm.Evm64
