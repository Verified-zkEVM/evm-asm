/-
  EvmAsm.Evm64.Push.Spec

  Specs for the EVM PUSH1..PUSH32 opcode family. Three-level architecture
  per `docs/push-opcode-design.md`:

    1. Per-byte helper:        `push_one_byte_spec_within` (this file)
    2. Generic n-byte spec:    (slice 4)
    3. EvmWord/stack spec:     (slice 4 / slice 5)

  This sub-slice (#101 sub-slice, parent evm-asm-ou3t) lands only the
  level-1 building block: the 2-instruction LBU+SB pair that copies one
  byte from the EVM code region (at `codePtr + codeOff`) into the new
  stack slot (at `sp + dstOff`).

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.Push.Program
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Stack slot allocation and zero-fill prefix
-- ============================================================================

def push_zero_slot_code (base : Word) : CodeReq :=
  (CodeReq.singleton base (.ADDI .x12 .x12 (-32))).union
    ((CodeReq.singleton (base + 4) (.SD .x12 .x0 0)).union
      ((CodeReq.singleton (base + 8) (.SD .x12 .x0 8)).union
        ((CodeReq.singleton (base + 12) (.SD .x12 .x0 16)).union
          (CodeReq.singleton (base + 16) (.SD .x12 .x0 24)))))

theorem push_zero_slot_code_eq_ofProg (base : Word) :
    push_zero_slot_code base =
      CodeReq.ofProg base
        (ADDI .x12 .x12 (-32) ;; SD .x12 .x0 0 ;; SD .x12 .x0 8 ;;
         SD .x12 .x0 16 ;; SD .x12 .x0 24) := by
  unfold push_zero_slot_code ADDI SD single seq
  change _ = CodeReq.ofProg base
    [.ADDI .x12 .x12 (-32), .SD .x12 .x0 0, .SD .x12 .x0 8,
     .SD .x12 .x0 16, .SD .x12 .x0 24]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  bv_addr

theorem push_zero_slot_spec_within
    (sp d0 d1 d2 d3 : Word) (base : Word) :
    let nsp := sp + signExtend12 ((-32 : BitVec 12))
    cpsTripleWithin 5 base (base + 20) (push_zero_slot_code base)
      ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       ((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x12 ↦ᵣ nsp) ** (.x0 ↦ᵣ (0 : Word)) **
       ((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word))) := by
  intro nsp
  unfold push_zero_slot_code
  have hAlloc := addi_spec_gen_same_within .x12 sp
    (-32 : BitVec 12) base (by decide)
  have hSd0 := generic_sd_spec_within .x12 .x0 nsp (0 : Word) d0
    (0 : BitVec 12) (base + 4)
  have hSd1 := generic_sd_spec_within .x12 .x0 nsp (0 : Word) d1
    (8 : BitVec 12) (base + 8)
  have hSd2 := generic_sd_spec_within .x12 .x0 nsp (0 : Word) d2
    (16 : BitVec 12) (base + 12)
  have hSd3 := generic_sd_spec_within .x12 .x0 nsp (0 : Word) d3
    (24 : BitVec 12) (base + 16)
  runBlock hAlloc hSd0 hSd1 hSd2 hSd3

theorem push_zero_slot_ofProg_spec_within
    (sp d0 d1 d2 d3 : Word) (base : Word) :
    let nsp := sp + signExtend12 ((-32 : BitVec 12))
    cpsTripleWithin 5 base (base + 20)
      (CodeReq.ofProg base
        (ADDI .x12 .x12 (-32) ;; SD .x12 .x0 0 ;; SD .x12 .x0 8 ;;
         SD .x12 .x0 16 ;; SD .x12 .x0 24))
      ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       ((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x12 ↦ᵣ nsp) ** (.x0 ↦ᵣ (0 : Word)) **
       ((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word))) := by
  intro nsp
  rw [← push_zero_slot_code_eq_ofProg]
  exact push_zero_slot_spec_within sp d0 d1 d2 d3 base

theorem evm_push_zero_slot_code_spec_within
    (n : Nat) (hn : n ≤ 32) (sp d0 d1 d2 d3 : Word) (base : Word) :
    let nsp := sp + signExtend12 ((-32 : BitVec 12))
    cpsTripleWithin 5 base (base + 20) (evm_push_code base n)
      ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       ((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x12 ↦ᵣ nsp) ** (.x0 ↦ᵣ (0 : Word)) **
       ((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word))) := by
  intro nsp
  have hPrefix := push_zero_slot_ofProg_spec_within sp d0 d1 d2 d3 base
  exact cpsTripleWithin_extend_code (h := hPrefix) (hmono := by
    unfold evm_push_code
    exact CodeReq.ofProg_mono_sub base base (evm_push n)
      (ADDI .x12 .x12 (-32) ;; SD .x12 .x0 0 ;; SD .x12 .x0 8 ;;
       SD .x12 .x0 16 ;; SD .x12 .x0 24) 0
      (by bv_omega)
      (by
        unfold evm_push ADDI SD single seq
        rfl)
      (by
        change 0 + 5 ≤ (evm_push n).length
        rw [evm_push_length]
        omega)
      (by
        rw [evm_push_length]
        omega))

/-- The four zero-filled limbs written by the PUSH allocation prefix fold to
    the EVM word value `0`. -/
theorem push_zero_slot_word_zero (nsp : Word) :
    (((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word))) =
    evmWordIs nsp (0 : EvmWord) := by
  have h0 : (nsp + signExtend12 (0 : BitVec 12) : Word) = nsp := by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega
  have h8 : (nsp + signExtend12 (8 : BitVec 12) : Word) = nsp + 8 := by congr 1
  have h16 : (nsp + signExtend12 (16 : BitVec 12) : Word) = nsp + 16 := by congr 1
  have h24 : (nsp + signExtend12 (24 : BitVec 12) : Word) = nsp + 24 := by congr 1
  rw [h0, h8, h16, h24, evmWordIs_zero]

/-- Right-associated variant of `push_zero_slot_word_zero` for composing byte
    copy postconditions after the zero-fill prefix. -/
theorem push_zero_slot_word_zero_right (nsp : Word) (Q : Assertion) :
    (((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) ** Q) =
    (evmWordIs nsp (0 : EvmWord) ** Q) := by
  have h0 : (nsp + signExtend12 (0 : BitVec 12) : Word) = nsp := by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega
  have h8 : (nsp + signExtend12 (8 : BitVec 12) : Word) = nsp + 8 := by
    congr 1
  have h16 : (nsp + signExtend12 (16 : BitVec 12) : Word) = nsp + 16 := by
    congr 1
  have h24 : (nsp + signExtend12 (24 : BitVec 12) : Word) = nsp + 24 := by
    congr 1
  rw [h0, h8, h16, h24]
  rw [evmWordIs_zero_right]

/-- Stack-shaped bridge for the generic PUSH allocation prefix: the first five
    instructions of `evm_push n` allocate a slot, zero-fill it, and expose the
    new top as `evmWordIs nsp 0` while framing the previous stack tail. -/
theorem evm_push_zero_slot_stack_spec_within
    (n : Nat) (hn : n ≤ 32) (sp d0 d1 d2 d3 : Word) (base : Word)
    (rest : List EvmWord) :
    let nsp := sp + signExtend12 ((-32 : BitVec 12))
    cpsTripleWithin 5 base (base + 20) (evm_push_code base n)
      ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       ((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       evmStackIs sp rest)
      ((.x12 ↦ᵣ nsp) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs nsp (0 : EvmWord) **
       evmStackIs sp rest) := by
  intro nsp
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      rw [← push_zero_slot_word_zero nsp]
      xperm_hyp hq)
    (cpsTripleWithin_frameR
      (evmStackIs sp rest)
      pcFree_evmStackIs
      (evm_push_zero_slot_code_spec_within n hn sp d0 d1 d2 d3 base))

/-- Stack-list variant of the generic PUSH allocation prefix: after the
    zero-filled slot is allocated, the new top of stack is the word `0`
    followed by the previous stack tail. -/
theorem evm_push_zero_slot_full_stack_spec_within
    (n : Nat) (hn : n ≤ 32) (sp d0 d1 d2 d3 : Word) (base : Word)
    (rest : List EvmWord) :
    let nsp := sp + signExtend12 ((-32 : BitVec 12))
    cpsTripleWithin 5 base (base + 20) (evm_push_code base n)
      ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       ((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       evmStackIs sp rest)
      ((.x12 ↦ᵣ nsp) ** (.x0 ↦ᵣ (0 : Word)) **
       evmStackIs nsp ((0 : EvmWord) :: rest)) := by
  intro nsp
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hq => by
      rw [evmStackIs_cons]
      rw [show (nsp + 32 : Word) = sp from by
        change (sp + signExtend12 ((-32 : BitVec 12)) + 32 : Word) = sp
        rw [show signExtend12 ((-32 : BitVec 12)) = (-32 : Word) from by decide]
        bv_omega]
      xperm_hyp hq)
    (evm_push_zero_slot_stack_spec_within n hn sp d0 d1 d2 d3 base rest)

-- ============================================================================
-- Semantic immediate word assembled by PUSH byte stores
-- ============================================================================

/-- Fold the immediate bytes copied by `evm_push n` into one stack limb.

    The executable code starts from a zero-filled 32-byte slot. For each
    immediate byte `i`, `pushByteDstOffset n i` gives the byte position in the
    new stack word; if that byte lies in `limb`, replay the corresponding
    `replaceByte`, otherwise leave the limb unchanged. -/
def pushImmediateLimb (n : Nat) (byteAt : Nat → BitVec 8) (limb : Nat) : Word :=
  (List.range n).foldl
    (fun acc i =>
      let dst := pushByteDstOffset n i
      if dst / 8 = limb then
        replaceByte acc (dst % 8) (byteAt i)
      else
        acc)
    (0 : Word)

/-- The semantic EVM word assembled by PUSH immediate bytes, starting from the
    zero-filled slot and replaying the generic byte-copy layout. -/
def pushImmediateWord (n : Nat) (byteAt : Nat → BitVec 8) : EvmWord :=
  EvmWord.fromLimbs fun
    | ⟨0, _⟩ => pushImmediateLimb n byteAt 0
    | ⟨1, _⟩ => pushImmediateLimb n byteAt 1
    | ⟨2, _⟩ => pushImmediateLimb n byteAt 2
    | ⟨3, _⟩ => pushImmediateLimb n byteAt 3

theorem pushImmediateWord_getLimbN_0 (n : Nat) (byteAt : Nat → BitVec 8) :
    (pushImmediateWord n byteAt).getLimbN 0 =
      pushImmediateLimb n byteAt 0 := by
  unfold pushImmediateWord
  rw [EvmWord.getLimbN_lt _ _ (by decide), EvmWord.getLimb_fromLimbs]

theorem pushImmediateWord_getLimbN_1 (n : Nat) (byteAt : Nat → BitVec 8) :
    (pushImmediateWord n byteAt).getLimbN 1 =
      pushImmediateLimb n byteAt 1 := by
  unfold pushImmediateWord
  rw [EvmWord.getLimbN_lt _ _ (by decide), EvmWord.getLimb_fromLimbs]

theorem pushImmediateWord_getLimbN_2 (n : Nat) (byteAt : Nat → BitVec 8) :
    (pushImmediateWord n byteAt).getLimbN 2 =
      pushImmediateLimb n byteAt 2 := by
  unfold pushImmediateWord
  rw [EvmWord.getLimbN_lt _ _ (by decide), EvmWord.getLimb_fromLimbs]

theorem pushImmediateWord_getLimbN_3 (n : Nat) (byteAt : Nat → BitVec 8) :
    (pushImmediateWord n byteAt).getLimbN 3 =
      pushImmediateLimb n byteAt 3 := by
  unfold pushImmediateWord
  rw [EvmWord.getLimbN_lt _ _ (by decide), EvmWord.getLimb_fromLimbs]

/-- Fold the four executable PUSH destination limbs into the compact semantic
    word assembled from the immediate byte stream. -/
theorem pushImmediateWord_evmWordIs_fold
    (sp : Word) (n : Nat) (byteAt : Nat → BitVec 8) :
    ((sp ↦ₘ pushImmediateLimb n byteAt 0) **
      ((sp + 8) ↦ₘ pushImmediateLimb n byteAt 1) **
      ((sp + 16) ↦ₘ pushImmediateLimb n byteAt 2) **
      ((sp + 24) ↦ₘ pushImmediateLimb n byteAt 3)) =
    evmWordIs sp (pushImmediateWord n byteAt) := by
  rw [evmWordIs_sp_limbs_eq sp (pushImmediateWord n byteAt)
    (pushImmediateLimb n byteAt 0)
    (pushImmediateLimb n byteAt 1)
    (pushImmediateLimb n byteAt 2)
    (pushImmediateLimb n byteAt 3)
    (pushImmediateWord_getLimbN_0 n byteAt)
    (pushImmediateWord_getLimbN_1 n byteAt)
    (pushImmediateWord_getLimbN_2 n byteAt)
    (pushImmediateWord_getLimbN_3 n byteAt)]

/-- Fold the generic PUSH immediate result limbs and existing tail stack into
    the stack-list shape used by the final `evm_push_n_stack_spec`. -/
theorem pushImmediateWord_evmStackIs_fold
    (sp : Word) (n : Nat) (byteAt : Nat → BitVec 8) (rest : List EvmWord) :
    (((sp ↦ₘ pushImmediateLimb n byteAt 0) **
      ((sp + 8) ↦ₘ pushImmediateLimb n byteAt 1) **
      ((sp + 16) ↦ₘ pushImmediateLimb n byteAt 2) **
      ((sp + 24) ↦ₘ pushImmediateLimb n byteAt 3)) **
      evmStackIs (sp + 32) rest) =
    evmStackIs sp (pushImmediateWord n byteAt :: rest) := by
  rw [pushImmediateWord_evmWordIs_fold]
  rfl

-- ============================================================================
-- Per-byte helper (mirror of `dup_pair_spec_within` for LBU+SB)
-- ============================================================================

theorem push_one_byte_code_eq_ofProg
    (base : Word) (codeOff dstOff : BitVec 12) :
    ((CodeReq.singleton base (.LBU .x7 .x10 codeOff)).union
      (CodeReq.singleton (base + 4) (.SB .x12 .x7 dstOff))) =
    CodeReq.ofProg base
      (LBU .x7 .x10 codeOff ;; SB .x12 .x7 dstOff) := by
  unfold LBU SB single seq
  change _ =
    CodeReq.ofProg base
      [.LBU .x7 .x10 codeOff, .SB .x12 .x7 dstOff]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_singleton]

/-- Two-instruction spec for one PUSH byte: LBU x7 from EVM code at
    `codePtr + codeOff`, then SB x7 to the new stack slot at
    `sp + dstOff`.

    `codeDwordAddr` / `dstDwordAddr` are the `alignToDword` of the source
    and destination byte addresses (in general distinct). Both bytes must
    satisfy the byte-validity precondition. The post records that `x7`
    holds the freshly-loaded byte (zero-extended to 64 bits) and that the
    destination doubleword has had its target byte replaced. -/
theorem push_one_byte_spec_within
    (codePtr sp v7Old codeWord dstWordOld : Word)
    (codeDwordAddr dstDwordAddr : Word)
    (codeOff dstOff : BitVec 12) (base : Word)
    (h_code_align : alignToDword (codePtr + signExtend12 codeOff) = codeDwordAddr)
    (h_code_valid : isValidByteAccess (codePtr + signExtend12 codeOff) = true)
    (h_dst_align  : alignToDword (sp + signExtend12 dstOff) = dstDwordAddr)
    (h_dst_valid  : isValidByteAccess (sp + signExtend12 dstOff) = true) :
    let byteZext :=
      (extractByte codeWord (byteOffset (codePtr + signExtend12 codeOff))).zeroExtend 64
    cpsTripleWithin 2 base (base + 8)
      ((CodeReq.singleton base (.LBU .x7 .x10 codeOff)).union
        (CodeReq.singleton (base + 4) (.SB .x12 .x7 dstOff)))
      ((.x10 ↦ᵣ codePtr) ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7Old) **
       (codeDwordAddr ↦ₘ codeWord) ** (dstDwordAddr ↦ₘ dstWordOld))
      ((.x10 ↦ᵣ codePtr) ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ byteZext) **
       (codeDwordAddr ↦ₘ codeWord) **
       (dstDwordAddr ↦ₘ
         replaceByte dstWordOld (byteOffset (sp + signExtend12 dstOff))
           (byteZext.truncate 8))) := by
  intro byteZext
  have L := lbu_spec_gen_within .x7 .x10 codePtr v7Old codeOff base
    codeDwordAddr codeWord (by nofun) h_code_align h_code_valid
  have S := sb_spec_gen_within .x12 .x7 sp byteZext dstOff (base + 4)
    dstDwordAddr dstWordOld h_dst_align h_dst_valid
  runBlock L S

theorem push_one_byte_ofProg_spec_within
    (codePtr sp v7Old codeWord dstWordOld : Word)
    (codeDwordAddr dstDwordAddr : Word)
    (codeOff dstOff : BitVec 12) (base : Word)
    (h_code_align : alignToDword (codePtr + signExtend12 codeOff) = codeDwordAddr)
    (h_code_valid : isValidByteAccess (codePtr + signExtend12 codeOff) = true)
    (h_dst_align  : alignToDword (sp + signExtend12 dstOff) = dstDwordAddr)
    (h_dst_valid  : isValidByteAccess (sp + signExtend12 dstOff) = true) :
    let byteZext :=
      (extractByte codeWord (byteOffset (codePtr + signExtend12 codeOff))).zeroExtend 64
    cpsTripleWithin 2 base (base + 8)
      (CodeReq.ofProg base (LBU .x7 .x10 codeOff ;; SB .x12 .x7 dstOff))
      ((.x10 ↦ᵣ codePtr) ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7Old) **
       (codeDwordAddr ↦ₘ codeWord) ** (dstDwordAddr ↦ₘ dstWordOld))
      ((.x10 ↦ᵣ codePtr) ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ byteZext) **
       (codeDwordAddr ↦ₘ codeWord) **
       (dstDwordAddr ↦ₘ
         replaceByte dstWordOld (byteOffset (sp + signExtend12 dstOff))
           (byteZext.truncate 8))) := by
  intro byteZext
  rw [← push_one_byte_code_eq_ofProg]
  exact push_one_byte_spec_within codePtr sp v7Old codeWord dstWordOld
    codeDwordAddr dstDwordAddr codeOff dstOff base
    h_code_align h_code_valid h_dst_align h_dst_valid

@[irreducible]
def pushOneBytePost
    (codePtr sp codeWord dstWordOld : Word)
    (codeDwordAddr dstDwordAddr : Word)
    (codeOff dstOff : BitVec 12) : Assertion :=
  let byteZext :=
    (extractByte codeWord (byteOffset (codePtr + signExtend12 codeOff))).zeroExtend 64
  ((.x10 ↦ᵣ codePtr) ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ byteZext) **
   (codeDwordAddr ↦ₘ codeWord) **
   (dstDwordAddr ↦ₘ
     replaceByte dstWordOld (byteOffset (sp + signExtend12 dstOff))
       (byteZext.truncate 8)))

theorem pushOneBytePost_unfold
    (codePtr sp codeWord dstWordOld : Word)
    (codeDwordAddr dstDwordAddr : Word)
    (codeOff dstOff : BitVec 12) :
    pushOneBytePost codePtr sp codeWord dstWordOld codeDwordAddr dstDwordAddr
      codeOff dstOff =
    (let byteZext :=
      (extractByte codeWord (byteOffset (codePtr + signExtend12 codeOff))).zeroExtend 64
    ((.x10 ↦ᵣ codePtr) ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ byteZext) **
     (codeDwordAddr ↦ₘ codeWord) **
     (dstDwordAddr ↦ₘ
       replaceByte dstWordOld (byteOffset (sp + signExtend12 dstOff))
         (byteZext.truncate 8)))) := by
  delta pushOneBytePost
  rfl

theorem push_one_byte_ofProg_named_spec_within
    (codePtr sp v7Old codeWord dstWordOld : Word)
    (codeDwordAddr dstDwordAddr : Word)
    (codeOff dstOff : BitVec 12) (base : Word)
    (h_code_align : alignToDword (codePtr + signExtend12 codeOff) = codeDwordAddr)
    (h_code_valid : isValidByteAccess (codePtr + signExtend12 codeOff) = true)
    (h_dst_align  : alignToDword (sp + signExtend12 dstOff) = dstDwordAddr)
    (h_dst_valid  : isValidByteAccess (sp + signExtend12 dstOff) = true) :
    cpsTripleWithin 2 base (base + 8)
      (CodeReq.ofProg base (LBU .x7 .x10 codeOff ;; SB .x12 .x7 dstOff))
      ((.x10 ↦ᵣ codePtr) ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7Old) **
       (codeDwordAddr ↦ₘ codeWord) ** (dstDwordAddr ↦ₘ dstWordOld))
      (pushOneBytePost codePtr sp codeWord dstWordOld codeDwordAddr dstDwordAddr
        codeOff dstOff) :=
  cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by rw [pushOneBytePost_unfold]; exact hp)
    (push_one_byte_ofProg_spec_within codePtr sp v7Old codeWord dstWordOld
      codeDwordAddr dstDwordAddr codeOff dstOff base
      h_code_align h_code_valid h_dst_align h_dst_valid)

@[irreducible]
def evmPushOneBytePost
    (n i : Nat) (codePtr sp codeWord dstWordOld : Word)
    (codeDwordAddr dstDwordAddr : Word) : Assertion :=
  let codeOff := BitVec.ofNat 12 (pushByteSrcOffset i)
  let dstOff := BitVec.ofNat 12 (pushByteDstOffset n i)
  let byteZext :=
    (extractByte codeWord (byteOffset (codePtr + signExtend12 codeOff))).zeroExtend 64
  ((.x10 ↦ᵣ codePtr) ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ byteZext) **
   (codeDwordAddr ↦ₘ codeWord) **
   (dstDwordAddr ↦ₘ
     replaceByte dstWordOld (byteOffset (sp + signExtend12 dstOff))
       (byteZext.truncate 8)))

theorem evmPushOneBytePost_unfold
    (n i : Nat) (codePtr sp codeWord dstWordOld : Word)
    (codeDwordAddr dstDwordAddr : Word) :
    evmPushOneBytePost n i codePtr sp codeWord dstWordOld
      codeDwordAddr dstDwordAddr =
    let codeOff := BitVec.ofNat 12 (pushByteSrcOffset i)
    let dstOff := BitVec.ofNat 12 (pushByteDstOffset n i)
    let byteZext :=
      (extractByte codeWord (byteOffset (codePtr + signExtend12 codeOff))).zeroExtend 64
    ((.x10 ↦ᵣ codePtr) ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ byteZext) **
     (codeDwordAddr ↦ₘ codeWord) **
     (dstDwordAddr ↦ₘ
       replaceByte dstWordOld (byteOffset (sp + signExtend12 dstOff))
         (byteZext.truncate 8))) := by
  delta evmPushOneBytePost
  rfl

/-- Lift the one-byte PUSH copy spec under the full generic `evm_push n`
    program for any byte index `i < n`. -/
theorem evm_push_one_byte_spec_within
    (n i : Nat) (hn : n ≤ 32) (hi : i < n)
    (codePtr sp v7Old codeWord dstWordOld : Word)
    (codeDwordAddr dstDwordAddr : Word) (base : Word)
    (h_code_align :
      alignToDword
        (codePtr + signExtend12 (BitVec.ofNat 12 (pushByteSrcOffset i))) =
          codeDwordAddr)
    (h_code_valid :
      isValidByteAccess
        (codePtr + signExtend12 (BitVec.ofNat 12 (pushByteSrcOffset i))) = true)
    (h_dst_align :
      alignToDword
        (sp + signExtend12 (BitVec.ofNat 12 (pushByteDstOffset n i))) =
          dstDwordAddr)
    (h_dst_valid :
      isValidByteAccess
        (sp + signExtend12 (BitVec.ofNat 12 (pushByteDstOffset n i))) = true) :
    cpsTripleWithin 2 (base + BitVec.ofNat 64 (4 * (5 + 2 * i)))
      ((base + BitVec.ofNat 64 (4 * (5 + 2 * i))) + 8)
      (evm_push_code base n)
      ((.x10 ↦ᵣ codePtr) ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7Old) **
       (codeDwordAddr ↦ₘ codeWord) ** (dstDwordAddr ↦ₘ dstWordOld))
      (evmPushOneBytePost n i codePtr sp codeWord dstWordOld
        codeDwordAddr dstDwordAddr) := by
  let codeOff := BitVec.ofNat 12 (pushByteSrcOffset i)
  let dstOff := BitVec.ofNat 12 (pushByteDstOffset n i)
  let subBase := base + BitVec.ofNat 64 (4 * (5 + 2 * i))
  have hByte := push_one_byte_ofProg_spec_within
    codePtr sp v7Old codeWord dstWordOld codeDwordAddr dstDwordAddr
    codeOff dstOff subBase h_code_align h_code_valid h_dst_align h_dst_valid
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by
      rw [evmPushOneBytePost_unfold]
      exact hp)
    (cpsTripleWithin_extend_code (h := hByte) (hmono := by
      unfold evm_push_code
      exact CodeReq.ofProg_mono_sub base subBase (evm_push n)
        (LBU .x7 .x10 codeOff ;; SB .x12 .x7 dstOff) (5 + 2 * i)
        (by rfl)
        (by
          have hlen :
              (LBU .x7 .x10 codeOff ;; SB .x12 .x7 dstOff).length = 2 := by
            unfold LBU SB single seq
            rfl
          rw [hlen]
          change ((evm_push n).drop (5 + 2 * i)).take 2 =
            (LBU .x7 .x10 (BitVec.ofNat 12 (pushByteSrcOffset i)) ;;
             SB .x12 .x7 (BitVec.ofNat 12 (pushByteDstOffset n i)))
          rw [evm_push_byte_slice hi])
        (by
          rw [evm_push_length]
          unfold LBU SB single seq
          simp only [Program.length_append, List.length_cons, List.length_nil]
          omega)
        (by
          rw [evm_push_length]
          omega)))

-- ============================================================================
-- PUSH1 complete stack spec (bead evm-asm-f0f5.11)
-- ============================================================================

/-- PUSH1 cpsTripleWithin spec: 7 instructions that push a concrete byte value
    onto the EVM stack. Composed from zero-slot (5 instrs) + byte-copy (2 instrs).

    The `byteVal` parameter makes the postcondition fully concrete, avoiding
    form-matching issues with abstract `byteAt` functions.

    `h_dst_align` encodes that `nsp = sp - 32` is 8-byte aligned:
    `alignToDword (nsp + signExtend12 0) = nsp`. -/
theorem evm_push1_stack_spec_within
    (sp codePtr v7Old d0 d1 d2 d3 codeWord codeDwordAddr : Word)
    (base : Word) (rest : List EvmWord)
    (byteVal : BitVec 8)
    (h_byte : extractByte codeWord
        (byteOffset (codePtr + signExtend12 (BitVec.ofNat 12 (pushByteSrcOffset 0)))) = byteVal)
    (h_code_align :
      alignToDword (codePtr + signExtend12 (BitVec.ofNat 12 (pushByteSrcOffset 0))) = codeDwordAddr)
    (h_code_valid :
      isValidByteAccess (codePtr + signExtend12 (BitVec.ofNat 12 (pushByteSrcOffset 0))) = true)
    (h_dst_align :
      alignToDword (sp + signExtend12 ((-32 : BitVec 12)) +
        signExtend12 (BitVec.ofNat 12 (pushByteDstOffset 1 0))) =
        sp + signExtend12 ((-32 : BitVec 12)))
    (h_dst_valid :
      isValidByteAccess (sp + signExtend12 ((-32 : BitVec 12)) +
        signExtend12 (BitVec.ofNat 12 (pushByteDstOffset 1 0))) = true) :
    let nsp := sp + signExtend12 ((-32 : BitVec 12))
    cpsTripleWithin 7 base (base + 28) (evm_push_code base 1)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ codePtr) ** (.x7 ↦ᵣ v7Old) **
       (.x0 ↦ᵣ (0 : Word)) **
       ((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       (codeDwordAddr ↦ₘ codeWord) ** evmStackIs sp rest)
      ((.x12 ↦ᵣ nsp) ** (.x10 ↦ᵣ codePtr) **
       (.x7 ↦ᵣ byteVal.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
       (codeDwordAddr ↦ₘ codeWord) **
       evmStackIs nsp (pushImmediateWord 1 (fun _ => byteVal) :: rest)) := by
  intro nsp
  -- Address normalization helpers
  have h8  : (nsp + signExtend12 (8  : BitVec 12) : Word) = nsp + 8  := by congr 1
  have h16 : (nsp + signExtend12 (16 : BitVec 12) : Word) = nsp + 16 := by congr 1
  have h24 : (nsp + signExtend12 (24 : BitVec 12) : Word) = nsp + 24 := by congr 1
  have h32 : (nsp + 32 : Word) = sp := by
    change (sp + signExtend12 ((-32 : BitVec 12)) + 32 : Word) = sp
    rw [show signExtend12 ((-32 : BitVec 12)) = (-32 : Word) from by decide]; bv_omega
  -- The dst byte offset within nsp is 0 (nsp is 8-byte aligned)
  have h_dstOff_zero : byteOffset (nsp + signExtend12 (BitVec.ofNat 12 (pushByteDstOffset 1 0))) = 0 := by
    -- All concrete parts: pushByteDstOffset 1 0 = 0, signExtend12 0 = 0
    have hse : signExtend12 (BitVec.ofNat 12 (pushByteDstOffset 1 0)) = (0 : Word) := by
      unfold signExtend12 pushByteDstOffset; decide
    -- Derive: nsp &&& ~~~7 = nsp from h_dst_align
    have hdst : nsp &&& ~~~(7 : Word) = nsp := by
      have := h_dst_align
      rw [hse] at this
      unfold alignToDword at this
      simpa using this
    -- Derive: nsp &&& 7 = 0 from hdst
    have h7 : nsp &&& (7 : Word) = 0 :=
      calc nsp &&& (7 : Word)
          = (nsp &&& ~~~(7 : Word)) &&& (7 : Word) := by rw [hdst]
        _ = nsp &&& (~~~(7 : Word) &&& (7 : Word)) := BitVec.and_assoc _ _ _
        _ = nsp &&& 0 := by rw [show ~~~(7 : Word) &&& (7 : Word) = 0 from by decide]
        _ = 0 := by simp [BitVec.and_zero]
    -- Conclude byteOffset (nsp + 0) = 0
    simp only [byteOffset]
    rw [hse]
    simp only [show (0:Word) = 0#64 from rfl]
    rw [BitVec.add_zero]
    rw [show nsp &&& 7#64 = 0 from by rw [show 7#64 = (7:Word) from rfl]; exact h7]
    rfl
  -- Zero-slot spec, framed with x10, x7, codeDword
  have hZero := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ codePtr) ** (.x7 ↦ᵣ v7Old) ** (codeDwordAddr ↦ₘ codeWord))
    (by pcFree)
    (evm_push_zero_slot_full_stack_spec_within 1 (by decide) sp d0 d1 d2 d3 base rest)
  -- Byte-copy spec (n=1, i=0, dstDword=nsp, dstWordOld=0)
  have hByte_raw := evm_push_one_byte_spec_within 1 0 (by decide) (by decide)
    codePtr nsp v7Old codeWord 0 codeDwordAddr nsp base
    h_code_align h_code_valid h_dst_align h_dst_valid
  -- Frame byte-copy with the remaining zero limbs + rest
  have hByte := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     ((nsp + 8) ↦ₘ (0 : Word)) ** ((nsp + 16) ↦ₘ (0 : Word)) **
     ((nsp + 24) ↦ₘ (0 : Word)) ** evmStackIs (nsp + 32) rest)
    (by pcFree)
    hByte_raw
  -- Compose zero-slot + byte-copy via seq, with bridging built into the weaken
  have hSeq := cpsTripleWithin_seq_same_cr hZero
    (cpsTripleWithin_weaken
      (fun _ hp => by
        -- hp : hZero.POST s — uses sp + signExtend12 (-32) form; fold to nsp
        rw [evmStackIs_cons, evmWordIs_zero] at hp
        rw [show sp + signExtend12 (-32) = nsp from rfl] at hp
        xperm_hyp hp)
      (fun _ hp => hp)
      hByte)
  -- Normalize hSeq's exit: base + 20 + 8 = base + 28 (BitVec add not definitional with free base)
  have h_exit : base + BitVec.ofNat 64 (4 * (5 + 2 * 0)) + 8 = (base + 28 : Word) := by
    simp only [show BitVec.ofNat 64 (4 * (5 + 2 * 0)) = (20 : Word) from rfl,
               BitVec.add_assoc,
               show (20 : Word) + 8 = 28 from rfl]
  rw [h_exit] at hSeq
  -- Weaken to fold POST into evmStackIs with pushImmediateWord.
  -- Use refine so that ?P' is resolved from the outer goal before proof scripts run.
  refine cpsTripleWithin_weaken ?_ ?_ hSeq
  · -- PRE weaken: theorem uses nsp + signExtend12 k; hSeq uses sp + signExtend12 (-32) + signExtend12 k
    intro _ hp
    simp only [show (nsp : Word) = sp + signExtend12 (-32) from rfl] at hp
    xperm_hyp hp
  · -- POST weaken: unfold evmPushOneBytePost, simplify, fold into evmStackIs
    intro _ hp
    rw [evmPushOneBytePost_unfold] at hp
    -- Step 1: Reduce let-bindings and simplify truncate 8 (zext 64 b) = b
    -- Keep pushByteSrcOffset/pushByteDstOffset un-reduced so h_byte/h_dstOff_zero match exactly
    have htrunc8 : ∀ (b : BitVec 8),
        BitVec.truncate 8 (BitVec.zeroExtend 64 b) = b := by
      intro b; simp [BitVec.truncate_eq_setWidth]
    simp only [htrunc8] at hp  -- reduces lets via zeta; htrunc8 fires on truncate arg
    -- Step 2: Apply h_byte and h_dstOff_zero via rw (exact syntactic match after let-reduction)
    rw [h_byte, h_dstOff_zero] at hp
    -- Step 3: Simplify replaceByte 0 0 byteVal = byteVal.zeroExtend 64
    -- Need show (0:Word)=0#64 so BitVec.zero_and can match the literal form
    simp only [replaceByte, show (0 : Nat) * 8 = 0 from rfl,
               show (0 : Word) = 0#64 from rfl,
               BitVec.zero_and, BitVec.shiftLeft_zero, BitVec.zero_or] at hp
    -- Fold slot atoms into evmStackIs nsp (pushImmediateWord 1 (fun _ => byteVal) :: rest)
    rw [← pushImmediateWord_evmStackIs_fold nsp 1 (fun _ => byteVal) rest]
    -- Evaluate pushImmediateLimb 1 (fun _ => byteVal) k for k = 0,1,2,3
    -- For k=0: (1-1-0)/8=0 is true → replaceByte 0 0 byteVal
    -- For k=1,2,3: (1-1-0)/8=k is false → 0
    simp only [pushImmediateLimb, pushByteDstOffset,
               show (1 - 1 - 0 : Nat) = 0 from rfl,
               show (0 : Nat) / 8 = 0 from rfl, show (0 : Nat) % 8 = 0 from rfl,
               show List.range 1 = [0] from rfl,
               List.foldl,
               show (0 : Nat) = 1 ↔ False from by decide,
               show (0 : Nat) = 2 ↔ False from by decide,
               show (0 : Nat) = 3 ↔ False from by decide,
               ite_true, if_false]
    simp only [replaceByte, show (0 : Nat) * 8 = 0 from rfl,
               show (0 : Word) = 0#64 from rfl,
               BitVec.zero_and, BitVec.shiftLeft_zero, BitVec.zero_or]
    xperm_hyp hp

end EvmAsm.Evm64
