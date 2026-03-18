/-
  EvmAsm.Examples.Echo

  An "echo" program that reads 4 words from privateInput via HINT_READ
  and writes them to publicValues via WRITE, demonstrating the
  read-then-write I/O pipeline with a compositional CPS specification.

  The `echo_spec` theorem proves end-to-end correctness: given 16+ bytes of
  privateInput, the program reads 16 bytes, writes them to publicValues, and halts.
-/

import EvmAsm.Rv32.Execution
import EvmAsm.Rv32.SepLogic
import EvmAsm.Rv32.CPSSpec
import EvmAsm.Rv32.SyscallSpecs
import EvmAsm.Rv32.Tactics.XSimp

namespace EvmAsm.Examples

open EvmAsm

-- ============================================================================
-- Echo program definition
-- ============================================================================

/-- Echo program: read 4 words from privateInput → mem[0x100..0x10C],
    then write them to publicValues, then halt. -/
def echo : Program :=
  HINT_READ 0x100 16 ;;   -- Read 4 words from privateInput → mem[0x100..0x10C]
  WRITE 13 0x100 16 ;;    -- Write 4 words from mem[0x100..0x10C] → publicValues
  HALT 0                   -- Halt

-- ============================================================================
-- Smoke tests (concrete execution)
-- ============================================================================

/-- The echo program is 12 instructions long. -/
example : echo.length = 12 := by native_decide

/-- A concrete initial state for smoke tests.
    privateInput is 16 bytes representing 4 LE words: 1, 2, 3, 4. -/
def echoInitState : MachineState where
  regs := fun _ => 0
  mem := fun _ => 0
  code := loadProgram 0 echo
  pc := 0
  privateInput := [1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0]
  publicValues := []

/-- After 11 steps, publicValues = 16 LE bytes (words 1, 2, 3, 4). -/
example : (stepN 11 echoInitState).bind
    (fun s => some s.publicValues) = some [1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0] := by
  native_decide

/-- After 11 steps, privateInput is consumed. -/
example : (stepN 11 echoInitState).bind
    (fun s => some s.privateInput) = some [] := by
  native_decide

/-- After 11 steps, the next step is HALT (returns none). -/
example : ((stepN 11 echoInitState).bind
    (fun s => step s)).isNone = true := by
  native_decide

-- ============================================================================
-- Instruction fetch lemmas
-- ============================================================================

private theorem fetch_0 : loadProgram 0 echo 0 = some (Instr.LI .x5 0xF1) := by native_decide
private theorem fetch_1 : loadProgram 0 echo 4 = some (Instr.LI .x10 0x100) := by native_decide
private theorem fetch_2 : loadProgram 0 echo 8 = some (Instr.LI .x11 16) := by native_decide
private theorem fetch_3 : loadProgram 0 echo 12 = some .ECALL := by native_decide
private theorem fetch_4 : loadProgram 0 echo 16 = some (Instr.LI .x5 0x02) := by native_decide
private theorem fetch_5 : loadProgram 0 echo 20 = some (Instr.LI .x10 13) := by native_decide
private theorem fetch_6 : loadProgram 0 echo 24 = some (Instr.LI .x11 0x100) := by native_decide
private theorem fetch_7 : loadProgram 0 echo 28 = some (Instr.LI .x12 16) := by native_decide
private theorem fetch_8 : loadProgram 0 echo 32 = some .ECALL := by native_decide
private theorem fetch_9 : loadProgram 0 echo 36 = some (Instr.LI .x5 0) := by native_decide
private theorem fetch_10 : loadProgram 0 echo 40 = some (Instr.LI .x10 0) := by native_decide
private theorem fetch_11 : loadProgram 0 echo 44 = some .ECALL := by native_decide

-- ============================================================================
-- Echo specification
-- ============================================================================

/-- End-to-end specification for the echo program.
    Given 16+ bytes of private input and 4 words of memory at 0x100,
    the program reads 16 bytes into memory, writes them to public values, and halts.

    The postcondition for publicValues uses the computed byte representation:
    bytesToWords converts the input bytes to LE words, then extractBytes + flatMap
    converts back to bytes. For properly 4-aligned input, this is the identity.

    Uses regOwn for scratch registers (no old values needed). -/
-- Helper: weaken holdsFor through assertion implication
private theorem holdsFor_mono {P Q : Assertion} (h : ∀ ps, P ps → Q ps) {s : MachineState}
    (hp : P.holdsFor s) : Q.holdsFor s := by
  obtain ⟨ps, hcompat, hPps⟩ := hp
  exact ⟨ps, hcompat, h ps hPps⟩

-- Helper: bytesToWords of exactly 16 bytes from a long enough list gives 4 words
private theorem bytesToWords_take16_length (inputBytes : List (BitVec 8))
    (hLen : 16 ≤ inputBytes.length) :
    (bytesToWords (inputBytes.take 16)).length = 4 := by
  have h16 : (inputBytes.take 16).length = 16 := by
    rw [List.length_take]; omega
  have h4 : 4 ∣ (inputBytes.take 16).length := ⟨4, by omega⟩
  have := bytesToWords_length (inputBytes.take 16) h4
  omega

-- CodeReq for the three sub-programs
private abbrev readCodeReq : CodeReq :=
  CodeReq.singleton 0 (.LI .x5 0xF1#32) |>.union
  (CodeReq.singleton 4 (.LI .x10 (0x100 : Word)) |>.union
  (CodeReq.singleton 8 (.LI .x11 (16 : Word)) |>.union
  (CodeReq.singleton 12 .ECALL)))

private abbrev writeCodeReq : CodeReq :=
  CodeReq.singleton 16 (.LI .x5 (BitVec.ofNat 32 0x02)) |>.union
  (CodeReq.singleton 20 (.LI .x10 13) |>.union
  (CodeReq.singleton 24 (.LI .x11 (0x100 : Word)) |>.union
  (CodeReq.singleton 28 (.LI .x12 (16 : Word)) |>.union
  (CodeReq.singleton 32 .ECALL))))

private abbrev haltCodeReq : CodeReq :=
  CodeReq.singleton 36 (.LI .x5 (0 : Word)) |>.union
  (CodeReq.singleton 40 (.LI .x10 (0 : Word)) |>.union
  (CodeReq.singleton 44 .ECALL))

private abbrev echoCodeReq : CodeReq :=
  readCodeReq |>.union (writeCodeReq |>.union haltCodeReq)

theorem echo_spec (inputBytes : List (BitVec 8))
    (oldWords : List Word)
    (oldPV : List (BitVec 8))
    (hInputLen : 16 ≤ inputBytes.length)
    (hOldWords : oldWords.length = 4) :
    let newWords := bytesToWords (inputBytes.take 16)
    let newBytesFlat := newWords.flatMap
      (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])
    cpsHaltTriple 0 echoCodeReq
      (regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
       privateInputIs inputBytes ** publicValuesIs oldPV ** memBufferIs 0x100 oldWords)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0x100 : Word)) ** (.x12 ↦ᵣ (16 : Word)) **
       privateInputIs (inputBytes.drop 16) **
       publicValuesIs (oldPV ++ newBytesFlat.take 16) **
       memBufferIs 0x100 newWords) := by
  -- Side conditions for sub-specs
  have hOldWords4 : (16 : Word).toNat = 4 * oldWords.length := by
    have : (16 : Word).toNat = 16 := by native_decide
    omega
  have hNewWordsLen : (bytesToWords (inputBytes.take 16)).length = 4 :=
    bytesToWords_take16_length inputBytes hInputLen
  have hWriteLen : (16 : Word).toNat ≤ 4 * (bytesToWords (inputBytes.take 16)).length := by
    have : (16 : Word).toNat = 16 := by native_decide
    omega
  have hAligned : (0x100 : Word) &&& 3#32 = 0#32 := by native_decide
  -- Step 1: Instantiate hint_read_spec_gen at base=0
  have hrd := hint_read_spec_gen (0x100 : Word) (16 : Word) inputBytes oldWords 0
    (by have : (16 : Word).toNat = 16 := by native_decide
        omega) hOldWords4
  simp only [show (0 : Addr) + 16 = 16 from by bv_omega,
             show (0 : Addr) + 4 = 4 from by bv_omega,
             show (0 : Addr) + 8 = 8 from by bv_omega,
             show (0 : Addr) + 12 = 12 from by bv_omega] at hrd
  -- Weaken hint_read postcondition: regIs → regOwn
  have hrd_w := cpsTriple_consequence _ _ _ _ _ _ _
    (fun _ hp => hp)
    (sepConj_mono (regIs_implies_regOwn .x5 _)
      (sepConj_mono (regIs_implies_regOwn .x10 _)
        (sepConj_mono_left (regIs_implies_regOwn .x11 _))))
    hrd
  -- Frame hint_read with (regOwn .x12 ** publicValuesIs oldPV)
  have hrd_f := cpsTriple_frame_left _ _ _ _ _
    (regOwn .x12 ** publicValuesIs oldPV)
    (pcFree_sepConj (pcFree_regOwn .x12) (pcFree_publicValuesIs _))
    hrd_w
  -- Extend to echoCodeReq
  have hrd_e : cpsTriple 0 16 echoCodeReq _ _ :=
    cpsTriple_extend_code (CodeReq.union_mono_left _ _) hrd_f
  -- Step 2: Instantiate write_public_spec_gen at base=16
  have hwr := write_public_spec_gen (0x100 : Word) (16 : Word) oldPV
    (bytesToWords (inputBytes.take 16)) 16
    hWriteLen hAligned
  rw [show (16 : Addr) + 20 = 36 from by bv_omega,
      show (16 : Addr) + 4 = 20 from by bv_omega,
      show (16 : Addr) + 8 = 24 from by bv_omega,
      show (16 : Addr) + 12 = 28 from by bv_omega,
      show (16 : Addr) + 16 = 32 from by bv_omega] at hwr
  -- Weaken write_public postcondition: regIs → regOwn for x5 and x10 only
  -- Keep x11 and x12 as concrete values (needed in final postcondition)
  have hwr_w := cpsTriple_consequence _ _ _ _ _ _ _
    (fun _ hp => hp)
    (sepConj_mono (regIs_implies_regOwn .x5 _)
      (sepConj_mono_left (regIs_implies_regOwn .x10 _)))
    hwr
  -- Frame write_public with privateInputIs (inputBytes.drop 16)
  have hwr_f := cpsTriple_frame_left _ _ _ _ _
    (privateInputIs (inputBytes.drop (16 : Word).toNat))
    (pcFree_privateInputIs _)
    hwr_w
  -- Extend to echoCodeReq: writeCodeReq ⊆ echoCodeReq
  have hwr_mono : ∀ a i, writeCodeReq a = some i → echoCodeReq a = some i := by
    intro a i h; unfold echoCodeReq readCodeReq writeCodeReq haltCodeReq at *
    simp only [CodeReq.union, CodeReq.singleton] at h ⊢
    -- Determine which address a is from h, then simplify all ifs in the goal
    repeat first | split at h | split | bv_omega | simp_all
  have hwr_e : cpsTriple 16 36 echoCodeReq _ _ :=
    cpsTriple_extend_code hwr_mono hwr_f
  -- Compose hint_read + write_public via cpsTriple_seq_with_perm
  have hrw := cpsTriple_seq_with_perm _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    hrd_e hwr_e
  -- Step 3: Instantiate halt_spec_gen at base=36
  have hht := halt_spec_gen (0 : Word) 36
  rw [show (36 : Addr) + 4 = 40 from by bv_omega,
      show (36 : Addr) + 8 = 44 from by bv_omega] at hht
  -- Frame halt with remaining atoms (x11, x12 keep concrete values)
  have hht_f := cpsHaltTriple_frame_left _ _ _ _
    ((.x11 ↦ᵣ (0x100 : Word)) ** (.x12 ↦ᵣ (16 : Word)) **
     publicValuesIs (oldPV ++ ((bytesToWords (inputBytes.take 16)).flatMap
       (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take (16 : Word).toNat) **
     memBufferIs (0x100 : Word) (bytesToWords (inputBytes.take 16)) **
     privateInputIs (inputBytes.drop (16 : Word).toNat))
    (pcFree_sepConj (pcFree_regIs .x11 _)
      (pcFree_sepConj (pcFree_regIs .x12 _)
        (pcFree_sepConj (pcFree_publicValuesIs _)
          (pcFree_sepConj (pcFree_memBufferIs _ _)
            (pcFree_privateInputIs _)))))
    hht
  -- Extend halt to echoCodeReq: haltCodeReq ⊆ echoCodeReq
  have hht_mono : ∀ a i, haltCodeReq a = some i → echoCodeReq a = some i := by
    intro a i h; unfold echoCodeReq readCodeReq writeCodeReq haltCodeReq at *
    simp only [CodeReq.union, CodeReq.singleton] at h ⊢
    repeat first | split at h | split | bv_omega | simp_all
  -- Adjust hrw postcondition to match hht_f precondition
  -- hrw post: (regOwn x5 ** regOwn x10 ** regOwn x11 ** regOwn x12 ** publicValuesIs (...) ** memBufferIs (...)) ** privateInputIs (...)
  -- hht_f pre: (regOwn x5 ** regOwn x10) ** (regOwn x11 ** regOwn x12 ** publicValuesIs (...) ** memBufferIs (...) ** privateInputIs (...))
  -- Same atoms, different grouping → xperm_hyp
  -- Compose read+write with halt using cpsTriple_seq_halt
  -- We need the midpoint assertion Q to match between hrw's postcondition and hht's precondition.
  -- Use cpsHaltTriple_consequence on the final result to adjust pre/post.
  -- Work directly: the whole proof is
  --   cpsHaltTriple_consequence (pre adjustment) (post adjustment)
  --     (cpsTriple_seq_halt hrw_adj hht_e)
  -- where hrw_adj weakens hrw's post to match hht_e's pre.
  --
  -- Since xperm_hyp needs a concrete goal, let's do it all in tactic mode.
  -- Define the midpoint assertion Q_mid (= hht_f's precondition)
  -- hht_f's pre: (regOwn .x5 ** regOwn .x10) ** Frame
  -- where Frame = regOwn .x11 ** regOwn .x12 ** publicValuesIs (...) ** memBufferIs (...) ** privateInputIs (...)
  -- Extend hht_f to echoCodeReq with explicit types
  have hht_e : cpsHaltTriple 36 echoCodeReq
    ((regOwn .x5 ** regOwn .x10) **
      (.x11 ↦ᵣ (0x100 : Word)) ** (.x12 ↦ᵣ (16 : Word)) **
        publicValuesIs (oldPV ++ ((bytesToWords (inputBytes.take 16)).flatMap
          (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take (16 : Word).toNat) **
          memBufferIs (0x100 : Word) (bytesToWords (inputBytes.take 16)) **
            privateInputIs (inputBytes.drop (16 : Word).toNat))
    (((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word))) **
      (.x11 ↦ᵣ (0x100 : Word)) ** (.x12 ↦ᵣ (16 : Word)) **
        publicValuesIs (oldPV ++ ((bytesToWords (inputBytes.take 16)).flatMap
          (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take (16 : Word).toNat) **
          memBufferIs (0x100 : Word) (bytesToWords (inputBytes.take 16)) **
            privateInputIs (inputBytes.drop (16 : Word).toNat)) :=
    fun R hR s hcr hPR hpc =>
      hht_f R hR s (CodeReq.SatisfiedBy_mono s hht_mono hcr) hPR hpc
  -- Weaken hrw's postcondition to match hht_e's precondition
  have hrw_adj : cpsTriple 0 36 echoCodeReq
    _ -- precondition (same as hrw)
    ((regOwn .x5 ** regOwn .x10) **
      (.x11 ↦ᵣ (0x100 : Word)) ** (.x12 ↦ᵣ (16 : Word)) **
        publicValuesIs (oldPV ++ ((bytesToWords (inputBytes.take 16)).flatMap
          (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take (16 : Word).toNat) **
          memBufferIs (0x100 : Word) (bytesToWords (inputBytes.take 16)) **
            privateInputIs (inputBytes.drop (16 : Word).toNat)) :=
    cpsTriple_consequence _ _ _ _ _ _ _
      (fun _ hp => hp) (fun h hp => by xperm_hyp hp) hrw
  -- Compose
  have hfinal := cpsTriple_seq_halt _ _ _ _ _ _ hrw_adj hht_e
  -- Adjust final pre/post to match echo_spec
  show cpsHaltTriple 0 echoCodeReq _ _
  exact cpsHaltTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    hfinal

end EvmAsm.Examples
