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

-- Abbreviations for the three sub-programs' instrAt assertions
-- Using the EXACT representations that hint_read_spec_gen / write_public_spec_gen / halt_spec_gen produce
private abbrev readInstrAt : Assertion :=
  (0 ↦ᵢ .LI .x5 0xF1#32) ** ((0 : Addr) + 4 ↦ᵢ .LI .x10 (0x100 : Word)) **
  ((0 : Addr) + 8 ↦ᵢ .LI .x11 (16 : Word)) ** ((0 : Addr) + 12 ↦ᵢ .ECALL)

private abbrev writeInstrAt : Assertion :=
  (16 ↦ᵢ .LI .x5 (BitVec.ofNat 32 0x02)) ** ((16 : Addr) + 4 ↦ᵢ .LI .x10 13) **
  ((16 : Addr) + 8 ↦ᵢ .LI .x11 (0x100 : Word)) ** ((16 : Addr) + 12 ↦ᵢ .LI .x12 (16 : Word)) **
  ((16 : Addr) + 16 ↦ᵢ .ECALL)

private abbrev haltInstrAt : Assertion :=
  (36 ↦ᵢ .LI .x5 (0 : Word)) ** ((36 : Addr) + 4 ↦ᵢ .LI .x10 (0 : Word)) ** ((36 : Addr) + 8 ↦ᵢ .ECALL)

private abbrev echoInstrAt : Assertion :=
  readInstrAt ** writeInstrAt ** haltInstrAt

theorem echo_spec (inputBytes : List (BitVec 8))
    (oldWords : List Word)
    (oldPV : List (BitVec 8))
    (hInputLen : 16 ≤ inputBytes.length)
    (hOldWords : oldWords.length = 4) :
    let newWords := bytesToWords (inputBytes.take 16)
    let newBytesFlat := newWords.flatMap
      (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])
    cpsHaltTriple 0
      (echoInstrAt **
       regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
       privateInputIs inputBytes ** publicValuesIs oldPV ** memBufferIs 0x100 oldWords)
      (echoInstrAt **
       (.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0x100 : Word)) ** (.x12 ↦ᵣ (16 : Word)) **
       privateInputIs (inputBytes.drop 16) **
       publicValuesIs (oldPV ++ newBytesFlat.take 16) **
       memBufferIs 0x100 newWords) := by
  intro newWords newBytesFlat
  -- Length lemma for bytesToWords
  have hBTW4 := bytesToWords_take16_length inputBytes hInputLen
  -- ================================================================
  -- Phase 1: HINT_READ at 0..16 (4 instructions)
  -- ================================================================
  have hread := hint_read_spec_gen (0x100 : Word) (16 : Word) inputBytes oldWords 0
    (by exact hInputLen) (by simp [hOldWords])
  -- pcFree proofs for instruction abbreviations
  have hRead_pf : readInstrAt.pcFree :=
    pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_instrAt _ _)
      (pcFree_sepConj (pcFree_instrAt _ _) (pcFree_instrAt _ _)))
  have hWrite_pf : writeInstrAt.pcFree :=
    pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_instrAt _ _)
      (pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_instrAt _ _) (pcFree_instrAt _ _))))
  have hHalt_pf : haltInstrAt.pcFree :=
    pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_instrAt _ _) (pcFree_instrAt _ _))
  -- Frame read with: writeInstrAt, haltInstrAt, regOwn x12, publicValuesIs
  have hread_framed := cpsTriple_frame_left _ _ _ _
    (writeInstrAt ** haltInstrAt ** regOwn .x12 ** publicValuesIs oldPV)
    (pcFree_sepConj hWrite_pf (pcFree_sepConj hHalt_pf
      (pcFree_sepConj (pcFree_regOwn _) (pcFree_publicValuesIs _))))
    hread
  -- ================================================================
  -- Phase 2: WRITE at 16..36 (5 instructions)
  -- ================================================================
  have hwrite := write_public_spec_gen (0x100 : Word) (16 : Word) oldPV
    (bytesToWords (inputBytes.take 16)) 16
    (by rw [hBTW4]; simp)
    (by native_decide)
  rw [show (16 : Addr) + 20 = 36 from by bv_omega] at hwrite
  -- Frame write with: readInstrAt, haltInstrAt, privateInputIs
  have hwrite_framed := cpsTriple_frame_left _ _ _ _
    (readInstrAt ** haltInstrAt ** privateInputIs (inputBytes.drop (BitVec.toNat (16 : Word))))
    (pcFree_sepConj hRead_pf (pcFree_sepConj hHalt_pf (pcFree_privateInputIs _)))
    hwrite
  -- ================================================================
  -- Phase 3: HALT at 36..44 (3 instructions)
  -- ================================================================
  have hhalt := halt_spec_gen (0 : Word) 36
  rw [show (36 : Addr) + 8 = 44 from by bv_omega] at hhalt
  -- Frame halt with everything else
  have hhalt_framed := cpsHaltTriple_frame_left 36 _ _
    (readInstrAt ** writeInstrAt **
     (.x11 ↦ᵣ (0x100 : Word)) ** (.x12 ↦ᵣ (16 : Word)) **
     privateInputIs (inputBytes.drop (BitVec.toNat (16 : Word))) **
     publicValuesIs (oldPV ++ newBytesFlat.take 16) ** memBufferIs (0x100 : Word) newWords)
    (pcFree_sepConj hRead_pf (pcFree_sepConj hWrite_pf
      (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
        (pcFree_sepConj (pcFree_privateInputIs _) (pcFree_sepConj (pcFree_publicValuesIs _)
          (pcFree_memBufferIs _ _)))))))
    hhalt
  -- ================================================================
  -- Composition: Direct proof by unfolding cpsHaltTriple
  -- ================================================================
  intro R hR s hPR hpc
  -- Phase 1: Apply hread_framed
  -- Need to permute hPR to match hread_framed precondition
  -- hPR : (echoInstrAt ** regOwn x5 ** regOwn x10 ** regOwn x11 ** regOwn x12 ** pI ** pvIs ** memBuf) ** R
  -- hread_framed wants: ((readInstrAt ** regOwn x5 ** regOwn x10 ** regOwn x11 ** pI ** memBuf) ** (writeInstrAt ** haltInstrAt ** regOwn x12 ** pvIs)) ** R
  -- Since echoInstrAt = readInstrAt ** writeInstrAt ** haltInstrAt (all abbrevs), xperm should handle this
  obtain ⟨k1, s1, hstep1, hpc1, hQ1⟩ := hread_framed R hR s (by
    apply holdsFor_mono (fun h hp => ?_) hPR
    xperm_hyp hp) hpc
  -- hQ1 : ((readInstrAt_expanded ** x5_is ** x10_is ** x11_is ** pI' ** memBuf') ** (writeInstrAt ** haltInstrAt ** regOwn x12 ** pvIs)) ** R
  -- Weaken regIs → regOwn for x5, x10, x11 (positions 5,6,7 in the flat chain, after 4 instrAt)
  -- Then permute for write phase
  -- Phase 2: Apply hwrite_framed
  obtain ⟨k2, s2, hstep2, hpc2, hQ2⟩ := hwrite_framed R hR s1 (by
    apply holdsFor_mono (fun h hp => ?_) hQ1
    -- hp : ((i0 ** i1 ** i2 ** i3 ** x5_is ** x10_is ** x11_is ** pI' ** memBuf') ** (wI ** hI ** regOwn x12 ** pvIs)) ** R
    -- Need: ((wI_expanded ** regOwn x5 ** regOwn x10 ** regOwn x11 ** regOwn x12 ** pvIs ** memBuf') ** (rI ** hI ** pI')) ** R
    -- Step 1: weaken regIs → regOwn in left-left part
    have hp1 := sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono (regIs_implies_regOwn .x5 0xF1#32)
          (sepConj_mono (regIs_implies_regOwn .x10 (0x100 : Word))
            (sepConj_mono_left (regIs_implies_regOwn .x11 (16 : Word)))))))))) h hp
    -- Step 2: permute
    xperm_hyp hp1) hpc1
  -- Phase 3: Apply hhalt_framed
  obtain ⟨k3, s3, hstep3, hhalt3, hQ3⟩ := hhalt_framed R hR s2 (by
    apply holdsFor_mono (fun h hp => ?_) hQ2
    -- Weaken regIs → regOwn for x5, x10 (positions 6,7 after 5 instrAt)
    have hp1 := sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono (regIs_implies_regOwn .x5 (BitVec.ofNat 32 0x02))
          (sepConj_mono_left (regIs_implies_regOwn .x10 (13 : Word)))))))))) h hp
    -- Permute
    xperm_hyp hp1) hpc2
  -- Compose step sequences
  refine ⟨k1 + k2 + k3, s3,
    stepN_add_eq (k1 + k2) k3 s s2 s3 (stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2) hstep3,
    hhalt3, ?_⟩
  -- Final postcondition rearrangement
  apply holdsFor_mono (fun h hp => ?_) hQ3
  xperm_hyp hp

end EvmAsm.Examples
