/-
  EvmAsm.Rv64.HintSpecs

  CPS-style Hoare triple for the zkvm-standards `read_input` syscall (t0=0xF2).

  The legacy SP1 HINT_LEN (t0=0xF0) and HINT_READ (t0=0xF1) syscall specs
  have been retired; their ECALL handler branches were removed from
  `Rv64/Execution.lean` in the same change.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

module

public import EvmAsm.Rv64.SyscallSpecs
public import EvmAsm.Rv64.Tactics.XSimp

@[expose] public section

namespace EvmAsm.Rv64

-- ============================================================================
-- read_input ECALL spec (zkvm-standards C ABI: t0 = 0xF2)
-- ============================================================================

/-- `read_input` (zkvm-standards C ABI, t0 = 0xF2) idempotently writes the
    input-buffer base pointer to memory at `a0` and the input length to
    memory at `a1`.  Does not consume or mutate the private input.

    Pre:  x5 = 0xF2; x10 = ptr_a0 (valid dword addr); x11 = ptr_a1 (valid dword addr);
          mem[ptr_a0] = old_ptr; mem[ptr_a1] = old_size;
          inputBufBaseIs buf_base; privateInputIs input
    Post: mem[ptr_a0] = buf_base; mem[ptr_a1] = input.length;
          inputBufBaseIs buf_base; privateInputIs input (unchanged) -/
theorem ecall_read_input_spec_gen_within
    (buf_base old_ptr old_size ptr_a0 ptr_a1 : Word)
    (input : List (BitVec 8)) (addr : Word)
    (hvalid_a0 : isValidDwordAccess ptr_a0 = true)
    (hvalid_a1 : isValidDwordAccess ptr_a1 = true) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr .ECALL)
      ((addr ↦ᵢ .ECALL) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0xF2)) **
        (.x10 ↦ᵣ ptr_a0) ** (.x11 ↦ᵣ ptr_a1) **
        (ptr_a0 ↦ₘ old_ptr) ** (ptr_a1 ↦ₘ old_size) **
        inputBufBaseIs buf_base ** privateInputIs input)
      ((addr ↦ᵢ .ECALL) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0xF2)) **
        (.x10 ↦ᵣ ptr_a0) ** (.x11 ↦ᵣ ptr_a1) **
        (ptr_a0 ↦ₘ buf_base) ** (ptr_a1 ↦ₘ (BitVec.ofNat 64 input.length)) **
        inputBufBaseIs buf_base ** privateInputIs input) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some .ECALL :=
    CodeReq.singleton_satisfiedBy.mp hcr
  -- Extract the big precondition (left of ** R), then split it
  have hBIG := holdsFor_sepConj_elim_left hPR
  -- hBIG : (addr ↦ᵢ ** x5 ** x10 ** x11 ** a0 ** a1 ** base ** priv).holdsFor s
  have hP_rest1 := holdsFor_sepConj_elim_right hBIG
  have hx5 : s.getReg .x5 = BitVec.ofNat 64 0xF2 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hP_rest1)
  have hP_rest2 := holdsFor_sepConj_elim_right hP_rest1
  have hx10 : s.getReg .x10 = ptr_a0 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hP_rest2)
  have hP_rest3 := holdsFor_sepConj_elim_right hP_rest2
  have hx11 : s.getReg .x11 = ptr_a1 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hP_rest3)
  -- Extract inputBufBase and privateInput
  have hP_rest4 := holdsFor_sepConj_elim_right hP_rest3  -- ptr_a0 ↦ₘ old_ptr
  have hP_rest5 := holdsFor_sepConj_elim_right hP_rest4  -- ptr_a1 ↦ₘ old_size
  have hP_rest6 := holdsFor_sepConj_elim_right hP_rest5  -- inputBufBaseIs buf_base
  have hbase : s.inputBufBase = buf_base :=
    holdsFor_inputBufBaseIs.mp (holdsFor_sepConj_elim_left hP_rest6)
  have hpi : s.privateInput = input :=
    holdsFor_privateInputIs.mp (holdsFor_sepConj_elim_right hP_rest6)
  -- Execute step
  rw [← hx10] at hvalid_a0; rw [← hx11] at hvalid_a1
  have hstep := step_ecall_read_input hfetch hx5 hvalid_a0 hvalid_a1
  rw [hbase, hpi] at hstep
  let s1 := s.setMem ptr_a0 buf_base
  let s2 := s1.setMem ptr_a1 (BitVec.ofNat 64 input.length)
  refine ⟨1, Nat.le_refl 1, s2.setPC (s.pc + 4),
    ?_, by simp [MachineState.setPC, s2, s1], ?_⟩
  · show (step s).bind (stepN 0) = some _
    simp only [hstep, s1, s2, hx10, hx11, stepN, Option.bind_some]
  · -- POST: build using two successive setMem updates then setPC.
    -- Permute PRE to have (a0 ↦ₘ old_ptr) first
    have hPR' : ((ptr_a0 ↦ₘ old_ptr) **
          ((ptr_a1 ↦ₘ old_size) **
           ((s.pc ↦ᵢ .ECALL) **
            (.x5 ↦ᵣ BitVec.ofNat 64 0xF2) **
            (.x10 ↦ᵣ ptr_a0) ** (.x11 ↦ᵣ ptr_a1) **
            inputBufBaseIs buf_base ** privateInputIs input ** R))).holdsFor s := by
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hPR
    -- Update a0 ↦ₘ old_ptr → a0 ↦ₘ buf_base
    have h1 : ((ptr_a0 ↦ₘ buf_base) **
          ((ptr_a1 ↦ₘ old_size) **
           ((s.pc ↦ᵢ .ECALL) **
            (.x5 ↦ᵣ BitVec.ofNat 64 0xF2) **
            (.x10 ↦ᵣ ptr_a0) ** (.x11 ↦ᵣ ptr_a1) **
            inputBufBaseIs buf_base ** privateInputIs input ** R))).holdsFor s1 :=
      holdsFor_sepConj_memIs_setMem hPR'
    -- Update a1 ↦ₘ old_size → a1 ↦ₘ len (permute first, then apply)
    have hPR1' : ((ptr_a1 ↦ₘ old_size) **
          ((ptr_a0 ↦ₘ buf_base) **
           ((s.pc ↦ᵢ .ECALL) **
            (.x5 ↦ᵣ BitVec.ofNat 64 0xF2) **
            (.x10 ↦ᵣ ptr_a0) ** (.x11 ↦ᵣ ptr_a1) **
            inputBufBaseIs buf_base ** privateInputIs input ** R))).holdsFor s1 := by
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using h1
    have h2 : ((ptr_a1 ↦ₘ (BitVec.ofNat 64 input.length)) **
          ((ptr_a0 ↦ₘ buf_base) **
           ((s.pc ↦ᵢ .ECALL) **
            (.x5 ↦ᵣ BitVec.ofNat 64 0xF2) **
            (.x10 ↦ᵣ ptr_a0) ** (.x11 ↦ᵣ ptr_a1) **
            inputBufBaseIs buf_base ** privateInputIs input ** R))).holdsFor s2 :=
      holdsFor_sepConj_memIs_setMem hPR1'
    -- Apply setPC
    have hPC : (((s.pc ↦ᵢ .ECALL) **
          (.x5 ↦ᵣ BitVec.ofNat 64 0xF2) **
          (.x10 ↦ᵣ ptr_a0) ** (.x11 ↦ᵣ ptr_a1) **
          (ptr_a0 ↦ₘ buf_base) ** (ptr_a1 ↦ₘ (BitVec.ofNat 64 input.length)) **
          inputBufBaseIs buf_base ** privateInputIs input) ** R).holdsFor s2 := by
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using h2
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) hPC

end EvmAsm.Rv64
