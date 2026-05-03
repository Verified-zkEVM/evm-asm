/-
  EvmAsm.Rv64.HintSpecs

  CPS-style Hoare triples for SP1 hint syscalls (`HINT_LEN`, `HINT_READ`).

  Step-level semantics live in `EvmAsm.Rv64.Execution`
  (`step_ecall_hint_len`, `step_ecall_hint_read`); this file lifts the
  former to a `cpsTripleWithin` that the macro-assembler can consume
  through `runBlock` / `cpsTripleWithin_seq`.

  Slice 4a of GH issue #120 (RLP RISC-V decoder, Phase 4 HINT_READ
  pipeline). The Phase 4 wrapper program needs ECALL specs in the same
  shape as `ecall_halt_spec_gen_within` so the wrapper body can be
  composed with surrounding ALU/branch instructions.

  The first HINT_READ spec below covers the one-output-dword case. The
  multi-dword buffer spec remains the central work of the full Phase 4
  slice.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64

-- ============================================================================
-- HINT_LEN ECALL spec (SP1 convention: t0 = 0xF0)
-- ============================================================================

/-- `HINT_LEN` reads the length of the privateInput byte stream into `x10`.
    SP1 convention: caller sets `x5 = 0xF0` then issues `ECALL`.

    Pre/post-state mirrors `ecall_halt_spec_gen_within`, plus a
    `privateInputIs` resource that exposes the `input.length` value
    in the post.

    `x0` is *not* listed: the syscall does not touch it, so the caller
    can frame it through with `cpsTripleWithin_frameR` if needed. -/
@[spec_gen_rv64] theorem ecall_hint_len_spec_gen_within
    (vOld : Word) (input : List (BitVec 8)) (addr : Word) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr .ECALL)
      ((.x10 ↦ᵣ vOld) ** (addr ↦ᵢ .ECALL) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0xF0)) ** privateInputIs input)
      ((.x10 ↦ᵣ (BitVec.ofNat 64 input.length)) ** (addr ↦ᵢ .ECALL) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0xF0)) ** privateInputIs input) := by
  intro R hR s hcr hPR hpc; subst hpc
  -- Fetch from the CodeReq side-condition, not from the precondition.
  have hfetch : s.code s.pc = some .ECALL :=
    CodeReq.singleton_satisfiedBy.mp hcr
  -- Pull resource hypotheses out of the right-associated chain.
  have hP := holdsFor_sepConj_elim_left hPR
  have hP_rest := holdsFor_sepConj_elim_right hP
  have hP_x5_priv := holdsFor_sepConj_elim_right hP_rest
  have hx5 : s.getReg .x5 = BitVec.ofNat 64 0xF0 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hP_x5_priv)
  have hpi : s.privateInput = input :=
    holdsFor_privateInputIs.mp (holdsFor_sepConj_elim_right hP_x5_priv)
  -- Step: HINT_LEN writes BitVec.ofNat 64 s.privateInput.length to x10
  --       and advances PC by 4.
  have hstep := step_ecall_hint_len hfetch hx5
  -- Rewrite via `hpi` so the post mentions `input.length` instead of
  -- `s.privateInput.length`.
  rw [hpi] at hstep
  -- Witness: 1 step lands in s' = (s.setReg x10 _).setPC (s.pc + 4).
  refine ⟨1, Nat.le_refl 1,
    (s.setReg .x10 (BitVec.ofNat 64 input.length)).setPC (s.pc + 4),
    ?_, by simp [MachineState.setPC], ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep]; rfl
  · -- Re-associate to apply `holdsFor_sepConj_regIs_setReg` on x10.
    have h1 := holdsFor_sepConj_assoc.mp hPR
    -- h1 : ((x10 ↦ᵣ vOld) ** (((addr ↦ᵢ .ECALL) ** ((x5 ↦ᵣ ..) **
    --        privateInputIs input)) ** R)).holdsFor s
    have h2 := holdsFor_sepConj_regIs_setReg
                (v' := BitVec.ofNat 64 input.length)
                (by decide) h1
    -- h2 : ((x10 ↦ᵣ ofNat input.length) ** (((addr ↦ᵢ .ECALL) ** ..) ** R))
    --        .holdsFor (s.setReg x10 _)
    have h3 := holdsFor_sepConj_assoc.mpr h2
    -- h3 : (((x10 ↦ᵣ ofNat input.length) ** ((addr ↦ᵢ .ECALL) ** ..)) ** R)
    --        .holdsFor (s.setReg x10 _)
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h3

/-- `HINT_LEN` variant for callers that only own the return register `x10`,
    rather than knowing its pre-state value. -/
theorem ecall_hint_len_spec_gen_own_within
    (input : List (BitVec 8)) (addr : Word) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr .ECALL)
      (((addr ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 64 0xF0)) **
        privateInputIs input) ** regOwn .x10)
      ((.x10 ↦ᵣ (BitVec.ofNat 64 input.length)) ** (addr ↦ᵢ .ECALL) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0xF0)) ** privateInputIs input) := by
  apply cpsTripleWithin_of_forall_regIs_to_regOwn
  intro vOld
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    (ecall_hint_len_spec_gen_within vOld input addr)

-- ============================================================================
-- HINT_READ ECALL spec (SP1 convention: t0 = 0xF1)
-- ============================================================================

private theorem holdsFor_sepConj_privateInputIs_setPrivateInput
    {vals vals' : List (BitVec 8)} {R : Assertion} {s : MachineState}
    (h : ((privateInputIs vals) ** R).holdsFor s) :
    ((privateInputIs vals') ** R).holdsFor { s with privateInput := vals' } := by
  rcases h with ⟨h, hcompat, h1, h2, hd, hunion, hp1, hp2⟩
  rw [privateInputIs] at hp1
  subst hp1
  rw [← hunion] at hcompat
  have hcompat_parts := (PartialState.CompatibleWith_union hd).mp hcompat
  have h2_no_private : h2.privateInput = none := by
    rcases hd with ⟨_, _, _, _, _, hpriv⟩
    rcases hpriv with hleft | hright
    · simp [PartialState.singletonPrivateInput] at hleft
    · exact hright
  have hd' : (PartialState.singletonPrivateInput vals').Disjoint h2 := by
    rcases hd with ⟨hr, hm, hc, hpc, hpv, _⟩
    exact ⟨hr, hm, hc, hpc, hpv, Or.inr h2_no_private⟩
  have h2compat' : h2.CompatibleWith { s with privateInput := vals' } := by
    rcases hcompat_parts.2 with ⟨hr, hm, hc, hpc, hpv, hpi⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r v hv
      simpa using hr r v hv
    · intro a v hv
      simpa using hm a v hv
    · intro a i hv
      simpa using hc a i hv
    · intro v hv
      simpa using hpc v hv
    · intro v hv
      simpa using hpv v hv
    · intro v hv
      rw [h2_no_private] at hv
      simp at hv
  exact ⟨_, (PartialState.CompatibleWith_union hd').mpr
    ⟨PartialState.CompatibleWith_singletonPrivateInput.mpr rfl, h2compat'⟩,
    _, _, hd', rfl, rfl, hp2⟩

/-- `HINT_READ` consumes up to one output dword from the private input stream
    and writes the consumed bytes to the caller-owned destination dword.

    This is the first reusable Phase 4 syscall bridge: it captures the input
    consumption and the memory output for `0 < nbytes ≤ 8`. Larger reads are
    handled by the later multi-dword buffer spec. -/
@[spec_gen_rv64] theorem ecall_hint_read_one_word_spec_gen_within
    (buf nbytes oldWord : Word) (input : List (BitVec 8)) (addr : Word)
    (h_pos : 0 < nbytes.toNat) (h_le8 : nbytes.toNat ≤ 8)
    (h_suff : nbytes.toNat ≤ input.length) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr .ECALL)
      ((.x10 ↦ᵣ buf) ** (.x11 ↦ᵣ nbytes) ** (buf ↦ₘ oldWord) **
        (addr ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 64 0xF1)) **
        privateInputIs input)
      ((.x10 ↦ᵣ buf) ** (.x11 ↦ᵣ nbytes) **
        (buf ↦ₘ bytesToWordLE (input.take nbytes.toNat)) **
        (addr ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 64 0xF1)) **
        privateInputIs (input.drop nbytes.toNat)) := by
  intro R hR s hcr hPR hpc; subst hpc
  let bytes := input.take nbytes.toNat
  have hfetch : s.code s.pc = some .ECALL :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hP := holdsFor_sepConj_elim_left hPR
  have hP_x11 := holdsFor_sepConj_elim_right hP
  have hP_mem := holdsFor_sepConj_elim_right hP_x11
  have hP_code := holdsFor_sepConj_elim_right hP_mem
  have hP_x5_priv := holdsFor_sepConj_elim_right hP_code
  have hx10 : s.getReg .x10 = buf :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hP)
  have hx11 : s.getReg .x11 = nbytes :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hP_x11)
  have hx5 : s.getReg .x5 = BitVec.ofNat 64 0xF1 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hP_x5_priv)
  have hpi : s.privateInput = input :=
    holdsFor_privateInputIs.mp (holdsFor_sepConj_elim_right hP_x5_priv)
  have h_suff_state : (s.getReg .x11).toNat ≤ s.privateInput.length := by
    rw [hx11, hpi]
    exact h_suff
  have hstep := step_ecall_hint_read hfetch hx5 h_suff_state
  have h_bytes_len : bytes.length = nbytes.toNat := by
    simp [bytes, List.length_take, h_suff]
  have h_bytes_take : bytes.take 8 = bytes := by
    apply List.take_of_length_le
    rw [h_bytes_len]
    exact h_le8
  have h_bytes_drop : bytes.drop 8 = [] := by
    apply List.drop_eq_nil_of_le
    rw [h_bytes_len]
    exact h_le8
  have h_after_private :
      ((privateInputIs (input.drop nbytes.toNat)) **
        (buf ↦ₘ oldWord) ** (.x10 ↦ᵣ buf) ** (.x11 ↦ᵣ nbytes) **
          (s.pc ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 64 0xF1)) ** R).holdsFor
          { s with privateInput := input.drop nbytes.toNat } := by
    have hpre :
        ((privateInputIs input) **
          (buf ↦ₘ oldWord) ** (.x10 ↦ᵣ buf) ** (.x11 ↦ᵣ nbytes) **
            (s.pc ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 64 0xF1)) ** R).holdsFor s := by
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hPR
    exact holdsFor_sepConj_privateInputIs_setPrivateInput
      (vals := input) (vals' := input.drop nbytes.toNat) hpre
  have h_after_mem :
      ((buf ↦ₘ bytesToWordLE bytes) **
        privateInputIs (input.drop nbytes.toNat) ** (.x10 ↦ᵣ buf) **
          (.x11 ↦ᵣ nbytes) ** (s.pc ↦ᵢ .ECALL) **
          (.x5 ↦ᵣ (BitVec.ofNat 64 0xF1)) ** R).holdsFor
          ({ s with privateInput := input.drop nbytes.toNat }.setMem buf
            (bytesToWordLE bytes)) := by
    have hpre :
        ((buf ↦ₘ oldWord) ** privateInputIs (input.drop nbytes.toNat) **
          (.x10 ↦ᵣ buf) ** (.x11 ↦ᵣ nbytes) ** (s.pc ↦ᵢ .ECALL) **
          (.x5 ↦ᵣ (BitVec.ofNat 64 0xF1)) ** R).holdsFor
          { s with privateInput := input.drop nbytes.toNat } := by
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using h_after_private
    exact holdsFor_sepConj_memIs_setMem (v' := bytesToWordLE bytes) hpre
  have h_write :
      ({ s with privateInput := input.drop nbytes.toNat }.writeBytesAsWords buf bytes) =
        ({ s with privateInput := input.drop nbytes.toNat }.setMem buf
          (bytesToWordLE bytes)) := by
    cases h_bytes : bytes with
    | nil =>
        have h_zero : nbytes.toNat = 0 := by
          simpa [h_bytes] using h_bytes_len.symm
        omega
    | cons b bs =>
        simp only [MachineState.writeBytesAsWords]
        have h_len_cons : (b :: bs).length ≤ 8 := by
          rw [← h_bytes, h_bytes_len]
          exact h_le8
        rw [List.take_of_length_le h_len_cons, List.drop_eq_nil_of_le h_len_cons]
        simp
  refine ⟨1, Nat.le_refl 1,
    (({ s with privateInput := input.drop nbytes.toNat }.writeBytesAsWords buf bytes)).setPC (s.pc + 4),
    ?_, by simp [MachineState.setPC], ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep]
    simp only [hx10, hx11, hpi]
    rfl
  · have hpost : (((.x10 ↦ᵣ buf) ** (.x11 ↦ᵣ nbytes) **
        (buf ↦ₘ bytesToWordLE bytes) ** (s.pc ↦ᵢ .ECALL) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0xF1)) **
        privateInputIs (input.drop nbytes.toNat)) ** R).holdsFor
          ({ s with privateInput := input.drop nbytes.toNat }.writeBytesAsWords buf bytes) := by
      rw [h_write]
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using h_after_mem
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) hpost

end EvmAsm.Rv64
