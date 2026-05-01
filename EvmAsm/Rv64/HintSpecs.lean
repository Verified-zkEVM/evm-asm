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

  HINT_READ is intentionally **not** covered here: it requires reasoning
  about the input-buffer placement convention (memory range owned in
  the post-state) and is the central work of slice 4 itself. HINT_LEN
  is purely register-only and can ship now.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Rv64.SyscallSpecs

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

end EvmAsm.Rv64
