/-
  EvmAsm.Rv64.RLP.Phase4HintLen

  Executable Phase 4 wrapper for the RLP decoder: set the SP1 syscall
  selector for HINT_LEN and invoke ECALL to read the private-input length.
-/

import EvmAsm.Rv64.HintSpecs
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64.Tactics

/-- HINT_LEN wrapper: `x5` is overwritten with the SP1 HINT_LEN selector and
    the private-input byte length is returned in `x10`. -/
def rlp_phase4_hint_len_prog : Program :=
  [.LI .x5 (BitVec.ofNat 64 0xF0), .ECALL]

theorem rlp_phase4_hint_len_code_eq_ofProg (base : Word) :
    CodeReq.ofProg base rlp_phase4_hint_len_prog =
      (CodeReq.singleton base (.LI .x5 (BitVec.ofNat 64 0xF0))).union
        (CodeReq.singleton (base + 4) .ECALL) := by
  simp only [rlp_phase4_hint_len_prog, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil, CodeReq.union_empty_right]

/-- Executable Phase 4 HINT_LEN wrapper spec. The wrapper sets the selector
    register and then invokes ECALL; the postcondition exposes the current
    private-input length in `x10`. -/
theorem rlp_phase4_hint_len_spec_within
    (input : List (BitVec 8)) (base : Word) :
    cpsTripleWithin 2 base (base + 8)
      (CodeReq.ofProg base rlp_phase4_hint_len_prog)
      ((base + 4 ↦ᵢ .ECALL) ** regOwn .x5 ** regOwn .x10 **
        privateInputIs input)
      ((base + 4 ↦ᵢ .ECALL) ** (.x10 ↦ᵣ (BitVec.ofNat 64 input.length)) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0xF0)) ** privateInputIs input) := by
  rw [rlp_phase4_hint_len_code_eq_ofProg]
  let cr := (CodeReq.singleton base (.LI .x5 (BitVec.ofNat 64 0xF0))).union
    (CodeReq.singleton (base + 4) .ECALL)
  have hli := li_spec_gen_own_within .x5 (BitVec.ofNat 64 0xF0) base (by nofun)
  have hli_ext : cpsTripleWithin 1 base (base + 4) cr
      (regOwn .x5)
      (.x5 ↦ᵣ (BitVec.ofNat 64 0xF0)) := by
    apply cpsTripleWithin_extend_code (cr' := cr)
    · exact CodeReq.union_mono_left
    · exact hli
  have hli_framed := cpsTripleWithin_frameR
    ((base + 4 ↦ᵢ .ECALL) ** regOwn .x10 ** privateInputIs input)
    (by pcFree) hli_ext
  have hlen := ecall_hint_len_spec_gen_own_within input (base + 4)
  have hlen_at_exit : cpsTripleWithin 1 (base + 4) (base + 8)
      (CodeReq.singleton (base + 4) .ECALL)
      (((base + 4 ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 64 0xF0)) **
        privateInputIs input) ** regOwn .x10)
      ((.x10 ↦ᵣ (BitVec.ofNat 64 input.length)) ** (base + 4 ↦ᵢ .ECALL) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0xF0)) ** privateInputIs input) := by
    have h_exit : (base + 4 : Word) + 4 = base + 8 := by bv_omega
    simpa only [h_exit] using hlen
  have hlen_ext : cpsTripleWithin 1 (base + 4) (base + 8) cr
      (((base + 4 ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 64 0xF0)) **
        privateInputIs input) ** regOwn .x10)
      ((.x10 ↦ᵣ (BitVec.ofNat 64 input.length)) ** (base + 4 ↦ᵢ .ECALL) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0xF0)) ** privateInputIs input) := by
    apply cpsTripleWithin_extend_code (cr' := cr)
    · apply CodeReq.singleton_mono
      apply CodeReq.union_skip
      · exact CodeReq.singleton_miss (a := base) (a' := base + 4)
          (i := .LI .x5 (BitVec.ofNat 64 0xF0)) (by bv_omega)
      · exact CodeReq.singleton_get (base + 4) .ECALL
    · exact hlen_at_exit
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp)
    hli_framed hlen_ext
  simpa only [Nat.reduceAdd, sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hseq

end EvmAsm.Rv64.RLP
