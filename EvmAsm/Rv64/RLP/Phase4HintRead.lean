/-
  EvmAsm.Rv64.RLP.Phase4HintRead

  First executable Phase 4 wrapper for the RLP decoder: set the SP1 syscall
  selector for HINT_READ and invoke ECALL for a one-dword input read.
-/

import EvmAsm.Rv64.HintSpecs
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64.Tactics

/-- One-dword HINT_READ wrapper: `x10` is the destination buffer, `x11` is
    the byte count, and `x5` is overwritten with the SP1 HINT_READ selector. -/
def rlp_phase4_hint_read_one_word_prog : Program :=
  [.LI .x5 (BitVec.ofNat 64 0xF1), .ECALL]

theorem rlp_phase4_hint_read_one_word_code_eq_ofProg (base : Word) :
    CodeReq.ofProg base rlp_phase4_hint_read_one_word_prog =
      (CodeReq.singleton base (.LI .x5 (BitVec.ofNat 64 0xF1))).union
        (CodeReq.singleton (base + 4) .ECALL) := by
  simp only [rlp_phase4_hint_read_one_word_prog, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil, CodeReq.union_empty_right]

/-- Executable Phase 4 HINT_READ wrapper spec for reads contained in one
    output dword. The destination dword is owned by the caller and updated to
    the little-endian packing of the consumed private-input bytes. -/
theorem rlp_phase4_hint_read_one_word_spec_within
    (buf nbytes oldWord : Word) (input : List (BitVec 8)) (base : Word)
    (h_pos : 0 < nbytes.toNat) (h_le8 : nbytes.toNat ≤ 8)
    (h_suff : nbytes.toNat ≤ input.length) :
    cpsTripleWithin 2 base (base + 8)
      (CodeReq.ofProg base rlp_phase4_hint_read_one_word_prog)
      ((base + 4 ↦ᵢ .ECALL) ** regOwn .x5 ** (.x10 ↦ᵣ buf) **
        (.x11 ↦ᵣ nbytes) ** (buf ↦ₘ oldWord) ** privateInputIs input)
      ((base + 4 ↦ᵢ .ECALL) ** (.x10 ↦ᵣ buf) ** (.x11 ↦ᵣ nbytes) **
        (buf ↦ₘ bytesToWordLE (input.take nbytes.toNat)) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0xF1)) **
        privateInputIs (input.drop nbytes.toNat)) := by
  rw [rlp_phase4_hint_read_one_word_code_eq_ofProg]
  let cr := (CodeReq.singleton base (.LI .x5 (BitVec.ofNat 64 0xF1))).union
    (CodeReq.singleton (base + 4) .ECALL)
  have hli := li_spec_gen_own_within .x5 (BitVec.ofNat 64 0xF1) base (by nofun)
  have hli_ext : cpsTripleWithin 1 base (base + 4) cr
      (regOwn .x5)
      (.x5 ↦ᵣ (BitVec.ofNat 64 0xF1)) := by
    apply cpsTripleWithin_extend_code (cr' := cr)
    · exact CodeReq.union_mono_left
    · exact hli
  have hli_framed := cpsTripleWithin_frameR
    ((base + 4 ↦ᵢ .ECALL) ** (.x10 ↦ᵣ buf) ** (.x11 ↦ᵣ nbytes) **
      (buf ↦ₘ oldWord) ** privateInputIs input)
    (by pcFree) hli_ext
  have hread := ecall_hint_read_one_word_spec_gen_within
    buf nbytes oldWord input (base + 4) h_pos h_le8 h_suff
  have hread_at_exit : cpsTripleWithin 1 (base + 4) (base + 8)
      (CodeReq.singleton (base + 4) .ECALL)
      ((.x10 ↦ᵣ buf) ** (.x11 ↦ᵣ nbytes) ** (buf ↦ₘ oldWord) **
        (base + 4 ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 64 0xF1)) **
        privateInputIs input)
      ((.x10 ↦ᵣ buf) ** (.x11 ↦ᵣ nbytes) **
        (buf ↦ₘ bytesToWordLE (input.take nbytes.toNat)) **
        (base + 4 ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 64 0xF1)) **
        privateInputIs (input.drop nbytes.toNat)) := by
    have h_exit : (base + 4 : Word) + 4 = base + 8 := by bv_addr
    simpa only [h_exit] using hread
  have hread_ext : cpsTripleWithin 1 (base + 4) (base + 8) cr
      ((.x10 ↦ᵣ buf) ** (.x11 ↦ᵣ nbytes) ** (buf ↦ₘ oldWord) **
        (base + 4 ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 64 0xF1)) **
        privateInputIs input)
      ((.x10 ↦ᵣ buf) ** (.x11 ↦ᵣ nbytes) **
        (buf ↦ₘ bytesToWordLE (input.take nbytes.toNat)) **
        (base + 4 ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 64 0xF1)) **
        privateInputIs (input.drop nbytes.toNat)) := by
    apply cpsTripleWithin_extend_code (cr' := cr)
    · apply CodeReq.singleton_mono
      apply CodeReq.union_skip
      · exact CodeReq.singleton_miss (a := base) (a' := base + 4)
          (i := .LI .x5 (BitVec.ofNat 64 0xF1)) (by bv_omega)
      · exact CodeReq.singleton_get (base + 4) .ECALL
    · exact hread_at_exit
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp)
    hli_framed hread_ext
  simpa only [Nat.reduceAdd, sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hseq

end EvmAsm.Rv64.RLP
