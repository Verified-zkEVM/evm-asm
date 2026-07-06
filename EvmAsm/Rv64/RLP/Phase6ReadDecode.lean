/-
  EvmAsm.Rv64.RLP.Phase6ReadDecode

  EL.3 / Phase 6 — the top-level pipeline's input hand-off: `read_input ⨾ LD`. The
  `read_input` Phase-4 wrapper (`rlp_phase4_read_input_len_spec_within_exact`) calls the
  zkvm-standards `read_input` syscall, writing `inputBufBase` and `privateInput.length` to two
  SP-relative cells. The schema decoder, however, wants the input buffer base in `x13` (its
  input pointer). This file bridges them: after the wrapper, one `LD x13, x12, ptr_ptr_off`
  loads `buf_base` from its cell into `x13`, leaving the machine ready for the decoder to run on
  `bytesRegion inputBufBase privateInput` (the host-ABI input contract, supplied by the caller).
-/

import EvmAsm.Rv64.RLP.Phase4HintLen
import EvmAsm.Rv64.InstructionSpecs

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000 in
/-- **Phase 6 input-pointer hand-off.** Run the `read_input` wrapper (4 instrs) then
    `LD x13, x12, ptr_ptr_off` (1 instr) to load the returned `inputBufBase` into `x13` — the
    schema decoder's input pointer. The two out-cells end holding `(buf_base, input.length)` and
    `x13 = buf_base`; `inputBufBaseIs`/`privateInputIs` are preserved. -/
theorem rlp_phase6_read_input_ptr
    (ptr_ptr_off size_ptr_off : BitVec 12)
    (sp buf_base old_ptr old_size v10 v11 v5 v13 : Word)
    (input : List (BitVec 8)) (base : Word)
    (hvalid_a0 : isValidDwordAccess (sp + signExtend12 ptr_ptr_off) = true)
    (hvalid_a1 : isValidDwordAccess (sp + signExtend12 size_ptr_off) = true) :
    cpsTripleWithin 5 base (base + 20)
      ((CodeReq.ofProg base (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off)).union
        (CodeReq.singleton (base + 16) (.LD .x13 .x12 ptr_ptr_off)))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x5 ↦ᵣ v5) ** (.x13 ↦ᵣ v13) **
        (base + 12 ↦ᵢ .ECALL) **
        ((sp + signExtend12 ptr_ptr_off) ↦ₘ old_ptr) **
        ((sp + signExtend12 size_ptr_off) ↦ₘ old_size) **
        inputBufBaseIs buf_base ** privateInputIs input)
      ((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ sp + signExtend12 ptr_ptr_off) **
        (.x11 ↦ᵣ sp + signExtend12 size_ptr_off) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0xF2)) **
        (.x13 ↦ᵣ buf_base) **
        (base + 12 ↦ᵢ .ECALL) **
        ((sp + signExtend12 ptr_ptr_off) ↦ₘ buf_base) **
        ((sp + signExtend12 size_ptr_off) ↦ₘ (BitVec.ofNat 64 input.length)) **
        inputBufBaseIs buf_base ** privateInputIs input) := by
  -- The read_input wrapper, framing x13 through it.
  have h_read := rlp_phase4_read_input_len_spec_within_exact ptr_ptr_off size_ptr_off
    sp buf_base old_ptr old_size v10 v11 v5 input base hvalid_a0 hvalid_a1
  have h_read' := cpsTripleWithin_frameR (.x13 ↦ᵣ v13) (by pcFree) h_read
  -- The load: LD x13, x12, ptr_ptr_off reads buf_base from its cell into x13.
  have h_ld := ld_spec_within .x13 .x12 sp v13 buf_base ptr_ptr_off (base + 16) (by decide)
  have h_ld' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ sp + signExtend12 ptr_ptr_off) ** (.x11 ↦ᵣ sp + signExtend12 size_ptr_off) **
      (.x5 ↦ᵣ (BitVec.ofNat 64 0xF2)) ** (base + 12 ↦ᵢ .ECALL) **
      ((sp + signExtend12 size_ptr_off) ↦ₘ (BitVec.ofNat 64 input.length)) **
      inputBufBaseIs buf_base ** privateInputIs input)
    (by pcFree) h_ld
  -- Disjointness: the wrapper code (base .. base+12) ⊥ the LD at base+16.
  have hd : (CodeReq.ofProg base (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off)).Disjoint
      (CodeReq.singleton (base + 16) (.LD .x13 .x12 ptr_ptr_off)) :=
    CodeReq.Disjoint.ofProg_singleton
      (CodeReq.ofProg_none_range_len base (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off) 4
        (base + 16) (rlp_phase4_read_input_len_prog_length ptr_ptr_off size_ptr_off)
        (by intro k hk; bv_omega))
  have composed := cpsTripleWithin_seq hd
    (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp) h_read')
    h_ld'
  rw [show base + 16 + 4 = base + 20 from by bv_omega,
      show (4 : Nat) + 1 = 5 from rfl] at composed
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) composed

end EvmAsm.Rv64.RLP
