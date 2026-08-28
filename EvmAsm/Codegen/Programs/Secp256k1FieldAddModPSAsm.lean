/-
  Verified byte-identical ABI-frame port of `secf_add_mod_p`.

  The routine adds the two 32-byte big-endian field elements into the global
  `secf_tmp0` scratch cell.  On carry-out it folds `C = 2^256 mod p` back into
  that temporary (so the mathematical sum is preserved modulo `p`), and then
  runs `secf_reduce_once` from the temporary into the caller's output buffer.

  Structure mirrors the `secf_sub_mod_p` port in
  `Secp256k1FieldSubModPSAsm.lean`: an identical six-slot ABI frame, the same
  `secf_tmp0` / `secp256k1_c_be` globals, and the same prologue/epilogue
  chaining.  The two differences are that the carry arm here writes back into
  the temporary *in place* (`a0 = a2`, discharged by
  `U256AddBeAInPlaceSAsm.u256AddBeAInPlaceFlat_spec`), and that the tail is a
  real call to `secf_reduce_once` rather than a copy.
-/

import EvmAsm.Codegen.Programs.Secp256k1FieldReduceOnceSAsm
import EvmAsm.Codegen.Programs.Secp256k1FieldSubModPSAsm
import EvmAsm.Codegen.Programs.Secp256k1Field
import EvmAsm.Codegen.Programs.U256AddBeAInPlaceSAsm
import EvmAsm.Codegen.Proofs.U256BeFlatTriples
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.RetForwardJoin

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

namespace Secp256k1FieldAddModPSAsm

open Secp256k1FieldReduceOnceSAsm

/-- The six callee-saved slots of `secf_add_mod_p`, identical to the
    `secf_sub_mod_p` frame. -/
def secfAddModPFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40)]

/-- The body between the prologue and the epilogue: instruction indices 7..26
    of `secfAddModP_prog`. -/
def secfAddModPBody : List Instr :=
  [ .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x19 (laHi GuestAddrs.secf_tmp0 (GuestAddrs.secf_add_mod_p + 40)),
    .ADDI .x19 .x19 (laLo GuestAddrs.secf_tmp0 (GuestAddrs.secf_add_mod_p + 40)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.u256_add_be (GuestAddrs.secf_add_mod_p + 60)),
    .MV .x20 .x10,
    .BEQ .x20 .x0 (24 : BitVec 13),
    .MV .x10 .x19,
    .AUIPC .x11 (laHi GuestAddrs.secp256k1_c_be (GuestAddrs.secf_add_mod_p + 76)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secp256k1_c_be (GuestAddrs.secf_add_mod_p + 76)),
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.u256_add_be (GuestAddrs.secf_add_mod_p + 88)),
    .MV .x10 .x19,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.secf_reduce_once (GuestAddrs.secf_add_mod_p + 100)),
    .LI .x10 (0 : Word) ]

/-- Byte-transparency: the deployed routine is exactly this ABI frame wrapped
    around `secfAddModPBody`, by `rfl`.  Together with
    `secp256k1FieldAddFunction_eq_prog` this pins the proof to the emitted
    image rather than to a re-modelled instruction list. -/
theorem secfAddModP_prog_eq :
    abiFrameProg (-48 : BitVec 12) (48 : BitVec 12)
      secfAddModPFrame secfAddModPBody = secfAddModP_prog := by
  rfl

#guard secfAddModPBody.length = 20
#guard secfAddModPFrame.length = 6

/-- Code surface: this routine, plus `u256_add_be`, plus everything
    `secf_reduce_once` may itself jump to (`secfReduceOnceCr` is already the
    four-way union of reduce-once, `u256_lt_be`, `u256_sub_be` and
    `secf_copy32`).  Six `ofProg` leaves in total. -/
def secfAddModPCr : CodeReq :=
  (Secp256k1FieldReduceOnceSAsm.secfReduceOnceCr.union
    (CodeReq.ofProg (GuestAddrs.u256_add_be : Word) u256AddBe_prog)).union
    (CodeReq.ofProg (GuestAddrs.secf_add_mod_p : Word) secfAddModP_prog)

/-- Entry values of the six saved registers. -/
def secfAddModPVals (ret s0 s1 s2 s3 s4 : Word) : Reg → Word := fun r =>
  match r with
  | .x1 => ret
  | .x8 => s0
  | .x9 => s1
  | .x18 => s2
  | .x19 => s3
  | .x20 => s4
  | _ => 0

/-- Body indices 7..14: latch the three arguments into callee-saved
    registers, materialize `&secf_tmp0` into `s3`, and re-present the
    argument triple for the first `u256_add_be` call.  Instruction-identical
    to the `secf_sub_mod_p` setup segment. -/
private theorem setup_spec (aPtr bPtr outPtr ret v8 v9 v18 v19 : Word) :
    cpsTripleWithin 8 (GuestAddrs.secf_add_mod_p + 28 : Word)
      (GuestAddrs.secf_add_mod_p + 60 : Word) secfAddModPCr
      (((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret))
      (((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ bPtr) **
        ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret)) := by
  have hmv8 := liftCode (cr' := secfAddModPCr)
    (mv_spec_gen_within .x8 .x10 aPtr v8
      (GuestAddrs.secf_add_mod_p + 28 : Word) (by decide))
    (by unfold secfAddModPCr; code_mem)
  rw [show (GuestAddrs.secf_add_mod_p + 28 : Word) + 4 =
      (GuestAddrs.secf_add_mod_p + 32 : Word) from by decide] at hmv8
  have hmv9 := liftCode (cr' := secfAddModPCr)
    (mv_spec_gen_within .x9 .x11 bPtr v9
      (GuestAddrs.secf_add_mod_p + 32 : Word) (by decide))
    (by unfold secfAddModPCr; code_mem)
  rw [show (GuestAddrs.secf_add_mod_p + 32 : Word) + 4 =
      (GuestAddrs.secf_add_mod_p + 36 : Word) from by decide] at hmv9
  have hmv18 := liftCode (cr' := secfAddModPCr)
    (mv_spec_gen_within .x18 .x12 outPtr v18
      (GuestAddrs.secf_add_mod_p + 36 : Word) (by decide))
    (by unfold secfAddModPCr; code_mem)
  rw [show (GuestAddrs.secf_add_mod_p + 36 : Word) + 4 =
      (GuestAddrs.secf_add_mod_p + 40 : Word) from by decide] at hmv18
  have hla := la_materialize_within .x19 v19
    (GuestAddrs.secf_add_mod_p + 40 : Word) (GuestAddrs.secf_tmp0 : Word)
    (cr := secfAddModPCr) (by decide) (by decide)
    (by unfold secfAddModPCr; code_mem) (by unfold secfAddModPCr; code_mem)
  rw [show (GuestAddrs.secf_add_mod_p + 40 : Word) + 8 =
      (GuestAddrs.secf_add_mod_p + 48 : Word) from by decide] at hla
  have hmv10 := liftCode (cr' := secfAddModPCr)
    (mv_spec_gen_within .x10 .x8 aPtr aPtr
      (GuestAddrs.secf_add_mod_p + 48 : Word) (by decide))
    (by unfold secfAddModPCr; code_mem)
  rw [show (GuestAddrs.secf_add_mod_p + 48 : Word) + 4 =
      (GuestAddrs.secf_add_mod_p + 52 : Word) from by decide] at hmv10
  have hmv11 := liftCode (cr' := secfAddModPCr)
    (mv_spec_gen_within .x11 .x9 bPtr bPtr
      (GuestAddrs.secf_add_mod_p + 52 : Word) (by decide))
    (by unfold secfAddModPCr; code_mem)
  rw [show (GuestAddrs.secf_add_mod_p + 52 : Word) + 4 =
      (GuestAddrs.secf_add_mod_p + 56 : Word) from by decide] at hmv11
  have hmv12 := liftCode (cr' := secfAddModPCr)
    (mv_spec_gen_within .x12 .x19 (GuestAddrs.secf_tmp0 : Word) outPtr
      (GuestAddrs.secf_add_mod_p + 56 : Word) (by decide))
    (by unfold secfAddModPCr; code_mem)
  rw [show (GuestAddrs.secf_add_mod_p + 56 : Word) + 4 =
      (GuestAddrs.secf_add_mod_p + 60 : Word) from by decide] at hmv12
  have h1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR
      (((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) **
        ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret))
      (by pcf) hmv8)
    (cpsTripleWithin_frameR
      (((.x8 : Reg) ↦ᵣ aPtr) ** ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret))
      (by pcf) hmv9)
  have h2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1
    (cpsTripleWithin_frameR
      (((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ bPtr) ** ((.x19 : Reg) ↦ᵣ v19) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x1 : Reg) ↦ᵣ ret))
      (by pcf) hmv18)
  have h3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h2
    (cpsTripleWithin_frameR
      (((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ bPtr) ** ((.x18 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret))
      (by pcf) hla)
  have h4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h3
    (cpsTripleWithin_frameR
      (((.x9 : Reg) ↦ᵣ bPtr) ** ((.x18 : Reg) ↦ᵣ outPtr) **
        ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ ret)) (by pcf) hmv10)
  have h5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h4
    (cpsTripleWithin_frameR
      (((.x8 : Reg) ↦ᵣ aPtr) ** ((.x18 : Reg) ↦ᵣ outPtr) **
        ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ ret)) (by pcf) hmv11)
  have h6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h5
    (cpsTripleWithin_frameR
      (((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ bPtr) **
        ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x10 : Reg) ↦ᵣ aPtr) **
        ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x1 : Reg) ↦ᵣ ret)) (by pcf) hmv12)
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h6


end Secp256k1FieldAddModPSAsm

end EvmAsm.Codegen
