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


/-- Step count of one `u256_add_be` invocation, kept opaque so the arithmetic
    in the composed step counts stays readable. -/
@[irreducible] def u256AddSteps (aPtr bPtr outPtr : Word)
    (aBytes bBytes orig : List (BitVec 8)) : Nat :=
  (U256AddBeSAsm.u256AddBeFn aPtr bPtr outPtr aBytes bBytes orig).body.steps + 1

/-- `u256_add_be`'s all-distinct whole-routine triple, lifted from its own
    `ofProg` code surface into this routine's six-way union.  The mathematical
    content is entirely `U256BeFlat.u256AddBeFlat_spec`; only the `CodeReq`
    changes. -/
private theorem u256AddCarryFlat_spec (ret aPtr bPtr outPtr : Word)
    (aBytes bBytes orig : List (BitVec 8))
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroA : Region.wf ⟨aPtr, aBytes⟩) (hroB : Region.wf ⟨bPtr, bBytes⟩)
    (hlenA : aBytes.length = 32) (hlenB : bBytes.length = 32)
    (hlenOrig : orig.length = 32)
    (hovA : aPtr.toNat + 32 < 2 ^ 64) (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisjA : aPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ aPtr.toNat)
    (hdisjB : bPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ bPtr.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (u256AddSteps aPtr bPtr outPtr aBytes bBytes orig)
      (GuestAddrs.u256_add_be : Word) ret secfAddModPCr
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns U256BeFlat.addScratch **
        bytesRegion outPtr orig **
        bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes)
      (((.x1 : Reg) ↦ᵣ ret) **
        ((.x10 : Reg) ↦ᵣ U256AddBeSAsm.u256AddBeCarry aBytes bBytes orig) **
        ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        regOwns U256BeFlat.addScratch **
        bytesRegion outPtr (U256AddBeSAsm.u256AddBeBytes aBytes bBytes orig) **
        bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes) := by
  rw [u256AddSteps]
  exact liftCode (cr' := secfAddModPCr)
    (U256BeFlat.u256AddBeFlat_spec ret aPtr bPtr outPtr aBytes bBytes orig
      hrw hroA hroB hlenA hlenB hlenOrig hovA hovB hovOut hdisjA hdisjB halign)
    (by unfold secfAddModPCr secfReduceOnceCr; code_mem)


/-- Body indices 7..15: the setup segment followed by the first `u256_add_be`
    call, which computes `x + y` into the global `secf_tmp0` and leaves the
    carry-out in `a0`.  Untouched resources ride along in the generic `pcFree`
    frame `A`. -/
private theorem setupFirstCall_spec (xPtr yPtr dst ret v8 v9 v18 v19 v20 : Word)
    (xs ys tmpOrig : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (hrwTmp : RwRegion.wf ⟨(GuestAddrs.secf_tmp0 : Word), 32⟩)
    (hroX : Region.wf ⟨xPtr, xs⟩) (hroY : Region.wf ⟨yPtr, ys⟩)
    (hlenX : xs.length = 32) (hlenY : ys.length = 32)
    (hlenTmp : tmpOrig.length = 32)
    (hovX : xPtr.toNat + 32 < 2 ^ 64) (hovY : yPtr.toNat + 32 < 2 ^ 64)
    (hdX : xPtr.toNat + 32 ≤ GuestAddrs.secf_tmp0 ∨
      GuestAddrs.secf_tmp0 + 32 ≤ xPtr.toNat)
    (hdY : yPtr.toNat + 32 ≤ GuestAddrs.secf_tmp0 ∨
      GuestAddrs.secf_tmp0 + 32 ≤ yPtr.toNat) :
    cpsTripleWithin
      (8 + (1 + u256AddSteps xPtr yPtr (GuestAddrs.secf_tmp0 : Word) xs ys tmpOrig))
      (GuestAddrs.secf_add_mod_p + 28 : Word)
      (GuestAddrs.secf_add_mod_p + 64 : Word) secfAddModPCr
      (((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) **
        ((.x20 : Reg) ↦ᵣ v20) ** ((.x10 : Reg) ↦ᵣ xPtr) **
        ((.x11 : Reg) ↦ᵣ yPtr) ** ((.x12 : Reg) ↦ᵣ dst) **
        ((.x1 : Reg) ↦ᵣ ret) ** regOwns U256BeFlat.addScratch **
        bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpOrig **
        bytesRegion xPtr xs ** bytesRegion yPtr ys ** A)
      (((.x8 : Reg) ↦ᵣ xPtr) ** ((.x9 : Reg) ↦ᵣ yPtr) **
        ((.x18 : Reg) ↦ᵣ dst) **
        ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x20 : Reg) ↦ᵣ v20) **
        ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_add_mod_p + 64 : Word)) **
        ((.x10 : Reg) ↦ᵣ U256AddBeSAsm.u256AddBeCarry xs ys tmpOrig) **
        ((.x11 : Reg) ↦ᵣ yPtr) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        regOwns U256BeFlat.addScratch **
        bytesRegion (GuestAddrs.secf_tmp0 : Word)
          (U256AddBeSAsm.u256AddBeBytes xs ys tmpOrig) **
        bytesRegion xPtr xs ** bytesRegion yPtr ys ** A) := by
  have hsetup := setup_spec xPtr yPtr dst ret v8 v9 v18 v19
  have hsetupF := cpsTripleWithin_frameR
    (((.x20 : Reg) ↦ᵣ v20) ** regOwns U256BeFlat.addScratch **
      bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpOrig **
      bytesRegion xPtr xs ** bytesRegion yPtr ys ** A)
    (by pcf; exact hA) hsetup
  have hcallee := u256AddCarryFlat_spec
    (GuestAddrs.secf_add_mod_p + 64 : Word) xPtr yPtr
    (GuestAddrs.secf_tmp0 : Word) xs ys tmpOrig hrwTmp hroX hroY
    hlenX hlenY hlenTmp hovX hovY (by decide) hdX hdY (by decide)
  rw [show (GuestAddrs.secf_add_mod_p + 64 : Word) =
      (GuestAddrs.secf_add_mod_p + 60 : Word) + 4 from by decide] at hcallee
  have hcall := callWithin_spec (cr := secfAddModPCr)
    (P := (((.x10 : Reg) ↦ᵣ xPtr) ** ((.x11 : Reg) ↦ᵣ yPtr) **
      ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      regOwns U256BeFlat.addScratch **
      bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpOrig **
      bytesRegion xPtr xs ** bytesRegion yPtr ys))
    (Q := (((.x10 : Reg) ↦ᵣ U256AddBeSAsm.u256AddBeCarry xs ys tmpOrig) **
      ((.x11 : Reg) ↦ᵣ yPtr) **
      ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      regOwns U256BeFlat.addScratch **
      bytesRegion (GuestAddrs.secf_tmp0 : Word)
        (U256AddBeSAsm.u256AddBeBytes xs ys tmpOrig) **
      bytesRegion xPtr xs ** bytesRegion yPtr ys))
    (GuestAddrs.secf_add_mod_p + 60 : Word) (GuestAddrs.u256_add_be : Word) ret
    (jalOff GuestAddrs.u256_add_be (GuestAddrs.secf_add_mod_p + 60))
    (u256AddSteps xPtr yPtr (GuestAddrs.secf_tmp0 : Word) xs ys tmpOrig)
    (by decide) (by unfold secfAddModPCr secfReduceOnceCr; code_mem) (by pcf)
    hcallee
  rw [show (GuestAddrs.secf_add_mod_p + 60 : Word) + 4 =
      (GuestAddrs.secf_add_mod_p + 64 : Word) from by decide] at hcall
  have hcallF := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ xPtr) ** ((.x9 : Reg) ↦ᵣ yPtr) **
      ((.x18 : Reg) ↦ᵣ dst) **
      ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x20 : Reg) ↦ᵣ v20) ** A)
    (by pcf; exact hA) hcall
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hsetupF hcallF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hc


/-- Body indices 16..17: latch the carry-out into `s4` and branch on it.
    `beq s4, x0, +24` from `secf_add_mod_p + 68` targets `+92` (index 23, the
    reduce setup) when the sum did not carry, and falls through to `+72`
    (index 18, the fold-back arm) when it did. -/
private theorem saveCarryBranch_spec (carry old20 : Word)
    (P : Assertion) (hP : P.pcFree) :
    cpsBranchWithin 2 (GuestAddrs.secf_add_mod_p + 64 : Word) secfAddModPCr
      (((.x20 : Reg) ↦ᵣ old20) ** ((.x10 : Reg) ↦ᵣ carry) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** P)
      (GuestAddrs.secf_add_mod_p + 92 : Word)
      (((.x20 : Reg) ↦ᵣ carry) ** ((.x10 : Reg) ↦ᵣ carry) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ⌜carry = 0⌝ ** P)
      (GuestAddrs.secf_add_mod_p + 72 : Word)
      (((.x20 : Reg) ↦ᵣ carry) ** ((.x10 : Reg) ↦ᵣ carry) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ⌜carry ≠ 0⌝ ** P) := by
  have hmv := liftCode (cr' := secfAddModPCr)
    (mv_spec_gen_within .x20 .x10 carry old20
      (GuestAddrs.secf_add_mod_p + 64 : Word) (by decide))
    (by unfold secfAddModPCr secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_add_mod_p + 64 : Word) + 4 =
      (GuestAddrs.secf_add_mod_p + 68 : Word) from by decide] at hmv
  have hmvF := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** P) (by exact pcFree_sepConj (by pcf) hP) hmv
  have hbr := cpsBranchWithin_frameR (((.x10 : Reg) ↦ᵣ carry) ** P)
    (pcFree_sepConj (by pcf) hP)
    (cpsBranchWithin_extend_code (cr' := secfAddModPCr)
      (h := beq_spec_gen_within .x20 .x0 (24 : BitVec 13) carry (0 : Word)
        (GuestAddrs.secf_add_mod_p + 68 : Word))
      (hmono := by unfold secfAddModPCr secfReduceOnceCr; code_mem))
  rw [show (GuestAddrs.secf_add_mod_p + 68 : Word) + signExtend13 (24 : BitVec 13) =
      (GuestAddrs.secf_add_mod_p + 92 : Word) from by
        rw [show signExtend13 (24 : BitVec 13) = (24 : Word) from by decide]
        decide,
    show (GuestAddrs.secf_add_mod_p + 68 : Word) + 4 =
      (GuestAddrs.secf_add_mod_p + 72 : Word) from by decide] at hbr
  have hc := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hmvF hbr
  exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) (fun _ hq => by xperm_hyp hq) hc


/-- The three aliasing contracts over `u256_add_be` share one clobber set, so
    the first-operand-aliased lift's scratch list is literally `addScratch`. -/
private theorem aInPlaceScratch_eq :
    U256AddBeAInPlaceSAsm.u256AddBeAInPlaceScratch = U256BeFlat.addScratch := rfl

/-- Step count of the first-operand-aliased `u256_add_be` invocation. -/
@[irreducible] def u256AddInPlaceSteps (aPtr bPtr : Word)
    (aBytes bBytes : List (BitVec 8)) : Nat :=
  (U256AddBeSAsm.u256AddBeInPlaceFn aPtr bPtr aBytes bBytes).body.steps + 1

/-- The aliased body's instruction count does not depend on the pointer or
    byte arguments, so the no-wraparound size side condition is uniform. -/
private theorem inPlaceSize_bound (aPtr bPtr : Word)
    (aBytes bBytes : List (BitVec 8)) :
    4 * ((U256AddBeSAsm.u256AddBeInPlaceFn aPtr bPtr aBytes bBytes).body.size
      + 1) ≤ 2 ^ 64 := by
  have h : (U256AddBeSAsm.u256AddBeInPlaceFn aPtr bPtr aBytes bBytes).body.size
      = (U256AddBeSAsm.u256AddBeInPlaceFn 0 0 [] []).body.size := rfl
  rw [h]
  decide

/-- `u256_add_be`'s first-operand-aliased (`a0 = a2`) whole-routine triple,
    lifted into this routine's code surface.  This is the contract retired
    from orphan status by the fold-back arm below. -/
private theorem u256AddAInPlaceLifted_spec (ret aPtr bPtr : Word)
    (aBytes bBytes : List (BitVec 8))
    (hrw : RwRegion.wf ⟨aPtr, 32⟩) (hroB : Region.wf ⟨bPtr, bBytes⟩)
    (hlenA : aBytes.length = 32) (hlenB : bBytes.length = 32)
    (hovA : aPtr.toNat + 32 < 2 ^ 64) (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hdisj : bPtr.toNat + 32 ≤ aPtr.toNat ∨ aPtr.toNat + 32 ≤ bPtr.toNat)
    (hsz : 4 * ((U256AddBeSAsm.u256AddBeInPlaceFn aPtr bPtr aBytes bBytes).body.size
      + 1) ≤ 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (u256AddInPlaceSteps aPtr bPtr aBytes bBytes)
      (GuestAddrs.u256_add_be : Word) ret secfAddModPCr
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ aPtr) ** regOwns U256BeFlat.addScratch **
        bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes)
      (((.x1 : Reg) ↦ᵣ ret) **
        ((.x10 : Reg) ↦ᵣ U256AddBeSAsm.u256AddBeCarry aBytes bBytes aBytes) **
        ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ aPtr) **
        regOwns U256BeFlat.addScratch **
        bytesRegion aPtr (U256AddBeSAsm.u256AddBeBytes aBytes bBytes aBytes) **
        bytesRegion bPtr bBytes) := by
  rw [u256AddInPlaceSteps, ← aInPlaceScratch_eq]
  exact liftCode (cr' := secfAddModPCr)
    (U256AddBeAInPlaceSAsm.u256AddBeAInPlaceFlat_spec ret aPtr bPtr aBytes bBytes
      hrw hroB hlenA hlenB hovA hovB hdisj hsz halign)
    (by
      unfold secfAddModPCr secfReduceOnceCr
        U256AddBeAInPlaceSAsm.u256AddBeAInPlaceCr
      code_mem)


/-- Body indices 18..22, the carry fold-back arm.  Reached only when the sum
    overflowed 256 bits; adds `C = 2^256 mod p` back into `secf_tmp0` in place
    (`a0 = a2 = &secf_tmp0`), which is exactly the aliasing shape discharged by
    `u256AddAInPlaceLifted_spec`. -/
private theorem foldBackArm_spec (ret0 v10 v11 v12 : Word)
    (tmpBytes : List (BitVec 8)) (B : Assertion) (hB : B.pcFree)
    (hrwTmp : RwRegion.wf ⟨(GuestAddrs.secf_tmp0 : Word), 32⟩)
    (hroC : Region.wf ⟨(GuestAddrs.secp256k1_c_be : Word),
      Secp256k1FieldSubModPSAsm.secp256k1CBytes⟩)
    (hlenTmp : tmpBytes.length = 32) :
    cpsTripleWithin
      (4 + (1 + u256AddInPlaceSteps (GuestAddrs.secf_tmp0 : Word)
        (GuestAddrs.secp256k1_c_be : Word) tmpBytes
        Secp256k1FieldSubModPSAsm.secp256k1CBytes))
      (GuestAddrs.secf_add_mod_p + 72 : Word)
      (GuestAddrs.secf_add_mod_p + 92 : Word) secfAddModPCr
      (((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
        ((.x12 : Reg) ↦ᵣ v12) ** ((.x1 : Reg) ↦ᵣ ret0) **
        regOwns U256BeFlat.addScratch **
        bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
        globalConst (GuestAddrs.secp256k1_c_be : Word)
          Secp256k1FieldSubModPSAsm.secp256k1CBytes ** B)
      (((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x10 : Reg) ↦ᵣ U256AddBeSAsm.u256AddBeCarry tmpBytes
          Secp256k1FieldSubModPSAsm.secp256k1CBytes tmpBytes) **
        ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_c_be : Word)) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_add_mod_p + 92 : Word)) **
        regOwns U256BeFlat.addScratch **
        bytesRegion (GuestAddrs.secf_tmp0 : Word)
          (U256AddBeSAsm.u256AddBeBytes tmpBytes
            Secp256k1FieldSubModPSAsm.secp256k1CBytes tmpBytes) **
        globalConst (GuestAddrs.secp256k1_c_be : Word)
          Secp256k1FieldSubModPSAsm.secp256k1CBytes ** B) := by
  -- index 18: mv a0, s3
  have hmv10 := liftCode (cr' := secfAddModPCr)
    (mv_spec_gen_within .x10 .x19 (GuestAddrs.secf_tmp0 : Word) v10
      (GuestAddrs.secf_add_mod_p + 72 : Word) (by decide))
    (by unfold secfAddModPCr secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_add_mod_p + 72 : Word) + 4 =
      (GuestAddrs.secf_add_mod_p + 76 : Word) from by decide] at hmv10
  -- indices 19..20: la a1, secp256k1_c_be
  have hla := la_materialize_within .x11 v11
    (GuestAddrs.secf_add_mod_p + 76 : Word) (GuestAddrs.secp256k1_c_be : Word)
    (cr := secfAddModPCr) (by decide) (by decide)
    (by unfold secfAddModPCr secfReduceOnceCr; code_mem)
    (by unfold secfAddModPCr secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_add_mod_p + 76 : Word) + 8 =
      (GuestAddrs.secf_add_mod_p + 84 : Word) from by decide] at hla
  -- index 21: mv a2, s3
  have hmv12 := liftCode (cr' := secfAddModPCr)
    (mv_spec_gen_within .x12 .x19 (GuestAddrs.secf_tmp0 : Word) v12
      (GuestAddrs.secf_add_mod_p + 84 : Word) (by decide))
    (by unfold secfAddModPCr secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_add_mod_p + 84 : Word) + 4 =
      (GuestAddrs.secf_add_mod_p + 88 : Word) from by decide] at hmv12
  -- index 22: the aliased call
  have hcallee := u256AddAInPlaceLifted_spec
    (GuestAddrs.secf_add_mod_p + 92 : Word) (GuestAddrs.secf_tmp0 : Word)
    (GuestAddrs.secp256k1_c_be : Word) tmpBytes
    Secp256k1FieldSubModPSAsm.secp256k1CBytes
    hrwTmp hroC hlenTmp (by decide) (by decide) (by decide) (by decide)
    (inPlaceSize_bound _ _ _ _) (by decide)
  rw [show (GuestAddrs.secf_add_mod_p + 92 : Word) =
      (GuestAddrs.secf_add_mod_p + 88 : Word) + 4 from by decide] at hcallee
  have hcall := callWithin_spec (cr := secfAddModPCr)
    (P := (((.x10 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_c_be : Word)) **
      ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      regOwns U256BeFlat.addScratch **
      bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
      bytesRegion (GuestAddrs.secp256k1_c_be : Word)
        Secp256k1FieldSubModPSAsm.secp256k1CBytes))
    (Q := (((.x10 : Reg) ↦ᵣ U256AddBeSAsm.u256AddBeCarry tmpBytes
        Secp256k1FieldSubModPSAsm.secp256k1CBytes tmpBytes) **
      ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_c_be : Word)) **
      ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      regOwns U256BeFlat.addScratch **
      bytesRegion (GuestAddrs.secf_tmp0 : Word)
        (U256AddBeSAsm.u256AddBeBytes tmpBytes
          Secp256k1FieldSubModPSAsm.secp256k1CBytes tmpBytes) **
      bytesRegion (GuestAddrs.secp256k1_c_be : Word)
        Secp256k1FieldSubModPSAsm.secp256k1CBytes))
    (GuestAddrs.secf_add_mod_p + 88 : Word) (GuestAddrs.u256_add_be : Word) ret0
    (jalOff GuestAddrs.u256_add_be (GuestAddrs.secf_add_mod_p + 88))
    (u256AddInPlaceSteps (GuestAddrs.secf_tmp0 : Word)
      (GuestAddrs.secp256k1_c_be : Word) tmpBytes
      Secp256k1FieldSubModPSAsm.secp256k1CBytes)
    (by decide) (by unfold secfAddModPCr secfReduceOnceCr; code_mem) (by pcf)
    hcallee
  rw [show (GuestAddrs.secf_add_mod_p + 88 : Word) + 4 =
      (GuestAddrs.secf_add_mod_p + 92 : Word) from by decide] at hcall
  -- chain 18 ; 19-20 ; 21 ; 22
  have h1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
        ((.x1 : Reg) ↦ᵣ ret0) ** regOwns U256BeFlat.addScratch **
        bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
        bytesRegion (GuestAddrs.secp256k1_c_be : Word)
          Secp256k1FieldSubModPSAsm.secp256k1CBytes ** B)
      (by pcf; exact hB) hmv10)
    (cpsTripleWithin_frameR
      (((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x10 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x12 : Reg) ↦ᵣ v12) ** ((.x1 : Reg) ↦ᵣ ret0) **
        regOwns U256BeFlat.addScratch **
        bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
        bytesRegion (GuestAddrs.secp256k1_c_be : Word)
          Secp256k1FieldSubModPSAsm.secp256k1CBytes ** B)
      (by pcf; exact hB) hla)
  have h2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1
    (cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_c_be : Word)) **
        ((.x1 : Reg) ↦ᵣ ret0) ** regOwns U256BeFlat.addScratch **
        bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
        bytesRegion (GuestAddrs.secp256k1_c_be : Word)
          Secp256k1FieldSubModPSAsm.secp256k1CBytes ** B)
      (by pcf; exact hB) hmv12)
  have h3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h2
    (cpsTripleWithin_frameR
      (((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) ** B)
      (by pcf; exact hB) hcall)
  exact cpsTripleWithin_weaken
    (fun _ hp => by simp only [globalConst] at hp ⊢; xperm_hyp hp)
    (fun _ hq => by simp only [globalConst] at hq ⊢; xperm_hyp hq) h3


end Secp256k1FieldAddModPSAsm

end EvmAsm.Codegen
