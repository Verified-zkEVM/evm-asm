/-
  EvmAsm.Codegen.Programs.Secp256k1FieldReduceOnceSAsm

  SAsm/CPS port scaffold for `secf_reduce_once`: reduce a 32-byte
  big-endian secp256k1 field element by subtracting p at most once.

  The emitted routine is an ABI-frame caller over three verified callees:
  `u256_lt_be`, `u256_sub_be`, and `secf_copy32`, with `la` materialization
  of the read-only modulus and the 8-byte comparison scratch cell.
-/

import EvmAsm.Codegen.Programs.Secp256k1Field
import EvmAsm.Codegen.Programs.Secp256k1FieldLeavesSAsm
import EvmAsm.Codegen.Programs.U256LtBeSAsm
import EvmAsm.Codegen.Programs.U256SubBeSAsm
import EvmAsm.Rv64.SAsm.BlockAtBridge
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.RetForwardJoin
import EvmAsm.Rv64.Tactics.DropPure
import EvmAsm.Rv64.Tactics.ExtractPure

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

namespace Secp256k1FieldReduceOnceSAsm

-- Address anchors for byte-transparent proof.
#guard GuestAddrs.secf_reduce_once = 0x8001fe68
#guard GuestAddrs.u256_lt_be = 0x800052c4
#guard GuestAddrs.u256_sub_be = 0x80005248
#guard GuestAddrs.secf_copy32 = 0x8001fca4
#guard GuestAddrs.secp256k1_p_be = 0xa3c052c0
#guard GuestAddrs.secf_cmp = 0xa3c053e0

/-- secp256k1 field prime, as 32 big-endian bytes. -/
def secp256k1PBytes : List (BitVec 8) :=
  [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
   0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
   0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
   0xff, 0xff, 0xff, 0xfe, 0xff, 0xff, 0xfc, 0x2f]

#guard secp256k1PBytes.length = 32

/-- The routine's frame slots: `ra`, `s0`, `s1`. -/
def secfReduceOnceFrame : FrameDesc := [(.x1, 0), (.x8, 8), (.x9, 16)]

/-- Body between ABI-frame prologue and epilogue. -/
def secfReduceOnceBody : List Instr :=
  [ .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.secp256k1_p_be (GuestAddrs.secf_reduce_once + 28)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secp256k1_p_be (GuestAddrs.secf_reduce_once + 28)),
    .AUIPC .x12 (laHi GuestAddrs.secf_cmp (GuestAddrs.secf_reduce_once + 36)),
    .ADDI .x12 .x12 (laLo GuestAddrs.secf_cmp (GuestAddrs.secf_reduce_once + 36)),
    .JAL .x1 (jalOff GuestAddrs.u256_lt_be (GuestAddrs.secf_reduce_once + 44)),
    .AUIPC .x5 (laHi GuestAddrs.secf_cmp (GuestAddrs.secf_reduce_once + 48)),
    .ADDI .x5 .x5 (laLo GuestAddrs.secf_cmp (GuestAddrs.secf_reduce_once + 48)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BNE .x6 .x0 (32 : BitVec 13),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.secp256k1_p_be (GuestAddrs.secf_reduce_once + 68)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secp256k1_p_be (GuestAddrs.secf_reduce_once + 68)),
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.u256_sub_be (GuestAddrs.secf_reduce_once + 80)),
    .LI .x10 (1 : Word),
    .JAL .x0 (20 : BitVec 21),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.secf_copy32 (GuestAddrs.secf_reduce_once + 100)),
    .LI .x10 (0 : Word) ]

#guard secfReduceOnceBody.length = 23

/-- Code surface for the caller plus all three callees it may jump to. -/
def secfReduceOnceCr : CodeReq :=
  (((CodeReq.ofProg (GuestAddrs.secf_reduce_once : Word) secfReduceOnce_prog).union
    (CodeReq.ofProg (GuestAddrs.u256_lt_be : Word) u256LtBe_prog)).union
    (CodeReq.ofProg (GuestAddrs.u256_sub_be : Word) u256SubBe_prog)).union
    (CodeReq.ofProg (GuestAddrs.secf_copy32 : Word) secfCopy32_prog)

/-- Byte-transparency: the emitted routine is exactly this ABI frame. -/
theorem secfReduceOnce_prog_eq :
    abiFrameProg (-32 : BitVec 12) (32 : BitVec 12)
      secfReduceOnceFrame secfReduceOnceBody = secfReduceOnce_prog := rfl


def secfReduceOnceVals (ret s0 s1 : Word) : Reg → Word := fun r =>
  match r with
  | .x1 => ret
  | .x8 => s0
  | .x9 => s1
  | _ => 0


/-- Real reduce-once byte result.  The caller is expected to supply values
    below `2p`; this pure post still states the exact branch semantics of
    the emitted routine. -/
def reduceOnceBytes (x orig : List (BitVec 8)) : List (BitVec 8) :=
  if beBytesToNat x < beBytesToNat secp256k1PBytes then
    x
  else
    U256SubBeSAsm.u256SubBeBytes x secp256k1PBytes orig

/-- Return flag: `1` iff the subtraction path was taken. -/
def reduceOnceFlag (x : List (BitVec 8)) : Word :=
  if beBytesToNat x < beBytesToNat secp256k1PBytes then (0 : Word) else (1 : Word)

/-- The `secf_cmp` scratch dword after the `u256_lt_be` call. -/
def cmpFlagWord (x : List (BitVec 8)) : Word :=
  if beBytesToNat x < beBytesToNat secp256k1PBytes then (1 : Word) else (0 : Word)

-- ============================================================================
-- Local flat adapter for callees whose `Fn` post preserves ambient assertions.
-- ============================================================================

private theorem asrtOf_intro_ambient (rw : RwRegion) (reach : Reach)
    (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion)
    (hlen : ws.length = rw.len) (hApc : A.pcFree) (hreach : reach rf ws A) :
    ∀ hp, (((regFileIs rf) ** bytesRegion rw.base ws) ** A) hp →
      asrtOf rw reach hp := by
  intro hp hh
  exact ⟨rf, ws, A, hlen, hApc, hreach, hh⟩

private theorem asrtOf_elim_ambient (rw : RwRegion) (reach : Reach) {Q : Assertion}
    (h : ∀ (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
      ws.length = rw.len → A.pcFree → reach rf ws A →
      ∀ hp, (((regFileIs rf) ** bytesRegion rw.base ws) ** A) hp → Q hp) :
    ∀ hp, asrtOf rw reach hp → Q hp := by
  rintro hp ⟨rf, ws, A, hlen, hApc, hreach, hsts⟩
  exact h rf ws A hlen hApc hreach hp hsts

private theorem retSpecFlatAmbient (f : Fn) (base : Word) (hspec : f.Spec base)
    (hsz : 4 * (f.body.size + 1) ≤ 2 ^ 64)
    (ret : Word) (halign : (ret &&& ~~~(1 : Word)) = ret)
    (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion)
    (hlen : ws.length = f.rw.len) (hApc : A.pcFree) (hpre : f.pre rf ws A)
    {Q : Assertion}
    (hpost : ∀ (rf' : RegFile) (ws' : List (BitVec 8)) (A' : Assertion),
      ws'.length = f.rw.len → A'.pcFree → f.post rf' ws' A' →
      ∀ hp, (((regFileIs rf') ** bytesRegion f.rw.base ws') ** A') hp → Q hp) :
    cpsTripleWithin (f.body.steps + 1) base ret
      (CodeReq.ofProg base (f.programRet base))
      (((((.x1 : Reg) ↦ᵣ ret) ** (regFileIs rf) ** bytesRegion f.rw.base ws)
        ** A) ** bytesRegion f.region.base f.region.bytes)
      ((((.x1 : Reg) ↦ᵣ ret) ** Q) ** bytesRegion f.region.base f.region.bytes) := by
  have hr := Fn.retSpec f base hspec hsz ret halign
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hr
  · have hp1 : ((((.x1 : Reg) ↦ᵣ ret)
        ** ((regFileIs rf ** bytesRegion f.rw.base ws) ** A))
        ** bytesRegion f.region.base f.region.bytes) h := by
      xperm_hyp hp
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (asrtOf_intro_ambient f.rw f.pre rf ws A hlen hApc hpre)) h hp1
    show (((.x1 : Reg) ↦ᵣ ret) ** asrtM f.region f.rw f.pre) h
    unfold asrtM
    xperm_hyp hp2
  · unfold asrtM at hq
    have hq1 : ((((.x1 : Reg) ↦ᵣ ret) ** asrtOf f.rw f.post)
        ** bytesRegion f.region.base f.region.bytes) h := by
      xperm_hyp hq
    exact sepConj_mono_left (sepConj_mono_right
      (asrtOf_elim_ambient f.rw f.post hpost)) h hq1

private theorem ltSetup_spec (src dst ret v8 v9 v12 : Word) :
    cpsTripleWithin 7 (GuestAddrs.secf_reduce_once + 16 : Word)
      (GuestAddrs.secf_reduce_once + 44 : Word) secfReduceOnceCr
      (((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) **
        ((.x12 : Reg) ↦ᵣ v12) ** ((.x1 : Reg) ↦ᵣ ret))
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ src) **
        ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_p_be : Word)) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        ((.x1 : Reg) ↦ᵣ ret)) := by
  have hmv8 := liftCode (cr' := secfReduceOnceCr)
    (mv_spec_gen_within .x8 .x10 src v8 (GuestAddrs.secf_reduce_once + 16 : Word)
      (by decide))
    (by unfold secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_reduce_once + 16 : Word) + 4 =
      (GuestAddrs.secf_reduce_once + 20 : Word) from by decide] at hmv8
  have hmv9 := liftCode (cr' := secfReduceOnceCr)
    (mv_spec_gen_within .x9 .x11 dst v9 (GuestAddrs.secf_reduce_once + 20 : Word)
      (by decide))
    (by unfold secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_reduce_once + 20 : Word) + 4 =
      (GuestAddrs.secf_reduce_once + 24 : Word) from by decide] at hmv9
  have hmv10 := liftCode (cr' := secfReduceOnceCr)
    (mv_spec_gen_within .x10 .x8 src src (GuestAddrs.secf_reduce_once + 24 : Word)
      (by decide))
    (by unfold secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_reduce_once + 24 : Word) + 4 =
      (GuestAddrs.secf_reduce_once + 28 : Word) from by decide] at hmv10
  have hlaP := la_materialize_within .x11 dst
    (GuestAddrs.secf_reduce_once + 28 : Word) (GuestAddrs.secp256k1_p_be : Word)
    (cr := secfReduceOnceCr) (by decide) (by decide)
    (by unfold secfReduceOnceCr; code_mem) (by unfold secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_reduce_once + 28 : Word) + 8 =
      (GuestAddrs.secf_reduce_once + 36 : Word) from by decide] at hlaP
  have hlaCmp := la_materialize_within .x12 v12
    (GuestAddrs.secf_reduce_once + 36 : Word) (GuestAddrs.secf_cmp : Word)
    (cr := secfReduceOnceCr) (by decide) (by decide)
    (by unfold secfReduceOnceCr; code_mem) (by unfold secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_reduce_once + 36 : Word) + 8 =
      (GuestAddrs.secf_reduce_once + 44 : Word) from by decide] at hlaCmp
  have hmv8F := cpsTripleWithin_frameR
    (((.x9 : Reg) ↦ᵣ v9) ** ((.x11 : Reg) ↦ᵣ dst) **
      ((.x12 : Reg) ↦ᵣ v12) ** ((.x1 : Reg) ↦ᵣ ret))
    (by pcf) hmv8
  have hmv9F := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ src) ** ((.x10 : Reg) ↦ᵣ src) **
      ((.x12 : Reg) ↦ᵣ v12) ** ((.x1 : Reg) ↦ᵣ ret))
    (by pcf) hmv9
  have hmv10F := cpsTripleWithin_frameR
    (((.x9 : Reg) ↦ᵣ dst) ** ((.x11 : Reg) ↦ᵣ dst) **
      ((.x12 : Reg) ↦ᵣ v12) ** ((.x1 : Reg) ↦ᵣ ret))
    (by pcf) hmv10
  have hlaPF := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
      ((.x10 : Reg) ↦ᵣ src) ** ((.x12 : Reg) ↦ᵣ v12) **
      ((.x1 : Reg) ↦ᵣ ret))
    (by pcf) hlaP
  have hlaCmpF := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
      ((.x10 : Reg) ↦ᵣ src) **
      ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_p_be : Word)) **
      ((.x1 : Reg) ↦ᵣ ret))
    (by pcf) hlaCmp
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hmv8F hmv9F
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 hmv10F
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 hlaPF
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c3 hlaCmpF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c4

private theorem u256LtBeInCr_spec (aPtr bPtr outPtr ret : Word)
    (as bs : List (BitVec 8))
    (hlenA : as.length = 32) (hlenB : bs.length = 32)
    (halignA : aPtr.toNat % 8 = 0) (halignB : bPtr.toNat % 8 = 0)
    (hovA : aPtr.toNat + 32 < 2 ^ 64) (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ k, k < 32 → isValidByteAccess (aPtr + BitVec.ofNat 64 k) = true)
    (hvalidB : ∀ k, k < 32 → isValidByteAccess (bPtr + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 295 (GuestAddrs.u256_lt_be : Word) ret secfReduceOnceCr
      (((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
       ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
       bytesRegion aPtr as ** bytesRegion bPtr bs ** memOwn outPtr)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ bPtr) **
       ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
       bytesRegion aPtr as ** bytesRegion bPtr bs **
       (outPtr ↦ₘ (if beBytesToNat as < beBytesToNat bs then (1 : Word) else (0 : Word)))) := by
  have h := U256LtBeSAsm.u256LtBe_spec aPtr bPtr outPtr ret as bs hlenA hlenB
    halignA halignB hovA hovB hvalidA hvalidB halignRet
  exact liftCode (cr' := secfReduceOnceCr) h (by unfold secfReduceOnceCr; code_mem)

private theorem secp256k1PByte_valid (k : Nat) (hk : k < 32) :
    isValidByteAccess ((GuestAddrs.secp256k1_p_be : Word) + BitVec.ofNat 64 k) = true := by
  interval_cases k <;> decide

private theorem ltSetupCall_spec (src dst ret v8 v9 v12 : Word)
    (xs : List (BitVec 8))
    (hlenX : xs.length = 32)
    (halignX : src.toNat % 8 = 0)
    (hovX : src.toNat + 32 < 2 ^ 64)
    (hvalidX : ∀ k, k < 32 → isValidByteAccess (src + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 303 (GuestAddrs.secf_reduce_once + 16 : Word)
      (GuestAddrs.secf_reduce_once + 48 : Word) secfReduceOnceCr
      (((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) **
        ((.x12 : Reg) ↦ᵣ v12) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs **
        globalConst (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes **
        memOwn (GuestAddrs.secf_cmp : Word))
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_p_be : Word)) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 48 : Word)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs **
        globalConst (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes **
        ((GuestAddrs.secf_cmp : Word) ↦ₘ
          (if beBytesToNat xs < beBytesToNat secp256k1PBytes then (1 : Word) else (0 : Word)))) := by
  unfold globalConst
  have hsetup := ltSetup_spec src dst ret v8 v9 v12
  have hsetupF := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
      bytesRegion src xs ** bytesRegion (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes **
      memOwn (GuestAddrs.secf_cmp : Word))
    (by pcf) hsetup
  have hcallee0 := u256LtBeInCr_spec src (GuestAddrs.secp256k1_p_be : Word)
    (GuestAddrs.secf_cmp : Word) (GuestAddrs.secf_reduce_once + 48 : Word)
    xs secp256k1PBytes hlenX (by decide) halignX (by decide) hovX (by decide)
    hvalidX secp256k1PByte_valid (by decide)
  have hcallee : cpsTripleWithin 295 (GuestAddrs.u256_lt_be : Word)
      (GuestAddrs.secf_reduce_once + 48 : Word) secfReduceOnceCr
      (((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 48 : Word)) **
        (((.x10 : Reg) ↦ᵣ src) **
        ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_p_be : Word)) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs ** bytesRegion (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes **
        memOwn (GuestAddrs.secf_cmp : Word)))
      (((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 48 : Word)) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_p_be : Word)) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs ** bytesRegion (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes **
        ((GuestAddrs.secf_cmp : Word) ↦ₘ
          (if beBytesToNat xs < beBytesToNat secp256k1PBytes then (1 : Word) else (0 : Word))))) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcallee0
  have hcall := callWithin_spec (cr := secfReduceOnceCr)
    (P := (((.x10 : Reg) ↦ᵣ src) **
        ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_p_be : Word)) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs ** bytesRegion (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes **
        memOwn (GuestAddrs.secf_cmp : Word)))
    (Q := (((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_p_be : Word)) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs ** bytesRegion (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes **
        ((GuestAddrs.secf_cmp : Word) ↦ₘ
          (if beBytesToNat xs < beBytesToNat secp256k1PBytes then (1 : Word) else (0 : Word)))) )
    (GuestAddrs.secf_reduce_once + 44 : Word) (GuestAddrs.u256_lt_be : Word) ret
    (jalOff GuestAddrs.u256_lt_be (GuestAddrs.secf_reduce_once + 44)) 295
    (by decide) (by unfold secfReduceOnceCr; code_mem) (by pcf) hcallee
  rw [show (GuestAddrs.secf_reduce_once + 44 : Word) + 4 =
      (GuestAddrs.secf_reduce_once + 48 : Word) from by decide] at hcall
  have hcallF := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst)) (by pcf) hcall
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsetupF hcallF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_mono_nSteps (by omega) hc)

private theorem cmpLoad_spec (flag src dst pPtr ret : Word)
    (xs : List (BitVec 8)) :
    cpsTripleWithin 3 (GuestAddrs.secf_reduce_once + 48 : Word)
      (GuestAddrs.secf_reduce_once + 60 : Word) secfReduceOnceCr
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ pPtr) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs ** globalConst pPtr secp256k1PBytes **
        ((GuestAddrs.secf_cmp : Word) ↦ₘ flag))
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ pPtr) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        ((.x6 : Reg) ↦ᵣ flag) ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs ** globalConst pPtr secp256k1PBytes **
        ((GuestAddrs.secf_cmp : Word) ↦ₘ flag)) := by
  unfold globalConst
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ pPtr) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs ** bytesRegion pPtr secp256k1PBytes **
        ((GuestAddrs.secf_cmp : Word) ↦ₘ flag)) )
      (fun v5 => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
      (P := (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ pPtr) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ v5) ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs ** bytesRegion pPtr secp256k1PBytes **
        ((GuestAddrs.secf_cmp : Word) ↦ₘ flag)) )
      (fun v6 => ?_))
  have hla := la_materialize_within .x5 v5
    (GuestAddrs.secf_reduce_once + 48 : Word) (GuestAddrs.secf_cmp : Word)
    (cr := secfReduceOnceCr) (by decide) (by decide)
    (by unfold secfReduceOnceCr; code_mem) (by unfold secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_reduce_once + 48 : Word) + 8 =
      (GuestAddrs.secf_reduce_once + 56 : Word) from by decide] at hla
  have hld := liftCode (cr' := secfReduceOnceCr)
    (ld_spec_within .x6 .x5 (GuestAddrs.secf_cmp : Word) v6 flag (0 : BitVec 12)
      (GuestAddrs.secf_reduce_once + 56 : Word) (by decide))
    (by unfold secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_cmp : Word) + signExtend12 (0 : BitVec 12) =
      (GuestAddrs.secf_cmp : Word) from by decide,
    show (GuestAddrs.secf_reduce_once + 56 : Word) + 4 =
      (GuestAddrs.secf_reduce_once + 60 : Word) from by decide] at hld
  have hlaF := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ pPtr) **
      ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x6 : Reg) ↦ᵣ v6) ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
      bytesRegion src xs ** bytesRegion pPtr secp256k1PBytes **
      ((GuestAddrs.secf_cmp : Word) ↦ₘ flag))
    (by pcf) hla
  have hldF := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ pPtr) **
      ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
      bytesRegion src xs ** bytesRegion pPtr secp256k1PBytes)
    (by pcf) hld
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hldF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hc

private theorem ltSetupCallLoad_spec (src dst ret v8 v9 v12 : Word)
    (xs : List (BitVec 8))
    (hlenX : xs.length = 32)
    (halignX : src.toNat % 8 = 0)
    (hovX : src.toNat + 32 < 2 ^ 64)
    (hvalidX : ∀ k, k < 32 → isValidByteAccess (src + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 306 (GuestAddrs.secf_reduce_once + 16 : Word)
      (GuestAddrs.secf_reduce_once + 60 : Word) secfReduceOnceCr
      (((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) **
        ((.x12 : Reg) ↦ᵣ v12) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs **
        globalConst (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes **
        memOwn (GuestAddrs.secf_cmp : Word))
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_p_be : Word)) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 48 : Word)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        ((.x6 : Reg) ↦ᵣ
          (if beBytesToNat xs < beBytesToNat secp256k1PBytes then (1 : Word) else (0 : Word))) **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs **
        globalConst (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes **
        ((GuestAddrs.secf_cmp : Word) ↦ₘ
          (if beBytesToNat xs < beBytesToNat secp256k1PBytes then (1 : Word) else (0 : Word)))) := by
  have hpre := ltSetupCall_spec src dst ret v8 v9 v12 xs hlenX halignX hovX hvalidX
  have hload := cmpLoad_spec
    (if beBytesToNat xs < beBytesToNat secp256k1PBytes then (1 : Word) else (0 : Word))
    src dst (GuestAddrs.secp256k1_p_be : Word)
    (GuestAddrs.secf_reduce_once + 48 : Word) xs
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hpre hload
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_mono_nSteps (by omega) hc)

private theorem cmpBranch_spec (flag src dst pPtr ret : Word)
    (xs : List (BitVec 8)) :
    cpsBranchWithin 1 (GuestAddrs.secf_reduce_once + 60 : Word) secfReduceOnceCr
      (((.x6 : Reg) ↦ᵣ flag) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ pPtr) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        ((.x1 : Reg) ↦ᵣ ret) **
        ((.x5 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs ** globalConst pPtr secp256k1PBytes **
        ((GuestAddrs.secf_cmp : Word) ↦ₘ flag))
      (GuestAddrs.secf_reduce_once + 92 : Word)
      (((.x6 : Reg) ↦ᵣ flag) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ⌜flag ≠ 0⌝ **
        ((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ pPtr) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        ((.x1 : Reg) ↦ᵣ ret) **
        ((.x5 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs ** globalConst pPtr secp256k1PBytes **
        ((GuestAddrs.secf_cmp : Word) ↦ₘ flag))
      (GuestAddrs.secf_reduce_once + 64 : Word)
      (((.x6 : Reg) ↦ᵣ flag) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ⌜flag = 0⌝ **
        ((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ pPtr) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        ((.x1 : Reg) ↦ᵣ ret) **
        ((.x5 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs ** globalConst pPtr secp256k1PBytes **
        ((GuestAddrs.secf_cmp : Word) ↦ₘ flag)) := by
  unfold globalConst
  have hbr := cpsBranchWithin_frameR
    (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ pPtr) **
      ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
      ((.x1 : Reg) ↦ᵣ ret) **
      ((.x5 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
      bytesRegion src xs ** bytesRegion pPtr secp256k1PBytes **
      ((GuestAddrs.secf_cmp : Word) ↦ₘ flag))
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := secfReduceOnceCr)
      (h := bne_spec_gen_within .x6 .x0 (32 : BitVec 13) flag (0 : Word)
        (GuestAddrs.secf_reduce_once + 60 : Word))
      (hmono := by unfold secfReduceOnceCr; code_mem))
  rw [show (GuestAddrs.secf_reduce_once + 60 : Word) + signExtend13 (32 : BitVec 13) =
        (GuestAddrs.secf_reduce_once + 92 : Word) from by
        rw [show signExtend13 (32 : BitVec 13) = (32 : Word) from by decide]
        decide,
      show (GuestAddrs.secf_reduce_once + 60 : Word) + 4 =
        (GuestAddrs.secf_reduce_once + 64 : Word) from by decide] at hbr
  exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    (fun _ hq => by xperm_hyp hq) hbr

theorem ltSetupCallLoadBranch_spec (src dst ret v8 v9 v12 : Word)
    (xs : List (BitVec 8))
    (hlenX : xs.length = 32)
    (halignX : src.toNat % 8 = 0)
    (hovX : src.toNat + 32 < 2 ^ 64)
    (hvalidX : ∀ k, k < 32 → isValidByteAccess (src + BitVec.ofNat 64 k) = true) :
    cpsBranchWithin 307 (GuestAddrs.secf_reduce_once + 16 : Word) secfReduceOnceCr
      (((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) **
        ((.x12 : Reg) ↦ᵣ v12) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs **
        globalConst (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes **
        memOwn (GuestAddrs.secf_cmp : Word))
      (GuestAddrs.secf_reduce_once + 92 : Word)
      (((.x6 : Reg) ↦ᵣ
          (if beBytesToNat xs < beBytesToNat secp256k1PBytes then (1 : Word) else (0 : Word))) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ⌜(if beBytesToNat xs < beBytesToNat secp256k1PBytes then (1 : Word) else (0 : Word)) ≠ 0⌝ **
        ((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_p_be : Word)) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 48 : Word)) **
        ((.x5 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs **
        globalConst (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes **
        ((GuestAddrs.secf_cmp : Word) ↦ₘ
          (if beBytesToNat xs < beBytesToNat secp256k1PBytes then (1 : Word) else (0 : Word))))
      (GuestAddrs.secf_reduce_once + 64 : Word)
      (((.x6 : Reg) ↦ᵣ
          (if beBytesToNat xs < beBytesToNat secp256k1PBytes then (1 : Word) else (0 : Word))) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ⌜(if beBytesToNat xs < beBytesToNat secp256k1PBytes then (1 : Word) else (0 : Word)) = 0⌝ **
        ((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_p_be : Word)) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 48 : Word)) **
        ((.x5 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs **
        globalConst (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes **
        ((GuestAddrs.secf_cmp : Word) ↦ₘ
          (if beBytesToNat xs < beBytesToNat secp256k1PBytes then (1 : Word) else (0 : Word)))) := by
  let flag : Word := if beBytesToNat xs < beBytesToNat secp256k1PBytes then (1 : Word) else (0 : Word)
  have hpre := ltSetupCallLoad_spec src dst ret v8 v9 v12 xs hlenX halignX hovX hvalidX
  have hbr := cmpBranch_spec flag src dst (GuestAddrs.secp256k1_p_be : Word)
    (GuestAddrs.secf_reduce_once + 48 : Word) xs
  exact cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr (fun _ hp => by xperm_hyp hp) hpre hbr

/-- Registers owned across the `secf_copy32` call, excluding `a0`/`a1`. -/
def copyScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x12, .x13, .x14, .x15, .x16, .x17]

/-- Copy scratch registers other than `t0`, which the copy leaf uses directly. -/
def copyRest : List Reg :=
  [.x6, .x7, .x28, .x29, .x30, .x31, .x12, .x13, .x14, .x15, .x16, .x17]

/-- Registers owned across the `u256_sub_be` call, excluding `a0`/`a1`/`a2`. -/
def subScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x13, .x14, .x15, .x16, .x17]

/-- Exposed registers preserved after the branch tail, excluding return register `a0`. -/
def retScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem x10_notin_retScratch : (.x10 : Reg) ∉ retScratch := by decide

private theorem copyScratch_eq_x5_rest :
    regOwns copyScratch = (regOwn .x5 ** regOwns copyRest) := by
  simp only [copyScratch, copyRest, regOwns_cons, regOwns_nil]

private theorem x11_copyScratch_to_retScratch (dst : Word) :
    ∀ h, (((.x11 : Reg) ↦ᵣ dst) ** regOwns copyScratch) h → regOwns retScratch h := by
  intro h hp
  rw [copyScratch_eq_x5_rest] at hp
  have hp1 : (regOwn .x11 ** (regOwn .x5 ** regOwns copyRest)) h := by
    exact sepConj_mono_left (regIs_to_regOwn .x11 dst) h hp
  simp only [retScratch, copyRest, regOwns_cons, regOwns_nil, sepConj_emp_right'] at hp1 ⊢
  xperm_hyp hp1

/-- High exposed scratch registers not materialized by the compare prefix. -/
def highScratch : List Reg := [.x31, .x13, .x14, .x15, .x16, .x17]

theorem branchScratch_to_subScratch (v5 v6 : Word) :
    ∀ h, (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwns highScratch) h →
      regOwns subScratch h := by
  intro h hp
  have hp1 : (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwns highScratch) h := by
    exact sepConj_mono
      (regIs_to_regOwn .x5 v5)
      (sepConj_mono (regIs_to_regOwn .x6 v6) (fun _ hh => hh)) h hp
  simp only [subScratch, highScratch, regOwns_cons, regOwns_nil, sepConj_emp_right'] at hp1 ⊢
  xperm_hyp hp1

theorem branchScratch_to_copyScratch (v5 v6 v12 : Word) :
    ∀ h, (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
      ((.x12 : Reg) ↦ᵣ v12) ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwns highScratch) h → regOwns copyScratch h := by
  intro h hp
  have hp1 : (regOwn .x5 ** regOwn .x6 ** regOwn .x12 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwns highScratch) h := by
    exact sepConj_mono
      (regIs_to_regOwn .x5 v5)
      (sepConj_mono (regIs_to_regOwn .x6 v6)
        (sepConj_mono (regIs_to_regOwn .x12 v12) (fun _ hh => hh))) h hp
  simp only [copyScratch, highScratch, regOwns_cons, regOwns_nil, sepConj_emp_right'] at hp1 ⊢
  xperm_hyp hp1

private theorem x10_notin_copyScratch : (.x10 : Reg) ∉ copyScratch := by decide
private theorem x11_notin_copyScratch : (.x11 : Reg) ∉ copyScratch := by decide
private theorem x10_notin_subScratch : (.x10 : Reg) ∉ subScratch := by decide
private theorem x11_notin_subScratch : (.x11 : Reg) ∉ subScratch := by decide
private theorem x12_notin_subScratch : (.x12 : Reg) ∉ subScratch := by decide

/-- Split the exposed register file around return register `a0`. -/
private theorem exposedRegs_split_ret (vf : Reg → Word) :
    regAtomsOf vf exposedRegs = ((.x10 ↦ᵣ vf .x10) ** regAtomsOf vf retScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [retScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

/-- Split the exposed register file around `secf_copy32`'s argument registers. -/
private theorem exposedRegs_split_copy (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** regAtomsOf vf copyScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [copyScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

/-- Split the exposed register file around `u256_sub_be`'s argument registers. -/
private theorem exposedRegs_split_sub (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) **
          (.x12 ↦ᵣ vf .x12) ** regAtomsOf vf subScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [subScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem secfCopy32Direct_spec (ret src dst : Word)
    (srcBytes orig : List (BitVec 8))
    (hlenSrc : srcBytes.length = 32) (hlenOrig : orig.length = 32)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 9 (GuestAddrs.secf_copy32 : Word) ret secfReduceOnceCr
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) **
        regOwn .x5 ** bytesRegion src srcBytes ** bytesRegion dst orig)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) **
        regOwn .x5 ** bytesRegion src srcBytes ** bytesRegion dst srcBytes) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) **
        bytesRegion src srcBytes ** bytesRegion dst orig)
      (fun tv => ?_))
  have hcopy0 := selectedDwordCopy_spec .x10 .x11 .x5 (by decide)
    src dst tv srcBytes orig 0 4 (by omega) (by omega) (by decide)
    (GuestAddrs.secf_copy32 : Word)
  rw [show (GuestAddrs.secf_copy32 : Word) + BitVec.ofNat 64 (4 * (2 * 4)) =
      (GuestAddrs.secf_copy32 + 32 : Word) from by decide,
    copyDwords_covers srcBytes orig 4 (by omega) (by omega)] at hcopy0
  have hcopy := liftCode (cr' := secfReduceOnceCr) hcopy0
    (by unfold secfReduceOnceCr; code_mem)
  have hcopyF := cpsTripleWithin_frameR (((.x1 : Reg) ↦ᵣ ret)) (by pcf) hcopy
  have hret0 := EvmAsm.Evm64.ret_spec_within' (GuestAddrs.secf_copy32 + 32 : Word) ret
  rw [halign] at hret0
  have hret := liftCode (cr' := secfReduceOnceCr) hret0
    (by unfold secfReduceOnceCr; code_mem)
  have hretF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) ** regOwn .x5 **
      bytesRegion src srcBytes ** bytesRegion dst srcBytes)
    (by pcf) hret
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hcopyF hretF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hc

private theorem copySetup_spec (src dst ret old10 old11 : Word) :
    cpsTripleWithin 2 (GuestAddrs.secf_reduce_once + 92 : Word)
      (GuestAddrs.secf_reduce_once + 100 : Word) secfReduceOnceCr
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ old10) ** ((.x11 : Reg) ↦ᵣ old11) **
        ((.x1 : Reg) ↦ᵣ ret))
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) **
        ((.x1 : Reg) ↦ᵣ ret)) := by
  have hmv10 := liftCode (cr' := secfReduceOnceCr)
    (mv_spec_gen_within .x10 .x8 src old10 (GuestAddrs.secf_reduce_once + 92 : Word)
      (by decide))
    (by unfold secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_reduce_once + 92 : Word) + 4 =
      (GuestAddrs.secf_reduce_once + 96 : Word) from by decide] at hmv10
  have hmv11 := liftCode (cr' := secfReduceOnceCr)
    (mv_spec_gen_within .x11 .x9 dst old11 (GuestAddrs.secf_reduce_once + 96 : Word)
      (by decide))
    (by unfold secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_reduce_once + 96 : Word) + 4 =
      (GuestAddrs.secf_reduce_once + 100 : Word) from by decide] at hmv11
  have hmv10F := cpsTripleWithin_frameR
    (((.x9 : Reg) ↦ᵣ dst) ** ((.x11 : Reg) ↦ᵣ old11) ** ((.x1 : Reg) ↦ᵣ ret))
    (by pcf) hmv10
  have hmv11F := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ src) ** ((.x10 : Reg) ↦ᵣ src) ** ((.x1 : Reg) ↦ᵣ ret))
    (by pcf) hmv11
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hmv10F hmv11F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hc

private theorem copySetupCall_spec (src dst ret old10 old11 : Word)
    (xs orig : List (BitVec 8))
    (hlenX : xs.length = 32) (hlenOrig : orig.length = 32)
    (halignRet : ((GuestAddrs.secf_reduce_once + 104 : Word) &&& ~~~(1 : Word)) =
      (GuestAddrs.secf_reduce_once + 104 : Word)) :
    cpsTripleWithin (2 + (1 + 9)) (GuestAddrs.secf_reduce_once + 92 : Word)
      (GuestAddrs.secf_reduce_once + 104 : Word) secfReduceOnceCr
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ old10) ** ((.x11 : Reg) ↦ᵣ old11) **
        ((.x1 : Reg) ↦ᵣ ret) ** regOwn .x5 ** bytesRegion src xs ** bytesRegion dst orig)
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 104 : Word)) **
        ((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) **
        regOwn .x5 ** bytesRegion src xs ** bytesRegion dst xs) := by
  have hsetup := copySetup_spec src dst ret old10 old11
  have hsetupF := cpsTripleWithin_frameR
    (regOwn .x5 ** bytesRegion src xs ** bytesRegion dst orig) (by pcf) hsetup
  have hcallee0 := secfCopy32Direct_spec (GuestAddrs.secf_reduce_once + 104 : Word)
    src dst xs orig hlenX hlenOrig halignRet
  have hcallee : cpsTripleWithin 9 (GuestAddrs.secf_copy32 : Word)
      (GuestAddrs.secf_reduce_once + 104 : Word) secfReduceOnceCr
      (((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 104 : Word)) **
        (((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) **
          regOwn .x5 ** bytesRegion src xs ** bytesRegion dst orig))
      (((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 104 : Word)) **
        (((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) **
          regOwn .x5 ** bytesRegion src xs ** bytesRegion dst xs)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcallee0
  have hcall := callWithin_spec (cr := secfReduceOnceCr)
    (P := (((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) **
      regOwn .x5 ** bytesRegion src xs ** bytesRegion dst orig))
    (Q := (((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) **
      regOwn .x5 ** bytesRegion src xs ** bytesRegion dst xs))
    (GuestAddrs.secf_reduce_once + 100 : Word) (GuestAddrs.secf_copy32 : Word) ret
    (jalOff GuestAddrs.secf_copy32 (GuestAddrs.secf_reduce_once + 100)) 9
    (by decide) (by unfold secfReduceOnceCr; code_mem) (by pcf) hcallee
  rw [show (GuestAddrs.secf_reduce_once + 100 : Word) + 4 =
      (GuestAddrs.secf_reduce_once + 104 : Word) from by decide] at hcall
  have hcallF := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst)) (by pcf) hcall
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsetupF hcallF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hc

private theorem copySetupCallFull_spec (src dst ret old10 old11 : Word)
    (xs orig : List (BitVec 8))
    (hlenX : xs.length = 32) (hlenOrig : orig.length = 32) :
    cpsTripleWithin (2 + (1 + 9)) (GuestAddrs.secf_reduce_once + 92 : Word)
      (GuestAddrs.secf_reduce_once + 104 : Word) secfReduceOnceCr
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ old10) ** ((.x11 : Reg) ↦ᵣ old11) **
        ((.x1 : Reg) ↦ᵣ ret) ** regOwns copyScratch **
        bytesRegion src xs ** bytesRegion dst orig)
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 104 : Word)) **
        ((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) **
        regOwns copyScratch ** bytesRegion src xs ** bytesRegion dst xs) := by
  have hbase := copySetupCall_spec src dst ret old10 old11 xs orig hlenX hlenOrig (by decide)
  have hbaseF := cpsTripleWithin_frameR (regOwns copyRest) (by pcf) hbase
  exact cpsTripleWithin_weaken (fun _ hp => by
      rw [copyScratch_eq_x5_rest] at hp
      xperm_hyp hp)
    (fun _ hq => by
      rw [copyScratch_eq_x5_rest]
      xperm_hyp hq) hbaseF

private theorem copyRetTail_spec (P : Assertion) (hP : P.pcFree) (src dst : Word) :
    cpsTripleWithin 1 (GuestAddrs.secf_reduce_once + 104 : Word)
      (GuestAddrs.secf_reduce_once + 108 : Word) secfReduceOnceCr
      ((((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 104 : Word)) **
        ((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) ** regOwns copyScratch) ** P)
      ((((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 104 : Word)) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwns retScratch) ** P) := by
  have hli := liftCode (cr' := secfReduceOnceCr)
    (li_spec_gen_within .x10 src (0 : Word) (GuestAddrs.secf_reduce_once + 104 : Word)
      (by decide))
    (by unfold secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_reduce_once + 104 : Word) + 4 =
      (GuestAddrs.secf_reduce_once + 108 : Word) from by decide] at hli
  have hliF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 104 : Word)) **
      ((.x11 : Reg) ↦ᵣ dst) ** regOwns copyScratch ** P)
    (by
      apply pcFree_sepConj
      · exact pcFree_regIs
      · apply pcFree_sepConj
        · exact pcFree_regIs
        · exact pcFree_sepConj (by pcf) hP) hli
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      have hq1 : ((((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 104 : Word)) **
          ((.x10 : Reg) ↦ᵣ (0 : Word)) **
          (((.x11 : Reg) ↦ᵣ dst) ** regOwns copyScratch)) ** P) h := by
        xperm_hyp hq
      exact sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (x11_copyScratch_to_retScratch dst))) h hq1) hliF

theorem copyArm_spec (src dst ret old10 old11 : Word)
    (xs orig : List (BitVec 8))
    (hlenX : xs.length = 32) (hlenOrig : orig.length = 32) :
    cpsTripleWithin ((2 + (1 + 9)) + 1) (GuestAddrs.secf_reduce_once + 92 : Word)
      (GuestAddrs.secf_reduce_once + 108 : Word) secfReduceOnceCr
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ old10) ** ((.x11 : Reg) ↦ᵣ old11) **
        ((.x1 : Reg) ↦ᵣ ret) ** regOwns copyScratch **
        bytesRegion src xs ** bytesRegion dst orig)
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 104 : Word)) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwns retScratch **
        bytesRegion src xs ** bytesRegion dst xs) := by
  have hcall := copySetupCallFull_spec src dst ret old10 old11 xs orig hlenX hlenOrig
  have htail := copyRetTail_spec
    (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
      bytesRegion src xs ** bytesRegion dst xs) (by pcf) src dst
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hcall htail
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hc

private theorem secfCopy32FlatAsrt_spec (ret src dst : Word)
    (srcBytes orig : List (BitVec 8)) (rf : RegFile)
    (hwf : (Region.mk src srcBytes).wf) (hrww : RwRegion.wf ⟨dst, 32⟩)
    (hlenOrig : orig.length = 32)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hpre : Secp256k1FieldLeavesSAsm.secfCopy32Fn src dst srcBytes orig |>.pre rf orig empAssertion) :
    cpsTripleWithin ((Secp256k1FieldLeavesSAsm.secfCopy32Fn src dst srcBytes orig).body.steps + 1)
      (GuestAddrs.secf_copy32 : Word) ret secfReduceOnceCr
      (((((.x1 : Reg) ↦ᵣ ret) ** regFileIs rf ** bytesRegion dst orig)
        ** empAssertion) ** bytesRegion src srcBytes)
      ((((.x1 : Reg) ↦ᵣ ret) **
        asrtOf ⟨dst, 32⟩
          (Secp256k1FieldLeavesSAsm.secfCopy32Fn src dst srcBytes orig |>.post))
        ** bytesRegion src srcBytes) := by
  have had := retSpecFlatAmbient
    (Secp256k1FieldLeavesSAsm.secfCopy32Fn src dst srcBytes orig)
    (GuestAddrs.secf_copy32 : Word)
    (Secp256k1FieldLeavesSAsm.secfCopy32Fn_spec src dst srcBytes orig hwf hrww
      (GuestAddrs.secf_copy32 : Word))
    (by show 4 * (8 + 1) ≤ 2 ^ 64; decide) ret halign rf orig empAssertion
    (by exact hlenOrig) (by pcf) hpre
    (Q := asrtOf ⟨dst, 32⟩
      (Secp256k1FieldLeavesSAsm.secfCopy32Fn src dst srcBytes orig |>.post))
    (fun rf' ws' A' hlen hApc hpost hp hh => ⟨rf', ws', A', hlen, hApc, hpost, hh⟩)
  rw [show (Secp256k1FieldLeavesSAsm.secfCopy32Fn src dst srcBytes orig).programRet
      (GuestAddrs.secf_copy32 : Word) = secfCopy32_prog from rfl] at had
  exact liftCode (cr' := secfReduceOnceCr) had (by unfold secfReduceOnceCr; code_mem)

private theorem u256SubBeFlat_spec (ret aPtr bPtr outPtr : Word)
    (aBytes bBytes orig : List (BitVec 8))
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroA : Region.wf ⟨aPtr, aBytes⟩) (hroB : Region.wf ⟨bPtr, bBytes⟩)
    (hlenA : aBytes.length = 32) (hlenB : bBytes.length = 32) (hlenOrig : orig.length = 32)
    (hovA : aPtr.toNat + 32 < 2 ^ 64) (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisjA : aPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ aPtr.toNat)
    (hdisjB : bPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ bPtr.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((U256SubBeSAsm.u256SubBeFn aPtr bPtr outPtr aBytes bBytes orig).body.steps + 1)
      (GuestAddrs.u256_sub_be : Word) ret secfReduceOnceCr
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns subScratch ** bytesRegion outPtr orig **
        bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes)
      (((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs **
        bytesRegion outPtr (U256SubBeSAsm.u256SubBeBytes aBytes bBytes orig) **
        bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns subScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ aPtr) **
        ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        bytesRegion outPtr orig ** bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes)
      (fun vf => ?_))
  have hpre : U256SubBeSAsm.u256SubBePre aPtr bPtr outPtr aBytes bBytes orig
      (fun r => if r = .x10 then aPtr else if r = .x11 then bPtr else if r = .x12 then outPtr else vf r)
      orig (bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes) := by
    refine ⟨?_, ?_, ?_, rfl, hlenA, hlenB, hlenOrig, hovA, hovB, hovOut, hdisjA, hdisjB, rfl⟩
    · show RegFile.get _ .x10 = aPtr
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = bPtr
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
    · show RegFile.get _ .x12 = outPtr
      rw [RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x12 : Reg) ≠ .x10),
        if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
      exact if_pos rfl
  have had := retSpecFlatAmbient
    (U256SubBeSAsm.u256SubBeFn aPtr bPtr outPtr aBytes bBytes orig)
    (GuestAddrs.u256_sub_be : Word)
    (U256SubBeSAsm.u256SubBe_spec aPtr bPtr outPtr aBytes bBytes orig hrw hroA hroB
      (GuestAddrs.u256_sub_be : Word))
    (by show 4 * (16 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then aPtr else if r = .x11 then bPtr else if r = .x12 then outPtr else vf r)
    orig (bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes)
    (by exact hlenOrig) (by pcf) hpre
    (Q := (regOwns exposedRegs ** bytesRegion outPtr (U256SubBeSAsm.u256SubBeBytes aBytes bBytes orig)) **
      (bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes))
    (fun rf' ws' A' hlen hApc hpost hp hh => by
      obtain ⟨_, _, _, hws, hA⟩ := hpost
      subst ws'
      subst A'
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
      exact sepConj_mono_left
        (sepConj_mono_left (regAtomsOf_to_regOwns (fun r => rf' r) exposedRegs)) hp hh)
  rw [show (U256SubBeSAsm.u256SubBeFn aPtr bPtr outPtr aBytes bBytes orig).programRet
      (GuestAddrs.u256_sub_be : Word) = u256SubBe_prog from rfl] at had
  have hadC := liftCode (cr' := secfReduceOnceCr) had (by unfold secfReduceOnceCr; code_mem)
  rw [show (U256SubBeSAsm.u256SubBeFn aPtr bPtr outPtr aBytes bBytes orig).region = Region.empty from rfl,
      show (U256SubBeSAsm.u256SubBeFn aPtr bPtr outPtr aBytes bBytes orig).rw.base = outPtr from rfl,
      show Region.empty.base = (0 : Word) from rfl,
      show Region.empty.bytes = ([] : List (BitVec 8)) from rfl,
      bytesRegion_nil] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_sub,
    show (if (Reg.x10 : Reg) = .x10 then aPtr else
        if (Reg.x10 : Reg) = .x11 then bPtr else if (Reg.x10 : Reg) = .x12 then outPtr else vf .x10) = aPtr from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then aPtr else
        if (Reg.x11 : Reg) = .x11 then bPtr else if (Reg.x11 : Reg) = .x12 then outPtr else vf .x11) = bPtr from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    show (if (Reg.x12 : Reg) = .x10 then aPtr else
        if (Reg.x12 : Reg) = .x11 then bPtr else if (Reg.x12 : Reg) = .x12 then outPtr else vf .x12) = outPtr from by
      rw [if_neg (by decide : ¬ ((Reg.x12 : Reg) = .x10)),
        if_neg (by decide : ¬ ((Reg.x12 : Reg) = .x11))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then aPtr else if r = .x11 then bPtr else if r = .x12 then outPtr else vf r)
      vf subScratch
      (fun r hr => by
        show (if r = .x10 then aPtr else if r = .x11 then bPtr else if r = .x12 then outPtr else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_subScratch (hc ▸ hr)),
            if_neg (fun (hc : r = .x11) => x11_notin_subScratch (hc ▸ hr)),
            if_neg (fun (hc : r = .x12) => x12_notin_subScratch (hc ▸ hr))])]
    at hadC
  exact cpsTripleWithin_weaken (fun h hp => by
      have hp1 : ((((.x1 : Reg) ↦ᵣ ret) **
            (((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
              ((.x12 : Reg) ↦ᵣ outPtr) ** regAtomsOf vf subScratch) **
            bytesRegion outPtr orig) **
          bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes) h := by
        xperm_hyp hp
      have hp2 : (((((.x1 : Reg) ↦ᵣ ret) **
              (((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
                ((.x12 : Reg) ↦ᵣ outPtr) ** regAtomsOf vf subScratch) **
              bytesRegion outPtr orig) **
            bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes) ** empAssertion) h := by
        rw [sepConj_emp_right']
        exact hp1
      exact hp2)
    (fun h hq => by
      rw [sepConj_emp_right'] at hq
      xperm_hyp hq) hadC

private theorem subSetup_spec (src dst ret old10 old11 old12 : Word) :
    cpsTripleWithin 4 (GuestAddrs.secf_reduce_once + 64 : Word)
      (GuestAddrs.secf_reduce_once + 80 : Word) secfReduceOnceCr
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ old10) ** ((.x11 : Reg) ↦ᵣ old11) **
        ((.x12 : Reg) ↦ᵣ old12) ** ((.x1 : Reg) ↦ᵣ ret))
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ src) **
        ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_p_be : Word)) **
        ((.x12 : Reg) ↦ᵣ dst) ** ((.x1 : Reg) ↦ᵣ ret)) := by
  have hmv10 := liftCode (cr' := secfReduceOnceCr)
    (mv_spec_gen_within .x10 .x8 src old10 (GuestAddrs.secf_reduce_once + 64 : Word)
      (by decide))
    (by unfold secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_reduce_once + 64 : Word) + 4 =
      (GuestAddrs.secf_reduce_once + 68 : Word) from by decide] at hmv10
  have hlaP := la_materialize_within .x11 old11
    (GuestAddrs.secf_reduce_once + 68 : Word) (GuestAddrs.secp256k1_p_be : Word)
    (cr := secfReduceOnceCr) (by decide) (by decide)
    (by unfold secfReduceOnceCr; code_mem) (by unfold secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_reduce_once + 68 : Word) + 8 =
      (GuestAddrs.secf_reduce_once + 76 : Word) from by decide] at hlaP
  have hmv12 := liftCode (cr' := secfReduceOnceCr)
    (mv_spec_gen_within .x12 .x9 dst old12 (GuestAddrs.secf_reduce_once + 76 : Word)
      (by decide))
    (by unfold secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_reduce_once + 76 : Word) + 4 =
      (GuestAddrs.secf_reduce_once + 80 : Word) from by decide] at hmv12
  have hmv10F := cpsTripleWithin_frameR
    (((.x9 : Reg) ↦ᵣ dst) ** ((.x11 : Reg) ↦ᵣ old11) **
      ((.x12 : Reg) ↦ᵣ old12) ** ((.x1 : Reg) ↦ᵣ ret))
    (by pcf) hmv10
  have hlaPF := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
      ((.x10 : Reg) ↦ᵣ src) ** ((.x12 : Reg) ↦ᵣ old12) **
      ((.x1 : Reg) ↦ᵣ ret))
    (by pcf) hlaP
  have hmv12F := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ src) ** ((.x10 : Reg) ↦ᵣ src) **
      ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_p_be : Word)) **
      ((.x1 : Reg) ↦ᵣ ret))
    (by pcf) hmv12
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hmv10F hlaPF
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 hmv12F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c2

private theorem subSetupCall_spec (src dst ret old10 old11 old12 : Word)
    (xs orig : List (BitVec 8))
    (hroX : Region.wf ⟨src, xs⟩)
    (hrwDst : RwRegion.wf ⟨dst, 32⟩)
    (hlenX : xs.length = 32) (hlenOrig : orig.length = 32)
    (hovX : src.toNat + 32 < 2 ^ 64)
    (hovDst : dst.toNat + 32 < 2 ^ 64)
    (hdisjX : src.toNat + 32 ≤ dst.toNat ∨ dst.toNat + 32 ≤ src.toNat)
    (hdisjP : (GuestAddrs.secp256k1_p_be : Word).toNat + 32 ≤ dst.toNat ∨
      dst.toNat + 32 ≤ (GuestAddrs.secp256k1_p_be : Word).toNat) :
    cpsTripleWithin (4 + (1 + ((U256SubBeSAsm.u256SubBeFn src
        (GuestAddrs.secp256k1_p_be : Word) dst xs secp256k1PBytes orig).body.steps + 1)))
      (GuestAddrs.secf_reduce_once + 64 : Word)
      (GuestAddrs.secf_reduce_once + 84 : Word) secfReduceOnceCr
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ old10) ** ((.x11 : Reg) ↦ᵣ old11) **
        ((.x12 : Reg) ↦ᵣ old12) ** ((.x1 : Reg) ↦ᵣ ret) **
        regOwns subScratch ** bytesRegion dst orig ** bytesRegion src xs **
        globalConst (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes)
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 84 : Word)) **
        regOwns exposedRegs **
        bytesRegion dst (U256SubBeSAsm.u256SubBeBytes xs secp256k1PBytes orig) **
        bytesRegion src xs **
        globalConst (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes) := by
  unfold globalConst
  have hsetup := subSetup_spec src dst ret old10 old11 old12
  have hsetupF := cpsTripleWithin_frameR
    (regOwns subScratch ** bytesRegion dst orig ** bytesRegion src xs **
      bytesRegion (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes)
    (by pcf) hsetup
  have hcallee0 := u256SubBeFlat_spec (GuestAddrs.secf_reduce_once + 84 : Word)
    src (GuestAddrs.secp256k1_p_be : Word) dst xs secp256k1PBytes orig
    hrwDst hroX (by decide) hlenX (by decide) hlenOrig hovX (by decide) hovDst
    hdisjX hdisjP (by decide)
  have hcallee : cpsTripleWithin
      ((U256SubBeSAsm.u256SubBeFn src (GuestAddrs.secp256k1_p_be : Word) dst xs secp256k1PBytes orig).body.steps + 1)
      (GuestAddrs.u256_sub_be : Word) (GuestAddrs.secf_reduce_once + 84 : Word)
      secfReduceOnceCr
      (((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 84 : Word)) **
        (((.x10 : Reg) ↦ᵣ src) **
          ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_p_be : Word)) **
          ((.x12 : Reg) ↦ᵣ dst) ** regOwns subScratch **
          bytesRegion dst orig ** bytesRegion src xs **
          bytesRegion (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes))
      (((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 84 : Word)) **
        (regOwns exposedRegs **
          bytesRegion dst (U256SubBeSAsm.u256SubBeBytes xs secp256k1PBytes orig) **
          bytesRegion src xs ** bytesRegion (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcallee0
  have hcall := callWithin_spec (cr := secfReduceOnceCr)
    (P := (((.x10 : Reg) ↦ᵣ src) **
          ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_p_be : Word)) **
          ((.x12 : Reg) ↦ᵣ dst) ** regOwns subScratch **
          bytesRegion dst orig ** bytesRegion src xs **
          bytesRegion (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes))
    (Q := (regOwns exposedRegs **
          bytesRegion dst (U256SubBeSAsm.u256SubBeBytes xs secp256k1PBytes orig) **
          bytesRegion src xs ** bytesRegion (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes))
    (GuestAddrs.secf_reduce_once + 80 : Word) (GuestAddrs.u256_sub_be : Word) ret
    (jalOff GuestAddrs.u256_sub_be (GuestAddrs.secf_reduce_once + 80))
    ((U256SubBeSAsm.u256SubBeFn src (GuestAddrs.secp256k1_p_be : Word) dst xs secp256k1PBytes orig).body.steps + 1)
    (by decide) (by unfold secfReduceOnceCr; code_mem) (by pcf) hcallee
  rw [show (GuestAddrs.secf_reduce_once + 80 : Word) + 4 =
      (GuestAddrs.secf_reduce_once + 84 : Word) from by decide] at hcall
  have hcallF := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst)) (by pcf) hcall
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsetupF hcallF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hc

private theorem subRetTail_spec (P : Assertion) (hP : P.pcFree) :
    cpsTripleWithin 2 (GuestAddrs.secf_reduce_once + 84 : Word)
      (GuestAddrs.secf_reduce_once + 108 : Word) secfReduceOnceCr
      ((((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 84 : Word)) **
        regOwns exposedRegs) ** P)
      ((((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 84 : Word)) **
        ((.x10 : Reg) ↦ᵣ (1 : Word)) ** regOwns retScratch) ** P) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns exposedRegs (by decide)
      (P := ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 84 : Word)) ** P)
      (fun vf => ?_))
  have hli := liftCode (cr' := secfReduceOnceCr)
    (li_spec_gen_within .x10 (vf .x10) (1 : Word)
      (GuestAddrs.secf_reduce_once + 84 : Word) (by decide))
    (by unfold secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_reduce_once + 84 : Word) + 4 =
      (GuestAddrs.secf_reduce_once + 88 : Word) from by decide] at hli
  have hjal := cpsTripleWithin_extend_code (cr' := secfReduceOnceCr)
    (h := jal_x0_spec_gen_within (20 : BitVec 21)
      (GuestAddrs.secf_reduce_once + 88 : Word))
    (hmono := by unfold secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_reduce_once + 88 : Word) + signExtend21 (20 : BitVec 21) =
      (GuestAddrs.secf_reduce_once + 108 : Word) from by
        rw [show signExtend21 (20 : BitVec 21) = (20 : Word) from by decide]
        decide] at hjal
  have hliF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 84 : Word)) **
      regAtomsOf vf retScratch ** P)
    (by exact pcFree_sepConj (by pcf) (pcFree_sepConj (pcFree_regAtomsOf vf retScratch) hP)) hli
  have hjalF0 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 84 : Word)) **
      ((.x10 : Reg) ↦ᵣ (1 : Word)) ** regAtomsOf vf retScratch ** P)
    (by
      apply pcFree_sepConj
      · exact pcFree_regIs
      · apply pcFree_sepConj
        · exact pcFree_regIs
        · exact pcFree_sepConj (pcFree_regAtomsOf vf retScratch) hP) hjal
  have hjalF : cpsTripleWithin 1 (GuestAddrs.secf_reduce_once + 88 : Word)
      (GuestAddrs.secf_reduce_once + 108 : Word) secfReduceOnceCr
      (((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 84 : Word)) **
        ((.x10 : Reg) ↦ᵣ (1 : Word)) ** regAtomsOf vf retScratch ** P)
      (((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 84 : Word)) **
        ((.x10 : Reg) ↦ᵣ (1 : Word)) ** regAtomsOf vf retScratch ** P) := by
    exact cpsTripleWithin_weaken (fun h hp => by
        have hp1 : (empAssertion ** (((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 84 : Word)) **
            ((.x10 : Reg) ↦ᵣ (1 : Word)) ** regAtomsOf vf retScratch ** P)) h := by
          rw [sepConj_emp_left']
          exact hp
        exact hp1)
      (fun h hq => by
        rw [sepConj_emp_left'] at hq
        exact hq) hjalF0
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hliF hjalF
  exact cpsTripleWithin_weaken (fun _ hp => by
      rw [exposedRegs_split_ret] at hp
      xperm_hyp hp)
    (fun h hq => by
      have hq1 : ((((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 84 : Word)) **
          ((.x10 : Reg) ↦ᵣ (1 : Word)) ** regAtomsOf vf retScratch) ** P) h := by
        xperm_hyp hq
      exact sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (regAtomsOf_to_regOwns vf retScratch))) h hq1) hc

theorem subArm_spec (src dst ret old10 old11 old12 : Word)
    (xs orig : List (BitVec 8))
    (hroX : Region.wf ⟨src, xs⟩)
    (hrwDst : RwRegion.wf ⟨dst, 32⟩)
    (hlenX : xs.length = 32) (hlenOrig : orig.length = 32)
    (hovX : src.toNat + 32 < 2 ^ 64)
    (hovDst : dst.toNat + 32 < 2 ^ 64)
    (hdisjX : src.toNat + 32 ≤ dst.toNat ∨ dst.toNat + 32 ≤ src.toNat)
    (hdisjP : (GuestAddrs.secp256k1_p_be : Word).toNat + 32 ≤ dst.toNat ∨
      dst.toNat + 32 ≤ (GuestAddrs.secp256k1_p_be : Word).toNat) :
    cpsTripleWithin ((4 + (1 + ((U256SubBeSAsm.u256SubBeFn src
        (GuestAddrs.secp256k1_p_be : Word) dst xs secp256k1PBytes orig).body.steps + 1))) + 2)
      (GuestAddrs.secf_reduce_once + 64 : Word)
      (GuestAddrs.secf_reduce_once + 108 : Word) secfReduceOnceCr
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ old10) ** ((.x11 : Reg) ↦ᵣ old11) **
        ((.x12 : Reg) ↦ᵣ old12) ** ((.x1 : Reg) ↦ᵣ ret) **
        regOwns subScratch ** bytesRegion dst orig ** bytesRegion src xs **
        globalConst (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes)
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once + 84 : Word)) **
        ((.x10 : Reg) ↦ᵣ (1 : Word)) ** regOwns retScratch **
        bytesRegion dst (U256SubBeSAsm.u256SubBeBytes xs secp256k1PBytes orig) **
        bytesRegion src xs **
        globalConst (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes) := by
  have hcall := subSetupCall_spec src dst ret old10 old11 old12 xs orig
    hroX hrwDst hlenX hlenOrig hovX hovDst hdisjX hdisjP
  have htail := subRetTail_spec
    (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
      bytesRegion dst (U256SubBeSAsm.u256SubBeBytes xs secp256k1PBytes orig) **
      bytesRegion src xs ** globalConst (GuestAddrs.secp256k1_p_be : Word) secp256k1PBytes)
    (by pcf)
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hcall htail
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hc

end Secp256k1FieldReduceOnceSAsm

end EvmAsm.Codegen
