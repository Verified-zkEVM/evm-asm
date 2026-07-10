/-
  Verified byte-identical ABI-frame port of `secf_sub_mod_p`.

  The caller first computes the wrapping 256-bit subtraction into the global
  `secf_tmp0` cell.  On borrow it subtracts `2^256 - p` from that temporary,
  producing `a - b + p`; otherwise it copies the temporary to the output.
-/

import EvmAsm.Codegen.Programs.Secp256k1FieldReduceOnceSAsmSupport
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.RetForwardJoin

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

namespace Secp256k1FieldSubModPSAsm

open Secp256k1FieldReduceOnceSAsm

#guard GuestAddrs.secf_sub_mod_p = 0x80020178
#guard GuestAddrs.u256_sub_be = 0x80005248
#guard GuestAddrs.secf_copy32 = 0x8001fea8
#guard GuestAddrs.secf_tmp0 = 0xa3c053c0
#guard GuestAddrs.secp256k1_c_be = 0xa3c052e0

def secfSubModPFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40)]

def secfSubModPBody : List Instr :=
  [ .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x19 (laHi GuestAddrs.secf_tmp0 (GuestAddrs.secf_sub_mod_p + 40)),
    .ADDI .x19 .x19 (laLo GuestAddrs.secf_tmp0 (GuestAddrs.secf_sub_mod_p + 40)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.u256_sub_be (GuestAddrs.secf_sub_mod_p + 60)),
    .MV .x20 .x10,
    .BEQ .x20 .x0 (28 : BitVec 13),
    .MV .x10 .x19,
    .AUIPC .x11 (laHi GuestAddrs.secp256k1_c_be (GuestAddrs.secf_sub_mod_p + 76)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secp256k1_c_be (GuestAddrs.secf_sub_mod_p + 76)),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.u256_sub_be (GuestAddrs.secf_sub_mod_p + 88)),
    .JAL .x0 (16 : BitVec 21),
    .MV .x10 .x19,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.secf_copy32 (GuestAddrs.secf_sub_mod_p + 104)),
    .LI .x10 (0 : Word) ]

theorem secfSubModP_prog_eq :
    abiFrameProg (-48 : BitVec 12) (48 : BitVec 12)
      secfSubModPFrame secfSubModPBody = secfSubModP_prog := by
  rfl

#guard secfSubModPBody.length = 21

def secfSubModPCr : CodeReq :=
  Secp256k1FieldReduceOnceSAsm.secfReduceOnceCr.union
    (CodeReq.ofProg (GuestAddrs.secf_sub_mod_p : Word) secfSubModP_prog)

def secfSubModPVals (ret s0 s1 s2 s3 s4 : Word) : Reg → Word := fun r =>
  match r with
  | .x1 => ret
  | .x8 => s0
  | .x9 => s1
  | .x18 => s2
  | .x19 => s3
  | .x20 => s4
  | _ => 0

def secp256k1CBytes : List (BitVec 8) :=
  [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x03, 0xd1]

#guard secp256k1CBytes.length = 32

private theorem setup_spec (aPtr bPtr outPtr ret v8 v9 v18 v19 : Word) :
    cpsTripleWithin 8 (GuestAddrs.secf_sub_mod_p + 28 : Word)
      (GuestAddrs.secf_sub_mod_p + 60 : Word) secfSubModPCr
      (((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret))
      (((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ bPtr) **
        ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret)) := by
  have hmv8 := liftCode (cr' := secfSubModPCr)
    (mv_spec_gen_within .x8 .x10 aPtr v8
      (GuestAddrs.secf_sub_mod_p + 28 : Word) (by decide))
    (by unfold secfSubModPCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p + 28 : Word) + 4 =
      (GuestAddrs.secf_sub_mod_p + 32 : Word) from by decide] at hmv8
  have hmv9 := liftCode (cr' := secfSubModPCr)
    (mv_spec_gen_within .x9 .x11 bPtr v9
      (GuestAddrs.secf_sub_mod_p + 32 : Word) (by decide))
    (by unfold secfSubModPCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p + 32 : Word) + 4 =
      (GuestAddrs.secf_sub_mod_p + 36 : Word) from by decide] at hmv9
  have hmv18 := liftCode (cr' := secfSubModPCr)
    (mv_spec_gen_within .x18 .x12 outPtr v18
      (GuestAddrs.secf_sub_mod_p + 36 : Word) (by decide))
    (by unfold secfSubModPCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p + 36 : Word) + 4 =
      (GuestAddrs.secf_sub_mod_p + 40 : Word) from by decide] at hmv18
  have hla := la_materialize_within .x19 v19
    (GuestAddrs.secf_sub_mod_p + 40 : Word) (GuestAddrs.secf_tmp0 : Word)
    (cr := secfSubModPCr) (by decide) (by decide)
    (by unfold secfSubModPCr; code_mem) (by unfold secfSubModPCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p + 40 : Word) + 8 =
      (GuestAddrs.secf_sub_mod_p + 48 : Word) from by decide] at hla
  have hmv10 := liftCode (cr' := secfSubModPCr)
    (mv_spec_gen_within .x10 .x8 aPtr aPtr
      (GuestAddrs.secf_sub_mod_p + 48 : Word) (by decide))
    (by unfold secfSubModPCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p + 48 : Word) + 4 =
      (GuestAddrs.secf_sub_mod_p + 52 : Word) from by decide] at hmv10
  have hmv11 := liftCode (cr' := secfSubModPCr)
    (mv_spec_gen_within .x11 .x9 bPtr bPtr
      (GuestAddrs.secf_sub_mod_p + 52 : Word) (by decide))
    (by unfold secfSubModPCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p + 52 : Word) + 4 =
      (GuestAddrs.secf_sub_mod_p + 56 : Word) from by decide] at hmv11
  have hmv12 := liftCode (cr' := secfSubModPCr)
    (mv_spec_gen_within .x12 .x19 (GuestAddrs.secf_tmp0 : Word) outPtr
      (GuestAddrs.secf_sub_mod_p + 56 : Word) (by decide))
    (by unfold secfSubModPCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p + 56 : Word) + 4 =
      (GuestAddrs.secf_sub_mod_p + 60 : Word) from by decide] at hmv12
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

private theorem exposedRegs_split_borrow (vf : Reg → Word) :
    regAtomsOf vf exposedRegs =
      (((.x10 : Reg) ↦ᵣ vf .x10) ** regAtomsOf vf retScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [retScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem exposedRegs_split_args (vf : Reg → Word) :
    regAtomsOf vf exposedRegs =
      (((.x10 : Reg) ↦ᵣ vf .x10) ** ((.x11 : Reg) ↦ᵣ vf .x11) **
        ((.x12 : Reg) ↦ᵣ vf .x12) ** regAtomsOf vf subScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [subScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_subScratch : (.x10 : Reg) ∉ subScratch := by decide
private theorem x11_notin_subScratch : (.x11 : Reg) ∉ subScratch := by decide
private theorem x12_notin_subScratch : (.x12 : Reg) ∉ subScratch := by decide

@[irreducible] def u256SubSteps (aPtr bPtr outPtr : Word)
    (aBytes bBytes orig : List (BitVec 8)) : Nat :=
  (U256SubBeSAsm.u256SubBeFn aPtr bPtr outPtr aBytes bBytes orig).body.steps + 1

private theorem u256SubBorrowFlat_spec (ret aPtr bPtr outPtr : Word)
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
    cpsTripleWithin (u256SubSteps aPtr bPtr outPtr aBytes bBytes orig)
      (GuestAddrs.u256_sub_be : Word) ret secfSubModPCr
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ aPtr) **
        ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        regOwns subScratch ** bytesRegion outPtr orig **
        bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes)
      (((.x1 : Reg) ↦ᵣ ret) **
        ((.x10 : Reg) ↦ᵣ U256SubBeSAsm.u256SubBeBorrow aBytes bBytes orig) **
        regOwns retScratch **
        bytesRegion outPtr (U256SubBeSAsm.u256SubBeBytes aBytes bBytes orig) **
        bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns subScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ aPtr) **
        ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        bytesRegion outPtr orig ** bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes)
      (fun vf => ?_))
  rw [u256SubSteps]
  let rf0 : RegFile := fun r =>
    if r = .x10 then aPtr else if r = .x11 then bPtr
    else if r = .x12 then outPtr else vf r
  have hpre : U256SubBeSAsm.u256SubBePre aPtr bPtr outPtr aBytes bBytes orig
      rf0 orig (bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes) := by
    refine ⟨?_, ?_, ?_, rfl, hlenA, hlenB, hlenOrig, hovA, hovB, hovOut,
      hdisjA, hdisjB, rfl⟩
    · simp [rf0, RegFile.get]
    · simp [rf0, RegFile.get]
    · simp [rf0, RegFile.get]
  have had := Fn.retSpecFlatAmbient
    (U256SubBeSAsm.u256SubBeFn aPtr bPtr outPtr aBytes bBytes orig)
    (GuestAddrs.u256_sub_be : Word)
    (U256SubBeSAsm.u256SubBe_spec aPtr bPtr outPtr aBytes bBytes orig hrw hroA hroB
      (GuestAddrs.u256_sub_be : Word))
    (by show 4 * (16 + 1) ≤ 2 ^ 64; decide) ret halign rf0 orig
    (bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes) (by pcf)
    (by exact hlenOrig) hpre
    (Q := (((.x10 : Reg) ↦ᵣ U256SubBeSAsm.u256SubBeBorrow aBytes bBytes orig) **
      regOwns retScratch **
      bytesRegion outPtr (U256SubBeSAsm.u256SubBeBytes aBytes bBytes orig)) **
      (bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes))
    (fun _ _ _ hpost => by exact hpost.2.2.2.2)
    (fun rf' ws' hlen hpost hp hh => by
      rcases hpost with ⟨hx10, hx11, hx12, hws, hA⟩
      subst ws'
      have hx10raw : rf' .x10 = U256SubBeSAsm.u256SubBeBorrow aBytes bBytes orig := by
        simpa [RegFile.get] using hx10
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_borrow, hx10raw] at hh
      have hh2 : (((((.x10 : Reg) ↦ᵣ U256SubBeSAsm.u256SubBeBorrow
            aBytes bBytes orig) ** regOwns retScratch) **
          bytesRegion
            (U256SubBeSAsm.u256SubBeFn aPtr bPtr outPtr aBytes bBytes orig).rw.base
            (U256SubBeSAsm.u256SubBeBytes aBytes bBytes orig)) **
          bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes) hp := by
        exact sepConj_mono_left
          (sepConj_mono_left
            (sepConj_mono_right
              (regAtomsOf_to_regOwns (fun r => rf' r) retScratch))) hp hh
      rw [show (U256SubBeSAsm.u256SubBeFn aPtr bPtr outPtr aBytes bBytes orig).rw.base =
        outPtr from rfl] at hh2
      xperm_hyp hh2)
  rw [show (U256SubBeSAsm.u256SubBeFn aPtr bPtr outPtr aBytes bBytes orig).programRet
      (GuestAddrs.u256_sub_be : Word) = u256SubBe_prog from rfl] at had
  have hadC := liftCode (cr' := secfSubModPCr) had
    (by unfold secfSubModPCr secfReduceOnceCr; code_mem)
  rw [show (U256SubBeSAsm.u256SubBeFn aPtr bPtr outPtr aBytes bBytes orig).region =
      Region.empty from rfl,
    show (U256SubBeSAsm.u256SubBeFn aPtr bPtr outPtr aBytes bBytes orig).rw.base =
      outPtr from rfl,
    show Region.empty.base = (0 : Word) from rfl,
    show Region.empty.bytes = ([] : List (BitVec 8)) from rfl,
    bytesRegion_nil, sepConj_emp_right'] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_args,
    show rf0 .x10 = aPtr from by simp [rf0],
    show rf0 .x11 = bPtr from by simp [rf0],
    show rf0 .x12 = outPtr from by simp [rf0],
    regAtomsOf_congr rf0 vf subScratch
      (fun r hr => by
        unfold rf0
        rw [if_neg (fun (hc : r = .x10) => x10_notin_subScratch (hc ▸ hr)),
          if_neg (fun (hc : r = .x11) => x11_notin_subScratch (hc ▸ hr)),
          if_neg (fun (hc : r = .x12) => x12_notin_subScratch (hc ▸ hr))])]
    at hadC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by rw [sepConj_emp_right'] at hq; xperm_hyp hq) hadC

private theorem setupFirstCall_spec (aPtr bPtr outPtr ret v8 v9 v18 v19 v20 : Word)
    (aBytes bBytes outOrig tmpOrig : List (BitVec 8))
    (hrwTmp : RwRegion.wf ⟨(GuestAddrs.secf_tmp0 : Word), 32⟩)
    (hroA : Region.wf ⟨aPtr, aBytes⟩) (hroB : Region.wf ⟨bPtr, bBytes⟩)
    (hlenA : aBytes.length = 32) (hlenB : bBytes.length = 32)
    (hlenTmp : tmpOrig.length = 32)
    (hovA : aPtr.toNat + 32 < 2 ^ 64) (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hdA : aPtr.toNat + 32 ≤ GuestAddrs.secf_tmp0 ∨
      GuestAddrs.secf_tmp0 + 32 ≤ aPtr.toNat)
    (hdB : bPtr.toNat + 32 ≤ GuestAddrs.secf_tmp0 ∨
      GuestAddrs.secf_tmp0 + 32 ≤ bPtr.toNat) :
    cpsTripleWithin
      (8 + (1 + u256SubSteps aPtr bPtr (GuestAddrs.secf_tmp0 : Word)
        aBytes bBytes tmpOrig))
      (GuestAddrs.secf_sub_mod_p + 28 : Word)
      (GuestAddrs.secf_sub_mod_p + 64 : Word) secfSubModPCr
      (((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) **
        ((.x20 : Reg) ↦ᵣ v20) ** ((.x10 : Reg) ↦ᵣ aPtr) **
        ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwns subScratch ** bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpOrig **
        bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes **
        bytesRegion outPtr outOrig **
        globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes)
      (((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ bPtr) **
        ((.x18 : Reg) ↦ᵣ outPtr) **
        ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x20 : Reg) ↦ᵣ v20) **
        ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_sub_mod_p + 64 : Word)) **
        ((.x10 : Reg) ↦ᵣ U256SubBeSAsm.u256SubBeBorrow aBytes bBytes tmpOrig) **
        regOwns retScratch ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion (GuestAddrs.secf_tmp0 : Word)
          (U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig) **
        bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes **
        bytesRegion outPtr outOrig **
        globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes) := by
  have hsetup := setup_spec aPtr bPtr outPtr ret v8 v9 v18 v19
  have hsetupF := cpsTripleWithin_frameR
    (((.x20 : Reg) ↦ᵣ v20) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwns subScratch ** bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpOrig **
      bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes ** bytesRegion outPtr outOrig **
      globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes)
    (by pcf) hsetup
  have hcallee := u256SubBorrowFlat_spec
    (GuestAddrs.secf_sub_mod_p + 64 : Word) aPtr bPtr
    (GuestAddrs.secf_tmp0 : Word) aBytes bBytes tmpOrig hrwTmp hroA hroB
    hlenA hlenB hlenTmp hovA hovB (by decide) hdA hdB (by decide)
  rw [show (GuestAddrs.secf_sub_mod_p + 64 : Word) =
      (GuestAddrs.secf_sub_mod_p + 60 : Word) + 4 from by decide] at hcallee
  have hcall := callWithin_spec (cr := secfSubModPCr)
    (P := (((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) ** regOwns subScratch **
      bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpOrig ** bytesRegion aPtr aBytes **
      bytesRegion bPtr bBytes))
    (Q := (((.x10 : Reg) ↦ᵣ U256SubBeSAsm.u256SubBeBorrow aBytes bBytes tmpOrig) **
      regOwns retScratch ** bytesRegion (GuestAddrs.secf_tmp0 : Word)
        (U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig) **
      bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes))
    (GuestAddrs.secf_sub_mod_p + 60 : Word) (GuestAddrs.u256_sub_be : Word) ret
    (jalOff GuestAddrs.u256_sub_be (GuestAddrs.secf_sub_mod_p + 60))
    (u256SubSteps aPtr bPtr (GuestAddrs.secf_tmp0 : Word) aBytes bBytes tmpOrig)
    (by decide) (by unfold secfSubModPCr secfReduceOnceCr; code_mem) (by pcf)
    hcallee
  rw [show (GuestAddrs.secf_sub_mod_p + 60 : Word) + 4 =
      (GuestAddrs.secf_sub_mod_p + 64 : Word) from by decide] at hcall
  have hcallF := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ bPtr) **
      ((.x18 : Reg) ↦ᵣ outPtr) **
      ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x20 : Reg) ↦ᵣ v20) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion outPtr outOrig **
      globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes)
    (by pcf) hcall
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hsetupF hcallF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hc

private theorem saveBorrowBranch_spec (borrow old20 : Word)
    (P : Assertion) (hP : P.pcFree) :
    cpsBranchWithin 2 (GuestAddrs.secf_sub_mod_p + 64 : Word) secfSubModPCr
      (((.x20 : Reg) ↦ᵣ old20) ** ((.x10 : Reg) ↦ᵣ borrow) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** P)
      (GuestAddrs.secf_sub_mod_p + 96 : Word)
      (((.x20 : Reg) ↦ᵣ borrow) ** ((.x10 : Reg) ↦ᵣ borrow) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ⌜borrow = 0⌝ ** P)
      (GuestAddrs.secf_sub_mod_p + 72 : Word)
      (((.x20 : Reg) ↦ᵣ borrow) ** ((.x10 : Reg) ↦ᵣ borrow) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ⌜borrow ≠ 0⌝ ** P) := by
  have hmv := liftCode (cr' := secfSubModPCr)
    (mv_spec_gen_within .x20 .x10 borrow old20
      (GuestAddrs.secf_sub_mod_p + 64 : Word) (by decide))
    (by unfold secfSubModPCr secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p + 64 : Word) + 4 =
      (GuestAddrs.secf_sub_mod_p + 68 : Word) from by decide] at hmv
  have hmvF := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** P) (by exact pcFree_sepConj (by pcf) hP) hmv
  have hbr := cpsBranchWithin_frameR (((.x10 : Reg) ↦ᵣ borrow) ** P)
    (pcFree_sepConj (by pcf) hP)
    (cpsBranchWithin_extend_code (cr' := secfSubModPCr)
      (h := beq_spec_gen_within .x20 .x0 (28 : BitVec 13) borrow (0 : Word)
        (GuestAddrs.secf_sub_mod_p + 68 : Word))
      (hmono := by unfold secfSubModPCr secfReduceOnceCr; code_mem))
  rw [show (GuestAddrs.secf_sub_mod_p + 68 : Word) + signExtend13 (28 : BitVec 13) =
      (GuestAddrs.secf_sub_mod_p + 96 : Word) from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]
        decide,
    show (GuestAddrs.secf_sub_mod_p + 68 : Word) + 4 =
      (GuestAddrs.secf_sub_mod_p + 72 : Word) from by decide] at hbr
  have hc := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hmvF hbr
  exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) (fun _ hq => by xperm_hyp hq) hc

private theorem retScratch_split_copy :
    regOwns retScratch = (regOwn .x11 ** regOwns copyScratch) := by
  simp only [retScratch, copyScratch, regOwns_cons, regOwns_nil]
  funext h
  exact propext ⟨fun hp => by xperm_hyp hp, fun hp => by xperm_hyp hp⟩

private theorem retScratch_split_sub :
    regOwns retScratch = (regOwn .x11 ** regOwn .x12 ** regOwns subScratch) := by
  simp only [retScratch, subScratch, regOwns_cons, regOwns_nil]
  funext h
  exact propext ⟨fun hp => by xperm_hyp hp, fun hp => by xperm_hyp hp⟩

private theorem copyScratch_split :
    regOwns copyScratch = (regOwn .x5 ** regOwns copyRest) := by
  simp only [copyScratch, copyRest, regOwns_cons, regOwns_nil]

private theorem copySetup_spec (tmpPtr outPtr ret old10 old11 : Word) :
    cpsTripleWithin 2 (GuestAddrs.secf_sub_mod_p + 96 : Word)
      (GuestAddrs.secf_sub_mod_p + 104 : Word) secfSubModPCr
      (((.x19 : Reg) ↦ᵣ tmpPtr) ** ((.x18 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ old10) ** ((.x11 : Reg) ↦ᵣ old11) **
        ((.x1 : Reg) ↦ᵣ ret))
      (((.x19 : Reg) ↦ᵣ tmpPtr) ** ((.x18 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ tmpPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ ret)) := by
  have hmv10 := liftCode (cr' := secfSubModPCr)
    (mv_spec_gen_within .x10 .x19 tmpPtr old10
      (GuestAddrs.secf_sub_mod_p + 96 : Word) (by decide))
    (by unfold secfSubModPCr secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p + 96 : Word) + 4 =
      (GuestAddrs.secf_sub_mod_p + 100 : Word) from by decide] at hmv10
  have hmv11 := liftCode (cr' := secfSubModPCr)
    (mv_spec_gen_within .x11 .x18 outPtr old11
      (GuestAddrs.secf_sub_mod_p + 100 : Word) (by decide))
    (by unfold secfSubModPCr secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p + 100 : Word) + 4 =
      (GuestAddrs.secf_sub_mod_p + 104 : Word) from by decide] at hmv11
  have h1 := cpsTripleWithin_frameR
    (((.x18 : Reg) ↦ᵣ outPtr) ** ((.x11 : Reg) ↦ᵣ old11) **
      ((.x1 : Reg) ↦ᵣ ret)) (by pcf) hmv10
  have h2 := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ tmpPtr) ** ((.x10 : Reg) ↦ᵣ tmpPtr) **
      ((.x1 : Reg) ↦ᵣ ret)) (by pcf) hmv11
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1 h2
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hc

private theorem copyArm_spec (outPtr ret borrow : Word)
    (tmpBytes outOrig : List (BitVec 8))
    (hlenTmp : tmpBytes.length = 32) (hlenOut : outOrig.length = 32) :
    cpsTripleWithin 13 (GuestAddrs.secf_sub_mod_p + 96 : Word)
      (GuestAddrs.secf_sub_mod_p + 112 : Word) secfSubModPCr
      ((((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x10 : Reg) ↦ᵣ borrow) **
        ((.x1 : Reg) ↦ᵣ ret) ** regOwns copyScratch **
        bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
        bytesRegion outPtr outOrig) ** regOwn .x11)
      (((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x18 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_sub_mod_p + 108 : Word)) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        regOwns copyScratch **
        bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
        bytesRegion outPtr tmpBytes) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x11)
      (P := ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x10 : Reg) ↦ᵣ borrow) **
        ((.x1 : Reg) ↦ᵣ ret) ** regOwns copyScratch **
        bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
        bytesRegion outPtr outOrig)
      (Q := ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x18 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_sub_mod_p + 108 : Word)) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        regOwns copyScratch **
        bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
        bytesRegion outPtr tmpBytes)
      (fun old11 => ?_)
  rw [copyScratch_split]
  have hsetup := copySetup_spec (GuestAddrs.secf_tmp0 : Word) outPtr ret borrow old11
  have hsetupF := cpsTripleWithin_frameR
    (regOwns copyScratch ** bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
      bytesRegion outPtr outOrig) (by pcf) hsetup
  have hcopy0 := secfCopy32Direct_spec (GuestAddrs.secf_sub_mod_p + 108 : Word)
    (GuestAddrs.secf_tmp0 : Word) outPtr tmpBytes outOrig hlenTmp hlenOut (by decide)
  have hcopy := liftCode (cr' := secfSubModPCr) hcopy0
    (by
      intro a i h
      unfold secfSubModPCr
      simp only [CodeReq.union, h])
  rw [show (GuestAddrs.secf_sub_mod_p + 108 : Word) =
      (GuestAddrs.secf_sub_mod_p + 104 : Word) + 4 from by decide] at hcopy
  have hcall := callWithin_spec (cr := secfSubModPCr)
    (P := (((.x10 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x11 : Reg) ↦ᵣ outPtr) ** regOwn .x5 **
      bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes ** bytesRegion outPtr outOrig))
    (Q := (((.x10 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x11 : Reg) ↦ᵣ outPtr) ** regOwn .x5 **
      bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes ** bytesRegion outPtr tmpBytes))
    (GuestAddrs.secf_sub_mod_p + 104 : Word) (GuestAddrs.secf_copy32 : Word) ret
    (jalOff GuestAddrs.secf_copy32 (GuestAddrs.secf_sub_mod_p + 104)) 9
    (by decide) (by unfold secfSubModPCr secfReduceOnceCr; code_mem) (by pcf)
    hcopy
  rw [show (GuestAddrs.secf_sub_mod_p + 104 : Word) + 4 =
      (GuestAddrs.secf_sub_mod_p + 108 : Word) from by decide] at hcall
  rw [copyScratch_split] at hsetupF
  have hcallF := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x18 : Reg) ↦ᵣ outPtr) ** regOwns copyRest) (by pcf) hcall
  have hc1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hsetupF hcallF
  have hli := liftCode (cr' := secfSubModPCr)
    (li_spec_gen_within .x10 (GuestAddrs.secf_tmp0 : Word) (0 : Word)
      (GuestAddrs.secf_sub_mod_p + 108 : Word) (by decide))
    (by unfold secfSubModPCr secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p + 108 : Word) + 4 =
      (GuestAddrs.secf_sub_mod_p + 112 : Word) from by decide] at hli
  have hliF := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x18 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_sub_mod_p + 108 : Word)) **
      ((.x11 : Reg) ↦ᵣ outPtr) ** regOwn .x5 ** regOwns copyRest **
      bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
      bytesRegion outPtr tmpBytes) (by pcf) hli
  have hc2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc1 hliF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hc2

private theorem borrowSetup_spec (outPtr ret old10 old11 old12 : Word) :
    cpsTripleWithin 4 (GuestAddrs.secf_sub_mod_p + 72 : Word)
      (GuestAddrs.secf_sub_mod_p + 88 : Word) secfSubModPCr
      (((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x10 : Reg) ↦ᵣ old10) **
        ((.x11 : Reg) ↦ᵣ old11) ** ((.x12 : Reg) ↦ᵣ old12) **
        ((.x1 : Reg) ↦ᵣ ret))
      (((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x18 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_c_be : Word)) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret)) := by
  have hmv10 := liftCode (cr' := secfSubModPCr)
    (mv_spec_gen_within .x10 .x19 (GuestAddrs.secf_tmp0 : Word) old10
      (GuestAddrs.secf_sub_mod_p + 72 : Word) (by decide))
    (by unfold secfSubModPCr secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p + 72 : Word) + 4 =
      (GuestAddrs.secf_sub_mod_p + 76 : Word) from by decide] at hmv10
  have hla := la_materialize_within .x11 old11
    (GuestAddrs.secf_sub_mod_p + 76 : Word) (GuestAddrs.secp256k1_c_be : Word)
    (cr := secfSubModPCr) (by decide) (by decide)
    (by unfold secfSubModPCr secfReduceOnceCr; code_mem)
    (by unfold secfSubModPCr secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p + 76 : Word) + 8 =
      (GuestAddrs.secf_sub_mod_p + 84 : Word) from by decide] at hla
  have hmv12 := liftCode (cr' := secfSubModPCr)
    (mv_spec_gen_within .x12 .x18 outPtr old12
      (GuestAddrs.secf_sub_mod_p + 84 : Word) (by decide))
    (by unfold secfSubModPCr secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p + 84 : Word) + 4 =
      (GuestAddrs.secf_sub_mod_p + 88 : Word) from by decide] at hmv12
  have h1 := cpsTripleWithin_frameR
    (((.x18 : Reg) ↦ᵣ outPtr) ** ((.x11 : Reg) ↦ᵣ old11) **
      ((.x12 : Reg) ↦ᵣ old12) ** ((.x1 : Reg) ↦ᵣ ret)) (by pcf) hmv10
  have h2 := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x18 : Reg) ↦ᵣ outPtr) **
      ((.x10 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x12 : Reg) ↦ᵣ old12) ** ((.x1 : Reg) ↦ᵣ ret)) (by pcf) hla
  have h3 := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x10 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_c_be : Word)) **
      ((.x1 : Reg) ↦ᵣ ret)) (by pcf) hmv12
  have hc1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1 h2
  have hc2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc1 h3
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hc2

private theorem borrowArm_spec (outPtr ret borrow : Word)
    (tmpBytes outOrig : List (BitVec 8))
    (hrwOut : RwRegion.wf ⟨outPtr, 32⟩)
    (hroTmp : Region.wf ⟨(GuestAddrs.secf_tmp0 : Word), tmpBytes⟩)
    (hroC : Region.wf ⟨(GuestAddrs.secp256k1_c_be : Word), secp256k1CBytes⟩)
    (hlenTmp : tmpBytes.length = 32) (hlenOut : outOrig.length = 32)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdTmp : GuestAddrs.secf_tmp0 + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ GuestAddrs.secf_tmp0)
    (hdC : GuestAddrs.secp256k1_c_be + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ GuestAddrs.secp256k1_c_be) :
    cpsTripleWithin
      (4 + (1 + u256SubSteps (GuestAddrs.secf_tmp0 : Word)
        (GuestAddrs.secp256k1_c_be : Word) outPtr tmpBytes secp256k1CBytes outOrig) + 2)
      (GuestAddrs.secf_sub_mod_p + 72 : Word)
      (GuestAddrs.secf_sub_mod_p + 112 : Word) secfSubModPCr
      (((((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x10 : Reg) ↦ᵣ borrow) **
        ((.x1 : Reg) ↦ᵣ ret) ** regOwns subScratch **
        bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
        globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes **
        bytesRegion outPtr outOrig) ** regOwn .x12) ** regOwn .x11)
      (((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x18 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_sub_mod_p + 92 : Word)) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwns retScratch **
        bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
        globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes **
        bytesRegion outPtr
          (U256SubBeSAsm.u256SubBeBytes tmpBytes secp256k1CBytes outOrig)) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x11)
    (P := (((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x10 : Reg) ↦ᵣ borrow) **
      ((.x1 : Reg) ↦ᵣ ret) ** regOwns subScratch **
      bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
      globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes **
      bytesRegion outPtr outOrig) ** regOwn .x12)
    (Q := ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x18 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_sub_mod_p + 92 : Word)) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwns retScratch **
      bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
      globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes **
      bytesRegion outPtr
        (U256SubBeSAsm.u256SubBeBytes tmpBytes secp256k1CBytes outOrig))
    (fun old11 => ?_)
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x12)
    (P := (((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x10 : Reg) ↦ᵣ borrow) **
      ((.x1 : Reg) ↦ᵣ ret) ** regOwns subScratch **
      bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
      globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes **
      bytesRegion outPtr outOrig) ** ((.x11 : Reg) ↦ᵣ old11))
    (Q := ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x18 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_sub_mod_p + 92 : Word)) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwns retScratch **
      bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
      globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes **
      bytesRegion outPtr
        (U256SubBeSAsm.u256SubBeBytes tmpBytes secp256k1CBytes outOrig))
    (fun old12 => ?_))
  have hsetup := borrowSetup_spec outPtr ret borrow old11 old12
  have hsetupF := cpsTripleWithin_frameR
    (regOwns subScratch ** bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
      globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes **
      bytesRegion outPtr outOrig) (by pcf) hsetup
  unfold globalConst at hsetupF ⊢
  have hcallee := u256SubBorrowFlat_spec (GuestAddrs.secf_sub_mod_p + 92 : Word)
    (GuestAddrs.secf_tmp0 : Word) (GuestAddrs.secp256k1_c_be : Word) outPtr
    tmpBytes secp256k1CBytes outOrig hrwOut hroTmp hroC hlenTmp (by decide)
    hlenOut (by decide) (by decide) hovOut hdTmp hdC (by decide)
  rw [show (GuestAddrs.secf_sub_mod_p + 92 : Word) =
      (GuestAddrs.secf_sub_mod_p + 88 : Word) + 4 from by decide] at hcallee
  have hcall := callWithin_spec (cr := secfSubModPCr)
    (P := (((.x10 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x11 : Reg) ↦ᵣ (GuestAddrs.secp256k1_c_be : Word)) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns subScratch **
      bytesRegion outPtr outOrig ** bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
      bytesRegion (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes))
    (Q := ((.x10 : Reg) ↦ᵣ U256SubBeSAsm.u256SubBeBorrow
        tmpBytes secp256k1CBytes outOrig) ** regOwns retScratch **
      bytesRegion outPtr
        (U256SubBeSAsm.u256SubBeBytes tmpBytes secp256k1CBytes outOrig) **
      bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
      bytesRegion (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes)
    (GuestAddrs.secf_sub_mod_p + 88 : Word) (GuestAddrs.u256_sub_be : Word) ret
    (jalOff GuestAddrs.u256_sub_be (GuestAddrs.secf_sub_mod_p + 88))
    (u256SubSteps (GuestAddrs.secf_tmp0 : Word)
      (GuestAddrs.secp256k1_c_be : Word) outPtr tmpBytes secp256k1CBytes outOrig)
    (by decide) (by unfold secfSubModPCr secfReduceOnceCr; code_mem) (by pcf)
    hcallee
  rw [show (GuestAddrs.secf_sub_mod_p + 88 : Word) + 4 =
      (GuestAddrs.secf_sub_mod_p + 92 : Word) from by decide] at hcall
  have hcallF := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x18 : Reg) ↦ᵣ outPtr)) (by pcf) hcall
  have hc1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hsetupF hcallF
  have hjal := liftCode (cr' := secfSubModPCr)
    (jal_x0_spec_gen_within (16 : BitVec 21)
      (GuestAddrs.secf_sub_mod_p + 92 : Word))
    (by unfold secfSubModPCr secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p + 92 : Word) + signExtend21 (16 : BitVec 21) =
      (GuestAddrs.secf_sub_mod_p + 108 : Word) from by
        rw [show signExtend21 (16 : BitVec 21) = (16 : Word) from by decide]
        decide] at hjal
  have hjalF := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x18 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_sub_mod_p + 92 : Word)) **
      ((.x10 : Reg) ↦ᵣ U256SubBeSAsm.u256SubBeBorrow
        tmpBytes secp256k1CBytes outOrig) ** regOwns retScratch **
      bytesRegion outPtr
        (U256SubBeSAsm.u256SubBeBytes tmpBytes secp256k1CBytes outOrig) **
      bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
      bytesRegion (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes) (by pcf) hjal
  rw [sepConj_emp_left'] at hjalF
  have hc2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc1 hjalF
  have hli := liftCode (cr' := secfSubModPCr)
    (li_spec_gen_within .x10
      (U256SubBeSAsm.u256SubBeBorrow tmpBytes secp256k1CBytes outOrig) (0 : Word)
      (GuestAddrs.secf_sub_mod_p + 108 : Word) (by decide))
    (by unfold secfSubModPCr secfReduceOnceCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p + 108 : Word) + 4 =
      (GuestAddrs.secf_sub_mod_p + 112 : Word) from by decide] at hli
  have hliF := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x18 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_sub_mod_p + 92 : Word)) **
      regOwns retScratch ** bytesRegion outPtr
        (U256SubBeSAsm.u256SubBeBytes tmpBytes secp256k1CBytes outOrig) **
      bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpBytes **
      bytesRegion (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes) (by pcf) hli
  have hc3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc2 hliF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hc3

/-- Exact byte-level result of the emitted branch structure. -/
def secfSubModPBytes (aBytes bBytes cBytes outOrig tmpOrig : List (BitVec 8)) :
    List (BitVec 8) :=
  let tmp := U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig
  if U256SubBeSAsm.u256SubBeBorrow aBytes bBytes tmpOrig = 0 then tmp
  else U256SubBeSAsm.u256SubBeBytes tmp cBytes outOrig

private def subJoinPost (aPtr bPtr outPtr borrow : Word)
    (aBytes bBytes outOrig tmpOrig : List (BitVec 8)) : Assertion :=
  let tmp := U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig
  ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ bPtr) **
  ((.x18 : Reg) ↦ᵣ outPtr) **
  ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
  ((.x20 : Reg) ↦ᵣ borrow) ** regOwn .x1 **
  ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwns retScratch **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  bytesRegion (GuestAddrs.secf_tmp0 : Word) tmp **
  bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes **
  globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes **
  bytesRegion outPtr (secfSubModPBytes aBytes bBytes secp256k1CBytes outOrig tmpOrig)

private theorem copyArm_to_join (aPtr bPtr outPtr borrow : Word)
    (aBytes bBytes outOrig tmpOrig : List (BitVec 8))
    (h_eq : borrow = U256SubBeSAsm.u256SubBeBorrow aBytes bBytes tmpOrig)
    (h_borrow : borrow = 0) :
    ∀ h,
      (((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ bPtr) **
        ((.x20 : Reg) ↦ᵣ borrow) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes **
        globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes **
        ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x18 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_sub_mod_p + 108 : Word)) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        regOwns copyScratch **
        bytesRegion (GuestAddrs.secf_tmp0 : Word)
          (U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig) **
        bytesRegion outPtr (U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig)) h →
      subJoinPost aPtr bPtr outPtr borrow aBytes bBytes outOrig tmpOrig h := by
  intro h hp
  unfold subJoinPost secfSubModPBytes
  simp only [← h_eq, if_pos h_borrow]
  have hp0 : ((((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_sub_mod_p + 108 : Word)) **
        ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ bPtr) **
        ((.x18 : Reg) ↦ᵣ outPtr) **
        ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x20 : Reg) ↦ᵣ borrow) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ outPtr) ** regOwns copyScratch **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion (GuestAddrs.secf_tmp0 : Word)
          (U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig) **
        bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes **
        globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes **
        bytesRegion outPtr (U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig)) :
      Assertion) h := by
    xperm_hyp hp
  have hp1 := sepConj_mono_left
    (regIs_to_regOwn .x1 (GuestAddrs.secf_sub_mod_p + 108 : Word)) h hp0
  have hp1' : (regOwn .x1 ** (((.x11 : Reg) ↦ᵣ outPtr) **
      ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ bPtr) **
      ((.x18 : Reg) ↦ᵣ outPtr) **
      ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
      ((.x20 : Reg) ↦ᵣ borrow) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
      regOwns copyScratch ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion (GuestAddrs.secf_tmp0 : Word)
        (U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig) **
      bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes **
      globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes **
      bytesRegion outPtr (U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig))) h := by
    xperm_hyp hp1
  have hp2 := sepConj_mono_right
    (sepConj_mono_left (regIs_to_regOwn .x11 outPtr)) h hp1'
  rw [retScratch_split_copy]
  xperm_hyp hp2

private theorem borrowArm_to_join (aPtr bPtr outPtr borrow : Word)
    (aBytes bBytes outOrig tmpOrig : List (BitVec 8))
    (h_eq : borrow = U256SubBeSAsm.u256SubBeBorrow aBytes bBytes tmpOrig)
    (h_borrow : borrow ≠ 0) :
    ∀ h,
      (((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ bPtr) **
        ((.x20 : Reg) ↦ᵣ borrow) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes **
        ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x18 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_sub_mod_p + 92 : Word)) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwns retScratch **
        bytesRegion (GuestAddrs.secf_tmp0 : Word)
          (U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig) **
        globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes **
        bytesRegion outPtr (U256SubBeSAsm.u256SubBeBytes
          (U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig)
          secp256k1CBytes outOrig)) h →
      subJoinPost aPtr bPtr outPtr borrow aBytes bBytes outOrig tmpOrig h := by
  intro h hp
  unfold subJoinPost secfSubModPBytes
  simp only [← h_eq, if_neg h_borrow]
  have hp0 : ((((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_sub_mod_p + 92 : Word)) **
        ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ bPtr) **
        ((.x18 : Reg) ↦ᵣ outPtr) **
        ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x20 : Reg) ↦ᵣ borrow) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        regOwns retScratch ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion (GuestAddrs.secf_tmp0 : Word)
          (U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig) **
        bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes **
        globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes **
        bytesRegion outPtr (U256SubBeSAsm.u256SubBeBytes
          (U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig)
          secp256k1CBytes outOrig)) : Assertion) h := by
    xperm_hyp hp
  have hp1 := sepConj_mono_left
    (regIs_to_regOwn .x1 (GuestAddrs.secf_sub_mod_p + 92 : Word)) h hp0
  xperm_hyp hp1

private theorem branchTail_spec (aPtr bPtr outPtr ret old20 : Word)
    (aBytes bBytes outOrig tmpOrig : List (BitVec 8))
    (hrwOut : RwRegion.wf ⟨outPtr, 32⟩)
    (hroTmp : Region.wf ⟨(GuestAddrs.secf_tmp0 : Word),
      U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig⟩)
    (hroC : Region.wf ⟨(GuestAddrs.secp256k1_c_be : Word), secp256k1CBytes⟩)
    (hlenTmp : (U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig).length = 32)
    (hlenOut : outOrig.length = 32) (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdTmp : GuestAddrs.secf_tmp0 + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ GuestAddrs.secf_tmp0)
    (hdC : GuestAddrs.secp256k1_c_be + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ GuestAddrs.secp256k1_c_be) :
    let borrow := U256SubBeSAsm.u256SubBeBorrow aBytes bBytes tmpOrig
    let tmp := U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig
    cpsTripleWithin
      (2 + (13 + (4 + (1 + u256SubSteps (GuestAddrs.secf_tmp0 : Word)
        (GuestAddrs.secp256k1_c_be : Word) outPtr tmp secp256k1CBytes outOrig) + 2)))
      (GuestAddrs.secf_sub_mod_p + 64 : Word)
      (GuestAddrs.secf_sub_mod_p + 112 : Word) secfSubModPCr
      (((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ bPtr) **
        ((.x18 : Reg) ↦ᵣ outPtr) **
        ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x20 : Reg) ↦ᵣ old20) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x10 : Reg) ↦ᵣ borrow) ** regOwns retScratch **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion (GuestAddrs.secf_tmp0 : Word) tmp **
        bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes **
        bytesRegion outPtr outOrig **
        globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes)
      (subJoinPost aPtr bPtr outPtr borrow aBytes bBytes outOrig tmpOrig) := by
  dsimp only
  let borrow := U256SubBeSAsm.u256SubBeBorrow aBytes bBytes tmpOrig
  let tmp := U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig
  let ctx : Assertion :=
    ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ bPtr) **
    ((.x18 : Reg) ↦ᵣ outPtr) **
    ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
    ((.x1 : Reg) ↦ᵣ ret) ** regOwns retScratch **
    bytesRegion (GuestAddrs.secf_tmp0 : Word) tmp ** bytesRegion aPtr aBytes **
    bytesRegion bPtr bBytes ** bytesRegion outPtr outOrig **
    globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes
  have hbr0 := saveBorrowBranch_spec borrow old20 ctx (by unfold ctx; pcf)
  have hjoin : cpsTripleWithin
      (2 + (13 + (4 + (1 + u256SubSteps (GuestAddrs.secf_tmp0 : Word)
        (GuestAddrs.secp256k1_c_be : Word) outPtr tmp secp256k1CBytes outOrig) + 2)))
      (GuestAddrs.secf_sub_mod_p + 64 : Word)
      (GuestAddrs.secf_sub_mod_p + 112 : Word) secfSubModPCr
      (((.x20 : Reg) ↦ᵣ old20) ** ((.x10 : Reg) ↦ᵣ borrow) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ctx)
      (subJoinPost aPtr bPtr outPtr borrow aBytes bBytes outOrig tmpOrig) := by
    refine retJoinStation_spec (cond := borrow = 0)
      (PT := (((.x20 : Reg) ↦ᵣ borrow) ** ((.x10 : Reg) ↦ᵣ borrow) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ctx))
      (PF := (((.x20 : Reg) ↦ᵣ borrow) ** ((.x10 : Reg) ↦ᵣ borrow) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ctx)) hbr0
      (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) ?_ ?_
    · intro hzero
      have hc0 := copyArm_spec outPtr ret borrow tmp outOrig hlenTmp hlenOut
      have hcF := cpsTripleWithin_frameR
        (((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ bPtr) **
          ((.x20 : Reg) ↦ᵣ borrow) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes **
          globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes)
        (by pcf) hc0
      have hcJ : cpsTripleWithin 13 (GuestAddrs.secf_sub_mod_p + 96 : Word)
          (GuestAddrs.secf_sub_mod_p + 112 : Word) secfSubModPCr
          (((.x20 : Reg) ↦ᵣ borrow) ** ((.x10 : Reg) ↦ᵣ borrow) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ctx)
          (subJoinPost aPtr bPtr outPtr borrow aBytes bBytes outOrig tmpOrig) := by
        refine cpsTripleWithin_weaken (fun h hp => ?_)
          (fun h hq => copyArm_to_join aPtr bPtr outPtr borrow aBytes bBytes
            outOrig tmpOrig (by rfl) hzero h (by xperm_hyp hq)) hcF
        unfold ctx at hp
        rw [retScratch_split_copy] at hp
        xperm_hyp hp
      exact cpsTripleWithin_mono_nSteps (by omega) hcJ
    · intro hnzero
      have hs0 := borrowArm_spec outPtr ret borrow tmp outOrig hrwOut hroTmp hroC
        hlenTmp hlenOut hovOut hdTmp hdC
      have hsF := cpsTripleWithin_frameR
        (((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ bPtr) **
          ((.x20 : Reg) ↦ᵣ borrow) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes)
        (by pcf) hs0
      have hsJ : cpsTripleWithin
          (4 + (1 + u256SubSteps (GuestAddrs.secf_tmp0 : Word)
            (GuestAddrs.secp256k1_c_be : Word) outPtr tmp secp256k1CBytes outOrig) + 2)
          (GuestAddrs.secf_sub_mod_p + 72 : Word)
          (GuestAddrs.secf_sub_mod_p + 112 : Word) secfSubModPCr
          (((.x20 : Reg) ↦ᵣ borrow) ** ((.x10 : Reg) ↦ᵣ borrow) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ctx)
          (subJoinPost aPtr bPtr outPtr borrow aBytes bBytes outOrig tmpOrig) := by
        refine cpsTripleWithin_weaken (fun h hp => ?_)
          (fun h hq => borrowArm_to_join aPtr bPtr outPtr borrow aBytes bBytes
            outOrig tmpOrig (by rfl) hnzero h (by xperm_hyp hq)) hsF
        unfold ctx at hp
        rw [retScratch_split_sub] at hp
        unfold globalConst at hp ⊢
        xperm_hyp hp
      exact cpsTripleWithin_mono_nSteps (by omega) hsJ
  exact cpsTripleWithin_weaken (fun _ hp => by unfold ctx; xperm_hyp hp)
    (fun _ hq => hq) hjoin

private def secfSubModPCallerPre (aPtr bPtr outPtr : Word)
    (aBytes bBytes outOrig tmpOrig : List (BitVec 8)) : Assertion :=
  ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
  ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwns subScratch ** bytesRegion (GuestAddrs.secf_tmp0 : Word) tmpOrig **
  bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes ** bytesRegion outPtr outOrig **
  globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes

private def secfSubModPCallerPost (aPtr bPtr outPtr : Word)
    (aBytes bBytes outOrig tmpOrig : List (BitVec 8)) : Assertion :=
  let tmp := U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig
  regOwn .x10 ** regOwns retScratch ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  bytesRegion (GuestAddrs.secf_tmp0 : Word) tmp **
  bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes **
  globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes **
  bytesRegion outPtr
    (secfSubModPBytes aBytes bBytes secp256k1CBytes outOrig tmpOrig)

private theorem secfSubModPBody_spec (aPtr bPtr outPtr ret v8 v9 v18 v19 v20 : Word)
    (aBytes bBytes outOrig tmpOrig : List (BitVec 8))
    (hrwTmp : RwRegion.wf ⟨(GuestAddrs.secf_tmp0 : Word), 32⟩)
    (hroA : Region.wf ⟨aPtr, aBytes⟩) (hroB : Region.wf ⟨bPtr, bBytes⟩)
    (hrwOut : RwRegion.wf ⟨outPtr, 32⟩)
    (hroTmp : Region.wf ⟨(GuestAddrs.secf_tmp0 : Word),
      U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig⟩)
    (hroC : Region.wf ⟨(GuestAddrs.secp256k1_c_be : Word), secp256k1CBytes⟩)
    (hlenA : aBytes.length = 32) (hlenB : bBytes.length = 32)
    (hlenTmp : tmpOrig.length = 32)
    (hlenTmp' : (U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig).length = 32)
    (hlenOut : outOrig.length = 32)
    (hovA : aPtr.toNat + 32 < 2 ^ 64) (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdATmp : aPtr.toNat + 32 ≤ GuestAddrs.secf_tmp0 ∨
      GuestAddrs.secf_tmp0 + 32 ≤ aPtr.toNat)
    (hdBTmp : bPtr.toNat + 32 ≤ GuestAddrs.secf_tmp0 ∨
      GuestAddrs.secf_tmp0 + 32 ≤ bPtr.toNat)
    (hdTmpOut : GuestAddrs.secf_tmp0 + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ GuestAddrs.secf_tmp0)
    (hdCOut : GuestAddrs.secp256k1_c_be + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ GuestAddrs.secp256k1_c_be) :
    cpsTripleWithin
      ((8 + (1 + u256SubSteps aPtr bPtr (GuestAddrs.secf_tmp0 : Word)
        aBytes bBytes tmpOrig)) +
       (2 + (13 + (4 + (1 + u256SubSteps (GuestAddrs.secf_tmp0 : Word)
        (GuestAddrs.secp256k1_c_be : Word) outPtr
        (U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig)
        secp256k1CBytes outOrig) + 2))))
      (GuestAddrs.secf_sub_mod_p + 28 : Word)
      (GuestAddrs.secf_sub_mod_p + 112 : Word) secfSubModPCr
      (((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) **
        ((.x20 : Reg) ↦ᵣ v20) ** ((.x1 : Reg) ↦ᵣ ret) **
        secfSubModPCallerPre aPtr bPtr outPtr aBytes bBytes outOrig tmpOrig)
      (subJoinPost aPtr bPtr outPtr
        (U256SubBeSAsm.u256SubBeBorrow aBytes bBytes tmpOrig)
        aBytes bBytes outOrig tmpOrig) := by
  have hfirst := setupFirstCall_spec aPtr bPtr outPtr ret v8 v9 v18 v19 v20
    aBytes bBytes outOrig tmpOrig hrwTmp hroA hroB hlenA hlenB hlenTmp
    hovA hovB hdATmp hdBTmp
  have htail := branchTail_spec aPtr bPtr outPtr
    (GuestAddrs.secf_sub_mod_p + 64 : Word) v20 aBytes bBytes outOrig tmpOrig
    hrwOut hroTmp hroC hlenTmp' hlenOut hovOut hdTmpOut hdCOut
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hfirst htail
  exact cpsTripleWithin_weaken (fun _ hp => by
      unfold secfSubModPCallerPre at hp
      xperm_hyp hp) (fun _ hq => hq) hc

private theorem secfSubModPRestore_spec (sp0 ret aPtr bPtr outPtr s0 s1 s2 s3 s4 : Word)
    (aBytes bBytes outOrig tmpOrig : List (BitVec 8))
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (secfSubModPFrame.length + 1 + 1)
      (GuestAddrs.secf_sub_mod_p + 112 : Word) ret secfSubModPCr
      (((.x2 : Reg) ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
        frameSlotsSaved secfSubModPFrame (sp0 + signExtend12 (-48 : BitVec 12))
          (secfSubModPVals ret s0 s1 s2 s3 s4) **
        subJoinPost aPtr bPtr outPtr
          (U256SubBeSAsm.u256SubBeBorrow aBytes bBytes tmpOrig)
          aBytes bBytes outOrig tmpOrig)
      (((.x2 : Reg) ↦ᵣ sp0) **
        regsAt secfSubModPFrame (secfSubModPVals ret s0 s1 s2 s3 s4) **
        frameSlotsSaved secfSubModPFrame (sp0 + signExtend12 (-48 : BitVec 12))
          (secfSubModPVals ret s0 s1 s2 s3 s4) **
        secfSubModPCallerPost aPtr bPtr outPtr aBytes bBytes outOrig tmpOrig) := by
  set newSp := sp0 + signExtend12 (-48 : BitVec 12) with hnewSp
  let R : Assertion :=
    ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwns retScratch **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    bytesRegion (GuestAddrs.secf_tmp0 : Word)
      (U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig) **
    bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes **
    globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes **
    bytesRegion outPtr
      (secfSubModPBytes aBytes bBytes secp256k1CBytes outOrig tmpOrig)
  let P : Assertion := (((.x2 : Reg) ↦ᵣ newSp) **
    frameSlotsSaved secfSubModPFrame newSp
      (secfSubModPVals ret s0 s1 s2 s3 s4) **
    ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ bPtr) **
    ((.x18 : Reg) ↦ᵣ outPtr) **
    ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
    ((.x20 : Reg) ↦ᵣ U256SubBeSAsm.u256SubBeBorrow aBytes bBytes tmpOrig) **
    R)
  refine cpsTripleWithin_weaken (P := P ** regOwn .x1) (fun h hp => ?_)
    (fun _ hq => hq) ?_
  · unfold P R
    unfold subJoinPost at hp
    rw [hnewSp]
    xperm_hyp hp
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x1) ?_
  intro v1
  have hload0 := loadSeq_spec secfSubModPFrame newSp
    (secfSubModPVals ret s0 s1 s2 s3 s4)
    (secfSubModPVals v1 aPtr bPtr outPtr (GuestAddrs.secf_tmp0 : Word)
      (U256SubBeSAsm.u256SubBeBorrow aBytes bBytes tmpOrig))
    (GuestAddrs.secf_sub_mod_p + 112 : Word) (by decide) (by decide)
  have hload := liftCode (cr' := secfSubModPCr) hload0
    (by unfold secfSubModPCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p + 112 : Word) +
      BitVec.ofNat 64 (4 * secfSubModPFrame.length) =
      (GuestAddrs.secf_sub_mod_p + 136 : Word) from by decide] at hload
  have hloadF := cpsTripleWithin_frameR
    R
    (by pcf) hload
  have hdealloc0 := addi_spec_gen_same_within .x2 newSp (48 : BitVec 12)
    (GuestAddrs.secf_sub_mod_p + 136 : Word) (by decide)
  rw [show newSp + signExtend12 (48 : BitVec 12) = sp0 from by
      rw [hnewSp]; exact sext_frameRestore sp0 (-48 : BitVec 12) (48 : BitVec 12) (by decide)]
    at hdealloc0
  have hdealloc := liftCode (cr' := secfSubModPCr) hdealloc0
    (by unfold secfSubModPCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p + 136 : Word) + 4 =
      (GuestAddrs.secf_sub_mod_p + 140 : Word) from by decide] at hdealloc
  have hdeallocF := cpsTripleWithin_frameR
    (regsAt secfSubModPFrame (secfSubModPVals ret s0 s1 s2 s3 s4) **
      frameSlotsSaved secfSubModPFrame newSp (secfSubModPVals ret s0 s1 s2 s3 s4) **
      R)
    (by pcf) hdealloc
  have hret0 := EvmAsm.Evm64.ret_spec_within'
    (GuestAddrs.secf_sub_mod_p + 140 : Word) ret
  rw [halign] at hret0
  have hret := liftCode (cr' := secfSubModPCr) hret0
    (by unfold secfSubModPCr; code_mem)
  have hretF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ sp0) **
      regsAt [(.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40)]
        (secfSubModPVals ret s0 s1 s2 s3 s4) **
      frameSlotsSaved secfSubModPFrame newSp (secfSubModPVals ret s0 s1 s2 s3 s4) **
      R)
    (by pcf) hret
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hloadF hdeallocF
  have hReg : regsAt secfSubModPFrame (secfSubModPVals ret s0 s1 s2 s3 s4) =
      (((.x1 : Reg) ↦ᵣ ret) **
        regsAt [(.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40)]
          (secfSubModPVals ret s0 s1 s2 s3 s4)) := by
    simp only [secfSubModPFrame, regsAt, secfSubModPVals, List.foldr_cons,
      List.foldr_nil, sepConj_emp_right']
  rw [hReg] at h12
  have h123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    h12 hretF
  have hRegV : regsAt secfSubModPFrame
      (secfSubModPVals v1 aPtr bPtr outPtr (GuestAddrs.secf_tmp0 : Word)
        (U256SubBeSAsm.u256SubBeBorrow aBytes bBytes tmpOrig)) =
      (((.x1 : Reg) ↦ᵣ v1) ** ((.x8 : Reg) ↦ᵣ aPtr) **
        ((.x9 : Reg) ↦ᵣ bPtr) ** ((.x18 : Reg) ↦ᵣ outPtr) **
        ((.x19 : Reg) ↦ᵣ (GuestAddrs.secf_tmp0 : Word)) **
        ((.x20 : Reg) ↦ᵣ U256SubBeSAsm.u256SubBeBorrow aBytes bBytes tmpOrig)) := by
    simp only [secfSubModPFrame, regsAt, secfSubModPVals, List.foldr_cons,
      List.foldr_nil, sepConj_emp_right']
  exact cpsTripleWithin_weaken (fun _ hp => by
      unfold P R at hp
      rw [hRegV]
      xperm_hyp hp) (fun h hq => by
        rw [hnewSp] at hq
        unfold R at hq
        unfold secfSubModPCallerPost
        rw [hReg]
        have hq0 : (((.x10 : Reg) ↦ᵣ (0 : Word)) **
            (((.x2 : Reg) ↦ᵣ sp0) **
              ((.x1 : Reg) ↦ᵣ ret) **
              regsAt [(.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40)]
                (secfSubModPVals ret s0 s1 s2 s3 s4) **
              frameSlotsSaved secfSubModPFrame
                (sp0 + signExtend12 (-48 : BitVec 12))
                (secfSubModPVals ret s0 s1 s2 s3 s4) **
              regOwns retScratch ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion (GuestAddrs.secf_tmp0 : Word)
                (U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig) **
              bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes **
              globalConst (GuestAddrs.secp256k1_c_be : Word) secp256k1CBytes **
              bytesRegion outPtr (secfSubModPBytes aBytes bBytes secp256k1CBytes
                outOrig tmpOrig))) h := by xperm_hyp hq
        have hq1 := sepConj_mono_left (regIs_to_regOwn .x10 (0 : Word)) h hq0
        xperm_hyp hq1) h123

def secfSubModPBodySteps (aPtr bPtr outPtr : Word)
    (aBytes bBytes outOrig tmpOrig : List (BitVec 8)) : Nat :=
  (8 + (1 + u256SubSteps aPtr bPtr (GuestAddrs.secf_tmp0 : Word)
    aBytes bBytes tmpOrig)) +
  (2 + (13 + (4 + (1 + u256SubSteps (GuestAddrs.secf_tmp0 : Word)
    (GuestAddrs.secp256k1_c_be : Word) outPtr
    (U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig)
    secp256k1CBytes outOrig) + 2)))

/-- Whole-routine byte-identical specification for `secf_sub_mod_p`.
    The output is the exact branch semantics of the emitted routine: the
    wrapping big-endian subtraction is copied when it does not borrow, and
    otherwise `2^256 - p` is subtracted from it. -/
theorem secfSubModP_spec
    (sp0 ret aPtr bPtr outPtr s0 s1 s2 s3 s4 : Word)
    (aBytes bBytes outOrig tmpOrig : List (BitVec 8))
    (hrwTmp : RwRegion.wf ⟨(GuestAddrs.secf_tmp0 : Word), 32⟩)
    (hroA : Region.wf ⟨aPtr, aBytes⟩) (hroB : Region.wf ⟨bPtr, bBytes⟩)
    (hrwOut : RwRegion.wf ⟨outPtr, 32⟩)
    (hroTmp : Region.wf ⟨(GuestAddrs.secf_tmp0 : Word),
      U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig⟩)
    (hroC : Region.wf ⟨(GuestAddrs.secp256k1_c_be : Word), secp256k1CBytes⟩)
    (hlenA : aBytes.length = 32) (hlenB : bBytes.length = 32)
    (hlenTmp : tmpOrig.length = 32)
    (hlenTmp' : (U256SubBeSAsm.u256SubBeBytes aBytes bBytes tmpOrig).length = 32)
    (hlenOut : outOrig.length = 32)
    (hovA : aPtr.toNat + 32 < 2 ^ 64) (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdATmp : aPtr.toNat + 32 ≤ GuestAddrs.secf_tmp0 ∨
      GuestAddrs.secf_tmp0 + 32 ≤ aPtr.toNat)
    (hdBTmp : bPtr.toNat + 32 ≤ GuestAddrs.secf_tmp0 ∨
      GuestAddrs.secf_tmp0 + 32 ≤ bPtr.toNat)
    (hdTmpOut : GuestAddrs.secf_tmp0 + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ GuestAddrs.secf_tmp0)
    (hdCOut : GuestAddrs.secp256k1_c_be + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ GuestAddrs.secp256k1_c_be)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      (1 + secfSubModPFrame.length +
        secfSubModPBodySteps aPtr bPtr outPtr aBytes bBytes outOrig tmpOrig +
        (secfSubModPFrame.length + 1 + 1))
      (GuestAddrs.secf_sub_mod_p : Word) ret secfSubModPCr
      (((.x2 : Reg) ↦ᵣ sp0) **
        regsAt secfSubModPFrame (secfSubModPVals ret s0 s1 s2 s3 s4) **
        frameSlotsOwn secfSubModPFrame (sp0 + signExtend12 (-48 : BitVec 12)) **
        secfSubModPCallerPre aPtr bPtr outPtr aBytes bBytes outOrig tmpOrig)
      (((.x2 : Reg) ↦ᵣ sp0) **
        regsAt secfSubModPFrame (secfSubModPVals ret s0 s1 s2 s3 s4) **
        frameSlotsSaved secfSubModPFrame (sp0 + signExtend12 (-48 : BitVec 12))
          (secfSubModPVals ret s0 s1 s2 s3 s4) **
        secfSubModPCallerPost aPtr bPtr outPtr aBytes bBytes outOrig tmpOrig) := by
  set newSp := sp0 + signExtend12 (-48 : BitVec 12) with hnewSp
  have halloc0 := addi_spec_gen_same_within .x2 sp0 (-48 : BitVec 12)
    (GuestAddrs.secf_sub_mod_p : Word) (by decide)
  rw [← hnewSp] at halloc0
  have halloc := liftCode (cr' := secfSubModPCr) halloc0
    (by unfold secfSubModPCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p : Word) + 4 =
      (GuestAddrs.secf_sub_mod_p + 4 : Word) from by decide] at halloc
  have hallocF := cpsTripleWithin_frameR
    (regsAt secfSubModPFrame (secfSubModPVals ret s0 s1 s2 s3 s4) **
      frameSlotsOwn secfSubModPFrame newSp **
      secfSubModPCallerPre aPtr bPtr outPtr aBytes bBytes outOrig tmpOrig)
    (by pcf) halloc
  have hstore0 := storeSeq_spec secfSubModPFrame newSp
    (secfSubModPVals ret s0 s1 s2 s3 s4)
    (GuestAddrs.secf_sub_mod_p + 4 : Word) (by decide)
  have hstore := liftCode (cr' := secfSubModPCr) hstore0
    (by unfold secfSubModPCr; code_mem)
  rw [show (GuestAddrs.secf_sub_mod_p + 4 : Word) +
      BitVec.ofNat 64 (4 * secfSubModPFrame.length) =
      (GuestAddrs.secf_sub_mod_p + 28 : Word) from by decide] at hstore
  have hstoreF := cpsTripleWithin_frameR
    (secfSubModPCallerPre aPtr bPtr outPtr aBytes bBytes outOrig tmpOrig)
    (by pcf) hstore
  have hbody0 := secfSubModPBody_spec aPtr bPtr outPtr ret s0 s1 s2 s3 s4
    aBytes bBytes outOrig tmpOrig hrwTmp hroA hroB hrwOut hroTmp hroC
    hlenA hlenB hlenTmp hlenTmp' hlenOut hovA hovB hovOut hdATmp hdBTmp
    hdTmpOut hdCOut
  have hbodyF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) **
      frameSlotsSaved secfSubModPFrame newSp
        (secfSubModPVals ret s0 s1 s2 s3 s4)) (by pcf) hbody0
  have htail := secfSubModPRestore_spec sp0 ret aPtr bPtr outPtr s0 s1 s2 s3 s4
    aBytes bBytes outOrig tmpOrig halignRet
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hallocF hstoreF
  have h123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      unfold secfSubModPCallerPre at hp ⊢
      simp only [secfSubModPFrame, regsAt, secfSubModPVals, List.foldr_cons,
        List.foldr_nil, sepConj_emp_right'] at hp ⊢
      xperm_hyp hp) h12 hbodyF
  have h1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    h123 htail
  exact cpsTripleWithin_weaken (fun _ hp => by rw [hnewSp]; xperm_hyp hp)
    (fun _ hq => by rw [hnewSp]; xperm_hyp hq) h1234

#print axioms secfSubModP_spec

end Secp256k1FieldSubModPSAsm

end EvmAsm.Codegen
