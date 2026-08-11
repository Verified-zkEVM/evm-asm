/-
  EvmAsm.Codegen.Proofs.MptWitnessIndexSpec

  Bottom-up contracts for the sorted witness-index helpers.  This file starts
  with the address calculation leaf; the comparison and heap helpers are
  intentionally contracted separately so callers can compose them without
  hiding their individual step bounds.

  These contracts establish termination/step bounds and frame preservation
  (including the fixed arena extent).  They do not establish heap order,
  sortedness, or permutation; those functional facts remain a builder-level
  obligation.
-/

import EvmAsm.Codegen.Programs.MptWitnessIndex
import EvmAsm.Codegen.Programs.U256MinSAsm
import EvmAsm.Rv64.SAsm.BlockAtBridge
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.RetForwardJoin
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Codegen.Proofs.HashBridgeKeccakZero
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.U256MinSAsm
open EvmAsm.Crypto

/-- The six instructions before the calling-convention return in
    `widx_record_ptr`.  The two AUIPC/ADDI immediates are parameters because
    the data label is link-layout dependent. -/
def widxRecordPtrBody (hi : BitVec 20) (lo : BitVec 12) : List Instr :=
  [ .SLLI .x5 .x10 (5 : BitVec 6),
    .SLLI .x6 .x10 (4 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .AUIPC .x10 hi,
    .ADDI .x10 .x10 lo,
    .ADD .x10 .x10 .x5 ]

def widxRecordPtrProg (hi : BitVec 20) (lo : BitVec 12) : Program :=
  widxRecordPtrBody hi lo ++ [.JALR .x0 .x1 (0 : BitVec 12)]

@[simp] theorem widxRecordPtrBody_length (hi : BitVec 20) (lo : BitVec 12) :
    (widxRecordPtrBody hi lo).length = 6 := by
  simp [widxRecordPtrBody]

@[simp] theorem widxRecordPtrProg_length (hi : BitVec 20) (lo : BitVec 12) :
    (widxRecordPtrProg hi lo).length = 7 := by
  change (widxRecordPtrBody hi lo).length + 1 = 7
  simp [widxRecordPtrBody]

def widxRecordPtrResult (base : Word) (hi : BitVec 20) (lo : BitVec 12)
    (rf : RegFile) : RegFile :=
  let s1 := rf.set .x5 (rf.get .x10 <<< 5)
  let s2 := s1.set .x6 (s1.get .x10 <<< 4)
  let s3 := s2.set .x5 (s2.get .x5 + s2.get .x6)
  let s4 := s3.set .x10
    ((base + 4 + 4 + 4) + ((hi.zeroExtend 32 <<< 12).signExtend 64))
  let s5 := s4.set .x10 (s4.get .x10 + signExtend12 lo)
  s5.set .x10 (s5.get .x10 + s5.get .x5)

/-- `widx_record_ptr` preserves the exposed register file except for the
    address arithmetic in `a0`, `t0`, and `t1`, then returns through `ra`.
    The result is stated as the exact register valuation of the six-step
    body, rather than as an unproved arithmetic summary. -/
theorem widx_record_ptr_spec
    (base ret : Word) (hi : BitVec 20) (lo : BitVec 12) (rf : RegFile)
    (halign : ret &&& ~~~(1 : Word) = ret) :
    cpsTripleWithin 7 base ret
      (CodeReq.ofProg base (widxRecordPtrProg hi lo))
      (regAtoms rf exposedRegs ** (.x1 ↦ᵣ ret))
      (regAtoms (widxRecordPtrResult base hi lo rf) exposedRegs ** (.x1 ↦ᵣ ret)) := by
  have h_body := blockAt_regs_spec (widxRecordPtrBody hi lo) rf base
    (by simp [blockOkAt, instrOkAt, instrOk, aluSem, Reg.isExposed,
      widxRecordPtrBody])
    (by simp [hasLoad, loadSem, storeSem, widxRecordPtrBody])
    (by simp [widxRecordPtrBody])
  rw [show base + BitVec.ofNat 64 (4 * (widxRecordPtrBody hi lo).length) = base + 24 by
    simp [widxRecordPtrBody]] at h_body
  have h_result :
      (execBlockAt Region.empty RwRegion.empty.base base rf []
        (widxRecordPtrBody hi lo)).1 = widxRecordPtrResult base hi lo rf := by
    simp [widxRecordPtrResult, widxRecordPtrBody, execBlockAt, execInstrRFAt,
      execInstrRF, aluSem]
  rw [h_result] at h_body
  have h_body_full := cpsTripleWithin_extend_code
    (hmono := CodeReq.ofProg_mono_sub base base (widxRecordPtrProg hi lo)
      (widxRecordPtrBody hi lo) 0 (by change base = base + (0 : Word); simp)
      (by rfl)
      (by change 6 ≤ 7; decide)
      (by change 4 * 7 < 2 ^ 64; decide))
    h_body
  have h_body_frame := cpsTripleWithin_frameR (.x1 ↦ᵣ ret) pcFree_regIs h_body_full
  have h_ret0 := EvmAsm.Evm64.ret_spec_within' (base + 24) ret
  rw [halign] at h_ret0
  have h_ret := cpsTripleWithin_extend_code
    (h := h_ret0)
    (hmono := CodeReq.ofProg_mono_sub base (base + 24) (widxRecordPtrProg hi lo)
      [.JALR .x0 .x1 (0 : BitVec 12)] 6
      (by
        have h24 : BitVec.ofNat 64 (4 * 6) = (24 : Word) := by decide
        rw [h24])
      (by
        change List.take 1 (List.drop 6 (widxRecordPtrBody hi lo ++
          [.JALR .x0 .x1 (0 : BitVec 12)])) =
          [.JALR .x0 .x1 (0 : BitVec 12)]
        simp [widxRecordPtrBody])
      (by change 7 ≤ 7; decide)
      (by change 4 * 7 < 2 ^ 64; decide))
  have h_ret_frame := cpsTripleWithin_frameL
    (regAtoms (widxRecordPtrResult base hi lo rf) exposedRegs)
    (pcFree_regAtoms _ _ ) h_ret
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    h_body_frame h_ret_frame

/-! ## `widx_cmp32`

The comparator is a fixed-length, big-endian, three-way byte comparison.  Its
two ordered `bltu` exits and its exhausted equality exit all share the normal
calling-convention return, so the proof follows the verified two-break loop
shape used by the existing 256-bit comparator, but leaves the result in `a0`
instead of writing a flag cell.
-/

def widxCmp32Prog : List Instr :=
  [ .LI .x5 (32 : Word),
    .BEQ .x5 .x0 (44 : BitVec 13),
    .LBU .x6 .x10 (0 : BitVec 12),
    .LBU .x7 .x11 (0 : BitVec 12),
    .BLTU .x6 .x7 (24 : BitVec 13),
    .BLTU .x7 .x6 (36 : BitVec 13),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x11 .x11 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (2 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

@[simp] theorem widxCmp32Prog_length : widxCmp32Prog.length = 16 := by
  simp [widxCmp32Prog]

private theorem widx_cmp32_mem_at (base A : Word) (k : Nat) (ins : Instr)
    (hA : A = base + BitVec.ofNat 64 (4 * k)) (hk : k < 16)
    (hins : ∀ h : k < widxCmp32Prog.length,
      widxCmp32Prog[k]'h = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i →
      CodeReq.ofProg base widxCmp32Prog a = some i := by
  have hk' : k < widxCmp32Prog.length := by
    rw [widxCmp32Prog_length]
    exact hk
  exact CodeReq.ofProg_mem_at base A _ k ins hA hk' (hins hk')
    (by rw [widxCmp32Prog_length]; decide)

private theorem widx_cmp32_counter_dec (i : Nat) (hi : i < 32) :
    BitVec.ofNat 64 (32 - i) + signExtend12 (-1 : BitVec 12)
      = BitVec.ofNat 64 (32 - (i + 1)) := by
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show ((-1 : Word)).toNat = 18446744073709551615 from rfl]
  omega

private theorem widx_cmp32_cursor_advance (p : Word) (i : Nat) :
    p + BitVec.ofNat 64 i + signExtend12 (1 : BitVec 12)
      = p + BitVec.ofNat 64 (i + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show ((1 : Word)).toNat = 1 from rfl,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem widx_cmp32_counter_ne_zero (i : Nat) (hi : i < 32) :
    ¬ (BitVec.ofNat 64 (32 - i) = (0 : Word)) := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, show ((0 : Word)).toNat = 0 from rfl] at this
  omega

private def widxCmp32Inv (ptrA ptrB ret : Word)
    (as bs : List (BitVec 8)) (i : Nat) : Assertion :=
  ⌜∀ j, j < i → as.getD j 0 = bs.getD j 0⌝ **
  ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
  ((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
  ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
  ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x6 ** regOwn .x7 **
  bytesRegion ptrA as ** bytesRegion ptrB bs

private def widxCmp32Post (ptrA ptrB ret : Word)
    (as bs : List (BitVec 8)) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (if as = bs then (1 : Word)
    else if beBytesToNat as < beBytesToNat bs then (0 : Word) else (2 : Word))) **
  ((.x1 : Reg) ↦ᵣ ret) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 **
  bytesRegion ptrA as ** bytesRegion ptrB bs

private theorem widx_cmp32_tail_spec (base ret : Word) (k : Nat) (c old : Word)
    (hk : k < 16) (hk1 : k + 1 < 16)
    (hins : ∀ h : k < widxCmp32Prog.length,
      widxCmp32Prog[k]'h = .LI .x10 c)
    (hinsRet : ∀ h : k + 1 < widxCmp32Prog.length,
      widxCmp32Prog[k + 1]'h = .JALR .x0 .x1 0)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 2 (base + BitVec.ofNat 64 (4 * k)) ret
      (CodeReq.ofProg base widxCmp32Prog)
      (((.x10 : Reg) ↦ᵣ old) ** ((.x1 : Reg) ↦ᵣ ret))
      (((.x10 : Reg) ↦ᵣ c) ** ((.x1 : Reg) ↦ᵣ ret)) := by
  set CR := CodeReq.ofProg base widxCmp32Prog with hCR
  have htail := sharedRetTail_spec CR (base + BitVec.ofNat 64 (4 * k)) ret
    .x10 c old empAssertion pcFree_emp (by decide) halignRet
    (by
      intro a i h
      exact widx_cmp32_mem_at base _ k _ rfl hk hins a i h)
    (by
      intro a i h
      have haddr : base + BitVec.ofNat 64 (4 * (k + 1)) =
          (base + BitVec.ofNat 64 (4 * k)) + 4 := by bv_omega
      exact widx_cmp32_mem_at base _ (k + 1) _ haddr.symm hk1 hinsRet a i h)
  rw [sepConj_emp_right'] at htail
  simpa [hCR] using htail

private theorem widx_cmp32_iter
    (base ret ptrA ptrB : Word) (as bs : List (BitVec 8))
    (hlenA : as.length = 32) (hlenB : bs.length = 32)
    (halignA : ptrA.toNat % 8 = 0) (halignB : ptrB.toNat % 8 = 0)
    (hovA : ptrA.toNat + 32 < 2 ^ 64)
    (hovB : ptrB.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ k, k < 32 →
      isValidByteAccess (ptrA + BitVec.ofNat 64 k) = true)
    (hvalidB : ∀ k, k < 32 →
      isValidByteAccess (ptrB + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret)
    (i : Nat) (hi : i < 32) :
    cpsBranchWithin 9 (base + 4)
      (CodeReq.ofProg base widxCmp32Prog)
      (widxCmp32Inv ptrA ptrB ret as bs i)
      ret (widxCmp32Post ptrA ptrB ret as bs)
      (base + 4) (widxCmp32Inv ptrA ptrB ret as bs (i + 1)) := by
  set CR := CodeReq.ofProg base widxCmp32Prog with hCR
  have hia : i < as.length := by omega
  have hib : i < bs.length := by omega
  set aByte := (as[i]'hia).zeroExtend 64 with haByte
  set bByte := (bs[i]'hib).zeroExtend 64 with hbByte
  have haBN : aByte.toNat = (as[i]'hia).toNat := by
    rw [haByte]
    show (BitVec.setWidth 64 _).toNat = _
    rw [BitVec.toNat_setWidth]
    have h := (as[i]'hia).isLt
    omega
  have hbBN : bByte.toNat = (bs[i]'hib).toNat := by
    rw [hbByte]
    show (BitVec.setWidth 64 _).toNat = _
    rw [BitVec.toNat_setWidth]
    have h := (bs[i]'hib).isLt
    omega
  have hgdA : as.getD i 0 = as[i]'hia := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hia]
    rfl
  have hgdB : bs.getD i 0 = bs[i]'hib := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hib]
    rfl
  unfold widxCmp32Inv
  refine cpsBranchWithin_pure_pre (fun hpref => ?_)
  refine cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x6)
      (P := (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
        ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x7 ** bytesRegion ptrA as ** bytesRegion ptrB bs))
      (fun v6 => ?_))
  refine cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x7)
      (P := (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
        ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x6 : Reg) ↦ᵣ v6) ** bytesRegion ptrA as ** bytesRegion ptrB bs))
      (fun v7 => ?_))
  suffices hmain :
      cpsBranchWithin 9 (base + 4) CR
        (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
         ((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
         ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
         ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
         bytesRegion ptrA as ** bytesRegion ptrB bs)
        ret (widxCmp32Post ptrA ptrB ret as bs)
        (base + 4) (widxCmp32Inv ptrA ptrB ret as bs (i + 1)) by
    exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq) hmain
  have hlbuA := liftCode (cr' := CR)
    (bytesRegion_lbu_within .x6 .x10 ptrA v6 (base + 8) as i
      (by decide) halignA hia (by omega) (hvalidA i hi))
    (by
      rw [hCR]
      exact widx_cmp32_mem_at base (base + 8) 2
        (.LBU .x6 .x10 (0 : BitVec 12)) (by bv_omega) (by decide)
        (fun _ => rfl))
  rw [show (base + 8) + 4 = base + 12 by bv_omega] at hlbuA
  have hlbuB := liftCode (cr' := CR)
    (bytesRegion_lbu_within .x7 .x11 ptrB v7 (base + 12) bs i
      (by decide) halignB hib (by omega) (hvalidB i hi))
    (by
      rw [hCR]
      exact widx_cmp32_mem_at base (base + 12) 3
        (.LBU .x7 .x11 (0 : BitVec 12)) (by bv_omega) (by decide)
        (fun _ => rfl))
  rw [show (base + 12) + 4 = base + 16 by bv_omega] at hlbuB
  have hlbuAF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x7 : Reg) ↦ᵣ v7) ** bytesRegion ptrB bs)
    (by pcf) hlbuA
  have hlbuBF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x6 : Reg) ↦ᵣ aByte) ** bytesRegion ptrA as)
    (by pcf) hlbuB
  have hpre := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hlbuAF hlbuBF
  have hbrHdr := cpsBranchWithin_frameR
    (((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
      ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x6 : Reg) ↦ᵣ v6) **
      ((.x7 : Reg) ↦ᵣ v7) ** bytesRegion ptrA as ** bytesRegion ptrB bs)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := beq_spec_gen_within .x5 .x0 (44 : BitVec 13)
        (BitVec.ofNat 64 (32 - i)) (0 : Word) (base + 4))
      (hmono := by
        rw [hCR]
        exact widx_cmp32_mem_at base (base + 4) 1
          (.BEQ .x5 .x0 (44 : BitVec 13)) (by bv_omega) (by decide)
          (fun _ => rfl)))
  rw [show signExtend13 (44 : BitVec 13) = (44 : Word) by decide,
      show (base + 4) + (44 : Word) = base + 48 by bv_omega,
      show (base + 4) + 4 = base + 8 by bv_omega] at hbrHdr
  have hbrA := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
      ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion ptrA as ** bytesRegion ptrB bs)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := bltu_spec_gen_within .x6 .x7 (24 : BitVec 13) aByte bByte
        (base + 16))
      (hmono := by
        rw [hCR]
        exact widx_cmp32_mem_at base (base + 16) 4
          (.BLTU .x6 .x7 (24 : BitVec 13)) (by bv_omega) (by decide)
          (fun _ => rfl)))
  rw [show signExtend13 (24 : BitVec 13) = (24 : Word) by decide,
      show (base + 16) + (24 : Word) = base + 40 by bv_omega,
      show (base + 16) + 4 = base + 20 by bv_omega] at hbrA
  have hbrB := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
      ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion ptrA as ** bytesRegion ptrB bs)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := bltu_spec_gen_within .x7 .x6 (36 : BitVec 13) bByte aByte
        (base + 20))
      (hmono := by
        rw [hCR]
        exact widx_cmp32_mem_at base (base + 20) 5
          (.BLTU .x7 .x6 (36 : BitVec 13)) (by bv_omega) (by decide)
          (fun _ => rfl)))
  rw [show signExtend13 (36 : BitVec 13) = (36 : Word) by decide,
      show (base + 20) + (36 : Word) = base + 56 by bv_omega,
      show (base + 20) + 4 = base + 24 by bv_omega] at hbrB
  set WSL : Assertion :=
    ((.x6 : Reg) ↦ᵣ aByte) ** ((.x7 : Reg) ↦ᵣ bByte) **
    ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
    ((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
    ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
    ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    bytesRegion ptrA as ** bytesRegion ptrB bs with hWSL
  have htailLt : BitVec.ult aByte bByte →
      cpsTripleWithin 2 (base + 40) ret CR WSL
        (widxCmp32Post ptrA ptrB ret as bs) := by
    intro hc
    have hltN : (as[i]'hia).toNat < (bs[i]'hib).toNat := by
      have hc' : aByte.toNat < bByte.toNat := by
        simpa [BitVec.ult, decide_eq_true_eq] using hc
      omega
    have hlt := beBytesToNat_lt_of_prefix_lt as bs (by omega) i hia
      hpref (by rw [hgdA, hgdB]; exact hltN)
    have hne : as ≠ bs := by
      intro heq
      rw [heq] at hlt
      exact Nat.lt_irrefl _ hlt
    have h := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ aByte) ** ((.x7 : Reg) ↦ᵣ bByte) **
        ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptrA as ** bytesRegion ptrB bs)
      (by pcf)
      (widx_cmp32_tail_spec base ret 10 0
        (ptrA + BitVec.ofNat 64 i) (by decide) (by decide)
        (fun h => by simp [widxCmp32Prog] at h ⊢)
        (fun h => by simp [widxCmp32Prog] at h ⊢) halignRet)
    refine cpsTripleWithin_weaken (fun _ hp => by rw [hWSL] at hp; xperm_hyp hp)
      (fun h hq => ?_) h
    unfold widxCmp32Post
    rw [if_neg hne, if_pos hlt]
    have hq1 : (((.x6 : Reg) ↦ᵣ aByte) ** ((.x7 : Reg) ↦ᵣ bByte) **
        ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion ptrA as ** bytesRegion ptrB bs) h := by
      xperm_hyp hq
    have hq1' : (((.x6 : Reg) ↦ᵣ aByte) ** ((.x7 : Reg) ↦ᵣ bByte) **
        ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptrA as ** bytesRegion ptrB bs) h := by
      xperm_hyp hq1
    have hq2 := sepConj_mono (regIs_to_regOwn .x6 aByte)
      (sepConj_mono (regIs_to_regOwn .x7 bByte)
        (sepConj_mono (regIs_to_regOwn .x5 (BitVec.ofNat 64 (32 - i)))
          (sepConj_mono (regIs_to_regOwn .x11 (ptrB + BitVec.ofNat 64 i))
            (fun _ hh => hh)))) h hq1'
    xperm_hyp hq2
  have htailGt : BitVec.ult bByte aByte →
      cpsTripleWithin 2 (base + 56) ret CR WSL
        (widxCmp32Post ptrA ptrB ret as bs) := by
    intro hc
    have hgtN : (bs[i]'hib).toNat < (as[i]'hia).toNat := by
      have hc' : bByte.toNat < aByte.toNat := by
        simpa [BitVec.ult, decide_eq_true_eq] using hc
      omega
    have hnlt : ¬ (beBytesToNat as < beBytesToNat bs) := by
      have hrev := beBytesToNat_lt_of_prefix_lt bs as (by omega) i hib
        (fun j hj => (hpref j hj).symm)
        (by rw [hgdA, hgdB]; exact hgtN)
      intro hab
      exact Nat.lt_irrefl _ (Nat.lt_trans hab hrev)
    have hne : as ≠ bs := by
      intro heq
      have hbad : (bs[i]'hib).toNat < (bs[i]'hib).toNat := by
        simp [heq] at hgtN
      exact Nat.lt_irrefl _ hbad
    have h := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ aByte) ** ((.x7 : Reg) ↦ᵣ bByte) **
        ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptrA as ** bytesRegion ptrB bs)
      (by pcf)
      (widx_cmp32_tail_spec base ret 14 2
        (ptrA + BitVec.ofNat 64 i) (by decide) (by decide)
        (fun h => by simp [widxCmp32Prog] at h ⊢)
        (fun h => by simp [widxCmp32Prog] at h ⊢) halignRet)
    refine cpsTripleWithin_weaken (fun _ hp => by rw [hWSL] at hp; xperm_hyp hp)
      (fun h hq => ?_) h
    unfold widxCmp32Post
    rw [if_neg hne, if_neg hnlt]
    have hq1 : (((.x6 : Reg) ↦ᵣ aByte) ** ((.x7 : Reg) ↦ᵣ bByte) **
        ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x10 : Reg) ↦ᵣ (2 : Word)) ** ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion ptrA as ** bytesRegion ptrB bs) h := by
      xperm_hyp hq
    have hq1' : (((.x6 : Reg) ↦ᵣ aByte) ** ((.x7 : Reg) ↦ᵣ bByte) **
        ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
        ((.x10 : Reg) ↦ᵣ (2 : Word)) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptrA as ** bytesRegion ptrB bs) h := by
      xperm_hyp hq1
    have hq2 := sepConj_mono (regIs_to_regOwn .x6 aByte)
      (sepConj_mono (regIs_to_regOwn .x7 bByte)
        (sepConj_mono (regIs_to_regOwn .x5 (BitVec.ofNat 64 (32 - i)))
          (sepConj_mono (regIs_to_regOwn .x11 (ptrB + BitVec.ofNat 64 i))
            (fun _ hh => hh)))) h hq1'
    xperm_hyp hq2
  have hcont : ¬ BitVec.ult aByte bByte → ¬ BitVec.ult bByte aByte →
      cpsTripleWithin 4 (base + 24) (base + 4) CR WSL
        (widxCmp32Inv ptrA ptrB ret as bs (i + 1)) := by
    intro hnAB hnBA
    have hEqByte : as[i]'hia = bs[i]'hib := by
      apply BitVec.eq_of_toNat_eq
      have h1 : ¬ aByte.toNat < bByte.toNat := by
        intro hlt
        exact hnAB (by simp [BitVec.ult, decide_eq_true_eq]; omega)
      have h2 : ¬ bByte.toNat < aByte.toNat := by
        intro hgt
        exact hnBA (by simp [BitVec.ult, decide_eq_true_eq]; omega)
      omega
    have hpref' : ∀ j, j < i + 1 → as.getD j 0 = bs.getD j 0 := by
      intro j hj
      by_cases hji : j < i
      · exact hpref j hji
      · have : j = i := by omega
        subst this
        rw [hgdA, hgdB, hEqByte]
    have haddiA := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x10 (ptrA + BitVec.ofNat 64 i) (1 : BitVec 12)
        (base + 24) (by decide))
      (by
        rw [hCR]
        exact widx_cmp32_mem_at base (base + 24) 6
          (.ADDI .x10 .x10 (1 : BitVec 12)) (by bv_omega) (by decide)
          (fun _ => rfl))
    rw [widx_cmp32_cursor_advance ptrA i,
      show base + 24 + 4 = base + 28 by bv_omega] at haddiA
    have haddiB := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x11 (ptrB + BitVec.ofNat 64 i) (1 : BitVec 12)
        (base + 28) (by decide))
      (by
        rw [hCR]
        exact widx_cmp32_mem_at base (base + 28) 7
          (.ADDI .x11 .x11 (1 : BitVec 12)) (by bv_omega) (by decide)
          (fun _ => rfl))
    rw [widx_cmp32_cursor_advance ptrB i,
      show base + 28 + 4 = base + 32 by bv_omega] at haddiB
    have haddiCtr := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x5 (BitVec.ofNat 64 (32 - i)) (-1 : BitVec 12)
        (base + 32) (by decide))
      (by
        rw [hCR]
        exact widx_cmp32_mem_at base (base + 32) 8
          (.ADDI .x5 .x5 (-1 : BitVec 12)) (by bv_omega) (by decide)
          (fun _ => rfl))
    rw [widx_cmp32_counter_dec i hi,
      show base + 32 + 4 = base + 36 by bv_omega] at haddiCtr
    have hjal := liftCode (cr' := CR)
      (jal_x0_spec_gen_within (-32 : BitVec 21) (base + 36))
      (by
        rw [hCR]
        exact widx_cmp32_mem_at base (base + 36) 9
          (.JAL .x0 (-32 : BitVec 21)) (by bv_omega) (by decide)
          (fun _ => rfl))
    rw [show signExtend21 (-32 : BitVec 21) = (-32 : Word) by decide,
      show base + 36 + (-32 : Word) = base + 4 by bv_omega]
      at hjal
    have hA := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
        ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x6 : Reg) ↦ᵣ aByte) ** ((.x7 : Reg) ↦ᵣ bByte) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion ptrA as ** bytesRegion ptrB bs) (by pcf) haddiA
    have hB := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 (i + 1))) **
        ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
        ((.x6 : Reg) ↦ᵣ aByte) ** ((.x7 : Reg) ↦ᵣ bByte) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion ptrA as ** bytesRegion ptrB bs) (by pcf) haddiB
    have hC := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 (i + 1))) **
        ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 (i + 1))) **
        ((.x6 : Reg) ↦ᵣ aByte) ** ((.x7 : Reg) ↦ᵣ bByte) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion ptrA as ** bytesRegion ptrB bs) (by pcf) haddiCtr
    have hJ := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - (i + 1))) **
        ((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 (i + 1))) **
        ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 (i + 1))) **
        ((.x6 : Reg) ↦ᵣ aByte) ** ((.x7 : Reg) ↦ᵣ bByte) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion ptrA as ** bytesRegion ptrB bs) (by pcf) hjal
    have hc1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hA hB
    have hc2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc1 hC
    have hc3 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by rw [sepConj_emp_left']; xperm_hyp hp) hc2 hJ
    refine cpsTripleWithin_weaken (fun _ hp => by rw [hWSL] at hp; xperm_hyp hp)
      (fun h hq => ?_) hc3
    unfold widxCmp32Inv
    rw [sepConj_emp_left'] at hq
    refine (sepConj_pure_left h).2 ⟨hpref', ?_⟩
    have hq1 : (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - (i + 1))) **
        ((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 (i + 1))) **
        ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 (i + 1))) **
        ((.x6 : Reg) ↦ᵣ aByte) ** ((.x7 : Reg) ↦ᵣ bByte) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion ptrA as ** bytesRegion ptrB bs) h := by
      xperm_hyp hq
    have hq1' : (((.x6 : Reg) ↦ᵣ aByte) ** ((.x7 : Reg) ↦ᵣ bByte) **
        ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - (i + 1))) **
        ((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 (i + 1))) **
        ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 (i + 1))) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion ptrA as ** bytesRegion ptrB bs) h := by
      xperm_hyp hq1
    have hq2 := sepConj_mono (regIs_to_regOwn .x6 aByte)
      (sepConj_mono (regIs_to_regOwn .x7 bByte)
        (fun _ hh => hh)) h hq1'
    xperm_hyp hq2
  have htailGt4 : BitVec.ult bByte aByte →
      cpsTripleWithin 4 (base + 56) ret CR WSL
        (widxCmp32Post ptrA ptrB ret as bs) :=
    fun hc => cpsTripleWithin_mono_nSteps (by omega) (htailGt hc)
  have hstB : ¬ BitVec.ult aByte bByte →
      cpsBranchWithin (1 + 4) (base + 20) CR WSL ret
        (widxCmp32Post ptrA ptrB ret as bs) (base + 4)
        (widxCmp32Inv ptrA ptrB ret as bs (i + 1)) := by
    intro hnAB
    exact breakStation_spec (PT := WSL) (PF := WSL)
      (cpsBranchWithin_weaken
        (fun h hp => by rw [hWSL] at hp; xperm_hyp hp)
        (fun _ hq => hq) (fun _ hq => hq) hbrB)
      (fun _ hq => by xperm_hyp hq)
      (fun _ hq => by xperm_hyp hq)
      htailGt4
      (fun hnBA => cpsTripleWithin_as_cpsBranchWithin_right ret
        (widxCmp32Post ptrA ptrB ret as bs) (hcont hnAB hnBA))
  have htailLt5 : BitVec.ult aByte bByte →
      cpsTripleWithin 5 (base + 40) ret CR WSL
        (widxCmp32Post ptrA ptrB ret as bs) :=
    fun hc => cpsTripleWithin_mono_nSteps (by omega) (htailLt hc)
  have hstA : cpsBranchWithin (1 + 5) (base + 16) CR WSL ret
      (widxCmp32Post ptrA ptrB ret as bs) (base + 4)
      (widxCmp32Inv ptrA ptrB ret as bs (i + 1)) := by
    exact breakStation_spec (PT := WSL) (PF := WSL)
      (cpsBranchWithin_weaken
        (fun h hp => by rw [hWSL] at hp; xperm_hyp hp)
        (fun _ hq => hq) (fun _ hq => hq) hbrA)
      (fun _ hq => by xperm_hyp hq)
      (fun _ hq => by xperm_hyp hq)
      htailLt5
      (fun hnAB => hstB hnAB)
  have hfall := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by rw [hWSL]; xperm_hyp hp) hpre hstA
  let PFalse : Assertion :=
    ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
      ((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
      ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x6 : Reg) ↦ᵣ v6) **
      ((.x7 : Reg) ↦ᵣ v7) ** bytesRegion ptrA as ** bytesRegion ptrB bs
  have hfall' := cpsBranchWithin_weaken
    (P' := PFalse) (fun h hp => by
      dsimp [PFalse] at hp
      simp only [sepConj_assoc']
      sep_perm hp)
    (fun _ hq => hq) (fun _ hq => hq) hfall
  have hres := breakStation_spec (PT := widxCmp32Post ptrA ptrB ret as bs)
    (PF := PFalse) hbrHdr
    (fun h hq => by
      have hq1 : (⌜BitVec.ofNat 64 (32 - i) = 0⌝ **
          ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
          ((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
          ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
          bytesRegion ptrA as ** bytesRegion ptrB bs) h := by
        xperm_hyp hq
      obtain ⟨hc, hrest⟩ := (sepConj_pure_left h).1 hq1
      exact False.elim ((widx_cmp32_counter_ne_zero i hi) hc))
    (fun h hq => by
      have hq1 : (⌜¬ BitVec.ofNat 64 (32 - i) = 0⌝ **
          ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
          ((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
          ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
          bytesRegion ptrA as ** bytesRegion ptrB bs) h := by
        xperm_hyp hq
      obtain ⟨hc, hrest⟩ := (sepConj_pure_left h).1 hq1
      have hrest' : PFalse h := by
        have hr : (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (32 - i)) **
            ((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 i)) **
            ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 i)) **
            ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
            bytesRegion ptrA as ** bytesRegion ptrB bs) h := by
          xperm_hyp hrest
        dsimp [PFalse]
        sep_perm hr
      exact (sepConj_pure_left h).2 ⟨hc, hrest'⟩)
    (fun hc => absurd hc (widx_cmp32_counter_ne_zero i hi))
    (fun _ => hfall')
  exact cpsBranchWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq) hres

private theorem widx_cmp32_exh
    (base ret ptrA ptrB : Word) (as bs : List (BitVec 8))
    (hlenA : as.length = 32) (hlenB : bs.length = 32)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 3 (base + 4) ret
      (CodeReq.ofProg base widxCmp32Prog)
      (widxCmp32Inv ptrA ptrB ret as bs 32)
      (widxCmp32Post ptrA ptrB ret as bs) := by
  set CR := CodeReq.ofProg base widxCmp32Prog with hCR
  unfold widxCmp32Inv
  refine cpsTripleWithin_pure_pre (fun hpref => ?_)
  have hEq : as = bs := bytes_eq_of_prefix_all as bs (by omega)
    (fun j hj => hpref j (by omega))
  have hbrHdr := cpsBranchWithin_frameR
    (((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 32)) **
      ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 32)) **
      ((.x1 : Reg) ↦ᵣ ret) ** regOwn .x6 ** regOwn .x7 **
      bytesRegion ptrA as ** bytesRegion ptrB bs)
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := beq_spec_gen_within .x5 .x0 (44 : BitVec 13)
        (BitVec.ofNat 64 (32 - 32)) (0 : Word) (base + 4))
      (hmono := by
        rw [hCR]
        exact widx_cmp32_mem_at base (base + 4) 1
          (.BEQ .x5 .x0 (44 : BitVec 13)) (by bv_omega) (by decide)
          (fun _ => rfl)))
  rw [show signExtend13 (44 : BitVec 13) = (44 : Word) by decide,
      show (base + 4) + (44 : Word) = base + 48 by bv_omega,
      show (base + 4) + 4 = base + 8 by bv_omega] at hbrHdr
  have htail0 := widx_cmp32_tail_spec base ret 12 1
    (ptrA + BitVec.ofNat 64 32) (by decide) (by decide)
    (fun h => by simp [widxCmp32Prog] at h ⊢)
    (fun h => by simp [widxCmp32Prog] at h ⊢) halignRet
  have htail := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 0) **
      ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 32)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x6 ** regOwn .x7 **
      bytesRegion ptrA as ** bytesRegion ptrB bs)
    (by pcf) htail0
  have htail' := cpsTripleWithin_weaken
    (P' := (((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 32)) **
      ((.x1 : Reg) ↦ᵣ ret)) **
      ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 0) **
      ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 32)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x6 ** regOwn .x7 **
      bytesRegion ptrA as ** bytesRegion ptrB bs)
    (Q' := widxCmp32Post ptrA ptrB ret as bs)
    (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      unfold widxCmp32Post
      rw [if_pos hEq]
      have hq1 : (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 0) **
          ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 32)) **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x6 ** regOwn .x7 ** bytesRegion ptrA as **
          bytesRegion ptrB bs) h := by
        xperm_hyp hq
      have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
        (sepConj_mono (regIs_to_regOwn .x11 _)
          (fun _ hh => hh)) h hq1
      sep_perm hq2)
    htail
  let PT : Assertion :=
    (((.x10 : Reg) ↦ᵣ (ptrA + BitVec.ofNat 64 32)) **
      ((.x1 : Reg) ↦ᵣ ret)) **
      ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 0) **
      ((.x11 : Reg) ↦ᵣ (ptrB + BitVec.ofNat 64 32)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x6 ** regOwn .x7 **
      bytesRegion ptrA as ** bytesRegion ptrB bs
  let PF : Assertion := PT
  have hjoin := retJoinStation_spec
    (cond := (BitVec.ofNat 64 (32 - 32) = (0 : Word)))
    (PT := PT) (PF := PF)
    hbrHdr
    (fun _ hq => by xperm_hyp hq)
    (fun _ hq => by xperm_hyp hq)
    (fun _ => htail')
    (fun hc => absurd (by decide :
      (BitVec.ofNat 64 (32 - 32) : Word) = (0 : Word)) hc)
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq)
    hjoin

theorem widx_cmp32_spec
    (base ret ptrA ptrB : Word) (as bs : List (BitVec 8))
    (hlenA : as.length = 32) (hlenB : bs.length = 32)
    (halignA : ptrA.toNat % 8 = 0) (halignB : ptrB.toNat % 8 = 0)
    (hovA : ptrA.toNat + 32 < 2 ^ 64)
    (hovB : ptrB.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ k, k < 32 →
      isValidByteAccess (ptrA + BitVec.ofNat 64 k) = true)
    (hvalidB : ∀ k, k < 32 →
      isValidByteAccess (ptrB + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 293 base ret
      (CodeReq.ofProg base widxCmp32Prog)
      (regOwn .x5 ** ((.x10 : Reg) ↦ᵣ ptrA) ** ((.x11 : Reg) ↦ᵣ ptrB) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x6 ** regOwn .x7 ** bytesRegion ptrA as ** bytesRegion ptrB bs)
      (widxCmp32Post ptrA ptrB ret as bs) := by
  set CR := CodeReq.ofProg base widxCmp32Prog with hCR
  let P0 : Assertion :=
    ((.x10 : Reg) ↦ᵣ ptrA) ** ((.x11 : Reg) ↦ᵣ ptrB) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x6 ** regOwn .x7 ** bytesRegion ptrA as ** bytesRegion ptrB bs
  have hli := liftCode (cr' := CR)
    (li_spec_gen_own_within .x5 (32 : Word) base (by decide))
    (by
      rw [hCR]
      exact widx_cmp32_mem_at base base 0
        (.LI .x5 (32 : Word)) (by bv_omega) (by decide)
        (fun _ => by simp [widxCmp32Prog]))
  rw [show base + 4 = base + 4 by rfl] at hli
  have hliF := cpsTripleWithin_frameR
    (P0) (by pcf) hli
  have hloop := twoBreakRetLoop_spec (hdr := base + 4) (ret := ret)
    (cr := CR) (Q := widxCmp32Post ptrA ptrB ret as bs) 32 9 4
    (widxCmp32Inv ptrA ptrB ret as bs)
    (fun i hi => widx_cmp32_iter base ret ptrA ptrB as bs hlenA hlenB
      halignA halignB hovA hovB hvalidA hvalidB halignRet i hi)
    (cpsTripleWithin_mono_nSteps (by decide)
      (widx_cmp32_exh base ret ptrA ptrB as bs hlenA hlenB
        halignRet))
  have hloop' := cpsTripleWithin_weaken
    (P' := P0 ** ((.x5 : Reg) ↦ᵣ (32 : Word)))
    (fun h hp => by
      unfold widxCmp32Inv
      exact (sepConj_pure_left h).2 ⟨
        (fun _ hj => by omega), by
          dsimp [P0] at hp
          sep_perm hp⟩)
    (fun _ hq => hq) hloop
  have hchain := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hliF hloop'
  simpa [P0] using hchain

/-! ## `widx_swap_records`

The helper swaps two six-dword records in place.  The machine model has one
writable-region resource, so its contract deliberately uses one arena and
record offsets rather than two independent `bytesRegion` atoms.  The offsets
are explicit in the invariant; they are not existentially hidden. -/

def widxSwapMem (arena : List (BitVec 8)) (qa qb : Nat) : Nat → List (BitVec 8)
  | 0 => arena
  | n + 1 =>
      let old := widxSwapMem arena qa qb n
      let va := packBytes ((old.drop (8 * (qa + n))).take 8)
      let vb := packBytes ((old.drop (8 * (qb + n))).take 8)
      setBytes (setBytes old (8 * (qa + n)) (dwordBytes vb))
        (8 * (qb + n)) (dwordBytes va)

@[simp] theorem widxSwapMem_zero (arena : List (BitVec 8)) (qa qb : Nat) :
    widxSwapMem arena qa qb 0 = arena := rfl

@[simp] theorem widxSwapMem_succ (arena : List (BitVec 8)) (qa qb n : Nat) :
    widxSwapMem arena qa qb (n + 1) =
      let old := widxSwapMem arena qa qb n
      let va := packBytes ((old.drop (8 * (qa + n))).take 8)
      let vb := packBytes ((old.drop (8 * (qb + n))).take 8)
      setBytes (setBytes old (8 * (qa + n)) (dwordBytes vb))
        (8 * (qb + n)) (dwordBytes va) := rfl

@[simp] theorem widxSwapMem_length (arena : List (BitVec 8)) (qa qb n : Nat) :
    (widxSwapMem arena qa qb n).length = arena.length := by
  induction n with
  | zero => rfl
  | succ n ih => simp [widxSwapMem, ih]

def widxSwapInv (arenaBase : Word) (arena : List (BitVec 8))
    (qa qb : Nat) (ret : Word) (n : Nat) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qa + n)))) **
    ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qb + n)))) **
    ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (6 - n)) **
    ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    regOwn .x5 ** regOwn .x31 **
    bytesRegion arenaBase (widxSwapMem arena qa qb n)

def widxSwapPost (arenaBase : Word) (arena : List (BitVec 8))
    (qa qb : Nat) (ret : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qa + 6)))) **
    ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qb + 6)))) **
    ((.x6 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x31 **
    bytesRegion arenaBase (widxSwapMem arena qa qb 6)

def widxSwapProg : List Instr :=
  [ .BEQ .x10 .x11 (44 : BitVec 13),
    .LI .x6 (6 : Word),
    .BEQ .x6 .x0 (36 : BitVec 13),
    .LD .x5 .x10 (0 : BitVec 12),
    .LD .x31 .x11 (0 : BitVec 12),
    .SD .x10 .x31 (0 : BitVec 12),
    .SD .x11 .x5 (0 : BitVec 12),
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x11 .x11 (8 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

@[simp] theorem widxSwapProg_length : widxSwapProg.length = 12 := by
  simp [widxSwapProg]

private theorem widx_swap_mem_at (base A : Word) (k : Nat) (ins : Instr)
    (hA : A = base + BitVec.ofNat 64 (4 * k)) (hk : k < 12)
    (hins : ∀ h : k < widxSwapProg.length, widxSwapProg[k]'h = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i →
      CodeReq.ofProg base widxSwapProg a = some i := by
  have hk' : k < widxSwapProg.length := by
    rw [widxSwapProg_length]
    exact hk
  exact CodeReq.ofProg_mem_at base A _ k ins hA hk' (hins hk') (by
    rw [widxSwapProg_length]
    decide)

private theorem widx_swap_cursor_advance8 (p : Word) (q : Nat) :
    p + BitVec.ofNat 64 (8 * q) + signExtend12 (8 : BitVec 12) =
      p + BitVec.ofNat 64 (8 * (q + 1)) := by
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show ((8 : Word)).toNat = 8 from rfl,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem widx_swap_counter_dec (n : Nat) (hn : n < 6) :
    BitVec.ofNat 64 (6 - n) + signExtend12 (-1 : BitVec 12) =
      BitVec.ofNat 64 (6 - (n + 1)) := by
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show ((-1 : Word)).toNat = 18446744073709551615 from rfl]
  omega

private theorem widx_swap_body_concrete
    (base arenaBase : Word) (arena : List (BitVec 8))
    (qa qb n : Nat) (ret v5 v31 : Word)
    (hn : n < 6)
    (hA : 8 * (qa + n) + 8 ≤ (widxSwapMem arena qa qb n).length)
    (hB : 8 * (qb + n) + 8 ≤ (widxSwapMem arena qa qb n).length) :
    cpsTripleWithin 8 (base + 12) (base + 8)
      (CodeReq.ofProg base widxSwapProg)
      (((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qa + n)))) **
       ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qb + n)))) **
       ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (6 - n)) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x31 : Reg) ↦ᵣ v31) **
       bytesRegion arenaBase (widxSwapMem arena qa qb n))
      (widxSwapInv arenaBase arena qa qb ret (n + 1)) := by
  let CR : CodeReq := CodeReq.ofProg base widxSwapProg
  let old := widxSwapMem arena qa qb n
  let va := packBytes ((old.drop (8 * (qa + n))).take 8)
  let vb := packBytes ((old.drop (8 * (qb + n))).take 8)
  have hA_old : 8 * (qa + n) + 8 ≤ old.length := by simpa [old] using hA
  have hB_old : 8 * (qb + n) + 8 ≤ old.length := by simpa [old] using hB
  have hqA : 8 * (qa + n) < old.length := by omega
  have hqB : 8 * (qb + n) < old.length := by omega
  have hA' := bytesRegion_ld_cursor_imm_within .x5 .x10 arenaBase v5
    (base + 12) old (qa + n) 0 (by decide) hqA (by decide)
  have hB' := bytesRegion_ld_cursor_imm_within .x31 .x11 arenaBase v31
    (base + 16) old (qb + n) 0 (by decide) hqB (by decide)
  have hAcode := cpsTripleWithin_extend_code
    (hmono := fun a i h => widx_swap_mem_at base (base + 12) 3 _
      (by bv_omega) (by decide) (fun h => by simp [widxSwapProg] at h ⊢) a i h)
    hA'
  have hBcode := cpsTripleWithin_extend_code
    (hmono := fun a i h => widx_swap_mem_at base (base + 16) 4 _
      (by bv_omega) (by decide) (fun h => by simp [widxSwapProg] at h ⊢) a i h)
    hB'
  have hAframe := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qb + n)))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (6 - n)) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x31 : Reg) ↦ᵣ v31))
    (by pcFree) hAcode
  rw [show (base + 12) + 4 = base + 16 by bv_omega] at hAframe
  simp only [old, Nat.add_zero] at hAframe
  have hBframe := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qa + n)))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (6 - n)) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x5 : Reg) ↦ᵣ
        packBytes (List.take 8 (List.drop (8 * (qa + n)) old))))
    (by pcFree) hBcode
  simp only [old, Nat.add_zero] at hBframe
  have hloads := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hAframe hBframe
  rw [show (base + 16) + 4 = base + 20 by bv_omega] at hloads
  have hsdA' := bytesRegion_sd_cursor_within .x10 .x31 arenaBase vb
    (base + 20) old (qa + n) hA_old
  have hsdB' := bytesRegion_sd_cursor_within .x11 .x5 arenaBase va
      (base + 24)
      (setBytes old (8 * (qa + n)) (dwordBytes vb)) (qb + n) (by
        simpa [length_setBytes] using hB_old)
  rw [show (base + 24) + 4 = base + 28 by bv_omega] at hsdB'
  have hsdAcode := cpsTripleWithin_extend_code
    (hmono := fun a i h => widx_swap_mem_at base (base + 20) 5 _
      (by bv_omega) (by decide) (fun h => by simp [widxSwapProg] at h ⊢) a i h)
    hsdA'
  have hsdBcode := cpsTripleWithin_extend_code
    (hmono := fun a i h => widx_swap_mem_at base (base + 24) 6 _
      (by bv_omega) (by decide) (fun h => by simp [widxSwapProg] at h ⊢) a i h)
    hsdB'
  have hsdAframe := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qb + n)))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (6 - n)) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x5 : Reg) ↦ᵣ va))
    (by pcFree) hsdAcode
  rw [show (base + 20) + 4 = base + 24 by bv_omega] at hsdAframe
  have hsdBframe := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qa + n)))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (6 - n)) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x31 : Reg) ↦ᵣ vb))
    (by pcFree) hsdBcode
  have hstores := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hsdAframe hsdBframe
  have haddiA := cpsTripleWithin_extend_code
    (hmono := fun a i h => widx_swap_mem_at base (base + 28) 7 _
      (by bv_omega) (by decide) (fun h => by simp [widxSwapProg] at h ⊢) a i h)
    (addi_spec_gen_same_within .x10
      (arenaBase + BitVec.ofNat 64 (8 * (qa + n))) (8 : BitVec 12)
      (base + 28) (by decide))
  have haddiB := cpsTripleWithin_extend_code
    (hmono := fun a i h => widx_swap_mem_at base (base + 32) 8 _
      (by bv_omega) (by decide) (fun h => by simp [widxSwapProg] at h ⊢) a i h)
    (addi_spec_gen_same_within .x11
      (arenaBase + BitVec.ofNat 64 (8 * (qb + n))) (8 : BitVec 12)
      (base + 32) (by decide))
  have haddiC := cpsTripleWithin_extend_code
    (hmono := fun a i h => widx_swap_mem_at base (base + 36) 9 _
      (by bv_omega) (by decide) (fun h => by simp [widxSwapProg] at h ⊢) a i h)
    (addi_spec_gen_same_within .x6 (BitVec.ofNat 64 (6 - n))
      (-1 : BitVec 12) (base + 36) (by decide))
  rw [widx_swap_cursor_advance8 arenaBase (qa + n)] at haddiA
  rw [widx_swap_cursor_advance8 arenaBase (qb + n)] at haddiB
  rw [widx_swap_counter_dec n (by omega)] at haddiC
  rw [show (base + 28) + 4 = base + 32 by bv_omega] at haddiA
  rw [show (base + 32) + 4 = base + 36 by bv_omega] at haddiB
  rw [show (base + 36) + 4 = base + 40 by bv_omega] at haddiC
  have hjump := cpsTripleWithin_extend_code
    (hmono := fun a i h => widx_swap_mem_at base (base + 40) 10 _
      (by bv_omega) (by decide) (fun h => by simp [widxSwapProg] at h ⊢) a i h)
    (jal_x0_spec_gen_within (-32 : BitVec 21) (base + 40))
  rw [show signExtend21 (-32 : BitVec 21) = (-32 : Word) from by decide] at hjump
  rw [show (base + 40) + (-32 : Word) = base + 8 by bv_omega] at hjump
  have haddiAframe := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qb + n)))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (6 - n)) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ va) **
      ((.x31 : Reg) ↦ᵣ vb) **
      bytesRegion arenaBase
        (setBytes (setBytes old (8 * (qa + n)) (dwordBytes vb))
          (8 * (qb + n)) (dwordBytes va))) (by
            pcFree
            all_goals exact bytesRegion_pcFree _ _) haddiA
  have haddiBframe := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qa + n + 1)))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (6 - n)) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ va) **
      ((.x31 : Reg) ↦ᵣ vb) **
      bytesRegion arenaBase
        (setBytes (setBytes old (8 * (qa + n)) (dwordBytes vb))
          (8 * (qb + n)) (dwordBytes va))) (by
            pcFree
            all_goals exact bytesRegion_pcFree _ _) haddiB
  have haddiCframe := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qa + n + 1)))) **
      ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qb + n + 1)))) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x5 : Reg) ↦ᵣ va) ** ((.x31 : Reg) ↦ᵣ vb) **
      bytesRegion arenaBase
        (setBytes (setBytes old (8 * (qa + n)) (dwordBytes vb))
          (8 * (qb + n)) (dwordBytes va))) (by
            pcFree
            all_goals exact bytesRegion_pcFree _ _) haddiC
  have hjumpFrame := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qa + n + 1)))) **
      ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qb + n + 1)))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (6 - (n + 1))) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x5 : Reg) ↦ᵣ va) ** ((.x31 : Reg) ↦ᵣ vb) **
      bytesRegion arenaBase
        (setBytes (setBytes old (8 * (qa + n)) (dwordBytes vb))
          (8 * (qb + n)) (dwordBytes va))) (by
            pcFree
            all_goals exact bytesRegion_pcFree _ _) hjump
  have hjumpFrame' := hjumpFrame
  simp only [sepConj_emp_left'] at hjumpFrame'
  have hchain := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hloads hstores
  have hchain := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hchain haddiAframe
  have hchain := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hchain haddiBframe
  have hchain := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hchain haddiCframe
  have hchain := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hchain hjumpFrame'
  let Ptarget : Assertion :=
    ((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qa + n)))) **
      ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qb + n)))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (6 - n)) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x5 : Reg) ↦ᵣ v5) ** ((.x31 : Reg) ↦ᵣ v31) **
      bytesRegion arenaBase old
  let Qtarget : Assertion :=
    ((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qa + n + 1)))) **
      ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qb + n + 1)))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (6 - (n + 1))) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x31 **
      bytesRegion arenaBase
        (setBytes (setBytes old (8 * (qa + n)) (dwordBytes vb))
          (8 * (qb + n)) (dwordBytes va))
  have hchain' := cpsTripleWithin_weaken
    (P' := Ptarget) (Q' := Qtarget)
    (fun _ hp => by
      dsimp [Ptarget] at hp
      simp only [sepConj_assoc']
      sep_perm hp)
    (fun h hq => by
      dsimp [Qtarget]
      have hq1 :
          (((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qa + n + 1)))) **
            ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qb + n + 1)))) **
            ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (6 - (n + 1))) **
            ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            regOwn .x5 ** regOwn .x31 **
            bytesRegion arenaBase
              (setBytes (setBytes old (8 * (qa + n)) (dwordBytes vb))
                (8 * (qb + n)) (dwordBytes va))) h := by
        exact (sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono_right
              (sepConj_mono_right
                (sepConj_mono (regIs_to_regOwn .x5 va)
                  (sepConj_mono (regIs_to_regOwn .x31 vb) (fun _ h => h)))))))) h hq
      exact hq1)
    hchain
  simpa [widxSwapInv, Ptarget, Qtarget, old, va, vb, widxSwapMem,
    Nat.add_assoc] using hchain'

private theorem widx_swap_body
    (base arenaBase : Word) (arena : List (BitVec 8))
    (qa qb n : Nat) (ret : Word)
    (hn : n < 6)
    (hA : 8 * (qa + n) + 8 ≤ (widxSwapMem arena qa qb n).length)
    (hB : 8 * (qb + n) + 8 ≤ (widxSwapMem arena qa qb n).length) :
    cpsTripleWithin 8 (base + 12) (base + 8)
      (CodeReq.ofProg base widxSwapProg)
      (widxSwapInv arenaBase arena qa qb ret n)
      (widxSwapInv arenaBase arena qa qb ret (n + 1)) := by
  let CR : CodeReq := CodeReq.ofProg base widxSwapProg
  have hbeq := cpsBranchWithin_extend_code (cr' := CR)
    (h := beq_spec_gen_within .x6 .x0 (36 : BitVec 13)
      (BitVec.ofNat 64 (6 - n)) (0 : Word) (base + 8))
    (hmono := fun a i h => widx_swap_mem_at base (base + 8) 2 _
      (by bv_omega) (by decide) (fun h => by simp [widxSwapProg] at h ⊢) a i h)
  rw [show signExtend13 (36 : BitVec 13) = (36 : Word) by decide,
    show (base + 8) + (36 : Word) = base + 44 by bv_omega,
    show (base + 8) + 4 = base + 12 by bv_omega] at hbeq
  have hhead0 := cpsBranchWithin_frameR
    (((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qa + n)))) **
      ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qb + n)))) **
      ((.x1 : Reg) ↦ᵣ ret) ** regOwn .x5 ** regOwn .x31 **
      bytesRegion arenaBase (widxSwapMem arena qa qb n)) (by pcf) hbeq
  let headRest : Assertion :=
    ((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qa + n)))) **
      ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qb + n)))) **
      ((.x1 : Reg) ↦ᵣ ret) ** regOwn .x5 ** regOwn .x31 **
      bytesRegion arenaBase (widxSwapMem arena qa qb n)
  let headSrc : Assertion :=
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (6 - n)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) ** headRest
  let headT : Assertion :=
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (6 - n)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ⌜BitVec.ofNat 64 (6 - n) = 0⌝) ** headRest
  let headF : Assertion :=
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (6 - n)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ⌜BitVec.ofNat 64 (6 - n) ≠ 0⌝) ** headRest
  have hhead :
      cpsBranchWithin 1 (base + 8) CR (widxSwapInv arenaBase arena qa qb ret n)
        (base + 44) (widxSwapInv arenaBase arena qa qb ret n)
        (base + 12) (widxSwapInv arenaBase arena qa qb ret n) := by
    refine cpsBranchWithin_weaken
      (P := headSrc) (Q_t := headT) (Q_f := headF)
      (P' := widxSwapInv arenaBase arena qa qb ret n)
      (Q_t' := widxSwapInv arenaBase arena qa qb ret n)
      (Q_f' := widxSwapInv arenaBase arena qa qb ret n)
      (fun _ hp => by
        try dsimp [headSrc, headRest, widxSwapInv] at hp ⊢
        sep_perm hp)
      (fun h hq => by
        have hq' := sepConj_mono_left (sepConj_strip_pure_end2) h hq
        try dsimp [headT, headRest, widxSwapInv] at hq' ⊢
        sep_perm hq')
      (fun h hq => by
        have hq' := sepConj_mono_left (sepConj_strip_pure_end2) h hq
        try dsimp [headF, headRest, widxSwapInv] at hq' ⊢
        sep_perm hq') hhead0
  let preA : Assertion :=
    ((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qa + n)))) **
      ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qb + n)))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (6 - n)) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word))
  let memA : Assertion := bytesRegion arenaBase (widxSwapMem arena qa qb n)
  have hforall : ∀ vf : Reg → Word,
      cpsTripleWithin 8 (base + 12) (base + 8)
    CR
        ((preA ** memA) ** regAtomsOf vf [.x5, .x31])
        (widxSwapInv arenaBase arena qa qb ret (n + 1)) := by
    intro vf
    have hcon := widx_swap_body_concrete base arenaBase arena qa qb n ret
      (vf .x5) (vf .x31) hn hA hB
    exact cpsTripleWithin_weaken
      (P' := (preA ** memA) ** regAtomsOf vf [.x5, .x31])
      (fun _ hp => by
        dsimp [preA, memA] at hp ⊢
        try simp only [sepConj_emp_right'] at hp ⊢
        sep_perm hp)
      (fun _ hq => hq) hcon
  have hpeel := cpsTripleWithin_peel_regOwns [ .x5, .x31 ] (by decide)
    (P := preA ** memA) hforall
  unfold widxSwapInv
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [preA, memA] at hp ⊢
      try simp only [sepConj_emp_right'] at hp ⊢
      sep_perm hp)
    (fun _ hq => hq) hpeel

private theorem widx_swap_head
    (base arenaBase : Word) (arena : List (BitVec 8))
    (qa qb n : Nat) (ret : Word) :
    cpsBranchWithin 1 (base + 8) (CodeReq.ofProg base widxSwapProg)
      (widxSwapInv arenaBase arena qa qb ret n)
      (base + 44) (widxSwapInv arenaBase arena qa qb ret n)
      (base + 12) (widxSwapInv arenaBase arena qa qb ret n) := by
  let CR : CodeReq := CodeReq.ofProg base widxSwapProg
  have hbeq := cpsBranchWithin_extend_code (cr' := CR)
    (h := beq_spec_gen_within .x6 .x0 (36 : BitVec 13)
      (BitVec.ofNat 64 (6 - n)) (0 : Word) (base + 8))
    (hmono := fun a i h => widx_swap_mem_at base (base + 8) 2 _
      (by bv_omega) (by decide) (fun h => by simp [widxSwapProg] at h ⊢) a i h)
  rw [show signExtend13 (36 : BitVec 13) = (36 : Word) by decide,
    show (base + 8) + (36 : Word) = base + 44 by bv_omega,
    show (base + 8) + 4 = base + 12 by bv_omega] at hbeq
  have hhead0 := cpsBranchWithin_frameR
    (((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qa + n)))) **
      ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qb + n)))) **
      ((.x1 : Reg) ↦ᵣ ret) ** regOwn .x5 ** regOwn .x31 **
      bytesRegion arenaBase (widxSwapMem arena qa qb n)) (by pcf) hbeq
  let headRest : Assertion :=
    ((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qa + n)))) **
      ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qb + n)))) **
      ((.x1 : Reg) ↦ᵣ ret) ** regOwn .x5 ** regOwn .x31 **
      bytesRegion arenaBase (widxSwapMem arena qa qb n)
  let headSrc : Assertion :=
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (6 - n)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) ** headRest
  let headT : Assertion :=
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (6 - n)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ⌜BitVec.ofNat 64 (6 - n) = 0⌝) ** headRest
  let headF : Assertion :=
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (6 - n)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ⌜BitVec.ofNat 64 (6 - n) ≠ 0⌝) ** headRest
  refine cpsBranchWithin_weaken
    (P := headSrc) (Q_t := headT) (Q_f := headF)
    (P' := widxSwapInv arenaBase arena qa qb ret n)
    (Q_t' := widxSwapInv arenaBase arena qa qb ret n)
    (Q_f' := widxSwapInv arenaBase arena qa qb ret n)
    (fun _ hp => by
      try dsimp [headSrc, headRest, widxSwapInv] at hp ⊢
      sep_perm hp)
    (fun h hq => by
      have hq' := sepConj_mono_left (sepConj_strip_pure_end2) h hq
      try dsimp [headT, headRest, widxSwapInv] at hq' ⊢
      sep_perm hq')
    (fun h hq => by
      have hq' := sepConj_mono_left (sepConj_strip_pure_end2) h hq
      try dsimp [headF, headRest, widxSwapInv] at hq' ⊢
      sep_perm hq') hhead0


private theorem widx_swap_head_false2
    (base arenaBase : Word) (arena : List (BitVec 8))
    (qa qb n : Nat) (ret : Word) (hn : n < 6) :
    cpsTripleWithin 1 (base + 8) (base + 12)
      (CodeReq.ofProg base widxSwapProg)
      (widxSwapInv arenaBase arena qa qb ret n)
      (widxSwapInv arenaBase arena qa qb ret n) := by
  let CR : CodeReq := CodeReq.ofProg base widxSwapProg
  have hbeq := cpsBranchWithin_extend_code (cr' := CR)
    (h := beq_spec_gen_within .x6 .x0 (36 : BitVec 13)
      (BitVec.ofNat 64 (6 - n)) (0 : Word) (base + 8))
    (hmono := fun a i h => widx_swap_mem_at base (base + 8) 2 _
      (by bv_omega) (by decide) (fun h => by simp [widxSwapProg] at h ⊢) a i h)
  rw [show signExtend13 (36 : BitVec 13) = (36 : Word) by decide,
    show (base + 8) + (36 : Word) = base + 44 by bv_omega,
    show (base + 8) + 4 = base + 12 by bv_omega] at hbeq
  have hframe := cpsBranchWithin_frameR
    (((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qa + n)))) **
      ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qb + n)))) **
      ((.x1 : Reg) ↦ᵣ ret) ** regOwn .x5 ** regOwn .x31 **
      bytesRegion arenaBase (widxSwapMem arena qa qb n)) (by pcf) hbeq
  have hfalse := cpsBranchWithin_ntakenPath hframe
    (fun _ hq => by
      obtain ⟨h1, _, _, _, hleft, _⟩ := hq
      obtain ⟨h6, h0pure, _, _, hx6, hx0pure⟩ := hleft
      have heq := ((sepConj_pure_right
        (P := ((.x0 : Reg) ↦ᵣ (0 : Word)))
        (Q := BitVec.ofNat 64 (6 - n) = (0 : Word)) h0pure).1 hx0pure).2
      have hnonzero : BitVec.ofNat 64 (6 - n) ≠ (0 : Word) := by
        intro hz
        have hz' := congrArg BitVec.toNat hz
        simp at hz'
        omega
      exact hnonzero heq)
  refine cpsTripleWithin_weaken
    (P' := widxSwapInv arenaBase arena qa qb ret n)
    (Q' := widxSwapInv arenaBase arena qa qb ret n)
    (fun _ hp => by
      dsimp [widxSwapInv] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      dsimp [widxSwapInv] at hq ⊢
      have hq' := sepConj_mono_left (sepConj_strip_pure_end2) _ hq
      xperm_hyp hq') hfalse

/-- The complete swap is exactly 58 steps: the entry BEQ and LI (2), six
    rounds of a header BEQ plus the eight-instruction swap body (6 * 9), the
    terminal header BEQ (1), and the JALR return (1). -/
theorem widx_swap_records_spec
    (base arenaBase : Word) (arena : List (BitVec 8))
    (qa qb : Nat) (ret : Word)
    (hneq : arenaBase + BitVec.ofNat 64 (8 * qa) ≠
      arenaBase + BitVec.ofNat 64 (8 * qb))
    (hA : 8 * (qa + 6) + 8 ≤ arena.length)
    (hB : 8 * (qb + 6) + 8 ≤ arena.length)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 58 base ret (CodeReq.ofProg base widxSwapProg)
      (widxSwapInv arenaBase arena qa qb ret 0)
      (widxSwapPost arenaBase arena qa qb ret) := by
  let CR : CodeReq := CodeReq.ofProg base widxSwapProg
  let rest0 : Assertion :=
    ((.x6 : Reg) ↦ᵣ (6 : Word)) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x31 **
      bytesRegion arenaBase arena
  have hbeq0 := cpsBranchWithin_extend_code (cr' := CR)
    (h := beq_spec_gen_within .x10 .x11 (44 : BitVec 13)
      (arenaBase + BitVec.ofNat 64 (8 * qa))
      (arenaBase + BitVec.ofNat 64 (8 * qb)) base)
    (hmono := fun a i h => widx_swap_mem_at base base 0 _
      (by bv_omega) (by decide) (fun h => by simp [widxSwapProg] at h ⊢) a i h)
  rw [show signExtend13 (44 : BitVec 13) = (44 : Word) by decide,
    show base + (44 : Word) = base + 44 by rfl,
    show base + 4 = base + 4 by rfl] at hbeq0
  have hbeq0f := cpsBranchWithin_frameR rest0 (by pcf) hbeq0
  let p0 : Assertion :=
    ((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * qa))) **
      ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * qb))) ** rest0
  let qt0 : Assertion :=
    (((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * qa))) **
      ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * qb))) ** rest0) **
      ⌜arenaBase + BitVec.ofNat 64 (8 * qa) =
        arenaBase + BitVec.ofNat 64 (8 * qb)⌝
  let qf0 : Assertion :=
    ((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * qa))) **
      ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * qb))) ** rest0 **
      ⌜arenaBase + BitVec.ofNat 64 (8 * qa) ≠
        arenaBase + BitVec.ofNat 64 (8 * qb)⌝
  have hbeq0' : cpsBranchWithin 1 base CR p0 (base + 44) qt0 (base + 4) qf0 := by
    refine cpsBranchWithin_weaken
      (P := (((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * qa))) **
        ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * qb)))) ** rest0)
      (Q_t := (((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * qa))) **
        ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * qb))) **
        ⌜arenaBase + BitVec.ofNat 64 (8 * qa) = arenaBase + BitVec.ofNat 64 (8 * qb)⌝) ** rest0)
      (Q_f := (((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * qa))) **
        ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * qb))) **
        ⌜arenaBase + BitVec.ofNat 64 (8 * qa) ≠ arenaBase + BitVec.ofNat 64 (8 * qb)⌝) ** rest0)
      (P' := p0) (Q_t' := qt0) (Q_f' := qf0)
      (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        simp [qt0, Nat.mul_comm] at hq ⊢
        sep_perm hq)
      (fun _ hq => by
        simp [qf0, Nat.mul_comm] at hq ⊢
        sep_perm hq) hbeq0f
  have hnot0 := cpsBranchWithin_ntakenStripPure3
    (Q_t := qt0)
    (A := ((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * qa))))
    (B := ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * qb))))
    (C := rest0)
    (Prop_f := arenaBase + BitVec.ofNat 64 (8 * qa) ≠
      arenaBase + BitVec.ofNat 64 (8 * qb)) hbeq0'
    (fun _ hq => by
      have heq := ((sepConj_pure_right
        (P := (((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * qa))) **
          ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * qb))) ** rest0))
        (Q := arenaBase + BitVec.ofNat 64 (8 * qa) =
          arenaBase + BitVec.ofNat 64 (8 * qb)) _).1 hq).2
      exact hneq heq)
  let restNoX6 : Assertion :=
    ((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * qa))) **
      ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * qb))) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x31 ** bytesRegion arenaBase arena
  have hli0 := cpsTripleWithin_extend_code
    (hmono := fun a i h => widx_swap_mem_at base (base + 4) 1 _
      (by bv_omega) (by decide) (fun h => by simp [widxSwapProg] at h ⊢) a i h)
    (li_spec_gen_within .x6 (6 : Word) (6 : Word) (base + 4) (by decide))
  rw [show (base + 4) + 4 = base + 8 by bv_omega] at hli0
  have hli := cpsTripleWithin_frameR restNoX6 (by pcf) hli0
  have hinit := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hnot0 hli
  have hround : ∀ j, j < 6 →
      cpsTripleWithin 9 (base + 8) (base + 8) CR
        (widxSwapInv arenaBase arena qa qb ret j)
        (widxSwapInv arenaBase arena qa qb ret (j + 1)) := by
    intro j hj
    have hAj : 8 * (qa + j) + 8 ≤ (widxSwapMem arena qa qb j).length := by
      rw [widxSwapMem_length]
      omega
    have hBj : 8 * (qb + j) + 8 ≤ (widxSwapMem arena qa qb j).length := by
      rw [widxSwapMem_length]
      omega
    have hh := widx_swap_head_false2 base arenaBase arena qa qb j ret hj
    have hb := widx_swap_body base arenaBase arena qa qb j ret hj hAj hBj
    exact cpsTripleWithin_seq_same_cr hh hb
  have hr0 := hround 0 (by decide)
  have hr1 := hround 1 (by decide)
  have hr2 := hround 2 (by decide)
  have hr3 := hround 3 (by decide)
  have hr4 := hround 4 (by decide)
  have hr5 := hround 5 (by decide)
  have hchain01 := cpsTripleWithin_seq_same_cr hr0 hr1
  have hchain02 := cpsTripleWithin_seq_same_cr hchain01 hr2
  have hchain03 := cpsTripleWithin_seq_same_cr hchain02 hr3
  have hchain04 := cpsTripleWithin_seq_same_cr hchain03 hr4
  have hchain05 := cpsTripleWithin_seq_same_cr hchain04 hr5
  let rest6 : Assertion :=
    ((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qa + 6)))) **
      ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qb + 6)))) **
      ((.x1 : Reg) ↦ᵣ ret) ** regOwn .x5 ** regOwn .x31 **
      bytesRegion arenaBase (widxSwapMem arena qa qb 6)
  have hbeq6 := cpsBranchWithin_extend_code (cr' := CR)
    (h := beq_spec_gen_within .x6 .x0 (36 : BitVec 13)
      (0 : Word) (0 : Word) (base + 8))
    (hmono := fun a i h => widx_swap_mem_at base (base + 8) 2 _
      (by bv_omega) (by decide) (fun h => by simp [widxSwapProg] at h ⊢) a i h)
  rw [show signExtend13 (36 : BitVec 13) = (36 : Word) by decide,
    show (base + 8) + (36 : Word) = base + 44 by bv_omega,
    show (base + 8) + 4 = base + 12 by bv_omega] at hbeq6
  have hframe6 := cpsBranchWithin_frameR rest6 (by pcf) hbeq6
  have hlast0 := cpsBranchWithin_takenPath hframe6
    (fun _ hq => by
      obtain ⟨h1, _, _, _, hleft, _⟩ := hq
      obtain ⟨h6, h0pure, _, _, hx6, hx0pure⟩ := hleft
      have hneq0 := ((sepConj_pure_right
        (P := ((.x0 : Reg) ↦ᵣ (0 : Word)))
        (Q := (0 : Word) ≠ 0) h0pure).1 hx0pure).2
      exact hneq0 rfl)
  have hlast := cpsTripleWithin_weaken
    (P' := widxSwapInv arenaBase arena qa qb ret 6)
    (Q' := widxSwapInv arenaBase arena qa qb ret 6)
    (fun _ hp => by
      dsimp [widxSwapInv, rest6] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      dsimp [widxSwapInv, rest6] at hq ⊢
      have hq' := sepConj_mono_left (sepConj_strip_pure_end2) _ hq
      xperm_hyp hq') hlast0
  have hloop := cpsTripleWithin_seq_same_cr hchain05 hlast
  let retRest : Assertion :=
    ((.x10 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qa + 6)))) **
      ((.x11 : Reg) ↦ᵣ (arenaBase + BitVec.ofNat 64 (8 * (qb + 6)))) **
      ((.x6 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x31 **
      bytesRegion arenaBase (widxSwapMem arena qa qb 6)
  have hret0 := cpsTripleWithin_extend_code
    (hmono := fun a i h => widx_swap_mem_at base (base + 44) 11 _
      (by bv_omega) (by decide) (fun h => by simp [widxSwapProg] at h ⊢) a i h)
    (jalr_x0_spec_gen_within .x1 ret (0 : BitVec 12) (base + 44))
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) by decide] at hret0
  change cpsTripleWithin 1 (base + 44) ((ret + (0 : Word)) &&& ~~~(1 : Word)) CR
      ((.x1 : Reg) ↦ᵣ ret) ((.x1 : Reg) ↦ᵣ ret) at hret0
  have hret1 : cpsTripleWithin 1 (base + 44) ret CR
      ((.x1 : Reg) ↦ᵣ ret) ((.x1 : Reg) ↦ᵣ ret) := by
    have hretAddr : (ret + (0 : Word)) &&& ~~~(1 : Word) = ret := by
      calc
        (ret + (0 : Word)) &&& ~~~(1 : Word) = ret &&& ~~~(1 : Word) := by
          congr 1
          exact BitVec.add_zero ret
        _ = ret := halignRet
    rw [hretAddr] at hret0
    exact hret0
  have hretF := cpsTripleWithin_frameR retRest (by pcf) hret1
  have hret := cpsTripleWithin_weaken
    (P' := widxSwapInv arenaBase arena qa qb ret 6)
    (Q' := widxSwapPost arenaBase arena qa qb ret)
    (fun _ hp => by
      dsimp [widxSwapInv, retRest] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      dsimp [widxSwapPost, retRest] at hq ⊢
      xperm_hyp hq) hretF
  have htail := cpsTripleWithin_seq_same_cr hloop hret
  have hinit' := cpsTripleWithin_weaken
    (P' := widxSwapInv arenaBase arena qa qb ret 0)
    (Q' := widxSwapInv arenaBase arena qa qb ret 0)
    (fun _ hp => by
      dsimp [widxSwapInv, p0, rest0, restNoX6] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      dsimp [widxSwapInv, rest0, restNoX6] at hq ⊢
      xperm_hyp hq) hinit
  have hmain := cpsTripleWithin_seq_same_cr hinit' htail
  simpa [CR] using hmain

end EvmAsm.Codegen.Proofs
