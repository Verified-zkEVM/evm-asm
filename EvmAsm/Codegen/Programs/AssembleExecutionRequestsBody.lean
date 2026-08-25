/-
  EvmAsm.Codegen.Programs.AssembleExecutionRequestsBody

  The body-copy section of `assemble_execution_requests` (#12206):
  instructions 14–66, i.e. five copy-loop segments back to back.

  Two segment lemmas, five uses:

  * `aer_mv_loop` — `MV x7,<ptr> ; MV x28,<len> ; <loop>`, the register-argument
    form used by the deposit / withdrawal / consolidation bodies
    (`m = 14, 23, 32`; nine instructions, `pc m → pc (m+9)`).
  * `aer_la_loop` — `la x7,<ptr global> ; LD x7 ; la x28,<len global> ; LD x28 ;
    <loop>`, the globals form used by the builder-deposit / builder-exit bodies
    (`m = 41, 54`; thirteen instructions, `pc m → pc (m+13)`).

  Both delegate the seven-instruction loop itself to
  `AssembleExecutionRequestsCopy.aer_copy_loop`, so the loop is proved once
  for all five sites and each segment lemma only adds its own setup.

  Net effect of a segment: `bytesRegion out ob` becomes
  `bytesRegion out (setBytes ob dstOff src)`, i.e. the body spliced in at the
  cursor, and the cursor advances by `src.length`.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.Programs.AssembleExecutionRequestsCopy

namespace EvmAsm.Codegen.AssembleExecutionRequestsBody

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.AssembleExecutionRequestsBase
open EvmAsm.Codegen.AssembleExecutionRequestsCopy

set_option maxRecDepth 8000

local macro "pcfB" : tactic =>
  `(tactic| repeat' first
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_emp
      | apply pcFree_sepConj)

private theorem word_add_zero_ofNat (p : Word) : p + BitVec.ofNat 64 0 = p :=
  BitVec.add_zero _

private theorem addr_off0 (p : Word) : p + signExtend12 (0 : BitVec 12) = p := by
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
  exact BitVec.add_zero _

/-! ## Segment A: register-argument setup + loop -/

/-- Working state of a register-argument copy segment. It is literally
    `copyInv`'s atom order with `F := (ptrReg ↦ᵣ srcPtr) ** (lenReg ↦ᵣ lenW)
    ** A`. -/
def SA (srcPtr out lenW : Word) (src : List (BitVec 8))
    (ptrReg lenReg : Reg) (A : Assertion)
    (v6 v7 v28 : Word) (ob : List (BitVec 8)) : Assertion :=
  (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion srcPtr src ** bytesRegion out ob ** regOwn .x29 **
  ((ptrReg ↦ᵣ srcPtr) ** (lenReg ↦ᵣ lenW) ** A)

/-- **A register-argument body copy.** `MV x7,ptrReg ; MV x28,lenReg ; loop`.
    Fuel `2 + 7·len + 1`, `pc m → pc (m+9)`. -/
theorem aer_mv_loop (m : Nat) (hc : CopyCode (m + 2))
    (ptrReg lenReg : Reg)
    (hmvP : ∀ a k, CodeReq.singleton (pc m) (.MV .x7 ptrReg) a = some k → aerCode a = some k)
    (hmvL : ∀ a k, CodeReq.singleton (pc (m + 1)) (.MV .x28 lenReg) a = some k →
      aerCode a = some k)
    (srcPtr out lenW v7 v28 : Word) (src ob : List (BitVec 8)) (dstOff : Nat)
    (hlenW : lenW = BitVec.ofNat 64 src.length)
    (halignS : srcPtr.toNat % 8 = 0) (halignD : out.toNat % 8 = 0)
    (hdstLen : dstOff + src.length ≤ ob.length)
    (hsrcOver : srcPtr.toNat + src.length < 2 ^ 64)
    (hdstOver : out.toNat + (dstOff + src.length) < 2 ^ 64)
    (hvalidS : ∀ i, i < src.length → isValidByteAccess (srcPtr + BitVec.ofNat 64 i) = true)
    (hvalidD : ∀ i, i < src.length →
      isValidByteAccess (out + BitVec.ofNat 64 (dstOff + i)) = true)
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin (2 + copyFuel src.length) (pc m) (pc (m + 9)) aerCode
      (SA srcPtr out lenW src ptrReg lenReg A
        (out + BitVec.ofNat 64 dstOff) v7 v28 ob)
      (SA srcPtr out lenW src ptrReg lenReg A
        (out + BitVec.ofNat 64 (dstOff + src.length))
        (srcPtr + BitVec.ofNat 64 src.length) (0 : Word)
        (setBytes ob dstOff src)) := by
  subst hlenW
  -- MV x7, ptrReg
  have h0core := mv_spec_gen_within .x7 ptrReg srcPtr v7 (pc m) (by decide)
  have h0c := cpsTripleWithin_extend_code hmvP h0core
  rw [pc_succ m] at h0c
  have h0 : cpsTripleWithin 1 (pc m) (pc (m + 1)) aerCode
      (SA srcPtr out (BitVec.ofNat 64 src.length) src ptrReg lenReg A
        (out + BitVec.ofNat 64 dstOff) v7 v28 ob)
      (SA srcPtr out (BitVec.ofNat 64 src.length) src ptrReg lenReg A
        (out + BitVec.ofNat 64 dstOff) srcPtr v28 ob) :=
    cpsTripleWithin_weaken
      (fun _ hp => by simp only [SA] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [SA] at hq ⊢; xperm_chunked hq)
      (cpsTripleWithin_frameR
        ((.x6 ↦ᵣ (out + BitVec.ofNat 64 dstOff)) ** (.x28 ↦ᵣ v28) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcPtr src ** bytesRegion out ob **
         regOwn .x29 ** (lenReg ↦ᵣ (BitVec.ofNat 64 src.length)) ** A)
        (by pcfB; exact hA) h0c)
  -- MV x28, lenReg
  have h1core := mv_spec_gen_within .x28 lenReg (BitVec.ofNat 64 src.length) v28 (pc (m + 1)) (by decide)
  have h1c := cpsTripleWithin_extend_code hmvL h1core
  rw [pc_succ (m + 1)] at h1c
  have h1 : cpsTripleWithin 1 (pc (m + 1)) (pc (m + 2)) aerCode
      (SA srcPtr out (BitVec.ofNat 64 src.length) src ptrReg lenReg A
        (out + BitVec.ofNat 64 dstOff) srcPtr v28 ob)
      (SA srcPtr out (BitVec.ofNat 64 src.length) src ptrReg lenReg A
        (out + BitVec.ofNat 64 dstOff) srcPtr (BitVec.ofNat 64 src.length) ob) :=
    cpsTripleWithin_weaken
      (fun _ hp => by simp only [SA] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [SA] at hq ⊢; xperm_chunked hq)
      (cpsTripleWithin_frameR
        ((.x6 ↦ᵣ (out + BitVec.ofNat 64 dstOff)) ** (.x7 ↦ᵣ srcPtr) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcPtr src ** bytesRegion out ob **
         regOwn .x29 ** (ptrReg ↦ᵣ srcPtr) ** A)
        (by pcfB; exact hA) h1c)
  -- the loop
  have hloop := aer_copy_loop (m + 2) hc srcPtr out src ob dstOff src.length 0
    (by omega) hdstLen halignS halignD hsrcOver hdstOver hvalidS hvalidD
    ((ptrReg ↦ᵣ srcPtr) ** (lenReg ↦ᵣ (BitVec.ofNat 64 src.length)) ** A)
    (by pcfB; exact hA)
  have h2 : cpsTripleWithin (copyFuel src.length) (pc (m + 2)) (pc (m + 9)) aerCode
      (SA srcPtr out (BitVec.ofNat 64 src.length) src ptrReg lenReg A
        (out + BitVec.ofNat 64 dstOff) srcPtr (BitVec.ofNat 64 src.length) ob)
      (SA srcPtr out (BitVec.ofNat 64 src.length) src ptrReg lenReg A
        (out + BitVec.ofNat 64 (dstOff + src.length))
        (srcPtr + BitVec.ofNat 64 src.length) (0 : Word)
        (setBytes ob dstOff src)) := by
    have hpc : m + 2 + 7 = m + 9 := by omega
    rw [hpc] at hloop
    refine cpsTripleWithin_weaken ?_ ?_ hloop
    · intro h hp
      simp only [SA] at hp
      simp only [copyInv, Nat.add_zero, word_add_zero_ofNat]
      exact hp
    · intro h hq
      simp only [copyDone, Nat.zero_add, copyDst_eq_setBytes] at hq
      simp only [SA]
      exact hq
  have c := cpsTripleWithin_seq_same_cr (cpsTripleWithin_seq_same_cr h0 h1) h2
  exact c

/-! ## Segment B: globals setup + loop -/

/-- Working state of a globals-driven copy segment: as `SA`, but the source
    pointer and length come from two dword cells rather than registers. -/
def SLa (srcPtr out lenW ptrA lenA : Word) (src : List (BitVec 8))
    (A : Assertion) (v6 v7 v28 : Word) (ob : List (BitVec 8)) : Assertion :=
  (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion srcPtr src ** bytesRegion out ob ** regOwn .x29 **
  ((ptrA ↦ₘ srcPtr) ** (lenA ↦ₘ lenW) ** A)

/-- **A globals-driven body copy.** `la x7,ptrA ; LD x7 ; la x28,lenA ;
    LD x28 ; loop`. Fuel `6 + 7·len + 1`, `pc m → pc (m+13)`. -/
theorem aer_la_loop (m : Nat) (hc : CopyCode (m + 6))
    (ptrA lenA : Word)
    (hrangeP : laInRange (pc m) ptrA) (hrangeL : laInRange (pc (m + 3)) lenA)
    (hlaP1 : ∀ a k, CodeReq.singleton (pc m) (.AUIPC .x7 (Rv64.laHi (pc m) ptrA)) a = some k →
      aerCode a = some k)
    (hlaP2 : ∀ a k, CodeReq.singleton (pc m + 4)
      (.ADDI .x7 .x7 (Rv64.laLo (pc m) ptrA)) a = some k → aerCode a = some k)
    (hldP : ∀ a k, CodeReq.singleton (pc (m + 2)) (.LD .x7 .x7 (0 : BitVec 12)) a = some k →
      aerCode a = some k)
    (hlaL1 : ∀ a k, CodeReq.singleton (pc (m + 3))
      (.AUIPC .x28 (Rv64.laHi (pc (m + 3)) lenA)) a = some k → aerCode a = some k)
    (hlaL2 : ∀ a k, CodeReq.singleton (pc (m + 3) + 4)
      (.ADDI .x28 .x28 (Rv64.laLo (pc (m + 3)) lenA)) a = some k → aerCode a = some k)
    (hldL : ∀ a k, CodeReq.singleton (pc (m + 5)) (.LD .x28 .x28 (0 : BitVec 12)) a = some k →
      aerCode a = some k)
    (srcPtr out lenW v7 v28 : Word) (src ob : List (BitVec 8)) (dstOff : Nat)
    (hlenW : lenW = BitVec.ofNat 64 src.length)
    (halignS : srcPtr.toNat % 8 = 0) (halignD : out.toNat % 8 = 0)
    (hdstLen : dstOff + src.length ≤ ob.length)
    (hsrcOver : srcPtr.toNat + src.length < 2 ^ 64)
    (hdstOver : out.toNat + (dstOff + src.length) < 2 ^ 64)
    (hvalidS : ∀ i, i < src.length → isValidByteAccess (srcPtr + BitVec.ofNat 64 i) = true)
    (hvalidD : ∀ i, i < src.length →
      isValidByteAccess (out + BitVec.ofNat 64 (dstOff + i)) = true)
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin (6 + copyFuel src.length) (pc m) (pc (m + 13)) aerCode
      (SLa srcPtr out lenW ptrA lenA src A
        (out + BitVec.ofNat 64 dstOff) v7 v28 ob)
      (SLa srcPtr out lenW ptrA lenA src A
        (out + BitVec.ofNat 64 (dstOff + src.length))
        (srcPtr + BitVec.ofNat 64 src.length) (0 : Word)
        (setBytes ob dstOff src)) := by
  subst hlenW
  have hpc2 : (pc m : Word) + 8 = pc (m + 2) := by
    have := pc_add m 2; simpa using this
  have hpc5 : (pc (m + 3) : Word) + 8 = pc (m + 5) := by
    have := pc_add (m + 3) 2
    simpa using this
  -- la x7, ptrA
  have hla1 := la_materialize_within (cr := aerCode) .x7 v7 (pc m) ptrA
    (by decide) hrangeP hlaP1 hlaP2
  rw [hpc2] at hla1
  have s0 : cpsTripleWithin 2 (pc m) (pc (m + 2)) aerCode
      (SLa srcPtr out (BitVec.ofNat 64 src.length) ptrA lenA src A (out + BitVec.ofNat 64 dstOff) v7 v28 ob)
      (SLa srcPtr out (BitVec.ofNat 64 src.length) ptrA lenA src A (out + BitVec.ofNat 64 dstOff) ptrA v28 ob) :=
    cpsTripleWithin_weaken
      (fun _ hp => by simp only [SLa] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [SLa] at hq ⊢; xperm_chunked hq)
      (cpsTripleWithin_frameR
        ((.x6 ↦ᵣ (out + BitVec.ofNat 64 dstOff)) ** (.x28 ↦ᵣ v28) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcPtr src ** bytesRegion out ob **
         regOwn .x29 ** (ptrA ↦ₘ srcPtr) ** (lenA ↦ₘ (BitVec.ofNat 64 src.length)) ** A)
        (by pcfB; exact hA) hla1)
  -- LD x7, 0(x7)
  have hld1core := ld_spec_gen_same_within .x7 ptrA srcPtr (0 : BitVec 12)
    (pc (m + 2)) (by decide)
  rw [addr_off0 ptrA] at hld1core
  have hld1c := cpsTripleWithin_extend_code hldP hld1core
  rw [pc_succ (m + 2)] at hld1c
  have s2 : cpsTripleWithin 1 (pc (m + 2)) (pc (m + 3)) aerCode
      (SLa srcPtr out (BitVec.ofNat 64 src.length) ptrA lenA src A (out + BitVec.ofNat 64 dstOff) ptrA v28 ob)
      (SLa srcPtr out (BitVec.ofNat 64 src.length) ptrA lenA src A (out + BitVec.ofNat 64 dstOff) srcPtr v28 ob) :=
    cpsTripleWithin_weaken
      (fun _ hp => by simp only [SLa] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [SLa] at hq ⊢; xperm_chunked hq)
      (cpsTripleWithin_frameR
        ((.x6 ↦ᵣ (out + BitVec.ofNat 64 dstOff)) ** (.x28 ↦ᵣ v28) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcPtr src ** bytesRegion out ob **
         regOwn .x29 ** (lenA ↦ₘ (BitVec.ofNat 64 src.length)) ** A)
        (by pcfB; exact hA) hld1c)
  -- la x28, lenA
  have hla2 := la_materialize_within (cr := aerCode) .x28 v28 (pc (m + 3)) lenA
    (by decide) hrangeL hlaL1 hlaL2
  rw [hpc5] at hla2
  have s3 : cpsTripleWithin 2 (pc (m + 3)) (pc (m + 5)) aerCode
      (SLa srcPtr out (BitVec.ofNat 64 src.length) ptrA lenA src A (out + BitVec.ofNat 64 dstOff) srcPtr v28 ob)
      (SLa srcPtr out (BitVec.ofNat 64 src.length) ptrA lenA src A (out + BitVec.ofNat 64 dstOff) srcPtr lenA ob) :=
    cpsTripleWithin_weaken
      (fun _ hp => by simp only [SLa] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [SLa] at hq ⊢; xperm_chunked hq)
      (cpsTripleWithin_frameR
        ((.x6 ↦ᵣ (out + BitVec.ofNat 64 dstOff)) ** (.x7 ↦ᵣ srcPtr) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcPtr src ** bytesRegion out ob **
         regOwn .x29 ** (ptrA ↦ₘ srcPtr) ** (lenA ↦ₘ (BitVec.ofNat 64 src.length)) ** A)
        (by pcfB; exact hA) hla2)
  -- LD x28, 0(x28)
  have hld2core := ld_spec_gen_same_within .x28 lenA (BitVec.ofNat 64 src.length) (0 : BitVec 12)
    (pc (m + 5)) (by decide)
  rw [addr_off0 lenA] at hld2core
  have hld2c := cpsTripleWithin_extend_code hldL hld2core
  rw [pc_succ (m + 5)] at hld2c
  have s5 : cpsTripleWithin 1 (pc (m + 5)) (pc (m + 6)) aerCode
      (SLa srcPtr out (BitVec.ofNat 64 src.length) ptrA lenA src A (out + BitVec.ofNat 64 dstOff) srcPtr lenA ob)
      (SLa srcPtr out (BitVec.ofNat 64 src.length) ptrA lenA src A (out + BitVec.ofNat 64 dstOff) srcPtr (BitVec.ofNat 64 src.length) ob) :=
    cpsTripleWithin_weaken
      (fun _ hp => by simp only [SLa] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [SLa] at hq ⊢; xperm_chunked hq)
      (cpsTripleWithin_frameR
        ((.x6 ↦ᵣ (out + BitVec.ofNat 64 dstOff)) ** (.x7 ↦ᵣ srcPtr) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcPtr src ** bytesRegion out ob **
         regOwn .x29 ** (ptrA ↦ₘ srcPtr) ** A)
        (by pcfB; exact hA) hld2c)
  -- the loop
  have hloop := aer_copy_loop (m + 6) hc srcPtr out src ob dstOff src.length 0
    (by omega) hdstLen halignS halignD hsrcOver hdstOver hvalidS hvalidD
    ((ptrA ↦ₘ srcPtr) ** (lenA ↦ₘ (BitVec.ofNat 64 src.length)) ** A)
    (by pcfB; exact hA)
  have s6 : cpsTripleWithin (copyFuel src.length) (pc (m + 6)) (pc (m + 13)) aerCode
      (SLa srcPtr out (BitVec.ofNat 64 src.length) ptrA lenA src A (out + BitVec.ofNat 64 dstOff) srcPtr (BitVec.ofNat 64 src.length) ob)
      (SLa srcPtr out (BitVec.ofNat 64 src.length) ptrA lenA src A
        (out + BitVec.ofNat 64 (dstOff + src.length))
        (srcPtr + BitVec.ofNat 64 src.length) (0 : Word)
        (setBytes ob dstOff src)) := by
    have hpc : m + 6 + 7 = m + 13 := by omega
    rw [hpc] at hloop
    refine cpsTripleWithin_weaken ?_ ?_ hloop
    · intro h hp
      simp only [SLa] at hp
      simp only [copyInv, Nat.add_zero, word_add_zero_ofNat]
      exact hp
    · intro h hq
      simp only [copyDone, Nat.zero_add, copyDst_eq_setBytes] at hq
      simp only [SLa]
      exact hq
  exact cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_seq_same_cr
      (cpsTripleWithin_seq_same_cr (cpsTripleWithin_seq_same_cr s0 s2) s3) s5) s6

end EvmAsm.Codegen.AssembleExecutionRequestsBody
