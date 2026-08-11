/-
  ExecutionRequestsHashFiveReads — compose five bgv offset reads B+72 → B+132.

  Fuel 75 = 15×5. Post: offsets in x19..x23, endW in x9, x5/x6 owned.
  Parent: #11578 rescope.
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.Programs.ExecutionRequestsHashReads
import EvmAsm.Codegen.Programs.ExecutionRequestsHashGates
import EvmAsm.Codegen.Programs.ExecutionRequestsHashBgv
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.ExecutionRequestsHashFiveReads

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.SgLoadU32leSAsm (leU32)
open EvmAsm.Codegen.ExecutionRequestsHashReads
open EvmAsm.Codegen.ExecutionRequestsHashGates
open EvmAsm.Codegen.ExecutionRequestsHashBgv

set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.execution_requests_hash

/-- Shared tail: zero + bytes + end-reg + free ambient. -/
def fiveReadTail (listBase endW : Word) (bs : List (BitVec 8))
    (A : Assertion) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** (.x9 ↦ᵣ endW) ** A

/-- Core regs excluding scratch x5/x6. -/
def fiveReadCore (ra a0 d19 d20 d21 d22 d23 listBase : Word) : Assertion :=
  (.x1 ↦ᵣ ra) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ a0) **
    (.x19 ↦ᵣ d19) ** (.x20 ↦ᵣ d20) ** (.x21 ↦ᵣ d21) **
    (.x22 ↦ᵣ d22) ** (.x23 ↦ᵣ d23)

/-- Owns mid-chain peel: `P ** own5 ** own6 ** Q`. -/
private theorem of_forall2_mid
    {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q R : Assertion}
    (h : ∀ v5 v6, cpsTripleWithin n entry exit_ cr
      (P ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** Q) R) :
    cpsTripleWithin n entry exit_ cr (P ** regOwn .x5 ** regOwn .x6 ** Q) R := by
  have h' : ∀ v5 v6, cpsTripleWithin n entry exit_ cr
      ((P ** Q) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6)) R := fun v5 v6 =>
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => hq)
      (h v5 v6)
  have hOwn := cpsTripleWithin_of_forall_regIs_to_regOwn2 h'
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => hq)
    hOwn

/-- Five offset reads: B+72 → B+132. Fuel 75.
    Post offsets match `erhOffsetsFromBytes bs endW` (x19..x23 + x9). -/
theorem erh_five_reads
    (listBase endW : Word) (bs : List (BitVec 8))
    (vOld v5 v6 v10 v19 v20 v21 v22 v23 : Word)
    (A : Assertion) (hA : A.pcFree)
    (h_align : listBase.toNat % 8 = 0)
    (h_fit : 20 ≤ bs.length)
    (h_over : listBase.toNat + 19 < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 75 (B + 72) (B + 132) fullCode
      (fiveReadCore vOld v10 v19 v20 v21 v22 v23 listBase **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** fiveReadTail listBase endW bs A)
      (fiveReadCore (B + 128) (leU32 (bs.drop 16) 0)
        (leU32 (bs.drop 0) 0) (leU32 (bs.drop 4) 0) (leU32 (bs.drop 8) 0)
        (leU32 (bs.drop 12) 0) (leU32 (bs.drop 16) 0) listBase **
        regOwn .x5 ** regOwn .x6 ** fiveReadTail listBase endW bs A) := by
  have hfit0 : 0 + 4 ≤ bs.length := by omega
  have hfit4 : 4 + 4 ≤ bs.length := by omega
  have hfit8 : 8 + 4 ≤ bs.length := by omega
  have hfit12 : 12 + 4 ≤ bs.length := by omega
  have hfit16 : 16 + 4 ≤ bs.length := by omega
  have hover0 : listBase.toNat + (0 + 3) < 2 ^ 64 := by omega
  have hover4 : listBase.toNat + (4 + 3) < 2 ^ 64 := by omega
  have hover8 : listBase.toNat + (8 + 3) < 2 ^ 64 := by omega
  have hover12 : listBase.toNat + (12 + 3) < 2 ^ 64 := by omega
  have hover16 : listBase.toNat + (16 + 3) < 2 ^ 64 := by omega
  -- Step 1 deposit
  have h1F : ((.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
      (.x23 ↦ᵣ v23) ** (.x9 ↦ᵣ endW) ** A).pcFree := by
    repeat (first | apply pcFree_sepConj | exact pcFree_regIs | exact hA)
  have h1raw := erh_read_dep listBase bs vOld v5 v6 v10 v19
    ((.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
      (.x23 ↦ᵣ v23) ** (.x9 ↦ᵣ endW) ** A) h1F
    h_align hfit0 hover0 h_valid
  have h1 : cpsTripleWithin 15 (B + 72) (B + 84) fullCode
      (fiveReadCore vOld v10 v19 v20 v21 v22 v23 listBase **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** fiveReadTail listBase endW bs A)
      (fiveReadCore (B + 80) (leU32 (bs.drop 0) 0)
        (leU32 (bs.drop 0) 0) v20 v21 v22 v23 listBase **
        regOwn .x5 ** regOwn .x6 ** fiveReadTail listBase endW bs A) :=
    cpsTripleWithin_weaken
      (fun _ hp => by simp only [fiveReadCore, fiveReadTail] at hp; xperm_chunked hp)
      (fun _ hq => by simp only [fiveReadCore, fiveReadTail]; xperm_chunked hq)
      h1raw
  -- Step 2 wdr
  have h2F : ((.x19 ↦ᵣ leU32 (bs.drop 0) 0) ** (.x21 ↦ᵣ v21) **
      (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23) ** (.x9 ↦ᵣ endW) ** A).pcFree := by
    repeat (first | apply pcFree_sepConj | exact pcFree_regIs | exact hA)
  have h2c : ∀ v5' v6', cpsTripleWithin 15 (B + 84) (B + 96) fullCode
      (fiveReadCore (B + 80) (leU32 (bs.drop 0) 0)
        (leU32 (bs.drop 0) 0) v20 v21 v22 v23 listBase **
        (.x5 ↦ᵣ v5') ** (.x6 ↦ᵣ v6') ** fiveReadTail listBase endW bs A)
      (fiveReadCore (B + 92) (leU32 (bs.drop 4) 0)
        (leU32 (bs.drop 0) 0) (leU32 (bs.drop 4) 0) v21 v22 v23 listBase **
        regOwn .x5 ** regOwn .x6 ** fiveReadTail listBase endW bs A) :=
    fun v5' v6' =>
      cpsTripleWithin_weaken
        (fun _ hp => by simp only [fiveReadCore, fiveReadTail] at hp; xperm_chunked hp)
        (fun _ hq => by simp only [fiveReadCore, fiveReadTail]; xperm_chunked hq)
        (erh_read_wdr listBase bs (B + 80) v5' v6'
          (leU32 (bs.drop 0) 0) v20
          ((.x19 ↦ᵣ leU32 (bs.drop 0) 0) ** (.x21 ↦ᵣ v21) **
            (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23) ** (.x9 ↦ᵣ endW) ** A) h2F
          h_align hfit4 hover4 h_valid)
  have h2 := of_forall2_mid h2c
  -- Step 3 con
  have h3F : ((.x19 ↦ᵣ leU32 (bs.drop 0) 0) **
      (.x20 ↦ᵣ leU32 (bs.drop 4) 0) ** (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23) **
      (.x9 ↦ᵣ endW) ** A).pcFree := by
    repeat (first | apply pcFree_sepConj | exact pcFree_regIs | exact hA)
  have h3c : ∀ v5' v6', cpsTripleWithin 15 (B + 96) (B + 108) fullCode
      (fiveReadCore (B + 92) (leU32 (bs.drop 4) 0)
        (leU32 (bs.drop 0) 0) (leU32 (bs.drop 4) 0) v21 v22 v23 listBase **
        (.x5 ↦ᵣ v5') ** (.x6 ↦ᵣ v6') ** fiveReadTail listBase endW bs A)
      (fiveReadCore (B + 104) (leU32 (bs.drop 8) 0)
        (leU32 (bs.drop 0) 0) (leU32 (bs.drop 4) 0) (leU32 (bs.drop 8) 0)
        v22 v23 listBase **
        regOwn .x5 ** regOwn .x6 ** fiveReadTail listBase endW bs A) :=
    fun v5' v6' =>
      cpsTripleWithin_weaken
        (fun _ hp => by simp only [fiveReadCore, fiveReadTail] at hp; xperm_chunked hp)
        (fun _ hq => by simp only [fiveReadCore, fiveReadTail]; xperm_chunked hq)
        (erh_read_con listBase bs (B + 92) v5' v6'
          (leU32 (bs.drop 4) 0) v21
          ((.x19 ↦ᵣ leU32 (bs.drop 0) 0) **
            (.x20 ↦ᵣ leU32 (bs.drop 4) 0) ** (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23) **
            (.x9 ↦ᵣ endW) ** A) h3F
          h_align hfit8 hover8 h_valid)
  have h3 := of_forall2_mid h3c
  -- Step 4 bdep
  have h4F : ((.x19 ↦ᵣ leU32 (bs.drop 0) 0) **
      (.x20 ↦ᵣ leU32 (bs.drop 4) 0) ** (.x21 ↦ᵣ leU32 (bs.drop 8) 0) **
      (.x23 ↦ᵣ v23) ** (.x9 ↦ᵣ endW) ** A).pcFree := by
    repeat (first | apply pcFree_sepConj | exact pcFree_regIs | exact hA)
  have h4c : ∀ v5' v6', cpsTripleWithin 15 (B + 108) (B + 120) fullCode
      (fiveReadCore (B + 104) (leU32 (bs.drop 8) 0)
        (leU32 (bs.drop 0) 0) (leU32 (bs.drop 4) 0) (leU32 (bs.drop 8) 0)
        v22 v23 listBase **
        (.x5 ↦ᵣ v5') ** (.x6 ↦ᵣ v6') ** fiveReadTail listBase endW bs A)
      (fiveReadCore (B + 116) (leU32 (bs.drop 12) 0)
        (leU32 (bs.drop 0) 0) (leU32 (bs.drop 4) 0) (leU32 (bs.drop 8) 0)
        (leU32 (bs.drop 12) 0) v23 listBase **
        regOwn .x5 ** regOwn .x6 ** fiveReadTail listBase endW bs A) :=
    fun v5' v6' =>
      cpsTripleWithin_weaken
        (fun _ hp => by simp only [fiveReadCore, fiveReadTail] at hp; xperm_chunked hp)
        (fun _ hq => by simp only [fiveReadCore, fiveReadTail]; xperm_chunked hq)
        (erh_read_bdep listBase bs (B + 104) v5' v6'
          (leU32 (bs.drop 8) 0) v22
          ((.x19 ↦ᵣ leU32 (bs.drop 0) 0) **
            (.x20 ↦ᵣ leU32 (bs.drop 4) 0) ** (.x21 ↦ᵣ leU32 (bs.drop 8) 0) **
            (.x23 ↦ᵣ v23) ** (.x9 ↦ᵣ endW) ** A) h4F
          h_align hfit12 hover12 h_valid)
  have h4 := of_forall2_mid h4c
  -- Step 5 bexit
  have h5F : ((.x19 ↦ᵣ leU32 (bs.drop 0) 0) **
      (.x20 ↦ᵣ leU32 (bs.drop 4) 0) ** (.x21 ↦ᵣ leU32 (bs.drop 8) 0) **
      (.x22 ↦ᵣ leU32 (bs.drop 12) 0) ** (.x9 ↦ᵣ endW) ** A).pcFree := by
    repeat (first | apply pcFree_sepConj | exact pcFree_regIs | exact hA)
  have h5c : ∀ v5' v6', cpsTripleWithin 15 (B + 120) (B + 132) fullCode
      (fiveReadCore (B + 116) (leU32 (bs.drop 12) 0)
        (leU32 (bs.drop 0) 0) (leU32 (bs.drop 4) 0) (leU32 (bs.drop 8) 0)
        (leU32 (bs.drop 12) 0) v23 listBase **
        (.x5 ↦ᵣ v5') ** (.x6 ↦ᵣ v6') ** fiveReadTail listBase endW bs A)
      (fiveReadCore (B + 128) (leU32 (bs.drop 16) 0)
        (leU32 (bs.drop 0) 0) (leU32 (bs.drop 4) 0) (leU32 (bs.drop 8) 0)
        (leU32 (bs.drop 12) 0) (leU32 (bs.drop 16) 0) listBase **
        regOwn .x5 ** regOwn .x6 ** fiveReadTail listBase endW bs A) :=
    fun v5' v6' =>
      cpsTripleWithin_weaken
        (fun _ hp => by simp only [fiveReadCore, fiveReadTail] at hp; xperm_chunked hp)
        (fun _ hq => by simp only [fiveReadCore, fiveReadTail]; xperm_chunked hq)
        (erh_read_bexit listBase bs (B + 116) v5' v6'
          (leU32 (bs.drop 12) 0) v23
          ((.x19 ↦ᵣ leU32 (bs.drop 0) 0) **
            (.x20 ↦ᵣ leU32 (bs.drop 4) 0) ** (.x21 ↦ᵣ leU32 (bs.drop 8) 0) **
            (.x22 ↦ᵣ leU32 (bs.drop 12) 0) ** (.x9 ↦ᵣ endW) ** A) h5F
          h_align hfit16 hover16 h_valid)
  have h5 := of_forall2_mid h5c
  have c01 := cpsTripleWithin_seq_same_cr h1 h2
  have c02 := cpsTripleWithin_seq_same_cr c01 h3
  have c03 := cpsTripleWithin_seq_same_cr c02 h4
  exact cpsTripleWithin_seq_same_cr c03 h5

/-- Bridge five-read post into `erhOffsetRegs` for mono/gates. -/
theorem fiveReadCore_to_erhOffsetRegs
    (listBase endW : Word) (bs : List (BitVec 8))
    (ra a0 : Word) (A : Assertion) :
    ∀ s, (fiveReadCore ra a0
        (leU32 (bs.drop 0) 0) (leU32 (bs.drop 4) 0) (leU32 (bs.drop 8) 0)
        (leU32 (bs.drop 12) 0) (leU32 (bs.drop 16) 0) listBase **
      fiveReadTail listBase endW bs A) s →
    ((.x1 ↦ᵣ ra) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ a0) **
      erhOffsetRegs (erhOffsetsFromBytes bs endW) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** A) s := by
  intro s hs
  simp only [fiveReadCore, fiveReadTail, erhOffsetRegs, erhOffsetsFromBytes] at hs ⊢
  xperm_chunked hs

end EvmAsm.Codegen.ExecutionRequestsHashFiveReads
