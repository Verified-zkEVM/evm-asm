/-
  ExecutionRequestsHashBody — validation accept prefix to hash-entry.

  Compose (fullCode = erh ∪ bgv):
    setup MVs (3) @ B+52
    early len≥20 (2) @ B+64
    five bgv reads (75) @ B+72
    mono+gates (42) @ B+132
  → hash-entry B+300. Fuel 122.

  Domain: listBase%8=0, 20≤bs.length, endW len gate, mono+gates on
  decoded offsets. Hash half residual from B+300.
  Parent: #11578 rescope.
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.Programs.ExecutionRequestsHashBgv
import EvmAsm.Codegen.Programs.ExecutionRequestsHashEarly
import EvmAsm.Codegen.Programs.ExecutionRequestsHashFiveReads
import EvmAsm.Codegen.Programs.ExecutionRequestsHashReads
import EvmAsm.Codegen.Programs.ExecutionRequestsHashGates
import EvmAsm.Codegen.Programs.ExecutionRequestsHashValPrefix
import EvmAsm.Codegen.Programs.ExecutionRequestsHashMono
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Evm64.EvmWordArith.MultiLimb

namespace EvmAsm.Codegen.ExecutionRequestsHashBody

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.SgLoadU32leSAsm (leU32)
open EvmAsm.Codegen.ExecutionRequestsHashBgv
open EvmAsm.Codegen.ExecutionRequestsHashEarly
open EvmAsm.Codegen.ExecutionRequestsHashFiveReads
open EvmAsm.Codegen.ExecutionRequestsHashReads
open EvmAsm.Codegen.ExecutionRequestsHashGates
open EvmAsm.Codegen.ExecutionRequestsHashValPrefix
open EvmAsm.Codegen.ExecutionRequestsHashMono
open EvmAsm.Evm64.EvmWord

set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.execution_requests_hash

local macro "pcf" : tactic =>
  `(tactic| repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact bytesRegion_pcFree _ _
      | exact pcFree_emp
      | exact pcFree_pure)

private theorem lift_erh {n : Nat} {entry exit_ : Word} {P Q : Assertion}
    (h : cpsTripleWithin n entry exit_ (CodeReq.ofProg B executionRequestsHash_prog) P Q) :
    cpsTripleWithin n entry exit_ fullCode P Q :=
  cpsTripleWithin_extend_code
    (fun a i hi => by
      unfold fullCode
      exact CodeReq.union_mono_left a i hi) h

private theorem of_forall2_pre
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

/-- Five-read free ambient (no bytes — those sit in fiveReadTail). -/
private def readExtra (endW outW v7 v28 : Word) (A : Assertion) : Assertion :=
  (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) ** (.x18 ↦ᵣ outW) **
    (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** A

/-- Validation accept body: B+52 → B+300. Fuel 122 = 3+2+75+42. -/
theorem erh_validation_accept_body
    (listBase endW outW : Word) (bs : List (BitVec 8))
    (v8 v9 v18 v5 v6 v7 v19 v20 v21 v22 v23 v28 ra : Word)
    (A : Assertion) (hA : A.pcFree)
    (h_align : listBase.toNat % 8 = 0)
    (h_fit : 20 ≤ bs.length)
    (h_over : listBase.toNat + 19 < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_ge : ¬ BitVec.ult endW (20 : Word))
    (hmono : erhOffsetsMonoW (erhOffsetsFromBytes bs endW))
    (hgates : erhGatesOkW (erhOffsetsFromBytes bs endW)) :
    cpsTripleWithin 122 (B + 52) (B + 300) fullCode
      ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23) ** (.x28 ↦ᵣ v28) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** A)
      (let o := erhOffsetsFromBytes bs endW
       (.x1 ↦ᵣ (B + 128)) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ o.bexit) **
         (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) ** (.x18 ↦ᵣ outW) **
         erhOffsetRegs o **
         erhGateTemps (o.end_ - o.bexit) (68 : Word)
           (rv64_divu (o.end_ - o.bexit) (68 : Word)) (16 : Word) **
         bytesRegion listBase bs ** A) := by
  let Extra : Assertion := readExtra endW outW v7 v28 A
  have hExtra : Extra.pcFree := by
    change (readExtra endW outW v7 v28 A).pcFree
    simp only [readExtra]; pcf; exact hA
  -- Step 1: setup MVs
  have hs0F : ((.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
      (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23) ** (.x28 ↦ᵣ v28) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** A).pcFree := by
    pcf; exact hA
  have hs0 := erh_setup_mvs listBase endW outW v8 v9 v18
    ((.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
      (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23) ** (.x28 ↦ᵣ v28) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** A) hs0F
  have hs : cpsTripleWithin 3 (B + 52) (B + 64) fullCode
      ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23) ** (.x28 ↦ᵣ v28) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** A)
      ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
        (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endW) ** (.x18 ↦ᵣ outW) **
        (.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23) ** (.x28 ↦ᵣ v28) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** A) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hs0
  -- Step 2: early len
  have he0F : ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
      (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outW) **
      (.x1 ↦ᵣ ra) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
      (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23) ** (.x28 ↦ᵣ v28) **
      bytesRegion listBase bs ** A).pcFree := by
    pcf; exact hA
  have he0 := erh_early_len_accept endW v5 h_ge
    ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
      (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ outW) **
      (.x1 ↦ᵣ ra) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
      (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23) ** (.x28 ↦ᵣ v28) **
      bytesRegion listBase bs ** A) he0F
  have he : cpsTripleWithin 2 (B + 64) (B + 72) fullCode
      ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
        (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endW) ** (.x18 ↦ᵣ outW) **
        (.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23) ** (.x28 ↦ᵣ v28) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** A)
      ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
        (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endW) ** (.x18 ↦ᵣ outW) **
        (.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ (20 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23) ** (.x28 ↦ᵣ v28) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** A) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) he0
  -- Step 3: five reads (x10 still listBase after setup/early)
  have hr0 := erh_five_reads listBase endW bs ra (20 : Word) v6 listBase
    v19 v20 v21 v22 v23 Extra hExtra
    h_align h_fit h_over h_valid
  have hr : cpsTripleWithin 75 (B + 72) (B + 132) fullCode
      ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) **
        (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endW) ** (.x18 ↦ᵣ outW) **
        (.x1 ↦ᵣ ra) ** (.x5 ↦ᵣ (20 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23) ** (.x28 ↦ᵣ v28) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs ** A)
      (fiveReadCore (B + 128) (leU32 (bs.drop 16) 0)
        (leU32 (bs.drop 0) 0) (leU32 (bs.drop 4) 0) (leU32 (bs.drop 8) 0)
        (leU32 (bs.drop 12) 0) (leU32 (bs.drop 16) 0) listBase **
        regOwn .x5 ** regOwn .x6 **
        fiveReadTail listBase endW bs Extra) :=
    cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [fiveReadCore, fiveReadTail, Extra, readExtra] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        simp only [fiveReadCore, fiveReadTail, Extra, readExtra] at hq ⊢
        xperm_chunked hq) hr0
  -- Step 4: mono+gates under owns peel
  let o := erhOffsetsFromBytes bs endW
  have hmgF : ((.x1 ↦ᵣ (B + 128)) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ o.bexit) **
      (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) ** (.x18 ↦ᵣ outW) **
      bytesRegion listBase bs ** A).pcFree := by
    pcf; exact hA
  have hmgc : ∀ w5 w6, cpsTripleWithin 42 (B + 132) (B + 300) fullCode
      (fiveReadCore (B + 128) (leU32 (bs.drop 16) 0)
        (leU32 (bs.drop 0) 0) (leU32 (bs.drop 4) 0) (leU32 (bs.drop 8) 0)
        (leU32 (bs.drop 12) 0) (leU32 (bs.drop 16) 0) listBase **
        (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) **
        fiveReadTail listBase endW bs Extra)
      ((.x1 ↦ᵣ (B + 128)) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ o.bexit) **
        (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) ** (.x18 ↦ᵣ outW) **
        erhOffsetRegs o **
        erhGateTemps (o.end_ - o.bexit) (68 : Word)
          (rv64_divu (o.end_ - o.bexit) (68 : Word)) (16 : Word) **
        bytesRegion listBase bs ** A) := by
    intro w5 w6
    have hmg0 := lift_erh
      (erh_mono_and_gates_accept o w5 w6 v7 v28 hmono hgates
        ((.x1 ↦ᵣ (B + 128)) ** (.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ o.bexit) **
          (.x11 ↦ᵣ endW) ** (.x12 ↦ᵣ outW) ** (.x18 ↦ᵣ outW) **
          bytesRegion listBase bs ** A) hmgF)
    refine cpsTripleWithin_weaken ?_ ?_ hmg0
    · intro s hp
      simp only [fiveReadCore, fiveReadTail, Extra, readExtra,
        erhOffsetRegs, erhGateTemps, erhOffsetsFromBytes, o] at hp ⊢
      xperm_chunked hp
    · intro s hq
      simp only [erhOffsetRegs, erhGateTemps, o] at hq ⊢
      xperm_chunked hq
  have hmg := of_forall2_pre hmgc
  -- Compose 3+2+75+42
  have c01 := cpsTripleWithin_seq_same_cr hs he
  have c02 := cpsTripleWithin_seq_same_cr c01 hr
  have c03 := cpsTripleWithin_seq_same_cr c02 hmg
  have hn : (3 + 2 + 75 + 42) = 122 := rfl
  rw [hn] at c03
  exact c03

end EvmAsm.Codegen.ExecutionRequestsHashBody
