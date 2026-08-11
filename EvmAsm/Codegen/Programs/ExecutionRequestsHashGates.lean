/-
  EvmAsm.Codegen.Programs.ExecutionRequestsHashGates

  Compose the five fixed-list accept gates of `execution_requests_hash`
  validation (GH #11578 rescope):

    deposit @ B+160 → withdrawal @ B+188 → consolidation @ B+216 →
    builderDeposit @ B+244 → builderExit @ B+272 → hash-entry @ B+300

  Fuel 35 = 7×5. Hash half residual starts at B+300 (la erh_digests).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.Programs.ExecutionRequestsHashVal
import EvmAsm.Codegen.Programs.ExecutionRequestsHashGate
import EvmAsm.Codegen.Programs.ExecutionRequestsHashLiGate
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Evm64.EvmWordArith.MultiLimb

namespace EvmAsm.Codegen.ExecutionRequestsHashGates

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.ExecutionRequestsHashVal
open EvmAsm.Codegen.ExecutionRequestsHashGate
open EvmAsm.Codegen.ExecutionRequestsHashLiGate
open EvmAsm.Evm64.EvmWord

set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.execution_requests_hash

/-- Offsets after the five bgv_u32le reads (x19=dep … x23=bdep, x9=end). -/
structure ErhOffsets where
  dep : Word
  wdr : Word
  con : Word
  bdep : Word
  bexit : Word
  end_ : Word

/-- All five gates accept under Word-level fixedListOkW. -/
def erhGatesOkW (o : ErhOffsets) : Prop :=
  fixedListOkW (o.wdr - o.dep) (192 : Word) (8192 : Word) ∧
  fixedListOkW (o.con - o.wdr) (76 : Word) (16 : Word) ∧
  fixedListOkW (o.bdep - o.con) (116 : Word) (2 : Word) ∧
  fixedListOkW (o.bexit - o.bdep) (184 : Word) (64 : Word) ∧
  fixedListOkW (o.end_ - o.bexit) (68 : Word) (16 : Word)

/-- Offset registers held through the five gates. -/
def erhOffsetRegs (o : ErhOffsets) : Assertion :=
  (.x19 ↦ᵣ o.dep) ** (.x20 ↦ᵣ o.wdr) ** (.x21 ↦ᵣ o.con) **
    (.x22 ↦ᵣ o.bdep) ** (.x23 ↦ᵣ o.bexit) ** (.x9 ↦ᵣ o.end_)

/-- Scratch temps used by each gate (clobbered). -/
def erhGateTemps (v5 v6 v7 v28 : Word) : Assertion :=
  (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
    (.x0 ↦ᵣ (0 : Word))

/-- Five-gate accept chain: B+160 → B+300 under erhGatesOkW. Fuel 35. -/
theorem erh_five_gates_accept
    (o : ErhOffsets)
    (v5 v6 v7 v28 : Word)
    (hok : erhGatesOkW o)
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 35 (B + 160) (B + 300)
      (CodeReq.ofProg B executionRequestsHash_prog)
      (erhOffsetRegs o ** erhGateTemps v5 v6 v7 v28 ** A)
      (erhOffsetRegs o **
        erhGateTemps (o.end_ - o.bexit) (68 : Word)
          (rv64_divu (o.end_ - o.bexit) (68 : Word)) (16 : Word) ** A) := by
  obtain ⟨hd, hw, hc, hbd, hbe⟩ := hok
  let Amb : Assertion := erhOffsetRegs o ** A
  have hpcA : ∀ {P : Assertion}, P.pcFree → (erhOffsetRegs o ** P).pcFree := by
    intro P hP; simp only [erhOffsetRegs]
    repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact hP
  have hpcRest4 (w1 w2 w3 w4 : Word) :
      ((.x19 ↦ᵣ w1) ** (.x22 ↦ᵣ w2) ** (.x23 ↦ᵣ w3) ** (.x9 ↦ᵣ w4) ** A).pcFree := by
    repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact hA
  have hpcRest4' (w1 w2 w3 w4 : Word) :
      ((.x21 ↦ᵣ w1) ** (.x22 ↦ᵣ w2) ** (.x23 ↦ᵣ w3) ** (.x9 ↦ᵣ w4) ** A).pcFree := by
    repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact hA
  have hpcRest4'' (w1 w2 w3 w4 : Word) :
      ((.x19 ↦ᵣ w1) ** (.x20 ↦ᵣ w2) ** (.x23 ↦ᵣ w3) ** (.x9 ↦ᵣ w4) ** A).pcFree := by
    repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact hA
  have hpcRest4''' (w1 w2 w3 w4 : Word) :
      ((.x19 ↦ᵣ w1) ** (.x20 ↦ᵣ w2) ** (.x21 ↦ᵣ w3) ** (.x9 ↦ᵣ w4) ** A).pcFree := by
    repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact hA
  have hpcRest4'''' (w1 w2 w3 w4 : Word) :
      ((.x19 ↦ᵣ w1) ** (.x20 ↦ᵣ w2) ** (.x21 ↦ᵣ w3) ** (.x22 ↦ᵣ w4) ** A).pcFree := by
    repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact hA
  -- Deposit: hi=x20=wdr, lo=x19=dep
  have gd0 := deposit_gate_accept o.wdr o.dep v5 v6 v7 v28 hd
    ((.x21 ↦ᵣ o.con) ** (.x22 ↦ᵣ o.bdep) ** (.x23 ↦ᵣ o.bexit) **
      (.x9 ↦ᵣ o.end_) ** A) (hpcRest4' _ _ _ _)
  have gd :=
    cpsTripleWithin_weaken
      (P' := Amb ** erhGateTemps v5 v6 v7 v28)
      (Q' := Amb ** erhGateTemps (o.wdr - o.dep) (192 : Word)
        (rv64_divu (o.wdr - o.dep) (192 : Word)) (8192 : Word))
      (fun _ hp => by
        simp only [Amb, erhOffsetRegs, erhGateTemps] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [Amb, erhOffsetRegs, erhGateTemps] at hq ⊢; xperm_chunked hq) gd0
  -- Withdrawal: hi=x21=con, lo=x20=wdr
  have gw0 := withdrawal_gate_accept o.con o.wdr
    (o.wdr - o.dep) (192 : Word)
    (rv64_divu (o.wdr - o.dep) (192 : Word)) (8192 : Word) hw
    ((.x19 ↦ᵣ o.dep) ** (.x22 ↦ᵣ o.bdep) ** (.x23 ↦ᵣ o.bexit) **
      (.x9 ↦ᵣ o.end_) ** A) (hpcRest4 _ _ _ _)
  have gw :=
    cpsTripleWithin_weaken
      (P' := Amb ** erhGateTemps (o.wdr - o.dep) (192 : Word)
        (rv64_divu (o.wdr - o.dep) (192 : Word)) (8192 : Word))
      (Q' := Amb ** erhGateTemps (o.con - o.wdr) (76 : Word)
        (rv64_divu (o.con - o.wdr) (76 : Word)) (16 : Word))
      (fun _ hp => by
        simp only [Amb, erhOffsetRegs, erhGateTemps] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [Amb, erhOffsetRegs, erhGateTemps] at hq ⊢; xperm_chunked hq) gw0
  -- Consolidation: hi=x22=bdep, lo=x21=con
  have gc0 := consolidation_gate_accept o.bdep o.con
    (o.con - o.wdr) (76 : Word)
    (rv64_divu (o.con - o.wdr) (76 : Word)) (16 : Word) hc
    ((.x19 ↦ᵣ o.dep) ** (.x20 ↦ᵣ o.wdr) ** (.x23 ↦ᵣ o.bexit) **
      (.x9 ↦ᵣ o.end_) ** A) (hpcRest4'' _ _ _ _)
  have gc :=
    cpsTripleWithin_weaken
      (P' := Amb ** erhGateTemps (o.con - o.wdr) (76 : Word)
        (rv64_divu (o.con - o.wdr) (76 : Word)) (16 : Word))
      (Q' := Amb ** erhGateTemps (o.bdep - o.con) (116 : Word)
        (rv64_divu (o.bdep - o.con) (116 : Word)) (2 : Word))
      (fun _ hp => by
        simp only [Amb, erhOffsetRegs, erhGateTemps] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [Amb, erhOffsetRegs, erhGateTemps] at hq ⊢; xperm_chunked hq) gc0
  -- Builder deposit: hi=x23=bexit, lo=x22=bdep
  have gbd0 := builder_deposit_gate_accept o.bexit o.bdep
    (o.bdep - o.con) (116 : Word)
    (rv64_divu (o.bdep - o.con) (116 : Word)) (2 : Word) hbd
    ((.x19 ↦ᵣ o.dep) ** (.x20 ↦ᵣ o.wdr) ** (.x21 ↦ᵣ o.con) **
      (.x9 ↦ᵣ o.end_) ** A) (hpcRest4''' _ _ _ _)
  have gbd :=
    cpsTripleWithin_weaken
      (P' := Amb ** erhGateTemps (o.bdep - o.con) (116 : Word)
        (rv64_divu (o.bdep - o.con) (116 : Word)) (2 : Word))
      (Q' := Amb ** erhGateTemps (o.bexit - o.bdep) (184 : Word)
        (rv64_divu (o.bexit - o.bdep) (184 : Word)) (64 : Word))
      (fun _ hp => by
        simp only [Amb, erhOffsetRegs, erhGateTemps] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [Amb, erhOffsetRegs, erhGateTemps] at hq ⊢; xperm_chunked hq) gbd0
  -- Builder exit: hi=x9=end, lo=x23=bexit
  have gbe0 := builder_exit_gate_accept o.end_ o.bexit
    (o.bexit - o.bdep) (184 : Word)
    (rv64_divu (o.bexit - o.bdep) (184 : Word)) (64 : Word) hbe
    ((.x19 ↦ᵣ o.dep) ** (.x20 ↦ᵣ o.wdr) ** (.x21 ↦ᵣ o.con) **
      (.x22 ↦ᵣ o.bdep) ** A) (hpcRest4'''' _ _ _ _)
  have gbe :=
    cpsTripleWithin_weaken
      (P' := Amb ** erhGateTemps (o.bexit - o.bdep) (184 : Word)
        (rv64_divu (o.bexit - o.bdep) (184 : Word)) (64 : Word))
      (Q' := Amb ** erhGateTemps (o.end_ - o.bexit) (68 : Word)
        (rv64_divu (o.end_ - o.bexit) (68 : Word)) (16 : Word))
      (fun _ hp => by
        simp only [Amb, erhOffsetRegs, erhGateTemps] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [Amb, erhOffsetRegs, erhGateTemps] at hq ⊢; xperm_chunked hq) gbe0
  have c12 := cpsTripleWithin_seq_same_cr gd gw
  have c123 := cpsTripleWithin_seq_same_cr c12 gc
  have c1234 := cpsTripleWithin_seq_same_cr c123 gbd
  have c12345 := cpsTripleWithin_seq_same_cr c1234 gbe
  have hn' : ((((7 + 7) + 7) + 7) + 7) = 35 := rfl
  rw [hn'] at c12345
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [Amb, erhOffsetRegs, erhGateTemps] at hp ⊢; xperm_chunked hp)
    (fun _ hq => by
      simp only [Amb, erhOffsetRegs, erhGateTemps] at hq ⊢; xperm_chunked hq)
    c12345

end EvmAsm.Codegen.ExecutionRequestsHashGates
