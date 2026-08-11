/-
  EvmAsm.Codegen.Programs.ExecutionRequestsHashValPrefix

  Compose offset-mono + five fixed-list gates for `execution_requests_hash`
  validation accept path (GH #11578 rescope):

    B+132 mono (7) → B+160 five gates (35) → B+300 hash-entry

  Fuel 42 = 7+35. Pre-gate bgv_u32le reads and prologue residual; hash half residual.
  Fail join @ B+480 residual (erh_fail_join).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.Programs.ExecutionRequestsHashGates
import EvmAsm.Codegen.Programs.ExecutionRequestsHashMono
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Evm64.EvmWordArith.MultiLimb

namespace EvmAsm.Codegen.ExecutionRequestsHashValPrefix

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.ExecutionRequestsHashGates
open EvmAsm.Codegen.ExecutionRequestsHashMono
open EvmAsm.Evm64.EvmWord

set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.execution_requests_hash

/-- Mono + five gates accept: B+132 → B+300. Fuel 42 = 7+35. -/
theorem erh_mono_and_gates_accept
    (o : ErhOffsets)
    (v5 v6 v7 v28 : Word)
    (hmono : erhOffsetsMonoW o)
    (hgates : erhGatesOkW o)
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 42 (B + 132) (B + 300)
      (CodeReq.ofProg B executionRequestsHash_prog)
      (erhOffsetRegs o ** erhGateTemps v5 v6 v7 v28 ** A)
      (erhOffsetRegs o **
        erhGateTemps (o.end_ - o.bexit) (68 : Word)
          (rv64_divu (o.end_ - o.bexit) (68 : Word)) (16 : Word) ** A) := by
  let Rest : Assertion :=
    (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** A
  have hRest : Rest.pcFree := by
    simp only [Rest]
    repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact hA
  -- Mono: offsets ** x5 ** x0 ** Rest
  have hm0 := erh_mono_accept o v5 hmono Rest hRest
  have hm : cpsTripleWithin 7 (B + 132) (B + 160)
      (CodeReq.ofProg B executionRequestsHash_prog)
      (erhOffsetRegs o ** erhGateTemps v5 v6 v7 v28 ** A)
      (erhOffsetRegs o ** erhGateTemps (20 : Word) v6 v7 v28 ** A) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [erhGateTemps, Rest] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by
        simp only [erhGateTemps, Rest] at hq ⊢; xperm_chunked hq) hm0
  -- Five gates under mono post temps (x5=20)
  have hg0 := erh_five_gates_accept o (20 : Word) v6 v7 v28 hgates A hA
  have c := cpsTripleWithin_seq_same_cr hm hg0
  have hn' : (7 + 35) = 42 := rfl
  rw [hn'] at c
  exact c

end EvmAsm.Codegen.ExecutionRequestsHashValPrefix
