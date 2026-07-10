import EvmAsm.Codegen.Programs.BalStorageReadsExecLogSpec

namespace EvmAsm.Codegen.BalStorageReadsExecLogSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP EvmAsm.Rv64.WP

private abbrev B : Word := (GuestAddrs.bal_storage_reads_in_exec_log : Word)
private abbrev WI : Word := (GuestAddrs.rlp_walk_init : Word)
private abbrev WN : Word := (GuestAddrs.rlp_walk_next : Word)

/-- The routine's full code requirement: its own bytes plus the two verified
    walker callees at their linked entries. -/
def bsreCR : CodeReq :=
  (CodeReq.ofProg B bsreProg).union
    ((rlp_walk_init_code WI).union (rlp_walk_next_code WN))

/-- Call-site adapter for the `jal rlp_walk_init` at slot 15 (`B + 60`):
    given ANY triple the callee's verified spec concludes from `ra = B + 64`,
    the call runs it and returns to `B + 64`.  The callee post stays
    abstract — instantiate with `rlp_walk_init_spec_within` at use site. -/
theorem bsre_callSite15_walkInit {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WI ((B + 60 + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code WI) ((.x1 ↦ᵣ (B + 60 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 60) (B + 60 + 4) bsreCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := cpsCallWithin
    (nSteps := n) (callerPC := B + 60) (calleeEntry := WI) (vOld := vRa)
    (calleeCode := rlp_walk_init_code WI) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_storage_reads_in_exec_log + 60))
    (by decide) (by decide) hPrest
    (by crDisjoint)
    hcallee
  refine cpsTripleWithin_extend_code (fun a i h => ?_) hcall
  rcases CodeReq.union_cases h with hl | hr
  · exact CodeReq.union_left _ (CodeReq.ofProg_mem_at B (B + 60) bsreProg 15 _
      (by decide) (by decide +kernel) (by decide +kernel) hbound a i hl)
  · exact CodeReq.union_right _ (CodeReq.union_left _ hr)

end EvmAsm.Codegen.BalStorageReadsExecLogSpec
