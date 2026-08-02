/-
  EvmAsm.Codegen.Programs.BalStorageReadsExecLogLink

  Continuation of `BalStorageReadsExecLogScan` (file-size guardrail split, the
  same reason that file was split out of `BalStorageReadsExecLogSpec`): the
  CONCRETE-LINKAGE half of `bal_storage_reads_in_exec_log` — the `bsreCR` code
  map, the walker-disjointness facts, the six per-call-site contracts and the
  two `la` pair specs.

  Nothing here is stride-dependent: these are address/code-membership facts
  about the routine's own instruction stream, so the GH #10644 stride
  generalisation does not reach them.  See `BalStorageReadsExecLogScan.lean` for
  the scan proof and `BalStorageReadsExecLogSpec.lean` for the routine's design
  notes and byte layout.
-/

import EvmAsm.Codegen.Programs.BalStorageReadsExecLogScan

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalStorageReadsExecLogSpec

/-! ## §6  Concrete linkage: code requirement, call-site adapters, `la` pairs

    Everything below is at the CONCRETE linked base
    (`balStorageReadsInExecLogPc`) — the walker callees live at
    fixed entries, so the `jal` offsets, code-range disjointness, and `la`
    resolutions are all kernel-decided. -/

/-- Concrete routine/callee entries. -/
abbrev B : Word := (balStorageReadsInExecLogPc : Word)
abbrev WI : Word := (GuestAddrs.rlp_walk_init : Word)
abbrev WN : Word := (GuestAddrs.rlp_walk_next : Word)

/-- The routine's full code requirement: its own bytes plus the two verified
    walker callees at their linked entries. -/
def bsreCR : CodeReq :=
  (CodeReq.ofProg B bsreProg).union
    ((rlp_walk_init_code WI).union (rlp_walk_next_code WN))

/-- The routine's bytes never shadow the walkers (separated code ranges). -/
theorem bsre_prog_disj_walkInit :
    (CodeReq.ofProg B bsreProg).Disjoint (rlp_walk_init_code WI) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bsre_prog_disj_walkNext :
    (CodeReq.ofProg B bsreProg).Disjoint (rlp_walk_next_code WN) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The two walkers occupy separated ranges. -/
theorem bsre_walkInit_disj_walkNext :
    (rlp_walk_init_code WI).Disjoint (rlp_walk_next_code WN) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Call-site adapter for the `jal rlp_walk_init` at slot 15 (`B + 60`). -/
theorem bsre_callSite15_walk_init {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WI ((B + 60 + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code WI) ((.x1 ↦ᵣ (B + 60 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 60) (B + 60 + 4) bsreCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 60) (calleeEntry := WI) (vOld := vRa)
    (calleeCode := rlp_walk_init_code WI) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_init (balStorageReadsInExecLogPc + 60))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 60) bsreProg 15 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bsre_prog_disj_walkInit
      (fun a i h => CodeReq.union_mono_left a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_next` at slot 18 (`B + 72`). -/
theorem bsre_callSite18_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 72 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 72 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 72) (B + 72 + 4) bsreCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 72) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (balStorageReadsInExecLogPc + 72))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 72) bsreProg 18 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bsre_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bsre_walkInit_disj_walkNext
        (fun _ _ hh => hh) a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_next` at slot 21 (`B + 84`). -/
theorem bsre_callSite21_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 84 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 84 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 84) (B + 84 + 4) bsreCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 84) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (balStorageReadsInExecLogPc + 84))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 84) bsreProg 21 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bsre_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bsre_walkInit_disj_walkNext
        (fun _ _ hh => hh) a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_next` at slot 24 (`B + 96`). -/
theorem bsre_callSite24_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 96 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 96 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 96) (B + 96 + 4) bsreCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 96) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (balStorageReadsInExecLogPc + 96))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 96) bsreProg 24 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bsre_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bsre_walkInit_disj_walkNext
        (fun _ _ hh => hh) a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_init` at slot 28 (`B + 112`). -/
theorem bsre_callSite28_walk_init {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WI ((B + 112 + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code WI) ((.x1 ↦ᵣ (B + 112 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 112) (B + 112 + 4) bsreCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 112) (calleeEntry := WI) (vOld := vRa)
    (calleeCode := rlp_walk_init_code WI) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_init (balStorageReadsInExecLogPc + 112))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 112) bsreProg 28 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bsre_prog_disj_walkInit
      (fun a i h => CodeReq.union_mono_left a i h) a i h


/-- Call-site adapter for the `jal rlp_walk_next` at slot 35 (`B + 140`). -/
theorem bsre_callSite35_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 140 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 140 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 140) (B + 140 + 4) bsreCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 140) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (balStorageReadsInExecLogPc + 140))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 140) bsreProg 35 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bsre_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bsre_walkInit_disj_walkNext
        (fun _ _ hh => hh) a i h) a i h


/-- The `la t0, bsr_krev` pair at slots 45–46: AUIPC+ADDI resolve
    to the linked scratch address. -/
theorem bsre_la_krev1_spec (vOld : Word) :
    cpsTripleWithin 2 (B + 180) (B + 188) bsreCR
      ((.x5 : Reg) ↦ᵣ vOld)
      ((.x5 : Reg) ↦ᵣ (bsrKrevPc : Word)) := by
  have hau := liftCode (cr' := bsreCR)
    (auipc_spec_gen_within .x5 vOld
      (laHi bsrKrevPc (balStorageReadsInExecLogPc + 180))
      (B + 180) (by decide))
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 180) bsreProg 45 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h))
  rw [show (B + 180) + 4 = B + 184 from by decide] at hau
  have haddi := liftCode (cr' := bsreCR)
    (addi_spec_gen_same_within .x5
      ((B + 180) + (((laHi bsrKrevPc
          (balStorageReadsInExecLogPc + 180)).zeroExtend 32
            <<< 12).signExtend 64))
      (laLo bsrKrevPc (balStorageReadsInExecLogPc + 180))
      (B + 184) (by decide))
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 184) bsreProg 46 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h))
  rw [show (B + 184) + 4 = B + 188 from by decide,
      show (B + 180) + (((laHi bsrKrevPc
          (balStorageReadsInExecLogPc + 180)).zeroExtend 32
            <<< 12).signExtend 64)
        + signExtend12 (laLo bsrKrevPc
            (balStorageReadsInExecLogPc + 180))
        = (bsrKrevPc : Word) from by decide] at haddi
  exact cpsTripleWithin_seq_same_cr hau haddi


/-- The `la x31, bsr_krev` pair at slots 66–67: AUIPC+ADDI resolve
    to the linked scratch address. -/
theorem bsre_la_krev2_spec (vOld : Word) :
    cpsTripleWithin 2 (B + 264) (B + 272) bsreCR
      ((.x31 : Reg) ↦ᵣ vOld)
      ((.x31 : Reg) ↦ᵣ (bsrKrevPc : Word)) := by
  have hau := liftCode (cr' := bsreCR)
    (auipc_spec_gen_within .x31 vOld
      (laHi bsrKrevPc (balStorageReadsInExecLogPc + 264))
      (B + 264) (by decide))
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 264) bsreProg 66 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h))
  rw [show (B + 264) + 4 = B + 268 from by decide] at hau
  have haddi := liftCode (cr' := bsreCR)
    (addi_spec_gen_same_within .x31
      ((B + 264) + (((laHi bsrKrevPc
          (balStorageReadsInExecLogPc + 264)).zeroExtend 32
            <<< 12).signExtend 64))
      (laLo bsrKrevPc (balStorageReadsInExecLogPc + 264))
      (B + 268) (by decide))
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 268) bsreProg 67 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h))
  rw [show (B + 268) + 4 = B + 272 from by decide,
      show (B + 264) + (((laHi bsrKrevPc
          (balStorageReadsInExecLogPc + 264)).zeroExtend 32
            <<< 12).signExtend 64)
        + signExtend12 (laLo bsrKrevPc
            (balStorageReadsInExecLogPc + 264))
        = (bsrKrevPc : Word) from by decide] at haddi
  exact cpsTripleWithin_seq_same_cr hau haddi



end BalStorageReadsExecLogSpec

end EvmAsm.Codegen
