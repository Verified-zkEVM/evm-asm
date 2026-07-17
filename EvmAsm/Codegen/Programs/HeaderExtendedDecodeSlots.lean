/-
  The remaining per-slot cross-`jal` call adapters of `headerExtendedDecode_prog`
  (`Programs/HeaderDecode.lean`, PR-K39), completing the sequential-walk backbone.

  Each theorem mirrors `hedCall_walkNext_slot14` / `hedCall_u64_slot81`
  (`HeaderExtendedDecodeCall.lean`): the JAL-membership witness is inlined
  (`hed_mono ∘ CodeReq.ofProg_mem_at`) and the callee is pinned to its leaf
  subsumption (`walkInit_mono` / `walkNext_mono` / `u64_mono`).  Slot `k` sits at
  guest offset `4·k` from the decoder base `HB`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.HeaderExtendedDecodeCall

namespace EvmAsm.Codegen.HeaderExtendedDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 8 (`HB + 32`) targeting `GuestAddrs.rlp_walk_init`. -/
theorem hedCall_walkInit_slot8 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WIB ((HB + 32 + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code WIB) ((.x1 ↦ᵣ (HB + 32 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 32) (HB + 32 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 32) WIB vRa (rlp_walk_init_code WIB)
    (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.header_extended_decode + 32))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 32) headerExtendedDecode_prog 8 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    walkInit_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 30 (`HB + 120`) targeting `GuestAddrs.rlp_walk_next`. -/
theorem hedCall_walkNext_slot30 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WNB ((HB + 120 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB) ((.x1 ↦ᵣ (HB + 120 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 120) (HB + 120 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 120) WNB vRa (rlp_walk_next_code WNB)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 120))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 120) headerExtendedDecode_prog 30 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    walkNext_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 35 (`HB + 140`) targeting `GuestAddrs.rlp_walk_next`. -/
theorem hedCall_walkNext_slot35 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WNB ((HB + 140 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB) ((.x1 ↦ᵣ (HB + 140 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 140) (HB + 140 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 140) WNB vRa (rlp_walk_next_code WNB)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 140))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 140) headerExtendedDecode_prog 35 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    walkNext_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 40 (`HB + 160`) targeting `GuestAddrs.rlp_walk_next`. -/
theorem hedCall_walkNext_slot40 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WNB ((HB + 160 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB) ((.x1 ↦ᵣ (HB + 160 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 160) (HB + 160 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 160) WNB vRa (rlp_walk_next_code WNB)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 160))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 160) headerExtendedDecode_prog 40 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    walkNext_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 56 (`HB + 224`) targeting `GuestAddrs.rlp_walk_next`. -/
theorem hedCall_walkNext_slot56 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WNB ((HB + 224 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB) ((.x1 ↦ᵣ (HB + 224 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 224) (HB + 224 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 224) WNB vRa (rlp_walk_next_code WNB)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 224))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 224) headerExtendedDecode_prog 56 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    walkNext_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 61 (`HB + 244`) targeting `GuestAddrs.rlp_walk_next`. -/
theorem hedCall_walkNext_slot61 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WNB ((HB + 244 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB) ((.x1 ↦ᵣ (HB + 244 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 244) (HB + 244 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 244) WNB vRa (rlp_walk_next_code WNB)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 244))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 244) headerExtendedDecode_prog 61 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    walkNext_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 66 (`HB + 264`) targeting `GuestAddrs.rlp_walk_next`. -/
theorem hedCall_walkNext_slot66 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WNB ((HB + 264 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB) ((.x1 ↦ᵣ (HB + 264 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 264) (HB + 264 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 264) WNB vRa (rlp_walk_next_code WNB)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 264))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 264) headerExtendedDecode_prog 66 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    walkNext_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 71 (`HB + 284`) targeting `GuestAddrs.rlp_walk_next`. -/
theorem hedCall_walkNext_slot71 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WNB ((HB + 284 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB) ((.x1 ↦ᵣ (HB + 284 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 284) (HB + 284 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 284) WNB vRa (rlp_walk_next_code WNB)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 284))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 284) headerExtendedDecode_prog 71 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    walkNext_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 76 (`HB + 304`) targeting `GuestAddrs.rlp_walk_next`. -/
theorem hedCall_walkNext_slot76 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WNB ((HB + 304 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB) ((.x1 ↦ᵣ (HB + 304 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 304) (HB + 304 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 304) WNB vRa (rlp_walk_next_code WNB)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 304))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 304) headerExtendedDecode_prog 76 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    walkNext_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 86 (`HB + 344`) targeting `GuestAddrs.rlp_walk_next`. -/
theorem hedCall_walkNext_slot86 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WNB ((HB + 344 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB) ((.x1 ↦ᵣ (HB + 344 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 344) (HB + 344 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 344) WNB vRa (rlp_walk_next_code WNB)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 344))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 344) headerExtendedDecode_prog 86 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    walkNext_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 96 (`HB + 384`) targeting `GuestAddrs.rlp_walk_next`. -/
theorem hedCall_walkNext_slot96 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WNB ((HB + 384 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB) ((.x1 ↦ᵣ (HB + 384 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 384) (HB + 384 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 384) WNB vRa (rlp_walk_next_code WNB)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 384))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 384) headerExtendedDecode_prog 96 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    walkNext_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 106 (`HB + 424`) targeting `GuestAddrs.rlp_walk_next`. -/
theorem hedCall_walkNext_slot106 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WNB ((HB + 424 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB) ((.x1 ↦ᵣ (HB + 424 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 424) (HB + 424 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 424) WNB vRa (rlp_walk_next_code WNB)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 424))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 424) headerExtendedDecode_prog 106 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    walkNext_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 116 (`HB + 464`) targeting `GuestAddrs.rlp_walk_next`. -/
theorem hedCall_walkNext_slot116 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WNB ((HB + 464 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB) ((.x1 ↦ᵣ (HB + 464 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 464) (HB + 464 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 464) WNB vRa (rlp_walk_next_code WNB)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 464))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 464) headerExtendedDecode_prog 116 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    walkNext_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 121 (`HB + 484`) targeting `GuestAddrs.rlp_walk_next`. -/
theorem hedCall_walkNext_slot121 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WNB ((HB + 484 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB) ((.x1 ↦ᵣ (HB + 484 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 484) (HB + 484 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 484) WNB vRa (rlp_walk_next_code WNB)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 484))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 484) headerExtendedDecode_prog 121 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    walkNext_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 126 (`HB + 504`) targeting `GuestAddrs.rlp_walk_next`. -/
theorem hedCall_walkNext_slot126 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WNB ((HB + 504 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB) ((.x1 ↦ᵣ (HB + 504 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 504) (HB + 504 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 504) WNB vRa (rlp_walk_next_code WNB)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 504))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 504) headerExtendedDecode_prog 126 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    walkNext_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 131 (`HB + 524`) targeting `GuestAddrs.rlp_walk_next`. -/
theorem hedCall_walkNext_slot131 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WNB ((HB + 524 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB) ((.x1 ↦ᵣ (HB + 524 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 524) (HB + 524 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 524) WNB vRa (rlp_walk_next_code WNB)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 524))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 524) headerExtendedDecode_prog 131 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    walkNext_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 141 (`HB + 564`) targeting `GuestAddrs.rlp_walk_next`. -/
theorem hedCall_walkNext_slot141 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WNB ((HB + 564 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB) ((.x1 ↦ᵣ (HB + 564 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 564) (HB + 564 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 564) WNB vRa (rlp_walk_next_code WNB)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 564))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 564) headerExtendedDecode_prog 141 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    walkNext_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 146 (`HB + 584`) targeting `GuestAddrs.rlp_walk_next`. -/
theorem hedCall_walkNext_slot146 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WNB ((HB + 584 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB) ((.x1 ↦ᵣ (HB + 584 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 584) (HB + 584 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 584) WNB vRa (rlp_walk_next_code WNB)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 584))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 584) headerExtendedDecode_prog 146 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    walkNext_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 156 (`HB + 624`) targeting `GuestAddrs.rlp_walk_next`. -/
theorem hedCall_walkNext_slot156 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WNB ((HB + 624 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB) ((.x1 ↦ᵣ (HB + 624 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 624) (HB + 624 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 624) WNB vRa (rlp_walk_next_code WNB)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 624))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 624) headerExtendedDecode_prog 156 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    walkNext_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 91 (`HB + 364`) targeting `GuestAddrs.rlp_content_to_u64`. -/
theorem hedCall_u64_slot91 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n CU64B ((HB + 364 + 4) &&& ~~~(1 : Word))
      (rlp_content_to_u64_code CU64B) ((.x1 ↦ᵣ (HB + 364 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 364) (HB + 364 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 364) CU64B vRa (rlp_content_to_u64_code CU64B)
    (jalOff GuestAddrs.rlp_content_to_u64 (GuestAddrs.header_extended_decode + 364))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 364) headerExtendedDecode_prog 91 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    u64_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 101 (`HB + 404`) targeting `GuestAddrs.rlp_content_to_u64`. -/
theorem hedCall_u64_slot101 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n CU64B ((HB + 404 + 4) &&& ~~~(1 : Word))
      (rlp_content_to_u64_code CU64B) ((.x1 ↦ᵣ (HB + 404 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 404) (HB + 404 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 404) CU64B vRa (rlp_content_to_u64_code CU64B)
    (jalOff GuestAddrs.rlp_content_to_u64 (GuestAddrs.header_extended_decode + 404))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 404) headerExtendedDecode_prog 101 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    u64_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 111 (`HB + 444`) targeting `GuestAddrs.rlp_content_to_u64`. -/
theorem hedCall_u64_slot111 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n CU64B ((HB + 444 + 4) &&& ~~~(1 : Word))
      (rlp_content_to_u64_code CU64B) ((.x1 ↦ᵣ (HB + 444 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 444) (HB + 444 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 444) CU64B vRa (rlp_content_to_u64_code CU64B)
    (jalOff GuestAddrs.rlp_content_to_u64 (GuestAddrs.header_extended_decode + 444))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 444) headerExtendedDecode_prog 111 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    u64_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 151 (`HB + 604`) targeting `GuestAddrs.rlp_content_to_u64`. -/
theorem hedCall_u64_slot151 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n CU64B ((HB + 604 + 4) &&& ~~~(1 : Word))
      (rlp_content_to_u64_code CU64B) ((.x1 ↦ᵣ (HB + 604 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 604) (HB + 604 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 604) CU64B vRa (rlp_content_to_u64_code CU64B)
    (jalOff GuestAddrs.rlp_content_to_u64 (GuestAddrs.header_extended_decode + 604))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 604) headerExtendedDecode_prog 151 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    u64_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

set_option maxRecDepth 8000 in
/-- Call-site adapter for the `jal` at slot 161 (`HB + 644`) targeting `GuestAddrs.rlp_content_to_u64`. -/
theorem hedCall_u64_slot161 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n CU64B ((HB + 644 + 4) &&& ~~~(1 : Word))
      (rlp_content_to_u64_code CU64B) ((.x1 ↦ᵣ (HB + 644 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 644) (HB + 644 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 644) CU64B vRa (rlp_content_to_u64_code CU64B)
    (jalOff GuestAddrs.rlp_content_to_u64 (GuestAddrs.header_extended_decode + 644))
    (by decide +kernel) (by decide)
    (fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 644) headerExtendedDecode_prog 161 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
    u64_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

#print axioms hedCall_walkInit_slot8
#print axioms hedCall_walkNext_slot30
#print axioms hedCall_u64_slot91

end EvmAsm.Codegen.HeaderExtendedDecodeSpec
