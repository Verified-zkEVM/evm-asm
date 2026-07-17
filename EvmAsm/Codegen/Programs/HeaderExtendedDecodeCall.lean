/-
  Call-site adapters for the cross-`jal` calls of `headerExtendedDecode_prog`
  (`Programs/HeaderDecode.lean`, PR-K39).

  Each `jal ra, <callee>` slot is wrapped by `WP.cpsCallWithin` (JAL sets
  `ra = callerPC + 4`, runs the callee `_within` triple, returns to the aligned
  continuation) and then re-based from `(singleton JAL).union calleeCode` onto
  the decoder's `fullCode` closure via `union_split_mono` with the JAL's
  `fullCode`-membership witness and the callee-leaf subsumption
  (`walkInit_mono` / `walkNext_mono` / `u64_mono` / `u256_mono`).

  `hedCall` is the generic adapter; the `hedCall_*_slotN` theorems instantiate it
  at the concrete slots for the sequential-walk backbone.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.HeaderExtendedDecodeSpec
import EvmAsm.Rv64.SAsm.DualReadByteScan

namespace EvmAsm.Codegen.HeaderExtendedDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP

set_option maxRecDepth 8000 in
/-- Generic call-site adapter: given the caller `jal ra` at `callerPC`, its
    `fullCode` membership, the callee entry/code with `fullCode` subsumption,
    the JAL/callee disjointness and offset/alignment facts, wrap a callee
    `_within` triple into a `fullCode` triple that starts at the JAL and lands
    at the architectural return `callerPC + 4`. -/
theorem hedCall {n : Nat} {Prest Q : Assertion}
    (callerPC calleeEntry vRa : Word) (calleeCode : CodeReq) (offset : BitVec 21)
    (hoffset : callerPC + signExtend21 offset = calleeEntry)
    (halign : (callerPC + 4) &&& ~~~(1 : Word) = callerPC + 4)
    (hjalmem : ∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i → fullCode a = some i)
    (hcalleemem : ∀ a i, calleeCode a = some i → fullCode a = some i)
    (hdisj : (CodeReq.singleton callerPC (.JAL .x1 offset)).Disjoint calleeCode)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n calleeEntry ((callerPC + 4) &&& ~~~(1 : Word))
      calleeCode ((.x1 ↦ᵣ (callerPC + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) callerPC (callerPC + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  cpsTripleWithin_extend_code (CodeReq.union_split_mono hjalmem hcalleemem)
    (WP.cpsCallWithin offset hoffset halign hPrest hdisj hcallee)

set_option maxRecDepth 8000 in
/-- The JAL at slot 14 (`HB + 56`) targeting `rlp_walk_next` is in `fullCode`. -/
theorem hedJal_slot14_mem :
    ∀ a i, CodeReq.singleton (HB + 56)
        (.JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 56))) a = some i →
      fullCode a = some i := by
  intro a i h
  exact hed_mono a i
    (CodeReq.ofProg_mem_at HB (HB + 56) headerExtendedDecode_prog 14 _
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h)

set_option maxRecDepth 8000 in
/-- Concrete call-site adapter for the first `jal rlp_walk_next` (slot 14,
    `HB + 56`): validates the offset/alignment/disjointness `decide`s and pins
    the callee to `walkNext_mono`. -/
theorem hedCall_walkNext_slot14 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WNB ((HB + 56 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB) ((.x1 ↦ᵣ (HB + 56 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (HB + 56) (HB + 56 + 4) fullCode
      ((.x1 ↦ᵣ vRa) ** Prest) Q :=
  hedCall (HB + 56) WNB vRa (rlp_walk_next_code WNB)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 56))
    (by decide +kernel) (by decide) hedJal_slot14_mem walkNext_mono
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel)) hPrest hcallee

#print axioms hedCall
#print axioms hedCall_walkNext_slot14

end EvmAsm.Codegen.HeaderExtendedDecodeSpec
