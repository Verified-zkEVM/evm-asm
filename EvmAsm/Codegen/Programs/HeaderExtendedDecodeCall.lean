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
import EvmAsm.Rv64.Tactics.XPermChunked

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

set_option maxRecDepth 8000 in
/-- The reusable `rlp_walk_next` invocation block ([j]-[j+2], `S → S+12`): the
    two argument `MV`s (`a0 ← s3` cursor at `S`, `a1 ← s1` endPtr at `S+4`) then
    the wrapped `jal rlp_walk_next` (`hcall`, the `hedCall` output at `S+8`).
    The read-only saved registers `s3 = x19` (cursor) and `s1 = x9` (endPtr) are
    framed unchanged, so the block's post is the callee post `Q` (the six-way
    `rlp_walk_next` status disjunction) with `x19`/`x9` preserved.  The
    subsequent `MV x19, x10` cursor-save and the `BNE x11, x0` status dispatch
    are handled by the caller. -/
theorem hedWalkCall {n : Nat} {Prest Q : Assertion}
    (S cursor endPtr v10 v11 raOld : Word) (hPrest : Prest.pcFree)
    (hMV0 : ∀ a i, CodeReq.singleton S (.MV .x10 .x19) a = some i → fullCode a = some i)
    (hMV1 : ∀ a i, CodeReq.singleton (S + 4) (.MV .x11 .x9) a = some i → fullCode a = some i)
    (hcall : cpsTripleWithin n (S + 8) (S + 12) fullCode
      (((.x1 : Reg) ↦ᵣ raOld) **
        (((.x10 : Reg) ↦ᵣ cursor) ** ((.x11 : Reg) ↦ᵣ endPtr) ** Prest)) Q) :
    cpsTripleWithin (2 + n) S (S + 12) fullCode
      (((.x19 : Reg) ↦ᵣ cursor) ** ((.x9 : Reg) ↦ᵣ endPtr) **
        ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
        ((.x1 : Reg) ↦ᵣ raOld) ** Prest)
      (((.x19 : Reg) ↦ᵣ cursor) ** ((.x9 : Reg) ↦ᵣ endPtr) ** Q) := by
  -- [j] MV x10, x19  (a0 ← s3 cursor)
  have hmv0 := mv_spec_gen_within .x10 .x19 cursor v10 S (by decide)
  have hmv0e := cpsTripleWithin_extend_code hMV0 hmv0
  have hmv0f := cpsTripleWithin_frameR
    (((.x9 : Reg) ↦ᵣ endPtr) ** ((.x11 : Reg) ↦ᵣ v11) **
     ((.x1 : Reg) ↦ᵣ raOld) ** Prest) (by pcFree; exact hPrest) hmv0e
  -- [j+1] MV x11, x9  (a1 ← s1 endPtr)
  have hmv1 := mv_spec_gen_within .x11 .x9 endPtr v11 (S + 4) (by decide)
  have hmv1e := cpsTripleWithin_extend_code hMV1 hmv1
  have hmv1f := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ cursor) ** ((.x10 : Reg) ↦ᵣ cursor) **
     ((.x1 : Reg) ↦ᵣ raOld) ** Prest) (by pcFree; exact hPrest) hmv1e
  -- [j+2] jal rlp_walk_next (wrapped call), framing the read-only s3/s1 on the
  -- left so the opaque `Prest` stays trailing (keeps `xperm` unblocked).
  have hcallf := cpsTripleWithin_frameL
    (((.x19 : Reg) ↦ᵣ cursor) ** ((.x9 : Reg) ↦ᵣ endPtr)) (by pcFree) hcall
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hmv0f hmv1f
  rw [show (S + 4 + 4 : Word) = S + 8 from by bv_omega] at s1
  -- explicit-typed permutation between the two-MV post and the (frameL) call pre,
  -- so `xperm` sees concrete assertions (not postponed metavariables).
  have hperm : ∀ h,
      ((((.x9 : Reg) ↦ᵣ endPtr) ** (.x11 : Reg) ↦ᵣ endPtr) **
        ((.x19 : Reg) ↦ᵣ cursor) ** ((.x10 : Reg) ↦ᵣ cursor) **
        ((.x1 : Reg) ↦ᵣ raOld) ** Prest) h →
      ((((.x19 : Reg) ↦ᵣ cursor) ** (.x9 : Reg) ↦ᵣ endPtr) **
        ((.x1 : Reg) ↦ᵣ raOld) ** ((.x10 : Reg) ↦ᵣ cursor) **
        ((.x11 : Reg) ↦ᵣ endPtr) ** Prest) h :=
    fun h hp => by xperm_hyp hp
  have s2 := cpsTripleWithin_seq_perm_same_cr hperm s1 hcallf
  refine cpsTripleWithin_mono_nSteps (nSteps := 1 + 1 + n) (by omega) ?_
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) s2

#print axioms hedWalkCall

end EvmAsm.Codegen.HeaderExtendedDecodeSpec
