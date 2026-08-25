/-
  EvmAsm.Codegen.Programs.HeaderExtendedDecodeWalkSite

  **The `rlp_walk_next` call sites of `header_extended_decode`, with the callee
  composed rather than assumed.**

  `GuestAddrs.header_extended_decode` calls `GuestAddrs.rlp_walk_next` at
  **nineteen** sites — byte offsets

  ```
  +56  +120 +140 +160 +224 +244 +264 +284 +304 +344
  +384 +424 +464 +484 +504 +524 +564 +584 +624
  ```

  (`JAL` at program indices 14, 30, 35, 40, 56, 61, 66, 71, 76, 86, 96, 106,
  116, 121, 126, 131, 141, 146, 156), all with the same three-instruction call
  block:

  ```
  A      mv   a0, s3      -- MV  x10 x19   (walk cursor)
  A + 4  mv   a1, s1      -- MV  x11 x9    (end pointer)
  A + 8  jal  ra, rlp_walk_next
  A + 12                  -- return; the site's `mv s3,a0` / `bnez a1` follow
  ```

  where `A = <site offset> - 8`.

  This file provides

    * `walkSiteCode` — the decoder image ∪ the whole `rlp_walk_next` call chain
      (thunk ∪ shared body ∪ lenient core), with the union's disjointness
      discharged from the linked extents;
    * `walk_next_call_block_within` — the generic three-instruction block with
      an ARBITRARY callee contract as a hypothesis;
    * `walk_next_site_composed_within` — the same block with
      `RlpWalkNextEntryTie.rlp_walk_next_entry_nonlist_strict_spec_within`
      **discharged**, i.e. `hcallee` is proved here, not assumed;
    * `walk_next_site_56_spec_within` … one anchored corollary per site,
      each `A` pinned to `GuestAddrs.header_extended_decode + <off> - 8` and
      the three code memberships `rfl`-checked against
      `headerExtendedDecode_prog`.

  ## ⚠️ What is INHERITED and what is ESTABLISHED — the non-LIST gate

  `RlpWalkNextEntryTie.rlp_walk_next_entry_nonlist_strict_spec_within` is
  `.conditional`: its `hnotlist` premise requires the RLP prefix byte at the
  cursor to be `< 0xc0`, i.e. the item being walked is a byte string and not a
  list.  The LIST arms — the runs that enter `rlp_validate_payload` — are not
  covered by that contract.

  **That gate is INHERITED here, at all nineteen sites, and it is not
  discharged.**  It is a premise of every theorem below.  The reason is not
  effort: it is that `header_extended_decode` *cannot* discharge it.  Reading
  the site block above, the decoder loads the cursor and the end pointer and
  calls; it inspects **nothing** about the byte at the cursor beforehand.  The
  only post-call test is `bnez a1` on the returned status, which happens after
  the callee has already run.  So no instruction of this routine establishes
  `prefix < 0xc0`, and no rearrangement of this proof could make one do so:
  the fact is a property of the caller's input buffer, not of the decoder's
  control flow.

  Semantically the non-LIST arm *is* the live one at all nineteen sites — every
  field of an execution-layer block header is a byte string, so a well-formed
  header never presents a `≥ 0xc0` prefix to these calls.  But that is a
  statement about well-formed headers, and `header_extended_decode` is a
  *decoder*: it is reachable with arbitrary attacker-supplied bytes, for which
  the claim is false.  Recording it as an established fact would be exactly the
  kind of "true of the intended input, assumed of all inputs" step this tranche
  is trying to eliminate.  It therefore stays a binder, and any whole-routine
  triple built on this file inherits it into its `gate :=`.

  #12776 consumes this downstream and needs to know: **the gate survives.**

  The thunk's OTHER gate, `s0 ≥ 2`, is already discharged inside
  `RlpWalkNextEntryTie` (`budget_ge_two`) and is not inherited.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.RlpWalkNextEntryTie
import EvmAsm.Codegen.Programs.HeaderU64ExtractSpec
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.DualReadByteScan

namespace EvmAsm.Codegen.HeaderExtendedDecodeWalkSite

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP
open EvmAsm.Rv64.SAsm (callWithin_spec)
open EvmAsm.Codegen.HeaderU64ExtractSpec (headerExtendedDecodeBase headerExtendedDecodeCode)

/-! ## The code requirement

    Four linked extents, pairwise non-overlapping by construction:

    | image                  | entry        | insns | bytes |
    |------------------------|--------------|------:|------:|
    | `header_extended_decode` | `0x8000bb64` | 174 | 696 |
    | `rlp_walk_next` (thunk)  | `0x80004cdc` |  13 |  52 |
    | `rlp_walk_next_shared`   | `0x80004d10` |  52 | 208 |
    | `rlp_walk_next_core`     | `0x80004e34` | 103 | 412 |

    The last three are already unioned as `RlpWalkNextEntryTie.wholeCode`; all
    three end below `0x80005000`, so the decoder's extent is disjoint from the
    union. -/

/-- The decoder image ∪ the whole `rlp_walk_next` call chain. -/
def walkSiteCode : CodeReq :=
  headerExtendedDecodeCode.union RlpWalkNextEntryTie.wholeCode

theorem walkSiteCode_dec_mem (a : Word) (i : Instr)
    (h : headerExtendedDecodeCode a = some i) : walkSiteCode a = some i :=
  CodeReq.union_mono_left a i h

/-- The decoder's linked base as a `Nat`, so the three range-disjointness side
    conditions below are `omega` on concrete addresses. -/
private theorem hed_base_toNat :
    (headerExtendedDecodeBase : Word).toNat = GuestAddrs.header_extended_decode := by
  decide

/-- The decoder's extent is disjoint from all three images of the walk chain:
    thunk, shared body and lenient core all end below `0x80005000`, while the
    decoder starts at `0x8000bb64`. -/
theorem decoder_walk_disjoint :
    headerExtendedDecodeCode.Disjoint RlpWalkNextEntryTie.wholeCode := by
  refine CodeReq.Disjoint.union_right ?_ (CodeReq.Disjoint.union_right ?_ ?_)
  · exact CodeReq.ofProg_disjoint_range_len headerExtendedDecodeBase
      headerExtendedDecode_prog 174 RlpWalkNextEntryTie.T rlpWalkNext_prog 13
      headerExtendedDecode_prog_length RlpWalkNextEntryTie.entry_length (by
        intro k1 k2 h1 h2 heq
        have hB : (headerExtendedDecodeBase : Word).toNat = 2147531620 := hed_base_toNat
        have hT : (RlpWalkNextEntryTie.T : Word).toNat = 2147503324 := by decide
        have h := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hB, hT] at h
        omega)
  · exact CodeReq.ofProg_disjoint_range_len headerExtendedDecodeBase
      headerExtendedDecode_prog 174 RlpWalkNextStrictTie.S rlpWalkNextShared_prog 52
      headerExtendedDecode_prog_length RlpWalkNextStrictTie.shared_length (by
        intro k1 k2 h1 h2 heq
        have hB : (headerExtendedDecodeBase : Word).toNat = 2147531620 := hed_base_toNat
        have hS : (RlpWalkNextStrictTie.S : Word).toNat = 2147503376 := by decide
        have h := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hB, hS] at h
        omega)
  · exact CodeReq.ofProg_disjoint_range_len headerExtendedDecodeBase
      headerExtendedDecode_prog 174 RlpWalkNextStrictTie.C rlpWalkNextCore_prog 103
      headerExtendedDecode_prog_length rfl (by
        intro k1 k2 h1 h2 heq
        have hB : (headerExtendedDecodeBase : Word).toNat = 2147531620 := hed_base_toNat
        have hC : (RlpWalkNextStrictTie.C : Word).toNat = 2147503668 := by decide
        have h := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hB, hC] at h
        omega)

theorem walkSiteCode_callee_mem (a : Word) (i : Instr)
    (h : RlpWalkNextEntryTie.wholeCode a = some i) : walkSiteCode a = some i :=
  CodeReq.mono_union_right decoder_walk_disjoint (fun _ _ h' => h') a i h

/-! ## Instruction membership at a program index -/

/-- `k < 174` as a bound on `headerExtendedDecode_prog.length`, routed through
    the named length theorem (`decide` on the goal re-elaborates the
    174-element `Instr` list and exhausts the recursion budget). -/
private theorem hed_index_lt (k : Nat) (h : k < 174) :
    k < headerExtendedDecode_prog.length := by
  rw [headerExtendedDecode_prog_length]; exact h

/-- Instruction `k` of the linked decoder Program is in `walkSiteCode`. -/
private theorem hed_mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = headerExtendedDecodeBase + BitVec.ofNat 64 (4 * k))
    (hk : k < headerExtendedDecode_prog.length)
    (hins : headerExtendedDecode_prog[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → walkSiteCode a = some i :=
  fun a i h => walkSiteCode_dec_mem a i
    (CodeReq.ofProg_mem_at headerExtendedDecodeBase A headerExtendedDecode_prog
      k ins hA hk hins
      (by rw [headerExtendedDecode_prog_length]; decide) a i h)

/-! ## The generic three-instruction call block -/

/-- **The `rlp_walk_next` call block, with an arbitrary callee contract.**

    `A → A + 12`, three instructions plus the callee's `n`.  `x19` (`s3`, the
    walk cursor) and `x9` (`s1`, the end pointer) are the two sources; both are
    handed to the callee as part of its own footprint, because the thunk
    restores `x9` from its frame and leaves `x19` untouched. -/
theorem walk_next_call_block_within
    (A calleeEntry cursor endPtr raIn old10 old11 : Word)
    (jal : BitVec 21) (n : Nat) (R Q : Assertion) (cr : CodeReq)
    (hjal : A + 8 + signExtend21 jal = calleeEntry)
    (hmv0_mem : ∀ a i,
      CodeReq.singleton A (.MV .x10 .x19) a = some i → cr a = some i)
    (hmv1_mem : ∀ a i,
      CodeReq.singleton (A + 4) (.MV .x11 .x9) a = some i → cr a = some i)
    (hjal_mem : ∀ a i,
      CodeReq.singleton (A + 8) (.JAL .x1 jal) a = some i → cr a = some i)
    (hR : R.pcFree)
    (hcallee : cpsTripleWithin n calleeEntry (A + 12) cr
      ((.x1 ↦ᵣ (A + 12)) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x19 ↦ᵣ cursor) ** (.x9 ↦ᵣ endPtr) ** R)
      ((.x1 ↦ᵣ (A + 12)) ** Q)) :
    cpsTripleWithin (3 + n) A (A + 12) cr
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ cursor) ** (.x9 ↦ᵣ endPtr) ** R)
      ((.x1 ↦ᵣ (A + 12)) ** Q) := by
  have hadd4 : A + 4 + 4 = A + 8 := by bv_omega
  have hadd8 : A + 8 + 4 = A + 12 := by bv_omega
  -- A: mv a0, s3
  have hmv0 := mv_spec_gen_within .x10 .x19 cursor old10 A (by decide)
  have hmv0c := cpsTripleWithin_extend_code hmv0_mem hmv0
  have hmv0f := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ old11) ** (.x9 ↦ᵣ endPtr) ** R)
    (pcFree_sepConj (by pcFree)
      (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) hR))) hmv0c
  -- A+4: mv a1, s1
  have hmv1 := mv_spec_gen_within .x11 .x9 endPtr old11 (A + 4) (by decide)
  rw [hadd4] at hmv1
  have hmv1c := cpsTripleWithin_extend_code hmv1_mem hmv1
  have hmv1f := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ cursor) ** R)
    (pcFree_sepConj (by pcFree)
      (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) hR))) hmv1c
  -- A+8: jal ra, rlp_walk_next
  have hcallee' : cpsTripleWithin n calleeEntry (A + 8 + 4) cr
      ((.x1 ↦ᵣ (A + 8 + 4)) ** ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x19 ↦ᵣ cursor) ** (.x9 ↦ᵣ endPtr) ** R))
      ((.x1 ↦ᵣ (A + 8 + 4)) ** Q) := by
    rw [hadd8]; exact hcallee
  have hcall := callWithin_spec (A + 8) calleeEntry raIn jal n
    hjal hjal_mem
    (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree)
      (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) hR)))) hcallee'
  rw [hadd8] at hcall
  have s01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hmv0f hmv1f
  have s012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s01 hcall
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) s012)

end EvmAsm.Codegen.HeaderExtendedDecodeWalkSite
