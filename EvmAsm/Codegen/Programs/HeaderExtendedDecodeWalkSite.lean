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

/-! ## The two-instruction argument setup -/

/-- **The `mv a0,s3 ; mv a1,s1` prefix of a `rlp_walk_next` call site.**

    `A → A + 8`, prepended to an already-composed call step `A + 8 → A + 12`.
    Splitting it this way keeps the post `Q` completely free, which matters
    because the thunk's post `entryPost` carries `x1` *inside* its existential
    body and so cannot be factored as `(.x1 ↦ᵣ _) ** Q`.

    `x19` (`s3`, the walk cursor) and `x9` (`s1`, the end pointer) are the two
    sources.  Both are still live at the call: `x9` because the thunk restores
    it from its own frame (so it is in the callee's footprint), `x19` because no
    instruction of the walk chain touches it (so it is framed). -/
theorem walk_next_mv_prefix_within
    (A cursor endPtr raIn old10 old11 : Word)
    (m : Nat) (Prest Q : Assertion) (cr : CodeReq)
    (hmv0_mem : ∀ a i,
      CodeReq.singleton A (.MV .x10 .x19) a = some i → cr a = some i)
    (hmv1_mem : ∀ a i,
      CodeReq.singleton (A + 4) (.MV .x11 .x9) a = some i → cr a = some i)
    (hPrest : Prest.pcFree)
    (hcall : cpsTripleWithin m (A + 8) (A + 12) cr
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
        (.x19 ↦ᵣ cursor) ** (.x9 ↦ᵣ endPtr) ** Prest) Q) :
    cpsTripleWithin (2 + m) A (A + 12) cr
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ cursor) ** (.x9 ↦ᵣ endPtr) ** Prest) Q := by
  have hadd4 : A + 4 + 4 = A + 8 := by bv_omega
  -- A: mv a0, s3
  have hmv0 := mv_spec_gen_within .x10 .x19 cursor old10 A (by decide)
  have hmv0c := cpsTripleWithin_extend_code hmv0_mem hmv0
  have hmv0f := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ old11) ** (.x9 ↦ᵣ endPtr) ** Prest)
    (pcFree_sepConj (by pcFree)
      (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) hPrest))) hmv0c
  -- A+4: mv a1, s1
  have hmv1 := mv_spec_gen_within .x11 .x9 endPtr old11 (A + 4) (by decide)
  rw [hadd4] at hmv1
  have hmv1c := cpsTripleWithin_extend_code hmv1_mem hmv1
  have hmv1f := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ cursor) ** Prest)
    (pcFree_sepConj (by pcFree)
      (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) hPrest))) hmv1c
  have s01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hmv0f hmv1f
  have s012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s01 hcall
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) s012)

/-! ## The call step, with the thunk's contract discharged

    `hcallee` below is **proved**, from
    `RlpWalkNextEntryTie.rlp_walk_next_entry_nonlist_strict_spec_within`.
    Nothing in this file assumes a callee contract. -/

/-- The walk chain has no instruction at an address inside the decoder's
    extent, so the site's `JAL` singleton is disjoint from it. -/
private theorem walk_none_at (A : Word) (k : Nat)
    (hA : A = headerExtendedDecodeBase + BitVec.ofNat 64 (4 * k))
    (hk : k < 174) : RlpWalkNextEntryTie.wholeCode A = none := by
  have hk' : k < headerExtendedDecode_prog.length := hed_index_lt k hk
  have hsome : headerExtendedDecodeCode A
      = some (headerExtendedDecode_prog.get ⟨k, hk'⟩) :=
    CodeReq.ofProg_lookup_addr headerExtendedDecodeBase headerExtendedDecode_prog k A
      hk' (by rw [headerExtendedDecode_prog_length]; decide) hA
  rcases decoder_walk_disjoint A with h | h
  · rw [hsome] at h; exact absurd h (by simp)
  · exact h

/-- `pcFree` extended to close `bytesRegion _.pcFree` leaves. -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj
    | pcFree)

/-- The frame a `rlp_walk_next` call site carries besides `x1`, `x10`, `x11`,
    `x19` and `x9`.

    Every register here is read off the disassembly of
    `GuestAddrs.header_extended_decode` or of the thunk it calls:

    | reg   | role                                    | read from |
    |-------|-----------------------------------------|-----------|
    | `x2`  | stack pointer, `sp + 96` on entry       | decoder idx 0 `addi sp,sp,-64`; the thunk's own frame is the 96 bytes below |
    | `x0`  | hardwired zero                          | decoder idx 9 `bne a2,zero,…` |
    | `x8`  | `s0`, spilled by the decoder            | decoder idx 2 `sd s0,8(sp)`, idx 6 `mv s0,a0` |
    | `x12` | `a2`, the callee's third result         | decoder idx 9 `bne a2,zero`, idx 18 `bne a2,t0` |
    | `x5`  | `t0`                                    | decoder idx 17 `li t0,32`; thunk idx 4 `sub t0,a1,a0` |
    | `x6`  | `t1`                                    | decoder idx 22 `lbu t1,0(t3)` |
    | `x7`  | `t2`                                    | required by `rlp_walk_next_shared`, not named by the decoder |
    | `x13` | `a3`                                    | clobbered by `rlp_walk_next_shared`; carried as `regOwn` |
    | `x28` | `t3`, copy-loop source pointer          | decoder idx 19 `sub t3,a0,a2` |
    | `x29` | `t4`, copy-loop destination pointer     | decoder idx 20 `mv t4,s2`, idx 46 `addi t4,s2,32` |
    | `x30` | `t5`                                    | clobbered by the walk chain |
    | `x31` | `t6`                                    | clobbered by the walk chain |
    | `x18` | `s2`, the 144-byte output struct pointer | decoder idx 4 `sd s2,24(sp)`, idx 7 `mv s2,a2` |

    `x30`, `x31`, `x7` and `x13` appear only because the CALLEE requires or
    clobbers them.  They are in `P` and `Q` — not omitted — precisely because
    `cpsTripleWithin` quantifies over every frame `R`, so a caller could pin
    them and a clobbering callee would falsify the triple.  `x18` is NOT in the
    walk chain's footprint (nothing in it touches `s2`), so it is framed rather
    than owned; it is listed here because the decoder needs it back. -/
abbrev siteFrame (sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v srcBase : Word) (srcBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ (sp + 96)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ s0Old) ** (.x12 ↦ᵣ a2Old) **
  (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** regOwn .x13 **
  (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
  memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) **
  memOwn (sp + 24) ** memOwn (sp + 32) ** memOwn (sp + 40) **
  memOwn (sp + 64) ** memOwn (sp + 72) ** memOwn (sp + 80) **
  bytesRegion srcBase srcBytes ** (.x18 ↦ᵣ s18v)

/-- The ten input-domain premises of
    `RlpWalkNextEntryTie.rlp_walk_next_entry_nonlist_strict_spec_within`,
    bundled so that a call site is one hypothesis rather than ten.

    Fields `salign`…`ll` and `endValid`/`lt` are ordinary resource framing
    (alignment, in-bounds, no-wrap, valid guest byte access, and the "the
    cursor is strictly before the end" translation of the thunk's `s0 ≥ 2`
    budget).

    ⛔ `notlist` is the REAL gate: it is the `.conditional` premise inherited
    from row 3 and it is NOT discharged anywhere in this file.  See the module
    docstring for why `header_extended_decode` cannot discharge it. -/
structure WalkPre (srcBase endPtr : Word) (srcBytes : List (BitVec 8))
    (srcOff : Nat) : Prop where
  salign : srcBase.toNat % 8 = 0
  off : srcOff < srcBytes.length
  over : srcBase.toNat + srcOff < 2 ^ 64
  valid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true
  ss : ¬ BitVec.ult ((srcBytes[srcOff]'off).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'off).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'off).zeroExtend 64 - (0x80 : Word))
          (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true →
        ((srcBytes[srcOff]'off).zeroExtend 64 - (0x80 : Word)) = (1 : Word) →
        srcOff + 1 < srcBytes.length ∧ srcBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1)) = true
  ls : ¬ BitVec.ult ((srcBytes[srcOff]'off).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((srcBytes[srcOff]'off).zeroExtend 64) (0xc0 : Word) = true →
        ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
            (((srcBytes[srcOff]'off).zeroExtend 64 - (0xb7 : Word)) +
              signExtend12 (1 : BitVec 12))) = true →
        srcOff + 1 + ((srcBytes[srcOff]'off).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'off).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'off).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true
  ll : ¬ BitVec.ult ((srcBytes[srcOff]'off).zeroExtend 64) (0xf8 : Word) = true →
        ¬ BitVec.ult endPtr ((srcBase + BitVec.ofNat 64 srcOff) +
            (((srcBytes[srcOff]'off).zeroExtend 64 - (0xf7 : Word)) +
              signExtend12 (1 : BitVec 12))) = true →
        srcOff + 1 + ((srcBytes[srcOff]'off).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ srcBytes.length ∧
        srcBase.toNat + (srcOff + 1 +
          ((srcBytes[srcOff]'off).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((srcBytes[srcOff]'off).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true
  endValid : isValidByteAccess endPtr = true
  lt : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true
  notlist : BitVec.ult ((srcBytes[srcOff]'off).zeroExtend 64) (0xc0 : Word) = true

/-- The post of one walk site: the thunk's own `entryPost`, plus the two
    registers the walk chain never touches (`x19` = `s3`, the cursor the
    decoder is about to overwrite with `a0`; `x18` = `s2`, the output
    pointer). -/
abbrev sitePost (A sp s0Old srcBase endPtr s18v : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat) : Assertion :=
  RlpWalkNextEntryTie.entryPost sp (A + 12) s0Old endPtr srcBase endPtr
      srcBytes srcOff floor **
    ((.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ s18v))

/--
**One `rlp_walk_next` call site of `header_extended_decode`, callee COMPOSED.**

`A → A + 12`, `2 + (1 + 122) = 125` steps: `mv a0,s3`, `mv a1,s1`, `jal`, and
the thunk's whole-routine contract.

`hcallee` is *not* a hypothesis.  The thunk's triple
`RlpWalkNextEntryTie.rlp_walk_next_entry_nonlist_strict_spec_within` is applied
here, so this theorem carries the real cost of the call rather than assuming
it.

⚠️ `hnotlist` is the INHERITED `.conditional` gate; see the module docstring.
It is a binder of this theorem and of every corollary below, and the decoder
cannot discharge it — no instruction of `header_extended_decode` inspects the
prefix byte before the call.
-/
theorem walk_next_site_composed_within
    (A : Word) (jal : BitVec 21)
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hjal : A + 8 + signExtend21 jal = RlpWalkNextEntryTie.T)
    (halign : (A + 8 + 4) &&& ~~~(1 : Word) = A + 8 + 4)
    (hnone : RlpWalkNextEntryTie.wholeCode (A + 8) = none)
    (hmv0_mem : ∀ a i,
      CodeReq.singleton A (.MV .x10 .x19) a = some i → walkSiteCode a = some i)
    (hmv1_mem : ∀ a i,
      CodeReq.singleton (A + 4) (.MV .x11 .x9) a = some i → walkSiteCode a = some i)
    (hjal_mem : ∀ a i,
      CodeReq.singleton (A + 8) (.JAL .x1 jal) a = some i → walkSiteCode a = some i)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 A (A + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost A sp s0Old srcBase endPtr s18v srcBytes srcOff floor) := by
  have hadd8 : A + 8 + 4 = A + 12 := by bv_omega
  -- The thunk's whole-routine contract, COMPOSED.
  have hthunk := RlpWalkNextEntryTie.rlp_walk_next_entry_nonlist_strict_spec_within
    sp (A + 12) s0Old endPtr srcBase endPtr a2Old t0Old t1Old t2Old
    t3Old t4Old t5Old t6Old srcBytes srcOff floor
    hpre.salign hpre.off hpre.over hpre.valid hpre.ss hpre.ls hpre.ll
    hpre.endValid hpre.lt hpre.notlist
  have hthunkF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x18 ↦ᵣ s18v))
    (by pcFreeR) hthunk
  have hthunkW := cpsTripleWithin_weaken
    (P' := (.x1 ↦ᵣ (A + 12)) **
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes))
    (Q' := sitePost A sp s0Old srcBase endPtr s18v srcBytes srcOff floor)
    (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) hthunkF
  have hthunk' : cpsTripleWithin 122 RlpWalkNextEntryTie.T
      ((A + 8 + 4) &&& ~~~(1 : Word)) RlpWalkNextEntryTie.wholeCode
      ((.x1 ↦ᵣ (A + 8 + 4)) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
          siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
            s18v srcBase srcBytes))
      (sitePost A sp s0Old srcBase endPtr s18v srcBytes srcOff floor) := by
    rw [hadd8]; exact hthunkW
  have hcall := cpsCallWithin (nSteps := 122) (callerPC := A + 8)
    (calleeEntry := RlpWalkNextEntryTie.T) (vOld := raIn)
    (calleeCode := RlpWalkNextEntryTie.wholeCode) jal hjal halign
    (by pcFreeR) (RlpWalkNextEntryTie.singleton_disjoint_of_none hnone) hthunk'
  have hcallE := cpsTripleWithin_extend_code
    (CodeReq.union_split_mono hjal_mem walkSiteCode_callee_mem) hcall
  rw [hadd8] at hcallE
  have hpre := walk_next_mv_prefix_within A (srcBase + BitVec.ofNat 64 srcOff) endPtr
    raIn old10 old11 (1 + 122)
    (siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v srcBase srcBytes)
    (sitePost A sp s0Old srcBase endPtr s18v srcBytes srcOff floor)
    walkSiteCode hmv0_mem hmv1_mem (by pcFreeR) hcallE
  exact cpsTripleWithin_mono_nSteps (by omega) hpre

/-! ## The nineteen anchored call sites

    Each corollary pins `A` to `GuestAddrs.header_extended_decode + <off> - 8`
    and discharges the three code memberships by `rfl` against
    `headerExtendedDecode_prog`.  The `JAL` target is spelled with `jalOff`
    against `GuestAddrs.rlp_walk_next`, so a relink that moved either symbol
    would break these, not silently retarget them. -/

set_option maxRecDepth 8000 in
/-- `rlp_walk_next` site at `GuestAddrs.header_extended_decode + 56`:
    `mv a0,s3` at program index 12, `mv a1,s1` at 13, `jal` at 14. -/
theorem walk_next_site_56_spec_within
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 (headerExtendedDecodeBase + BitVec.ofNat 64 48)
      (headerExtendedDecodeBase + BitVec.ofNat 64 48 + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost (headerExtendedDecodeBase + BitVec.ofNat 64 48) sp s0Old srcBase
        endPtr s18v srcBytes srcOff floor) :=
  walk_next_site_composed_within _
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 56))
    sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v raIn old10 old11 srcBytes srcOff floor
    (by decide) (by decide)
    (walk_none_at _ 14 (by decide) (by decide))
    (hed_mem_at 12 _ _ (by decide) (hed_index_lt 12 (by decide)) rfl)
    (hed_mem_at 13 _ _ (by decide) (hed_index_lt 13 (by decide)) rfl)
    (hed_mem_at 14 _ _ (by decide) (hed_index_lt 14 (by decide)) rfl)
    hpre

set_option maxRecDepth 8000 in
/-- `rlp_walk_next` site at `GuestAddrs.header_extended_decode + 120`:
    `mv a0,s3` at program index 28, `mv a1,s1` at 29, `jal` at 30. -/
theorem walk_next_site_120_spec_within
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 (headerExtendedDecodeBase + BitVec.ofNat 64 112)
      (headerExtendedDecodeBase + BitVec.ofNat 64 112 + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost (headerExtendedDecodeBase + BitVec.ofNat 64 112) sp s0Old srcBase
        endPtr s18v srcBytes srcOff floor) :=
  walk_next_site_composed_within _
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 120))
    sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v raIn old10 old11 srcBytes srcOff floor
    (by decide) (by decide)
    (walk_none_at _ 30 (by decide) (by decide))
    (hed_mem_at 28 _ _ (by decide) (hed_index_lt 28 (by decide)) rfl)
    (hed_mem_at 29 _ _ (by decide) (hed_index_lt 29 (by decide)) rfl)
    (hed_mem_at 30 _ _ (by decide) (hed_index_lt 30 (by decide)) rfl)
    hpre

set_option maxRecDepth 8000 in
/-- `rlp_walk_next` site at `GuestAddrs.header_extended_decode + 140`:
    `mv a0,s3` at program index 33, `mv a1,s1` at 34, `jal` at 35. -/
theorem walk_next_site_140_spec_within
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 (headerExtendedDecodeBase + BitVec.ofNat 64 132)
      (headerExtendedDecodeBase + BitVec.ofNat 64 132 + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost (headerExtendedDecodeBase + BitVec.ofNat 64 132) sp s0Old srcBase
        endPtr s18v srcBytes srcOff floor) :=
  walk_next_site_composed_within _
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 140))
    sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v raIn old10 old11 srcBytes srcOff floor
    (by decide) (by decide)
    (walk_none_at _ 35 (by decide) (by decide))
    (hed_mem_at 33 _ _ (by decide) (hed_index_lt 33 (by decide)) rfl)
    (hed_mem_at 34 _ _ (by decide) (hed_index_lt 34 (by decide)) rfl)
    (hed_mem_at 35 _ _ (by decide) (hed_index_lt 35 (by decide)) rfl)
    hpre

set_option maxRecDepth 8000 in
/-- `rlp_walk_next` site at `GuestAddrs.header_extended_decode + 160`:
    `mv a0,s3` at program index 38, `mv a1,s1` at 39, `jal` at 40. -/
theorem walk_next_site_160_spec_within
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 (headerExtendedDecodeBase + BitVec.ofNat 64 152)
      (headerExtendedDecodeBase + BitVec.ofNat 64 152 + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost (headerExtendedDecodeBase + BitVec.ofNat 64 152) sp s0Old srcBase
        endPtr s18v srcBytes srcOff floor) :=
  walk_next_site_composed_within _
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 160))
    sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v raIn old10 old11 srcBytes srcOff floor
    (by decide) (by decide)
    (walk_none_at _ 40 (by decide) (by decide))
    (hed_mem_at 38 _ _ (by decide) (hed_index_lt 38 (by decide)) rfl)
    (hed_mem_at 39 _ _ (by decide) (hed_index_lt 39 (by decide)) rfl)
    (hed_mem_at 40 _ _ (by decide) (hed_index_lt 40 (by decide)) rfl)
    hpre

set_option maxRecDepth 8000 in
/-- `rlp_walk_next` site at `GuestAddrs.header_extended_decode + 224`:
    `mv a0,s3` at program index 54, `mv a1,s1` at 55, `jal` at 56. -/
theorem walk_next_site_224_spec_within
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 (headerExtendedDecodeBase + BitVec.ofNat 64 216)
      (headerExtendedDecodeBase + BitVec.ofNat 64 216 + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost (headerExtendedDecodeBase + BitVec.ofNat 64 216) sp s0Old srcBase
        endPtr s18v srcBytes srcOff floor) :=
  walk_next_site_composed_within _
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 224))
    sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v raIn old10 old11 srcBytes srcOff floor
    (by decide) (by decide)
    (walk_none_at _ 56 (by decide) (by decide))
    (hed_mem_at 54 _ _ (by decide) (hed_index_lt 54 (by decide)) rfl)
    (hed_mem_at 55 _ _ (by decide) (hed_index_lt 55 (by decide)) rfl)
    (hed_mem_at 56 _ _ (by decide) (hed_index_lt 56 (by decide)) rfl)
    hpre

set_option maxRecDepth 8000 in
/-- `rlp_walk_next` site at `GuestAddrs.header_extended_decode + 244`:
    `mv a0,s3` at program index 59, `mv a1,s1` at 60, `jal` at 61. -/
theorem walk_next_site_244_spec_within
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 (headerExtendedDecodeBase + BitVec.ofNat 64 236)
      (headerExtendedDecodeBase + BitVec.ofNat 64 236 + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost (headerExtendedDecodeBase + BitVec.ofNat 64 236) sp s0Old srcBase
        endPtr s18v srcBytes srcOff floor) :=
  walk_next_site_composed_within _
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 244))
    sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v raIn old10 old11 srcBytes srcOff floor
    (by decide) (by decide)
    (walk_none_at _ 61 (by decide) (by decide))
    (hed_mem_at 59 _ _ (by decide) (hed_index_lt 59 (by decide)) rfl)
    (hed_mem_at 60 _ _ (by decide) (hed_index_lt 60 (by decide)) rfl)
    (hed_mem_at 61 _ _ (by decide) (hed_index_lt 61 (by decide)) rfl)
    hpre

set_option maxRecDepth 8000 in
/-- `rlp_walk_next` site at `GuestAddrs.header_extended_decode + 264`:
    `mv a0,s3` at program index 64, `mv a1,s1` at 65, `jal` at 66. -/
theorem walk_next_site_264_spec_within
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 (headerExtendedDecodeBase + BitVec.ofNat 64 256)
      (headerExtendedDecodeBase + BitVec.ofNat 64 256 + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost (headerExtendedDecodeBase + BitVec.ofNat 64 256) sp s0Old srcBase
        endPtr s18v srcBytes srcOff floor) :=
  walk_next_site_composed_within _
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 264))
    sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v raIn old10 old11 srcBytes srcOff floor
    (by decide) (by decide)
    (walk_none_at _ 66 (by decide) (by decide))
    (hed_mem_at 64 _ _ (by decide) (hed_index_lt 64 (by decide)) rfl)
    (hed_mem_at 65 _ _ (by decide) (hed_index_lt 65 (by decide)) rfl)
    (hed_mem_at 66 _ _ (by decide) (hed_index_lt 66 (by decide)) rfl)
    hpre

set_option maxRecDepth 8000 in
/-- `rlp_walk_next` site at `GuestAddrs.header_extended_decode + 284`:
    `mv a0,s3` at program index 69, `mv a1,s1` at 70, `jal` at 71. -/
theorem walk_next_site_284_spec_within
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 (headerExtendedDecodeBase + BitVec.ofNat 64 276)
      (headerExtendedDecodeBase + BitVec.ofNat 64 276 + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost (headerExtendedDecodeBase + BitVec.ofNat 64 276) sp s0Old srcBase
        endPtr s18v srcBytes srcOff floor) :=
  walk_next_site_composed_within _
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 284))
    sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v raIn old10 old11 srcBytes srcOff floor
    (by decide) (by decide)
    (walk_none_at _ 71 (by decide) (by decide))
    (hed_mem_at 69 _ _ (by decide) (hed_index_lt 69 (by decide)) rfl)
    (hed_mem_at 70 _ _ (by decide) (hed_index_lt 70 (by decide)) rfl)
    (hed_mem_at 71 _ _ (by decide) (hed_index_lt 71 (by decide)) rfl)
    hpre

set_option maxRecDepth 8000 in
/-- `rlp_walk_next` site at `GuestAddrs.header_extended_decode + 304`:
    `mv a0,s3` at program index 74, `mv a1,s1` at 75, `jal` at 76. -/
theorem walk_next_site_304_spec_within
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 (headerExtendedDecodeBase + BitVec.ofNat 64 296)
      (headerExtendedDecodeBase + BitVec.ofNat 64 296 + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost (headerExtendedDecodeBase + BitVec.ofNat 64 296) sp s0Old srcBase
        endPtr s18v srcBytes srcOff floor) :=
  walk_next_site_composed_within _
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 304))
    sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v raIn old10 old11 srcBytes srcOff floor
    (by decide) (by decide)
    (walk_none_at _ 76 (by decide) (by decide))
    (hed_mem_at 74 _ _ (by decide) (hed_index_lt 74 (by decide)) rfl)
    (hed_mem_at 75 _ _ (by decide) (hed_index_lt 75 (by decide)) rfl)
    (hed_mem_at 76 _ _ (by decide) (hed_index_lt 76 (by decide)) rfl)
    hpre

set_option maxRecDepth 8000 in
/-- `rlp_walk_next` site at `GuestAddrs.header_extended_decode + 344`:
    `mv a0,s3` at program index 84, `mv a1,s1` at 85, `jal` at 86. -/
theorem walk_next_site_344_spec_within
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 (headerExtendedDecodeBase + BitVec.ofNat 64 336)
      (headerExtendedDecodeBase + BitVec.ofNat 64 336 + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost (headerExtendedDecodeBase + BitVec.ofNat 64 336) sp s0Old srcBase
        endPtr s18v srcBytes srcOff floor) :=
  walk_next_site_composed_within _
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 344))
    sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v raIn old10 old11 srcBytes srcOff floor
    (by decide) (by decide)
    (walk_none_at _ 86 (by decide) (by decide))
    (hed_mem_at 84 _ _ (by decide) (hed_index_lt 84 (by decide)) rfl)
    (hed_mem_at 85 _ _ (by decide) (hed_index_lt 85 (by decide)) rfl)
    (hed_mem_at 86 _ _ (by decide) (hed_index_lt 86 (by decide)) rfl)
    hpre

set_option maxRecDepth 8000 in
/-- `rlp_walk_next` site at `GuestAddrs.header_extended_decode + 384`:
    `mv a0,s3` at program index 94, `mv a1,s1` at 95, `jal` at 96. -/
theorem walk_next_site_384_spec_within
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 (headerExtendedDecodeBase + BitVec.ofNat 64 376)
      (headerExtendedDecodeBase + BitVec.ofNat 64 376 + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost (headerExtendedDecodeBase + BitVec.ofNat 64 376) sp s0Old srcBase
        endPtr s18v srcBytes srcOff floor) :=
  walk_next_site_composed_within _
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 384))
    sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v raIn old10 old11 srcBytes srcOff floor
    (by decide) (by decide)
    (walk_none_at _ 96 (by decide) (by decide))
    (hed_mem_at 94 _ _ (by decide) (hed_index_lt 94 (by decide)) rfl)
    (hed_mem_at 95 _ _ (by decide) (hed_index_lt 95 (by decide)) rfl)
    (hed_mem_at 96 _ _ (by decide) (hed_index_lt 96 (by decide)) rfl)
    hpre

set_option maxRecDepth 8000 in
/-- `rlp_walk_next` site at `GuestAddrs.header_extended_decode + 424`:
    `mv a0,s3` at program index 104, `mv a1,s1` at 105, `jal` at 106. -/
theorem walk_next_site_424_spec_within
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 (headerExtendedDecodeBase + BitVec.ofNat 64 416)
      (headerExtendedDecodeBase + BitVec.ofNat 64 416 + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost (headerExtendedDecodeBase + BitVec.ofNat 64 416) sp s0Old srcBase
        endPtr s18v srcBytes srcOff floor) :=
  walk_next_site_composed_within _
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 424))
    sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v raIn old10 old11 srcBytes srcOff floor
    (by decide) (by decide)
    (walk_none_at _ 106 (by decide) (by decide))
    (hed_mem_at 104 _ _ (by decide) (hed_index_lt 104 (by decide)) rfl)
    (hed_mem_at 105 _ _ (by decide) (hed_index_lt 105 (by decide)) rfl)
    (hed_mem_at 106 _ _ (by decide) (hed_index_lt 106 (by decide)) rfl)
    hpre

set_option maxRecDepth 8000 in
/-- `rlp_walk_next` site at `GuestAddrs.header_extended_decode + 464`:
    `mv a0,s3` at program index 114, `mv a1,s1` at 115, `jal` at 116. -/
theorem walk_next_site_464_spec_within
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 (headerExtendedDecodeBase + BitVec.ofNat 64 456)
      (headerExtendedDecodeBase + BitVec.ofNat 64 456 + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost (headerExtendedDecodeBase + BitVec.ofNat 64 456) sp s0Old srcBase
        endPtr s18v srcBytes srcOff floor) :=
  walk_next_site_composed_within _
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 464))
    sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v raIn old10 old11 srcBytes srcOff floor
    (by decide) (by decide)
    (walk_none_at _ 116 (by decide) (by decide))
    (hed_mem_at 114 _ _ (by decide) (hed_index_lt 114 (by decide)) rfl)
    (hed_mem_at 115 _ _ (by decide) (hed_index_lt 115 (by decide)) rfl)
    (hed_mem_at 116 _ _ (by decide) (hed_index_lt 116 (by decide)) rfl)
    hpre

set_option maxRecDepth 8000 in
/-- `rlp_walk_next` site at `GuestAddrs.header_extended_decode + 484`:
    `mv a0,s3` at program index 119, `mv a1,s1` at 120, `jal` at 121. -/
theorem walk_next_site_484_spec_within
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 (headerExtendedDecodeBase + BitVec.ofNat 64 476)
      (headerExtendedDecodeBase + BitVec.ofNat 64 476 + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost (headerExtendedDecodeBase + BitVec.ofNat 64 476) sp s0Old srcBase
        endPtr s18v srcBytes srcOff floor) :=
  walk_next_site_composed_within _
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 484))
    sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v raIn old10 old11 srcBytes srcOff floor
    (by decide) (by decide)
    (walk_none_at _ 121 (by decide) (by decide))
    (hed_mem_at 119 _ _ (by decide) (hed_index_lt 119 (by decide)) rfl)
    (hed_mem_at 120 _ _ (by decide) (hed_index_lt 120 (by decide)) rfl)
    (hed_mem_at 121 _ _ (by decide) (hed_index_lt 121 (by decide)) rfl)
    hpre

set_option maxRecDepth 8000 in
/-- `rlp_walk_next` site at `GuestAddrs.header_extended_decode + 504`:
    `mv a0,s3` at program index 124, `mv a1,s1` at 125, `jal` at 126. -/
theorem walk_next_site_504_spec_within
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 (headerExtendedDecodeBase + BitVec.ofNat 64 496)
      (headerExtendedDecodeBase + BitVec.ofNat 64 496 + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost (headerExtendedDecodeBase + BitVec.ofNat 64 496) sp s0Old srcBase
        endPtr s18v srcBytes srcOff floor) :=
  walk_next_site_composed_within _
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 504))
    sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v raIn old10 old11 srcBytes srcOff floor
    (by decide) (by decide)
    (walk_none_at _ 126 (by decide) (by decide))
    (hed_mem_at 124 _ _ (by decide) (hed_index_lt 124 (by decide)) rfl)
    (hed_mem_at 125 _ _ (by decide) (hed_index_lt 125 (by decide)) rfl)
    (hed_mem_at 126 _ _ (by decide) (hed_index_lt 126 (by decide)) rfl)
    hpre

set_option maxRecDepth 8000 in
/-- `rlp_walk_next` site at `GuestAddrs.header_extended_decode + 524`:
    `mv a0,s3` at program index 129, `mv a1,s1` at 130, `jal` at 131. -/
theorem walk_next_site_524_spec_within
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 (headerExtendedDecodeBase + BitVec.ofNat 64 516)
      (headerExtendedDecodeBase + BitVec.ofNat 64 516 + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost (headerExtendedDecodeBase + BitVec.ofNat 64 516) sp s0Old srcBase
        endPtr s18v srcBytes srcOff floor) :=
  walk_next_site_composed_within _
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 524))
    sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v raIn old10 old11 srcBytes srcOff floor
    (by decide) (by decide)
    (walk_none_at _ 131 (by decide) (by decide))
    (hed_mem_at 129 _ _ (by decide) (hed_index_lt 129 (by decide)) rfl)
    (hed_mem_at 130 _ _ (by decide) (hed_index_lt 130 (by decide)) rfl)
    (hed_mem_at 131 _ _ (by decide) (hed_index_lt 131 (by decide)) rfl)
    hpre

set_option maxRecDepth 8000 in
/-- `rlp_walk_next` site at `GuestAddrs.header_extended_decode + 564`:
    `mv a0,s3` at program index 139, `mv a1,s1` at 140, `jal` at 141. -/
theorem walk_next_site_564_spec_within
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 (headerExtendedDecodeBase + BitVec.ofNat 64 556)
      (headerExtendedDecodeBase + BitVec.ofNat 64 556 + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost (headerExtendedDecodeBase + BitVec.ofNat 64 556) sp s0Old srcBase
        endPtr s18v srcBytes srcOff floor) :=
  walk_next_site_composed_within _
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 564))
    sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v raIn old10 old11 srcBytes srcOff floor
    (by decide) (by decide)
    (walk_none_at _ 141 (by decide) (by decide))
    (hed_mem_at 139 _ _ (by decide) (hed_index_lt 139 (by decide)) rfl)
    (hed_mem_at 140 _ _ (by decide) (hed_index_lt 140 (by decide)) rfl)
    (hed_mem_at 141 _ _ (by decide) (hed_index_lt 141 (by decide)) rfl)
    hpre

set_option maxRecDepth 8000 in
/-- `rlp_walk_next` site at `GuestAddrs.header_extended_decode + 584`:
    `mv a0,s3` at program index 144, `mv a1,s1` at 145, `jal` at 146. -/
theorem walk_next_site_584_spec_within
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 (headerExtendedDecodeBase + BitVec.ofNat 64 576)
      (headerExtendedDecodeBase + BitVec.ofNat 64 576 + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost (headerExtendedDecodeBase + BitVec.ofNat 64 576) sp s0Old srcBase
        endPtr s18v srcBytes srcOff floor) :=
  walk_next_site_composed_within _
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 584))
    sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v raIn old10 old11 srcBytes srcOff floor
    (by decide) (by decide)
    (walk_none_at _ 146 (by decide) (by decide))
    (hed_mem_at 144 _ _ (by decide) (hed_index_lt 144 (by decide)) rfl)
    (hed_mem_at 145 _ _ (by decide) (hed_index_lt 145 (by decide)) rfl)
    (hed_mem_at 146 _ _ (by decide) (hed_index_lt 146 (by decide)) rfl)
    hpre

set_option maxRecDepth 8000 in
/-- `rlp_walk_next` site at `GuestAddrs.header_extended_decode + 624`:
    `mv a0,s3` at program index 154, `mv a1,s1` at 155, `jal` at 156. -/
theorem walk_next_site_624_spec_within
    (sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      s18v raIn old10 old11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff floor : Nat)
    (hpre : WalkPre srcBase endPtr srcBytes srcOff) :
    cpsTripleWithin 125 (headerExtendedDecodeBase + BitVec.ofNat 64 616)
      (headerExtendedDecodeBase + BitVec.ofNat 64 616 + 12) walkSiteCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) **
        (.x19 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x9 ↦ᵣ endPtr) **
        siteFrame sp s0Old a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          s18v srcBase srcBytes)
      (sitePost (headerExtendedDecodeBase + BitVec.ofNat 64 616) sp s0Old srcBase
        endPtr s18v srcBytes srcOff floor) :=
  walk_next_site_composed_within _
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 624))
    sp s0Old srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
    s18v raIn old10 old11 srcBytes srcOff floor
    (by decide) (by decide)
    (walk_none_at _ 156 (by decide) (by decide))
    (hed_mem_at 154 _ _ (by decide) (hed_index_lt 154 (by decide)) rfl)
    (hed_mem_at 155 _ _ (by decide) (hed_index_lt 155 (by decide)) rfl)
    (hed_mem_at 156 _ _ (by decide) (hed_index_lt 156 (by decide)) rfl)
    hpre

end EvmAsm.Codegen.HeaderExtendedDecodeWalkSite
