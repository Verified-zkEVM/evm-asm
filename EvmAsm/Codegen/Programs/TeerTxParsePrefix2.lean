/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix2

  PASS 3 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  Continues `TeerTxParsePrefix` (which landed the first call group,
  `tx_type_dispatch`, instrs 34..41).  This module composes the REST of the
  tx-parse prefix (instructions 42..181), from the `tx_type_dispatch`
  parse-success fall-through (`teerB + 168`) through to the per-auth loop head
  guard (`teerB + 724`, instruction 181):

    * type==4 check (42..46) + inner-payload cursor/len setup (47..53);
    * the `to`/value walk GROUP: `rlp_walk_init`@54 + 6× `rlp_walk_next`;
    * the authorization-list walk GROUP: re-`rlp_walk_init`@110 + 10×
      `rlp_walk_next`;
    * `rlp_list_count_items`@169 (count→x23) + list re-init@176;
    * each post-call parse-failure `BNE` (→ far epilogue `teerB + 2856`).

  Straight-line (call-free) blocks are proved over `teerCode` directly (as in
  `TeerBodyDecode`); the call groups lift the assumed callee contracts
  (`TeerBodyAssumptions`) through the `jal` via `callWithin_spec`, framing each
  callee's scratch footprint; every post-call `BNE` dispatch is proved over
  `fullCode` via `teer_mono` (mirroring `teer_txtype_bne_spec`).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## Body scratch globals used by the prefix straight-line blocks -/

/-- Guest `.bss` cell holding the recipient (`to`) content pointer. -/
abbrev teerRecipientPtr : Word := (GuestAddrs.teer_recipient_ptr : Word)
/-- Guest `.bss` cell holding the recipient (`to`) content length. -/
abbrev teerRecipientLen : Word := (GuestAddrs.teer_recipient_len : Word)
/-- Guest `.bss` cell holding the `value ≠ 0` flag. -/
abbrev teerValueNonzero : Word := (GuestAddrs.teer_value_nonzero : Word)
/-- Guest `.bss` cell holding the authorization-list item count. -/
abbrev teerAuthCount : Word := (GuestAddrs.teer_auth_count : Word)

/-! ## type==4 check: load teer_type (instructions 42..45)

    From the `tx_type_dispatch` parse-success fall-through (`teerB + 168`):
    materialise `&teer_type` into `x5`, load the parsed type into `x6`, and
    `li x7, 4`.  Exit `teerB + 184`, the type-mismatch `BNE` at instruction 46.
    Stated over `teerCode` (call-free). -/
set_option maxRecDepth 8000 in
theorem teer_type4_load_spec (v5 v6 v7 tval : Word) :
    cpsTripleWithin 4 (teerB + 168) (teerB + 184) teerCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (teerType ↦ₘ tval))
      ((.x5 ↦ᵣ teerType) ** (.x6 ↦ᵣ tval) ** (.x7 ↦ᵣ (4 : Word)) ** (teerType ↦ₘ tval)) := by
  have h0 := la_materialize_within .x5 v5 (teerB + 168) teerType (by decide) (by decide)
    (CodeReq.ofProg_mem_at teerB (teerB + 168) teerProg 42
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (teerB + 168) teerType))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
    (CodeReq.ofProg_mem_at teerB (teerB + 172) teerProg 43
      (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (teerB + 168) teerType))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
  have h1 := ld_spec_gen_within .x6 .x5 teerType v6 tval (0 : BitVec 12) (teerB + 176) (by decide)
  have h2 := li_spec_gen_within .x7 v7 (4 : Word) (teerB + 180) (by decide)
  runBlock h0 h1 h2

/-! ## type==4 check: dispatch (instruction 46)

    `bne x6(type), x7(=4)` at `teerB + 184`.  TAKEN (`type ≠ 4`) exits to the
    far epilogue `teerB + 2856` (a non-type-4 transaction contributes nothing);
    NOT-TAKEN (`type = 4`) falls through to `teerB + 188`, the inner-payload
    cursor setup. -/
set_option maxRecDepth 8000 in
theorem teer_type4_bne_spec (tval : Word) :
    cpsBranchWithin 1 (teerB + 184) fullCode
      ((.x6 ↦ᵣ tval) ** (.x7 ↦ᵣ (4 : Word)))
      (teerB + 2856) ((.x6 ↦ᵣ tval) ** (.x7 ↦ᵣ (4 : Word)) ** ⌜tval ≠ (4 : Word)⌝)
      (teerB + 188) ((.x6 ↦ᵣ tval) ** (.x7 ↦ᵣ (4 : Word)) ** ⌜tval = (4 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x6 .x7 (2672 : BitVec 13) tval (4 : Word) (teerB + 184)
  rw [show (teerB + 184) + signExtend13 (2672 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2672 : BitVec 13) = (2672 : Word) from by decide]; bv_omega,
      show (teerB + 184) + 4 = teerB + 188 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 184) teerProg 46
    (.BNE .x6 .x7 (2672 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

/-! ## inner-payload cursor/len setup (instructions 47..53)

    `type == 4` fall-through (`teerB + 188`): load `teer_inner_off` into `x6`,
    compute the inner-payload cursor `x21 = x8(txPtr) + inner_off` and length
    `x22 = x9(txLen) - inner_off`, and stage them into the `rlp_walk_init` ABI
    args `a0`/`a1`.  Exit `teerB + 216`, the `jal rlp_walk_init` at
    instruction 54.  Stated over `teerCode` (call-free). -/
set_option maxRecDepth 8000 in
theorem teer_cursor_setup_spec (v8 v9 v5 v6 v10o v11o v21o v22o ioff : Word) :
    cpsTripleWithin 7 (teerB + 188) (teerB + 216) teerCode
      ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x10 ↦ᵣ v10o) ** (.x11 ↦ᵣ v11o) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o) **
        (teerInnerOff ↦ₘ ioff))
      ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x5 ↦ᵣ teerInnerOff) ** (.x6 ↦ᵣ ioff) **
        (.x10 ↦ᵣ (v8 + ioff)) ** (.x11 ↦ᵣ (v9 - ioff)) **
        (.x21 ↦ᵣ (v8 + ioff)) ** (.x22 ↦ᵣ (v9 - ioff)) **
        (teerInnerOff ↦ₘ ioff)) := by
  have h0 := la_materialize_within .x5 v5 (teerB + 188) teerInnerOff (by decide) (by decide)
    (CodeReq.ofProg_mem_at teerB (teerB + 188) teerProg 47
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (teerB + 188) teerInnerOff))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
    (CodeReq.ofProg_mem_at teerB (teerB + 192) teerProg 48
      (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (teerB + 188) teerInnerOff))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
  have h1 := ld_spec_gen_within .x6 .x5 teerInnerOff v6 ioff (0 : BitVec 12) (teerB + 196) (by decide)
  have h2 := add_spec_gen_within .x21 .x8 .x6 v8 ioff v21o (teerB + 200) (by decide)
  have h3 := sub_spec_gen_within .x22 .x9 .x6 v9 ioff v22o (teerB + 204) (by decide)
  have h4 := mv_spec_gen_within .x10 .x21 (v8 + ioff) v10o (teerB + 208) (by decide)
  have h5 := mv_spec_gen_within .x11 .x22 (v9 - ioff) v11o (teerB + 212) (by decide)
  runBlock h0 h1 h2 h3 h4 h5

/-! ## Reusable `rlp_walk_init` call group

    `rlp_walk_init` is invoked three times in the prefix (instrs 54, 110, 176);
    this site-abstract lemma lifts the assumed `RlpWalkInitAssumed` contract
    through one `jal`, parameterised by the call PC `A`, the `jal` offset, and
    the membership / return-parity (`heven`) witnesses.  The cursor-init result
    (three-arm: short-list / long-list / parse-shape failure) is published into
    `a0`/`a1`/`a2`, with `t0..t2,t3..t6` owned.  The contract's exit is
    `ret &&& ~~~1`; with `ret := A + 4` (a 4-aligned return PC, `heven`) that is
    `A + 4`, matching `callWithin_spec`'s rigid return. -/
set_option maxRecDepth 8000 in
theorem teer_walkinit_call_spec_at (wi : RlpWalkInitAssumed fullCode)
    (A : Word) (off : BitVec 21)
    (htarget : A + signExtend21 off = wi.entry)
    (hmem : ∀ a i, CodeReq.singleton A (.JAL .x1 off) a = some i → fullCode a = some i)
    (heven : (A + 4) &&& ~~~(1 : Word) = A + 4)
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat)
    (halign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    cpsTripleWithin (1 + 81) A (A + 4) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes))
      ((.x1 ↦ᵣ (A + 4)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
              (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
              (.x12 ↦ᵣ (0 : Word))) h) ∨
           (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) +
                (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                  signExtend12 (1 : BitVec 12)))) **
              (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
              (.x12 ↦ᵣ (0 : Word))) h) ∨
           (∃ cur endp st : Word,
             (((.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endp) ** (.x12 ↦ᵣ st) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hflat := wi.flat (A + 4) listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old
    t6Old listBytes listOff halign hoff hover hvalid
  rw [heven] at hflat
  have hcallee : cpsTripleWithin 81 wi.entry (A + 4) fullCode
      ((.x1 ↦ᵣ (A + 4)) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes))
      ((.x1 ↦ᵣ (A + 4)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
              (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
              (.x12 ↦ᵣ (0 : Word))) h) ∨
           (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) +
                (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                  signExtend12 (1 : BitVec 12)))) **
              (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
              (.x12 ↦ᵣ (0 : Word))) h) ∨
           (∃ cur endp st : Word,
             (((.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endp) ** (.x12 ↦ᵣ st) ** ⌜st ≠ (0 : Word)⌝) h))))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hflat
  have hP : Assertion.pcFree ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
      (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ a2Old) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
      (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase listBytes) := by
    repeat' first
      | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
      | apply pcFree_sepConj
  exact callWithin_spec A wi.entry raIn off 81 htarget hmem hP hcallee

/-- **`rlp_walk_init`@54** (`teerB + 216 → teerB + 220`, the inner-payload
    to/value walk).  Thin instantiation of `teer_walkinit_call_spec_at`. -/
abbrev wiJalOff54 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_eip7702_existing_authority_refund + 216)

set_option maxRecDepth 8000 in
theorem teer_walkinit54_call_spec (wi : RlpWalkInitAssumed fullCode)
    (hwi : wi.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_init)
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat)
    (halign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    cpsTripleWithin (1 + 81) (teerB + 216) (teerB + 220) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes))
      ((.x1 ↦ᵣ (teerB + 220)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
              (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
              (.x12 ↦ᵣ (0 : Word))) h) ∨
           (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) +
                (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                  signExtend12 (1 : BitVec 12)))) **
              (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
              (.x12 ↦ᵣ (0 : Word))) h) ∨
           (∃ cur endp st : Word,
             (((.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endp) ** (.x12 ↦ᵣ st) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 216) (.JAL .x1 wiJalOff54) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 216) teerProg 54 (.JAL .x1 wiJalOff54)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walkinit_call_spec_at wi (teerB + 216) wiJalOff54
    (by rw [hwi]; decide) hmem (by decide)
    listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn listBytes listOff
    halign hoff hover hvalid
  rw [show (teerB + 216) + 4 = teerB + 220 from by bv_omega] at hres
  exact hres

/-! ## `to`/value walk GROUP — `rlp_walk_init` dispatch (instruction 55)

    `bne x12(a2), x0` at `teerB + 220`.  TAKEN (`a2 ≠ 0`, a parse-shape
    failure) exits to the far epilogue `teerB + 2856`; NOT-TAKEN (`a2 = 0`,
    cursor established) falls to `teerB + 224`, the first `rlp_walk_next` arg
    shuffle. -/
set_option maxRecDepth 8000 in
theorem teer_walkinit55_bne_spec (a2 : Word) :
    cpsBranchWithin 1 (teerB + 220) fullCode
      ((.x12 ↦ᵣ a2) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x12 ↦ᵣ a2) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a2 ≠ (0 : Word)⌝)
      (teerB + 224) ((.x12 ↦ᵣ a2) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a2 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x12 .x0 (2636 : BitVec 13) a2 (0 : Word) (teerB + 220)
  rw [show (teerB + 220) + signExtend13 (2636 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2636 : BitVec 13) = (2636 : Word) from by decide]; bv_omega,
      show (teerB + 220) + 4 = teerB + 224 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 220) teerProg 55
    (.BNE .x12 .x0 (2636 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

/-! ## Reusable `rlp_walk_next` call group

    Every `jal rlp_walk_next` in the prefix (and each per-auth iteration) has
    the identical framing shape; only the call site `A`, the `jal` offset, and
    the concrete-membership / return-parity facts differ.  This site-abstract
    lemma lifts the assumed `RlpWalkNextAssumed` contract through one `jal`;
    each site instantiates it with its own `A := teerB + <pc>`, `off`, and the
    three `by decide`/`ofProg` witnesses.  The advance result (a `rlpWalkNextOk`
    success arm or a non-advance status arm) is carried through unchanged; the
    following `bne a1, 0` dispatches on it. -/
set_option maxRecDepth 8000 in
theorem teer_walknext_call_spec_at (wn : RlpWalkNextAssumed fullCode)
    (A : Word) (off : BitVec 21)
    (htarget : A + signExtend21 off = wn.entry)
    (hmem : ∀ a i, CodeReq.singleton A (.JAL .x1 off) a = some i → fullCode a = some i)
    (heven : (A + 4) &&& ~~~(1 : Word) = A + 4)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin (1 + 87) A (A + 4) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (A + 4)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hflat := wn.flat (A + 4) srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old
    t6Old srcBytes srcOff halign hoff hover hvalid
  rw [heven] at hflat
  have hcallee : cpsTripleWithin 87 wn.entry (A + 4) fullCode
      ((.x1 ↦ᵣ (A + 4)) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (A + 4)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hflat
  have hP : Assertion.pcFree ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
      (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion srcBase srcBytes) := by
    repeat' first
      | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
      | apply pcFree_sepConj
  exact callWithin_spec A wn.entry raIn off 87 htarget hmem hP hcallee

/-! ## `to`/value walk GROUP — first `rlp_walk_next` (instruction 60)

    Instantiates `teer_walknext_call_spec_at` at the first walk site
    (`teerB + 240 → teerB + 244`, `jal rlp_walk_next` at instruction 60). -/
abbrev wnJalOff60 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 240)

set_option maxRecDepth 8000 in
theorem teer_walknext60_call_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin (1 + 87) (teerB + 240) (teerB + 244) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (teerB + 244)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 240) (.JAL .x1 wnJalOff60) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 240) teerProg 60 (.JAL .x1 wnJalOff60)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walknext_call_spec_at wn (teerB + 240) wnJalOff60
    (by rw [hwn]; decide) hmem (by decide)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    halign hoff hover hvalid
  rw [show (teerB + 240) + 4 = teerB + 244 from by bv_omega] at hres
  exact hres

/-! ## `to`/value walk GROUP — first `rlp_walk_next` dispatch (instruction 61)

    `bne x11(a1), x0` at `teerB + 244`.  TAKEN (`a1 ≠ 0`, a non-advance status
    ⇒ end-of-list / malformed) exits to the far epilogue `teerB + 2856`;
    NOT-TAKEN (`a1 = 0`, item advanced) falls to `teerB + 248`. -/
set_option maxRecDepth 8000 in
theorem teer_walknext61_bne_spec (a1 : Word) :
    cpsBranchWithin 1 (teerB + 244) fullCode
      ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 ≠ (0 : Word)⌝)
      (teerB + 248) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x11 .x0 (2612 : BitVec 13) a1 (0 : Word) (teerB + 244)
  rw [show (teerB + 244) + signExtend13 (2612 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2612 : BitVec 13) = (2612 : Word) from by decide]; bv_omega,
      show (teerB + 244) + 4 = teerB + 248 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 244) teerProg 61
    (.BNE .x11 .x0 (2612 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

/-! ## authorization-list `rlp_list_count_items` call (instruction 169)

    The `jal rlp_list_count_items` at `teerB + 676 → teerB + 680`.  Lifts the
    assumed `RlpListCountItemsAssumed` contract through the `jal` via
    `callWithin_spec`: `a0` = list ptr, `a1` = list length, `a2` =
    `&teer_auth_count`; on success `a0 = 0` and the count is written to the out
    cell (`countModel`); on failure `a0 ≠ 0`.  `t0..t2,t3..t6` owned.  Like
    `tx_type_dispatch`, the contract's pre already leads with `x1` and its exit
    is `ret` directly (via `_hret`). -/
abbrev rcJalOff169 : BitVec 21 :=
  jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.tx_eip7702_existing_authority_refund + 676)

set_option maxRecDepth 8000 in
theorem teer_count169_call_spec (rc : RlpListCountItemsAssumed fullCode)
    (hrc : rc.entry = BitVec.ofNat 64 GuestAddrs.rlp_list_count_items)
    (listBase outPtr outOld t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (listBytes : List (BitVec 8)) (listLen : Nat)
    (halign : listBase.toNat % 8 = 0)
    (hbound : listLen ≤ listBytes.length)
    (hover : listBase.toNat + listBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < listBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (1 + nRlpListCountItemsSteps) (teerB + 676) (teerB + 680) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLen) ** (.x12 ↦ᵣ outPtr) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes ** (outPtr ↦ₘ outOld)))
      ((.x1 ↦ᵣ (teerB + 680)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           (∃ cnt, rc.countModel listBytes listLen = some cnt ∧
             (((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ cnt)) h)) ∨
           (rc.countModel listBytes listLen = none ∧
             (∃ st, (((.x10 ↦ᵣ st) ** memOwn outPtr ** ⌜st ≠ (0 : Word)⌝) h)))))) := by
  have hflat := rc.flat (teerB + 680) listBase (BitVec.ofNat 64 listLen) outPtr outOld
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBytes listLen
    (by decide) rfl halign hbound hover hvalid
  have hcallee : cpsTripleWithin nRlpListCountItemsSteps rc.entry (teerB + 680) fullCode
      ((.x1 ↦ᵣ (teerB + 680)) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLen) ** (.x12 ↦ᵣ outPtr) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes ** (outPtr ↦ₘ outOld)))
      ((.x1 ↦ᵣ (teerB + 680)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           (∃ cnt, rc.countModel listBytes listLen = some cnt ∧
             (((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ cnt)) h)) ∨
           (rc.countModel listBytes listLen = none ∧
             (∃ st, (((.x10 ↦ᵣ st) ** memOwn outPtr ** ⌜st ≠ (0 : Word)⌝) h)))))) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by xperm_hyp hq) hflat
  have htarget : (teerB + 676) + signExtend21 rcJalOff169 = rc.entry := by rw [hrc]; decide
  have hmem : ∀ a i, CodeReq.singleton (teerB + 676) (.JAL .x1 rcJalOff169) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 676) teerProg 169 (.JAL .x1 rcJalOff169)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hP : Assertion.pcFree ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLen) **
      (.x12 ↦ᵣ outPtr) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
      (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase listBytes ** (outPtr ↦ₘ outOld)) := by
    repeat' first
      | exact pcFree_regIs | exact pcFree_memIs | exact bytesRegion_pcFree _ _
      | apply pcFree_sepConj
  have hcall := callWithin_spec (teerB + 676) rc.entry raIn rcJalOff169 nRlpListCountItemsSteps
    htarget hmem hP hcallee
  rw [show (teerB + 676) + 4 = teerB + 680 from by bv_omega] at hcall
  exact hcall

/-! ## authorization-list count dispatch (instruction 170)

    `bne x10(a0), x0` at `teerB + 680`.  TAKEN (`a0 ≠ 0`, count parse failure)
    exits to the far epilogue `teerB + 2856`; NOT-TAKEN (`a0 = 0`) falls to
    `teerB + 684`, the count load into `x23`. -/
set_option maxRecDepth 8000 in
theorem teer_count170_bne_spec (a0 : Word) :
    cpsBranchWithin 1 (teerB + 680) fullCode
      ((.x10 ↦ᵣ a0) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x10 ↦ᵣ a0) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a0 ≠ (0 : Word)⌝)
      (teerB + 684) ((.x10 ↦ᵣ a0) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a0 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x10 .x0 (2176 : BitVec 13) a0 (0 : Word) (teerB + 680)
  rw [show (teerB + 680) + signExtend13 (2176 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2176 : BitVec 13) = (2176 : Word) from by decide]; bv_omega,
      show (teerB + 680) + 4 = teerB + 684 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 680) teerProg 170
    (.BNE .x10 .x0 (2176 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

/-- **`rlp_walk_init`@110** (`teerB + 440 → teerB + 444`, the re-init of the
    inner-payload walk that descends to the authorization_list).  Thin
    instantiation of `teer_walkinit_call_spec_at`. -/
abbrev wiJalOff110 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_eip7702_existing_authority_refund + 440)

set_option maxRecDepth 8000 in
theorem teer_walkinit110_call_spec (wi : RlpWalkInitAssumed fullCode)
    (hwi : wi.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_init)
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat)
    (halign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    cpsTripleWithin (1 + 81) (teerB + 440) (teerB + 444) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes))
      ((.x1 ↦ᵣ (teerB + 444)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
              (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
              (.x12 ↦ᵣ (0 : Word))) h) ∨
           (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) +
                (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                  signExtend12 (1 : BitVec 12)))) **
              (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
              (.x12 ↦ᵣ (0 : Word))) h) ∨
           (∃ cur endp st : Word,
             (((.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endp) ** (.x12 ↦ᵣ st) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 440) (.JAL .x1 wiJalOff110) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 440) teerProg 110 (.JAL .x1 wiJalOff110)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walkinit_call_spec_at wi (teerB + 440) wiJalOff110
    (by rw [hwi]; decide) hmem (by decide)
    listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn listBytes listOff
    halign hoff hover hvalid
  rw [show (teerB + 440) + 4 = teerB + 444 from by bv_omega] at hres
  exact hres

/-! **`rlp_walk_init`@110 dispatch** (instruction 111, `teerB + 444`):
    `bne a2, 0` → far epilogue `teerB + 2856` (parse-shape fail) / fall to
    `teerB + 448`. -/
set_option maxRecDepth 8000 in
theorem teer_walkinit111_bne_spec (a2 : Word) :
    cpsBranchWithin 1 (teerB + 444) fullCode
      ((.x12 ↦ᵣ a2) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x12 ↦ᵣ a2) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a2 ≠ (0 : Word)⌝)
      (teerB + 448) ((.x12 ↦ᵣ a2) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a2 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x12 .x0 (2412 : BitVec 13) a2 (0 : Word) (teerB + 444)
  rw [show (teerB + 444) + signExtend13 (2412 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2412 : BitVec 13) = (2412 : Word) from by decide]; bv_omega,
      show (teerB + 444) + 4 = teerB + 448 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 444) teerProg 111
    (.BNE .x12 .x0 (2412 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

/-- **`rlp_walk_init`@176** (`teerB + 704 → teerB + 708`, the walk over the
    authorization_list itself, whose cursor/end seed the per-auth loop).  Thin
    instantiation of `teer_walkinit_call_spec_at`. -/
abbrev wiJalOff176 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_eip7702_existing_authority_refund + 704)

set_option maxRecDepth 8000 in
theorem teer_walkinit176_call_spec (wi : RlpWalkInitAssumed fullCode)
    (hwi : wi.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_init)
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat)
    (halign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    cpsTripleWithin (1 + 81) (teerB + 704) (teerB + 708) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes))
      ((.x1 ↦ᵣ (teerB + 708)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes) **
         (fun h =>
           (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
              (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
              (.x12 ↦ᵣ (0 : Word))) h) ∨
           (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) +
                (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                  signExtend12 (1 : BitVec 12)))) **
              (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
              (.x12 ↦ᵣ (0 : Word))) h) ∨
           (∃ cur endp st : Word,
             (((.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endp) ** (.x12 ↦ᵣ st) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 704) (.JAL .x1 wiJalOff176) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 704) teerProg 176 (.JAL .x1 wiJalOff176)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walkinit_call_spec_at wi (teerB + 704) wiJalOff176
    (by rw [hwi]; decide) hmem (by decide)
    listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn listBytes listOff
    halign hoff hover hvalid
  rw [show (teerB + 704) + 4 = teerB + 708 from by bv_omega] at hres
  exact hres

/-! **`rlp_walk_init`@176 dispatch** (instruction 177, `teerB + 708`):
    `bne a2, 0` → far epilogue `teerB + 2856` (parse-shape fail) / fall to
    `teerB + 712`, the loop counter/cursor init (`teer_loop_init_spec`). -/
set_option maxRecDepth 8000 in
theorem teer_walkinit177_bne_spec (a2 : Word) :
    cpsBranchWithin 1 (teerB + 708) fullCode
      ((.x12 ↦ᵣ a2) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x12 ↦ᵣ a2) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a2 ≠ (0 : Word)⌝)
      (teerB + 712) ((.x12 ↦ᵣ a2) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a2 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x12 .x0 (2148 : BitVec 13) a2 (0 : Word) (teerB + 708)
  rw [show (teerB + 708) + signExtend13 (2148 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2148 : BitVec 13) = (2148 : Word) from by decide]; bv_omega,
      show (teerB + 708) + 4 = teerB + 712 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 708) teerProg 177
    (.BNE .x12 .x0 (2148 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

/-! ## `to` field capture (instructions 87..96)

    After the 6th `rlp_walk_next` (the `to` field) returns `a0`(x10) = content
    end and `a2`(x12) = content length, record the recipient content pointer
    `x30 = a0 - a2` into `teer_recipient_ptr` and the length into
    `teer_recipient_len`, then stage `a0`/`a1` for the next `rlp_walk_next`
    (past `to`).  Exit `teerB + 388`.  Over `teerCode` (call-free). -/
set_option maxRecDepth 8000 in
theorem teer_recipient_capture_spec (v10 v11o v12 v25 v30o v5o v24o rpo rlo : Word) :
    cpsTripleWithin 10 (teerB + 348) (teerB + 388) teerCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11o) ** (.x12 ↦ᵣ v12) ** (.x25 ↦ᵣ v25) **
        (.x30 ↦ᵣ v30o) ** (.x5 ↦ᵣ v5o) ** (.x24 ↦ᵣ v24o) **
        (teerRecipientPtr ↦ₘ rpo) ** (teerRecipientLen ↦ₘ rlo))
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v25) ** (.x12 ↦ᵣ v12) ** (.x25 ↦ᵣ v25) **
        (.x30 ↦ᵣ (v10 - v12)) ** (.x5 ↦ᵣ teerRecipientLen) ** (.x24 ↦ᵣ v10) **
        (teerRecipientPtr ↦ₘ (v10 - v12)) ** (teerRecipientLen ↦ₘ v12)) := by
  have h0 := sub_spec_gen_within .x30 .x10 .x12 v10 v12 v30o (teerB + 348) (by decide)
  have h1 := la_materialize_within .x5 v5o (teerB + 352) teerRecipientPtr (by decide) (by decide)
    (CodeReq.ofProg_mem_at teerB (teerB + 352) teerProg 88
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (teerB + 352) teerRecipientPtr))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
    (CodeReq.ofProg_mem_at teerB (teerB + 356) teerProg 89
      (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (teerB + 352) teerRecipientPtr))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
  have h2 := sd_spec_gen_within .x5 .x30 teerRecipientPtr (v10 - v12) rpo (0 : BitVec 12)
    (teerB + 360)
  have h3 := la_materialize_within .x5 teerRecipientPtr (teerB + 364) teerRecipientLen
    (by decide) (by decide)
    (CodeReq.ofProg_mem_at teerB (teerB + 364) teerProg 91
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (teerB + 364) teerRecipientLen))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
    (CodeReq.ofProg_mem_at teerB (teerB + 368) teerProg 92
      (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (teerB + 364) teerRecipientLen))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
  have h4 := sd_spec_gen_within .x5 .x12 teerRecipientLen v12 rlo (0 : BitVec 12) (teerB + 372)
  have h5 := mv_spec_gen_within .x24 .x10 v10 v24o (teerB + 376) (by decide)
  have h6 := mv_spec_gen_within .x10 .x24 v10 v10 (teerB + 380) (by decide)
  have h7 := mv_spec_gen_within .x11 .x25 v25 v11o (teerB + 384) (by decide)
  runBlock h0 h1 h2 h3 h4 h5 h6 h7

/-! ## `value ≠ 0` flag (instructions 99..102)

    After the 7th `rlp_walk_next` (past `to`, the `value` field), set
    `teer_value_nonzero = (value content length > 0)` via `sltu x30, x0, a2`.
    Exit `teerB + 412`.  Over `teerCode` (call-free). -/
set_option maxRecDepth 8000 in
theorem teer_value_nonzero_spec (v12 v30o v5o vno : Word) :
    cpsTripleWithin 4 (teerB + 396) (teerB + 412) teerCode
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12) ** (.x30 ↦ᵣ v30o) ** (.x5 ↦ᵣ v5o) **
        (teerValueNonzero ↦ₘ vno))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12) **
        (.x30 ↦ᵣ (if BitVec.ult (0 : Word) v12 then (1 : Word) else 0)) **
        (.x5 ↦ᵣ teerValueNonzero) **
        (teerValueNonzero ↦ₘ (if BitVec.ult (0 : Word) v12 then (1 : Word) else 0))) := by
  have h0 := sltu_spec_gen_within .x30 .x0 .x12 v30o (0 : Word) v12 (teerB + 396) (by decide)
  have h1 := la_materialize_within .x5 v5o (teerB + 400) teerValueNonzero (by decide) (by decide)
    (CodeReq.ofProg_mem_at teerB (teerB + 400) teerProg 100
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (teerB + 400) teerValueNonzero))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
    (CodeReq.ofProg_mem_at teerB (teerB + 404) teerProg 101
      (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (teerB + 400) teerValueNonzero))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
  have h2 := sd_spec_gen_within .x5 .x30 teerValueNonzero
    (if BitVec.ult (0 : Word) v12 then (1 : Word) else 0) vno (0 : BitVec 12) (teerB + 408)
  runBlock h0 h1 h2

/-! ## authorization-list content ptr/len + count out setup (instructions 163..168)

    After the 10th authorization-list `rlp_walk_next` returns `a0`(x10) = list
    content end and `a2`(x12) = content length, compute the content pointer
    `x21 = a0 - a2` and length `x22 = a2`, stage them into `a0`/`a1`, and
    materialise `&teer_auth_count` into `a2`(x12) for the count call.  Exit
    `teerB + 676`, the `jal rlp_list_count_items` at instruction 169.  Over
    `teerCode` (call-free). -/
set_option maxRecDepth 8000 in
theorem teer_authlist_setup_spec (v10 v11o v12 v21o v22o : Word) :
    cpsTripleWithin 6 (teerB + 652) (teerB + 676) teerCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11o) ** (.x12 ↦ᵣ v12) ** (.x21 ↦ᵣ v21o) **
        (.x22 ↦ᵣ v22o))
      ((.x10 ↦ᵣ (v10 - v12)) ** (.x11 ↦ᵣ v12) ** (.x12 ↦ᵣ teerAuthCount) **
        (.x21 ↦ᵣ (v10 - v12)) ** (.x22 ↦ᵣ v12)) := by
  have h0 := sub_spec_gen_within .x21 .x10 .x12 v10 v12 v21o (teerB + 652) (by decide)
  have h1 := mv_spec_gen_within .x22 .x12 v12 v22o (teerB + 656) (by decide)
  have h2 := mv_spec_gen_within .x10 .x21 (v10 - v12) v10 (teerB + 660) (by decide)
  have h3 := mv_spec_gen_within .x11 .x22 v12 v11o (teerB + 664) (by decide)
  have h4 := la_materialize_within .x12 v12 (teerB + 668) teerAuthCount (by decide) (by decide)
    (CodeReq.ofProg_mem_at teerB (teerB + 668) teerProg 167
      (.AUIPC .x12 (EvmAsm.Rv64.laHi (teerB + 668) teerAuthCount))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
    (CodeReq.ofProg_mem_at teerB (teerB + 672) teerProg 168
      (.ADDI .x12 .x12 (EvmAsm.Rv64.laLo (teerB + 668) teerAuthCount))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
  runBlock h0 h1 h2 h3 h4

/-! ## count load + list re-init setup (instructions 171..175)

    On the count-success fall-through (`teerB + 684`), load `teer_auth_count`
    into the callee-saved counter `x23` and stage the list content ptr/len
    (`x21`/`x22`, captured at instr 163) into `a0`/`a1` for the list-walk
    `rlp_walk_init` at instruction 176.  Exit `teerB + 704`.  Over `teerCode`. -/
set_option maxRecDepth 8000 in
theorem teer_countload_setup_spec (v21 v22 v5o v23o v10o v11o cnt : Word) :
    cpsTripleWithin 5 (teerB + 684) (teerB + 704) teerCode
      ((.x5 ↦ᵣ v5o) ** (.x23 ↦ᵣ v23o) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        (.x10 ↦ᵣ v10o) ** (.x11 ↦ᵣ v11o) ** (teerAuthCount ↦ₘ cnt))
      ((.x5 ↦ᵣ teerAuthCount) ** (.x23 ↦ᵣ cnt) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        (.x10 ↦ᵣ v21) ** (.x11 ↦ᵣ v22) ** (teerAuthCount ↦ₘ cnt)) := by
  have h0 := la_materialize_within .x5 v5o (teerB + 684) teerAuthCount (by decide) (by decide)
    (CodeReq.ofProg_mem_at teerB (teerB + 684) teerProg 171
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (teerB + 684) teerAuthCount))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
    (CodeReq.ofProg_mem_at teerB (teerB + 688) teerProg 172
      (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (teerB + 684) teerAuthCount))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
  have h1 := ld_spec_gen_within .x23 .x5 teerAuthCount v23o cnt (0 : BitVec 12) (teerB + 692)
    (by decide)
  have h2 := mv_spec_gen_within .x10 .x21 v21 v10o (teerB + 696) (by decide)
  have h3 := mv_spec_gen_within .x11 .x22 v22 v11o (teerB + 700) (by decide)
  runBlock h0 h1 h2 h3

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
