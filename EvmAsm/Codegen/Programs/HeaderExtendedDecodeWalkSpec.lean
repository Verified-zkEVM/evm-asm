import EvmAsm.Codegen.Programs.HeaderDecode
import EvmAsm.Codegen.Programs.RlpWalkCallSAsm
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.HeaderExtendedDecodeWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

/-!
  Exact linked-site contracts for the outer walker calls in
  header_extended_decode.  The leaf proof is supplied by the caller while this
  file fixes each call PC and target.  The explicit by-decide offset proof is a
  drift alarm: a moved or retargeted JAL breaks the site contract loudly.
-/

abbrev decoderBase : Word := (GuestAddrs.header_extended_decode : Word)
abbrev walkInitBase : Word := (GuestAddrs.rlp_walk_init : Word)
abbrev walkNextBase : Word := (GuestAddrs.rlp_walk_next : Word)

theorem walk_next_site
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (callPC calleeEntry oldRa : Word) (offset : BitVec 21)
    (hpre : Prest.pcFree)
    (hoffset : callPC + signExtend21 offset = calleeEntry)
    (halign : (callPC + 4) &&& ~~~(1 : Word) = callPC + 4)
    (hdisj : (CodeReq.singleton callPC (.JAL .x1 offset)).Disjoint
      (rlp_walk_next_code calleeEntry))
    (hcode : ∀ a i,
      (CodeReq.singleton callPC (.JAL .x1 offset)).union
        (rlp_walk_next_code calleeEntry) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n calleeEntry ((callPC + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code calleeEntry)
      ((.x1 ↦ᵣ (callPC + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) callPC (callPC + 4) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  exact EvmAsm.Codegen.RlpWalkCallSAsm.rlp_walk_next_call_within
    callPC calleeEntry oldRa offset hpre hoffset halign hdisj hcode hcallee

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_init_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 32) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_init
          (GuestAddrs.header_extended_decode + 32)))).union
        (rlp_walk_init_code walkInitBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkInitBase
      (((decoderBase + 32) + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code walkInitBase)
      ((.x1 ↦ᵣ ((decoderBase + 32) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 32) (decoderBase + 36) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := EvmAsm.Codegen.RlpWalkCallSAsm.rlp_walk_init_call_within
    (decoderBase + 32) walkInitBase oldRa
    (jalOff GuestAddrs.rlp_walk_init
      (GuestAddrs.header_extended_decode + 32)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 32) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_init : Word) rlp_walk_init_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkInitBase, BitVec.add_assoc] using h

/-! A uniform skip segment between two walker calls.  On entry `x10` is the
    cursor returned by the preceding call and `x11` is its status.  The
    segment saves the cursor, branches nonzero status to the common failure
    epilogue, and on the zero arm reloads the cursor/end pair for the next
    call.  Keeping the branch and both register moves in one parameterised
    contract makes the changing meanings of `x11` explicit at this boundary.
-/

def walkNextSkipCode (base : Word) (bneOff : BitVec 13) : CodeReq :=
  (CodeReq.singleton base (.MV .x19 .x10)).union
    ((CodeReq.singleton (base + 4) (.BNE .x11 .x0 bneOff)).union
      ((CodeReq.singleton (base + 8) (.MV .x10 .x19)).union
        (CodeReq.singleton (base + 12) (.MV .x11 .x9))))

set_option maxRecDepth 8000 in
theorem walk_next_skip_segment
    {cr : CodeReq}
    (base failPC : Word) (bneOff : BitVec 13)
    (cursor status endPtr oldRa : Word) (F : Assertion) (hF : F.pcFree)
    (hoff : base + 4 + signExtend13 bneOff = failPC)
    (hcode0 : ∀ a i,
      CodeReq.singleton base (.MV .x19 .x10) a = some i → cr a = some i)
    (hcode1 : ∀ a i,
      CodeReq.singleton (base + 4) (.BNE .x11 .x0 bneOff) a = some i → cr a = some i)
    (hcode2 : ∀ a i,
      CodeReq.singleton (base + 8) (.MV .x10 .x19) a = some i → cr a = some i)
    (hcode3 : ∀ a i,
      CodeReq.singleton (base + 12) (.MV .x11 .x9) a = some i → cr a = some i) :
    cpsBranchWithin 4 base cr
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr) **
        (.x19 ↦ᵣ oldRa) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      (base + 16)
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x9 ↦ᵣ endPtr) **
        (.x19 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      failPC
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr) **
        (.x19 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  have hmv0 := mv_spec_gen_within .x19 .x10 cursor oldRa base (by decide)
  have hmv0' := cpsTripleWithin_extend_code
    hcode0 hmv0
  have hmv0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr) ** (.x0 ↦ᵣ (0 : Word)) ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact hF) hmv0'
  have hmv0P : cpsTripleWithin 1 base (base + 4) cr
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr) **
        (.x19 ↦ᵣ oldRa) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr) **
        (.x19 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
    refine cpsTripleWithin_weaken
      (P := (((.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ oldRa)) **
        (.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr) ** (.x0 ↦ᵣ (0 : Word)) ** F))
      (P' := ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr) **
        (.x19 ↦ᵣ oldRa) ** (.x0 ↦ᵣ (0 : Word)) ** F))
      (Q := (((.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ cursor)) **
        (.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr) ** (.x0 ↦ᵣ (0 : Word)) ** F))
      (Q' := ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr) **
        (.x19 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word)) ** F))
      (by intro _ hp; xperm_chunked hp) (by intro _ hp; xperm_chunked hp) hmv0F
  have hbne := bne_spec_gen_within .x11 .x0 bneOff status (0 : Word) (base + 4)
  rw [hoff, show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hbne
  have hbne' := cpsBranchWithin_extend_code
    hcode1 hbne
  have hbneF := cpsBranchWithin_frameR
    ((.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ cursor) ** (.x9 ↦ᵣ endPtr) ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact hF) hbne'
  have hmv1 := mv_spec_gen_within .x10 .x19 cursor cursor (base + 8) (by decide)
  have hmv1' := cpsTripleWithin_extend_code
    hcode2 hmv1
  have hmv1F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr) ** (.x0 ↦ᵣ (0 : Word)) ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact hF) hmv1'
  have hmv2 := mv_spec_gen_within .x11 .x9 endPtr status (base + 12) (by decide)
  have hmv2' := cpsTripleWithin_extend_code
    hcode3 hmv2
  have hmv2F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word)) ** F)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact hF) hmv2'
  have hmv1F0 : cpsTripleWithin 1 (base + 8) (base + 12) cr
      (((.x19 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) **
        (.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      (((.x19 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) **
        (.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
    simpa [BitVec.add_assoc] using hmv1F
  have hmv1B : cpsTripleWithin 1 (base + 8) (base + 12) cr
      (((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜status = 0⌝) **
        (.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ cursor) ** (.x9 ↦ᵣ endPtr) ** F)
      (((.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr)) **
        (.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
    refine cpsTripleWithin_weaken
      (P := (((.x19 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) **
        (.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr) ** (.x0 ↦ᵣ (0 : Word)) ** F))
      (P' := (((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜status = 0⌝) **
        (.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ cursor) ** (.x9 ↦ᵣ endPtr) ** F))
      (Q := (((.x19 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) **
        (.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr) ** (.x0 ↦ᵣ (0 : Word)) ** F))
      (Q' := (((.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr)) **
        (.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word)) ** F))
      (by
        intro h hp
        have hp1 :
            ((((.x19 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) **
              (.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr) ** (.x0 ↦ᵣ (0 : Word)) ** F) **
              ⌜status = 0⌝) h := by
          xperm_chunked hp
        exact ((sepConj_pure_right h).1 hp1).1)
      (by intro _ hp; xperm_chunked hp)
      hmv1F0
  have hmv2B : cpsTripleWithin 1 (base + 12) (base + 12 + 4) cr
      (((.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr)) **
        (.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      (((.x9 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) **
        (.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
    refine cpsTripleWithin_weaken
      (P := (((.x9 ↦ᵣ endPtr) ** (.x11 ↦ᵣ status)) **
        (.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word)) ** F))
      (P' := (((.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr)) **
        (.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word)) ** F))
      (Q := (((.x9 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) **
        (.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word)) ** F))
      (Q' := (((.x9 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) **
        (.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word)) ** F))
      (by intro _ hp; xperm_chunked hp) (by intro _ hp; exact hp)
      hmv2F
  have htail0 := cpsTripleWithin_seq_same_cr hmv1B hmv2B
  have htail : cpsTripleWithin 2 (base + 8) (base + 16) cr
      (((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜status = 0⌝) **
        (.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ cursor) ** (.x9 ↦ᵣ endPtr) ** F)
      (((.x9 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) **
        (.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
    simpa [BitVec.add_assoc] using htail0
  have hbranch := cpsBranchWithin_seq_cpsTripleWithin_taken_same_cr
    (cpsBranchWithin_swap hbneF) htail
  have hbranch' : cpsBranchWithin 3 (base + 4) cr
      (((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) **
        (.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ cursor) ** (.x9 ↦ᵣ endPtr) ** F)
      (base + 16)
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x9 ↦ᵣ endPtr) **
        (.x19 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      failPC
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr) **
        (.x19 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
    refine cpsBranchWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by xperm_chunked hp)
      (fun h hp => by
        have hp1 :
            (((.x10 ↦ᵣ cursor) ** (.x19 ↦ᵣ cursor) ** (.x9 ↦ᵣ endPtr) ** F **
              (.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) **
              ⌜status ≠ 0⌝) h := by
          xperm_chunked hp
        have hp2 := ((sepConj_pure_right h).1 hp1).1
        xperm_chunked hp2)
      hbranch
  have hfull := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hmv0P hbranch'
  simpa [Nat.add_assoc] using hfull

/-- The successful (`c = 0`) arm of a skip segment is the precondition of the
    next walker call.  This adapter composes that arm while retaining the
    original status-failure epilogue.  The two bounds are intentionally kept
    separate: `4` is the local skip segment and `n` is the callee contract. -/
theorem walk_next_skip_then_next_call
    {cr : CodeReq} {P S Sf Q : Assertion} {n : Nat}
    (base nextPC exitPC failPC : Word)
    (hskip : cpsBranchWithin 4 base cr P nextPC S failPC Sf)
    (hnext : cpsTripleWithin n nextPC exitPC cr S Q) :
    cpsBranchWithin (4 + n) base cr P exitPC Q failPC Sf := by
  exact cpsBranchWithin_seq_cpsTripleWithin_taken_same_cr hskip hnext

/-! The first uniform linked segment is the four instructions at `+124`:
    save cursor, reject nonzero status, and reload cursor/end for the call at
    `+140`.  The call contract is supplied by the corresponding site theorem;
    spelling the concrete PCs here keeps the link and the failure target
    checked at the composition boundary. -/
set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_skip_field1_then_next
    {cr : CodeReq} {F Q : Assertion} {n : Nat}
    (cursor status endPtr savedCursor returnRa : Word) (hF : F.pcFree)
    (hcode0 : ∀ a i,
      CodeReq.singleton (decoderBase + 124) (.MV .x19 .x10) a = some i →
        cr a = some i)
    (hcode1 : ∀ a i,
      CodeReq.singleton (decoderBase + 128)
        (.BNE .x11 .x0 (0x218 : BitVec 13)) a = some i →
        cr a = some i)
    (hcode2 : ∀ a i,
      CodeReq.singleton (decoderBase + 132) (.MV .x10 .x19) a = some i →
        cr a = some i)
    (hcode3 : ∀ a i,
      CodeReq.singleton (decoderBase + 136) (.MV .x11 .x9) a = some i →
        cr a = some i)
    (hnext : cpsTripleWithin n (decoderBase + 140) (decoderBase + 144) cr
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x9 ↦ᵣ endPtr) **
        (.x19 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ returnRa) ** F)
      Q) :
    cpsBranchWithin (4 + n) (decoderBase + 124) cr
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr) **
        (.x19 ↦ᵣ savedCursor) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ returnRa) ** F)
      (decoderBase + 144) Q
      (decoderBase + 664)
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ status) ** (.x9 ↦ᵣ endPtr) **
        (.x19 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ returnRa) ** F) := by
  have hFseg : ((.x1 ↦ᵣ returnRa) ** F).pcFree :=
    pcFree_sepConj (P := (.x1 ↦ᵣ returnRa)) (Q := F)
      (pcFree_regIs (r := .x1) (v := returnRa)) hF
  have hseg := walk_next_skip_segment (cr := cr)
    (decoderBase + 124) (decoderBase + 664) (0x218 : BitVec 13)
    cursor status endPtr savedCursor ((.x1 ↦ᵣ returnRa) ** F)
    hFseg (by decide)
    hcode0 hcode1 hcode2 hcode3
  exact walk_next_skip_then_next_call
    (decoderBase + 124) (decoderBase + 140) (decoderBase + 144)
    (decoderBase + 664) hseg hnext

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_next_field0_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 56) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_next
          (GuestAddrs.header_extended_decode + 56)))).union
        (rlp_walk_next_code walkNextBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkNextBase
      (((decoderBase + 56) + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code walkNextBase)
      ((.x1 ↦ᵣ ((decoderBase + 56) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 56) (decoderBase + 60) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := walk_next_site (decoderBase + 56) walkNextBase oldRa
    (jalOff GuestAddrs.rlp_walk_next
      (GuestAddrs.header_extended_decode + 56)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 56) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_next : Word) rlp_walk_next_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkNextBase, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_next_field1_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 120) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_next
          (GuestAddrs.header_extended_decode + 120)))).union
        (rlp_walk_next_code walkNextBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkNextBase
      (((decoderBase + 120) + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code walkNextBase)
      ((.x1 ↦ᵣ ((decoderBase + 120) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 120) (decoderBase + 124) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := walk_next_site (decoderBase + 120) walkNextBase oldRa
    (jalOff GuestAddrs.rlp_walk_next
      (GuestAddrs.header_extended_decode + 120)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 120) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_next : Word) rlp_walk_next_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkNextBase, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_next_field2_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 140) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_next
          (GuestAddrs.header_extended_decode + 140)))).union
        (rlp_walk_next_code walkNextBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkNextBase
      (((decoderBase + 140) + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code walkNextBase)
      ((.x1 ↦ᵣ ((decoderBase + 140) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 140) (decoderBase + 144) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := walk_next_site (decoderBase + 140) walkNextBase oldRa
    (jalOff GuestAddrs.rlp_walk_next
      (GuestAddrs.header_extended_decode + 140)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 140) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_next : Word) rlp_walk_next_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkNextBase, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_next_field3_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 160) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_next
          (GuestAddrs.header_extended_decode + 160)))).union
        (rlp_walk_next_code walkNextBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkNextBase
      (((decoderBase + 160) + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code walkNextBase)
      ((.x1 ↦ᵣ ((decoderBase + 160) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 160) (decoderBase + 164) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := walk_next_site (decoderBase + 160) walkNextBase oldRa
    (jalOff GuestAddrs.rlp_walk_next
      (GuestAddrs.header_extended_decode + 160)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 160) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_next : Word) rlp_walk_next_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkNextBase, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_next_field4_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 224) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_next
          (GuestAddrs.header_extended_decode + 224)))).union
        (rlp_walk_next_code walkNextBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkNextBase
      (((decoderBase + 224) + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code walkNextBase)
      ((.x1 ↦ᵣ ((decoderBase + 224) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 224) (decoderBase + 228) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := walk_next_site (decoderBase + 224) walkNextBase oldRa
    (jalOff GuestAddrs.rlp_walk_next
      (GuestAddrs.header_extended_decode + 224)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 224) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_next : Word) rlp_walk_next_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkNextBase, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_next_field5_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 244) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_next
          (GuestAddrs.header_extended_decode + 244)))).union
        (rlp_walk_next_code walkNextBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkNextBase
      (((decoderBase + 244) + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code walkNextBase)
      ((.x1 ↦ᵣ ((decoderBase + 244) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 244) (decoderBase + 248) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := walk_next_site (decoderBase + 244) walkNextBase oldRa
    (jalOff GuestAddrs.rlp_walk_next
      (GuestAddrs.header_extended_decode + 244)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 244) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_next : Word) rlp_walk_next_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkNextBase, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_next_field6_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 264) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_next
          (GuestAddrs.header_extended_decode + 264)))).union
        (rlp_walk_next_code walkNextBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkNextBase
      (((decoderBase + 264) + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code walkNextBase)
      ((.x1 ↦ᵣ ((decoderBase + 264) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 264) (decoderBase + 268) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := walk_next_site (decoderBase + 264) walkNextBase oldRa
    (jalOff GuestAddrs.rlp_walk_next
      (GuestAddrs.header_extended_decode + 264)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 264) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_next : Word) rlp_walk_next_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkNextBase, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_next_field7_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 284) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_next
          (GuestAddrs.header_extended_decode + 284)))).union
        (rlp_walk_next_code walkNextBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkNextBase
      (((decoderBase + 284) + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code walkNextBase)
      ((.x1 ↦ᵣ ((decoderBase + 284) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 284) (decoderBase + 288) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := walk_next_site (decoderBase + 284) walkNextBase oldRa
    (jalOff GuestAddrs.rlp_walk_next
      (GuestAddrs.header_extended_decode + 284)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 284) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_next : Word) rlp_walk_next_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkNextBase, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_next_field8_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 304) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_next
          (GuestAddrs.header_extended_decode + 304)))).union
        (rlp_walk_next_code walkNextBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkNextBase
      (((decoderBase + 304) + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code walkNextBase)
      ((.x1 ↦ᵣ ((decoderBase + 304) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 304) (decoderBase + 308) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := walk_next_site (decoderBase + 304) walkNextBase oldRa
    (jalOff GuestAddrs.rlp_walk_next
      (GuestAddrs.header_extended_decode + 304)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 304) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_next : Word) rlp_walk_next_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkNextBase, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_next_field9_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 344) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_next
          (GuestAddrs.header_extended_decode + 344)))).union
        (rlp_walk_next_code walkNextBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkNextBase
      (((decoderBase + 344) + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code walkNextBase)
      ((.x1 ↦ᵣ ((decoderBase + 344) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 344) (decoderBase + 348) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := walk_next_site (decoderBase + 344) walkNextBase oldRa
    (jalOff GuestAddrs.rlp_walk_next
      (GuestAddrs.header_extended_decode + 344)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 344) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_next : Word) rlp_walk_next_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkNextBase, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_next_field10_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 384) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_next
          (GuestAddrs.header_extended_decode + 384)))).union
        (rlp_walk_next_code walkNextBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkNextBase
      (((decoderBase + 384) + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code walkNextBase)
      ((.x1 ↦ᵣ ((decoderBase + 384) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 384) (decoderBase + 388) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := walk_next_site (decoderBase + 384) walkNextBase oldRa
    (jalOff GuestAddrs.rlp_walk_next
      (GuestAddrs.header_extended_decode + 384)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 384) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_next : Word) rlp_walk_next_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkNextBase, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_next_field11_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 424) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_next
          (GuestAddrs.header_extended_decode + 424)))).union
        (rlp_walk_next_code walkNextBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkNextBase
      (((decoderBase + 424) + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code walkNextBase)
      ((.x1 ↦ᵣ ((decoderBase + 424) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 424) (decoderBase + 428) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := walk_next_site (decoderBase + 424) walkNextBase oldRa
    (jalOff GuestAddrs.rlp_walk_next
      (GuestAddrs.header_extended_decode + 424)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 424) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_next : Word) rlp_walk_next_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkNextBase, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_next_field12_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 464) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_next
          (GuestAddrs.header_extended_decode + 464)))).union
        (rlp_walk_next_code walkNextBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkNextBase
      (((decoderBase + 464) + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code walkNextBase)
      ((.x1 ↦ᵣ ((decoderBase + 464) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 464) (decoderBase + 468) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := walk_next_site (decoderBase + 464) walkNextBase oldRa
    (jalOff GuestAddrs.rlp_walk_next
      (GuestAddrs.header_extended_decode + 464)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 464) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_next : Word) rlp_walk_next_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkNextBase, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_next_field13_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 484) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_next
          (GuestAddrs.header_extended_decode + 484)))).union
        (rlp_walk_next_code walkNextBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkNextBase
      (((decoderBase + 484) + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code walkNextBase)
      ((.x1 ↦ᵣ ((decoderBase + 484) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 484) (decoderBase + 488) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := walk_next_site (decoderBase + 484) walkNextBase oldRa
    (jalOff GuestAddrs.rlp_walk_next
      (GuestAddrs.header_extended_decode + 484)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 484) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_next : Word) rlp_walk_next_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkNextBase, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_next_field14_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 504) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_next
          (GuestAddrs.header_extended_decode + 504)))).union
        (rlp_walk_next_code walkNextBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkNextBase
      (((decoderBase + 504) + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code walkNextBase)
      ((.x1 ↦ᵣ ((decoderBase + 504) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 504) (decoderBase + 508) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := walk_next_site (decoderBase + 504) walkNextBase oldRa
    (jalOff GuestAddrs.rlp_walk_next
      (GuestAddrs.header_extended_decode + 504)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 504) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_next : Word) rlp_walk_next_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkNextBase, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_next_field15_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 524) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_next
          (GuestAddrs.header_extended_decode + 524)))).union
        (rlp_walk_next_code walkNextBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkNextBase
      (((decoderBase + 524) + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code walkNextBase)
      ((.x1 ↦ᵣ ((decoderBase + 524) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 524) (decoderBase + 528) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := walk_next_site (decoderBase + 524) walkNextBase oldRa
    (jalOff GuestAddrs.rlp_walk_next
      (GuestAddrs.header_extended_decode + 524)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 524) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_next : Word) rlp_walk_next_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkNextBase, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_next_field16_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 564) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_next
          (GuestAddrs.header_extended_decode + 564)))).union
        (rlp_walk_next_code walkNextBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkNextBase
      (((decoderBase + 564) + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code walkNextBase)
      ((.x1 ↦ᵣ ((decoderBase + 564) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 564) (decoderBase + 568) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := walk_next_site (decoderBase + 564) walkNextBase oldRa
    (jalOff GuestAddrs.rlp_walk_next
      (GuestAddrs.header_extended_decode + 564)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 564) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_next : Word) rlp_walk_next_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkNextBase, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_next_field17_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 584) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_next
          (GuestAddrs.header_extended_decode + 584)))).union
        (rlp_walk_next_code walkNextBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkNextBase
      (((decoderBase + 584) + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code walkNextBase)
      ((.x1 ↦ᵣ ((decoderBase + 584) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 584) (decoderBase + 588) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := walk_next_site (decoderBase + 584) walkNextBase oldRa
    (jalOff GuestAddrs.rlp_walk_next
      (GuestAddrs.header_extended_decode + 584)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 584) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_next : Word) rlp_walk_next_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkNextBase, BitVec.add_assoc] using h

set_option maxRecDepth 8000 in
theorem header_extended_decode_walk_next_field18_spec_within
    {cr : CodeReq} {Prest Q : Assertion} {n : Nat}
    (oldRa : Word) (hpre : Prest.pcFree)
    (hcode : ∀ a i,
      (CodeReq.singleton (decoderBase + 624) (.JAL .x1
        (jalOff GuestAddrs.rlp_walk_next
          (GuestAddrs.header_extended_decode + 624)))).union
        (rlp_walk_next_code walkNextBase) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n walkNextBase
      (((decoderBase + 624) + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code walkNextBase)
      ((.x1 ↦ᵣ ((decoderBase + 624) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (decoderBase + 624) (decoderBase + 628) cr
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h := walk_next_site (decoderBase + 624) walkNextBase oldRa
    (jalOff GuestAddrs.rlp_walk_next
      (GuestAddrs.header_extended_decode + 624)) hpre
    (by decide)
    (by decide)
    (by
      change (CodeReq.singleton (decoderBase + 624) _).Disjoint
        (CodeReq.ofProg (GuestAddrs.rlp_walk_next : Word) rlp_walk_next_prog)
      exact CodeReq.Disjoint.singleton_ofProg (by decide))
    hcode hcallee
  simpa [decoderBase, walkNextBase, BitVec.add_assoc] using h

end EvmAsm.Codegen.HeaderExtendedDecodeWalkSpec
