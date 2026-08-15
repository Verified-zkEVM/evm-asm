import EvmAsm.Codegen.Programs.HeaderDecode
import EvmAsm.Codegen.Programs.RlpWalkCallSAsm

namespace EvmAsm.Codegen.HeaderExtendedDecodeWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

/-!
  Exact linked-site contracts for the outer walker calls in
  header_extended_decode.  The leaf proof is supplied by the caller while this
  file fixes each call PC and target.  The explicit by-decide offset proof is a
  drift alarm: a moved or retargeted JAL breaks the site contract loudly.
-/

abbrev decoderBase : Word := (GuestAddrs.header_extended_decode : Word)
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

