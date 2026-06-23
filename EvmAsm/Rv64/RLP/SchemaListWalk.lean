/-
  EvmAsm.Rv64.RLP.SchemaListWalk

  EL.3 / Phase 5 — the RLP-LIST schema decoder: descend one list level to its payload, then run
  the N-field fold over the element fields. This is the shape every real STF structure takes —
  a transaction / block header is an RLP list whose elements are the fields.

  `unified_list_header_descend` (the "descend one list level to its payload" primitive) leaves
  `x13` at the payload pointer and clobbers the scratch registers; its post has exactly the same
  atom order as `schema_walk`'s `schemaINV` precondition, so bridging it is a positional
  scratch weaken (concrete → `regOwn`) plus an `x13`-pointer rewrite (`hptr` gives the payload
  offset from the list prefix). The output region is framed through the descend. The result:
  decode a list-structured schema into one shared output `bytesRegion`, coinciding field-by-field
  with the RLP spec (`schemaDecodes`).
-/

import EvmAsm.Rv64.RLP.SchemaFold
import EvmAsm.Rv64.RLP.UnifiedListDescendConcrete

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000 in
/-- **List schema decode.** From `x13 = regionBase + ofNat O` pointing at a `.list` value (window
    `hwindow0`), whose payload begins at offset `O'` (`hptr`), descend the list header then decode
    the element fields `specs` (any scalar/byte-array mix) into the output region. -/
theorem list_schema_walk
    (base regionBase outBase : Word) (rOut : Reg) (bs : List Byte) (O O' : Nat) (hO : O < bs.length)
    (specs : List FieldSpec) (out : List Byte) (outLen : Nat)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hwindow0 : regionLongWindow regionBase bs O hO)
    (hptr : itemPtrRegion (bs[O]'hO) regionBase O = regionBase + BitVec.ofNat 64 O')
    (hdalign : outBase.toNat % 8 = 0)
    (hlen : out.length = outLen)
    (hdov : outBase.toNat + outLen < 2 ^ 64)
    (hdval : ∀ i, i < outLen → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hvalid : SchemaValid bs outLen O' specs)
    (hcode : base.toNat + (148 + schemaSize specs) < 2 ^ 64) :
    cpsTripleWithin (61 + schemaSteps specs) base
        ((base + 148) + BitVec.ofNat 64 (schemaSize specs))
      (((CodeReq.singleton base (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
        (schemaCR (base + 148) rOut specs))
      (((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
        (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase out))
      (schemaINV regionBase outBase rOut bs (O' + schemaEnc specs) (schemaOut out specs))
    ∧ schemaDecodes bs O' specs := by
  have hb148 : (base + 148).toNat = base.toNat + 148 := by bv_omega
  -- Descend the list header (61 steps, base .. base+148), framing the output region through it.
  have t_desc := cpsTripleWithin_frameR ((rOut ↦ᵣ outBase) ** bytesRegion outBase out)
    (by exact pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _))
    (unified_list_header_descend base regionBase bs O hO v5Old v10 v11Old v12Old v14Old v15Old
      halign hover (hwin O hO) hwindow0)
  rw [hptr] at t_desc
  -- Weaken the descend's clobbered scratch (concrete) to the canonical `regOwn` interface.
  have t_desc' : cpsTripleWithin 61 base (base + 148)
      ((CodeReq.singleton base (.LBU .x5 .x13 0)).union (CodeReq.ofProg (base + 4) unified_decoder_prog))
      (((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
        (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase out))
      (schemaINV regionBase outBase rOut bs O' out) :=
    cpsTripleWithin_weaken (fun _ h => h)
      (fun _ hp => sepConj_mono_left
        (sepConj_mono (regIs_implies_regOwn .x5)
          (sepConj_mono_right
            (sepConj_mono (regIs_implies_regOwn .x10)
              (sepConj_mono (regIs_implies_regOwn .x11)
                (sepConj_mono (regIs_implies_regOwn .x12)
                  (sepConj_mono_right
                    (sepConj_mono (regIs_implies_regOwn .x14)
                      (sepConj_mono_left (regIs_implies_regOwn .x15))))))))) _ hp)
      t_desc
  -- The field fold at base+148, offset O'.
  have hsw := schema_walk regionBase outBase rOut bs halign hover hwin hdalign outLen hdov hdval
    specs (base + 148) O' out hlen hvalid (by rw [hb148]; omega)
  -- Disjointness: descend code (base .. base+148) ⊥ schema code (base+148 ..).
  have hd : ((CodeReq.singleton base (.LBU .x5 .x13 0)).union
        (CodeReq.ofProg (base + 4) unified_decoder_prog)).Disjoint
      (schemaCR (base + 148) rOut specs) := by
    refine codeReq_disjoint_of_ranges _ _ (base + 148).toNat ?_ ?_
    · intro a ha
      have h1 : CodeReq.singleton base (.LBU .x5 .x13 0) a = none :=
        CodeReq.singleton_miss (by bv_omega)
      have h2 : CodeReq.ofProg (base + 4) unified_decoder_prog a = none :=
        CodeReq.ofProg_none_range_len _ _ 36 a unified_decoder_prog_length (fun k hk => by bv_omega)
      simp only [CodeReq.union, h1, h2]
    · intro a ha
      exact schemaCR_none_below rOut specs (base + 148) a (by rw [hb148]; omega) ha
  refine ⟨?_, hsw.2⟩
  exact cpsTripleWithin_seq hd t_desc' hsw.1

end EvmAsm.Rv64.RLP
