/-
  EvmAsm.Rv64.RLP.WithdrawalDecodeShortWP

  First composed withdrawal-decoder WP layer: run the walk-init classifier with
  schema handoff resources, then continue the short-list success exit through
  the generated withdrawal schema success tail.  Other exits stay open for the
  failure/long-list layers.
-/

import EvmAsm.Rv64.RLP.WithdrawalSchemaWP

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

namespace WithdrawalDecode

theorem walkInitEmptyFailNotListFailShortLongCode_none_above
    (base a : Word) (h : base.toNat + 172 ≤ a.toNat) :
    walkInitEmptyFailNotListFailShortLongCode base a = none := by
  unfold walkInitEmptyFailNotListFailShortLongCode walkInitEmptyFailOrPrefixCode
    walkInitEmptyFailStatusCode failStatusReturnCode statusReturnCode
    walkInitNonzeroPrefixTailCode walkInitPrefixShortLongTailCode
    walkInitPrefixListCheckNotListFailF8Code walkInitPrefixListCheckOrNotListFailCode
    walkInitPrefixListCheckCode walkInitPrefixNotListFailStatusCode walkInitListF8Code
    walkInitShortLongCheckCode
  have h0 : CodeReq.singleton base (.BEQ .x11 .x0 (156 : BitVec 13)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h156 : CodeReq.singleton (base + 156) (.LI .x10 (1 : Word)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h160 : CodeReq.singleton (base + 156 + 4) (.JALR .x0 .x1 (0 : BitVec 12)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h4 : CodeReq.singleton (base + 4) (.ADD .x11 .x10 .x11) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h8 : CodeReq.singleton (base + 8) (.LBU .x5 .x10 0) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h12 : CodeReq.singleton (base + 12) (.LI .x6 (0xc0 : Word)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h16 : CodeReq.singleton (base + 16) (.BLTU .x5 .x6 (148 : BitVec 13)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h164 : CodeReq.singleton (base + 164) (.LI .x10 (1 : Word)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h168 : CodeReq.singleton (base + 164 + 4) (.JALR .x0 .x1 (0 : BitVec 12)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h20 : CodeReq.singleton (base + 20) (.LI .x6 (0xf8 : Word)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h24 : CodeReq.singleton (base + 24) (.BLTU .x5 .x6 (100 : BitVec 13)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  simp only [failStatusReturnCode, statusReturnCode, CodeReq.union,
    h0, h156, h160, h4, h8, h12, h16, h164, h168, h20, h24]

theorem walkInitEmptyFailNotListFailShortLongCode_none_at_shortSuccessJump
    (base : Word) :
    walkInitEmptyFailNotListFailShortLongCode base (base + 124) = none := by
  unfold walkInitEmptyFailNotListFailShortLongCode walkInitEmptyFailOrPrefixCode
    walkInitEmptyFailStatusCode failStatusReturnCode statusReturnCode
    walkInitNonzeroPrefixTailCode walkInitPrefixShortLongTailCode
    walkInitPrefixListCheckNotListFailF8Code walkInitPrefixListCheckOrNotListFailCode
    walkInitPrefixListCheckCode walkInitPrefixNotListFailStatusCode walkInitListF8Code
    walkInitShortLongCheckCode
  have h0 : CodeReq.singleton base (.BEQ .x11 .x0 (156 : BitVec 13)) (base + 124) = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h156 : CodeReq.singleton (base + 156) (.LI .x10 (1 : Word)) (base + 124) = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h160 : CodeReq.singleton (base + 156 + 4) (.JALR .x0 .x1 (0 : BitVec 12)) (base + 124) = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h4 : CodeReq.singleton (base + 4) (.ADD .x11 .x10 .x11) (base + 124) = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h8 : CodeReq.singleton (base + 8) (.LBU .x5 .x10 0) (base + 124) = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h12 : CodeReq.singleton (base + 12) (.LI .x6 (0xc0 : Word)) (base + 124) = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h16 : CodeReq.singleton (base + 16) (.BLTU .x5 .x6 (148 : BitVec 13)) (base + 124) = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h164 : CodeReq.singleton (base + 164) (.LI .x10 (1 : Word)) (base + 124) = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h168 : CodeReq.singleton (base + 164 + 4) (.JALR .x0 .x1 (0 : BitVec 12)) (base + 124) = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h20 : CodeReq.singleton (base + 20) (.LI .x6 (0xf8 : Word)) (base + 124) = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h24 : CodeReq.singleton (base + 24) (.BLTU .x5 .x6 (100 : BitVec 13)) (base + 124) = none :=
    CodeReq.singleton_miss (by bv_omega)
  simp only [failStatusReturnCode, statusReturnCode, CodeReq.union,
    h0, h156, h160, h4, h8, h12, h16, h164, h168, h20, h24]

theorem walkInitEmptyFailNotListFailShortLongCode_disjoint_shortSuccessJump
    (base : Word) :
    (walkInitEmptyFailNotListFailShortLongCode base).Disjoint
      (walkInitShortSuccessJumpCode base) := by
  intro a
  by_cases h_eq : a = base + 124
  · left
    subst h_eq
    exact walkInitEmptyFailNotListFailShortLongCode_none_at_shortSuccessJump base
  · right
    unfold walkInitShortSuccessJumpCode
    exact CodeReq.singleton_miss h_eq

theorem walkInitEmptyFailNotListFailShortLongCode_disjoint_schemaTail
    (base : Word) (specs : List FieldSpec)
    (hcode : base.toNat + 172 + 4 + schemaSize specs + 8 < 2 ^ 64) :
    (walkInitEmptyFailNotListFailShortLongCode base).Disjoint
      ((schemaCursorInitCode (base + 172)).union
        ((schemaCR (base + 172 + 4) .x8 specs).union
          (successStatusReturnCode
            ((base + 172 + 4) + BitVec.ofNat 64 (schemaSize specs))))) := by
  have hbase172 : (base + 172).toNat = base.toNat + 172 := by
    bv_omega
  refine codeReq_disjoint_of_ranges _ _ (base.toNat + 172) ?_ ?_
  · intro a ha
    exact walkInitEmptyFailNotListFailShortLongCode_none_above base a ha
  · intro a ha
    exact schemaCursorInitSuccessReturnTail_none_below (base + 172) .x8 specs a
      (by rw [hbase172]; omega) (by rw [hbase172]; exact ha)

theorem walkInitEmptyFailNotListFailShortLongCode_disjoint_shortSuccessTail
    (base : Word) (specs : List FieldSpec)
    (hcode : base.toNat + 172 + 4 + schemaSize specs + 8 < 2 ^ 64) :
    (walkInitEmptyFailNotListFailShortLongCode base).Disjoint
      ((walkInitShortSuccessJumpCode base).union
        ((schemaCursorInitCode (base + 172)).union
          ((schemaCR (base + 172 + 4) .x8 specs).union
            (successStatusReturnCode
              ((base + 172 + 4) + BitVec.ofNat 64 (schemaSize specs)))))) := by
  exact CodeReq.Disjoint.union_right
    (walkInitEmptyFailNotListFailShortLongCode_disjoint_shortSuccessJump base)
    (walkInitEmptyFailNotListFailShortLongCode_disjoint_schemaTail base specs hcode)

attribute [rv64_wp_disjoint]
  walkInitEmptyFailNotListFailShortLongCode_disjoint_shortSuccessTail

theorem walkInitSchemaFrameNBranch_exits
    (base inputBase listLen raVal t0Old t1Old outBase : Word)
    (input : List Byte) (hoff : 0 < input.length)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover0 : inputBase.toNat + 0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (inputBase + BitVec.ofNat 64 0) = true) :
    (walkInitEmptyFailNotListFailShortLongFramedNBranch base inputBase listLen raVal
      t0Old t1Old input 0 hsalign hoff hover0 hvalid0
      (schemaWalkInitFrame outBase) (schemaWalkInitFrame_pcFree outBase)).exits =
      [ (failStatusReturnExit raVal,
          (walkInitEmptyFailStatusPost listLen raVal **
            ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion inputBase input)) **
            schemaWalkInitFrame outBase)
      , (failStatusReturnExit raVal,
          walkInitPrefixNotListFailStatusPost inputBase listLen raVal input 0 hoff **
            schemaWalkInitFrame outBase)
      , (base + 124,
          walkInitShortListCandidatePost inputBase listLen raVal input 0 hoff **
            schemaWalkInitFrame outBase)
      , (base + 28,
          walkInitLongListCandidatePost inputBase listLen raVal input 0 hoff **
            schemaWalkInitFrame outBase)
      ] := by
  simp [walkInitEmptyFailNotListFailShortLongFramedNBranch,
    walkInitEmptyFailNotListFailShortLongNBranch,
    walkInitEmptyFailOrPrefixBranch, walkInitPrefixListCheckOrNotListFailBranch,
    walkInitEmptyFailStatusBranch, walkInitPrefixListCheckBranch,
    walkInitShortLongCheckBranch, walkInitEmptyFailStatusPost,
    failStatusReturnExit, statusReturnExit, WP.CFG.nbranchFrameR, WP.NBranch.frameR,
    WP.CFG.branchFrameR, WP.Branch.frameR, WP.CFG.branchSeqNotTakenNBranchDisjoint,
    WP.Branch.seqNotTakenNBranchDisjoint, WP.CFG.branchSeqNotTakenBlockDisjoint,
    WP.CFG.branchSeqTakenBlockDisjoint, WP.CFG.branchSeqNotTakenDisjoint,
    WP.CFG.branchSeqTakenDisjoint, WP.Branch.seqNotTakenDisjoint,
    WP.Branch.seqTakenDisjoint, WP.CFG.nbranchOfBranch, WP.NBranch.ofBranch,
    WP.Branch.ofSpec, WP.CFG.block, WP.Triple.ofSpec]

/-- Walk-init classifier with the short-list success exit continued through the
    generated withdrawal schema success tail. Empty, not-list, and long-list
    exits remain explicit for later failure/long-list automation. -/
def walkInitShortSuccessSchemaNBranch
    (base inputBase listLen raVal t0Old t1Old outBase : Word)
    (input d0 d1 d2 d3 : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : ∀ i, i < input.length → isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (hcode : base.toNat + 172 + 4 + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    WP.NBranch base
      ((walkInitEmptyFailNotListFailShortLongCode base).union
        ((walkInitShortSuccessJumpCode base).union
          ((schemaCursorInitCode (base + 172)).union
            ((schemaCR (base + 172 + 4) .x8 (successFieldSpecs d0 d1 d2 d3)).union
              (successStatusReturnCode
                ((base + 172 + 4) + BitVec.ofNat 64
                  (schemaSize (successFieldSpecs d0 d1 d2 d3)))))))) := by
  have hover0 : inputBase.toNat + 0 < 2 ^ 64 := by
    omega
  have hvalid0 : isValidByteAccess (inputBase + BitVec.ofNat 64 0) = true :=
    hwin 0 hoff
  let br := walkInitEmptyFailNotListFailShortLongFramedNBranch base inputBase listLen raVal
    t0Old t1Old input 0 hsalign hoff hover0 hvalid0
    (schemaWalkInitFrame outBase) (schemaWalkInitFrame_pcFree outBase)
  let tailCert := successFieldSpecsReturnAbiCertOfInputFromWalkShortExit base inputBase outBase
    raVal input d0 d1 d2 d3 hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput hsalign hdalign hover
    hwin hdov hdval hcode
  let F := schemaWalkInitFrame outBase
  let emptyPost : Assertion :=
    (walkInitEmptyFailStatusPost listLen raVal **
      ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion inputBase input)) ** F
  let notListPost : Assertion :=
    walkInitPrefixNotListFailStatusPost inputBase listLen raVal input 0 hoff ** F
  let shortPost : Assertion :=
    walkInitShortListCandidatePost inputBase listLen raVal input 0 hoff ** F
  let longPost : Assertion :=
    walkInitLongListCandidatePost inputBase listLen raVal input 0 hoff ** F
  have hexits : br.exits =
      [(failStatusReturnExit raVal, emptyPost),
        (failStatusReturnExit raVal, notListPost),
        (base + 124, shortPost),
        (base + 28, longPost)] := by
    dsimp [br, F, emptyPost, notListPost, shortPost, longPost]
    rw [walkInitSchemaFrameNBranch_exits]
    rfl
  wp_rv64_nbranch_third_cert_auto br, hexits, tailCert

theorem walkInitShortSuccessSchemaNBranch_pre
    (base inputBase listLen raVal t0Old t1Old outBase : Word)
    (input d0 d1 d2 d3 : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : ∀ i, i < input.length → isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (hcode : base.toNat + 172 + 4 + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    (walkInitShortSuccessSchemaNBranch base inputBase listLen raVal t0Old t1Old outBase input
      d0 d1 d2 d3 hsalign hoff hover hwin hdalign hdov hdval hc0 hl0 hc1 hl1 haddr hc3
      hl3 hinput hcode).pre =
      ((walkInitEmptyFailStatusPre listLen raVal (inputBase + BitVec.ofNat 64 0) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion inputBase input) **
        schemaWalkInitFrame outBase) := by
  unfold walkInitShortSuccessSchemaNBranch
  rfl

end WithdrawalDecode

end EvmAsm.Rv64.RLP
