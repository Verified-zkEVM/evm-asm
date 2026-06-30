/-
  EvmAsm.Rv64.RLP.WithdrawalDecode

  WP-facing specification facade for an RV64 `withdrawal_decode` routine.
  The static schema below intentionally contains only field positions and output
  layout.  It does not contain decoded bytes or values; those are introduced only
  by the postcondition, through the pure `EvmAsm.EL.decodeWithdrawal` function.
-/

import EvmAsm.Rv64.WP
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.WP
import EvmAsm.Rv64.Tactics.ExtractPure
import EvmAsm.Rv64.RLP.WalkDecodeBridge
import EvmAsm.Rv64.RLP.WalkInitWP
import EvmAsm.EL.Withdrawal

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL
open EvmAsm.EL.RLP

namespace WithdrawalDecode

/-! ## Static ABI layout -/

/-- Field kind for the fixed EIP-4895 withdrawal schema.  This is static
    layout/control information, not a decoded value. -/
inductive FieldKind where
  | scalarU64
  | address20
  deriving DecidableEq, Repr

/-- One static field of `rlp([index, validator_index, address, amount])`.
    The schema records only where to read a field from and where to write it in
    the ABI output struct. -/
structure FieldLayout where
  inputIndex : Nat
  outputOffset : Nat
  kind : FieldKind
  deriving DecidableEq, Repr

/-- Output struct size used by the codegen ABI: 48 bytes. -/
def outputSize : Nat := 48

/-- Static schema for the ABI output struct:
    `index@0`, `validator_index@8`, `address@16`, `amount@40`. -/
def schema : List FieldLayout :=
  [ { inputIndex := 0, outputOffset := 0,  kind := .scalarU64 }
  , { inputIndex := 1, outputOffset := 8,  kind := .scalarU64 }
  , { inputIndex := 2, outputOffset := 16, kind := .address20 }
  , { inputIndex := 3, outputOffset := 40, kind := .scalarU64 }
  ]

theorem schema_length : schema.length = 4 := rfl

/-! ## Concrete program blocks -/

/-- The 32-byte stack frame base after the withdrawal decoder prologue. -/
def prologueFrameBase (sp0 : Word) : Word :=
  sp0 + signExtend12 (-32 : BitVec 12)

/-- Prologue block: allocate a 32-byte frame, save `ra`/`s0`/`s1`/`s2`,
    and copy the output-struct pointer from `a2` to `s0`. -/
def prologue : List Instr :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12)
  , .SD .x2 .x1 (0 : BitVec 12)
  , .SD .x2 .x8 (8 : BitVec 12)
  , .SD .x2 .x9 (16 : BitVec 12)
  , .SD .x2 .x18 (24 : BitVec 12)
  , .MV .x8 .x12
  ]

theorem prologue_length : prologue.length = 6 := rfl

/-- Code requirement for the withdrawal decoder prologue rooted at `base`. -/
def prologueCode (base : Word) : CodeReq :=
  CodeReq.ofProg base prologue

/-- Machine precondition for the prologue. The four memory cells are the
    caller-owned stack slots that become the saved frame. -/
def prologuePre (sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word) : Assertion :=
  ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
    (.x18 ↦ᵣ s2Old) ** (.x12 ↦ᵣ outBase) **
    (prologueFrameBase sp0 ↦ₘ m0) **
    ((prologueFrameBase sp0 + 8) ↦ₘ m1) **
    ((prologueFrameBase sp0 + 16) ↦ₘ m2) **
    ((prologueFrameBase sp0 + 24) ↦ₘ m3))

/-- Machine postcondition for the prologue. `s0` now owns the output pointer,
    `sp` points at the new frame, and the caller-save values are spilled. -/
def prologuePost (sp0 raVal s0Old s1Old s2Old outBase : Word) : Assertion :=
  ((.x2 ↦ᵣ prologueFrameBase sp0) ** (.x1 ↦ᵣ raVal) **
    (.x8 ↦ᵣ outBase) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) ** (.x12 ↦ᵣ outBase) **
    (prologueFrameBase sp0 ↦ₘ raVal) **
    ((prologueFrameBase sp0 + 8) ↦ₘ s0Old) **
    ((prologueFrameBase sp0 + 16) ↦ₘ s1Old) **
    ((prologueFrameBase sp0 + 24) ↦ₘ s2Old))

/-- Verified prologue block, packaged in the same CPS contract as the rest of
    the RV64 instruction specs. -/
theorem prologue_spec_within
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word) :
    cpsTripleWithin 6 base (base + 24) (prologueCode base)
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3)
      (prologuePost sp0 raVal s0Old s1Old s2Old outBase) := by
  unfold prologuePre prologuePost prologueFrameBase
  have hadd := addi_spec_gen_same_within .x2 sp0 (-32 : BitVec 12) base (by decide)
  have hsd0 := sd_spec_gen_within .x2 .x1 (sp0 + signExtend12 (-32 : BitVec 12)) raVal m0
    (0 : BitVec 12) (base + 4)
  have hsd1 := sd_spec_gen_within .x2 .x8 (sp0 + signExtend12 (-32 : BitVec 12)) s0Old m1
    (8 : BitVec 12) (base + 8)
  have hsd2 := sd_spec_gen_within .x2 .x9 (sp0 + signExtend12 (-32 : BitVec 12)) s1Old m2
    (16 : BitVec 12) (base + 12)
  have hsd3 := sd_spec_gen_within .x2 .x18 (sp0 + signExtend12 (-32 : BitVec 12)) s2Old m3
    (24 : BitVec 12) (base + 16)
  have hmv := mv_spec_gen_within .x8 .x12 outBase s0Old (base + 20) (by decide)
  simp only [signExtend12_0] at hsd0
  runBlock hadd hsd0 hsd1 hsd2 hsd3 hmv

/-- WP certificate for the concrete prologue. Later proof-producing code can
    compose this certificate directly instead of replaying the instruction proof. -/
def prologueCert (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word) :
    WP.CFG.Cert base (base + 24) (prologueCode base)
      (prologuePost sp0 raVal s0Old s1Old s2Old outBase) :=
  WP.CFG.block (WP.Entails.refl _)
    (prologue_spec_within base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3)

/-! ## Status return endpoints -/

/-- Small status-return block: set `a0` to `status` and return through `ra`. -/
def statusReturn (status : Word) : List Instr :=
  [ .LI .x10 status
  , .JALR .x0 .x1 (0 : BitVec 12)
  ]

theorem statusReturn_length (status : Word) : (statusReturn status).length = 2 := rfl

/-- Code requirement for a status-return block rooted at `base`.  WP certificates
    keep code as a disjoint union of instruction fetches; `statusReturn` remains
    the executable list shape. -/
def statusReturnCode (base status : Word) : CodeReq :=
  (CodeReq.singleton base (.LI .x10 status)).union
    (CodeReq.singleton (base + 4) (.JALR .x0 .x1 (0 : BitVec 12)))

/-- Return PC used by a status-return block, exactly matching `JALR x0, ra, 0`. -/
def statusReturnExit (raVal : Word) : Word :=
  (raVal + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)

/-- Internal precondition for a status-return block. -/
def statusReturnPre (raVal statusOld : Word) : Assertion :=
  ((.x1 ↦ᵣ raVal) ** (.x10 ↦ᵣ statusOld))

/-- Internal postcondition for a status-return block. -/
def statusReturnPost (raVal status : Word) : Assertion :=
  ((.x1 ↦ᵣ raVal) ** (.x10 ↦ᵣ status))

/-- WP certificate for a status-return block. -/
def statusReturnCert (base raVal statusOld status : Word) :
    WP.CFG.Cert base (statusReturnExit raVal) (statusReturnCode base status)
      (statusReturnPost raVal status) := by
  unfold statusReturnPost statusReturnExit statusReturnCode
  have hli0 := li_spec_gen_within .x10 statusOld status base (by decide)
  have hli := cpsTripleWithin_frameL (.x1 ↦ᵣ raVal) (by pcFree) hli0
  have hret0 := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 4)
  have hret := cpsTripleWithin_frameR (.x10 ↦ᵣ status) (by pcFree) hret0
  exact WP.CFG.seqBlockDisjoint
    (CodeReq.Disjoint.singleton (by bv_omega))
    hli
    hret
    (by wp_rv64_link)

/-- Verified status-return block. -/
theorem statusReturn_spec_within (base raVal statusOld status : Word) :
    cpsTripleWithin (statusReturnCert base raVal statusOld status).nSteps base
      (statusReturnExit raVal) (statusReturnCode base status)
      (statusReturnPre raVal statusOld)
      (statusReturnPost raVal status) :=
  by
    unfold statusReturnPre
    exact (statusReturnCert base raVal statusOld status).sound

/-- Reason-erased failure return block: set status `1` and return. -/
def failStatusReturn : List Instr :=
  statusReturn (1 : Word)

theorem failStatusReturn_length : failStatusReturn.length = 2 := rfl

def failStatusReturnCode (base : Word) : CodeReq :=
  statusReturnCode base (1 : Word)

def failStatusReturnExit (raVal : Word) : Word :=
  statusReturnExit raVal

def failStatusReturnPre (raVal statusOld : Word) : Assertion :=
  statusReturnPre raVal statusOld

def failStatusReturnPost (raVal : Word) : Assertion :=
  statusReturnPost raVal (1 : Word)

def failStatusReturnCert (base raVal statusOld : Word) :
    WP.CFG.Cert base (failStatusReturnExit raVal) (failStatusReturnCode base)
      (failStatusReturnPost raVal) :=
  statusReturnCert base raVal statusOld (1 : Word)

/-- Verified reason-erased failure return block. -/
theorem failStatusReturn_spec_within
    (base raVal statusOld : Word) :
    cpsTripleWithin (failStatusReturnCert base raVal statusOld).nSteps base
      (failStatusReturnExit raVal) (failStatusReturnCode base)
      (failStatusReturnPre raVal statusOld)
      (failStatusReturnPost raVal) :=
  statusReturn_spec_within base raVal statusOld (1 : Word)

/-- Success return block: set status `0` and return. -/
def successStatusReturn : List Instr :=
  statusReturn (0 : Word)

theorem successStatusReturn_length : successStatusReturn.length = 2 := rfl

def successStatusReturnCode (base : Word) : CodeReq :=
  statusReturnCode base (0 : Word)

def successStatusReturnExit (raVal : Word) : Word :=
  statusReturnExit raVal

def successStatusReturnPre (raVal statusOld : Word) : Assertion :=
  statusReturnPre raVal statusOld

def successStatusReturnPost (raVal : Word) : Assertion :=
  statusReturnPost raVal (0 : Word)

def successStatusReturnCert (base raVal statusOld : Word) :
    WP.CFG.Cert base (successStatusReturnExit raVal) (successStatusReturnCode base)
      (successStatusReturnPost raVal) :=
  statusReturnCert base raVal statusOld (0 : Word)

/-- Verified success return block. -/
theorem successStatusReturn_spec_within
    (base raVal statusOld : Word) :
    cpsTripleWithin (successStatusReturnCert base raVal statusOld).nSteps base
      (successStatusReturnExit raVal) (successStatusReturnCode base)
      (successStatusReturnPre raVal statusOld)
      (successStatusReturnPost raVal) :=
  statusReturn_spec_within base raVal statusOld (0 : Word)

/-! ## Walk-init branch endpoint composition -/

/-- Code for the first `rlp_walk_init` branch plus the reason-erased failure
    endpoint placed at the branch's empty-input target. -/
def walkInitEmptyFailStatusCode (base : Word) : CodeReq :=
  (CodeReq.singleton base (.BEQ .x11 .x0 (156 : BitVec 13))).union
    (failStatusReturnCode (base + 156))

/-- Precondition for the first walk-init branch while carrying just enough
    status-return state to service the empty-input arm. -/
def walkInitEmptyFailStatusPre (listLen raVal statusOld : Word) : Assertion :=
  walkInitZeroNonzeroPre listLen ** failStatusReturnPre raVal statusOld

/-- Empty-input arm after it has run the reason-erased failure status endpoint. -/
def walkInitEmptyFailStatusPost (listLen raVal : Word) : Assertion :=
  failStatusReturnPost raVal ** walkInitZeroPost listLen

/-- Nonempty-input arm, left open for the real decoder continuation. -/
def walkInitNonzeroOpenStatusPost (listLen raVal statusOld : Word) : Assertion :=
  walkInitNonzeroPost listLen ** failStatusReturnPre raVal statusOld

/-- WP branch certificate for the first `rlp_walk_init` split, with the
    empty-input arm already continued through the shared failure-status endpoint
    and the nonzero arm left as a branch exit. -/
def walkInitEmptyFailStatusBranch (base listLen raVal statusOld : Word) :
    WP.Branch base (walkInitEmptyFailStatusCode base) := by
  let br0 : WP.Branch base (CodeReq.singleton base (.BEQ .x11 .x0 (156 : BitVec 13))) :=
    WP.Branch.ofSpec (walkInitZeroNonzeroBranch_singleton_spec base listLen)
  let br := WP.CFG.branchFrameR br0 (failStatusReturnPre raVal statusOld) (by
    unfold failStatusReturnPre statusReturnPre
    pcFree)
  have htail0 := failStatusReturn_spec_within (base + 156) raVal statusOld
  have htail := cpsTripleWithin_frameR (walkInitZeroPost listLen) (by
    unfold walkInitZeroPost
    pcFree) htail0
  unfold walkInitEmptyFailStatusCode failStatusReturnCode
  exact WP.CFG.branchSeqTakenBlockDisjoint
    (CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega)))
    br
    htail
    (by
      intro h hp
      dsimp [br, WP.CFG.branchFrameR, WP.Branch.frameR] at hp
      xperm_hyp hp)

theorem walkInitEmptyFailStatusBranch_pre
    (base listLen raVal statusOld : Word) :
    (walkInitEmptyFailStatusBranch base listLen raVal statusOld).pre =
      walkInitEmptyFailStatusPre listLen raVal statusOld := by
  rfl

theorem walkInitEmptyFailStatusBranch_taken_post
    (base listLen raVal statusOld : Word) :
    (walkInitEmptyFailStatusBranch base listLen raVal statusOld).post_t =
      walkInitEmptyFailStatusPost listLen raVal := by
  rfl

theorem walkInitEmptyFailStatusBranch_notTaken_post
    (base listLen raVal statusOld : Word) :
    (walkInitEmptyFailStatusBranch base listLen raVal statusOld).post_f =
      walkInitNonzeroOpenStatusPost listLen raVal statusOld := by
  rfl

/-- Fall-through prefix tail after the initial zero/nonzero split:
    `ADD x11,x10,x11; LBU x5,x10,0; LI x6,0xc0`. -/
def walkInitNonzeroPrefixTailCode (base : Word) : CodeReq :=
  (CodeReq.singleton (base + 4) (.ADD .x11 .x10 .x11)).union
    ((CodeReq.singleton (base + 8) (.LBU .x5 .x10 0)).union
      (CodeReq.singleton (base + 12) (.LI .x6 (0xc0 : Word))))

/-- Code for the empty-input failure arm plus the nonzero prefix tail. -/
def walkInitEmptyFailOrPrefixCode (base : Word) : CodeReq :=
  (walkInitEmptyFailStatusCode base).union (walkInitNonzeroPrefixTailCode base)

/-- State after the nonzero walk-init prefix tail has loaded the RLP prefix byte
    and initialized the `0xc0` list threshold. -/
def walkInitPrefixLoadedPost
    (listBase listLen raVal : Word) (listBytes : List Byte)
    (listOff : Nat) (hoff : listOff < listBytes.length) : Assertion :=
  ((.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
    (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
    (.x5 ↦ᵣ ((listBytes[listOff]'hoff).zeroExtend 64)) **
    (.x6 ↦ᵣ (0xc0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
    bytesRegion listBase listBytes ** ⌜listLen ≠ (0 : Word)⌝)

theorem walkInitNonzeroPrefixTail_spec_within
    (base listBase listLen raVal t0Old t1Old : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    cpsTripleWithin 3 (base + 4) (base + 16) (walkInitNonzeroPrefixTailCode base)
      ((walkInitNonzeroOpenStatusPost listLen raVal (listBase + BitVec.ofNat 64 listOff)) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion listBase listBytes)
      (walkInitPrefixLoadedPost listBase listLen raVal listBytes listOff hoff) := by
  unfold walkInitNonzeroOpenStatusPost walkInitNonzeroPost failStatusReturnPre
    statusReturnPre walkInitPrefixLoadedPost walkInitNonzeroPrefixTailCode
  have hadd := add_spec_gen_rd_eq_rs2_within .x11 .x10
    (listBase + BitVec.ofNat 64 listOff) listLen (base + 4) (by decide)
  have hlbu := bytesRegion_lbu_within .x5 .x10 listBase t0Old (base + 8)
    listBytes listOff (by decide) hsalign hoff hover hvalid
  have hli := li_spec_gen_within .x6 t1Old (0xc0 : Word) (base + 12) (by decide)
  have hblk : cpsTripleWithin 3 (base + 4) (base + 16)
      ((CodeReq.singleton (base + 4) (.ADD .x11 .x10 .x11)).union
        ((CodeReq.singleton (base + 8) (.LBU .x5 .x10 0)).union
          (CodeReq.singleton (base + 12) (.LI .x6 (0xc0 : Word)))))
      ((.x11 ↦ᵣ listLen) ** (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes)
      ((.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
        (.x5 ↦ᵣ ((listBytes[listOff]'hoff).zeroExtend 64)) **
        (.x6 ↦ᵣ (0xc0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion listBase listBytes) := by
    runBlock hadd hlbu hli
  have hframed := cpsTripleWithin_frameR (⌜listLen ≠ (0 : Word)⌝) (by pcFree) hblk
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp) hframed

theorem walkInitEmptyFailStatusCode_disjoint_prefixTail (base : Word) :
    (walkInitEmptyFailStatusCode base).Disjoint (walkInitNonzeroPrefixTailCode base) := by
  unfold walkInitEmptyFailStatusCode walkInitNonzeroPrefixTailCode failStatusReturnCode
    statusReturnCode
  refine CodeReq.Disjoint.union_left ?_ ?_
  · refine CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton (by bv_omega)) ?_
    refine CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega))
  · refine CodeReq.Disjoint.union_left ?_ ?_
    · refine CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton (by bv_omega)) ?_
      refine CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton (by bv_omega))
        (CodeReq.Disjoint.singleton (by bv_omega))
    · refine CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton (by bv_omega)) ?_
      refine CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton (by bv_omega))
        (CodeReq.Disjoint.singleton (by bv_omega))

theorem walkInitEmptyFailStatusCode_disjoint_singleton
    (base a : Word) (i : Instr)
    (h0 : base ≠ a) (h156 : base + 156 ≠ a) (h160 : base + 160 ≠ a) :
    (walkInitEmptyFailStatusCode base).Disjoint (CodeReq.singleton a i) := by
  unfold walkInitEmptyFailStatusCode failStatusReturnCode statusReturnCode
  refine CodeReq.Disjoint.union_left ?_ ?_
  · exact CodeReq.Disjoint.singleton h0
  · refine CodeReq.Disjoint.union_left ?_ ?_
    · exact CodeReq.Disjoint.singleton h156
    · rw [show base + 156 + 4 = base + 160 from by bv_omega]
      exact CodeReq.Disjoint.singleton h160

theorem walkInitNonzeroPrefixTailCode_disjoint_singleton
    (base a : Word) (i : Instr)
    (h4 : base + 4 ≠ a) (h8 : base + 8 ≠ a) (h12 : base + 12 ≠ a) :
    (walkInitNonzeroPrefixTailCode base).Disjoint (CodeReq.singleton a i) := by
  unfold walkInitNonzeroPrefixTailCode
  refine CodeReq.Disjoint.union_left ?_ ?_
  · exact CodeReq.Disjoint.singleton h4
  · refine CodeReq.Disjoint.union_left ?_ ?_
    · exact CodeReq.Disjoint.singleton h8
    · exact CodeReq.Disjoint.singleton h12

/-- WP branch certificate after the first walk-init split and the nonzero prefix
    tail.  The taken arm is the already-serviced empty-input failure endpoint;
    the not-taken arm has loaded the prefix and remains open for the classifier. -/
def walkInitEmptyFailOrPrefixBranch
    (base listBase listLen raVal t0Old t1Old : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    WP.Branch base (walkInitEmptyFailOrPrefixCode base) := by
  let listPtr := listBase + BitVec.ofNat 64 listOff
  let br0 := walkInitEmptyFailStatusBranch base listLen raVal listPtr
  let frame : Assertion := (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion listBase listBytes
  let br := WP.CFG.branchFrameR br0 frame (by
    dsimp [frame]
    pcFree)
  have htail := walkInitNonzeroPrefixTail_spec_within base listBase listLen raVal
    t0Old t1Old listBytes listOff hsalign hoff hover hvalid
  unfold walkInitEmptyFailOrPrefixCode
  exact WP.CFG.branchSeqNotTakenBlockDisjoint
    (walkInitEmptyFailStatusCode_disjoint_prefixTail base)
    br
    htail
    (by
      intro h hp
      dsimp [br, frame, br0, listPtr, WP.CFG.branchFrameR, WP.Branch.frameR] at hp
      simpa only [listPtr, frame] using hp)

theorem walkInitEmptyFailOrPrefixBranch_pre
    (base listBase listLen raVal t0Old t1Old : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    (walkInitEmptyFailOrPrefixBranch base listBase listLen raVal t0Old t1Old
      listBytes listOff hsalign hoff hover hvalid).pre =
      (walkInitEmptyFailStatusPre listLen raVal (listBase + BitVec.ofNat 64 listOff) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion listBase listBytes) := by
  rfl

theorem walkInitEmptyFailOrPrefixBranch_taken_post
    (base listBase listLen raVal t0Old t1Old : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    (walkInitEmptyFailOrPrefixBranch base listBase listLen raVal t0Old t1Old
      listBytes listOff hsalign hoff hover hvalid).post_t =
      (walkInitEmptyFailStatusPost listLen raVal **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion listBase listBytes) := by
  rfl

theorem walkInitEmptyFailOrPrefixBranch_notTaken_post
    (base listBase listLen raVal t0Old t1Old : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    (walkInitEmptyFailOrPrefixBranch base listBase listLen raVal t0Old t1Old
      listBytes listOff hsalign hoff hover hvalid).post_f =
      walkInitPrefixLoadedPost listBase listLen raVal listBytes listOff hoff := by
  rfl

/-- Loaded RLP list prefix byte as a 64-bit word. -/
def walkInitPrefixWord (listBytes : List Byte) (listOff : Nat)
    (hoff : listOff < listBytes.length) : Word :=
  (listBytes[listOff]'hoff).zeroExtend 64

/-- The next classifier instruction after the loaded prefix: `BLTU x5 x6 148`,
    sending non-list prefixes to the failure target and list-shaped prefixes to
    the fall-through decoder. -/
def walkInitPrefixListCheckCode (base : Word) : CodeReq :=
  CodeReq.singleton (base + 16) (.BLTU .x5 .x6 (148 : BitVec 13))

/-- Code through the empty-input failure endpoint and the first list-prefix
    classifier. -/
def walkInitEmptyFailOrListCheckCode (base : Word) : CodeReq :=
  (walkInitEmptyFailOrPrefixCode base).union (walkInitPrefixListCheckCode base)

/-- Prefix-classifier taken arm: the loaded prefix is not an RLP list prefix. -/
def walkInitPrefixNotListPost
    (listBase listLen raVal : Word) (listBytes : List Byte)
    (listOff : Nat) (hoff : listOff < listBytes.length) : Assertion :=
  walkInitPrefixLoadedPost listBase listLen raVal listBytes listOff hoff **
    ⌜BitVec.ult (walkInitPrefixWord listBytes listOff hoff) (0xc0 : Word)⌝

/-- Prefix-classifier fall-through arm: the loaded prefix is list-shaped and is
    ready for the short-list/long-list split. -/
def walkInitPrefixListPost
    (listBase listLen raVal : Word) (listBytes : List Byte)
    (listOff : Nat) (hoff : listOff < listBytes.length) : Assertion :=
  walkInitPrefixLoadedPost listBase listLen raVal listBytes listOff hoff **
    ⌜¬ BitVec.ult (walkInitPrefixWord listBytes listOff hoff) (0xc0 : Word)⌝

theorem walkInitPrefixListCheck_spec_within
    (base listBase listLen raVal : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hoff : listOff < listBytes.length) :
    cpsBranchWithin 1 (base + 16) (walkInitPrefixListCheckCode base)
      (walkInitPrefixLoadedPost listBase listLen raVal listBytes listOff hoff)
      (base + 164) (walkInitPrefixNotListPost listBase listLen raVal listBytes listOff hoff)
      (base + 20) (walkInitPrefixListPost listBase listLen raVal listBytes listOff hoff) := by
  unfold walkInitPrefixListCheckCode walkInitPrefixLoadedPost walkInitPrefixNotListPost
    walkInitPrefixListPost walkInitPrefixWord
  let pfx : Word := (listBytes[listOff]'hoff).zeroExtend 64
  have hbr := bltu_spec_gen_within .x5 .x6 (148 : BitVec 13) pfx (0xc0 : Word) (base + 16)
  rw [show (base + 16) + signExtend13 (148 : BitVec 13) = base + 164 from by
        rw [show signExtend13 (148 : BitVec 13) = (148 : Word) from by decide]
        bv_omega,
      show (base + 16 : Word) + 4 = base + 20 from by bv_omega] at hbr
  have hframed := cpsBranchWithin_frameR
    (((.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
      (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes ** ⌜listLen ≠ (0 : Word)⌝))
    (by pcFree) hbr
  exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold walkInitPrefixLoadedPost
      xperm_hyp hp)
    (fun h hp => by
      unfold walkInitPrefixLoadedPost
      xperm_hyp hp) hframed

/-- WP branch certificate for the list-prefix classifier. -/
def walkInitPrefixListCheckBranch
    (base listBase listLen raVal : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hoff : listOff < listBytes.length) :
    WP.Branch (base + 16) (walkInitPrefixListCheckCode base) :=
  WP.Branch.ofSpec
    (walkInitPrefixListCheck_spec_within base listBase listLen raVal listBytes listOff hoff)

theorem walkInitEmptyFailOrPrefixCode_disjoint_listCheck (base : Word) :
    (walkInitEmptyFailOrPrefixCode base).Disjoint (walkInitPrefixListCheckCode base) := by
  unfold walkInitEmptyFailOrPrefixCode walkInitEmptyFailStatusCode failStatusReturnCode
    statusReturnCode walkInitNonzeroPrefixTailCode walkInitPrefixListCheckCode
  refine CodeReq.Disjoint.union_left ?_ ?_
  · refine CodeReq.Disjoint.union_left ?_ ?_
    · exact CodeReq.Disjoint.singleton (by bv_omega)
    · refine CodeReq.Disjoint.union_left ?_ ?_
      · exact CodeReq.Disjoint.singleton (by bv_omega)
      · exact CodeReq.Disjoint.singleton (by bv_omega)
  · refine CodeReq.Disjoint.union_left ?_ ?_
    · exact CodeReq.Disjoint.singleton (by bv_omega)
    · refine CodeReq.Disjoint.union_left ?_ ?_
      · exact CodeReq.Disjoint.singleton (by bv_omega)
      · exact CodeReq.Disjoint.singleton (by bv_omega)

/-- Multi-exit WP certificate after the empty-input split, prefix load, and first
    prefix classifier. Exits are: empty failure already returned, non-list
    failure target, and list-shaped fall-through. -/
def walkInitEmptyFailOrListCheckNBranch
    (base listBase listLen raVal t0Old t1Old : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    WP.NBranch base (walkInitEmptyFailOrListCheckCode base) := by
  let br := walkInitEmptyFailOrPrefixBranch base listBase listLen raVal t0Old t1Old
    listBytes listOff hsalign hoff hover hvalid
  let tail := WP.CFG.nbranchOfBranch
    (walkInitPrefixListCheckBranch base listBase listLen raVal listBytes listOff hoff)
  unfold walkInitEmptyFailOrListCheckCode
  wp_rv64_branch_not_taken_nbranch_disjoint
    (walkInitEmptyFailOrPrefixCode_disjoint_listCheck base), br, tail

theorem walkInitEmptyFailOrListCheckNBranch_pre
    (base listBase listLen raVal t0Old t1Old : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    (walkInitEmptyFailOrListCheckNBranch base listBase listLen raVal t0Old t1Old
      listBytes listOff hsalign hoff hover hvalid).pre =
      (walkInitEmptyFailStatusPre listLen raVal (listBase + BitVec.ofNat 64 listOff) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion listBase listBytes) := by
  rfl

/-- The reason-erased failure endpoint placed at the not-list target. -/
def walkInitPrefixNotListFailStatusCode (base : Word) : CodeReq :=
  failStatusReturnCode (base + 164)

/-- Code for the prefix list-check branch with its not-list failure endpoint
    already serviced. -/
def walkInitPrefixListCheckOrNotListFailCode (base : Word) : CodeReq :=
  (walkInitPrefixListCheckCode base).union (walkInitPrefixNotListFailStatusCode base)

/-- Code through empty-input failure, prefix load, list-prefix classification,
    and the not-list failure endpoint. The list-shaped arm remains open. -/
def walkInitEmptyFailNotListFailOrListCode (base : Word) : CodeReq :=
  (walkInitEmptyFailOrPrefixCode base).union
    (walkInitPrefixListCheckOrNotListFailCode base)

/-- Frame preserved by the not-list failure endpoint. -/
def walkInitPrefixNotListFailStatusFrame
    (listBase listLen : Word) (listBytes : List Byte)
    (listOff : Nat) (hoff : listOff < listBytes.length) : Assertion :=
  ((.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
    (.x5 ↦ᵣ walkInitPrefixWord listBytes listOff hoff) ** (.x6 ↦ᵣ (0xc0 : Word)) **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes **
    ⌜listLen ≠ (0 : Word)⌝ **
    ⌜BitVec.ult (walkInitPrefixWord listBytes listOff hoff) (0xc0 : Word)⌝)

/-- Not-list arm after it has run the reason-erased failure status endpoint. -/
def walkInitPrefixNotListFailStatusPost
    (listBase listLen raVal : Word) (listBytes : List Byte)
    (listOff : Nat) (hoff : listOff < listBytes.length) : Assertion :=
  failStatusReturnPost raVal **
    walkInitPrefixNotListFailStatusFrame listBase listLen listBytes listOff hoff

theorem walkInitPrefixNotListFailStatusFrame_pcFree
    (listBase listLen : Word) (listBytes : List Byte)
    (listOff : Nat) (hoff : listOff < listBytes.length) :
    (walkInitPrefixNotListFailStatusFrame listBase listLen listBytes listOff hoff).pcFree := by
  unfold walkInitPrefixNotListFailStatusFrame
  pcFree

theorem walkInitPrefixNotListFailStatus_spec_within
    (base listBase listLen raVal : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hoff : listOff < listBytes.length) :
    cpsTripleWithin (failStatusReturnCert (base + 164) raVal
        (listBase + BitVec.ofNat 64 listOff)).nSteps
      (base + 164) (failStatusReturnExit raVal)
      (walkInitPrefixNotListFailStatusCode base)
      (walkInitPrefixNotListPost listBase listLen raVal listBytes listOff hoff)
      (walkInitPrefixNotListFailStatusPost listBase listLen raVal listBytes listOff hoff) := by
  unfold walkInitPrefixNotListFailStatusCode
  have hfail := failStatusReturn_spec_within (base + 164) raVal
    (listBase + BitVec.ofNat 64 listOff)
  have hframed := cpsTripleWithin_frameR
    (walkInitPrefixNotListFailStatusFrame listBase listLen listBytes listOff hoff)
    (walkInitPrefixNotListFailStatusFrame_pcFree listBase listLen listBytes listOff hoff)
    hfail
  exact cpsTripleWithin_weaken (fun h hp => by
      unfold walkInitPrefixNotListPost walkInitPrefixLoadedPost at hp
      unfold failStatusReturnPre statusReturnPre walkInitPrefixNotListFailStatusFrame
        walkInitPrefixWord
      xperm_hyp hp)
    (fun h hp => by
      unfold walkInitPrefixNotListFailStatusPost
      xperm_hyp hp) hframed

theorem walkInitPrefixListCheckCode_disjoint_notListFailStatus (base : Word) :
    (walkInitPrefixListCheckCode base).Disjoint
      (walkInitPrefixNotListFailStatusCode base) := by
  unfold walkInitPrefixListCheckCode walkInitPrefixNotListFailStatusCode
    failStatusReturnCode statusReturnCode
  refine CodeReq.Disjoint.union_right
    (CodeReq.Disjoint.singleton (by bv_omega))
    (CodeReq.Disjoint.singleton (by bv_omega))

theorem walkInitEmptyFailOrPrefixCode_disjoint_notListFailStatus (base : Word) :
    (walkInitEmptyFailOrPrefixCode base).Disjoint
      (walkInitPrefixNotListFailStatusCode base) := by
  unfold walkInitEmptyFailOrPrefixCode walkInitEmptyFailStatusCode failStatusReturnCode
    statusReturnCode walkInitNonzeroPrefixTailCode walkInitPrefixNotListFailStatusCode
  refine CodeReq.Disjoint.union_left ?_ ?_
  · refine CodeReq.Disjoint.union_left ?_ ?_
    · refine CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton (by bv_omega))
        (CodeReq.Disjoint.singleton (by bv_omega))
    · refine CodeReq.Disjoint.union_left ?_ ?_
      · refine CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.singleton (by bv_omega))
          (CodeReq.Disjoint.singleton (by bv_omega))
      · refine CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.singleton (by bv_omega))
          (CodeReq.Disjoint.singleton (by bv_omega))
  · refine CodeReq.Disjoint.union_left ?_ ?_
    · refine CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton (by bv_omega))
        (CodeReq.Disjoint.singleton (by bv_omega))
    · refine CodeReq.Disjoint.union_left ?_ ?_
      · refine CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.singleton (by bv_omega))
          (CodeReq.Disjoint.singleton (by bv_omega))
      · refine CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.singleton (by bv_omega))
          (CodeReq.Disjoint.singleton (by bv_omega))

theorem walkInitEmptyFailOrPrefixCode_disjoint_listCheckOrNotListFail (base : Word) :
    (walkInitEmptyFailOrPrefixCode base).Disjoint
      (walkInitPrefixListCheckOrNotListFailCode base) := by
  unfold walkInitPrefixListCheckOrNotListFailCode
  exact CodeReq.Disjoint.union_right
    (walkInitEmptyFailOrPrefixCode_disjoint_listCheck base)
    (walkInitEmptyFailOrPrefixCode_disjoint_notListFailStatus base)

/-- Multi-exit WP certificate after the first two failure cases have been
    serviced. Exits are: empty failure returned, not-list failure returned, and
    list-shaped fall-through. -/
def walkInitEmptyFailNotListFailOrListNBranch
    (base listBase listLen raVal t0Old t1Old : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    WP.NBranch base (walkInitEmptyFailNotListFailOrListCode base) := by
  let br := walkInitEmptyFailOrPrefixBranch base listBase listLen raVal t0Old t1Old
    listBytes listOff hsalign hoff hover hvalid
  let listBranch := walkInitPrefixListCheckBranch base listBase listLen raVal
    listBytes listOff hoff
  have hfail := walkInitPrefixNotListFailStatus_spec_within base listBase listLen raVal
    listBytes listOff hoff
  let listTail0 := WP.CFG.nbranchOfBranch listBranch
  let tail : WP.NBranch (base + 16) (walkInitPrefixListCheckOrNotListFailCode base) := by
    unfold walkInitPrefixListCheckOrNotListFailCode walkInitPrefixNotListFailStatusCode
    wp_rv64_nbranch_head_block_disjoint
      (walkInitPrefixListCheckCode_disjoint_notListFailStatus base), listTail0, hfail
  unfold walkInitEmptyFailNotListFailOrListCode
  wp_rv64_branch_not_taken_nbranch_disjoint
    (walkInitEmptyFailOrPrefixCode_disjoint_listCheckOrNotListFail base), br, tail

theorem walkInitEmptyFailNotListFailOrListNBranch_pre
    (base listBase listLen raVal t0Old t1Old : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    (walkInitEmptyFailNotListFailOrListNBranch base listBase listLen raVal t0Old t1Old
      listBytes listOff hsalign hoff hover hvalid).pre =
      (walkInitEmptyFailStatusPre listLen raVal (listBase + BitVec.ofNat 64 listOff) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion listBase listBytes) := by
  rfl

/-- Branch certificate for the prefix list-check with the not-list arm already
    serviced by the reason-erased failure endpoint. -/
def walkInitPrefixListCheckOrNotListFailBranch
    (base listBase listLen raVal : Word) (listBytes : List Byte)
    (listOff : Nat) (hoff : listOff < listBytes.length) :
    WP.Branch (base + 16) (walkInitPrefixListCheckOrNotListFailCode base) := by
  let br := walkInitPrefixListCheckBranch base listBase listLen raVal listBytes listOff hoff
  have hfail := walkInitPrefixNotListFailStatus_spec_within base listBase listLen raVal
    listBytes listOff hoff
  unfold walkInitPrefixListCheckOrNotListFailCode walkInitPrefixNotListFailStatusCode
  wp_rv64_branch_taken_block_disjoint
    (walkInitPrefixListCheckCode_disjoint_notListFailStatus base), br, hfail

/-- The list-shaped fall-through loads the next classifier threshold `0xf8`. -/
def walkInitListF8Code (base : Word) : CodeReq :=
  CodeReq.singleton (base + 20) (.LI .x6 (0xf8 : Word))

def walkInitPrefixListCheckNotListFailF8Code (base : Word) : CodeReq :=
  (walkInitPrefixListCheckOrNotListFailCode base).union (walkInitListF8Code base)

def walkInitShortLongCheckCode (base : Word) : CodeReq :=
  CodeReq.singleton (base + 24) (.BLTU .x5 .x6 (100 : BitVec 13))

def walkInitPrefixShortLongTailCode (base : Word) : CodeReq :=
  (walkInitPrefixListCheckNotListFailF8Code base).union (walkInitShortLongCheckCode base)

def walkInitEmptyFailNotListFailShortLongCode (base : Word) : CodeReq :=
  (walkInitEmptyFailOrPrefixCode base).union (walkInitPrefixShortLongTailCode base)

def walkInitNonzeroNotListFailShortLongCode (base : Word) : CodeReq :=
  (walkInitNonzeroPrefixTailCode base).union (walkInitPrefixShortLongTailCode base)

def walkInitEmptyFailThenNonzeroShortLongCode (base : Word) : CodeReq :=
  (walkInitEmptyFailStatusCode base).union (walkInitNonzeroNotListFailShortLongCode base)

/-- State after the list-shaped fall-through has prepared the `0xf8` short/long
    list threshold. -/
def walkInitPrefixF8Post
    (listBase listLen raVal : Word) (listBytes : List Byte)
    (listOff : Nat) (hoff : listOff < listBytes.length) : Assertion :=
  ((.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
    (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
    (.x5 ↦ᵣ walkInitPrefixWord listBytes listOff hoff) ** (.x6 ↦ᵣ (0xf8 : Word)) **
    (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes **
    ⌜listLen ≠ (0 : Word)⌝ **
    ⌜¬ BitVec.ult (walkInitPrefixWord listBytes listOff hoff) (0xc0 : Word)⌝)

def walkInitShortListCandidatePost
    (listBase listLen raVal : Word) (listBytes : List Byte)
    (listOff : Nat) (hoff : listOff < listBytes.length) : Assertion :=
  walkInitPrefixF8Post listBase listLen raVal listBytes listOff hoff **
    ⌜BitVec.ult (walkInitPrefixWord listBytes listOff hoff) (0xf8 : Word)⌝

def walkInitLongListCandidatePost
    (listBase listLen raVal : Word) (listBytes : List Byte)
    (listOff : Nat) (hoff : listOff < listBytes.length) : Assertion :=
  walkInitPrefixF8Post listBase listLen raVal listBytes listOff hoff **
    ⌜¬ BitVec.ult (walkInitPrefixWord listBytes listOff hoff) (0xf8 : Word)⌝

theorem walkInitPrefixSetF8_spec_within
    (base listBase listLen raVal : Word) (listBytes : List Byte)
    (listOff : Nat) (hoff : listOff < listBytes.length) :
    cpsTripleWithin 1 (base + 20) (base + 24) (walkInitListF8Code base)
      (walkInitPrefixListPost listBase listLen raVal listBytes listOff hoff)
      (walkInitPrefixF8Post listBase listLen raVal listBytes listOff hoff) := by
  unfold walkInitListF8Code walkInitPrefixListPost walkInitPrefixLoadedPost
    walkInitPrefixF8Post walkInitPrefixWord
  let pfx : Word := (listBytes[listOff]'hoff).zeroExtend 64
  have hli := li_spec_gen_within .x6 (0xc0 : Word) (0xf8 : Word) (base + 20) (by decide)
  have hframed := cpsTripleWithin_frameR
    (((.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
      (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x5 ↦ᵣ pfx) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes **
      ⌜listLen ≠ (0 : Word)⌝ ** ⌜¬ BitVec.ult pfx (0xc0 : Word)⌝))
    (by pcFree) hli
  rw [show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hframed
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp) hframed

theorem walkInitShortLongCheck_spec_within
    (base listBase listLen raVal : Word) (listBytes : List Byte)
    (listOff : Nat) (hoff : listOff < listBytes.length) :
    cpsBranchWithin 1 (base + 24) (walkInitShortLongCheckCode base)
      (walkInitPrefixF8Post listBase listLen raVal listBytes listOff hoff)
      (base + 124) (walkInitShortListCandidatePost listBase listLen raVal listBytes listOff hoff)
      (base + 28) (walkInitLongListCandidatePost listBase listLen raVal listBytes listOff hoff) := by
  unfold walkInitShortLongCheckCode walkInitPrefixF8Post walkInitShortListCandidatePost
    walkInitLongListCandidatePost walkInitPrefixWord
  let pfx : Word := (listBytes[listOff]'hoff).zeroExtend 64
  have hbr := bltu_spec_gen_within .x5 .x6 (100 : BitVec 13) pfx (0xf8 : Word) (base + 24)
  rw [show (base + 24) + signExtend13 (100 : BitVec 13) = base + 124 from by
        rw [show signExtend13 (100 : BitVec 13) = (100 : Word) from by decide]
        bv_omega,
      show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at hbr
  have hframed := cpsBranchWithin_frameR
    (((.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
      (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes ** ⌜listLen ≠ (0 : Word)⌝ **
      ⌜¬ BitVec.ult pfx (0xc0 : Word)⌝))
    (by pcFree) hbr
  exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hp => by unfold walkInitPrefixF8Post walkInitPrefixWord; xperm_hyp hp)
    (fun h hp => by unfold walkInitPrefixF8Post walkInitPrefixWord; xperm_hyp hp) hframed

def walkInitShortLongCheckBranch
    (base listBase listLen raVal : Word) (listBytes : List Byte)
    (listOff : Nat) (hoff : listOff < listBytes.length) :
    WP.Branch (base + 24) (walkInitShortLongCheckCode base) :=
  WP.Branch.ofSpec
    (walkInitShortLongCheck_spec_within base listBase listLen raVal listBytes listOff hoff)

theorem walkInitPrefixListCheckOrNotListFailCode_disjoint_listF8 (base : Word) :
    (walkInitPrefixListCheckOrNotListFailCode base).Disjoint (walkInitListF8Code base) := by
  unfold walkInitPrefixListCheckOrNotListFailCode walkInitPrefixListCheckCode
    walkInitPrefixNotListFailStatusCode failStatusReturnCode statusReturnCode walkInitListF8Code
  refine CodeReq.Disjoint.union_left (CodeReq.Disjoint.singleton (by bv_omega)) ?_
  refine CodeReq.Disjoint.union_left
    (CodeReq.Disjoint.singleton (by bv_omega))
    (CodeReq.Disjoint.singleton (by bv_omega))

theorem walkInitPrefixListCheckNotListFailF8Code_disjoint_shortLong (base : Word) :
    (walkInitPrefixListCheckNotListFailF8Code base).Disjoint (walkInitShortLongCheckCode base) := by
  unfold walkInitPrefixListCheckNotListFailF8Code walkInitPrefixListCheckOrNotListFailCode
    walkInitPrefixListCheckCode walkInitPrefixNotListFailStatusCode failStatusReturnCode
    statusReturnCode walkInitListF8Code walkInitShortLongCheckCode
  refine CodeReq.Disjoint.union_left ?_ (CodeReq.Disjoint.singleton (by bv_omega))
  refine CodeReq.Disjoint.union_left (CodeReq.Disjoint.singleton (by bv_omega)) ?_
  refine CodeReq.Disjoint.union_left
    (CodeReq.Disjoint.singleton (by bv_omega))
    (CodeReq.Disjoint.singleton (by bv_omega))

theorem walkInitEmptyFailOrPrefixCode_disjoint_listF8 (base : Word) :
    (walkInitEmptyFailOrPrefixCode base).Disjoint (walkInitListF8Code base) := by
  unfold walkInitEmptyFailOrPrefixCode walkInitEmptyFailStatusCode failStatusReturnCode
    statusReturnCode walkInitNonzeroPrefixTailCode walkInitListF8Code
  refine CodeReq.Disjoint.union_left ?_ ?_
  · refine CodeReq.Disjoint.union_left (CodeReq.Disjoint.singleton (by bv_omega)) ?_
    refine CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega))
  · refine CodeReq.Disjoint.union_left (CodeReq.Disjoint.singleton (by bv_omega)) ?_
    refine CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega))

theorem walkInitEmptyFailOrPrefixCode_disjoint_shortLong (base : Word) :
    (walkInitEmptyFailOrPrefixCode base).Disjoint (walkInitShortLongCheckCode base) := by
  unfold walkInitEmptyFailOrPrefixCode walkInitEmptyFailStatusCode failStatusReturnCode
    statusReturnCode walkInitNonzeroPrefixTailCode walkInitShortLongCheckCode
  refine CodeReq.Disjoint.union_left ?_ ?_
  · refine CodeReq.Disjoint.union_left (CodeReq.Disjoint.singleton (by bv_omega)) ?_
    refine CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega))
  · refine CodeReq.Disjoint.union_left (CodeReq.Disjoint.singleton (by bv_omega)) ?_
    refine CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega))

theorem walkInitEmptyFailOrPrefixCode_disjoint_shortLongTail (base : Word) :
    (walkInitEmptyFailOrPrefixCode base).Disjoint (walkInitPrefixShortLongTailCode base) := by
  unfold walkInitPrefixShortLongTailCode walkInitPrefixListCheckNotListFailF8Code
  exact CodeReq.Disjoint.union_right
    (CodeReq.Disjoint.union_right
      (walkInitEmptyFailOrPrefixCode_disjoint_listCheckOrNotListFail base)
      (walkInitEmptyFailOrPrefixCode_disjoint_listF8 base))
    (walkInitEmptyFailOrPrefixCode_disjoint_shortLong base)

theorem walkInitNonzeroPrefixTailCode_disjoint_prefixShortLongTail (base : Word) :
    (walkInitNonzeroPrefixTailCode base).Disjoint (walkInitPrefixShortLongTailCode base) := by
  unfold walkInitPrefixShortLongTailCode walkInitPrefixListCheckNotListFailF8Code
    walkInitPrefixListCheckOrNotListFailCode walkInitPrefixListCheckCode
    walkInitPrefixNotListFailStatusCode failStatusReturnCode statusReturnCode
    walkInitListF8Code walkInitShortLongCheckCode
  have d16 := walkInitNonzeroPrefixTailCode_disjoint_singleton base (base + 16) (.BLTU .x5 .x6 (148 : BitVec 13))
    (by bv_omega) (by bv_omega) (by bv_omega)
  have d164 := walkInitNonzeroPrefixTailCode_disjoint_singleton base (base + 164) (.LI .x10 (1 : Word))
    (by bv_omega) (by bv_omega) (by bv_omega)
  have d168 := walkInitNonzeroPrefixTailCode_disjoint_singleton base (base + 164 + 4) (.JALR .x0 .x1 (0 : BitVec 12))
    (by bv_omega) (by bv_omega) (by bv_omega)
  have d20 := walkInitNonzeroPrefixTailCode_disjoint_singleton base (base + 20) (.LI .x6 (0xf8 : Word))
    (by bv_omega) (by bv_omega) (by bv_omega)
  have d24 := walkInitNonzeroPrefixTailCode_disjoint_singleton base (base + 24) (.BLTU .x5 .x6 (100 : BitVec 13))
    (by bv_omega) (by bv_omega) (by bv_omega)
  exact CodeReq.Disjoint.union_right
    (CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.union_right d16 (CodeReq.Disjoint.union_right d164 d168)) d20) d24

theorem walkInitEmptyFailStatusCode_disjoint_prefixShortLongTail (base : Word) :
    (walkInitEmptyFailStatusCode base).Disjoint (walkInitPrefixShortLongTailCode base) := by
  unfold walkInitPrefixShortLongTailCode walkInitPrefixListCheckNotListFailF8Code
    walkInitPrefixListCheckOrNotListFailCode walkInitPrefixListCheckCode
    walkInitPrefixNotListFailStatusCode failStatusReturnCode statusReturnCode
    walkInitListF8Code walkInitShortLongCheckCode
  have d16 := walkInitEmptyFailStatusCode_disjoint_singleton base (base + 16) (.BLTU .x5 .x6 (148 : BitVec 13))
    (by bv_omega) (by bv_omega) (by bv_omega)
  have d164 := walkInitEmptyFailStatusCode_disjoint_singleton base (base + 164) (.LI .x10 (1 : Word))
    (by bv_omega) (by bv_omega) (by bv_omega)
  have d168 := walkInitEmptyFailStatusCode_disjoint_singleton base (base + 164 + 4) (.JALR .x0 .x1 (0 : BitVec 12))
    (by bv_omega) (by bv_omega) (by bv_omega)
  have d20 := walkInitEmptyFailStatusCode_disjoint_singleton base (base + 20) (.LI .x6 (0xf8 : Word))
    (by bv_omega) (by bv_omega) (by bv_omega)
  have d24 := walkInitEmptyFailStatusCode_disjoint_singleton base (base + 24) (.BLTU .x5 .x6 (100 : BitVec 13))
    (by bv_omega) (by bv_omega) (by bv_omega)
  exact CodeReq.Disjoint.union_right
    (CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.union_right d16 (CodeReq.Disjoint.union_right d164 d168)) d20) d24

theorem walkInitEmptyFailStatusCode_disjoint_nonzeroNotListFailShortLong (base : Word) :
    (walkInitEmptyFailStatusCode base).Disjoint
      (walkInitNonzeroNotListFailShortLongCode base) := by
  unfold walkInitNonzeroNotListFailShortLongCode
  exact CodeReq.Disjoint.union_right
    (walkInitEmptyFailStatusCode_disjoint_prefixTail base)
    (walkInitEmptyFailStatusCode_disjoint_prefixShortLongTail base)

/-- Tail classifier from the already-loaded prefix at base + 16 through the
    not-list failure endpoint and the short-list/long-list split. -/
def walkInitPrefixShortLongTailNBranch
    (base listBase listLen raVal : Word) (listBytes : List Byte)
    (listOff : Nat) (hoff : listOff < listBytes.length) :
    WP.NBranch (base + 16) (walkInitPrefixShortLongTailCode base) := by
  let listBranch := walkInitPrefixListCheckOrNotListFailBranch base listBase listLen raVal
    listBytes listOff hoff
  have hf8 := walkInitPrefixSetF8_spec_within base listBase listLen raVal
    listBytes listOff hoff
  let f8Branch : WP.Branch (base + 16) (walkInitPrefixListCheckNotListFailF8Code base) := by
    unfold walkInitPrefixListCheckNotListFailF8Code
    wp_rv64_branch_not_taken_block_disjoint
      (walkInitPrefixListCheckOrNotListFailCode_disjoint_listF8 base), listBranch, hf8
  let shortLong := WP.CFG.nbranchOfBranch
    (walkInitShortLongCheckBranch base listBase listLen raVal listBytes listOff hoff)
  unfold walkInitPrefixShortLongTailCode
  wp_rv64_branch_not_taken_nbranch_disjoint
    (walkInitPrefixListCheckNotListFailF8Code_disjoint_shortLong base), f8Branch, shortLong

/-- Nonzero walk-init tail: load the first prefix byte, service the not-list
    failure endpoint, and expose short-list/long-list candidates. -/
def walkInitNonzeroNotListFailShortLongNBranch
    (base listBase listLen raVal t0Old t1Old : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    WP.NBranch (base + 4) (walkInitNonzeroNotListFailShortLongCode base) := by
  have hprefix := walkInitNonzeroPrefixTail_spec_within base listBase listLen raVal
    t0Old t1Old listBytes listOff hsalign hoff hover hvalid
  let tail := walkInitPrefixShortLongTailNBranch base listBase listLen raVal
    listBytes listOff hoff
  unfold walkInitNonzeroNotListFailShortLongCode
  wp_rv64_seq_block_nbranch_disjoint
    (walkInitNonzeroPrefixTailCode_disjoint_prefixShortLongTail base), hprefix, tail

theorem walkInitNonzeroNotListFailShortLongNBranch_pre
    (base listBase listLen raVal t0Old t1Old : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    (walkInitNonzeroNotListFailShortLongNBranch base listBase listLen raVal t0Old t1Old
      listBytes listOff hsalign hoff hover hvalid).pre =
      ((walkInitNonzeroOpenStatusPost listLen raVal (listBase + BitVec.ofNat 64 listOff)) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion listBase listBytes) := by
  rfl

/-- Same classifier as walkInitEmptyFailNotListFailShortLongNBranch, but built
    by preserving the empty-input head exit and continuing the nonzero second exit. -/
def walkInitEmptyFailThenNonzeroShortLongNBranch
    (base listBase listLen raVal t0Old t1Old : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    WP.NBranch base (walkInitEmptyFailThenNonzeroShortLongCode base) := by
  let listPtr := listBase + BitVec.ofNat 64 listOff
  let frame : Assertion := (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion listBase listBytes
  let statusBranch := walkInitEmptyFailStatusBranch base listLen raVal listPtr
  let br0 := WP.CFG.nbranchOfBranch statusBranch
  let br := WP.CFG.nbranchFrameR br0 frame (by
    dsimp [frame]
    pcFree)
  let tail := walkInitNonzeroNotListFailShortLongNBranch base listBase listLen raVal
    t0Old t1Old listBytes listOff hsalign hoff hover hvalid
  unfold walkInitEmptyFailThenNonzeroShortLongCode
  wp_rv64_nbranch_exit_nbranch_disjoint
    (walkInitEmptyFailStatusCode_disjoint_nonzeroNotListFailShortLong base), br,
    [(statusBranch.exit_t, (statusBranch.post_t ** frame))], tail

theorem walkInitEmptyFailThenNonzeroShortLongNBranch_pre
    (base listBase listLen raVal t0Old t1Old : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    (walkInitEmptyFailThenNonzeroShortLongNBranch base listBase listLen raVal t0Old t1Old
      listBytes listOff hsalign hoff hover hvalid).pre =
      (walkInitEmptyFailStatusPre listLen raVal (listBase + BitVec.ofNat 64 listOff) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion listBase listBytes) := by
  rfl

/-- Multi-exit WP certificate after the first list-prefix classifier has reached
    the short-list versus long-list split. Exits are empty failure, not-list
    failure, short-list candidate, and long-list candidate. -/
def walkInitEmptyFailNotListFailShortLongNBranch
    (base listBase listLen raVal t0Old t1Old : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    WP.NBranch base (walkInitEmptyFailNotListFailShortLongCode base) := by
  let br := walkInitEmptyFailOrPrefixBranch base listBase listLen raVal t0Old t1Old
    listBytes listOff hsalign hoff hover hvalid
  let listBranch := walkInitPrefixListCheckOrNotListFailBranch base listBase listLen raVal
    listBytes listOff hoff
  have hf8 := walkInitPrefixSetF8_spec_within base listBase listLen raVal
    listBytes listOff hoff
  let f8Branch : WP.Branch (base + 16) (walkInitPrefixListCheckNotListFailF8Code base) := by
    unfold walkInitPrefixListCheckNotListFailF8Code
    wp_rv64_branch_not_taken_block_disjoint
      (walkInitPrefixListCheckOrNotListFailCode_disjoint_listF8 base), listBranch, hf8
  let shortLong := WP.CFG.nbranchOfBranch
    (walkInitShortLongCheckBranch base listBase listLen raVal listBytes listOff hoff)
  let tail : WP.NBranch (base + 16) (walkInitPrefixShortLongTailCode base) := by
    unfold walkInitPrefixShortLongTailCode
    wp_rv64_branch_not_taken_nbranch_disjoint
      (walkInitPrefixListCheckNotListFailF8Code_disjoint_shortLong base), f8Branch, shortLong
  unfold walkInitEmptyFailNotListFailShortLongCode
  wp_rv64_branch_not_taken_nbranch_disjoint
    (walkInitEmptyFailOrPrefixCode_disjoint_shortLongTail base), br, tail

theorem walkInitEmptyFailNotListFailShortLongNBranch_pre
    (base listBase listLen raVal t0Old t1Old : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    (walkInitEmptyFailNotListFailShortLongNBranch base listBase listLen raVal t0Old t1Old
      listBytes listOff hsalign hoff hover hvalid).pre =
      (walkInitEmptyFailStatusPre listLen raVal (listBase + BitVec.ofNat 64 listOff) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion listBase listBytes) := by
  rfl

/-- Uniformly frame the symbolic walk-init classifier. Generated decoder proofs
    use this after WP reduction to carry caller-owned resources, such as the ABI
    output buffer, across every still-open exit. -/
def walkInitEmptyFailNotListFailShortLongFramedNBranch
    (base listBase listLen raVal t0Old t1Old : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (F : Assertion) (hF : F.pcFree) :
    WP.NBranch base (walkInitEmptyFailNotListFailShortLongCode base) := by
  let br := walkInitEmptyFailNotListFailShortLongNBranch base listBase listLen raVal
    t0Old t1Old listBytes listOff hsalign hoff hover hvalid
  wp_rv64_nbranch_frame br, F, hF

theorem walkInitEmptyFailNotListFailShortLongFramedNBranch_pre
    (base listBase listLen raVal t0Old t1Old : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (F : Assertion) (hF : F.pcFree) :
    (walkInitEmptyFailNotListFailShortLongFramedNBranch base listBase listLen raVal t0Old t1Old
      listBytes listOff hsalign hoff hover hvalid F hF).pre =
      ((walkInitEmptyFailNotListFailShortLongNBranch base listBase listLen raVal t0Old t1Old
        listBytes listOff hsalign hoff hover hvalid).pre ** F) := by
  rfl

theorem walkInitEmptyFailNotListFailShortLongFramedNBranch_pre_expanded
    (base listBase listLen raVal t0Old t1Old : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (F : Assertion) (hF : F.pcFree) :
    (walkInitEmptyFailNotListFailShortLongFramedNBranch base listBase listLen raVal t0Old t1Old
      listBytes listOff hsalign hoff hover hvalid F hF).pre =
      ((walkInitEmptyFailStatusPre listLen raVal (listBase + BitVec.ofNat 64 listOff) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion listBase listBytes) ** F) := by
  rw [walkInitEmptyFailNotListFailShortLongFramedNBranch_pre,
    walkInitEmptyFailNotListFailShortLongNBranch_pre]

/-! ## Pure decode bridge -/

/-- The decoded withdrawal value described by four already-decoded field byte strings.
    This is a postcondition/result helper, not part of the static schema. -/
def fromFieldBytes (d0 d1 d2 d3 : List Byte) : Withdrawal where
  index := Nat.fromBytesBE d0
  validatorIndex := Nat.fromBytesBE d1
  address := BitVec.ofNat 160 (Nat.fromBytesBE d2)
  amount := Nat.fromBytesBE d3

/-- If the pure RLP decoder sees exactly the four withdrawal byte fields and the
    field guards match `decodeWithdrawal`'s strict scalar/address contract, then
    `decodeWithdrawal` succeeds with the value derived from those bytes. -/
theorem decodeWithdrawal_eq_some_of_decodeFully_fields
    {input d0 d1 d2 d3 : List Byte}
    (hfull : decodeFully input = some (.list [.bytes d0, .bytes d1, .bytes d2, .bytes d3]))
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8) :
    decodeWithdrawal input = some (fromFieldBytes d0 d1 d2 d3) := by
  unfold decodeWithdrawal fromFieldBytes
  rw [hfull]
  simp only [hc0, hl0, hc1, hl1, haddr, hc3, hl3, ne_eq, not_false_eq_true,
    and_self, if_true]

/-- Short-list walk capstone specialized to withdrawal fields. The hypotheses are
    exactly the reusable walk/decode bridge facts for four byte-string items plus
    the strict field guards. -/
theorem decodeWithdrawal_shortList_four_of_decodeAux (pfx : Byte) (payload : List Byte)
    (off1 off2 off3 off4 : Nat) (d0 d1 d2 d3 : List Byte)
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (h0 : ∀ m, decodeAux (m + 1) payload = some (.bytes d0, payload.drop off1))
    (h1 : ∀ m, decodeAux (m + 1) (payload.drop off1) = some (.bytes d1, payload.drop off2))
    (h2 : ∀ m, decodeAux (m + 1) (payload.drop off2) = some (.bytes d2, payload.drop off3))
    (h3 : ∀ m, decodeAux (m + 1) (payload.drop off3) = some (.bytes d3, payload.drop off4))
    (hend : payload.drop off4 = [])
    (h_min : 2 ≤ payload.length)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8) :
    decodeWithdrawal (pfx :: payload) = some (fromFieldBytes d0 d1 d2 d3) := by
  have hfull := decodeFully_shortList_four pfx payload off1 off2 off3 off4
    (.bytes d0) (.bytes d1) (.bytes d2) (.bytes d3) h_class h_len h0 h1 h2 h3 hend h_min
  exact decodeWithdrawal_eq_some_of_decodeFully_fields hfull hc0 hl0 hc1 hl1 haddr hc3 hl3

/-- Short-list walk capstone specialized to withdrawal fields, phrased over the
    remainder chain exposed by validating WP field posts. -/
theorem decodeWithdrawal_shortList_four_of_decodeAux_chain
    (pfx : Byte) (payload r1 r2 r3 r4 : List Byte) (d0 d1 d2 d3 : List Byte)
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (h0 : ∀ m, decodeAux (m + 1) payload = some (.bytes d0, r1))
    (h1 : ∀ m, decodeAux (m + 1) r1 = some (.bytes d1, r2))
    (h2 : ∀ m, decodeAux (m + 1) r2 = some (.bytes d2, r3))
    (h3 : ∀ m, decodeAux (m + 1) r3 = some (.bytes d3, r4))
    (hend : r4 = [])
    (h_min : 2 ≤ payload.length)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8) :
    decodeWithdrawal (pfx :: payload) = some (fromFieldBytes d0 d1 d2 d3) := by
  have hfull := decodeFully_shortList_four_chain pfx payload r1 r2 r3 r4
    (.bytes d0) (.bytes d1) (.bytes d2) (.bytes d3) h_class h_len h0 h1 h2 h3 hend h_min
  exact decodeWithdrawal_eq_some_of_decodeFully_fields hfull hc0 hl0 hc1 hl1 haddr hc3 hl3

/-- Implicit-argument facade for tactic use of the chain-shaped success bridge. -/
theorem decodeWithdrawal_shortList_four_of_decodeAux_chain_auto
    {pfx : Byte} {payload r1 r2 r3 r4 d0 d1 d2 d3 : List Byte}
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (h0 : ∀ m, decodeAux (m + 1) payload = some (.bytes d0, r1))
    (h1 : ∀ m, decodeAux (m + 1) r1 = some (.bytes d1, r2))
    (h2 : ∀ m, decodeAux (m + 1) r2 = some (.bytes d2, r3))
    (h3 : ∀ m, decodeAux (m + 1) r3 = some (.bytes d3, r4))
    (hend : r4 = [])
    (h_min : 2 ≤ payload.length)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8) :
    decodeWithdrawal (pfx :: payload) = some (fromFieldBytes d0 d1 d2 d3) :=
  decodeWithdrawal_shortList_four_of_decodeAux_chain pfx payload r1 r2 r3 r4 d0 d1 d2 d3
    h_class h_len h0 h1 h2 h3 hend h_min hc0 hl0 hc1 hl1 haddr hc3 hl3

/-- The pure withdrawal decoder rejects empty input. -/
theorem decodeWithdrawal_nil : decodeWithdrawal ([] : List Byte) = none := by
  rfl

/-! ## Result bytes, derived from the pure decoder result -/

/-- Eight little-endian bytes of a 64-bit word. -/
def u64LEBytes (v : Word) : List Byte :=
  [ v.truncate 8
  , (v >>> 8).truncate 8
  , (v >>> 16).truncate 8
  , (v >>> 24).truncate 8
  , (v >>> 32).truncate 8
  , (v >>> 40).truncate 8
  , (v >>> 48).truncate 8
  , (v >>> 56).truncate 8
  ]

theorem u64LEBytes_length (v : Word) : (u64LEBytes v).length = 8 := rfl

/-- Twenty big-endian bytes of a 160-bit address word. -/
def addressBEBytes (v : BitVec 160) : List Byte :=
  [ (v >>> 152).truncate 8
  , (v >>> 144).truncate 8
  , (v >>> 136).truncate 8
  , (v >>> 128).truncate 8
  , (v >>> 120).truncate 8
  , (v >>> 112).truncate 8
  , (v >>> 104).truncate 8
  , (v >>> 96).truncate 8
  , (v >>> 88).truncate 8
  , (v >>> 80).truncate 8
  , (v >>> 72).truncate 8
  , (v >>> 64).truncate 8
  , (v >>> 56).truncate 8
  , (v >>> 48).truncate 8
  , (v >>> 40).truncate 8
  , (v >>> 32).truncate 8
  , (v >>> 24).truncate 8
  , (v >>> 16).truncate 8
  , (v >>> 8).truncate 8
  , v.truncate 8
  ]

theorem addressBEBytes_length (v : BitVec 160) : (addressBEBytes v).length = 20 := rfl

/-- ABI struct bytes for a successful pure withdrawal decode. -/
def successBytes (w : Withdrawal) : List Byte :=
  u64LEBytes (BitVec.ofNat 64 w.index) ++
  u64LEBytes (BitVec.ofNat 64 w.validatorIndex) ++
  addressBEBytes w.address ++
  List.replicate 4 (0 : Byte) ++
  u64LEBytes (BitVec.ofNat 64 w.amount)

theorem successBytes_length (w : Withdrawal) : (successBytes w).length = outputSize := by
  simp [successBytes, outputSize, u64LEBytes, addressBEBytes]

/-! ## ABI assertions -/

/-- Own an arbitrary byte region of a fixed length.  Used on failure paths,
    where the routine reports failure and the output buffer contents are not
    part of the functional contract. -/
def bytesRegionAny (base : Word) (n : Nat) : Assertion :=
  fun h => ∃ bs : List Byte, bs.length = n ∧ bytesRegion base bs h

theorem bytesRegionAny_pcFree (base : Word) (n : Nat) :
    (bytesRegionAny base n).pcFree := by
  intro h hp
  obtain ⟨bs, _hlen, hbs⟩ := hp
  exact bytesRegion_pcFree base bs h hbs

instance (base : Word) (n : Nat) : Assertion.PCFree (bytesRegionAny base n) :=
  ⟨bytesRegionAny_pcFree base n⟩

/-- Zero/nonzero walk-init split with an arbitrary caller frame carried across both
    exits. Unlike the deeper prefix classifier, this certificate needs no prefix
    readability hypotheses, so it is usable for the empty-input ABI path. -/
def walkInitEmptyFailOrNonzeroFramedNBranch
    (base listLen raVal statusOld : Word) (F : Assertion) (hF : F.pcFree) :
    WP.NBranch base (walkInitEmptyFailStatusCode base) := by
  let br := WP.CFG.nbranchOfBranch (walkInitEmptyFailStatusBranch base listLen raVal statusOld)
  wp_rv64_nbranch_frame br, F, hF

theorem walkInitEmptyFailOrNonzeroFramedNBranch_pre
    (base listLen raVal statusOld : Word) (F : Assertion) (hF : F.pcFree) :
    (walkInitEmptyFailOrNonzeroFramedNBranch base listLen raVal statusOld F hF).pre =
      (walkInitEmptyFailStatusPre listLen raVal statusOld ** F) := by
  rfl

/-- Zero/nonzero walk-init split carrying the ABI output buffer across both exits. -/
def walkInitEmptyFailOrNonzeroOutputNBranch
    (base listLen raVal statusOld outBase : Word) :
    WP.NBranch base (walkInitEmptyFailStatusCode base) :=
  walkInitEmptyFailOrNonzeroFramedNBranch base listLen raVal statusOld
    (bytesRegionAny outBase outputSize) (bytesRegionAny_pcFree outBase outputSize)

theorem walkInitEmptyFailOrNonzeroOutputNBranch_pre
    (base listLen raVal statusOld outBase : Word) :
    (walkInitEmptyFailOrNonzeroOutputNBranch base listLen raVal statusOld outBase).pre =
      (walkInitEmptyFailStatusPre listLen raVal statusOld **
        bytesRegionAny outBase outputSize) := by
  rw [walkInitEmptyFailOrNonzeroOutputNBranch,
    walkInitEmptyFailOrNonzeroFramedNBranch_pre]

/-- Walk-init classifier with the ABI output buffer framed across every exit. -/
def walkInitEmptyFailNotListFailShortLongOutputNBranch
    (base listBase listLen raVal t0Old t1Old outBase : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    WP.NBranch base (walkInitEmptyFailNotListFailShortLongCode base) :=
  walkInitEmptyFailNotListFailShortLongFramedNBranch base listBase listLen raVal
    t0Old t1Old listBytes listOff hsalign hoff hover hvalid
    (bytesRegionAny outBase outputSize) (bytesRegionAny_pcFree outBase outputSize)

theorem walkInitEmptyFailNotListFailShortLongOutputNBranch_pre
    (base listBase listLen raVal t0Old t1Old outBase : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    (walkInitEmptyFailNotListFailShortLongOutputNBranch base listBase listLen raVal t0Old t1Old
      outBase listBytes listOff hsalign hoff hover hvalid).pre =
      ((walkInitEmptyFailStatusPre listLen raVal (listBase + BitVec.ofNat 64 listOff) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion listBase listBytes) **
        bytesRegionAny outBase outputSize) := by
  rw [walkInitEmptyFailNotListFailShortLongOutputNBranch,
    walkInitEmptyFailNotListFailShortLongFramedNBranch_pre_expanded]

/-- Raw empty-input failure exit of the walk-init classifier, including the
    scratch/input frame that was carried across the classifier. -/
def walkInitEmptyFailOutputPost
    (listBase listLen raVal t0Old t1Old outBase : Word)
    (listBytes : List Byte) : Assertion :=
  ((walkInitEmptyFailStatusPost listLen raVal **
    ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion listBase listBytes)) **
    bytesRegionAny outBase outputSize)

/-- Raw not-list failure exit after the reason-erased failure endpoint. -/
def walkInitNotListFailOutputPost
    (listBase listLen raVal outBase : Word) (listBytes : List Byte)
    (listOff : Nat) (hoff : listOff < listBytes.length) : Assertion :=
  walkInitPrefixNotListFailStatusPost listBase listLen raVal listBytes listOff hoff **
    bytesRegionAny outBase outputSize

/-- Raw short-list candidate exit, with the ABI output buffer preserved. -/
def walkInitShortListOutputPost
    (listBase listLen raVal outBase : Word) (listBytes : List Byte)
    (listOff : Nat) (hoff : listOff < listBytes.length) : Assertion :=
  walkInitShortListCandidatePost listBase listLen raVal listBytes listOff hoff **
    bytesRegionAny outBase outputSize

/-- Raw long-list candidate exit, with the ABI output buffer preserved. -/
def walkInitLongListOutputPost
    (listBase listLen raVal outBase : Word) (listBytes : List Byte)
    (listOff : Nat) (hoff : listOff < listBytes.length) : Assertion :=
  walkInitLongListCandidatePost listBase listLen raVal listBytes listOff hoff **
    bytesRegionAny outBase outputSize

/-- The four raw exits of `walkInitEmptyFailNotListFailShortLongOutputNBranch`,
    named so generated proof code can target cases rather than list membership. -/
def walkInitEmptyFailNotListFailShortLongOutputExits
    (base listBase listLen raVal t0Old t1Old outBase : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hoff : listOff < listBytes.length) : List (Word × Assertion) :=
  [ (failStatusReturnExit raVal,
      walkInitEmptyFailOutputPost listBase listLen raVal t0Old t1Old outBase listBytes)
  , (failStatusReturnExit raVal,
      walkInitNotListFailOutputPost listBase listLen raVal outBase listBytes listOff hoff)
  , (base + 124,
      walkInitShortListOutputPost listBase listLen raVal outBase listBytes listOff hoff)
  , (base + 28,
      walkInitLongListOutputPost listBase listLen raVal outBase listBytes listOff hoff)
  ]

theorem walkInitEmptyFailNotListFailShortLongOutputNBranch_exits
    (base listBase listLen raVal t0Old t1Old outBase : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true) :
    (walkInitEmptyFailNotListFailShortLongOutputNBranch base listBase listLen raVal t0Old t1Old
      outBase listBytes listOff hsalign hoff hover hvalid).exits =
      walkInitEmptyFailNotListFailShortLongOutputExits base listBase listLen raVal t0Old t1Old
        outBase listBytes listOff hoff := by
  simp [walkInitEmptyFailNotListFailShortLongOutputNBranch,
    walkInitEmptyFailNotListFailShortLongFramedNBranch,
    walkInitEmptyFailNotListFailShortLongNBranch,
    walkInitEmptyFailOrPrefixBranch, walkInitPrefixListCheckOrNotListFailBranch,
    walkInitEmptyFailStatusBranch, walkInitPrefixListCheckBranch,
    walkInitShortLongCheckBranch, walkInitEmptyFailStatusPost,
    walkInitEmptyFailNotListFailShortLongOutputExits, walkInitEmptyFailOutputPost,
    walkInitNotListFailOutputPost, walkInitShortListOutputPost, walkInitLongListOutputPost,
    failStatusReturnExit, statusReturnExit, WP.CFG.nbranchFrameR, WP.NBranch.frameR,
    WP.CFG.branchFrameR, WP.Branch.frameR, WP.CFG.branchSeqNotTakenNBranchDisjoint,
    WP.Branch.seqNotTakenNBranchDisjoint, WP.CFG.branchSeqNotTakenBlockDisjoint,
    WP.CFG.branchSeqTakenBlockDisjoint, WP.CFG.branchSeqNotTakenDisjoint,
    WP.CFG.branchSeqTakenDisjoint, WP.Branch.seqNotTakenDisjoint,
    WP.Branch.seqTakenDisjoint, WP.CFG.nbranchOfBranch, WP.NBranch.ofBranch,
    WP.Branch.ofSpec, WP.CFG.block, WP.Triple.ofSpec]

/-- Case-oriented weakening for the four raw walk-init classifier exits. This is
    the generated-proof entry point: callers provide one entailment per control
    case, and the membership-map proof is built here. -/
def walkInitEmptyFailNotListFailShortLongOutputCaseNBranch
    (base listBase listLen raVal t0Old t1Old outBase : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (emptyPost notListPost shortPost longPost : Assertion)
    (hEmpty : WP.Entails
      (walkInitEmptyFailOutputPost listBase listLen raVal t0Old t1Old outBase listBytes)
      emptyPost)
    (hNotList : WP.Entails
      (walkInitNotListFailOutputPost listBase listLen raVal outBase listBytes listOff hoff)
      notListPost)
    (hShort : WP.Entails
      (walkInitShortListOutputPost listBase listLen raVal outBase listBytes listOff hoff)
      shortPost)
    (hLong : WP.Entails
      (walkInitLongListOutputPost listBase listLen raVal outBase listBytes listOff hoff)
      longPost) :
    WP.NBranch base (walkInitEmptyFailNotListFailShortLongCode base) := by
  let br := walkInitEmptyFailNotListFailShortLongOutputNBranch base listBase listLen raVal
    t0Old t1Old outBase listBytes listOff hsalign hoff hover hvalid
  wp_rv64_nbranch_weaken_posts4_with br,
    (walkInitEmptyFailNotListFailShortLongOutputNBranch_exits base listBase listLen raVal
      t0Old t1Old outBase listBytes listOff hsalign hoff hover hvalid),
    hEmpty, hNotList, hShort, hLong

theorem walkInitEmptyFailNotListFailShortLongOutputCaseNBranch_pre
    (base listBase listLen raVal t0Old t1Old outBase : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (emptyPost notListPost shortPost longPost : Assertion)
    (hEmpty : WP.Entails
      (walkInitEmptyFailOutputPost listBase listLen raVal t0Old t1Old outBase listBytes)
      emptyPost)
    (hNotList : WP.Entails
      (walkInitNotListFailOutputPost listBase listLen raVal outBase listBytes listOff hoff)
      notListPost)
    (hShort : WP.Entails
      (walkInitShortListOutputPost listBase listLen raVal outBase listBytes listOff hoff)
      shortPost)
    (hLong : WP.Entails
      (walkInitLongListOutputPost listBase listLen raVal outBase listBytes listOff hoff)
      longPost) :
    (walkInitEmptyFailNotListFailShortLongOutputCaseNBranch base listBase listLen raVal
      t0Old t1Old outBase listBytes listOff hsalign hoff hover hvalid emptyPost notListPost
      shortPost longPost hEmpty hNotList hShort hLong).pre =
      (walkInitEmptyFailNotListFailShortLongOutputNBranch base listBase listLen raVal t0Old t1Old
        outBase listBytes listOff hsalign hoff hover hvalid).pre := by
  rfl

theorem walkInitEmptyFailNotListFailShortLongOutputCaseNBranch_exits
    (base listBase listLen raVal t0Old t1Old outBase : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (emptyPost notListPost shortPost longPost : Assertion)
    (hEmpty : WP.Entails
      (walkInitEmptyFailOutputPost listBase listLen raVal t0Old t1Old outBase listBytes)
      emptyPost)
    (hNotList : WP.Entails
      (walkInitNotListFailOutputPost listBase listLen raVal outBase listBytes listOff hoff)
      notListPost)
    (hShort : WP.Entails
      (walkInitShortListOutputPost listBase listLen raVal outBase listBytes listOff hoff)
      shortPost)
    (hLong : WP.Entails
      (walkInitLongListOutputPost listBase listLen raVal outBase listBytes listOff hoff)
      longPost) :
    (walkInitEmptyFailNotListFailShortLongOutputCaseNBranch base listBase listLen raVal
      t0Old t1Old outBase listBytes listOff hsalign hoff hover hvalid emptyPost notListPost
      shortPost longPost hEmpty hNotList hShort hLong).exits =
      [ (failStatusReturnExit raVal, emptyPost)
      , (failStatusReturnExit raVal, notListPost)
      , (base + 124, shortPost)
      , (base + 28, longPost)
      ] := by
  rfl

/-- Turn raw walk-init exits into a caller-provided semantic exit list. The map
    proof remains available for unusual generated control-flow shapes; prefer
    `walkInitEmptyFailNotListFailShortLongOutputCaseNBranch` when mapping the
    standard four classifier cases. -/
def walkInitEmptyFailNotListFailShortLongOutputMappedNBranch
    (base listBase listLen raVal t0Old t1Old outBase : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (exits : List (Word × Assertion))
    (hmap : ∀ ex ∈
      (walkInitEmptyFailNotListFailShortLongOutputNBranch base listBase listLen raVal t0Old t1Old
        outBase listBytes listOff hsalign hoff hover hvalid).exits,
      ∃ ex' ∈ exits, ex'.1 = ex.1 ∧ WP.Entails ex.2 ex'.2) :
    WP.NBranch base (walkInitEmptyFailNotListFailShortLongCode base) := by
  let br := walkInitEmptyFailNotListFailShortLongOutputNBranch base listBase listLen raVal
    t0Old t1Old outBase listBytes listOff hsalign hoff hover hvalid
  wp_rv64_nbranch_weaken_posts br, exits, hmap

theorem walkInitEmptyFailNotListFailShortLongOutputMappedNBranch_pre
    (base listBase listLen raVal t0Old t1Old outBase : Word)
    (listBytes : List Byte) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (exits : List (Word × Assertion))
    (hmap : ∀ ex ∈
      (walkInitEmptyFailNotListFailShortLongOutputNBranch base listBase listLen raVal t0Old t1Old
        outBase listBytes listOff hsalign hoff hover hvalid).exits,
      ∃ ex' ∈ exits, ex'.1 = ex.1 ∧ WP.Entails ex.2 ex'.2) :
    (walkInitEmptyFailNotListFailShortLongOutputMappedNBranch base listBase listLen raVal
      t0Old t1Old outBase listBytes listOff hsalign hoff hover hvalid exits hmap).pre =
      (walkInitEmptyFailNotListFailShortLongOutputNBranch base listBase listLen raVal t0Old t1Old
        outBase listBytes listOff hsalign hoff hover hvalid).pre := by
  rfl

/-- Result portion of the ABI postcondition.  Success is exactly
    `decodeWithdrawal input = some w`; failure is exactly `decodeWithdrawal input = none`.
    The static schema above is not consulted here except through the fixed output size. -/
def resultPost (input : List Byte) (outBase : Word) : Assertion :=
  match decodeWithdrawal input with
  | some w =>
      ((.x10 ↦ᵣ (0 : Word)) ** bytesRegion outBase (successBytes w) **
        ⌜decodeWithdrawal input = some w⌝)
  | none =>
      ((.x10 ↦ᵣ (1 : Word)) ** bytesRegionAny outBase outputSize **
        ⌜decodeWithdrawal input = none⌝)

theorem resultPost_success {input : List Byte} {outBase : Word} {w : Withdrawal}
    (hdec : decodeWithdrawal input = some w) :
    resultPost input outBase =
      ((.x10 ↦ᵣ (0 : Word)) ** bytesRegion outBase (successBytes w) **
        ⌜decodeWithdrawal input = some w⌝) := by
  unfold resultPost
  rw [hdec]

theorem resultPost_failure {input : List Byte} {outBase : Word}
    (hdec : decodeWithdrawal input = none) :
    resultPost input outBase =
      ((.x10 ↦ᵣ (1 : Word)) ** bytesRegionAny outBase outputSize **
        ⌜decodeWithdrawal input = none⌝) := by
  unfold resultPost
  rw [hdec]

/-- Disjunctive public view of the ABI result.  The success side carries a
    decoded withdrawal witness and its output bytes; the failure side carries
    only the reason-erased `decodeWithdrawal input = none` fact. -/
def resultDisjPost (input : List Byte) (outBase : Word) : Assertion :=
  fun h =>
    (∃ w : Withdrawal,
      ((.x10 ↦ᵣ (0 : Word)) ** bytesRegion outBase (successBytes w) **
        ⌜decodeWithdrawal input = some w⌝) h) ∨
    (((.x10 ↦ᵣ (1 : Word)) ** bytesRegionAny outBase outputSize **
      ⌜decodeWithdrawal input = none⌝) h)

/-- The stronger match-shaped result post implies the explicit disjunctive view. -/
theorem resultPost_entails_resultDisjPost
    (input : List Byte) (outBase : Word) :
    WP.Entails (resultPost input outBase) (resultDisjPost input outBase) := by
  intro h hp
  unfold resultPost at hp
  unfold resultDisjPost
  cases hdec : decodeWithdrawal input with
  | none =>
      rw [hdec] at hp
      exact Or.inr hp
  | some w =>
      rw [hdec] at hp
      exact Or.inl ⟨w, hp⟩

/-- ABI resources carried by the zero/nonzero split for the empty input case. -/
def emptyInputAbiFrame (inputBase outBase : Word) : Assertion :=
  bytesRegion inputBase [] ** bytesRegionAny outBase outputSize

theorem emptyInputAbiFrame_pcFree (inputBase outBase : Word) :
    (emptyInputAbiFrame inputBase outBase).pcFree := by
  unfold emptyInputAbiFrame
  exact pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegionAny_pcFree _ _)

/-- A minimal ABI precondition for a withdrawal decoder entry.  A concrete
    program proof may strengthen this with scratch registers, stack cells, or
    helper-code frames through the WP precondition. -/
def abiPre (inputBase outBase raVal : Word) (input : List Byte) : Assertion :=
  ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 input.length) **
   (.x12 ↦ᵣ outBase) ** (.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) **
   bytesRegion inputBase input ** bytesRegionAny outBase outputSize)

/-- ABI postcondition common to any implementation of `withdrawal_decode`.
    It preserves `ra`, preserves the input bytes, and reports the pure decoder
    result through `resultPost`. Scratch and argument registers not mentioned
    here may be described by a stronger implementation-specific postcondition. -/
def abiPost (inputBase outBase raVal : Word) (input : List Byte) : Assertion :=
  ((.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion inputBase input **
    resultPost input outBase)

/-- ABI postcondition with an explicit success/failure disjunction over the Lean
    decoder result.  This is the public characterization shape; `abiPost` above
    is kept as the stronger match-shaped implementation post used by existing
    proofs. -/
def abiDisjPost (inputBase outBase raVal : Word) (input : List Byte) : Assertion :=
  ((.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion inputBase input **
    resultDisjPost input outBase)

/-- The existing ABI postcondition implies the explicit disjunctive view. -/
theorem abiPost_entails_abiDisjPost
    (inputBase outBase raVal : Word) (input : List Byte) :
    WP.Entails (abiPost inputBase outBase raVal input)
      (abiDisjPost inputBase outBase raVal input) := by
  intro h hp
  unfold abiPost at hp
  unfold abiDisjPost
  exact sepConj_mono_right
    (sepConj_mono_right
      (sepConj_mono_right (resultPost_entails_resultDisjPost input outBase))) h hp

/-- Empty-input resources plus the pure decoder failure fact. -/
def emptyInputDecodeFrame (inputBase outBase : Word) : Assertion :=
  emptyInputAbiFrame inputBase outBase ** ⌜decodeWithdrawal ([] : List Byte) = none⌝

theorem emptyInputDecodeFrame_pcFree (inputBase outBase : Word) :
    (emptyInputDecodeFrame inputBase outBase).pcFree := by
  unfold emptyInputDecodeFrame
  exact pcFree_sepConj (emptyInputAbiFrame_pcFree inputBase outBase) pcFree_pure

/-- Strong post for the empty-input walk-init failure arm. It keeps the exact
    resource spine produced by the shallow walk-init slice and adds the pure
    Lean decoder failure fact. -/
def emptyInputFailurePost (inputBase outBase raVal : Word) : Assertion :=
  ((((.x1 ↦ᵣ raVal) ** (.x10 ↦ᵣ (1 : Word))) ** (.x11 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) ** ⌜(0 : Word) = (0 : Word)⌝) **
    (bytesRegion inputBase [] ** bytesRegionAny outBase outputSize) **
    ⌜decodeWithdrawal ([] : List Byte) = none⌝)

/-- The shallow walk-init WP split specialized to empty input, with its head exit
    mapped to a semantic failure post carrying decodeWithdrawal_nil. The nonzero
    exit remains open and impossible under the zero length value. -/
def walkInitEmptyInputFailureNBranch
    (base inputBase outBase raVal statusOld : Word) :
    WP.NBranch base (walkInitEmptyFailStatusCode base) := by
  let frame := emptyInputAbiFrame inputBase outBase
  let br := walkInitEmptyFailOrNonzeroFramedNBranch base (0 : Word) raVal statusOld
    frame (emptyInputAbiFrame_pcFree inputBase outBase)
  have hhead : WP.Entails
      (walkInitEmptyFailStatusPost (0 : Word) raVal ** frame)
      (emptyInputFailurePost inputBase outBase raVal) := by
    intro h hp
    unfold emptyInputFailurePost
    dsimp [frame] at hp
    unfold emptyInputAbiFrame walkInitEmptyFailStatusPost failStatusReturnPost statusReturnPost
      walkInitZeroPost at hp
    rw [show (⌜decodeWithdrawal ([] : List Byte) = none⌝ : Assertion) = empAssertion by
      funext h
      unfold EvmAsm.Rv64.pure EvmAsm.Rv64.empAssertion
      apply propext
      constructor
      · intro h_p
        exact h_p.1
      · intro h_empty
        exact ⟨h_empty, decodeWithdrawal_nil⟩]
    simp only [sepConj_emp_right']
    simpa using hp
  exact WP.CFG.nbranchWeakenHeadPost br (by rfl) hhead

theorem walkInitEmptyInputFailureNBranch_pre
    (base inputBase outBase raVal statusOld : Word) :
    (walkInitEmptyInputFailureNBranch base inputBase outBase raVal statusOld).pre =
      (walkInitEmptyFailStatusPre (0 : Word) raVal statusOld **
        emptyInputAbiFrame inputBase outBase) := by
  rfl

/-- ABI resources preserved by the reason-erased failure endpoint.  The pure
    failure fact is supplied by the path that selected this endpoint, not by the
    static schema. -/
def failStatusReturnAbiFrame (inputBase outBase : Word) (input : List Byte) : Assertion :=
  ((.x0 ↦ᵣ (0 : Word)) ** bytesRegion inputBase input **
    bytesRegionAny outBase outputSize ** ⌜decodeWithdrawal input = none⌝)

theorem failStatusReturnAbiFrame_pcFree
    (inputBase outBase : Word) (input : List Byte) :
    (failStatusReturnAbiFrame inputBase outBase input).pcFree := by
  unfold failStatusReturnAbiFrame
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj (bytesRegion_pcFree _ _)
      (pcFree_sepConj (bytesRegionAny_pcFree _ _) pcFree_pure))

/-- ABI-facing precondition for a failure endpoint reached after a path has
    established that the pure withdrawal decoder fails. -/
def failStatusReturnAbiPre
    (inputBase outBase raVal statusOld : Word) (input : List Byte) : Assertion :=
  failStatusReturnPre raVal statusOld ** failStatusReturnAbiFrame inputBase outBase input

/-- WP certificate adapting the reason-erased failure endpoint to the public ABI
    postcondition.  The exact failure reason is intentionally absent; only the
    pure `decodeWithdrawal input = none` case fact is used to expose the unified
    postcondition's failure disjunct. -/
def failStatusReturnAbiCert
    (base inputBase outBase raVal statusOld : Word) (input : List Byte) :
    WP.CFG.Cert base (failStatusReturnExit raVal) (failStatusReturnCode base)
      (abiPost inputBase outBase raVal input) := by
  have hfail := failStatusReturn_spec_within base raVal statusOld
  have hframed := cpsTripleWithin_frameR
    (failStatusReturnAbiFrame inputBase outBase input)
    (failStatusReturnAbiFrame_pcFree inputBase outBase input) hfail
  exact WP.CFG.block (by
    intro h hp
    have hpCase := hp
    unfold failStatusReturnPost statusReturnPost failStatusReturnAbiFrame at hp hpCase
    extract_pure hpCase
    obtain ⟨hdec, _hpRest⟩ := hpCase
    unfold abiPost
    rw [resultPost_failure hdec]
    xperm_hyp hp) hframed

/-- Verified ABI-facing failure endpoint. -/
theorem failStatusReturn_abiPost_spec_within
    (base inputBase outBase raVal statusOld : Word) (input : List Byte) :
    cpsTripleWithin (failStatusReturnAbiCert base inputBase outBase raVal statusOld input).nSteps
      base (failStatusReturnExit raVal) (failStatusReturnCode base)
      (failStatusReturnAbiPre inputBase outBase raVal statusOld input)
      (abiPost inputBase outBase raVal input) :=
  by
    unfold failStatusReturnAbiPre
    exact (failStatusReturnAbiCert base inputBase outBase raVal statusOld input).sound

/-- ABI resources preserved by the success endpoint after the field decoders have
    populated the output struct with the pure decoder result bytes. -/
def successStatusReturnAbiFrame
    (inputBase outBase : Word) (input : List Byte) (w : Withdrawal) : Assertion :=
  ((.x0 ↦ᵣ (0 : Word)) ** bytesRegion inputBase input **
    bytesRegion outBase (successBytes w) ** ⌜decodeWithdrawal input = some w⌝)

theorem successStatusReturnAbiFrame_pcFree
    (inputBase outBase : Word) (input : List Byte) (w : Withdrawal) :
    (successStatusReturnAbiFrame inputBase outBase input w).pcFree := by
  unfold successStatusReturnAbiFrame
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj (bytesRegion_pcFree _ _)
      (pcFree_sepConj (bytesRegion_pcFree _ _) pcFree_pure))

/-- ABI-facing precondition for a success endpoint reached after a path has
    established the decoded withdrawal and written its output bytes. -/
def successStatusReturnAbiPre
    (inputBase outBase raVal statusOld : Word) (input : List Byte)
    (w : Withdrawal) : Assertion :=
  successStatusReturnPre raVal statusOld ** successStatusReturnAbiFrame inputBase outBase input w

/-- WP certificate adapting the success endpoint to the public ABI postcondition. -/
def successStatusReturnAbiCert
    (base inputBase outBase raVal statusOld : Word) (input : List Byte)
    (w : Withdrawal) :
    WP.CFG.Cert base (successStatusReturnExit raVal) (successStatusReturnCode base)
      (abiPost inputBase outBase raVal input) := by
  have hsuccess := successStatusReturn_spec_within base raVal statusOld
  have hframed := cpsTripleWithin_frameR
    (successStatusReturnAbiFrame inputBase outBase input w)
    (successStatusReturnAbiFrame_pcFree inputBase outBase input w) hsuccess
  exact WP.CFG.block (by
    intro h hp
    have hpCase := hp
    unfold successStatusReturnPost statusReturnPost successStatusReturnAbiFrame at hp hpCase
    extract_pure hpCase
    obtain ⟨hdec, _hpRest⟩ := hpCase
    unfold abiPost
    rw [resultPost_success hdec]
    xperm_hyp hp) hframed

/-- Verified ABI-facing success endpoint. -/
theorem successStatusReturn_abiPost_spec_within
    (base inputBase outBase raVal statusOld : Word) (input : List Byte)
    (w : Withdrawal) :
    cpsTripleWithin (successStatusReturnAbiCert base inputBase outBase raVal statusOld input w).nSteps
      base (successStatusReturnExit raVal) (successStatusReturnCode base)
      (successStatusReturnAbiPre inputBase outBase raVal statusOld input w)
      (abiPost inputBase outBase raVal input) :=
  by
    unfold successStatusReturnAbiPre
    exact (successStatusReturnAbiCert base inputBase outBase raVal statusOld input w).sound

/-- A WP-facing certificate that a concrete control-flow proof implements the
    withdrawal decoder ABI.  The computed precondition is `cfg.pre`, so generated
    proofs can add whatever scratch resources their chosen program needs. -/
abbrev Cert (entry exit_ : Word) (cr : CodeReq)
    (inputBase outBase raVal : Word) (input : List Byte) :=
  WP.CFG.Cert entry exit_ cr (abiPost inputBase outBase raVal input)

def certPre {entry exit_ : Word} {cr : CodeReq}
    {inputBase outBase raVal : Word} {input : List Byte}
    (cert : Cert entry exit_ cr inputBase outBase raVal input) : Assertion :=
  cert.pre

theorem certSound {entry exit_ : Word} {cr : CodeReq}
    {inputBase outBase raVal : Word} {input : List Byte}
    (cert : Cert entry exit_ cr inputBase outBase raVal input) :
    cpsTripleWithin cert.nSteps entry exit_ cr cert.pre
      (abiPost inputBase outBase raVal input) :=
  cert.sound

/-- ABI-facing certificate with the explicit disjunctive success/failure post. -/
abbrev DisjCert (entry exit_ : Word) (cr : CodeReq)
    (inputBase outBase raVal : Word) (input : List Byte) :=
  WP.CFG.Cert entry exit_ cr (abiDisjPost inputBase outBase raVal input)

/-- The computed precondition of a disjunctive withdrawal decoder certificate. -/
def disjCertPre {entry exit_ : Word} {cr : CodeReq}
    {inputBase outBase raVal : Word} {input : List Byte}
    (cert : DisjCert entry exit_ cr inputBase outBase raVal input) : Assertion :=
  cert.pre

/-- Any existing ABI-facing certificate can be viewed through the explicit
    disjunctive postcondition without changing its WP precondition. -/
def toDisjCert {entry exit_ : Word} {cr : CodeReq}
    {inputBase outBase raVal : Word} {input : List Byte}
    (cert : Cert entry exit_ cr inputBase outBase raVal input) :
    DisjCert entry exit_ cr inputBase outBase raVal input :=
  WP.CFG.weakenPost cert (abiPost_entails_abiDisjPost inputBase outBase raVal input)

/-- Viewing an existing certificate through the disjunctive post preserves the
    computed weakest precondition. -/
theorem toDisjCert_pre {entry exit_ : Word} {cr : CodeReq}
    {inputBase outBase raVal : Word} {input : List Byte}
    (cert : Cert entry exit_ cr inputBase outBase raVal input) :
    (toDisjCert cert).pre = cert.pre :=
  rfl

/-- Top-level disjunctive characterization theorem: an implementation certified
    against `abiPost` also proves the RISC-V code returns the same success/failure
    case as the Lean `decodeWithdrawal` function. -/
theorem certSound_disj {entry exit_ : Word} {cr : CodeReq}
    {inputBase outBase raVal : Word} {input : List Byte}
    (cert : Cert entry exit_ cr inputBase outBase raVal input) :
    cpsTripleWithin cert.nSteps entry exit_ cr cert.pre
      (abiDisjPost inputBase outBase raVal input) :=
  cpsTripleWithin_weaken (fun _ hp => hp)
    (abiPost_entails_abiDisjPost inputBase outBase raVal input) cert.sound

/-- Soundness theorem for certificates that are built directly against the
    explicit disjunctive post. -/
theorem disjCertSound {entry exit_ : Word} {cr : CodeReq}
    {inputBase outBase raVal : Word} {input : List Byte}
    (cert : DisjCert entry exit_ cr inputBase outBase raVal input) :
    cpsTripleWithin cert.nSteps entry exit_ cr cert.pre
      (abiDisjPost inputBase outBase raVal input) :=
  cert.sound

/-- Package an implementation triple as a withdrawal decoder certificate. -/
def ofSpec {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {pre : Assertion} {inputBase outBase raVal : Word} {input : List Byte}
    (h : cpsTripleWithin nSteps entry exit_ cr pre
      (abiPost inputBase outBase raVal input)) :
    Cert entry exit_ cr inputBase outBase raVal input :=
  WP.CFG.block (WP.Entails.refl _) h

end WithdrawalDecode
end EvmAsm.Rv64.RLP
