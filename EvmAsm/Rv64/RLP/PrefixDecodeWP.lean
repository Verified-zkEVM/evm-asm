/-
  EvmAsm.Rv64.RLP.PrefixDecodeWP

  WP-facing proof for a compact RLP prefix decoder. The target is generic RLP
  prefix information, not a schema-specific datatype decoder.
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.WP
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XCancelStruct
import EvmAsm.Rv64.RLP.Phase1
import EvmAsm.EL.RLP.PrefixDecode

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.EL.RLP

namespace PrefixDecode

/-- Numeric ABI code for the pure RLP prefix class. Zero is reserved for the
    empty-input failure case. -/
def prefixClassCode : PrefixClass → Word
  | .singleByte => (1 : Word)
  | .shortBytes => (2 : Word)
  | .longBytes => (3 : Word)
  | .shortList => (4 : Word)
  | .longList => (5 : Word)

/-- Header-byte count as an RV64 word. -/
def prefixHeaderBytesWord (pfx : Byte) : Word :=
  BitVec.ofNat 64 (rlpPrefixHeaderBytes pfx)

/-- Compact executable prefix decoder.

Inputs: `a0` = input base, `a1` = input length, `ra` = return address.
Outputs: `a0` = status (`0` success, `1` empty input), `a1` = class code,
`a2` = header-byte count. Scratch: `t0=x5`, `t1=x6`. -/
def prog : List Instr :=
  [ .BEQ .x11 .x0 (120 : BitVec 13),       -- 0  empty input -> idx 30
    .LBU .x5 .x10 0,                       -- 1  prefix
    .ADDI .x10 .x0 (0x80 : BitVec 12),    -- 2
    .BLTU .x5 .x10 (44 : BitVec 13),       -- 3  single byte -> idx 14
    .ADDI .x10 .x0 (0xb8 : BitVec 12),    -- 4
    .BLTU .x5 .x10 (52 : BitVec 13),      -- 5  short bytes -> idx 18
    .ADDI .x10 .x0 (0xc0 : BitVec 12),    -- 6
    .BLTU .x5 .x10 (60 : BitVec 13),      -- 7  long bytes -> idx 22
    .ADDI .x10 .x0 (0xf8 : BitVec 12),    -- 8
    .BLTU .x5 .x10 (68 : BitVec 13),      -- 9  short list -> idx 26
    .LI .x10 (0 : Word),                   -- 10 long list
    .LI .x11 (5 : Word),                   -- 11
    .ADDI .x12 .x5 (-246 : BitVec 12),     -- 12 header = pfx - 0xf6
    .JALR .x0 .x1 0,                       -- 13
    .LI .x10 (0 : Word),                   -- 14 single byte
    .LI .x11 (1 : Word),                   -- 15
    .LI .x12 (0 : Word),                   -- 16
    .JALR .x0 .x1 0,                       -- 17
    .LI .x10 (0 : Word),                   -- 18 short bytes
    .LI .x11 (2 : Word),                   -- 19
    .LI .x12 (1 : Word),                   -- 20
    .JALR .x0 .x1 0,                       -- 21
    .LI .x10 (0 : Word),                   -- 22 long bytes
    .LI .x11 (3 : Word),                   -- 23
    .ADDI .x12 .x5 (-182 : BitVec 12),     -- 24 header = pfx - 0xb6
    .JALR .x0 .x1 0,                       -- 25
    .LI .x10 (0 : Word),                   -- 26 short list
    .LI .x11 (4 : Word),                   -- 27
    .LI .x12 (1 : Word),                   -- 28
    .JALR .x0 .x1 0,                       -- 29
    .LI .x10 (1 : Word),                   -- 30 empty input
    .LI .x11 (0 : Word),                   -- 31
    .LI .x12 (0 : Word),                   -- 32
    .JALR .x0 .x1 0 ]                      -- 33

theorem prog_length : prog.length = 34 := rfl

private theorem prog_code_bound : 4 * prog.length < 2 ^ 64 := by
  rw [prog_length]
  norm_num


/-- The embedded classifier slice uses the existing Phase 1 cascade layout. -/
def classifierProg : Program :=
  rlp_phase1_classifier_prog (44 : BitVec 13) (52 : BitVec 13)
    (60 : BitVec 13) (68 : BitVec 13)

theorem classifierProg_length : classifierProg.length = 8 := rfl

abbrev classifierCode (base : Word) : CodeReq :=
  rlp_phase1_classifier_code (44 : BitVec 13) (52 : BitVec 13)
    (60 : BitVec 13) (68 : BitVec 13) (base + 8)


private theorem classifier_step0_slice :
    (prog.drop 2).take (rlp_phase1_step_prog (0x80 : BitVec 12) (44 : BitVec 13)).length =
      rlp_phase1_step_prog (0x80 : BitVec 12) (44 : BitVec 13) := rfl

private theorem classifier_step1_slice :
    (prog.drop 4).take (rlp_phase1_step_prog (0xb8 : BitVec 12) (52 : BitVec 13)).length =
      rlp_phase1_step_prog (0xb8 : BitVec 12) (52 : BitVec 13) := rfl

private theorem classifier_step2_slice :
    (prog.drop 6).take (rlp_phase1_step_prog (0xc0 : BitVec 12) (60 : BitVec 13)).length =
      rlp_phase1_step_prog (0xc0 : BitVec 12) (60 : BitVec 13) := rfl

private theorem classifier_step3_slice :
    (prog.drop 8).take (rlp_phase1_step_prog (0xf8 : BitVec 12) (68 : BitVec 13)).length =
      rlp_phase1_step_prog (0xf8 : BitVec 12) (68 : BitVec 13) := rfl

private theorem classifierCode_mono_code (base : Word) :
    ∀ a i, classifierCode base a = some i → CodeReq.ofProg base prog a = some i := by
  unfold classifierCode rlp_phase1_classifier_code
  apply CodeReq.union_sub
  · exact CodeReq.ofProg_mono_sub base (base + 8) prog
      (rlp_phase1_step_prog (0x80 : BitVec 12) (44 : BitVec 13)) 2
      (by bv_omega) classifier_step0_slice
      (by rw [prog_length, rlp_phase1_step_prog]; norm_num) prog_code_bound
  · apply CodeReq.union_sub
    · exact CodeReq.ofProg_mono_sub base ((base + 8) + 8) prog
        (rlp_phase1_step_prog (0xb8 : BitVec 12) (52 : BitVec 13)) 4
        (by bv_omega) classifier_step1_slice
        (by rw [prog_length, rlp_phase1_step_prog]; norm_num) prog_code_bound
    · apply CodeReq.union_sub
      · exact CodeReq.ofProg_mono_sub base ((base + 8) + 16) prog
          (rlp_phase1_step_prog (0xc0 : BitVec 12) (60 : BitVec 13)) 6
          (by bv_omega) classifier_step2_slice
          (by rw [prog_length, rlp_phase1_step_prog]; norm_num) prog_code_bound
      · exact CodeReq.ofProg_mono_sub base ((base + 8) + 24) prog
          (rlp_phase1_step_prog (0xf8 : BitVec 12) (68 : BitVec 13)) 8
          (by bv_omega) classifier_step3_slice
          (by rw [prog_length, rlp_phase1_step_prog]; norm_num) prog_code_bound

abbrev code (base : Word) : CodeReq :=
  CodeReq.ofProg base prog


private theorem signExtend13_44 :
    signExtend13 (44 : BitVec 13) = (44 : Word) := by decide

private theorem signExtend13_52 :
    signExtend13 (52 : BitVec 13) = (52 : Word) := by decide

private theorem signExtend13_60 :
    signExtend13 (60 : BitVec 13) = (60 : Word) := by decide

private theorem signExtend13_68 :
    signExtend13 (68 : BitVec 13) = (68 : Word) := by decide

/-- WP summary for the embedded Phase 1 classifier, lifted to this decoder's full code. -/
def classifierNBranch (base : Word) (pfx : Byte) (v10 : Word) :
    WP.NBranch (base + 8) (code base) :=
  WP.NBranch.extendCode
    (WP.NBranch.ofSpec
      (rlp_phase1_classifier_spec_class_within pfx v10 (base + 8)
        (44 : BitVec 13) (52 : BitVec 13) (60 : BitVec 13) (68 : BitVec 13)
        (base + 56) (base + 72) (base + 88) (base + 104) (base + 40)
        (by rw [signExtend13_44]; bv_omega)
        (by rw [signExtend13_52]; bv_omega)
        (by rw [signExtend13_60]; bv_omega)
        (by rw [signExtend13_68]; bv_omega)
        (by bv_omega)))
    (classifierCode_mono_code base)


theorem classifierNBranch_pre (base : Word) (pfx : Byte) (v10 : Word) :
    (classifierNBranch base pfx v10).pre =
      ((.x5 ↦ᵣ BitVec.setWidth 64 pfx) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10)) :=
  rfl

theorem classifierNBranch_exits (base : Word) (pfx : Byte) (v10 : Word) :
    (classifierNBranch base pfx v10).exits =
      [(base + 56, rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0x80
          (classifyPrefix pfx = .singleByte)),
       (base + 72, rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xB8
          (classifyPrefix pfx = .shortBytes)),
       (base + 88, rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xC0
          (classifyPrefix pfx = .longBytes)),
       (base + 104, rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xF8
          (classifyPrefix pfx = .shortList)),
       (base + 40, rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xF8
          (classifyPrefix pfx = .longList))] :=
  rfl


def returnExit (raVal : Word) : Word :=
  raVal &&& ~~~(1 : Word)

/-- Generic status/class/header return block used by this decoder and reusable by
    other small RLP classifiers. -/
def returnProg (status classCode headerBytes : Word) : List Instr :=
  [ .LI .x10 status
  , .LI .x11 classCode
  , .LI .x12 headerBytes
  , .JALR .x0 .x1 0
  ]

theorem returnProg_length (status classCode headerBytes : Word) :
    (returnProg status classCode headerBytes).length = 4 := rfl

def returnCode (base status classCode headerBytes : Word) : CodeReq :=
  CodeReq.ofProg base (returnProg status classCode headerBytes)

/-- WP-synthesized return block. The generated precondition owns only the three
    overwritten ABI output registers plus `ra`. -/
def returnCert (base raVal status classCode headerBytes : Word) :
    WP.CFG.Cert base (returnExit raVal) (returnCode base status classCode headerBytes)
      ((.x10 ↦ᵣ status) ** (.x11 ↦ᵣ classCode) ** (.x12 ↦ᵣ headerBytes) **
        (.x1 ↦ᵣ raVal)) := by
  unfold returnExit returnCode returnProg
  wp_rv64_leaf_synth

theorem returnCert_pre (base raVal status classCode headerBytes : Word) :
    (returnCert base raVal status classCode headerBytes).pre =
      (regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** (.x1 ↦ᵣ raVal)) := rfl

private def returnCertInProg (base addr raVal status classCode headerBytes : Word)
    (idx : Nat)
    (haddr : addr = base + BitVec.ofNat 64 (4 * idx))
    (hslice : (prog.drop idx).take (returnProg status classCode headerBytes).length =
      returnProg status classCode headerBytes)
    (hrange : idx + (returnProg status classCode headerBytes).length ≤ prog.length) :
    WP.CFG.Cert addr (returnExit raVal) (code base)
      ((.x10 ↦ᵣ status) ** (.x11 ↦ᵣ classCode) ** (.x12 ↦ᵣ headerBytes) **
        (.x1 ↦ᵣ raVal)) :=
  WP.CFG.extendCode (returnCert addr raVal status classCode headerBytes)
    (CodeReq.ofProg_mono_sub base addr prog (returnProg status classCode headerBytes) idx
      haddr hslice hrange (by rw [prog_length]; norm_num))

def emptyReturnCert (base raVal : Word) :
    WP.CFG.Cert (base + 120) (returnExit raVal) (code base)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal)) :=
  returnCertInProg base (base + 120) raVal (1 : Word) (0 : Word) (0 : Word) 30
    (by bv_omega) (by rfl) (by norm_num [prog, returnProg])

def singleByteReturnCert (base raVal : Word) :
    WP.CFG.Cert (base + 56) (returnExit raVal) (code base)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (1 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal)) :=
  returnCertInProg base (base + 56) raVal (0 : Word) (1 : Word) (0 : Word) 14
    (by bv_omega) (by rfl) (by norm_num [prog, returnProg])

def shortBytesReturnCert (base raVal : Word) :
    WP.CFG.Cert (base + 72) (returnExit raVal) (code base)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** (.x12 ↦ᵣ (1 : Word)) **
        (.x1 ↦ᵣ raVal)) :=
  returnCertInProg base (base + 72) raVal (0 : Word) (2 : Word) (1 : Word) 18
    (by bv_omega) (by rfl) (by norm_num [prog, returnProg])

def longBytesTailProg : List Instr :=
  [ .LI .x10 (0 : Word)
  , .LI .x11 (3 : Word)
  , .ADDI .x12 .x5 (-182 : BitVec 12)
  , .JALR .x0 .x1 0
  ]

theorem longBytesTailProg_length : longBytesTailProg.length = 4 := rfl

def longBytesTailCert (addr raVal pfx : Word) :
    WP.CFG.Cert addr (returnExit raVal) (CodeReq.ofProg addr longBytesTailProg)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
        (.x12 ↦ᵣ (pfx + signExtend12 (-182 : BitVec 12))) ** (.x5 ↦ᵣ pfx) **
        (.x1 ↦ᵣ raVal)) := by
  unfold returnExit longBytesTailProg
  wp_rv64_leaf_synth

def longBytesReturnCert (base raVal pfx : Word) :
    WP.CFG.Cert (base + 88) (returnExit raVal) (code base)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
        (.x12 ↦ᵣ (pfx + signExtend12 (-182 : BitVec 12))) ** (.x5 ↦ᵣ pfx) **
        (.x1 ↦ᵣ raVal)) :=
  WP.CFG.extendCode (longBytesTailCert (base + 88) raVal pfx)
    (CodeReq.ofProg_mono_sub base (base + 88) prog longBytesTailProg 22
      (by bv_omega) (by rfl) (by norm_num [prog, longBytesTailProg])
      (by rw [prog_length]; norm_num))

def shortListReturnCert (base raVal : Word) :
    WP.CFG.Cert (base + 104) (returnExit raVal) (code base)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (4 : Word)) ** (.x12 ↦ᵣ (1 : Word)) **
        (.x1 ↦ᵣ raVal)) :=
  returnCertInProg base (base + 104) raVal (0 : Word) (4 : Word) (1 : Word) 26
    (by bv_omega) (by rfl) (by norm_num [prog, returnProg])

def longListTailProg : List Instr :=
  [ .LI .x10 (0 : Word)
  , .LI .x11 (5 : Word)
  , .ADDI .x12 .x5 (-246 : BitVec 12)
  , .JALR .x0 .x1 0
  ]

theorem longListTailProg_length : longListTailProg.length = 4 := rfl

def longListTailCert (addr raVal pfx : Word) :
    WP.CFG.Cert addr (returnExit raVal) (CodeReq.ofProg addr longListTailProg)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (5 : Word)) **
        (.x12 ↦ᵣ (pfx + signExtend12 (-246 : BitVec 12))) ** (.x5 ↦ᵣ pfx) **
        (.x1 ↦ᵣ raVal)) := by
  unfold returnExit longListTailProg
  wp_rv64_leaf_synth

def longListReturnCert (base raVal pfx : Word) :
    WP.CFG.Cert (base + 40) (returnExit raVal) (code base)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (5 : Word)) **
        (.x12 ↦ᵣ (pfx + signExtend12 (-246 : BitVec 12))) ** (.x5 ↦ᵣ pfx) **
        (.x1 ↦ᵣ raVal)) :=
  WP.CFG.extendCode (longListTailCert (base + 40) raVal pfx)
    (CodeReq.ofProg_mono_sub base (base + 40) prog longListTailProg 10
      (by bv_omega) (by rfl) (by norm_num [prog, longListTailProg])
      (by rw [prog_length]; norm_num))


/-- Machine precondition for the prefix decoder. The only static data is the
    input byte region and the incoming register/scratch values. -/
def abiPre
    (inputBase raVal a2Old t0Old t1Old : Word) (input : List Byte) : Assertion :=
  ((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 input.length) **
    (.x12 ↦ᵣ a2Old) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
    (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion inputBase input)

/-- Match-shaped result postcondition. -/
def resultPost (input : List Byte) : Assertion :=
  match decodePrefixInfo input with
  | none =>
      ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6)
  | some (cls, headerBytes) =>
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ prefixClassCode cls) **
        (.x12 ↦ᵣ BitVec.ofNat 64 headerBytes) ** regOwn .x5 ** regOwn .x6)

/-- Full ABI postcondition: result registers plus preserved `x0`, `ra`, and input bytes. -/
def abiPost (inputBase raVal : Word) (input : List Byte) : Assertion :=
  resultPost input ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion inputBase input

/-- Public disjunctive view of the result. -/
def resultDisjPost (input : List Byte) : Assertion :=
  fun h =>
    (((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** ⌜decodePrefixInfo input = none⌝) h) ∨
    (∃ cls headerBytes,
      (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ prefixClassCode cls) **
          (.x12 ↦ᵣ BitVec.ofNat 64 headerBytes) ** regOwn .x5 ** regOwn .x6 **
          ⌜decodePrefixInfo input = some (cls, headerBytes)⌝) h))

/-- Full ABI postcondition with explicit success/failure disjunction. -/
def abiDisjPost (inputBase raVal : Word) (input : List Byte) : Assertion :=
  resultDisjPost input ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion inputBase input


private def classifierFrame
    (inputBase raVal : Word) (pfx : Byte) (rest : List Byte) : Assertion :=
  (.x1 ↦ᵣ raVal) ** regOwn .x6 ** regOwn .x11 ** regOwn .x12 **
    bytesRegion inputBase (pfx :: rest)

private theorem classifierFrame_pcFree
    (inputBase raVal : Word) (pfx : Byte) (rest : List Byte) :
    (classifierFrame inputBase raVal pfx rest).pcFree := by
  unfold classifierFrame
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regOwn
      (pcFree_sepConj pcFree_regOwn
        (pcFree_sepConj pcFree_regOwn (bytesRegion_pcFree _ _))))

private def singleByteReturnFrame
    (inputBase : Word) (pfx : Byte) (rest : List Byte) : Assertion :=
  regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x6 **
    bytesRegion inputBase (pfx :: rest) ** ⌜classifyPrefix pfx = .singleByte⌝

private theorem singleByteReturnFrame_pcFree
    (inputBase : Word) (pfx : Byte) (rest : List Byte) :
    (singleByteReturnFrame inputBase pfx rest).pcFree := by
  unfold singleByteReturnFrame
  exact pcFree_sepConj pcFree_regOwn
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regOwn
        (pcFree_sepConj (bytesRegion_pcFree _ _) pcFree_pure)))

/-- Single-byte endpoint adapted to the public prefix-decoder ABI post. -/
def singleByteAbiCert
    (base inputBase raVal : Word) (pfx : Byte) (rest : List Byte) :
    WP.CFG.Cert (base + 56) (returnExit raVal) (code base)
      (abiPost inputBase raVal (pfx :: rest)) := by
  let F := singleByteReturnFrame inputBase pfx rest
  refine WP.CFG.weakenPost
    (WP.CFG.frameR (singleByteReturnCert base raVal) F
      (singleByteReturnFrame_pcFree inputBase pfx rest)) ?_
  intro h hp
  unfold abiPost resultPost decodePrefixInfo
  unfold F singleByteReturnFrame at hp
  extract_pure hp
  obtain ⟨h_class, hp⟩ := hp
  simp [h_class, prefixClassCode, rlpPrefixHeaderBytes]
  xcancel_struct hp


private theorem classifierSingleByte_handoff
    (base inputBase raVal : Word) (pfx : Byte) (rest : List Byte) :
    WP.Entails
      (rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0x80
        (classifyPrefix pfx = .singleByte) ** classifierFrame inputBase raVal pfx rest)
      (singleByteAbiCert base inputBase raVal pfx rest).pre := by
  intro h hp
  change
    (((regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** (.x1 ↦ᵣ raVal)) **
      singleByteReturnFrame inputBase pfx rest) h)
  rw [rlp_phase1_exit_post_acc_unfold] at hp
  unfold classifierFrame at hp
  unfold singleByteReturnFrame
  have hp' := sepConj_mono_left
    (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (fun _ hp => hp)
        (sepConj_mono (regIs_implies_regOwn .x10) (fun _ hp => hp)))) h hp
  xperm_hyp hp'

private theorem signExtend12_neg182 :
    signExtend12 (-182 : BitVec 12) = (-182 : Word) := by decide

private theorem signExtend12_neg246 :
    signExtend12 (-246 : BitVec 12) = (-246 : Word) := by decide


/-- The match-shaped result post implies the public success/failure disjunction. -/
theorem resultPost_entails_resultDisjPost (input : List Byte) :
    WP.Entails (resultPost input) (resultDisjPost input) := by
  intro h hp
  unfold resultPost at hp
  unfold resultDisjPost
  cases hdec : decodePrefixInfo input with
  | none =>
      rw [hdec] at hp
      exact Or.inl (by
        rw [show (⌜(none : Option (PrefixClass × Nat)) = none⌝ : Assertion) = empAssertion by
          funext h
          unfold EvmAsm.Rv64.pure EvmAsm.Rv64.empAssertion
          apply propext
          constructor
          · intro h_p
            exact h_p.1
          · intro h_empty
            exact ⟨h_empty, rfl⟩]
        simp only [sepConj_emp_right']
        xperm_hyp hp)
  | some result =>
      rcases result with ⟨cls, headerBytes⟩
      rw [hdec] at hp
      exact Or.inr ⟨cls, headerBytes, by
        rw [show (⌜some (cls, headerBytes) = some (cls, headerBytes)⌝ : Assertion) = empAssertion by
          funext h
          unfold EvmAsm.Rv64.pure EvmAsm.Rv64.empAssertion
          apply propext
          constructor
          · intro h_p
            exact h_p.1
          · intro h_empty
            exact ⟨h_empty, rfl⟩]
        simp only [sepConj_emp_right']
        xperm_hyp hp⟩

/-- The match-shaped ABI post implies the explicit disjunctive ABI view. -/
theorem abiPost_entails_abiDisjPost
    (inputBase raVal : Word) (input : List Byte) :
    WP.Entails (abiPost inputBase raVal input)
      (abiDisjPost inputBase raVal input) := by
  intro h hp
  unfold abiPost at hp
  unfold abiDisjPost
  exact sepConj_mono_left (resultPost_entails_resultDisjPost input) h hp

/-- A WP-facing certificate that a concrete control-flow proof implements the
    prefix decoder ABI. The computed precondition is `cert.pre`. -/
abbrev Cert (entry exit_ : Word) (cr : CodeReq)
    (inputBase raVal : Word) (input : List Byte) :=
  WP.CFG.Cert entry exit_ cr (abiPost inputBase raVal input)

def certPre {entry exit_ : Word} {cr : CodeReq}
    {inputBase raVal : Word} {input : List Byte}
    (cert : Cert entry exit_ cr inputBase raVal input) : Assertion :=
  cert.pre

theorem certSound {entry exit_ : Word} {cr : CodeReq}
    {inputBase raVal : Word} {input : List Byte}
    (cert : Cert entry exit_ cr inputBase raVal input) :
    cpsTripleWithin cert.nSteps entry exit_ cr cert.pre
      (abiPost inputBase raVal input) :=
  cert.sound

/-- ABI-facing certificate with the explicit success/failure postcondition. -/
abbrev DisjCert (entry exit_ : Word) (cr : CodeReq)
    (inputBase raVal : Word) (input : List Byte) :=
  WP.CFG.Cert entry exit_ cr (abiDisjPost inputBase raVal input)

def disjCertPre {entry exit_ : Word} {cr : CodeReq}
    {inputBase raVal : Word} {input : List Byte}
    (cert : DisjCert entry exit_ cr inputBase raVal input) : Assertion :=
  cert.pre

/-- View an ABI certificate through the explicit disjunctive postcondition. -/
def toDisjCert {entry exit_ : Word} {cr : CodeReq}
    {inputBase raVal : Word} {input : List Byte}
    (cert : Cert entry exit_ cr inputBase raVal input) :
    DisjCert entry exit_ cr inputBase raVal input :=
  WP.CFG.weakenPost cert (abiPost_entails_abiDisjPost inputBase raVal input)

theorem toDisjCert_pre {entry exit_ : Word} {cr : CodeReq}
    {inputBase raVal : Word} {input : List Byte}
    (cert : Cert entry exit_ cr inputBase raVal input) :
    (toDisjCert cert).pre = cert.pre :=
  rfl

/-- Top-level disjunctive characterization theorem for any concrete prefix
    decoder certificate. -/
theorem certSound_disj {entry exit_ : Word} {cr : CodeReq}
    {inputBase raVal : Word} {input : List Byte}
    (cert : Cert entry exit_ cr inputBase raVal input) :
    cpsTripleWithin cert.nSteps entry exit_ cr cert.pre
      (abiDisjPost inputBase raVal input) :=
  cpsTripleWithin_weaken (fun _ hp => hp)
    (abiPost_entails_abiDisjPost inputBase raVal input) cert.sound

/-- Soundness theorem for certificates built directly against the disjunctive post. -/
theorem disjCertSound {entry exit_ : Word} {cr : CodeReq}
    {inputBase raVal : Word} {input : List Byte}
    (cert : DisjCert entry exit_ cr inputBase raVal input) :
    cpsTripleWithin cert.nSteps entry exit_ cr cert.pre
      (abiDisjPost inputBase raVal input) :=
  cert.sound

/-- Package an implementation triple as a prefix decoder certificate. -/
def ofSpec {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {pre : Assertion} {inputBase raVal : Word} {input : List Byte}
    (h : cpsTripleWithin nSteps entry exit_ cr pre
      (abiPost inputBase raVal input)) :
    Cert entry exit_ cr inputBase raVal input :=
  WP.CFG.block (WP.Entails.refl _) h

/-- RLP-generic arithmetic bridge for long byte-string prefix headers. -/
theorem headerBytesWord_longBytes (pfx : Byte) (h : classifyPrefix pfx = .longBytes) :
    (pfx.zeroExtend 64 : Word) + signExtend12 (-182 : BitVec 12) =
      prefixHeaderBytesWord pfx := by
  have hrange := (classifyPrefix_longBytes_iff pfx).mp h
  unfold prefixHeaderBytesWord rlpPrefixHeaderBytes
  rw [h, signExtend12_neg182]
  unfold rlpPrefixLongBytesHeaderBytes rlpPrefixLongBytesLenOfLen
  bv_omega

/-- RLP-generic arithmetic bridge for long list prefix headers. -/
theorem headerBytesWord_longList (pfx : Byte) (h : classifyPrefix pfx = .longList) :
    (pfx.zeroExtend 64 : Word) + signExtend12 (-246 : BitVec 12) =
      prefixHeaderBytesWord pfx := by
  have hrange := (classifyPrefix_longList_iff pfx).mp h
  unfold prefixHeaderBytesWord rlpPrefixHeaderBytes
  rw [h, signExtend12_neg246]
  unfold rlpPrefixLongListHeaderBytes rlpPrefixLongListLenOfLen
  bv_omega

private def emptyReturnFrame (inputBase : Word) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion inputBase []

private theorem emptyReturnFrame_pcFree (inputBase : Word) :
    (emptyReturnFrame inputBase).pcFree := by
  unfold emptyReturnFrame
  exact pcFree_sepConj pcFree_regOwn
    (pcFree_sepConj pcFree_regOwn
      (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)))

/-- Empty-input endpoint adapted to the public prefix-decoder ABI post. -/
def emptyAbiCert (base inputBase raVal : Word) :
    WP.CFG.Cert (base + 120) (returnExit raVal) (code base)
      (abiPost inputBase raVal []) := by
  let F := emptyReturnFrame inputBase
  refine WP.CFG.weakenPost
    (WP.CFG.frameR (emptyReturnCert base raVal) F (emptyReturnFrame_pcFree inputBase)) ?_
  intro h hp
  unfold abiPost resultPost decodePrefixInfo
  unfold F emptyReturnFrame at hp
  xcancel_struct hp

private def shortBytesReturnFrame
    (inputBase : Word) (pfx : Byte) (rest : List Byte) : Assertion :=
  regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x6 **
    bytesRegion inputBase (pfx :: rest) ** ⌜classifyPrefix pfx = .shortBytes⌝

private theorem shortBytesReturnFrame_pcFree
    (inputBase : Word) (pfx : Byte) (rest : List Byte) :
    (shortBytesReturnFrame inputBase pfx rest).pcFree := by
  unfold shortBytesReturnFrame
  exact pcFree_sepConj pcFree_regOwn
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regOwn
        (pcFree_sepConj (bytesRegion_pcFree _ _) pcFree_pure)))

/-- Short-byte-string endpoint adapted to the public prefix-decoder ABI post. -/
def shortBytesAbiCert
    (base inputBase raVal : Word) (pfx : Byte) (rest : List Byte) :
    WP.CFG.Cert (base + 72) (returnExit raVal) (code base)
      (abiPost inputBase raVal (pfx :: rest)) := by
  let F := shortBytesReturnFrame inputBase pfx rest
  refine WP.CFG.weakenPost
    (WP.CFG.frameR (shortBytesReturnCert base raVal) F
      (shortBytesReturnFrame_pcFree inputBase pfx rest)) ?_
  intro h hp
  unfold abiPost resultPost decodePrefixInfo
  unfold F shortBytesReturnFrame at hp
  extract_pure hp
  obtain ⟨h_class, hp⟩ := hp
  simp [h_class, prefixClassCode, rlpPrefixHeaderBytes]
  xcancel_struct hp

private theorem classifierShortBytes_handoff
    (base inputBase raVal : Word) (pfx : Byte) (rest : List Byte) :
    WP.Entails
      (rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xB8
        (classifyPrefix pfx = .shortBytes) ** classifierFrame inputBase raVal pfx rest)
      (shortBytesAbiCert base inputBase raVal pfx rest).pre := by
  intro h hp
  change
    (((regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** (.x1 ↦ᵣ raVal)) **
      shortBytesReturnFrame inputBase pfx rest) h)
  rw [rlp_phase1_exit_post_acc_unfold] at hp
  unfold classifierFrame at hp
  unfold shortBytesReturnFrame
  have hp' := sepConj_mono_left
    (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (fun _ hp => hp)
        (sepConj_mono (regIs_implies_regOwn .x10) (fun _ hp => hp)))) h hp
  xperm_hyp hp'

private def shortListReturnFrame
    (inputBase : Word) (pfx : Byte) (rest : List Byte) : Assertion :=
  regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x6 **
    bytesRegion inputBase (pfx :: rest) ** ⌜classifyPrefix pfx = .shortList⌝

private theorem shortListReturnFrame_pcFree
    (inputBase : Word) (pfx : Byte) (rest : List Byte) :
    (shortListReturnFrame inputBase pfx rest).pcFree := by
  unfold shortListReturnFrame
  exact pcFree_sepConj pcFree_regOwn
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regOwn
        (pcFree_sepConj (bytesRegion_pcFree _ _) pcFree_pure)))

/-- Short-list endpoint adapted to the public prefix-decoder ABI post. -/
def shortListAbiCert
    (base inputBase raVal : Word) (pfx : Byte) (rest : List Byte) :
    WP.CFG.Cert (base + 104) (returnExit raVal) (code base)
      (abiPost inputBase raVal (pfx :: rest)) := by
  let F := shortListReturnFrame inputBase pfx rest
  refine WP.CFG.weakenPost
    (WP.CFG.frameR (shortListReturnCert base raVal) F
      (shortListReturnFrame_pcFree inputBase pfx rest)) ?_
  intro h hp
  unfold abiPost resultPost decodePrefixInfo
  unfold F shortListReturnFrame at hp
  extract_pure hp
  obtain ⟨h_class, hp⟩ := hp
  simp [h_class, prefixClassCode, rlpPrefixHeaderBytes]
  xcancel_struct hp

private theorem classifierShortList_handoff
    (base inputBase raVal : Word) (pfx : Byte) (rest : List Byte) :
    WP.Entails
      (rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xF8
        (classifyPrefix pfx = .shortList) ** classifierFrame inputBase raVal pfx rest)
      (shortListAbiCert base inputBase raVal pfx rest).pre := by
  intro h hp
  change
    (((regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** (.x1 ↦ᵣ raVal)) **
      shortListReturnFrame inputBase pfx rest) h)
  rw [rlp_phase1_exit_post_acc_unfold] at hp
  unfold classifierFrame at hp
  unfold shortListReturnFrame
  have hp' := sepConj_mono_left
    (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (fun _ hp => hp)
        (sepConj_mono (regIs_implies_regOwn .x10) (fun _ hp => hp)))) h hp
  xperm_hyp hp'

private def longBytesReturnFrame
    (inputBase : Word) (pfx : Byte) (rest : List Byte) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** regOwn .x6 **
    bytesRegion inputBase (pfx :: rest) ** ⌜classifyPrefix pfx = .longBytes⌝

private theorem longBytesReturnFrame_pcFree
    (inputBase : Word) (pfx : Byte) (rest : List Byte) :
    (longBytesReturnFrame inputBase pfx rest).pcFree := by
  unfold longBytesReturnFrame
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regOwn
      (pcFree_sepConj (bytesRegion_pcFree _ _) pcFree_pure))

private theorem exactResultOwn5_entails
    (status classCode headerBytes pfxWord : Word) :
    WP.Entails
      ((.x10 ↦ᵣ status) ** (.x11 ↦ᵣ classCode) ** (.x12 ↦ᵣ headerBytes) **
        (.x5 ↦ᵣ pfxWord) ** regOwn .x6)
      ((.x10 ↦ᵣ status) ** (.x11 ↦ᵣ classCode) ** (.x12 ↦ᵣ headerBytes) **
        regOwn .x5 ** regOwn .x6) := by
  intro h hp
  exact sepConj_mono_right
    (sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono_left (regIs_implies_regOwn .x5)))) h hp

/-- Long-byte-string endpoint adapted to the public prefix-decoder ABI post. -/
def longBytesAbiCert
    (base inputBase raVal : Word) (pfx : Byte) (rest : List Byte) :
    WP.CFG.Cert (base + 88) (returnExit raVal) (code base)
      (abiPost inputBase raVal (pfx :: rest)) := by
  let pfxWord : Word := BitVec.setWidth 64 pfx
  let imm : BitVec 12 := -182
  let F := longBytesReturnFrame inputBase pfx rest
  refine WP.CFG.weakenPost
    (WP.CFG.frameR (longBytesReturnCert base raVal pfxWord) F
      (longBytesReturnFrame_pcFree inputBase pfx rest)) ?_
  intro h hp
  unfold abiPost resultPost decodePrefixInfo
  unfold F longBytesReturnFrame at hp
  extract_pure hp
  obtain ⟨h_class, hp⟩ := hp
  have h_header : pfxWord + signExtend12 imm = prefixHeaderBytesWord pfx := by
    subst imm
    simpa [pfxWord] using headerBytesWord_longBytes pfx h_class
  simp [h_class, prefixClassCode]
  unfold prefixHeaderBytesWord at h_header
  rw [← h_header]
  exact sepConj_mono_left
    (exactResultOwn5_entails (0 : Word) (3 : Word)
      (pfxWord + signExtend12 imm) pfxWord) h (by
      xcancel_struct hp)

private theorem classifierLongBytes_handoff
    (base inputBase raVal : Word) (pfx : Byte) (rest : List Byte) :
    WP.Entails
      (rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xC0
        (classifyPrefix pfx = .longBytes) ** classifierFrame inputBase raVal pfx rest)
      (longBytesAbiCert base inputBase raVal pfx rest).pre := by
  intro h hp
  change
    (((regOwn .x10 ** regOwn .x11 ** (.x5 ↦ᵣ BitVec.setWidth 64 pfx) **
      regOwn .x12 ** (.x1 ↦ᵣ raVal)) ** longBytesReturnFrame inputBase pfx rest) h)
  rw [rlp_phase1_exit_post_acc_unfold] at hp
  unfold classifierFrame at hp
  unfold longBytesReturnFrame
  have hp' := sepConj_mono_left
    (sepConj_mono (fun _ hp => hp)
      (sepConj_mono (fun _ hp => hp)
        (sepConj_mono (regIs_implies_regOwn .x10) (fun _ hp => hp)))) h hp
  xperm_hyp hp'

private def longListReturnFrame
    (inputBase : Word) (pfx : Byte) (rest : List Byte) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** regOwn .x6 **
    bytesRegion inputBase (pfx :: rest) ** ⌜classifyPrefix pfx = .longList⌝

private theorem longListReturnFrame_pcFree
    (inputBase : Word) (pfx : Byte) (rest : List Byte) :
    (longListReturnFrame inputBase pfx rest).pcFree := by
  unfold longListReturnFrame
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regOwn
      (pcFree_sepConj (bytesRegion_pcFree _ _) pcFree_pure))

/-- Long-list endpoint adapted to the public prefix-decoder ABI post. -/
def longListAbiCert
    (base inputBase raVal : Word) (pfx : Byte) (rest : List Byte) :
    WP.CFG.Cert (base + 40) (returnExit raVal) (code base)
      (abiPost inputBase raVal (pfx :: rest)) := by
  let pfxWord : Word := BitVec.setWidth 64 pfx
  let imm : BitVec 12 := -246
  let F := longListReturnFrame inputBase pfx rest
  refine WP.CFG.weakenPost
    (WP.CFG.frameR (longListReturnCert base raVal pfxWord) F
      (longListReturnFrame_pcFree inputBase pfx rest)) ?_
  intro h hp
  unfold abiPost resultPost decodePrefixInfo
  unfold F longListReturnFrame at hp
  extract_pure hp
  obtain ⟨h_class, hp⟩ := hp
  have h_header : pfxWord + signExtend12 imm = prefixHeaderBytesWord pfx := by
    subst imm
    simpa [pfxWord] using headerBytesWord_longList pfx h_class
  simp [h_class, prefixClassCode]
  unfold prefixHeaderBytesWord at h_header
  rw [← h_header]
  exact sepConj_mono_left
    (exactResultOwn5_entails (0 : Word) (5 : Word)
      (pfxWord + signExtend12 imm) pfxWord) h (by
      xcancel_struct hp)

private theorem classifierLongList_handoff
    (base inputBase raVal : Word) (pfx : Byte) (rest : List Byte) :
    WP.Entails
      (rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xF8
        (classifyPrefix pfx = .longList) ** classifierFrame inputBase raVal pfx rest)
      (longListAbiCert base inputBase raVal pfx rest).pre := by
  intro h hp
  change
    (((regOwn .x10 ** regOwn .x11 ** (.x5 ↦ᵣ BitVec.setWidth 64 pfx) **
      regOwn .x12 ** (.x1 ↦ᵣ raVal)) ** longListReturnFrame inputBase pfx rest) h)
  rw [rlp_phase1_exit_post_acc_unfold] at hp
  unfold classifierFrame at hp
  unfold longListReturnFrame
  have hp' := sepConj_mono_left
    (sepConj_mono (fun _ hp => hp)
      (sepConj_mono (fun _ hp => hp)
        (sepConj_mono (regIs_implies_regOwn .x10) (fun _ hp => hp)))) h hp
  xperm_hyp hp'

/-- The loaded-prefix classifier joined to all five ABI endpoint blocks. -/
def classifierAbiCert
    (base inputBase raVal : Word) (pfx : Byte) (rest : List Byte) :
    WP.CFG.Cert (base + 8) (returnExit raVal) (code base)
      (abiPost inputBase raVal (pfx :: rest)) := by
  let F := classifierFrame inputBase raVal pfx rest
  let br := WP.CFG.nbranchFrameR (classifierNBranch base pfx inputBase) F
    (classifierFrame_pcFree inputBase raVal pfx rest)
  refine WP.CFG.nbranch br 4 ?_
  intro ex hex
  have hex' : ex ∈
      [(base + 56,
          rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0x80
            (classifyPrefix pfx = .singleByte) ** F),
       (base + 72,
          rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xB8
            (classifyPrefix pfx = .shortBytes) ** F),
       (base + 88,
          rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xC0
            (classifyPrefix pfx = .longBytes) ** F),
       (base + 104,
          rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xF8
            (classifyPrefix pfx = .shortList) ** F),
       (base + 40,
          rlp_phase1_exit_post_acc (BitVec.setWidth 64 pfx) 0xF8
            (classifyPrefix pfx = .longList) ** F)] := by
    dsimp [br, F, WP.CFG.nbranchFrameR, WP.NBranch.frameR] at hex
    rw [classifierNBranch_exits] at hex
    simpa using hex
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hex'
  rcases hex' with h1 | h2 | h3 | h4 | h5
  · rcases h1 with ⟨rfl, rfl⟩
    simpa [F] using
      (WP.CFG.weakenPre (singleByteAbiCert base inputBase raVal pfx rest)
        (classifierSingleByte_handoff base inputBase raVal pfx rest)).sound
  · rcases h2 with ⟨rfl, rfl⟩
    simpa [F] using
      (WP.CFG.weakenPre (shortBytesAbiCert base inputBase raVal pfx rest)
        (classifierShortBytes_handoff base inputBase raVal pfx rest)).sound
  · rcases h3 with ⟨rfl, rfl⟩
    simpa [F] using
      (WP.CFG.weakenPre (longBytesAbiCert base inputBase raVal pfx rest)
        (classifierLongBytes_handoff base inputBase raVal pfx rest)).sound
  · rcases h4 with ⟨rfl, rfl⟩
    simpa [F] using
      (WP.CFG.weakenPre (shortListAbiCert base inputBase raVal pfx rest)
        (classifierShortList_handoff base inputBase raVal pfx rest)).sound
  · rcases h5 with ⟨rfl, rfl⟩
    simpa [F] using
      (WP.CFG.weakenPre (longListAbiCert base inputBase raVal pfx rest)
        (classifierLongList_handoff base inputBase raVal pfx rest)).sound

private theorem entry_beq_mono_code (base : Word) :
    ∀ a i, CodeReq.singleton base (.BEQ .x11 .x0 (120 : BitVec 13)) a = some i →
      code base a = some i :=
  CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base prog 0 base
    (by rw [prog_length]; norm_num)
    (by rw [prog_length]; norm_num) (by bv_omega))

private theorem entry_lbu_mono_code (base : Word) :
    ∀ a i, CodeReq.singleton (base + 4) (.LBU .x5 .x10 0) a = some i →
      code base a = some i :=
  CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base prog 1 (base + 4)
    (by rw [prog_length]; norm_num)
    (by rw [prog_length]; norm_num) (by bv_omega))

/-- Head zero/nonzero split for the prefix decoder. -/
theorem entryBranch_spec (base inputLen : Word) :
    cpsBranchWithin 1 base (code base)
      ((.x11 ↦ᵣ inputLen) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 120) ((.x11 ↦ᵣ inputLen) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜inputLen = (0 : Word)⌝)
      (base + 4) ((.x11 ↦ᵣ inputLen) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜inputLen ≠ (0 : Word)⌝) := by
  have h := beq_spec_gen_within .x11 .x0 (120 : BitVec 13) inputLen (0 : Word) base
  rw [show base + signExtend13 (120 : BitVec 13) = base + 120 from by
    rw [show signExtend13 (120 : BitVec 13) = (120 : Word) from by decide]] at h
  exact cpsBranchWithin_extend_code (entry_beq_mono_code base) h

def entryBranch (base inputLen : Word) :
    WP.Branch base (code base) :=
  WP.Branch.ofSpec (entryBranch_spec base inputLen)

/-- Nonempty entry fallthrough: load the first byte and shape the classifier precondition. -/
theorem prefixLoadToClassifier_spec
    (base inputBase raVal a2Old t0Old t1Old : Word)
    (pfx : Byte) (rest : List Byte)
    (halign : inputBase.toNat % 8 = 0)
    (hover0 : inputBase.toNat + 0 < 2 ^ 64)
    (hvalid : isValidByteAccess inputBase = true) :
    cpsTripleWithin 1 (base + 4) (base + 8) (code base)
      (abiPre inputBase raVal a2Old t0Old t1Old (pfx :: rest))
      (((.x5 ↦ᵣ BitVec.setWidth 64 pfx) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ inputBase)) ** classifierFrame inputBase raVal pfx rest) := by
  have hlbu := bytesRegion_lbu_within .x5 .x10 inputBase t0Old (base + 4)
    (pfx :: rest) 0 (by decide) halign (by simp) hover0 (by
      simpa using hvalid)
  rw [show inputBase + BitVec.ofNat 64 0 = inputBase from by bv_omega] at hlbu
  have hload := cpsTripleWithin_extend_code (entry_lbu_mono_code base) hlbu
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hload
  let F : Assertion :=
    (.x11 ↦ᵣ BitVec.ofNat 64 (pfx :: rest).length) ** (.x12 ↦ᵣ a2Old) **
      (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)
  have hfr := cpsTripleWithin_frameR F (by
    unfold F
    pcFree) hload
  refine cpsTripleWithin_weaken ?_ ?_ hfr
  · intro h hp
    unfold abiPre at hp
    unfold F
    xperm_hyp hp
  · intro h hp
    unfold F at hp
    unfold classifierFrame
    have hp' := sepConj_mono_right
      (sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12)
          (sepConj_mono (regIs_implies_regOwn .x6)
            (sepConj_mono (fun _ hp => hp) (fun _ hp => hp))))) h hp
    simp only [List.getElem_cons_zero] at hp'
    xperm_hyp hp'

/-- Nonempty tail after the head branch has fallen through. -/
def nonemptyTailCert
    (base inputBase raVal a2Old t0Old t1Old : Word)
    (pfx : Byte) (rest : List Byte)
    (halign : inputBase.toNat % 8 = 0)
    (hover0 : inputBase.toNat + 0 < 2 ^ 64)
    (hvalid : isValidByteAccess inputBase = true) :
    WP.CFG.Cert (base + 4) (returnExit raVal) (code base)
      (abiPost inputBase raVal (pfx :: rest)) :=
  WP.CFG.seqExact (classifierAbiCert base inputBase raVal pfx rest)
    (prefixLoadToClassifier_spec base inputBase raVal a2Old t0Old t1Old pfx rest
      halign hover0 hvalid)

private def entryFrame
    (inputBase raVal a2Old t0Old t1Old : Word) (input : List Byte) : Assertion :=
  (.x10 ↦ᵣ inputBase) ** (.x12 ↦ᵣ a2Old) ** (.x5 ↦ᵣ t0Old) **
    (.x6 ↦ᵣ t1Old) ** (.x1 ↦ᵣ raVal) ** bytesRegion inputBase input

private theorem entryFrame_pcFree
    (inputBase raVal a2Old t0Old t1Old : Word) (input : List Byte) :
    (entryFrame inputBase raVal a2Old t0Old t1Old input).pcFree := by
  unfold entryFrame
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)))))

private theorem entry_empty_handoff
    (base inputBase raVal a2Old t0Old t1Old : Word) :
    WP.Entails
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        entryFrame inputBase raVal a2Old t0Old t1Old [])
      (emptyAbiCert base inputBase raVal).pre := by
  intro h hp
  change
    (((regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** (.x1 ↦ᵣ raVal)) **
      emptyReturnFrame inputBase) h)
  unfold entryFrame at hp
  unfold emptyReturnFrame
  have hp' := sepConj_mono
    (sepConj_mono (regIs_implies_regOwn .x11) (fun _ hp => hp))
    (sepConj_mono (regIs_implies_regOwn .x10)
      (sepConj_mono (regIs_implies_regOwn .x12)
        (sepConj_mono (regIs_implies_regOwn .x5)
          (sepConj_mono (regIs_implies_regOwn .x6)
            (sepConj_mono (fun _ hp => hp) (fun _ hp => hp)))))) h hp
  xperm_hyp hp'

/-- Top empty-input certificate. -/
def emptyTopCert
    (base inputBase raVal a2Old t0Old t1Old : Word) :
    WP.CFG.Cert base (returnExit raVal) (code base)
      (abiPost inputBase raVal []) := by
  let F := entryFrame inputBase raVal a2Old t0Old t1Old []
  have hbr := entryBranch_spec base (0 : Word)
  have hpath0 : cpsTripleWithin 1 base (base + 120) (code base)
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
    refine cpsBranchWithin_takenStripPure2 hbr ?_
    intro h hp
    extract_pure hp
    exact hp.1 rfl
  have hpath := cpsTripleWithin_frameR F (entryFrame_pcFree inputBase raVal a2Old t0Old t1Old []) hpath0
  refine WP.CFG.weakenPre
    (pre' := abiPre inputBase raVal a2Old t0Old t1Old [])
    (WP.CFG.seq hpath (emptyAbiCert base inputBase raVal)
      (entry_empty_handoff base inputBase raVal a2Old t0Old t1Old)) ?_
  intro h hp
  unfold abiPre at hp
  simp only [List.length_nil] at hp
  change (((.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ a2Old) **
    (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x1 ↦ᵣ raVal) ** bytesRegion inputBase []) h) at hp
  change ((((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
    entryFrame inputBase raVal a2Old t0Old t1Old []) h)
  unfold entryFrame
  xperm_hyp hp

private theorem entry_nonempty_handoff
    (inputBase raVal a2Old t0Old t1Old : Word) (pfx : Byte) (rest : List Byte) :
    WP.Entails
      (((.x11 ↦ᵣ BitVec.ofNat 64 (pfx :: rest).length) ** (.x0 ↦ᵣ (0 : Word))) **
        entryFrame inputBase raVal a2Old t0Old t1Old (pfx :: rest))
      (abiPre inputBase raVal a2Old t0Old t1Old (pfx :: rest)) := by
  intro h hp
  unfold entryFrame at hp
  unfold abiPre
  xperm_hyp hp

/-- Top nonempty-input certificate. -/
def nonemptyTopCert
    (base inputBase raVal a2Old t0Old t1Old : Word)
    (pfx : Byte) (rest : List Byte)
    (h_len_word : BitVec.ofNat 64 (pfx :: rest).length ≠ (0 : Word))
    (halign : inputBase.toNat % 8 = 0)
    (hover0 : inputBase.toNat + 0 < 2 ^ 64)
    (hvalid : isValidByteAccess inputBase = true) :
    WP.CFG.Cert base (returnExit raVal) (code base)
      (abiPost inputBase raVal (pfx :: rest)) := by
  let inputLen : Word := BitVec.ofNat 64 (pfx :: rest).length
  let F := entryFrame inputBase raVal a2Old t0Old t1Old (pfx :: rest)
  have hbr := entryBranch_spec base inputLen
  have hpath0 : cpsTripleWithin 1 base (base + 4) (code base)
      ((.x11 ↦ᵣ inputLen) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ inputLen) ** (.x0 ↦ᵣ (0 : Word))) := by
    refine cpsBranchWithin_ntakenStripPure2 hbr ?_
    intro h hp
    extract_pure hp
    exact h_len_word (by
      subst inputLen
      exact hp.1)
  have hpath := cpsTripleWithin_frameR F
    (entryFrame_pcFree inputBase raVal a2Old t0Old t1Old (pfx :: rest)) hpath0
  refine WP.CFG.weakenPre
    (pre' := abiPre inputBase raVal a2Old t0Old t1Old (pfx :: rest))
    (WP.CFG.seq hpath
      (nonemptyTailCert base inputBase raVal a2Old t0Old t1Old pfx rest
        halign hover0 hvalid)
      (entry_nonempty_handoff inputBase raVal a2Old t0Old t1Old pfx rest)) ?_
  intro h hp
  unfold abiPre at hp
  change ((((.x11 ↦ᵣ BitVec.ofNat 64 (pfx :: rest).length) ** (.x0 ↦ᵣ (0 : Word))) **
    entryFrame inputBase raVal a2Old t0Old t1Old (pfx :: rest)) h)
  unfold entryFrame
  xperm_hyp hp

/-- Top prefix-decoder certificate, by input shape. Empty input needs no memory
    side conditions; nonempty input supplies the static facts for the prefix `LBU`. -/
def topCert
    (base inputBase raVal a2Old t0Old t1Old : Word) (input : List Byte)
    (h_len_word : input ≠ [] → BitVec.ofNat 64 input.length ≠ (0 : Word))
    (halign : input ≠ [] → inputBase.toNat % 8 = 0)
    (hover0 : input ≠ [] → inputBase.toNat + 0 < 2 ^ 64)
    (hvalid : input ≠ [] → isValidByteAccess inputBase = true) :
    Cert base (returnExit raVal) (code base) inputBase raVal input := by
  cases input with
  | nil =>
      exact emptyTopCert base inputBase raVal a2Old t0Old t1Old
  | cons pfx rest =>
      exact nonemptyTopCert base inputBase raVal a2Old t0Old t1Old pfx rest
        (h_len_word (by simp)) (halign (by simp)) (hover0 (by simp)) (hvalid (by simp))

theorem topCertSound_disj
    (base inputBase raVal a2Old t0Old t1Old : Word) (input : List Byte)
    (h_len_word : input ≠ [] → BitVec.ofNat 64 input.length ≠ (0 : Word))
    (halign : input ≠ [] → inputBase.toNat % 8 = 0)
    (hover0 : input ≠ [] → inputBase.toNat + 0 < 2 ^ 64)
    (hvalid : input ≠ [] → isValidByteAccess inputBase = true) :
    cpsTripleWithin
      (topCert base inputBase raVal a2Old t0Old t1Old input h_len_word halign hover0 hvalid).nSteps
      base (returnExit raVal) (code base)
      (topCert base inputBase raVal a2Old t0Old t1Old input h_len_word halign hover0 hvalid).pre
      (abiDisjPost inputBase raVal input) :=
  certSound_disj (topCert base inputBase raVal a2Old t0Old t1Old input
    h_len_word halign hover0 hvalid)

/-- RLP-generic bridge from a static length bound to the length-word
    nonzero side condition `topCert` needs. Any caller that already knows
    `input.length < 2 ^ 64` (true of every realistic input) gets the witness
    for free instead of having to construct it by hand. -/
theorem lenWord_ne_zero_of_nonempty_of_lt
    {input : List Byte}
    (h_nonempty : input ≠ [])
    (h_len_lt : input.length < 2 ^ 64) :
    BitVec.ofNat 64 input.length ≠ (0 : Word) := by
  have hpos : 0 < input.length := List.length_pos_of_ne_nil h_nonempty
  intro heq
  have htoNat : (BitVec.ofNat 64 input.length).toNat = (0 : Word).toNat :=
    congrArg BitVec.toNat heq
  simp [BitVec.toNat_ofNat] at htoNat
  omega

/-- Caller-friendly top certificate: a static length bound replaces the
    manual length-word nonzero witness required by `topCert`. -/
def topCertStatic
    (base inputBase raVal a2Old t0Old t1Old : Word) (input : List Byte)
    (h_len_lt : input.length < 2 ^ 64)
    (halign : input ≠ [] → inputBase.toNat % 8 = 0)
    (hover0 : input ≠ [] → inputBase.toNat + 0 < 2 ^ 64)
    (hvalid : input ≠ [] → isValidByteAccess inputBase = true) :
    Cert base (returnExit raVal) (code base) inputBase raVal input :=
  topCert base inputBase raVal a2Old t0Old t1Old input
    (fun h_nonempty => lenWord_ne_zero_of_nonempty_of_lt h_nonempty h_len_lt)
    halign hover0 hvalid

theorem topCertStaticSound_disj
    (base inputBase raVal a2Old t0Old t1Old : Word) (input : List Byte)
    (h_len_lt : input.length < 2 ^ 64)
    (halign : input ≠ [] → inputBase.toNat % 8 = 0)
    (hover0 : input ≠ [] → inputBase.toNat + 0 < 2 ^ 64)
    (hvalid : input ≠ [] → isValidByteAccess inputBase = true) :
    cpsTripleWithin
      (topCertStatic base inputBase raVal a2Old t0Old t1Old input h_len_lt halign hover0 hvalid).nSteps
      base (returnExit raVal) (code base)
      (topCertStatic base inputBase raVal a2Old t0Old t1Old input h_len_lt halign hover0 hvalid).pre
      (abiDisjPost inputBase raVal input) :=
  certSound_disj (topCertStatic base inputBase raVal a2Old t0Old t1Old input
    h_len_lt halign hover0 hvalid)

/-- RLP-generic tactic for small prefix range side conditions. -/
macro "wp_rlp_range" : tactic =>
  `(tactic|
    first
    | decide
    | omega
    | bv_omega
    | simp only [BitVec.ult, decide_eq_true_eq,
        show (0x80 : Word).toNat = 0x80 from by decide,
        show (0xb8 : Word).toNat = 0xb8 from by decide,
        show (0xc0 : Word).toNat = 0xc0 from by decide,
        show (0xf8 : Word).toNat = 0xf8 from by decide] at * <;> omega)

end PrefixDecode
end EvmAsm.Rv64.RLP
