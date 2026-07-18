/-
  Extract body: rlp_walk_init call at E+144 (instr 36) + BNE a2=0 not-taken.

  Pattern: leaf `rlp_walk_init_spec_within` + `callWithin_spec` under
  `extractLinkedCode` (HeaderFields / type_dispatch call style).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.GenericSpecs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.EL.RLP.Basic
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressLoadType
import EvmAsm.Codegen.Programs.RlpWalkCallSAsm
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP
open EvmAsm.Codegen
open EvmAsm.Codegen.RlpWalkCallSAsm

/-- Link after JAL walk_init (instr 37 BNE). -/
abbrev LinkWalkInit : Word := E + 148
/-- After BNE a2=0 not-taken fallthrough. -/
abbrev AfterWalkInitOk : Word := E + 152

private def walkInitJalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_extract_to_address + 144)

/-- Leaf pre without ra (call adapter Prest). -/
def extractWalkInitPrest (txBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (txBytes : List (BitVec 8)) (listOff : Nat) : Assertion :=
  (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
    (.x12 ↦ᵣ a2Old) **
    (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
    (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion txBase txBytes

/-- Leaf post with ra = LinkWalkInit (9-way init outcome). -/
def extractWalkInitPost (txBase listLen : Word) (txBytes : List (BitVec 8))
    (listOff : Nat) (hoff : listOff < txBytes.length) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkInit) **
    bytesRegion txBase txBytes) **
   (fun h =>
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (2 : Word)) ** ⌜listLen = (0 : Word)⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 listOff)) **
        (.x11 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (1 : Word)) **
        ⌜listLen ≠ (0 : Word) ∧
          BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true⌝) h) ∨
     (((.x10 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
        (.x11 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (0 : Word)) **
        ⌜listLen ≠ (0 : Word) ∧
          ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
          BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
          (txBase + BitVec.ofNat 64 listOff) +
            (((txBytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
            = (txBase + BitVec.ofNat 64 listOff) + listLen⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 listOff)) **
        (.x11 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (3 : Word)) **
        ⌜listLen ≠ (0 : Word) ∧
          ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
          BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
          (txBase + BitVec.ofNat 64 listOff) +
            (((txBytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
            ≠ (txBase + BitVec.ofNat 64 listOff) + listLen⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 listOff)) **
        (.x11 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (4 : Word)) **
        ⌜listLen ≠ (0 : Word) ∧
          ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
          ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
          BitVec.ult ((txBase + BitVec.ofNat 64 listOff) + listLen)
            ((txBase + BitVec.ofNat 64 listOff) +
              (((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
            = true⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 listOff)) **
        (.x11 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (5 : Word)) **
        ⌜listLen ≠ (0 : Word) ∧
          ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
          ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
          ¬ BitVec.ult ((txBase + BitVec.ofNat 64 listOff) + listLen)
            ((txBase + BitVec.ofNat 64 listOff) +
              (((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
            = true ∧
          txBytes[listOff + 1]? = some (0 : BitVec 8)⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 listOff)) **
        (.x11 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (6 : Word)) **
        ⌜listLen ≠ (0 : Word) ∧
          ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
          ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
          ¬ BitVec.ult ((txBase + BitVec.ofNat 64 listOff) + listLen)
            ((txBase + BitVec.ofNat 64 listOff) +
              (((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
            = true ∧
          txBytes[listOff + 1]? ≠ some (0 : BitVec 8) ∧
          BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((txBytes.drop (listOff + 1)).take
            ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true⌝) h) ∨
     (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 listOff)) **
        (.x11 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (7 : Word)) **
        ⌜listLen ≠ (0 : Word) ∧
          ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
          ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
          ¬ BitVec.ult ((txBase + BitVec.ofNat 64 listOff) + listLen)
            ((txBase + BitVec.ofNat 64 listOff) +
              (((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
            = true ∧
          txBytes[listOff + 1]? ≠ some (0 : BitVec 8) ∧
          ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((txBytes.drop (listOff + 1)).take
            ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true ∧
          ((txBase + BitVec.ofNat 64 listOff) +
              (((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
              BitVec.ofNat 64 (Nat.fromBytesBE ((txBytes.drop (listOff + 1)).take
                ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))
            ≠ (txBase + BitVec.ofNat 64 listOff) + listLen⌝) h) ∨
     (((.x10 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) +
          (((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))) **
        (.x11 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (0 : Word)) **
        ⌜listLen ≠ (0 : Word) ∧
          ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
          ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
          ¬ BitVec.ult ((txBase + BitVec.ofNat 64 listOff) + listLen)
            ((txBase + BitVec.ofNat 64 listOff) +
              (((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
            = true ∧
          txBytes[listOff + 1]? ≠ some (0 : BitVec 8) ∧
          ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((txBytes.drop (listOff + 1)).take
            ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true ∧
          ((txBase + BitVec.ofNat 64 listOff) +
              (((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
              BitVec.ofNat 64 (Nat.fromBytesBE ((txBytes.drop (listOff + 1)).take
                ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))
            = (txBase + BitVec.ofNat 64 listOff) + listLen⌝) h)))

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _)

theorem extractWalkInitPrest_pcFree
    (txBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (txBytes : List (BitVec 8)) (listOff : Nat) :
    (extractWalkInitPrest txBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      txBytes listOff).pcFree := by
  unfold extractWalkInitPrest; pcf

theorem walkInitJalOff_resolves :
    WalkInitJalPc + signExtend21 walkInitJalOff = WI := by
  simp only [WalkInitJalPc, WI, walkInitJalOff, E]; decide

theorem walkInit_in_extractLinked_available :
    ∀ a i, walkInitCode a = some i → extractLinkedCode a = some i :=
  walkInit_in_extractLinked

set_option maxRecDepth 8000 in
/-- JAL walk_init under extractLinkedCode: leaf 9-way post at LinkWalkInit. -/
theorem extractWalkInitCall
    (txBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (txBytes : List (BitVec 8)) (listOff : Nat) (old1 : Word)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : listOff < txBytes.length)
    (hover : txBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 listOff) = true)
    (hll_len : ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        listOff + 1 + ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length)
    (hll_over : ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        txBase.toNat + (listOff + 1 +
          ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hll_valid : ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        ∀ k, k < ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (listOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 81) WalkInitJalPc LinkWalkInit extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkInitPrest txBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          txBytes listOff)
      (extractWalkInitPost txBase listLen txBytes listOff hoff) := by
  have hret : (LinkWalkInit &&& ~~~(1 : Word)) = LinkWalkInit := by
    simp only [LinkWalkInit, E]; decide
  have hleaf := rlp_walk_init_spec_within WI txBase LinkWalkInit listLen
    a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old txBytes listOff
    hsalign hoff hover hvalid hll_len hll_over hll_valid
  rw [hret] at hleaf
  -- Reshape to Prest outer form; post = extractWalkInitPost
  have hleafP : cpsTripleWithin 81 WI LinkWalkInit walkInitCode
      ((.x1 ↦ᵣ LinkWalkInit) **
        extractWalkInitPrest txBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          txBytes listOff)
      (extractWalkInitPost txBase listLen txBytes listOff hoff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkInitPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [extractWalkInitPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code walkInit_in_extractLinked hleafP
  -- callWithin wants post ((.x1 ↦ Link) ** Q); reshape full post to that
  have hcallee' : cpsTripleWithin 81 WI LinkWalkInit extractLinkedCode
      ((.x1 ↦ᵣ LinkWalkInit) **
        extractWalkInitPrest txBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          txBytes listOff)
      ((.x1 ↦ᵣ LinkWalkInit) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion txBase txBytes) **
         (fun h =>
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ (0 : Word)) **
              (.x12 ↦ᵣ (2 : Word)) ** ⌜listLen = (0 : Word)⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 listOff)) **
              (.x11 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (1 : Word)) **
              ⌜listLen ≠ (0 : Word) ∧
                BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true⌝) h) ∨
           (((.x10 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
              (.x11 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (0 : Word)) **
              ⌜listLen ≠ (0 : Word) ∧
                ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
                BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
                (txBase + BitVec.ofNat 64 listOff) +
                  (((txBytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
                    signExtend12 (1 : BitVec 12))
                  = (txBase + BitVec.ofNat 64 listOff) + listLen⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 listOff)) **
              (.x11 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (3 : Word)) **
              ⌜listLen ≠ (0 : Word) ∧
                ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
                BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
                (txBase + BitVec.ofNat 64 listOff) +
                  (((txBytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
                    signExtend12 (1 : BitVec 12))
                  ≠ (txBase + BitVec.ofNat 64 listOff) + listLen⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 listOff)) **
              (.x11 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (4 : Word)) **
              ⌜listLen ≠ (0 : Word) ∧
                ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
                ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
                BitVec.ult ((txBase + BitVec.ofNat 64 listOff) + listLen)
                  ((txBase + BitVec.ofNat 64 listOff) +
                    (((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                      signExtend12 (1 : BitVec 12)))
                  = true⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 listOff)) **
              (.x11 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (5 : Word)) **
              ⌜listLen ≠ (0 : Word) ∧
                ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
                ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
                ¬ BitVec.ult ((txBase + BitVec.ofNat 64 listOff) + listLen)
                  ((txBase + BitVec.ofNat 64 listOff) +
                    (((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                      signExtend12 (1 : BitVec 12)))
                  = true ∧
                txBytes[listOff + 1]? = some (0 : BitVec 8)⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 listOff)) **
              (.x11 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (6 : Word)) **
              ⌜listLen ≠ (0 : Word) ∧
                ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
                ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
                ¬ BitVec.ult ((txBase + BitVec.ofNat 64 listOff) + listLen)
                  ((txBase + BitVec.ofNat 64 listOff) +
                    (((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                      signExtend12 (1 : BitVec 12)))
                  = true ∧
                txBytes[listOff + 1]? ≠ some (0 : BitVec 8) ∧
                BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((txBytes.drop (listOff + 1)).take
                  ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)))
                  (56 : Word) = true⌝) h) ∨
           (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 listOff)) **
              (.x11 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (7 : Word)) **
              ⌜listLen ≠ (0 : Word) ∧
                ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
                ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
                ¬ BitVec.ult ((txBase + BitVec.ofNat 64 listOff) + listLen)
                  ((txBase + BitVec.ofNat 64 listOff) +
                    (((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                      signExtend12 (1 : BitVec 12)))
                  = true ∧
                txBytes[listOff + 1]? ≠ some (0 : BitVec 8) ∧
                ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((txBytes.drop (listOff + 1)).take
                  ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)))
                  (56 : Word) = true ∧
                ((txBase + BitVec.ofNat 64 listOff) +
                    (((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                      signExtend12 (1 : BitVec 12))) +
                    BitVec.ofNat 64 (Nat.fromBytesBE ((txBytes.drop (listOff + 1)).take
                      ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))
                  ≠ (txBase + BitVec.ofNat 64 listOff) + listLen⌝) h) ∨
           (((.x10 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) +
                (((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                  signExtend12 (1 : BitVec 12)))) **
              (.x11 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (0 : Word)) **
              ⌜listLen ≠ (0 : Word) ∧
                ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
                ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
                ¬ BitVec.ult ((txBase + BitVec.ofNat 64 listOff) + listLen)
                  ((txBase + BitVec.ofNat 64 listOff) +
                    (((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                      signExtend12 (1 : BitVec 12)))
                  = true ∧
                txBytes[listOff + 1]? ≠ some (0 : BitVec 8) ∧
                ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((txBytes.drop (listOff + 1)).take
                  ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)))
                  (56 : Word) = true ∧
                ((txBase + BitVec.ofNat 64 listOff) +
                    (((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
                      signExtend12 (1 : BitVec 12))) +
                    BitVec.ofNat 64 (Nat.fromBytesBE ((txBytes.drop (listOff + 1)).take
                      ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))
                  = (txBase + BitVec.ofNat 64 listOff) + listLen⌝) h)))) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [extractWalkInitPost] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec WalkInitJalPc WI old1 walkInitJalOff 81
    walkInitJalOff_resolves
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E WalkInitJalPc extractProg 36
        (.JAL .x1 walkInitJalOff) (by simp only [WalkInitJalPc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi))
    (extractWalkInitPrest_pcFree txBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      txBytes listOff)
    hcallee'
  rw [show (WalkInitJalPc + 4 : Word) = LinkWalkInit from by
    simp only [WalkInitJalPc, LinkWalkInit]; bv_omega] at hcall
  -- call post is ((.x1) ** Qcore); goal is extractWalkInitPost
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [extractWalkInitPost]
    xperm_hyp hq) hcall

/-- Short-success post at LinkWalkInit (a2=0; cursor = list+1). -/
def extractWalkInitShortPost (txBase listLen : Word) (txBytes : List (BitVec 8))
    (listOff : Nat) (t5Old t6Old : Word) : Assertion :=
  (.x10 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
    (.x11 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + listLen)) **
    (.x12 ↦ᵣ (0 : Word)) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
    (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkInit) **
    bytesRegion txBase txBytes

set_option maxRecDepth 8000 in
/-- JAL walk_init short-success path under extractLinkedCode (15-step leaf).
    Discharge short pure from `extractSuccess_short_walkInit_guards`. -/
theorem extractWalkInitCall_short
    (txBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (txBytes : List (BitVec 8)) (listOff : Nat) (old1 : Word)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : listOff < txBytes.length)
    (hover : txBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (txBase + BitVec.ofNat 64 listOff) +
        (((txBytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (txBase + BitVec.ofNat 64 listOff) + listLen) :
    cpsTripleWithin (1 + 15) WalkInitJalPc LinkWalkInit extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkInitPrest txBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          txBytes listOff)
      (extractWalkInitShortPost txBase listLen txBytes listOff t5Old t6Old) := by
  have hret : (LinkWalkInit &&& ~~~(1 : Word)) = LinkWalkInit := by
    simp only [LinkWalkInit, E]; decide
  have hleaf0 := rlp_walk_init_short_spec_within WI txBase LinkWalkInit listLen
    a2Old t0Old t1Old t2Old t3Old t4Old txBytes listOff
    hsalign hoff hover hvalid hlen h_ge h_hi h_exact
  rw [hret] at hleaf0
  -- Frame x30/x31 (short path does not touch them)
  have hleafF := cpsTripleWithin_frameR
    ((.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old))
    (by
      apply pcFree_sepConj
      · exact pcFree_regIs
      · exact pcFree_regIs) hleaf0
  have hleafP : cpsTripleWithin 15 WI LinkWalkInit walkInitCode
      ((.x1 ↦ᵣ LinkWalkInit) **
        extractWalkInitPrest txBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          txBytes listOff)
      (extractWalkInitShortPost txBase listLen txBytes listOff t5Old t6Old) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkInitPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [extractWalkInitShortPost] at hq ⊢
      xperm_hyp hq) hleafF
  have hcallee := cpsTripleWithin_extend_code walkInit_in_extractLinked hleafP
  have hcallee' : cpsTripleWithin 15 WI LinkWalkInit extractLinkedCode
      ((.x1 ↦ᵣ LinkWalkInit) **
        extractWalkInitPrest txBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
          txBytes listOff)
      ((.x1 ↦ᵣ LinkWalkInit) **
        ((.x10 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
          (.x11 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + listLen)) **
          (.x12 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion txBase txBytes)) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [extractWalkInitShortPost] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec WalkInitJalPc WI old1 walkInitJalOff 15
    walkInitJalOff_resolves
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E WalkInitJalPc extractProg 36
        (.JAL .x1 walkInitJalOff) (by simp only [WalkInitJalPc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi))
    (extractWalkInitPrest_pcFree txBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      txBytes listOff)
    hcallee'
  rw [show (WalkInitJalPc + 4 : Word) = LinkWalkInit from by
    simp only [WalkInitJalPc, LinkWalkInit]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [extractWalkInitShortPost]
    xperm_hyp hq) hcall

set_option maxRecDepth 8000 in
/-- BNE a2,x0 field_fail: not-taken when a2=0 → AfterWalkInitOk. -/
theorem extractWalkInitBneOk :
    cpsTripleWithin 1 LinkWalkInit AfterWalkInitOk extractLinkedCode
      ((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x12 .x0 (404 : BitVec 13)
    (0 : Word) (0 : Word) LinkWalkInit
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LinkWalkInit extractProg 37
        (.BNE .x12 .x0 (404 : BitVec 13))
        (by simp only [LinkWalkInit]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  -- not-taken: a2 = x0 = 0 → fallthrough (taken post has ⌜0 ≠ 0⌝ absurd)
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkWalkInit + 4 = AfterWalkInitOk := by
    simp only [LinkWalkInit, AfterWalkInitOk]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- Short post → common temps/bytes + ∃ cursor,end a2=0 OK regs
    (honest replacement for universal `walkInitOkFail_drop` on short path). -/
theorem extractWalkInitShortPost_to_okNested
    (txBase listLen : Word) (txBytes : List (BitVec 8))
    (listOff : Nat) (t5Old t6Old : Word) :
    ∀ h, extractWalkInitShortPost txBase listLen txBytes listOff t5Old t6Old h →
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkInit) **
          bytesRegion txBase txBytes) **
        (fun st => ∃ cursor endPtr : Word,
          ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
            (.x12 ↦ᵣ (0 : Word))) st)) h := by
  intro h hp
  simp only [extractWalkInitShortPost] at hp
  -- Reassoc flat short post → (temps/bytes) ** (x10 ** x11 ** x12)
  have hp' :
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkInit) **
          bytesRegion txBase txBytes) **
        ((.x10 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
          (.x11 ↦ᵣ ((txBase + BitVec.ofNat 64 listOff) + listLen)) **
          (.x12 ↦ᵣ (0 : Word)))) h := by
    xperm_hyp hp
  obtain ⟨hL, hR, hd, hu, hRest, hRegs⟩ := hp'
  refine ⟨hL, hR, hd, hu, hRest, ?_⟩
  exact ⟨(txBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12),
    (txBase + BitVec.ofNat 64 listOff) + listLen, hRegs⟩

#print axioms extractWalkInitPrest_pcFree
#print axioms walkInitJalOff_resolves
#print axioms extractWalkInitCall
#print axioms extractWalkInitCall_short
#print axioms extractWalkInitShortPost_to_okNested
#print axioms extractWalkInitBneOk

end EvmAsm.Codegen.TxExtractToAddressSpec


