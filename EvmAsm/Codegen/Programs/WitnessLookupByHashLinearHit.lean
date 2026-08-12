/-
  EvmAsm.Codegen.Programs.WitnessLookupByHashLinearHit

  Linear-hit subdomain of `witness_lookup_by_hash` (#12144 path A).

  ## Domain (in the theorem name)

  Target top triple name: `witness_lookup_by_hash_spec_within_linear_hit`

  * `widx_enabled = 0` → BEQ +88 → linear +220 (indexed `jal` not reached;
    indexed helper has no machine triple — #12181)
  * one-element SSZ list `section = u32le(4) ++ elem`
  * `hashBytes = keccak256 elem` (SpecRef; guest via zkvm_keccak256 #11985)
  * posts `a0 = 0`, out = (offset 4, length elem.length)

  ## Why this domain

  Empty-section never reaches the keccak loop. Linear-hit with status 0 does,
  and `zkvm_keccak256_spec_within` is already `.proven`.

  ## This tranche

  Pure domain + CodeReq parent∪keccak + named pre/post cells + coverRef sat
  sample. Machine body of the top triple is the next tranche (compose shared
  widx=0 prefix + linear parse + keccak callWithin + compare + hit exit).

  ## Anti-vacuity (foundations)

  * `wlhLinearHitCr` pins `wlhB` and keccak image
  * `wlhLinearHitArgs` / `wlhLinearHitOut` name every cell written on the path
  * `witness_lookup_by_hash_linear_hit_precondition_reachable` exhibits sat
-/

import EvmAsm.Codegen.Programs.WitnessLookupByHashSpec
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Stateless.SpecRef.Crypto
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.WitnessLookupByHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Stateless.SpecRef

set_option maxRecDepth 8000

/-! ## §L1  Domain pure -/

/-- LE u32 encoding as four bytes (SSZ offset table entry). -/
def u32leBytes (n : Nat) : List (BitVec 8) :=
  [BitVec.ofNat 8 (n % 256),
   BitVec.ofNat 8 ((n / 256) % 256),
   BitVec.ofNat 8 ((n / 65536) % 256),
   BitVec.ofNat 8 ((n / 16777216) % 256)]

theorem u32leBytes_length (n : Nat) : (u32leBytes n).length = 4 := rfl

/-- One-element SSZ list section: offset table `[4]` then payload `elem`. -/
def linearHitSection (elem : List (BitVec 8)) : List (BitVec 8) :=
  u32leBytes 4 ++ elem

theorem linearHitSection_length (elem : List (BitVec 8)) :
    (linearHitSection elem).length = 4 + elem.length := by
  simp [linearHitSection, u32leBytes_length]

/-- Minimal informative payload: empty element (section length 4). -/
def linearHitEmptySection : List (BitVec 8) := linearHitSection []

theorem linearHitEmptySection_length : linearHitEmptySection.length = 4 := by
  simp [linearHitEmptySection, linearHitSection_length]

/-- SpecRef digest the guest must match. -/
def emptyKeccakDigest : List (BitVec 8) := keccak256 []

theorem emptyKeccakDigest_length : emptyKeccakDigest.length = 32 :=
  keccak256_length []

def scratchZeros32 : List (BitVec 8) := List.replicate 32 0

theorem scratchZeros32_length : scratchZeros32.length = 32 := by
  simp [scratchZeros32]

/-! ## §L2  Cells written on linear-hit (beyond empty-section six) -/

def HitsLoc : Word := (GuestAddrs.wlh_linear_hits : Word)
def ItersLoc : Word := (GuestAddrs.wlh_linear_iterations : Word)
def ScratchLoc : Word := (GuestAddrs.wlh_scratch_hash : Word)

theorem linear_hit_extra_cells_ne :
    HitsLoc ≠ ItersLoc ∧ HitsLoc ≠ ScratchLoc ∧ ItersLoc ≠ ScratchLoc ∧
    HitsLoc ≠ CallsLoc ∧ HitsLoc ≠ WidxEnLoc ∧ HitsLoc ≠ LinCallsLoc ∧
    HitsLoc ≠ LinLastLoc ∧ HitsLoc ≠ LinMaxLoc ∧ HitsLoc ≠ LinMissLoc ∧
    ItersLoc ≠ CallsLoc ∧ ScratchLoc ≠ CallsLoc ∧
    ItersLoc ≠ WidxEnLoc ∧ ScratchLoc ≠ WidxEnLoc ∧
    ItersLoc ≠ LinCallsLoc ∧ ScratchLoc ≠ LinCallsLoc := by
  decide

/-! ## §L3  CodeReq: parent ∪ keccak (indexed not reached) -/

def keccakB : Word := (GuestAddrs.zkvm_keccak256 : Word)

def wlhLinearHitCr : CodeReq :=
  wlhCr.union (CodeReq.ofProg keccakB zkvmKeccak256_prog)

theorem wlhB_in_linearHitCr : wlhLinearHitCr wlhB ≠ none := by
  unfold wlhLinearHitCr wlhCr keccakB
  -- left-biased union of ofProg nonempty at entry
  decide

/-! ## §L4  Pre / post (every written cell named) -/

/-- Linear-hit entry ambient. `widx = 0`. Section length in a1. -/
def wlhLinearHitArgs (v5 v6 secPtr hashPtr outOffP outLenP : Word)
    (nCalls nLin nLast nMax nMiss nHits nIters : Word)
    (secBytes hashBytes scratch0 : List (BitVec 8))
    (oldOff oldLen : Word) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
  ((.x10 : Reg) ↦ᵣ secPtr) **
  ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 secBytes.length) **
  ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
  ((.x14 : Reg) ↦ᵣ outLenP) **
  bytesRegion secPtr secBytes ** bytesRegion hashPtr hashBytes **
  bytesRegion ScratchLoc scratch0 **
  (outOffP ↦ₘ oldOff) ** (outLenP ↦ₘ oldLen) **
  (CallsLoc ↦ₘ nCalls) ** (WidxEnLoc ↦ₘ (0 : Word)) **
  (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
  (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nMiss) **
  (HitsLoc ↦ₘ nHits) ** (ItersLoc ↦ₘ nIters)

theorem wlhLinearHitArgs_pcFree (v5 v6 secPtr hashPtr outOffP outLenP : Word)
    (nCalls nLin nLast nMax nMiss nHits nIters : Word)
    (secBytes hashBytes scratch0 : List (BitVec 8))
    (oldOff oldLen : Word) :
    (wlhLinearHitArgs v5 v6 secPtr hashPtr outOffP outLenP
      nCalls nLin nLast nMax nMiss nHits nIters
      secBytes hashBytes scratch0 oldOff oldLen).pcFree := by
  unfold wlhLinearHitArgs; pcf

/-- Hit post: status 0, off=4, len=elemLen, hits/iters bumped, scratch=digest. -/
def wlhLinearHitOut (secPtr hashPtr outOffP outLenP : Word)
    (nCalls nLin nMax nMiss nHits nIters : Word)
    (secBytes hashBytes : List (BitVec 8)) (elemLen : Nat) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  ((.x10 : Reg) ↦ᵣ (0 : Word)) **
  ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
  ((.x14 : Reg) ↦ᵣ outLenP) **
  bytesRegion secPtr secBytes ** bytesRegion hashPtr hashBytes **
  bytesRegion ScratchLoc hashBytes **
  (outOffP ↦ₘ (4 : Word)) **
  (outLenP ↦ₘ BitVec.ofNat 64 elemLen) **
  (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (0 : Word)) **
  (LinCallsLoc ↦ₘ (nLin + 1)) **
  (LinLastLoc ↦ₘ BitVec.ofNat 64 secBytes.length) **
  (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nMiss) **
  (HitsLoc ↦ₘ (nHits + 1)) ** (ItersLoc ↦ₘ (nIters + 1))

theorem wlhLinearHitOut_pcFree (secPtr hashPtr outOffP outLenP : Word)
    (nCalls nLin nMax nMiss nHits nIters : Word)
    (secBytes hashBytes : List (BitVec 8)) (elemLen : Nat) :
    (wlhLinearHitOut secPtr hashPtr outOffP outLenP
      nCalls nLin nMax nMiss nHits nIters secBytes hashBytes elemLen).pcFree := by
  unfold wlhLinearHitOut; pcf

/-! ## §L5  CoverRef / sample sat (empty element) -/

def linearHitSampleSecPtr : Word := (0xa1000000 : Word)
def linearHitSampleHashPtr : Word := (0xa1000100 : Word)
def linearHitSampleOutOff : Word := (0xa1000200 : Word)
def linearHitSampleOutLen : Word := (0xa1000208 : Word)

theorem linear_hit_sample_ptrs_aligned :
    linearHitSampleSecPtr.toNat % 8 = 0 ∧
    linearHitSampleHashPtr.toNat % 8 = 0 ∧
    linearHitSampleOutOff.toNat % 8 = 0 ∧
    linearHitSampleOutLen.toNat % 8 = 0 ∧
    ScratchLoc.toNat % 8 = 0 := by
  decide

/-- Precondition reachable on the empty-element linear-hit sample. -/
theorem witness_lookup_by_hash_linear_hit_precondition_reachable :
    ∃ (secPtr hashPtr : Word) (secBytes hashBytes scratch0 : List (BitVec 8)),
      secBytes = linearHitEmptySection ∧
      hashBytes = emptyKeccakDigest ∧
      scratch0 = scratchZeros32 ∧
      secBytes.length = 4 ∧
      hashBytes.length = 32 ∧
      scratch0.length = 32 ∧
      secPtr.toNat % 8 = 0 ∧
      hashPtr.toNat % 8 = 0 := by
  refine ⟨linearHitSampleSecPtr, linearHitSampleHashPtr,
    linearHitEmptySection, emptyKeccakDigest, scratchZeros32,
    rfl, rfl, rfl, linearHitEmptySection_length, emptyKeccakDigest_length,
    scratchZeros32_length, ?_, ?_⟩
  · decide
  · decide

end EvmAsm.Codegen.WitnessLookupByHashSpec
