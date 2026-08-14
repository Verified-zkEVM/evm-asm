/-
  EvmAsm.Codegen.Programs.HeaderValidateParentHashSpec

  Whole-routine machine contract for `header_validate_parent_hash` (#12346
  residual callee triple).  Pre/post match the pinned premise shape in
  `ValidateHeaderParentHashCorrespondence` (PR #12362) exactly:

    hvphEntryRest / hvphCalleePost
      — x1 link, x2 at caller sp0, 32-byte frameSlotsOwn/Saved,
        a0..a3 = this/parent RLP, scratch ownership, both byte regions.

  Cut from origin/main @ db997caeb.  Program length 43.

  Inner calls (objdump-verified on stateless_guest.elf):
    +36 → headers_parent_hash (NO machine triple — named premise)
    +68 → zkvm_keccak256 one-shot (proven `zkvm_keccak256_spec_within`)

  Status (a0): 0 match, 1 RLP extract fail, 2 hash mismatch.
  Conjunct 11 depth: adapter → HVPH → headers_parent_hash → keccak.
-/

import EvmAsm.Codegen.Programs.HeadersKeccak
import EvmAsm.Codegen.Proofs.HashBridgeKeccakTop
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.TwoExitLoop

namespace EvmAsm.Codegen.HeaderValidateParentHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs

/-! ## Bases, code, and the pinned ABI shape (#12362) -/

abbrev H : Word := (GuestAddrs.header_validate_parent_hash : Word)
abbrev K : Word := (GuestAddrs.zkvm_keccak256 : Word)
abbrev P : Word := (GuestAddrs.headers_parent_hash : Word)
abbrev Claimed : Word := (GuestAddrs.hvph_claimed : Word)
abbrev Computed : Word := (GuestAddrs.hvph_computed : Word)

abbrev hvphProg : Program := headerValidateParentHash_prog
abbrev keccakProg : Program := zkvmKeccak256_prog
abbrev headersProg : Program := headersParentHash_prog

theorem hvph_length : hvphProg.length = 43 := by decide
theorem headers_length : headersProg.length = 34 := by decide

def hvphCode : CodeReq := CodeReq.ofProg H hvphProg
def keccakCode : CodeReq := CodeReq.ofProg K keccakProg
def headersCode : CodeReq := CodeReq.ofProg P headersProg

/-- HVPH plus both callees. -/
def fullCode : CodeReq :=
  hvphCode.union (headersCode.union keccakCode)

/-- 32-byte ABI frame — identical to the #12362 adapter pin. -/
def hvphFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24)]

def hvphSavedFrame : FrameDesc :=
  [(.x8, 8), (.x9, 16), (.x18, 24)]

def hvphFrameVals (ret : Word) (vals : Reg → Word) : Reg → Word :=
  fun r => if r = .x1 then ret else vals r

/-- Entry assertion — identical to adapter `hvphEntryRest`. -/
def hvphPre
    (sp0 thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word)
    (thisBytes parentBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ sp0) **
  frameSlotsOwn hvphFrame (sp0 + signExtend12 (-32 : BitVec 12)) **
  regsAt hvphSavedFrame vals **
  (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
  (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes

/-- Exit assertion — identical to adapter `hvphCalleePost`. -/
def hvphPost
    (sp0 thisPtr parentPtr ret status : Word) (vals : Reg → Word)
    (thisBytes parentBytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
  frameSlotsSaved hvphFrame (sp0 + signExtend12 (-32 : BitVec 12))
    (hvphFrameVals ret vals) **
  regsAt hvphSavedFrame vals **
  (.x10 ↦ᵣ status) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
  regOwn .x12 ** regOwn .x13 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes

theorem hvphPre_pcFree
    (sp0 thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word)
    (thisBytes parentBytes : List (BitVec 8)) :
    (hvphPre sp0 thisPtr thisLen parentPtr parentLen vals
      thisBytes parentBytes).pcFree := by
  unfold hvphPre hvphFrame hvphSavedFrame
  pcf

/-- Keccak jal at H+68 is the one-shot entry (not segments). -/
theorem hvph_keccak_jal_oneshot :
    (∀ a i, CodeReq.singleton (H + 68)
        (.JAL .x1 (jalOff GuestAddrs.zkvm_keccak256
          (GuestAddrs.header_validate_parent_hash + 68))) a = some i →
      hvphCode a = some i) ∧
    (GuestAddrs.zkvm_keccak256 : Nat) ≠ GuestAddrs.zkvm_keccak256_segments := by
  refine ⟨?_, by decide⟩
  exact CodeReq.ofProg_mem_at H (H + 68) hvphProg 17 _
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)

/-! ## Code membership helpers -/

theorem hvph_mono : ∀ a i, hvphCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi

theorem hvph_headers_disjoint : hvphCode.Disjoint headersCode := by
  unfold hvphCode headersCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [hvph_length]; decide
  · rw [headers_length]; decide
  · rw [hvph_length, headers_length]; decide

theorem hvph_keccak_disjoint : hvphCode.Disjoint keccakCode := by
  unfold hvphCode keccakCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [hvph_length]; decide
  · decide  -- zkvmKeccak256_prog.length
  · decide

/-! ## Callees (objdump-confirmed)

    `header_validate_parent_hash` is **not** self-contained:

    | Offset | Target | Machine status |
    |--------|--------|----------------|
    | **+36** | `headers_parent_hash` | **no** Progress row / no triple (emit drift only) |
    | **+68** | `zkvm_keccak256` (one-shot) | **proven** `zkvm_keccak256_spec_within` |

    Conjunct 11 chain: validate_header adapter → HVPH → headers_parent_hash → keccak.
    The HVPH top triple therefore names an explicit **`headers_parent_hash`
    premise**; keccak is discharged by the proven leaf (not a premise).
-/

/-- Objdump pin: +36 jal targets `headers_parent_hash`. -/
theorem hvph_headers_jal_mem :
    ∀ a i, CodeReq.singleton (H + 36)
        (.JAL .x1 (jalOff GuestAddrs.headers_parent_hash
          (GuestAddrs.header_validate_parent_hash + 36))) a = some i →
      hvphCode a = some i :=
  CodeReq.ofProg_mem_at H (H + 36) hvphProg 9 _
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)

/-! ## Top theorem (shape pin)

    TODO(body): compose prologue ;; headers premise ;; dispatch ;; keccak leaf ;;
    compare ;; epilogue.  Scaffold locks ABI shape + both jal pins.
-/

/-- **Shape-locked top contract** for `header_validate_parent_hash`.

    Matches #12362 adapter `hvphPre`/`hvphPost` exactly.  The statement takes a
    named `headers_parent_hash` premise (`h_headers`); the keccak call at +68 is
    *not* a premise — proofs must invoke `zkvm_keccak256_spec_within`. -/
def header_validate_parent_hash_spec_within_type
    (n nHeaders : Nat) (sp0 thisPtr thisLen parentPtr parentLen ret status : Word)
    (vals : Reg → Word)
    (thisBytes parentBytes : List (BitVec 8))
    (h_headers : Prop) : Prop :=
  h_headers →
  cpsTripleWithin n H ret fullCode
    ((.x1 ↦ᵣ ret) **
      hvphPre sp0 thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes)
    (hvphPost sp0 thisPtr parentPtr ret status vals thisBytes parentBytes)

-- Length / pin KATs used by review and by the adapter's oneshot check.
example : hvphProg.length = 43 := hvph_length
example : (GuestAddrs.zkvm_keccak256 : Nat) ≠ GuestAddrs.zkvm_keccak256_segments :=
  hvph_keccak_jal_oneshot.2

end EvmAsm.Codegen.HeaderValidateParentHashSpec
