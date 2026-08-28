/-
  EvmAsm.Codegen.Programs.BlockAccessListHashSpec

  Whole-routine contract for `block_access_list_hash` (31 instructions,
  `BlockAccessListHash.lean`): the SSZ navigation wrapper that locates the
  `block_access_list` section inside the payload and TAIL-CALLS
  `block_access_list_hash_core` to hash it.

  ## The exit shape comes first

  This routine does not return.  Its last instruction is `JAL x0,
  block_access_list_hash_core` — executed AFTER the epilogue has restored `ra`
  and popped the frame — so the callee returns directly to *our* caller.  The
  triple's exit is therefore `ret`, the value `x1` held on entry, and the
  postcondition is the CORE's postcondition verbatim: there is no state in which
  control is back inside `block_access_list_hash` with a result to describe.
  Concretely the composition is

      idx 0..29   : `cpsTripleWithin 30 W (W + 120)`   (prologue, body, epilogue)
      idx 30      : `jal0_spec_pcFree`, `W + 120 → coreB`
      core        : `block_access_list_hash_core_spec_within`, `coreB → ret`

  and nothing re-enters `W`.

  ## Navigation

    NPR          = sszBase + 16
    exec_payload = NPR + 44          = sszBase + 60
    bal_off      = u32 @ exec_payload + 528   (= sszBase + 588)
    vh_off       = u32 @ NPR + 4              (= sszBase + 20)
    bal_start    = exec_payload + bal_off
    bal_end      = NPR + vh_off

  Both `u32` pointers are `≡ 4 (mod 8)` for the linked, 8-aligned
  `sszBase = INPUT_MEM_START`, so the two reads compose against
  `bah_u32le_offset_spec_within` (`BlockAccessListHashBahOffset.lean`) and NOT
  against the flat `Region.wf` form, whose region base — and hence `a0` — must
  be dword-aligned.

  ## `bah_bal_start` is OWNED, not framed

  `bal_start` is computed before the second call and consumed after it, and the
  temporaries it would otherwise live in (`t3`/`t4`) are inside
  `bah_u32le`'s clobber set.  The guest therefore spills it to the `.bss` cell
  `bah_bal_start` (`SD` at idx 15) and reloads it (`LD` at idx 21).  That single
  dword is the only state crossing a call boundary in this routine, and it is
  carried as an OWNED cell (`memOwn` before the store, `↦ₘ bal_start` between
  the store and the reload) rather than framed: a framed `↦ₘ` would have to
  name a value the caller cannot know, and the cell is genuinely scratch.

  ## Scope note on the hashed slab (#13014, in its milder form)

  The precondition presents the BAL slab at `bal_start` as its OWN
  `bytesRegion`, disjoint from the SSZ header region the two `u32`s are read
  from.  This is the shape `block_access_list_hash_core_spec_within` already
  requires and it is inherited unchanged.

  ⚠️ `bytesRegion b bs` owns `⌈|bs|/8⌉` dwords and pins the last one to
  `packBytes` of a zero-PADDED tail, so a slab whose length is not a multiple of
  8 would silently assert that the bytes between the slab's end and the next
  dword boundary are `0x00` — an assumption about payload bytes the routine
  never reads.  Rather than let that widen in silence, `h_slab8` states
  `8 ∣ input.length` explicitly: with it the region covers whole dwords and
  claims nothing whatever about anything past the slab.  It is a stated
  restriction on which BAL sections this row covers, not a hidden one, and it is
  what keeps this row clear of #13014 proper.
-/
import EvmAsm.Codegen.Programs.BlockAccessListHashBahOffset
import EvmAsm.Codegen.Programs.BlockAccessListHashCoreSpec
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.CtrlSpecs

namespace EvmAsm.Codegen.BlockAccessListHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.BlockAccessListHashBahOffset (bahCr bah_u32le_offset_spec_within)

set_option maxRecDepth 8000

/-! ## §1  The routine, its code requirement, and its neighbours -/

/-- `block_access_list_hash` at its linked guest address. -/
abbrev W : Word := (GuestAddrs.block_access_list_hash : Word)

abbrev wProgL : List Instr := blockAccessListHash_prog

/-- The image claim for the wrapper itself. -/
abbrev wCr : CodeReq := CodeReq.ofProg W wProgL

/-- Instruction `k`'s address. -/
abbrev At (k : Nat) : Word := W + BitVec.ofNat 64 (4 * k)

/-- The `.bss` spill cell for `bal_start`. -/
abbrev balStartLoc : Word := (GuestAddrs.bah_bal_start : Word)

/-- Everything the composed triple may fetch from: this wrapper, the `bah_u32le`
    leaf it calls twice, and the core (which itself carries `zkvm_keccak256`). -/
abbrev allCode : CodeReq :=
  wCr.union (bahCr.union BlockAccessListHashCoreSpec.fullCode)

theorem wProg_len : wProgL.length = 31 := by
  simp only [wProgL, blockAccessListHash_prog]; decide

theorem wProg_bound : 4 * wProgL.length < 2 ^ 64 := by
  rw [wProg_len]; norm_num

/-- Fetching the wrapper's own instruction `k`. -/
theorem wMem (k : Nat) (ins : Instr)
    (hk : k < wProgL.length) (hins : wProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton (At k) ins a = some i → allCode a = some i := by
  intro a i h
  have hw : wCr a = some i :=
    CodeReq.ofProg_mem_at W (At k) wProgL k ins rfl hk hins wProg_bound a i h
  exact CodeReq.union_mono_left a i hw

theorem ofNat_add (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

theorem At_add (k n : Nat) : At k + BitVec.ofNat 64 (4 * n) = At (k + n) := by
  show W + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 (4 * n) = _
  rw [BitVec.add_assoc, ofNat_add]
  congr 2
  omega

theorem At_succ (k : Nat) : At k + 4 = At (k + 1) := by
  have h := At_add k 1
  rwa [show BitVec.ofNat 64 (4 * 1) = (4 : Word) from rfl] at h

/-! ## §2  Fetching the callees

    `allCode` is a three-way union.  Every pair of programs in it is
    range-separated at the linked addresses — `zkvm_keccak256`
    `[0x80003460, 0x80003574)`, `bah_u32le` `[0x8000caa0, 0x8000cad0)`,
    `block_access_list_hash_core` `[0x8000cad0, 0x8000cae8)`, this wrapper
    `[0x8000cae8, 0x8000cb64)` — so each `Disjoint` obligation is one
    `ofProg_ranges` application with `decide`able side conditions. -/

private abbrev coreW : CodeReq := BlockAccessListHashCoreSpec.wrapperCode
private abbrev keccakC : CodeReq := BlockAccessListHashCoreSpec.keccakCode

private theorem disj_w_bah : wCr.Disjoint bahCr :=
  CodeReq.Disjoint.ofProg_ranges W BlockAccessListHashBahOffset.BahB
    wProgL BlockAccessListHashBahOffset.bahProgL
    (by rw [wProg_len]; decide) (by decide) (by decide)

private theorem disj_w_coreW : wCr.Disjoint coreW :=
  CodeReq.Disjoint.ofProg_ranges W BlockAccessListHashCoreSpec.B
    wProgL blockAccessListHashCore_prog
    (by rw [wProg_len]; decide) (by decide) (by rw [wProg_len]; decide)

private theorem disj_w_keccak : wCr.Disjoint keccakC :=
  CodeReq.Disjoint.ofProg_ranges W BlockAccessListHashCoreSpec.K
    wProgL zkvmKeccak256_prog
    (by rw [wProg_len]; decide) (by decide) (by decide)

private theorem disj_bah_coreW : bahCr.Disjoint coreW :=
  CodeReq.Disjoint.ofProg_ranges BlockAccessListHashBahOffset.BahB
    BlockAccessListHashCoreSpec.B
    BlockAccessListHashBahOffset.bahProgL blockAccessListHashCore_prog
    (by decide) (by decide) (by decide)

private theorem disj_bah_keccak : bahCr.Disjoint keccakC :=
  CodeReq.Disjoint.ofProg_ranges BlockAccessListHashBahOffset.BahB
    BlockAccessListHashCoreSpec.K
    BlockAccessListHashBahOffset.bahProgL zkvmKeccak256_prog
    (by decide) (by decide) (by decide)

/-- The `bah_u32le` leaf's own code requirement, as seen from `allCode`. -/
theorem bahMem : ∀ a i, bahCr a = some i → allCode a = some i :=
  fun a i h =>
    CodeReq.mono_union_right disj_w_bah
      (fun a i h => CodeReq.union_mono_left a i h) a i h

private theorem coreWMem : ∀ a i, coreW a = some i → allCode a = some i :=
  fun a i h =>
    CodeReq.mono_union_right disj_w_coreW
      (fun a i h =>
        CodeReq.mono_union_right disj_bah_coreW
          (fun a i h => CodeReq.union_mono_left a i h) a i h) a i h

private theorem keccakMem : ∀ a i, keccakC a = some i → allCode a = some i :=
  fun a i h =>
    CodeReq.mono_union_right disj_w_keccak
      (fun a i h =>
        CodeReq.mono_union_right disj_bah_keccak
          (fun a i h =>
            CodeReq.mono_union_right
              (CodeReq.Disjoint.ofProg_ranges BlockAccessListHashCoreSpec.B
                BlockAccessListHashCoreSpec.K
                blockAccessListHashCore_prog zkvmKeccak256_prog
                (by decide) (by decide) (by decide))
              (fun a i h => h) a i h) a i h) a i h

/-- The core's whole code requirement (its own six instructions plus the
    `zkvm_keccak256` body it carries), as seen from `allCode`. -/
theorem coreMem :
    ∀ a i, BlockAccessListHashCoreSpec.fullCode a = some i → allCode a = some i :=
  CodeReq.union_split_mono coreWMem keccakMem

/-! ## §3  The exit shape: the tail jump

    Index 30 is `JAL x0, block_access_list_hash_core`, reached with the frame
    already popped and `ra` already restored.  It moves the PC and nothing
    else, so any pc-free assertion survives it unchanged — which is what lets
    the core's precondition be established BEFORE the jump and consumed after
    it. -/

theorem tail_target :
    At 30 + signExtend21
        (jalOff GuestAddrs.block_access_list_hash_core
          (GuestAddrs.block_access_list_hash + 120))
      = BlockAccessListHashCoreSpec.B := by
  decide

theorem tail_jump_spec (P : Assertion) (hP : P.pcFree) :
    cpsTripleWithin 1 (At 30) BlockAccessListHashCoreSpec.B allCode P P := by
  have h := jal0_spec_pcFree
    (jalOff GuestAddrs.block_access_list_hash_core
      (GuestAddrs.block_access_list_hash + 120))
    (At 30) hP
  rw [tail_target] at h
  exact cpsTripleWithin_extend_code
    (wMem 30 _ (by rw [wProg_len]; decide) (by rfl)) h

end EvmAsm.Codegen.BlockAccessListHashSpec
