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

end EvmAsm.Codegen.BlockAccessListHashSpec
