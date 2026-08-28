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
import EvmAsm.Rv64.Tactics.XCancelStruct

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

/-! ## §4  Stack geometry

    The prologue drops `sp` by 32 and fills four slots; the core, reached after
    the epilogue has restored `sp`, wants `memOwn (sp0 - 16)` plus
    `stackFree (sp0 - 16) 4`, i.e. cells at `sp0 - 48 … sp0 - 16`.  Six owned
    dwords below `sp0` cover both, with `sp0 - 8` left over and framed. -/

/-- `sp` inside the frame. -/
abbrev sp1 (sp0 : Word) : Word := sp0 + signExtend12 (-32 : BitVec 12)

theorem sp1_slot0 (sp0 : Word) :
    sp1 sp0 + signExtend12 (0 : BitVec 12) = sp0 - BitVec.ofNat 64 32 := by
  show sp0 + signExtend12 (-32 : BitVec 12) + signExtend12 (0 : BitVec 12) = _
  rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide,
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
  bv_omega

theorem sp1_slot8 (sp0 : Word) :
    sp1 sp0 + signExtend12 (8 : BitVec 12) = sp0 - BitVec.ofNat 64 24 := by
  show sp0 + signExtend12 (-32 : BitVec 12) + signExtend12 (8 : BitVec 12) = _
  rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide,
    show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
  bv_omega

theorem sp1_slot16 (sp0 : Word) :
    sp1 sp0 + signExtend12 (16 : BitVec 12) = sp0 - BitVec.ofNat 64 16 := by
  show sp0 + signExtend12 (-32 : BitVec 12) + signExtend12 (16 : BitVec 12) = _
  rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide,
    show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]
  bv_omega

theorem sp1_slot24 (sp0 : Word) :
    sp1 sp0 + signExtend12 (24 : BitVec 12) = sp0 - BitVec.ofNat 64 8 := by
  show sp0 + signExtend12 (-32 : BitVec 12) + signExtend12 (24 : BitVec 12) = _
  rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide,
    show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]
  bv_omega

/-- The epilogue's `addi sp, sp, 32` undoes the prologue's. -/
theorem sp1_restore (sp0 : Word) :
    sp1 sp0 + signExtend12 (32 : BitVec 12) = sp0 := by
  show sp0 + signExtend12 (-32 : BitVec 12) + signExtend12 (32 : BitVec 12) = _
  rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide,
    show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]
  bv_omega

/-- The six owned dwords, split into the four the prologue uses and the two
    below them that only the core sees. -/
theorem stackFree6_split (sp0 : Word) :
    stackFree sp0 6 =
      (memOwn (sp0 - BitVec.ofNat 64 48) ** memOwn (sp0 - BitVec.ofNat 64 40) **
        memOwn (sp0 - BitVec.ofNat 64 32) ** memOwn (sp0 - BitVec.ofNat 64 24) **
        memOwn (sp0 - BitVec.ofNat 64 16) ** memOwn (sp0 - BitVec.ofNat 64 8)) := by
  show (memOwn (sp0 - BitVec.ofNat 64 (8 * 6)) ** memOwn (sp0 - BitVec.ofNat 64 (8 * 5)) **
      memOwn (sp0 - BitVec.ofNat 64 (8 * 4)) ** memOwn (sp0 - BitVec.ofNat 64 (8 * 3)) **
      memOwn (sp0 - BitVec.ofNat 64 (8 * 2)) ** memOwn (sp0 - BitVec.ofNat 64 (8 * 1)) **
      empAssertion) = _
  rw [sepConj_emp_right']

/-! ## §5  Prologue (idx 0..4): drop `sp`, save `ra`, `s0`, `s1`, `s2` -/

/-- A local pc-freeness driver: the built-in `pcf` stops at `bytesRegion` and at
    an ambient hypothesis, both of which appear in every frame here. -/
macro "pcf_b" : tactic =>
  `(tactic| repeat (first
      | apply pcFree_sepConj
      | exact pcFree_regIs | exact pcFree_memIs
      | exact pcFree_regOwn | exact pcFree_memOwn | exact pcFree_emp
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regOwns _
      | exact pcFree_stackFree _ _
      | assumption))

theorem prologue_spec (sp0 ret v8 v9 v18 : Word) (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 5 (At 0) (At 5) allCode
      ((((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) ** ((.x8 : Reg) ↦ᵣ v8) **
        ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) **
        memOwn (sp0 - BitVec.ofNat 64 32) ** memOwn (sp0 - BitVec.ofNat 64 24) **
        memOwn (sp0 - BitVec.ofNat 64 16) ** memOwn (sp0 - BitVec.ofNat 64 8)) ** R)
      ((((.x2 : Reg) ↦ᵣ sp1 sp0) ** ((.x1 : Reg) ↦ᵣ ret) ** ((.x8 : Reg) ↦ᵣ v8) **
        ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) **
        ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
        ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) ** ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18)) ** R) := by
  -- idx 0: addi sp, sp, -32
  have s0 := cpsTripleWithin_extend_code
    (wMem 0 (.ADDI .x2 .x2 (-32 : BitVec 12)) (by rw [wProg_len]; decide) (by rfl))
    (addi_spec_gen_same_within .x2 sp0 (-32 : BitVec 12) (At 0) (by decide))
  rw [At_succ 0] at s0
  have f0 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
      ((.x18 : Reg) ↦ᵣ v18) **
      memOwn (sp0 - BitVec.ofNat 64 32) ** memOwn (sp0 - BitVec.ofNat 64 24) **
      memOwn (sp0 - BitVec.ofNat 64 16) ** memOwn (sp0 - BitVec.ofNat 64 8) ** R)
    (by pcf_b) s0
  -- idx 1: sd ra, 0(sp)
  have s1 := cpsTripleWithin_extend_code
    (wMem 1 (.SD .x2 .x1 (0 : BitVec 12)) (by rw [wProg_len]; decide) (by rfl))
    (sd_spec_gen_own_within .x2 .x1 (sp1 sp0) ret (0 : BitVec 12) (At 1))
  rw [At_succ 1, sp1_slot0] at s1
  have f1 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) **
      memOwn (sp0 - BitVec.ofNat 64 24) ** memOwn (sp0 - BitVec.ofNat 64 16) **
      memOwn (sp0 - BitVec.ofNat 64 8) ** R)
    (by pcf_b) s1
  -- idx 2: sd s0, 8(sp)
  have s2 := cpsTripleWithin_extend_code
    (wMem 2 (.SD .x2 .x8 (8 : BitVec 12)) (by rw [wProg_len]; decide) (by rfl))
    (sd_spec_gen_own_within .x2 .x8 (sp1 sp0) v8 (8 : BitVec 12) (At 2))
  rw [At_succ 2, sp1_slot8] at s2
  have f2 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) **
      ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** memOwn (sp0 - BitVec.ofNat 64 16) **
      memOwn (sp0 - BitVec.ofNat 64 8) ** R)
    (by pcf_b) s2
  -- idx 3: sd s1, 16(sp)
  have s3 := cpsTripleWithin_extend_code
    (wMem 3 (.SD .x2 .x9 (16 : BitVec 12)) (by rw [wProg_len]; decide) (by rfl))
    (sd_spec_gen_own_within .x2 .x9 (sp1 sp0) v9 (16 : BitVec 12) (At 3))
  rw [At_succ 3, sp1_slot16] at s3
  have f3 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** ((.x8 : Reg) ↦ᵣ v8) ** ((.x18 : Reg) ↦ᵣ v18) **
      ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
      memOwn (sp0 - BitVec.ofNat 64 8) ** R)
    (by pcf_b) s3
  -- idx 4: sd s2, 24(sp)
  have s4 := cpsTripleWithin_extend_code
    (wMem 4 (.SD .x2 .x18 (24 : BitVec 12)) (by rw [wProg_len]; decide) (by rfl))
    (sd_spec_gen_own_within .x2 .x18 (sp1 sp0) v18 (24 : BitVec 12) (At 4))
  rw [At_succ 4, sp1_slot24] at s4
  have f4 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
      ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
      ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) ** R)
    (by pcf_b) s4
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) f0 f1
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c1 f2
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c2 f3
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c3 f4
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c4

/-! ## §6  SSZ navigation addresses

    The guest reaches the two `u32` fields by three chained `addi`s.  These
    lemmas put the results in the `base + BitVec.ofNat 64 off` form that
    `bah_u32le_offset_spec_within` consumes, which is where the offsets `588`
    and `20` — and hence the `≡ 4 (mod 8)` misalignment — become explicit. -/

/-- `NPR = sszBase + 16`. -/
abbrev npr (b : Word) : Word := b + signExtend12 (16 : BitVec 12)

/-- `exec_payload = NPR + 44 = sszBase + 60`. -/
abbrev execP (b : Word) : Word := npr b + signExtend12 (44 : BitVec 12)

theorem field1_addr (b : Word) :
    execP b + signExtend12 (528 : BitVec 12) = b + BitVec.ofNat 64 588 := by
  show b + signExtend12 (16 : BitVec 12) + signExtend12 (44 : BitVec 12)
      + signExtend12 (528 : BitVec 12) = _
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
    show signExtend12 (44 : BitVec 12) = (44 : Word) from by decide,
    show signExtend12 (528 : BitVec 12) = (528 : Word) from by decide,
    show (BitVec.ofNat 64 588 : Word) = (588 : Word) from by decide]
  bv_omega

theorem field2_addr (b : Word) :
    npr b + signExtend12 (4 : BitVec 12) = b + BitVec.ofNat 64 20 := by
  show b + signExtend12 (16 : BitVec 12) + signExtend12 (4 : BitVec 12) = _
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
    show signExtend12 (4 : BitVec 12) = (4 : Word) from by decide,
    show (BitVec.ofNat 64 20 : Word) = (20 : Word) from by decide]
  bv_omega

/-! ## §7  Body before the first call (idx 5..9)

    `s0 := a0` (the SSZ base), `s1 := a1` (the digest destination), `s2 := NPR`,
    `t3 := exec_payload`, `a0 := &bal_off`. -/

theorem setup_spec (b outPtr v8 v9 v18 v28 : Word) (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 5 (At 5) (At 10) allCode
      ((((.x10 : Reg) ↦ᵣ b) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x8 : Reg) ↦ᵣ v8) **
        ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) ** ((.x28 : Reg) ↦ᵣ v28)) ** R)
      ((((.x10 : Reg) ↦ᵣ (b + BitVec.ofNat 64 588)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        ((.x8 : Reg) ↦ᵣ b) ** ((.x9 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ npr b) **
        ((.x28 : Reg) ↦ᵣ execP b)) ** R) := by
  -- idx 5: mv s0, a0
  have s5 := cpsTripleWithin_extend_code
    (wMem 5 (.MV .x8 .x10) (by rw [wProg_len]; decide) (by rfl))
    (mv_spec_gen_within .x8 .x10 b v8 (At 5) (by decide))
  rw [At_succ 5] at s5
  have f5 := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ outPtr) ** ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) **
      ((.x28 : Reg) ↦ᵣ v28) ** R)
    (by pcf_b) s5
  -- idx 6: mv s1, a1
  have s6 := cpsTripleWithin_extend_code
    (wMem 6 (.MV .x9 .x11) (by rw [wProg_len]; decide) (by rfl))
    (mv_spec_gen_within .x9 .x11 outPtr v9 (At 6) (by decide))
  rw [At_succ 6] at s6
  have f6 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ b) ** ((.x8 : Reg) ↦ᵣ b) ** ((.x18 : Reg) ↦ᵣ v18) **
      ((.x28 : Reg) ↦ᵣ v28) ** R)
    (by pcf_b) s6
  -- idx 7: addi s2, s0, 16
  have s7 := cpsTripleWithin_extend_code
    (wMem 7 (.ADDI .x18 .x8 (16 : BitVec 12)) (by rw [wProg_len]; decide) (by rfl))
    (addi_spec_gen_within .x18 .x8 v18 b (16 : BitVec 12) (At 7) (by decide))
  rw [At_succ 7] at s7
  have f7 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ b) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x28 : Reg) ↦ᵣ v28) ** R)
    (by pcf_b) s7
  -- idx 8: addi t3, s2, 44
  have s8 := cpsTripleWithin_extend_code
    (wMem 8 (.ADDI .x28 .x18 (44 : BitVec 12)) (by rw [wProg_len]; decide) (by rfl))
    (addi_spec_gen_within .x28 .x18 v28 (npr b) (44 : BitVec 12) (At 8) (by decide))
  rw [At_succ 8] at s8
  have f8 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ b) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x8 : Reg) ↦ᵣ b) **
      ((.x9 : Reg) ↦ᵣ outPtr) ** R)
    (by pcf_b) s8
  -- idx 9: addi a0, t3, 528
  have s9 := cpsTripleWithin_extend_code
    (wMem 9 (.ADDI .x10 .x28 (528 : BitVec 12)) (by rw [wProg_len]; decide) (by rfl))
    (addi_spec_gen_within .x10 .x28 b (execP b) (528 : BitVec 12) (At 9) (by decide))
  rw [At_succ 9, field1_addr] at s9
  have f9 := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ outPtr) ** ((.x8 : Reg) ↦ᵣ b) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x18 : Reg) ↦ᵣ npr b) ** R)
    (by pcf_b) s9
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) f5 f6
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c1 f7
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c2 f8
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c3 f9
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c4

end EvmAsm.Codegen.BlockAccessListHashSpec
