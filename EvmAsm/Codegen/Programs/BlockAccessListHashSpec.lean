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

    `allCode` is a three-way union.  Its four programs — `zkvm_keccak256`,
    `bah_u32le`, `block_access_list_hash_core`, and this wrapper — occupy
    pairwise disjoint `[base, base + 4 * length)` windows at their linked
    addresses, with `bah_u32le`, the core and the wrapper laid out
    consecutively in that order.  So every `Disjoint` obligation below is one
    `ofProg_ranges` application whose three side conditions are `decide`able
    from `GuestAddrs` and the program lengths.

    ⚠️ The windows are deliberately NOT written out here as hex.  Spelling a
    live `GuestAddrs.*` value as a literal — even in prose — is the #12498
    defect, and `check-no-hardcoded-guest-pc.sh` reads comments too: an earlier
    draft of this block listed all four ranges and the gate correctly rejected
    it.  The extents belong to `GuestAddrs` and to `nm`, not to a docstring
    that cannot be re-derived when the image moves. -/

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

/-! ## §8  The two `bah_u32le` calls

    Both are `jal ra, bah_u32le` with `a0` an INTERIOR, 4-mod-8 pointer into the
    SSZ region, so both consume `bah_u32le_offset_spec_within` and neither could
    consume the flat `Region.wf` form.  The leaf leaves `t0`/`t1` owned. -/

theorem call1_spec (b : Word) (hdr : List (BitVec 8)) (vRa v5 v6 : Word)
    (R : Assertion) (hR : R.pcFree)
    (h_align : b.toNat % 8 = 0)
    (h_fit : 588 + 4 ≤ hdr.length)
    (h_over : b.toNat + (588 + 3) < 2 ^ 64)
    (h_valid : ∀ k, k < hdr.length →
      isValidByteAccess (b + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (1 + 12) (At 10) (At 11) allCode
      ((((.x1 : Reg) ↦ᵣ vRa) ** ((.x10 : Reg) ↦ᵣ (b + BitVec.ofNat 64 588)) **
        ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion b hdr) ** R)
      ((((.x1 : Reg) ↦ᵣ At 11) **
        ((.x10 : Reg) ↦ᵣ SgLoadU32leSAsm.leU32 (hdr.drop 588) 0) **
        regOwn .x5 ** regOwn .x6 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion b hdr) ** R) := by
  have hcallee0 := bah_u32le_offset_spec_within b 588 hdr (At 11) v5 v6
    h_align h_fit h_over h_valid
  rw [show ((At 11 : Word) &&& ~~~(1 : Word)) = At 11 from by decide] at hcallee0
  have hcallee := cpsTripleWithin_extend_code bahMem hcallee0
  have hframed := cpsTripleWithin_frameR R hR hcallee
  have hcallee' :
      cpsTripleWithin 12 BlockAccessListHashBahOffset.BahB (At 10 + 4) allCode
        (((.x1 : Reg) ↦ᵣ (At 10 + 4)) **
          (((.x10 : Reg) ↦ᵣ (b + BitVec.ofNat 64 588)) ** ((.x5 : Reg) ↦ᵣ v5) **
            ((.x6 : Reg) ↦ᵣ v6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            bytesRegion b hdr ** R))
        (((.x1 : Reg) ↦ᵣ (At 10 + 4)) **
          (((.x10 : Reg) ↦ᵣ SgLoadU32leSAsm.leU32 (hdr.drop 588) 0) **
            regOwn .x5 ** regOwn .x6 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            bytesRegion b hdr ** R)) := by
    rw [At_succ 10]
    exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
      (fun _ hq => by xcancel_struct hq) hframed
  have hcall := callWithin_spec (At 10) BlockAccessListHashBahOffset.BahB vRa
    (jalOff GuestAddrs.bah_u32le (GuestAddrs.block_access_list_hash + 40)) 12
    (by decide)
    (wMem 10 _ (by rw [wProg_len]; decide) (by rfl))
    (by pcf_b)
    hcallee'
  rw [At_succ 10] at hcall
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) hcall

/-! ## §9  Between the calls (idx 11..16)

    `t3` and `t4` are recomputed because `bah_u32le` owns them, `bal_start` is
    spilled to `bah_bal_start` (the one piece of state that crosses the second
    call), and `a0` is pointed at the `vh_off` field. -/

private theorem la13_hi :
    Codegen.laHi GuestAddrs.bah_bal_start (GuestAddrs.block_access_list_hash + 52)
      = Rv64.laHi (At 13) balStartLoc := by decide

private theorem la13_lo :
    Codegen.laLo GuestAddrs.bah_bal_start (GuestAddrs.block_access_list_hash + 52)
      = Rv64.laLo (At 13) balStartLoc := by decide

private theorem la13_range : laInRange (At 13) balStartLoc := by decide

theorem mid_spec (b balOffW v5 v28 v29 : Word) (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 6 (At 11) (At 17) allCode
      ((((.x10 : Reg) ↦ᵣ balOffW) ** ((.x18 : Reg) ↦ᵣ npr b) **
        ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x5 : Reg) ↦ᵣ v5) **
        memOwn balStartLoc) ** R)
      ((((.x10 : Reg) ↦ᵣ (b + BitVec.ofNat 64 20)) ** ((.x18 : Reg) ↦ᵣ npr b) **
        ((.x28 : Reg) ↦ᵣ execP b) ** ((.x29 : Reg) ↦ᵣ (execP b + balOffW)) **
        ((.x5 : Reg) ↦ᵣ balStartLoc) **
        (balStartLoc ↦ₘ (execP b + balOffW))) ** R) := by
  -- idx 11: addi t3, s2, 44
  have s11 := cpsTripleWithin_extend_code
    (wMem 11 (.ADDI .x28 .x18 (44 : BitVec 12)) (by rw [wProg_len]; decide) (by rfl))
    (addi_spec_gen_within .x28 .x18 v28 (npr b) (44 : BitVec 12) (At 11) (by decide))
  rw [At_succ 11] at s11
  have f11 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ balOffW) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x5 : Reg) ↦ᵣ v5) **
      memOwn balStartLoc ** R)
    (by pcf_b) s11
  -- idx 12: add t4, t3, a0
  have s12 := cpsTripleWithin_extend_code
    (wMem 12 (.ADD .x29 .x28 .x10) (by rw [wProg_len]; decide) (by rfl))
    (add_spec_within .x29 .x28 .x10 (execP b) balOffW v29 (At 12) (by decide))
  rw [At_succ 12] at s12
  have f12 := cpsTripleWithin_frameR
    (((.x18 : Reg) ↦ᵣ npr b) ** ((.x5 : Reg) ↦ᵣ v5) ** memOwn balStartLoc ** R)
    (by pcf_b) s12
  -- idx 13..14: la t0, bah_bal_start
  have s13 := la_materialize_within .x5 v5 (At 13) balStartLoc (by decide) la13_range
    (by
      rw [show Rv64.laHi (At 13) balStartLoc
          = Codegen.laHi GuestAddrs.bah_bal_start
              (GuestAddrs.block_access_list_hash + 52) from la13_hi.symm]
      exact wMem 13 _ (by rw [wProg_len]; decide) (by rfl))
    (by
      rw [show Rv64.laLo (At 13) balStartLoc
          = Codegen.laLo GuestAddrs.bah_bal_start
              (GuestAddrs.block_access_list_hash + 52) from la13_lo.symm,
        At_succ 13]
      exact wMem 14 _ (by rw [wProg_len]; decide) (by rfl))
  rw [show (At 13 + 8 : Word) = At 15 from by
    have h := At_add 13 2
    rwa [show BitVec.ofNat 64 (4 * 2) = (8 : Word) from rfl] at h] at s13
  have f13 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ balOffW) ** ((.x18 : Reg) ↦ᵣ npr b) **
      ((.x28 : Reg) ↦ᵣ execP b) ** ((.x29 : Reg) ↦ᵣ (execP b + balOffW)) **
      memOwn balStartLoc ** R)
    (by pcf_b) s13
  -- idx 15: sd t4, 0(t0)
  have s15 := cpsTripleWithin_extend_code
    (wMem 15 (.SD .x5 .x29 (0 : BitVec 12)) (by rw [wProg_len]; decide) (by rfl))
    (sd_spec_gen_own_within .x5 .x29 balStartLoc (execP b + balOffW)
      (0 : BitVec 12) (At 15))
  rw [At_succ 15,
    show balStartLoc + signExtend12 (0 : BitVec 12) = balStartLoc from by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at s15
  have f15 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ balOffW) ** ((.x18 : Reg) ↦ᵣ npr b) **
      ((.x28 : Reg) ↦ᵣ execP b) ** R)
    (by pcf_b) s15
  -- idx 16: addi a0, s2, 4
  have s16 := cpsTripleWithin_extend_code
    (wMem 16 (.ADDI .x10 .x18 (4 : BitVec 12)) (by rw [wProg_len]; decide) (by rfl))
    (addi_spec_gen_within .x10 .x18 balOffW (npr b) (4 : BitVec 12) (At 16) (by decide))
  rw [At_succ 16, field2_addr] at s16
  have f16 := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ execP b) ** ((.x29 : Reg) ↦ᵣ (execP b + balOffW)) **
      ((.x5 : Reg) ↦ᵣ balStartLoc) ** (balStartLoc ↦ₘ (execP b + balOffW)) ** R)
    (by pcf_b) s16
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) f11 f12
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c1 f13
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c2 f15
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c3 f16
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c4

/-! ## §10  The second call (idx 17) -/

theorem call2_spec (b : Word) (hdr : List (BitVec 8)) (vRa v5 v6 : Word)
    (R : Assertion) (hR : R.pcFree)
    (h_align : b.toNat % 8 = 0)
    (h_fit : 20 + 4 ≤ hdr.length)
    (h_over : b.toNat + (20 + 3) < 2 ^ 64)
    (h_valid : ∀ k, k < hdr.length →
      isValidByteAccess (b + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (1 + 12) (At 17) (At 18) allCode
      ((((.x1 : Reg) ↦ᵣ vRa) ** ((.x10 : Reg) ↦ᵣ (b + BitVec.ofNat 64 20)) **
        ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion b hdr) ** R)
      ((((.x1 : Reg) ↦ᵣ At 18) **
        ((.x10 : Reg) ↦ᵣ SgLoadU32leSAsm.leU32 (hdr.drop 20) 0) **
        regOwn .x5 ** regOwn .x6 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion b hdr) ** R) := by
  have hcallee0 := bah_u32le_offset_spec_within b 20 hdr (At 18) v5 v6
    h_align h_fit h_over h_valid
  rw [show ((At 18 : Word) &&& ~~~(1 : Word)) = At 18 from by decide] at hcallee0
  have hcallee := cpsTripleWithin_extend_code bahMem hcallee0
  have hframed := cpsTripleWithin_frameR R hR hcallee
  have hcallee' :
      cpsTripleWithin 12 BlockAccessListHashBahOffset.BahB (At 17 + 4) allCode
        (((.x1 : Reg) ↦ᵣ (At 17 + 4)) **
          (((.x10 : Reg) ↦ᵣ (b + BitVec.ofNat 64 20)) ** ((.x5 : Reg) ↦ᵣ v5) **
            ((.x6 : Reg) ↦ᵣ v6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            bytesRegion b hdr ** R))
        (((.x1 : Reg) ↦ᵣ (At 17 + 4)) **
          (((.x10 : Reg) ↦ᵣ SgLoadU32leSAsm.leU32 (hdr.drop 20) 0) **
            regOwn .x5 ** regOwn .x6 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            bytesRegion b hdr ** R)) := by
    rw [At_succ 17]
    exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
      (fun _ hq => by xcancel_struct hq) hframed
  have hcall := callWithin_spec (At 17) BlockAccessListHashBahOffset.BahB vRa
    (jalOff GuestAddrs.bah_u32le (GuestAddrs.block_access_list_hash + 68)) 12
    (by decide)
    (wMem 17 _ (by rw [wProg_len]; decide) (by rfl))
    (by pcf_b)
    hcallee'
  rw [At_succ 17] at hcall
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) hcall

/-! ## §11  After the second call (idx 18..24)

    `bal_end` is formed, `bal_start` is RELOADED from the spill cell, and the
    core's three arguments are placed: `a0 = bal_start`, `a1 = bal_end -
    bal_start`, `a2 = the digest destination`. -/

private theorem la19_hi :
    Codegen.laHi GuestAddrs.bah_bal_start (GuestAddrs.block_access_list_hash + 76)
      = Rv64.laHi (At 19) balStartLoc := by decide

private theorem la19_lo :
    Codegen.laLo GuestAddrs.bah_bal_start (GuestAddrs.block_access_list_hash + 76)
      = Rv64.laLo (At 19) balStartLoc := by decide

private theorem la19_range : laInRange (At 19) balStartLoc := by decide

theorem post_spec (b outPtr balStart vhOffW v5 v11 v12 v29 v30 : Word)
    (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 7 (At 18) (At 25) allCode
      ((((.x10 : Reg) ↦ᵣ vhOffW) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
        ((.x9 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ npr b) ** ((.x5 : Reg) ↦ᵣ v5) **
        ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
        (balStartLoc ↦ₘ balStart)) ** R)
      ((((.x10 : Reg) ↦ᵣ balStart) **
        ((.x11 : Reg) ↦ᵣ (npr b + vhOffW - balStart)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        ((.x9 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ npr b) **
        ((.x5 : Reg) ↦ᵣ balStartLoc) ** ((.x29 : Reg) ↦ᵣ balStart) **
        ((.x30 : Reg) ↦ᵣ (npr b + vhOffW)) **
        (balStartLoc ↦ₘ balStart)) ** R) := by
  -- idx 18: add t5, s2, a0
  have s18 := cpsTripleWithin_extend_code
    (wMem 18 (.ADD .x30 .x18 .x10) (by rw [wProg_len]; decide) (by rfl))
    (add_spec_within .x30 .x18 .x10 (npr b) vhOffW v30 (At 18) (by decide))
  rw [At_succ 18] at s18
  have f18 := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x5 : Reg) ↦ᵣ v5) ** ((.x29 : Reg) ↦ᵣ v29) **
      (balStartLoc ↦ₘ balStart) ** R)
    (by pcf_b) s18
  -- idx 19..20: la t0, bah_bal_start
  have s19 := la_materialize_within .x5 v5 (At 19) balStartLoc (by decide) la19_range
    (by
      rw [show Rv64.laHi (At 19) balStartLoc
          = Codegen.laHi GuestAddrs.bah_bal_start
              (GuestAddrs.block_access_list_hash + 76) from la19_hi.symm]
      exact wMem 19 _ (by rw [wProg_len]; decide) (by rfl))
    (by
      rw [show Rv64.laLo (At 19) balStartLoc
          = Codegen.laLo GuestAddrs.bah_bal_start
              (GuestAddrs.block_access_list_hash + 76) from la19_lo.symm,
        At_succ 19]
      exact wMem 20 _ (by rw [wProg_len]; decide) (by rfl))
  rw [show (At 19 + 8 : Word) = At 21 from by
    have h := At_add 19 2
    rwa [show BitVec.ofNat 64 (4 * 2) = (8 : Word) from rfl] at h] at s19
  have f19 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ vhOffW) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
      ((.x9 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ npr b) ** ((.x29 : Reg) ↦ᵣ v29) **
      ((.x30 : Reg) ↦ᵣ (npr b + vhOffW)) ** (balStartLoc ↦ₘ balStart) ** R)
    (by pcf_b) s19
  -- idx 21: ld t4, 0(t0)
  have s21 := cpsTripleWithin_extend_code
    (wMem 21 (.LD .x29 .x5 (0 : BitVec 12)) (by rw [wProg_len]; decide) (by rfl))
    (ld_spec_gen_within .x29 .x5 balStartLoc v29 balStart (0 : BitVec 12) (At 21)
      (by decide))
  rw [At_succ 21,
    show balStartLoc + signExtend12 (0 : BitVec 12) = balStartLoc from by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at s21
  have f21 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ vhOffW) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
      ((.x9 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ npr b) **
      ((.x30 : Reg) ↦ᵣ (npr b + vhOffW)) ** R)
    (by pcf_b) s21
  -- idx 22: sub a1, t5, t4
  have s22 := cpsTripleWithin_extend_code
    (wMem 22 (.SUB .x11 .x30 .x29) (by rw [wProg_len]; decide) (by rfl))
    (sub_spec_within .x11 .x30 .x29 (npr b + vhOffW) balStart v11 (At 22) (by decide))
  rw [At_succ 22] at s22
  have f22 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ vhOffW) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x18 : Reg) ↦ᵣ npr b) ** ((.x5 : Reg) ↦ᵣ balStartLoc) **
      (balStartLoc ↦ₘ balStart) ** R)
    (by pcf_b) s22
  -- idx 23: mv a0, t4
  have s23 := cpsTripleWithin_extend_code
    (wMem 23 (.MV .x10 .x29) (by rw [wProg_len]; decide) (by rfl))
    (mv_spec_gen_within .x10 .x29 balStart vhOffW (At 23) (by decide))
  rw [At_succ 23] at s23
  have f23 := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ (npr b + vhOffW - balStart)) ** ((.x12 : Reg) ↦ᵣ v12) **
      ((.x9 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ npr b) **
      ((.x5 : Reg) ↦ᵣ balStartLoc) ** ((.x30 : Reg) ↦ᵣ (npr b + vhOffW)) **
      (balStartLoc ↦ₘ balStart) ** R)
    (by pcf_b) s23
  -- idx 24: mv a2, s1
  have s24 := cpsTripleWithin_extend_code
    (wMem 24 (.MV .x12 .x9) (by rw [wProg_len]; decide) (by rfl))
    (mv_spec_gen_within .x12 .x9 outPtr v12 (At 24) (by decide))
  rw [At_succ 24] at s24
  have f24 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ balStart) ** ((.x11 : Reg) ↦ᵣ (npr b + vhOffW - balStart)) **
      ((.x18 : Reg) ↦ᵣ npr b) ** ((.x5 : Reg) ↦ᵣ balStartLoc) **
      ((.x29 : Reg) ↦ᵣ balStart) ** ((.x30 : Reg) ↦ᵣ (npr b + vhOffW)) **
      (balStartLoc ↦ₘ balStart) ** R)
    (by pcf_b) s24
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) f18 f19
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c1 f21
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c2 f22
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c3 f23
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c4 f24
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c5

/-! ## §12  Epilogue (idx 25..29)

    `ra`, `s0`, `s1`, `s2` come back and `sp` is popped BEFORE the tail jump, so
    the core runs on the caller's frame with the caller's return address — which
    is exactly why the routine's exit is the core's exit. -/

theorem epilogue_spec (sp0 ret v8 v9 v18 vRa vs0 vs1 vs2 : Word)
    (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 5 (At 25) (At 30) allCode
      ((((.x2 : Reg) ↦ᵣ sp1 sp0) ** ((.x1 : Reg) ↦ᵣ vRa) ** ((.x8 : Reg) ↦ᵣ vs0) **
        ((.x9 : Reg) ↦ᵣ vs1) ** ((.x18 : Reg) ↦ᵣ vs2) **
        ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
        ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) ** ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18)) ** R)
      ((((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) ** ((.x8 : Reg) ↦ᵣ v8) **
        ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) **
        ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
        ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) ** ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18)) ** R) := by
  -- idx 25: ld ra, 0(sp)
  have s25 := cpsTripleWithin_extend_code
    (wMem 25 (.LD .x1 .x2 (0 : BitVec 12)) (by rw [wProg_len]; decide) (by rfl))
    (ld_spec_gen_within .x1 .x2 (sp1 sp0) vRa ret (0 : BitVec 12) (At 25) (by decide))
  rw [At_succ 25, sp1_slot0] at s25
  have f25 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ vs0) ** ((.x9 : Reg) ↦ᵣ vs1) ** ((.x18 : Reg) ↦ᵣ vs2) **
      ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) ** ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) **
      ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18) ** R)
    (by pcf_b) s25
  -- idx 26: ld s0, 8(sp)
  have s26 := cpsTripleWithin_extend_code
    (wMem 26 (.LD .x8 .x2 (8 : BitVec 12)) (by rw [wProg_len]; decide) (by rfl))
    (ld_spec_gen_within .x8 .x2 (sp1 sp0) vs0 v8 (8 : BitVec 12) (At 26) (by decide))
  rw [At_succ 26, sp1_slot8] at s26
  have f26 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** ((.x9 : Reg) ↦ᵣ vs1) ** ((.x18 : Reg) ↦ᵣ vs2) **
      ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) **
      ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18) ** R)
    (by pcf_b) s26
  -- idx 27: ld s1, 16(sp)
  have s27 := cpsTripleWithin_extend_code
    (wMem 27 (.LD .x9 .x2 (16 : BitVec 12)) (by rw [wProg_len]; decide) (by rfl))
    (ld_spec_gen_within .x9 .x2 (sp1 sp0) vs1 v9 (16 : BitVec 12) (At 27) (by decide))
  rw [At_succ 27, sp1_slot16] at s27
  have f27 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** ((.x8 : Reg) ↦ᵣ v8) ** ((.x18 : Reg) ↦ᵣ vs2) **
      ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
      ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18) ** R)
    (by pcf_b) s27
  -- idx 28: ld s2, 24(sp)
  have s28 := cpsTripleWithin_extend_code
    (wMem 28 (.LD .x18 .x2 (24 : BitVec 12)) (by rw [wProg_len]; decide) (by rfl))
    (ld_spec_gen_within .x18 .x2 (sp1 sp0) vs2 v18 (24 : BitVec 12) (At 28) (by decide))
  rw [At_succ 28, sp1_slot24] at s28
  have f28 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
      ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
      ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) ** R)
    (by pcf_b) s28
  -- idx 29: addi sp, sp, 32
  have s29 := cpsTripleWithin_extend_code
    (wMem 29 (.ADDI .x2 .x2 (32 : BitVec 12)) (by rw [wProg_len]; decide) (by rfl))
    (addi_spec_gen_same_within .x2 (sp1 sp0) (32 : BitVec 12) (At 29) (by decide))
  rw [At_succ 29, sp1_restore] at s29
  have f29 := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
      ((.x18 : Reg) ↦ᵣ v18) **
      ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
      ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) ** ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18) ** R)
    (by pcf_b) s29
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) f25 f26
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c1 f27
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c2 f28
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c3 f29
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c4

/-! ## §13  The body, idx 0..29

    Everything from the first `addi sp` to the last `addi sp`, with both calls
    composed.  `t0`/`t1` come back from each call OWNED, and the suffix is
    proved for every value they might hold — that is what
    `cpsTripleWithin_of_forall_regIs_to_regOwn` is for. -/

/-- idx 18..29: place the core's arguments, then restore and pop. -/
theorem tail2_spec (sp0 ret b outPtr : Word) (hdr : List (BitVec 8))
    (v5 v8 v9 v11 v12 v18 v29 v30 : Word)
    (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 12 (At 18) (At 30) allCode
      ((((.x10 : Reg) ↦ᵣ SgLoadU32leSAsm.leU32 (hdr.drop 20) 0) ** ((.x11 : Reg) ↦ᵣ v11) **
        ((.x12 : Reg) ↦ᵣ v12) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x18 : Reg) ↦ᵣ npr b) ** ((.x5 : Reg) ↦ᵣ v5) **
        ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
        (balStartLoc ↦ₘ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) **
        ((.x2 : Reg) ↦ᵣ sp1 sp0) ** ((.x1 : Reg) ↦ᵣ At 18) **
        ((.x8 : Reg) ↦ᵣ b) **
        ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
        ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) **
        ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18)) ** R)
      ((((.x10 : Reg) ↦ᵣ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) **
        ((.x11 : Reg) ↦ᵣ ((npr b + SgLoadU32leSAsm.leU32 (hdr.drop 20) 0) - (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0))) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x18 : Reg) ↦ᵣ v18) ** ((.x5 : Reg) ↦ᵣ balStartLoc) **
        ((.x29 : Reg) ↦ᵣ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) ** ((.x30 : Reg) ↦ᵣ (npr b + SgLoadU32leSAsm.leU32 (hdr.drop 20) 0)) **
        (balStartLoc ↦ₘ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) **
        ((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) ** ((.x8 : Reg) ↦ᵣ v8) **
        ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
        ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) **
        ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18)) ** R) := by
  have hpost := post_spec b outPtr ((execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) (SgLoadU32leSAsm.leU32 (hdr.drop 20) 0) v5 v11 v12 v29 v30
    (((.x2 : Reg) ↦ᵣ sp1 sp0) ** ((.x1 : Reg) ↦ᵣ At 18) ** ((.x8 : Reg) ↦ᵣ b) **
      ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
      ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) ** ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18) ** R)
    (by pcf_b)
  have hepi := epilogue_spec sp0 ret v8 v9 v18 (At 18) b outPtr (npr b)
    (((.x10 : Reg) ↦ᵣ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) **
      ((.x11 : Reg) ↦ᵣ ((npr b + SgLoadU32leSAsm.leU32 (hdr.drop 20) 0) - (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0))) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x5 : Reg) ↦ᵣ balStartLoc) **
      ((.x29 : Reg) ↦ᵣ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) ** ((.x30 : Reg) ↦ᵣ (npr b + SgLoadU32leSAsm.leU32 (hdr.drop 20) 0)) **
      (balStartLoc ↦ₘ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) ** R)
    (by pcf_b)
  have c := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xcancel_struct hp) hpost hepi
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c

/-- idx 11..29: everything between the first call's return and the tail jump.
    `t0` comes back from the second call OWNED, so the part after it is proved
    for EVERY value it might hold and then repackaged. -/
theorem suffix_spec (sp0 ret b outPtr : Word) (hdr : List (BitVec 8))
    (v5 v6 v8 v9 v12 v18 v28 v29 v30 : Word)
    (R : Assertion) (hR : R.pcFree)
    (h_align : b.toNat % 8 = 0)
    (h_fit : 592 ≤ hdr.length)
    (h_over : b.toNat + 591 < 2 ^ 64)
    (h_valid : ∀ k, k < hdr.length →
      isValidByteAccess (b + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 31 (At 11) (At 30) allCode
      ((((.x10 : Reg) ↦ᵣ SgLoadU32leSAsm.leU32 (hdr.drop 588) 0) ** ((.x18 : Reg) ↦ᵣ npr b) **
        ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x5 : Reg) ↦ᵣ v5) **
        ((.x6 : Reg) ↦ᵣ v6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        memOwn balStartLoc ** bytesRegion b hdr **
        ((.x2 : Reg) ↦ᵣ sp1 sp0) ** ((.x1 : Reg) ↦ᵣ At 11) **
        ((.x8 : Reg) ↦ᵣ b) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ v12) **
        ((.x30 : Reg) ↦ᵣ v30) **
        ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
        ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) **
        ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18)) ** R)
      ((((.x10 : Reg) ↦ᵣ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) **
        ((.x11 : Reg) ↦ᵣ ((npr b + SgLoadU32leSAsm.leU32 (hdr.drop 20) 0) - (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0))) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x18 : Reg) ↦ᵣ v18) ** ((.x5 : Reg) ↦ᵣ balStartLoc) ** regOwn .x6 **
        ((.x28 : Reg) ↦ᵣ execP b) ** ((.x29 : Reg) ↦ᵣ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) **
        ((.x30 : Reg) ↦ᵣ (npr b + SgLoadU32leSAsm.leU32 (hdr.drop 20) 0)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        (balStartLoc ↦ₘ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) ** bytesRegion b hdr **
        ((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) ** ((.x8 : Reg) ↦ᵣ v8) **
        ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
        ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) **
        ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18)) ** R) := by
  -- idx 11..16
  have hmid := mid_spec b (SgLoadU32leSAsm.leU32 (hdr.drop 588) 0) v5 v28 v29
    (((.x6 : Reg) ↦ᵣ v6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion b hdr **
      ((.x2 : Reg) ↦ᵣ sp1 sp0) ** ((.x1 : Reg) ↦ᵣ At 11) ** ((.x8 : Reg) ↦ᵣ b) **
      ((.x9 : Reg) ↦ᵣ outPtr) ** ((.x11 : Reg) ↦ᵣ outPtr) **
      ((.x12 : Reg) ↦ᵣ v12) ** ((.x30 : Reg) ↦ᵣ v30) **
      ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
      ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) ** ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18) ** R)
    (by pcf_b)
  -- idx 17
  have hc2 := call2_spec b hdr (At 11) balStartLoc v6
    (((.x2 : Reg) ↦ᵣ sp1 sp0) ** ((.x8 : Reg) ↦ᵣ b) ** ((.x9 : Reg) ↦ᵣ outPtr) **
      ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ v12) **
      ((.x18 : Reg) ↦ᵣ npr b) ** ((.x28 : Reg) ↦ᵣ execP b) **
      ((.x29 : Reg) ↦ᵣ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) ** ((.x30 : Reg) ↦ᵣ v30) **
      (balStartLoc ↦ₘ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) **
      ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
      ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) ** ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18) ** R)
    (by pcf_b) h_align (by omega) (by omega) h_valid
  -- idx 18..29, for every value `t0` might come back holding
  have htail : ∀ v5', cpsTripleWithin 12 (At 18) (At 30) allCode
      ((((.x10 : Reg) ↦ᵣ SgLoadU32leSAsm.leU32 (hdr.drop 20) 0) ** ((.x11 : Reg) ↦ᵣ outPtr) **
        ((.x12 : Reg) ↦ᵣ v12) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x18 : Reg) ↦ᵣ npr b) **
        ((.x29 : Reg) ↦ᵣ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) ** ((.x30 : Reg) ↦ᵣ v30) **
        (balStartLoc ↦ₘ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) **
        ((.x2 : Reg) ↦ᵣ sp1 sp0) ** ((.x1 : Reg) ↦ᵣ At 18) **
        ((.x8 : Reg) ↦ᵣ b) **
        ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
        ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) **
        ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18) **
        (((.x28 : Reg) ↦ᵣ execP b) ** regOwn .x6 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion b hdr ** R)) **
        ((.x5 : Reg) ↦ᵣ v5'))
      ((((.x10 : Reg) ↦ᵣ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) **
        ((.x11 : Reg) ↦ᵣ ((npr b + SgLoadU32leSAsm.leU32 (hdr.drop 20) 0) - (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0))) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x18 : Reg) ↦ᵣ v18) ** ((.x5 : Reg) ↦ᵣ balStartLoc) **
        ((.x29 : Reg) ↦ᵣ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) ** ((.x30 : Reg) ↦ᵣ (npr b + SgLoadU32leSAsm.leU32 (hdr.drop 20) 0)) **
        (balStartLoc ↦ₘ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) **
        ((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) ** ((.x8 : Reg) ↦ᵣ v8) **
        ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
        ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) **
        ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18)) **
        (((.x28 : Reg) ↦ᵣ execP b) ** regOwn .x6 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion b hdr ** R)) := by
    intro v5'
    have h := tail2_spec sp0 ret b outPtr hdr v5' v8 v9 outPtr v12 v18
      ((execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) v30
      (((.x28 : Reg) ↦ᵣ execP b) ** regOwn .x6 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion b hdr ** R)
      (by pcf_b)
    exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
      (fun _ hq => by xcancel_struct hq) h
  have hown := cpsTripleWithin_of_forall_regIs_to_regOwn htail
  have c1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xcancel_struct hp) hmid hc2
  have c2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xcancel_struct hp) c1 hown
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c2

theorem body_spec (sp0 ret b outPtr : Word) (hdr : List (BitVec 8))
    (v5 v6 v8 v9 v12 v18 v28 v29 v30 : Word)
    (R : Assertion) (hR : R.pcFree)
    (h_align : b.toNat % 8 = 0)
    (h_fit : 592 ≤ hdr.length)
    (h_over : b.toNat + 591 < 2 ^ 64)
    (h_valid : ∀ k, k < hdr.length →
      isValidByteAccess (b + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 54 (At 0) (At 30) allCode
      ((((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x10 : Reg) ↦ᵣ b) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ v12) **
        ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) **
        ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        memOwn (sp0 - BitVec.ofNat 64 32) ** memOwn (sp0 - BitVec.ofNat 64 24) **
        memOwn (sp0 - BitVec.ofNat 64 16) ** memOwn (sp0 - BitVec.ofNat 64 8) **
        memOwn balStartLoc ** bytesRegion b hdr) ** R)
      ((((.x10 : Reg) ↦ᵣ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) **
        ((.x11 : Reg) ↦ᵣ ((npr b + SgLoadU32leSAsm.leU32 (hdr.drop 20) 0)
          - (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0))) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x18 : Reg) ↦ᵣ v18) ** ((.x5 : Reg) ↦ᵣ balStartLoc) ** regOwn .x6 **
        ((.x28 : Reg) ↦ᵣ execP b) **
        ((.x29 : Reg) ↦ᵣ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) **
        ((.x30 : Reg) ↦ᵣ (npr b + SgLoadU32leSAsm.leU32 (hdr.drop 20) 0)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        (balStartLoc ↦ₘ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) **
        bytesRegion b hdr **
        ((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) ** ((.x8 : Reg) ↦ᵣ v8) **
        ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
        ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) **
        ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18)) ** R) := by
  -- idx 0..4
  have hpro := prologue_spec sp0 ret v8 v9 v18
    (((.x10 : Reg) ↦ᵣ b) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ v12) **
      ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x28 : Reg) ↦ᵣ v28) **
      ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      memOwn balStartLoc ** bytesRegion b hdr ** R)
    (by pcf_b)
  -- idx 5..9
  have hset := setup_spec b outPtr v8 v9 v18 v28
    (((.x2 : Reg) ↦ᵣ sp1 sp0) ** ((.x1 : Reg) ↦ᵣ ret) ** ((.x12 : Reg) ↦ᵣ v12) **
      ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x29 : Reg) ↦ᵣ v29) **
      ((.x30 : Reg) ↦ᵣ v30) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      memOwn balStartLoc **
      ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
      ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) ** ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18) **
      bytesRegion b hdr ** R)
    (by pcf_b)
  -- idx 10
  have hc1 := call1_spec b hdr ret v5 v6
    (((.x2 : Reg) ↦ᵣ sp1 sp0) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ v12) **
      ((.x8 : Reg) ↦ᵣ b) ** ((.x9 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ npr b) **
      ((.x28 : Reg) ↦ᵣ execP b) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
      memOwn balStartLoc **
      ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
      ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) ** ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18) ** R)
    (by pcf_b) h_align (by omega) (by omega) h_valid
  -- idx 11..29, for every pair of values the leaf may leave in `t0`/`t1`
  -- idx 11..29, for every pair of values the leaf may leave in `t0`/`t1`.
  -- The two peels need one reassociation between them: `of_forall` only ever
  -- sees the LAST conjunct, so `t0` comes off first and `t1` after the shuffle.
  have hsuf6 : ∀ v6', cpsTripleWithin 31 (At 11) (At 30) allCode
      (((((.x10 : Reg) ↦ᵣ SgLoadU32leSAsm.leU32 (hdr.drop 588) 0) **
          ((.x18 : Reg) ↦ᵣ npr b) ** ((.x28 : Reg) ↦ᵣ execP b) **
          ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          memOwn balStartLoc ** bytesRegion b hdr **
          ((.x2 : Reg) ↦ᵣ sp1 sp0) ** ((.x1 : Reg) ↦ᵣ At 11) **
          ((.x8 : Reg) ↦ᵣ b) ** ((.x9 : Reg) ↦ᵣ outPtr) **
          ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ v12) **
          ((.x30 : Reg) ↦ᵣ v30) **
          ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) **
          ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
          ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) **
          ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18) ** R) ** regOwn .x5) **
        ((.x6 : Reg) ↦ᵣ v6'))
      ((((.x10 : Reg) ↦ᵣ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) **
        ((.x11 : Reg) ↦ᵣ ((npr b + SgLoadU32leSAsm.leU32 (hdr.drop 20) 0)
          - (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0))) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x18 : Reg) ↦ᵣ v18) ** ((.x5 : Reg) ↦ᵣ balStartLoc) ** regOwn .x6 **
        ((.x28 : Reg) ↦ᵣ execP b) **
        ((.x29 : Reg) ↦ᵣ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) **
        ((.x30 : Reg) ↦ᵣ (npr b + SgLoadU32leSAsm.leU32 (hdr.drop 20) 0)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        (balStartLoc ↦ₘ (execP b + SgLoadU32leSAsm.leU32 (hdr.drop 588) 0)) **
        bytesRegion b hdr **
        ((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) ** ((.x8 : Reg) ↦ᵣ v8) **
        ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) ** ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
        ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) **
        ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18)) ** R) := by
    intro v6'
    refine cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
      (fun _ hq => hq)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
        (P := (((.x10 : Reg) ↦ᵣ SgLoadU32leSAsm.leU32 (hdr.drop 588) 0) **
            ((.x18 : Reg) ↦ᵣ npr b) ** ((.x28 : Reg) ↦ᵣ execP b) **
            ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            memOwn balStartLoc ** bytesRegion b hdr **
            ((.x2 : Reg) ↦ᵣ sp1 sp0) ** ((.x1 : Reg) ↦ᵣ At 11) **
            ((.x8 : Reg) ↦ᵣ b) ** ((.x9 : Reg) ↦ᵣ outPtr) **
            ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ v12) **
            ((.x30 : Reg) ↦ᵣ v30) **
            ((sp0 - BitVec.ofNat 64 32) ↦ₘ ret) **
            ((sp0 - BitVec.ofNat 64 24) ↦ₘ v8) **
            ((sp0 - BitVec.ofNat 64 16) ↦ₘ v9) **
            ((sp0 - BitVec.ofNat 64 8) ↦ₘ v18) ** R) **
          ((.x6 : Reg) ↦ᵣ v6'))
        (fun v5' => ?_))
    exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
      (fun _ hq => by xcancel_struct hq)
      (suffix_spec sp0 ret b outPtr hdr v5' v6' v8 v9 v12 v18 (execP b) v29 v30
        R hR h_align h_fit h_over h_valid)
  have hsuf := cpsTripleWithin_of_forall_regIs_to_regOwn hsuf6
  have c1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xcancel_struct hp) hpro hset
  have c2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xcancel_struct hp) c1 hc1
  have c3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xcancel_struct hp) c2 hsuf
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c3

/-! ## §14  What remains: the hand-off to the core

    `body_spec` ▸ `tail_jump_spec` ▸ `block_access_list_hash_core_spec_within`
    is the whole routine.  The first two are proved above and the third is
    rowed `.proven`; what is NOT done here is the assertion plumbing that turns
    `body_spec`'s post into the core's precondition.  Spelled out so the next
    step is mechanical rather than exploratory, the obligations are:

    * `x11`: the body leaves `bal_end - bal_start`; the core wants
      `BitVec.ofNat 64 input.length`.  Bridged by a hypothesis
      `h_len : (npr b + vh_off) - (execP b + bal_off) = BitVec.ofNat 64 input.length`
      relating the witness's declared extent to the slab actually presented.

    * `regOwns keccakBodyFreeTemps` (`[x5, x6, x7, x13..x17, x30, x31]`): `x6`
      arrives already owned from the second call, `x5` (`= bah_bal_start`) and
      `x30` (`= bal_end`) arrive PINNED and need `regIs_implies_regOwn`, and
      `x7`, `x13..x17`, `x31` ride through untouched from the caller.

    * `memOwn (sp0 - 16) ** stackFree (sp0 - 16) 4`, i.e. cells at
      `sp0 - 48 … sp0 - 16`: three of them come back from the epilogue as
      `↦ₘ` (still holding `ra`, `s0`, `s1`) and need `memIs_implies_memOwn`;
      the other two are the extra pair in `stackFree sp0 6`
      (`stackFree6_split`).  `sp0 - 8` is left over and belongs in the core's
      ambient `A`.

    * `regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20)`: exactly the four
      callee-saved values the epilogue restored, with `x20` never touched.

    ⚠️ The scope note in this module's header applies to that step and not
    before it: the slab region `bytesRegion bal_start input` is presented as its
    own atom with `8 ∣ input.length` stated explicitly, so that no assumption
    about the bytes after the slab can enter by the back door.  If a future
    version of this proof finds it needs those bytes to be zero, that is #13014
    proper and does not belong here.
-/

-- #13030 temporary module-floor audit.  This body contract is not yet a
-- whole-routine Progress row, so keep a local kernel axiom report until the
-- eventual row can move it into Progress/AxiomWitnesses.lean.
#print axioms body_spec

end EvmAsm.Codegen.BlockAccessListHashSpec
