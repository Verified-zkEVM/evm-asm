/-
  EvmAsm.Codegen.Proofs.CallFrameEnterSpec

  **The `call_frame_enter` machine triple — the depth-1 (pool-base) arm (#12318).**

  `call_frame_enter` (`Codegen/Programs/CallFrameDescend.lean`,
  `callFrameEnter_prog`, 41 instructions at `GuestAddrs.call_frame_enter`,
  image entry `Codegen/Proofs/GuestImageEntries.lean:644`) is the frame-descent
  helper every message call goes through.  It bumps the sparse-memory epoch,
  stamps the new epoch into the per-depth epoch table, asks `frame_base` for
  the child frame's arena address, and returns the three per-frame pointers the
  caller re-points its registers from: `a0 =` child memory base, `a1 =` child
  stack top, `a2 =` child env base.

  ## Extent, derived rather than quoted

  `scripts/asm-fixtures/symbol-addresses.tsv` puts `call_frame_enter` at
  `0x8003c76c` and the next `.text` symbol, `call_frame_set_call_env`, at
  `0x8003c810`.  That is `0xa4 = 164` bytes, and `164 = 41 * 4` cross-checks the
  `#guard callFrameEnter_prog.length = 41` in the Program module.  The callee
  `frame_base` sits at `0x8003c6ec` with `frame_depth_push` next at
  `0x8003c704`: `0x18 = 24 = 6 * 4`, matching the 6-step bound in
  `CallFrameBaseSAsm.frameBase_spec`.

  ## What this module proves

  `callFrameEnterDepth1Flat_spec`, a 38-step whole-routine triple
  entry → `ret`, under one named gate:

  * `evm_call_depth ↦ₘ 1` — the parent is the top-level frame.

  The gate is **this routine's own**, not inherited: the callee contract
  (`frameBase_spec`) is total.  The `beq t1, t2` at instruction index 19
  compares the loaded `evm_call_depth` against the `li t2, 1` immediately
  above it, so under the gate the branch is TAKEN and control jumps to index
  29.  The covered path is therefore indices 0..19 and 29..40 — **32 of the
  41 instructions** — and the claim is the documented depth-1 behaviour: the
  child's memory base *is* `evm_memory_pool`, with no parent MSIZE to add.

  Three things the triple states that are worth naming:

  * **The epoch bump is a real effect, not framing.**  `evm_sparse_memory_next_epoch`
    goes from `epoch` to `epoch + 1`, and the per-depth slot
    `evm_sparse_memory_epoch_by_depth + 8 * depth` goes from whatever it held
    to `epoch` — the *old* next-epoch value, published before the increment
    lands in the register that stores it.  Both cells are named in the pre and
    the post.
  * **The two returned frame pointers are the callee's arithmetic, composed.**
    `a1 = frame_base(depth) + 0x8200` and `a2 = frame_base(depth) + 0x18400`,
    where `frame_base(depth) = call_frame_arena + depth * 0x19000` comes from
    `frameBase_spec` — reused, not re-proved.
  * ⭐ **`frame_parent_bases` is NOT read, and the triple says so by not naming
    it.**  Because `cpsTripleWithin` universally quantifies over a `pcFree`
    frame, its absence from both the pre and the post is a no-touch guarantee
    over the whole covered path — which is exactly the difference between the
    depth-1 arm and the arm this proof does not cover.

  ## Registers

  `t0`, `t1`, `t2` (`x5`, `x6`, `x7`) are CLOBBERED and the post says so rather
  than framing them away: `t0` comes back holding `99328` (the second
  `lui`/`addiw` pair's constant, `0x18400`), `t1` and `t2` both holding `1`
  (the loaded call depth and the comparison immediate).  `ra`, `sp` and `s0`
  are restored.

  `a3`-`a7` and `t3`-`t6` (`x13`-`x17`, `x28`-`x31`) are surrendered to the
  callee as `regOwns` and come back as `regOwns`: `frameBase_spec` takes
  ownership of them and returns no information about them, so neither does
  this contract.  That is the honest statement, not a weakening — nothing in
  `call_frame_enter`'s own 41 instructions touches any of them.

  ## The `CodeReq` union is FORCED

  The `jal ra, frame_base` at instruction index 13 is UNCONDITIONAL and sits
  ABOVE the routine's only branch (index 19), so every path through the
  routine leaves its own bytes.  A single `CodeReq.ofProg` could state nothing
  here.  `cfeCR` therefore pairs the `GuestImageEntries.lean:644` pairing with
  the `frame_base` pairing.

  ⚠️ Written `CodeReq.union a b`, not `a.union b` — per #13198, the dotted
  spelling used to hide the `GuestAddrs.call_frame_enter` anchor inside the
  first leg from `scripts/proof-frontier.py --shape`.  The prefix spelling
  grades `whole-routine` either way.

  ## ⚠️ What is deliberately NOT proven

  The `depth ≠ 1` arm, instruction indices 20..28: the `la t0, frame_parent_bases`
  pair, the `slli`/`add` index into it, the two `ld`s that fetch the parent's
  base and frame pointer, the `ld t2, 488(t2)` that reads the parent's MSIZE,
  the `add a0, t1, t2` that forms `parentMemBase + parentMSIZE`, and the
  `j` that rejoins at index 31.  The registry row is therefore `.conditional`
  with the one gate named.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only
  (audited by the `#print axioms` at the end of this file).
-/

import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.WP.Call
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Codegen.Programs.CallFrameDescend
import EvmAsm.Codegen.Programs.CallFrameBaseSAsm

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen

/-! ## Segment A — the prologue, the epoch bump and the per-depth epoch stamp -/

/-- `call_frame_enter` instructions 0..12 (`base .. base + 48`): push a 16-byte
    frame, spill `ra` and `s0`, then

    * `la t0, evm_sparse_memory_next_epoch`; `ld t1, 0(t0)`;
      `addi t2, t1, 1`; `sd t2, 0(t0)` — read the current epoch and write back
      its successor;
    * `la t0, evm_sparse_memory_epoch_by_depth`; `slli t2, a0, 3`;
      `add t0, t0, t2`; `sd t1, 0(t0)` — stamp the *old* epoch into the child
      depth's slot.

    `a0` (the child depth) is untouched throughout, which is what makes it
    still the `frame_base` argument at index 13. -/
theorem callFrameEnter_segA_body_spec
    (base sp ra v5 v6 v7 v8 depth nextEpochPtr epochByDepthPtr epoch oldSlot : Word)
    (hlaNE : base + (12 : Word) +
        (((laHi GuestAddrs.evm_sparse_memory_next_epoch
            (GuestAddrs.call_frame_enter + 12)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.evm_sparse_memory_next_epoch
          (GuestAddrs.call_frame_enter + 12)) = nextEpochPtr)
    (hlaEBD : base + (32 : Word) +
        (((laHi GuestAddrs.evm_sparse_memory_epoch_by_depth
            (GuestAddrs.call_frame_enter + 32)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.evm_sparse_memory_epoch_by_depth
          (GuestAddrs.call_frame_enter + 32)) = epochByDepthPtr) :
    cpsTripleWithin 13 base (base + (52 : Word))
      (CodeReq.ofProg base callFrameEnter_prog)
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x7 ↦ᵣ v7) ** (.x8 ↦ᵣ v8) ** (.x10 ↦ᵣ depth) **
       memOwn (sp - (16 : Word)) ** memOwn (sp - (8 : Word)) **
       (nextEpochPtr ↦ₘ epoch) **
       ((epochByDepthPtr + (depth <<< (3 : Nat))) ↦ₘ oldSlot))
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp - (16 : Word))) **
       (.x5 ↦ᵣ (epochByDepthPtr + (depth <<< (3 : Nat)))) ** (.x6 ↦ᵣ epoch) **
       (.x7 ↦ᵣ (depth <<< (3 : Nat))) ** (.x8 ↦ᵣ v8) ** (.x10 ↦ᵣ depth) **
       ((sp - (16 : Word)) ↦ₘ ra) ** ((sp - (8 : Word)) ↦ₘ v8) **
       (nextEpochPtr ↦ₘ (epoch + (1 : Word))) **
       ((epochByDepthPtr + (depth <<< (3 : Nat))) ↦ₘ epoch)) := by
  unfold callFrameEnter_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 0: `addi sp, sp, -16`
  have P0 := addi_spec_gen_same_within .x2 sp (-16 : BitVec 12) base (by nofun)
  rw [show signExtend12 (-16 : BitVec 12) = (-16 : Word) from by decide,
      show sp + (-16 : Word) = sp - (16 : Word) from by bv_omega] at P0
  -- index 1: `sd ra, 0(sp)`
  have P1 := sd_spec_gen_own_within .x2 .x1 (sp - (16 : Word)) ra (0 : BitVec 12)
    (base + (4 : Word))
  rw [show (sp - (16 : Word)) + signExtend12 (0 : BitVec 12) = sp - (16 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at P1
  -- index 2: `sd s0, 8(sp)`
  have P2 := sd_spec_gen_own_within .x2 .x8 (sp - (16 : Word)) v8 (8 : BitVec 12)
    (base + (8 : Word))
  rw [show (sp - (16 : Word)) + signExtend12 (8 : BitVec 12) = sp - (8 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at P2
  -- indices 3, 4: `la t0, evm_sparse_memory_next_epoch`
  have P3 := auipc_spec_gen_within .x5 v5
    (laHi GuestAddrs.evm_sparse_memory_next_epoch (GuestAddrs.call_frame_enter + 12))
    (base + (12 : Word)) (by nofun)
  have P4 := addi_spec_gen_same_within .x5
    ((base + (12 : Word)) +
      (((laHi GuestAddrs.evm_sparse_memory_next_epoch
          (GuestAddrs.call_frame_enter + 12)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.evm_sparse_memory_next_epoch (GuestAddrs.call_frame_enter + 12))
    (base + (16 : Word)) (by nofun)
  rw [hlaNE] at P4
  -- index 5: `ld t1, 0(t0)` — the current sparse-memory epoch
  have P5 := ld_spec_gen_within .x6 .x5 nextEpochPtr v6 epoch (0 : BitVec 12)
    (base + (20 : Word)) (by nofun)
  rw [show nextEpochPtr + signExtend12 (0 : BitVec 12) = nextEpochPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at P5
  -- index 6: `addi t2, t1, 1`
  have P6 := addi_spec_gen_within .x7 .x6 v7 epoch (1 : BitVec 12)
    (base + (24 : Word)) (by nofun)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at P6
  -- index 7: `sd t2, 0(t0)` — publish the successor epoch
  have P7 := sd_spec_gen_within .x5 .x7 nextEpochPtr (epoch + (1 : Word)) epoch
    (0 : BitVec 12) (base + (28 : Word))
  rw [show nextEpochPtr + signExtend12 (0 : BitVec 12) = nextEpochPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at P7
  -- indices 8, 9: `la t0, evm_sparse_memory_epoch_by_depth`
  have P8 := auipc_spec_gen_within .x5 nextEpochPtr
    (laHi GuestAddrs.evm_sparse_memory_epoch_by_depth (GuestAddrs.call_frame_enter + 32))
    (base + (32 : Word)) (by nofun)
  have P9 := addi_spec_gen_same_within .x5
    ((base + (32 : Word)) +
      (((laHi GuestAddrs.evm_sparse_memory_epoch_by_depth
          (GuestAddrs.call_frame_enter + 32)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.evm_sparse_memory_epoch_by_depth (GuestAddrs.call_frame_enter + 32))
    (base + (36 : Word)) (by nofun)
  rw [hlaEBD] at P9
  -- index 10: `slli t2, a0, 3` — the child depth's 8-byte slot offset
  have P10 := slli_spec_gen_within .x7 .x10 (epoch + (1 : Word)) depth (3 : BitVec 6)
    (base + (40 : Word)) (by nofun)
  rw [show ((3 : BitVec 6).toNat) = 3 from by decide] at P10
  -- index 11: `add t0, t0, t2`
  have P11 := add_spec_gen_rd_eq_rs1_within .x5 .x7 epochByDepthPtr
    (depth <<< (3 : Nat)) (base + (44 : Word)) (by nofun)
  -- index 12: `sd t1, 0(t0)` — stamp the OLD epoch into the child depth's slot
  have P12 := sd_spec_gen_within .x5 .x6 (epochByDepthPtr + (depth <<< (3 : Nat)))
    epoch oldSlot (0 : BitVec 12) (base + (48 : Word))
  rw [show (epochByDepthPtr + (depth <<< (3 : Nat))) + signExtend12 (0 : BitVec 12)
      = epochByDepthPtr + (depth <<< (3 : Nat)) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at P12
  runBlock P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12

/-! ## Segment B — the call depth discrimination -/

/-- `call_frame_enter` instructions 14..19 (`base + 56 .. base + 116`):
    `mv s0, a0` stashes the child frame base the callee just returned, then
    `la t0, evm_call_depth`; `ld t1, 0(t0)`; `li t2, 1`; `beq t1, t2, +40`.

    Under the gate `evm_call_depth ↦ₘ 1` the branch is TAKEN, jumping past the
    parent-MSIZE arm to index 29.  Only the taken immediate is resolved, so
    only `hbr` is a premise. -/
theorem callFrameEnter_segB_body_spec
    (base fb w5 w6 w7 y8 callDepthPtr : Word)
    (hlaCD : base + (60 : Word) +
        (((laHi GuestAddrs.evm_call_depth
            (GuestAddrs.call_frame_enter + 60)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.evm_call_depth
          (GuestAddrs.call_frame_enter + 60)) = callDepthPtr)
    (hbr : signExtend13 (40 : BitVec 13) = (40 : Word)) :
    cpsTripleWithin 6 (base + (56 : Word)) (base + (116 : Word))
      (CodeReq.ofProg base callFrameEnter_prog)
      ((.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x8 ↦ᵣ y8) **
       (.x10 ↦ᵣ fb) ** (callDepthPtr ↦ₘ (1 : Word)))
      ((.x5 ↦ᵣ callDepthPtr) ** (.x6 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (1 : Word)) **
       (.x8 ↦ᵣ fb) ** (.x10 ↦ᵣ fb) ** (callDepthPtr ↦ₘ (1 : Word))) := by
  unfold callFrameEnter_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 14: `mv s0, a0` — the child frame base
  have R0 := mv_spec_gen_within .x8 .x10 fb y8 (base + (56 : Word)) (by nofun)
  -- indices 15, 16: `la t0, evm_call_depth`
  have R1 := auipc_spec_gen_within .x5 w5
    (laHi GuestAddrs.evm_call_depth (GuestAddrs.call_frame_enter + 60))
    (base + (60 : Word)) (by nofun)
  have R2 := addi_spec_gen_same_within .x5
    ((base + (60 : Word)) +
      (((laHi GuestAddrs.evm_call_depth
          (GuestAddrs.call_frame_enter + 60)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.evm_call_depth (GuestAddrs.call_frame_enter + 60))
    (base + (64 : Word)) (by nofun)
  rw [hlaCD] at R2
  -- index 17: `ld t1, 0(t0)` — the parent's call depth, gated to 1
  have R3 := ld_spec_gen_within .x6 .x5 callDepthPtr w6 (1 : Word) (0 : BitVec 12)
    (base + (68 : Word)) (by nofun)
  rw [show callDepthPtr + signExtend12 (0 : BitVec 12) = callDepthPtr from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at R3
  -- index 18: `li t2, 1`
  have R4 := li_spec_gen_within .x7 w7 (1 : Word) (base + (72 : Word)) (by nofun)
  -- index 19: `beq t1, t2, .Lcfe_pool` — TAKEN, the depth is 1
  have RB := beq_spec_gen_within .x6 .x7 (40 : BitVec 13) (1 : Word) (1 : Word)
    (base + (76 : Word))
  rw [hbr, show base + (76 : Word) + (40 : Word) = base + (116 : Word) from by bv_omega]
    at RB
  have R5 : cpsTripleWithin 1 (base + (76 : Word)) (base + (116 : Word))
      (CodeReq.singleton (base + (76 : Word)) (.BEQ .x6 .x7 (40 : BitVec 13)))
      ((.x6 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (1 : Word)))
      ((.x6 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (1 : Word))) :=
    cpsBranchWithin_takenStripPure2 RB (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact absurd h_pure.2 (by decide))
  runBlock R0 R1 R2 R3 R4 R5

/-! ## Segment C — `.Lcfe_pool` and the epilogue -/

/-- `call_frame_enter` instructions 29..40 (`base + 116 .. base + 160`):
    `la a0, evm_memory_pool` — at depth 1 the child's memory base *is* the pool
    base — then the two frame-offset materialisations
    `lui/addiw/add a1, s0, 0x8200` (child stack top) and
    `lui/addiw/add a2, s0, 0x18400` (child env base), then reload `ra` and
    `s0`, pop the frame and `ret`.

    ⭐ `frame_parent_bases` is not named here, and the `pcFree` frame turns
    that silence into a no-read guarantee for the covered path. -/
theorem callFrameEnter_segC_body_spec
    (base sp ra link fb v8 z5 z10 z11 z12 poolPtr : Word)
    (hlaMP : base + (116 : Word) +
        (((laHi GuestAddrs.evm_memory_pool
            (GuestAddrs.call_frame_enter + 116)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.evm_memory_pool
          (GuestAddrs.call_frame_enter + 116)) = poolPtr) :
    cpsTripleWithin 12 (base + (116 : Word)) (ra &&& ~~~(1 : Word))
      (CodeReq.ofProg base callFrameEnter_prog)
      ((.x1 ↦ᵣ link) ** (.x2 ↦ᵣ (sp - (16 : Word))) ** (.x5 ↦ᵣ z5) **
       (.x8 ↦ᵣ fb) ** (.x10 ↦ᵣ z10) ** (.x11 ↦ᵣ z11) ** (.x12 ↦ᵣ z12) **
       ((sp - (16 : Word)) ↦ₘ ra) ** ((sp - (8 : Word)) ↦ₘ v8))
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ (99328 : Word)) **
       (.x8 ↦ᵣ v8) ** (.x10 ↦ᵣ poolPtr) **
       (.x11 ↦ᵣ (fb + (33280 : Word))) ** (.x12 ↦ᵣ (fb + (99328 : Word))) **
       ((sp - (16 : Word)) ↦ₘ ra) ** ((sp - (8 : Word)) ↦ₘ v8)) := by
  unfold callFrameEnter_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- indices 29, 30: `la a0, evm_memory_pool`
  have T0 := auipc_spec_gen_within .x10 z10
    (laHi GuestAddrs.evm_memory_pool (GuestAddrs.call_frame_enter + 116))
    (base + (116 : Word)) (by nofun)
  have T1 := addi_spec_gen_same_within .x10
    ((base + (116 : Word)) +
      (((laHi GuestAddrs.evm_memory_pool
          (GuestAddrs.call_frame_enter + 116)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.evm_memory_pool (GuestAddrs.call_frame_enter + 116))
    (base + (120 : Word)) (by nofun)
  rw [hlaMP] at T1
  -- indices 31, 32: `lui t0, 8`; `addiw t0, t0, 512` — the 0x8200 stack-top offset
  have T2 := lui_spec_gen_within .x5 z5 (8 : BitVec 20) (base + (124 : Word)) (by nofun)
  rw [show ((((8 : BitVec 20)).zeroExtend 32 <<< 12).signExtend 64) = (32768 : Word) from by
    decide] at T2
  have T3 := addiw_spec_gen_same_within .x5 (32768 : Word) (512 : BitVec 12)
    (base + (128 : Word)) (by nofun)
  rw [show (((32768 : Word).truncate 32 + (signExtend12 (512 : BitVec 12)).truncate 32
      : BitVec 32).signExtend 64) = (33280 : Word) from by decide] at T3
  -- index 33: `add a1, s0, t0`
  have T4 := add_spec_gen_within .x11 .x8 .x5 fb (33280 : Word) z11
    (base + (132 : Word)) (by nofun)
  -- indices 34, 35: `lui t0, 24`; `addiw t0, t0, 1024` — the 0x18400 env offset
  have T5 := lui_spec_gen_within .x5 (33280 : Word) (24 : BitVec 20)
    (base + (136 : Word)) (by nofun)
  rw [show ((((24 : BitVec 20)).zeroExtend 32 <<< 12).signExtend 64) = (98304 : Word) from by
    decide] at T5
  have T6 := addiw_spec_gen_same_within .x5 (98304 : Word) (1024 : BitVec 12)
    (base + (140 : Word)) (by nofun)
  rw [show (((98304 : Word).truncate 32 + (signExtend12 (1024 : BitVec 12)).truncate 32
      : BitVec 32).signExtend 64) = (99328 : Word) from by decide] at T6
  -- index 36: `add a2, s0, t0`
  have T7 := add_spec_gen_within .x12 .x8 .x5 fb (99328 : Word) z12
    (base + (144 : Word)) (by nofun)
  -- indices 37, 38: reload `ra` and `s0`
  have T8 := ld_spec_gen_within .x1 .x2 (sp - (16 : Word)) link ra (0 : BitVec 12)
    (base + (148 : Word)) (by nofun)
  rw [show (sp - (16 : Word)) + signExtend12 (0 : BitVec 12) = sp - (16 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at T8
  have T9 := ld_spec_gen_within .x8 .x2 (sp - (16 : Word)) fb v8 (8 : BitVec 12)
    (base + (152 : Word)) (by nofun)
  rw [show (sp - (16 : Word)) + signExtend12 (8 : BitVec 12) = sp - (8 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at T9
  -- index 39: `addi sp, sp, 16`
  have T10 := addi_spec_gen_same_within .x2 (sp - (16 : Word)) (16 : BitVec 12)
    (base + (156 : Word)) (by nofun)
  rw [show (sp - (16 : Word)) + signExtend12 (16 : BitVec 12) = sp from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at T10
  -- index 40: `ret`
  have T11 := EvmAsm.Evm64.ret_spec_within' (base + (160 : Word)) ra
  runBlock T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11

/-- Segment B with `t0`/`t1`/`t2` surrendered rather than valued — the shape
    the callee hands back.  All three are written before they are read, so
    ownership is all the block needs. -/
theorem callFrameEnter_segB_own_spec
    (base fb y8 callDepthPtr : Word)
    (hlaCD : base + (60 : Word) +
        (((laHi GuestAddrs.evm_call_depth
            (GuestAddrs.call_frame_enter + 60)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.evm_call_depth
          (GuestAddrs.call_frame_enter + 60)) = callDepthPtr)
    (hbr : signExtend13 (40 : BitVec 13) = (40 : Word)) :
    cpsTripleWithin 6 (base + (56 : Word)) (base + (116 : Word))
      (CodeReq.ofProg base callFrameEnter_prog)
      ((.x8 ↦ᵣ y8) ** (.x10 ↦ᵣ fb) ** (callDepthPtr ↦ₘ (1 : Word)) **
       regOwns [(.x5 : Reg), .x6, .x7])
      ((.x5 ↦ᵣ callDepthPtr) ** (.x6 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (1 : Word)) **
       (.x8 ↦ᵣ fb) ** (.x10 ↦ᵣ fb) ** (callDepthPtr ↦ₘ (1 : Word))) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns [(.x5 : Reg), .x6, .x7] (by decide)
      (P := (.x8 ↦ᵣ y8) ** (.x10 ↦ᵣ fb) ** (callDepthPtr ↦ₘ (1 : Word)))
      (fun vf => ?_))
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right'] at hp
      xperm_hyp hp)
    (fun _ hq => hq)
    (callFrameEnter_segB_body_spec base fb (vf .x5) (vf .x6) (vf .x7) y8 callDepthPtr
      hlaCD hbr)

/-- Segment C with `a1`/`a2` surrendered rather than valued — the shape the
    callee hands back.  Both are written by the two `add`s before anything
    reads them. -/
theorem callFrameEnter_segC_own_spec
    (base sp ra link fb v8 z5 z10 poolPtr : Word)
    (hlaMP : base + (116 : Word) +
        (((laHi GuestAddrs.evm_memory_pool
            (GuestAddrs.call_frame_enter + 116)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.evm_memory_pool
          (GuestAddrs.call_frame_enter + 116)) = poolPtr) :
    cpsTripleWithin 12 (base + (116 : Word)) (ra &&& ~~~(1 : Word))
      (CodeReq.ofProg base callFrameEnter_prog)
      ((.x1 ↦ᵣ link) ** (.x2 ↦ᵣ (sp - (16 : Word))) ** (.x5 ↦ᵣ z5) **
       (.x8 ↦ᵣ fb) ** (.x10 ↦ᵣ z10) **
       ((sp - (16 : Word)) ↦ₘ ra) ** ((sp - (8 : Word)) ↦ₘ v8) **
       regOwns [(.x11 : Reg), .x12])
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ (99328 : Word)) **
       (.x8 ↦ᵣ v8) ** (.x10 ↦ᵣ poolPtr) **
       (.x11 ↦ᵣ (fb + (33280 : Word))) ** (.x12 ↦ᵣ (fb + (99328 : Word))) **
       ((sp - (16 : Word)) ↦ₘ ra) ** ((sp - (8 : Word)) ↦ₘ v8)) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns [(.x11 : Reg), .x12] (by decide)
      (P := (.x1 ↦ᵣ link) ** (.x2 ↦ᵣ (sp - (16 : Word))) ** (.x5 ↦ᵣ z5) **
        (.x8 ↦ᵣ fb) ** (.x10 ↦ᵣ z10) **
        ((sp - (16 : Word)) ↦ₘ ra) ** ((sp - (8 : Word)) ↦ₘ v8))
      (fun vf => ?_))
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right'] at hp
      xperm_hyp hp)
    (fun _ hq => hq)
    (callFrameEnter_segC_body_spec base sp ra link fb v8 z5 z10 (vf .x11) (vf .x12)
      poolPtr hlaMP)

/-! ## The deployed (anchored) whole-routine contract -/

/-- The routine's linked entry. -/
abbrev CFE : Word := (GuestAddrs.call_frame_enter : Word)

/-- Its one callee, on its linked entry. -/
abbrev FB : Word := (GuestAddrs.frame_base : Word)

/-- `call_frame_enter`'s code requirement: its own 41 instructions at
    `GuestAddrs.call_frame_enter`, plus the one routine it calls.

    The union is FORCED: the `jal ra, frame_base` at instruction index 13 is
    UNCONDITIONAL and sits above the routine's only branch, so every path
    leaves its own bytes.

    ⚠️ Spelled `CodeReq.union a b`, not `a.union b` — see #13198. -/
def cfeCR : CodeReq :=
  CodeReq.union
    (CodeReq.ofProg CFE callFrameEnter_prog)
    (CodeReq.ofProg FB frameBase_prog)

theorem cfe_disj_frameBase :
    (CodeReq.ofProg CFE callFrameEnter_prog).Disjoint
      (CodeReq.ofProg FB frameBase_prog) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem cfeProg_sub_cfeCR :
    ∀ a i, CodeReq.ofProg CFE callFrameEnter_prog a = some i → cfeCR a = some i :=
  CodeReq.union_mono_left

/-- The registers `call_frame_enter` surrenders to `frame_base` and never
    touches itself: `a3`-`a7` and `t3`-`t6`.  They go in as `regOwns` and come
    back as `regOwns`. -/
def cfeCalleeTemps : List Reg :=
  [.x13, .x14, .x15, .x16, .x17, .x28, .x29, .x30, .x31]

/-- The frame-arena address `frame_base` returns for a child depth — the
    callee's arithmetic, named once so the composed post can quote it. -/
abbrev cfeChildFrameBase (depth : Word) : Word :=
  (GuestAddrs.call_frame_arena : Word) + depth * (0x19000 : Word)

/-- The register hand-over into `frame_base`: the five registers this routine
    is holding values in at the call site (`t0`-`t2`, `a1`, `a2`) plus the nine
    it never touches make up exactly `fbRest`, the callee's owned set.

    Handing a valued register to a contract that only asks for ownership is a
    strengthening of the pre, so it is sound in this direction and this
    direction only — the post cannot hand the values back. -/
theorem cfe_atoms_to_fbRest (ret depth a5 a6 a7 a11 a12 : Word) :
    ∀ h,
      (((.x1 : Reg) ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ depth) ** ((.x5 : Reg) ↦ᵣ a5) ** ((.x6 : Reg) ↦ᵣ a6) **
         ((.x7 : Reg) ↦ᵣ a7) ** ((.x11 : Reg) ↦ᵣ a11) ** ((.x12 : Reg) ↦ᵣ a12) **
         regOwns cfeCalleeTemps)) h →
      (((.x10 : Reg) ↦ᵣ depth) ** ((.x1 : Reg) ↦ᵣ ret) **
        regOwns CallFrameBaseSAsm.fbRest) h := by
  intro h hp
  simp only [cfeCalleeTemps, regOwns_cons, regOwns_nil, sepConj_emp_right'] at hp
  have hp2 : (((.x10 : Reg) ↦ᵣ depth) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x5 : Reg) ↦ᵣ a5) ** ((.x6 : Reg) ↦ᵣ a6) ** ((.x7 : Reg) ↦ᵣ a7) **
      regOwn (.x28 : Reg) ** regOwn (.x29 : Reg) ** regOwn (.x30 : Reg) **
      regOwn (.x31 : Reg) ** ((.x11 : Reg) ↦ᵣ a11) ** ((.x12 : Reg) ↦ᵣ a12) **
      regOwn (.x13 : Reg) ** regOwn (.x14 : Reg) ** regOwn (.x15 : Reg) **
      regOwn (.x16 : Reg) ** regOwn (.x17 : Reg)) h := by xperm_hyp hp
  simp only [CallFrameBaseSAsm.fbRest, regOwns_cons, regOwns_nil, sepConj_emp_right']
  exact sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn _)
      (sepConj_mono (regIs_implies_regOwn _)
        (sepConj_mono (regIs_implies_regOwn _)
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right
              (sepConj_mono (regIs_implies_regOwn _)
                (sepConj_mono (regIs_implies_regOwn _) (fun _ hx => hx)))))))))))
    h hp2

/-- Call-site adapter for the `jal ra, frame_base` at instruction index 13
    (`CFE + 52`) — the unconditional frame-arena query. -/
theorem cfe_callSite13 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n FB ((CFE + (52 : Word) + 4) &&& ~~~(1 : Word))
      (CodeReq.ofProg FB frameBase_prog)
      ((.x1 ↦ᵣ (CFE + (52 : Word) + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (CFE + (52 : Word)) (CFE + (52 : Word) + 4) cfeCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := CFE + (52 : Word)) (calleeEntry := FB) (vOld := vRa)
    (calleeCode := CodeReq.ofProg FB frameBase_prog)
    (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.frame_base (GuestAddrs.call_frame_enter + 52))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at CFE (CFE + (52 : Word)) callFrameEnter_prog 13 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right cfe_disj_frameBase (fun _ _ h => h) a i h

/-- ⭐ **`call_frame_enter`, whole routine, depth-1 arm.**

    Entry `GuestAddrs.call_frame_enter`, exit `ra &&& ~~~1` — the caller's
    return address — over `cfeCR`, which pairs the linked `GuestAddrs` entry
    with `callFrameEnter_prog` exactly as `GuestImageEntries.lean:644` does,
    unioned with the one routine it calls.

    ⭐ **The callee contract is reused, not re-proved:**
    `CallFrameBaseSAsm.frameBase_spec`, a 6-step register-only triple that
    returns `a0 = call_frame_arena + depth * 0x19000`.

    One named gate selects the arm, and it is **this routine's own**:

    * `evm_call_depth = 1` — the parent is the top-level frame.

    Under it the `beq t1, t2` at index 19 is taken and the child's memory base
    is the pool base itself.  The routine also, unconditionally on this path:

    * bumps `evm_sparse_memory_next_epoch` from `epoch` to `epoch + 1`;
    * stamps the OLD `epoch` into
      `evm_sparse_memory_epoch_by_depth + 8 * depth`;
    * returns `a1 = frame_base(depth) + 0x8200` (child stack top) and
      `a2 = frame_base(depth) + 0x18400` (child env base).

    `ra`, `sp` and `s0` come back intact.  ⚠️ `t0`, `t1`, `t2` are CLOBBERED
    and the post says so.  `a3`-`a7`, `t3`-`t6` are surrendered to the callee
    and returned as `regOwns` — `frameBase_spec` says nothing about them, so
    neither does this.

    ⭐ **`frame_parent_bases` is NOT read**, which the triple states by not
    naming it anywhere — the `pcFree` frame turning that silence into a
    no-touch guarantee over the covered path.

    ⚠️ NOT proven: the `depth ≠ 1` arm at indices 20..28, which indexes
    `frame_parent_bases` and adds the parent's MSIZE at offset 488. -/
theorem callFrameEnterDepth1Flat_spec
    (sp ra depth v5 v6 v7 v8 v11 v12 epoch oldSlot : Word) :
    cpsTripleWithin 38 CFE (ra &&& ~~~(1 : Word)) cfeCR
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x7 ↦ᵣ v7) ** (.x8 ↦ᵣ v8) ** (.x10 ↦ᵣ depth) **
       (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwns cfeCalleeTemps **
       memOwn (sp - (16 : Word)) ** memOwn (sp - (8 : Word)) **
       ((GuestAddrs.evm_sparse_memory_next_epoch : Word) ↦ₘ epoch) **
       (((GuestAddrs.evm_sparse_memory_epoch_by_depth : Word) + (depth <<< (3 : Nat)))
          ↦ₘ oldSlot) **
       ((GuestAddrs.evm_call_depth : Word) ↦ₘ (1 : Word)))
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ (99328 : Word)) **
       (.x6 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (1 : Word)) ** (.x8 ↦ᵣ v8) **
       (.x10 ↦ᵣ (GuestAddrs.evm_memory_pool : Word)) **
       (.x11 ↦ᵣ (cfeChildFrameBase depth + (33280 : Word))) **
       (.x12 ↦ᵣ (cfeChildFrameBase depth + (99328 : Word))) **
       regOwns cfeCalleeTemps **
       ((sp - (16 : Word)) ↦ₘ ra) ** ((sp - (8 : Word)) ↦ₘ v8) **
       ((GuestAddrs.evm_sparse_memory_next_epoch : Word) ↦ₘ (epoch + (1 : Word))) **
       (((GuestAddrs.evm_sparse_memory_epoch_by_depth : Word) + (depth <<< (3 : Nat)))
          ↦ₘ epoch) **
       ((GuestAddrs.evm_call_depth : Word) ↦ₘ (1 : Word))) := by
  -- segment A: prologue, epoch bump, per-depth epoch stamp
  have hA := cpsTripleWithin_extend_code cfeProg_sub_cfeCR
    (callFrameEnter_segA_body_spec CFE sp ra v5 v6 v7 v8 depth
      (GuestAddrs.evm_sparse_memory_next_epoch : Word)
      (GuestAddrs.evm_sparse_memory_epoch_by_depth : Word) epoch oldSlot
      (by decide) (by decide))
  -- everything the callee and segments B..C touch that segment A does not
  have hA := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwns cfeCalleeTemps **
     ((GuestAddrs.evm_call_depth : Word) ↦ₘ (1 : Word)))
    (by
      dsimp [cfeCalleeTemps]
      pcf) hA
  -- the callee, reused rather than re-proved: `frame_base`'s 6-step
  -- register-only contract, with the five valued registers this routine holds
  -- at the call site weakened into the ownership the callee asks for
  have hU0 := CallFrameBaseSAsm.frameBase_spec depth (CFE + (52 : Word) + 4) (by decide)
  have hU : cpsTripleWithin 6 FB ((CFE + (52 : Word) + 4) &&& ~~~(1 : Word))
      (CodeReq.ofProg FB frameBase_prog)
      ((.x1 ↦ᵣ (CFE + (52 : Word) + 4)) **
        ((.x10 ↦ᵣ depth) **
         (.x5 ↦ᵣ ((GuestAddrs.evm_sparse_memory_epoch_by_depth : Word)
            + (depth <<< (3 : Nat)))) **
         (.x6 ↦ᵣ epoch) ** (.x7 ↦ᵣ (depth <<< (3 : Nat))) **
         (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwns cfeCalleeTemps))
      ((.x1 ↦ᵣ (CFE + (52 : Word) + 4)) ** (.x10 ↦ᵣ cfeChildFrameBase depth) **
        regOwns [(.x5 : Reg), .x6, .x7] ** regOwns [(.x11 : Reg), .x12] **
        regOwns cfeCalleeTemps) :=
    cpsTripleWithin_weaken
      (cfe_atoms_to_fbRest (CFE + (52 : Word) + 4) depth _ epoch _ v11 v12)
      (fun _ hq => by
        simp only [cfeCalleeTemps, CallFrameBaseSAsm.fbRest, regOwns_cons, regOwns_nil,
          sepConj_emp_right'] at hq ⊢
        xperm_hyp hq)
      hU0
  have hCall := cfe_callSite13 (n := 6) ra
    (by
      dsimp [cfeCalleeTemps]
      pcf) hU
  rw [show CFE + (52 : Word) + 4 = CFE + (56 : Word) from by bv_omega] at hCall
  -- segment B: the call-depth discrimination, taken under the gate
  have hB := cpsTripleWithin_extend_code cfeProg_sub_cfeCR
    (callFrameEnter_segB_own_spec CFE (cfeChildFrameBase depth) v8
      (GuestAddrs.evm_call_depth : Word) (by decide) (by decide))
  -- segment C: the pool base, the two frame offsets and the epilogue
  have hC := cpsTripleWithin_extend_code cfeProg_sub_cfeCR
    (callFrameEnter_segC_own_spec CFE sp ra (CFE + (56 : Word))
      (cfeChildFrameBase depth) v8 (GuestAddrs.evm_call_depth : Word)
      (cfeChildFrameBase depth) (GuestAddrs.evm_memory_pool : Word) (by decide))
  seqFrame hA hCall
  seqFrame hAhCall hB
  seqFrame hAhCallhB hC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hAhCallhBhC

#print axioms callFrameEnterDepth1Flat_spec

end EvmAsm.Codegen.Proofs
