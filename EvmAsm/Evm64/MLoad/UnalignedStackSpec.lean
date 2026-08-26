/-
  EvmAsm.Evm64.MLoad.UnalignedStackSpec

  Per-quarter unaligned MLOAD stack-level wrappers (q0/q1/q2/q3), shaped
  to match the `h0/h1/h2/h3` hypotheses of
  `evm_mload_combined_one_limb_sequence_stack_spec_within` in
  `EvmAsm/Evm64/MLoad/StackSpec.lean`. Split out of `StackSpec.lean` so
  the host file stays under the 1500-line file-size cap (#3126).

  Direct MLOAD analog of the per-quarter MSTORE lemmas in
  `EvmAsm/Evm64/MStore/UnalignedStackSpec.lean`.
-/

module

public import EvmAsm.Evm64.Stack
public import EvmAsm.Evm64.MLoad.Spec
public import EvmAsm.Evm64.MLoad.UnalignedSpec

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/--
MLOAD q0 unaligned per-quarter stack spec: a fully-instantiated unaligned
byte-load triple at `(base + 8) .. (base + 100)` over the q0 byte-pack
program slot of `evm_mload_code`, shaped to match the `h0` hypothesis of
`evm_mload_combined_one_limb_sequence_stack_spec_within` (above).

For q0 the destination dword offset is `0`, so the stored limb lands at
`sp + 0 = sp` — i.e. the dst slot IS the prologue-threaded `(sp ↦ₘ offset)`
cell, which transitions from holding `offset` to holding the packed limb
`mloadPackedLimbFromDwordPair loVal hiVal start`.

The pre/post threads the prologue cells (`offReg`, `memBaseReg`,
`addrReg ↦ᵣ memBase + offset`) UNCHANGED on the right of the underlying
unaligned spec, plus the byte-pack cells (`byteReg`, `accReg`, `loAddr`,
`hiAddr`) inside the byte-load assertion.

Sub-slice toward `evm_mload_stack_spec_within` (evm-asm-lrhou / GH #53
follow-up): together with q1/q2/q3 siblings (filed as follow-ups), feeds
`evm_mload_combined_one_limb_sequence_stack_spec_within` to land the
topmost stack-level MLOAD theorem.

Distinctive token: evm_mload_unaligned_one_limb_q0_stack_spec_within #53.
-/
theorem evm_mload_unaligned_one_limb_q0_stack_spec_within
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld : Word)
    (loAddr hiAddr loVal hiVal : Word) (start : Nat)
    (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mloadLimbWindowOk (memBase + offset) loAddr hiAddr start
                  24 25 26 27 28 29 30 31) :
    cpsTripleWithin 23 (base + 8) (base + 100)
      (mloadOneLimbCode addrReg byteReg accReg
        24 25 26 27 28 29 30 31 0 (base + 8))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (sp ↦ₘ offset) **
       ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
        (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (sp ↦ₘ mloadPackedLimbFromDwordPair loVal hiVal start) **
       ((byteReg ↦ᵣ
          (mloadByteFromDwordPair loVal hiVal start 7).zeroExtend 64) **
        (accReg ↦ᵣ mloadPackedLimbFromDwordPair loVal hiVal start) **
        (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))) := by
  -- Underlying unaligned one-limb spec at the q0 slot, with dstOff = 0
  -- and dstWordOld = offset (matches the prologue-threaded `sp ↦ₘ offset`
  -- cell since `sp + signExtend12 0 = sp`).
  have core := mload_one_limb_unaligned_spec_within addrReg byteReg accReg
    (memBase + offset) accOld byteOld loVal hiVal loAddr hiAddr sp offset
    24 25 26 27 28 29 30 31 (0 : BitVec 12) start (base + 8)
    h_byte_ne_x0 h_acc_ne_x0 h_window
  rw [mloadOneLimbUnalignedPre_unfold, mloadOneLimbUnalignedPost_unfold] at core
  -- `signExtend12 0 = 0` so `sp + signExtend12 0 = sp`.
  have hsig : sp + signExtend12 (0 : BitVec 12) = sp := by
    have : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
    rw [this]; bv_omega
  rw [hsig] at core
  -- Normalize endpoint: `base + 8 + 92 = base + 100`.
  have hpc : (base + 8 + 92 : Word) = base + 100 := by bv_omega
  rw [hpc] at core
  -- Frame the prologue-threaded `(offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase)`
  -- on the left. (`addrReg ↦ᵣ memBase + offset` is already in `core`'s pre.)
  have framed := cpsTripleWithin_frameL
    (F := (offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase))
    (by pcFree) core
  -- Permute pre/post into the goal's grouping.
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
MLOAD q1 unaligned per-quarter stack spec: a fully-instantiated unaligned
byte-load triple at `(base + 100) .. (base + 192)` over the q1 byte-pack
program slot of `evm_mload_code`, shaped to match the `h1` hypothesis of
`evm_mload_combined_one_limb_sequence_stack_spec_within` (above).

For q1 the destination dword offset is `8`, so the stored limb lands at
`sp + 8` — a fresh limb slot DISTINCT from the prologue-threaded
`(sp ↦ₘ offset)` cell at `sp + 0`. The q0 packed-limb cell at `sp` is
threaded UNCHANGED through q1's pre/post (sitting in the right-side
frame of the underlying unaligned spec).

Sub-slice toward `evm_mload_stack_spec_within` (evm-asm-lrhou / GH #53
follow-up): together with q0/q2/q3 siblings, feeds
`evm_mload_combined_one_limb_sequence_stack_spec_within` to land the
topmost stack-level MLOAD theorem.

Distinctive token: evm_mload_unaligned_one_limb_q1_stack_spec_within #53.
-/
theorem evm_mload_unaligned_one_limb_q1_stack_spec_within
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld : Word)
    (q0Old : Word)
    (loAddr1 hiAddr1 loVal1 hiVal1 : Word) (start : Nat)
    (dstOld : Word)
    (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mloadLimbWindowOk (memBase + offset) loAddr1 hiAddr1 start
                  16 17 18 19 20 21 22 23) :
    cpsTripleWithin 23 (base + 100) (base + 192)
      (mloadOneLimbCode addrReg byteReg accReg
        16 17 18 19 20 21 22 23 8 (base + 100))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (sp ↦ₘ q0Old) **
       (sp + 8 ↦ₘ dstOld) **
       ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
        (loAddr1 ↦ₘ loVal1) ** (hiAddr1 ↦ₘ hiVal1)))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (sp ↦ₘ q0Old) **
       (sp + 8 ↦ₘ mloadPackedLimbFromDwordPair loVal1 hiVal1 start) **
       ((byteReg ↦ᵣ
          (mloadByteFromDwordPair loVal1 hiVal1 start 7).zeroExtend 64) **
        (accReg ↦ᵣ mloadPackedLimbFromDwordPair loVal1 hiVal1 start) **
        (loAddr1 ↦ₘ loVal1) ** (hiAddr1 ↦ₘ hiVal1))) := by
  -- Underlying unaligned one-limb spec at the q1 slot, with dstOff = 8
  -- and dstWordOld = dstOld stored at `sp + signExtend12 8 = sp + 8`.
  have core := mload_one_limb_unaligned_spec_within addrReg byteReg accReg
    (memBase + offset) accOld byteOld loVal1 hiVal1 loAddr1 hiAddr1 sp dstOld
    16 17 18 19 20 21 22 23 (8 : BitVec 12) start (base + 100)
    h_byte_ne_x0 h_acc_ne_x0 h_window
  rw [mloadOneLimbUnalignedPre_unfold, mloadOneLimbUnalignedPost_unfold] at core
  -- `signExtend12 8 = 8` so `sp + signExtend12 8 = sp + 8`.
  have hsig : sp + signExtend12 (8 : BitVec 12) = sp + 8 := by
    have : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
    rw [this]
  rw [hsig] at core
  -- Normalize endpoint: `base + 100 + 92 = base + 192`.
  have hpc : (base + 100 + 92 : Word) = base + 192 := by bv_omega
  rw [hpc] at core
  -- Frame the prologue-threaded `(offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase)`
  -- and the q0 packed-limb cell `(sp ↦ₘ q0Old)` on the left.
  have framed := cpsTripleWithin_frameL
    (F := (offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) ** (sp ↦ₘ q0Old))
    (by pcFree) core
  -- Permute pre/post into the goal's grouping.
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
MLOAD q2 unaligned per-quarter stack spec: a fully-instantiated unaligned
byte-load triple at `(base + 192) .. (base + 284)` over the q2 byte-pack
program slot of `evm_mload_code`, shaped to match the `h2` hypothesis of
`evm_mload_combined_one_limb_sequence_stack_spec_within` (above).

For q2 the destination dword offset is `16`, so the stored limb lands at
`sp + 16` — a fresh limb slot DISTINCT from both the prologue-threaded
`(sp ↦ₘ offset)` cell at `sp + 0` (now holding the q0 packed limb) and
the q1 packed-limb cell at `sp + 8`. The q0 cell at `sp` and the q1 cell
at `sp + 8` are threaded UNCHANGED through q2's pre/post (sitting in the
right-side frame of the underlying unaligned spec).

Sub-slice toward `evm_mload_stack_spec_within` (evm-asm-lrhou / GH #53
follow-up): together with q0/q1/q3 siblings, feeds
`evm_mload_combined_one_limb_sequence_stack_spec_within` to land the
topmost stack-level MLOAD theorem.

Distinctive token: evm_mload_unaligned_one_limb_q2_stack_spec_within #53.
-/
theorem evm_mload_unaligned_one_limb_q2_stack_spec_within
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld : Word)
    (q0Old q1Old : Word)
    (loAddr2 hiAddr2 loVal2 hiVal2 : Word) (start : Nat)
    (dstOld : Word)
    (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mloadLimbWindowOk (memBase + offset) loAddr2 hiAddr2 start
                  8 9 10 11 12 13 14 15) :
    cpsTripleWithin 23 (base + 192) (base + 284)
      (mloadOneLimbCode addrReg byteReg accReg
        8 9 10 11 12 13 14 15 16 (base + 192))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (sp ↦ₘ q0Old) **
       (sp + 8 ↦ₘ q1Old) **
       (sp + 16 ↦ₘ dstOld) **
       ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
        (loAddr2 ↦ₘ loVal2) ** (hiAddr2 ↦ₘ hiVal2)))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (sp ↦ₘ q0Old) **
       (sp + 8 ↦ₘ q1Old) **
       (sp + 16 ↦ₘ mloadPackedLimbFromDwordPair loVal2 hiVal2 start) **
       ((byteReg ↦ᵣ
          (mloadByteFromDwordPair loVal2 hiVal2 start 7).zeroExtend 64) **
        (accReg ↦ᵣ mloadPackedLimbFromDwordPair loVal2 hiVal2 start) **
        (loAddr2 ↦ₘ loVal2) ** (hiAddr2 ↦ₘ hiVal2))) := by
  -- Underlying unaligned one-limb spec at the q2 slot, with dstOff = 16
  -- and dstWordOld = dstOld stored at `sp + signExtend12 16 = sp + 16`.
  have core := mload_one_limb_unaligned_spec_within addrReg byteReg accReg
    (memBase + offset) accOld byteOld loVal2 hiVal2 loAddr2 hiAddr2 sp dstOld
    8 9 10 11 12 13 14 15 (16 : BitVec 12) start (base + 192)
    h_byte_ne_x0 h_acc_ne_x0 h_window
  rw [mloadOneLimbUnalignedPre_unfold, mloadOneLimbUnalignedPost_unfold] at core
  -- `signExtend12 16 = 16` so `sp + signExtend12 16 = sp + 16`.
  have hsig : sp + signExtend12 (16 : BitVec 12) = sp + 16 := by
    have : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
    rw [this]
  rw [hsig] at core
  -- Normalize endpoint: `base + 192 + 92 = base + 284`.
  have hpc : (base + 192 + 92 : Word) = base + 284 := by bv_omega
  rw [hpc] at core
  -- Frame the prologue-threaded `(offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase)`
  -- and the q0/q1 packed-limb cells `(sp ↦ₘ q0Old) ** (sp + 8 ↦ₘ q1Old)`
  -- on the left.
  have framed := cpsTripleWithin_frameL
    (F := (offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) **
          (sp ↦ₘ q0Old) ** (sp + 8 ↦ₘ q1Old))
    (by pcFree) core
  -- Permute pre/post into the goal's grouping.
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
MLOAD q3 unaligned per-quarter stack spec: a fully-instantiated unaligned
byte-load triple at `(base + 284) .. (base + 376)` over the q3 byte-pack
program slot of `evm_mload_code`, shaped to match the `h3` hypothesis of
`evm_mload_combined_one_limb_sequence_stack_spec_within` (above).

For q3 the destination dword offset is `24`, so the stored limb lands at
`sp + 24` — a fresh limb slot DISTINCT from the prologue-threaded
`(sp ↦ₘ offset)` cell at `sp + 0` (now holding the q0 packed limb), the
q1 packed-limb cell at `sp + 8`, and the q2 packed-limb cell at
`sp + 16`. The q0/q1/q2 cells are threaded UNCHANGED through q3's
pre/post (sitting in the right-side frame of the underlying unaligned
spec).

Sub-slice toward `evm_mload_stack_spec_within` (evm-asm-lrhou / GH #53
follow-up): together with q0/q1/q2 siblings, feeds
`evm_mload_combined_one_limb_sequence_stack_spec_within` to land the
topmost stack-level MLOAD theorem.

Distinctive token: evm_mload_unaligned_one_limb_q3_stack_spec_within #53.
-/
theorem evm_mload_unaligned_one_limb_q3_stack_spec_within
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld : Word)
    (q0Old q1Old q2Old : Word)
    (loAddr3 hiAddr3 loVal3 hiVal3 : Word) (start : Nat)
    (dstOld : Word)
    (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mloadLimbWindowOk (memBase + offset) loAddr3 hiAddr3 start
                  0 1 2 3 4 5 6 7) :
    cpsTripleWithin 23 (base + 284) (base + 376)
      (mloadOneLimbCode addrReg byteReg accReg
        0 1 2 3 4 5 6 7 24 (base + 284))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (sp ↦ₘ q0Old) **
       (sp + 8 ↦ₘ q1Old) **
       (sp + 16 ↦ₘ q2Old) **
       (sp + 24 ↦ₘ dstOld) **
       ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
        (loAddr3 ↦ₘ loVal3) ** (hiAddr3 ↦ₘ hiVal3)))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (sp ↦ₘ q0Old) **
       (sp + 8 ↦ₘ q1Old) **
       (sp + 16 ↦ₘ q2Old) **
       (sp + 24 ↦ₘ mloadPackedLimbFromDwordPair loVal3 hiVal3 start) **
       ((byteReg ↦ᵣ
          (mloadByteFromDwordPair loVal3 hiVal3 start 7).zeroExtend 64) **
        (accReg ↦ᵣ mloadPackedLimbFromDwordPair loVal3 hiVal3 start) **
        (loAddr3 ↦ₘ loVal3) ** (hiAddr3 ↦ₘ hiVal3))) := by
  -- Underlying unaligned one-limb spec at the q3 slot, with dstOff = 24
  -- and dstWordOld = dstOld stored at `sp + signExtend12 24 = sp + 24`.
  have core := mload_one_limb_unaligned_spec_within addrReg byteReg accReg
    (memBase + offset) accOld byteOld loVal3 hiVal3 loAddr3 hiAddr3 sp dstOld
    0 1 2 3 4 5 6 7 (24 : BitVec 12) start (base + 284)
    h_byte_ne_x0 h_acc_ne_x0 h_window
  rw [mloadOneLimbUnalignedPre_unfold, mloadOneLimbUnalignedPost_unfold] at core
  -- `signExtend12 24 = 24` so `sp + signExtend12 24 = sp + 24`.
  have hsig : sp + signExtend12 (24 : BitVec 12) = sp + 24 := by
    have : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
    rw [this]
  rw [hsig] at core
  -- Normalize endpoint: `base + 284 + 92 = base + 376`.
  have hpc : (base + 284 + 92 : Word) = base + 376 := by bv_omega
  rw [hpc] at core
  -- Frame the prologue-threaded `(offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase)`
  -- and the q0/q1/q2 packed-limb cells on the left.
  have framed := cpsTripleWithin_frameL
    (F := (offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) **
          (sp ↦ₘ q0Old) ** (sp + 8 ↦ₘ q1Old) ** (sp + 16 ↦ₘ q2Old))
    (by pcFree) core
  -- Permute pre/post into the goal's grouping.
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

end EvmAsm.Evm64
