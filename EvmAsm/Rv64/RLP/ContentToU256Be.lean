/-
  EvmAsm.Rv64.RLP.ContentToU256Be

  A verified RISC-V leaf subroutine that is a **drop-in replacement** for the
  (currently unverified) codegen guest function `rlp_content_to_u256_be`
  emitted as a raw assembly string by
  `EvmAsm/Codegen/Programs/RlpWalk.lean` (`rlpContentToU256BeFunction`).

  The guest routine decodes the prefix-stripped payload of an RLP byte-string
  item (an Ethereum *scalar*, e.g. a balance / nonce / gas value) into a
  right-aligned 32-byte big-endian `u256` output buffer. It is one half of
  `rlp_field_to_u256_be` (`EvmAsm/Codegen/Programs/Tx.lean`).

  ## Caller-facing contract (LP64, see `EvmAsm/Evm64/CallingConvention.lean`)

  `rlp_content_to_u256_be` is a frameless leaf function: it is reached by
  `jal ra, rlp_content_to_u256_be` and returns with `ret` (`JALR x0, ra, 0`).

  ### Inputs (how to give them)
  * `a0` (`x10`) — pointer to the `content` bytes (the prefix-stripped payload).
  * `a1` (`x11`) — `content` byte length.
  * `a2` (`x12`) — pointer to the 32-byte output buffer. Must be 8-byte aligned
    (the routine writes it with `SD`); ownership of the four dwords at `a2`,
    `a2+8`, `a2+16`, `a2+24` is transferred to the routine for the duration of
    the call and returned to the caller on exit.

  ### Outputs (where they are located)
  * `a0` (`x10`) — **status**: `0` on success, `2` when `content` is too long
    (`len > 32`, which cannot fit a `u256`).
  * The 32 bytes at `a2` hold, **on success**, the big-endian `u256` whose
    low `len` bytes are `content` (right-aligned, high bytes zero).

  ### What happens to the output memory region
  * On **success** (`len ≤ 32`) the output region holds the decoded value.
  * On **failure** (`len > 32`) the routine returns `a0 = 2` and the 32-byte
    output region may hold **arbitrary content** — callers must not read it.
    (This implementation in fact zeroes the buffer before the length check, so
    the bytes are all `0`; the *contract* deliberately under-specifies them so
    that any conforming implementation is a valid drop-in and callers never
    depend on the zero-fill. This is expressed below with `memOwnU256`: the
    caller still owns a writable 32-byte region at `a2`, but its contents are
    unconstrained.)

  ## Verification status

  This file lays out the faithful 21-instruction drop-in body
  `rlp_content_to_u256_be_prog` and proves the **content-too-long failure
  path** (`len > 32`) as a complete leaf-function Hoare triple
  (`rlp_content_to_u256_be_too_long_spec_within`). The success path (the
  right-aligned copy loop, `len ≤ 32`) is a follow-up.
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.RLP.Phase2LongLoopGeneral
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPerm

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/--
The faithful verified drop-in body for the codegen guest `rlp_content_to_u256_be`
(21 instructions). Register map: `a0=x10`, `a1=x11`, `a2=x12`, `t0=x5`, `t1=x6`,
`t2=x7`, `t3=x28`, `t4=x29`, `ra=x1`.

```
   0  SD   x12 x0 0      ; zero out[0..7]
   1  SD   x12 x0 8      ; zero out[8..15]
   2  SD   x12 x0 16     ; zero out[16..23]
   3  SD   x12 x0 24     ; zero out[24..31]
   4  LI   x5  32        ; t0 = 32
   5  BLTU x5  x11 56    ; if 32 < len goto too_long (idx 19, +56 bytes)
   6  SUB  x5  x5  x11   ; t0 = 32 - len
   7  ADD  x6  x12 x5    ; t1 = a2 + (32 - len)   right-aligned dst
   8  MV   x7  x10       ; t2 = src
   9  MV   x28 x11       ; t3 = remaining
  10  BEQ  x28 x0 28     ; copy loop: if remaining==0 goto done (idx 17, +28)
  11  LBU  x29 x7 0      ; t4 = src[0]
  12  SB   x6  x29 0     ; dst[0] = t4
  13  ADDI x7  x7 1
  14  ADDI x6  x6 1
  15  ADDI x28 x28 (-1)
  16  JAL  x0 (-24)      ; goto copy loop (idx 10, -24 bytes)
  17  LI   x10 0         ; done: a0 = 0 (ok)
  18  JALR x0 x1 0       ; ret
  19  LI   x10 2         ; too_long: a0 = 2
  20  JALR x0 x1 0       ; ret
```
-/
def rlp_content_to_u256_be_prog : List Instr :=
  [ .SD .x12 .x0 0,           -- 0
    .SD .x12 .x0 8,           -- 1
    .SD .x12 .x0 16,          -- 2
    .SD .x12 .x0 24,          -- 3
    .LI .x5 (32 : Word),      -- 4
    .BLTU .x5 .x11 (56 : BitVec 13),   -- 5
    .SUB .x5 .x5 .x11,        -- 6
    .ADD .x6 .x12 .x5,        -- 7
    .MV .x7 .x10,             -- 8
    .MV .x28 .x11,            -- 9
    .BEQ .x28 .x0 (28 : BitVec 13),    -- 10
    .LBU .x29 .x7 0,          -- 11
    .SB .x6 .x29 0,           -- 12
    .ADDI .x7 .x7 (1 : BitVec 12),     -- 13
    .ADDI .x6 .x6 (1 : BitVec 12),     -- 14
    .ADDI .x28 .x28 (-1 : BitVec 12),  -- 15
    .JAL .x0 (-24 : BitVec 21),        -- 16
    .LI .x10 (0 : Word),      -- 17
    .JALR .x0 .x1 0,          -- 18
    .LI .x10 (2 : Word),      -- 19
    .JALR .x0 .x1 0 ]         -- 20

theorem rlp_content_to_u256_be_prog_length :
    rlp_content_to_u256_be_prog.length = 21 := rfl

/-- The drop-in body as a `CodeReq` rooted at `base`. -/
abbrev rlp_content_to_u256_be_code (base : Word) : CodeReq :=
  CodeReq.ofProg base rlp_content_to_u256_be_prog

/-- Owned, value-unconstrained 32-byte output region: four dwords at
    `outPtr`, `outPtr+8`, `outPtr+16`, `outPtr+24`. Used as the caller's
    output-buffer ownership token, both on entry and (for the failure path)
    on exit — capturing "the caller owns a writable 32-byte region whose
    contents are unconstrained". -/
def memOwnU256 (outPtr : Word) : Assertion :=
  memOwn outPtr ** memOwn (outPtr + 8) ** memOwn (outPtr + 16) ** memOwn (outPtr + 24)

/--
**`rlp_content_to_u256_be` — content-too-long failure path.**

When the requested content length exceeds 32 bytes (`32 <ᵤ len`), the routine
returns status `a0 = 2` and leaves the 32-byte output buffer at `a2` owned by
the caller but with **arbitrary content** (`memOwnU256 outPtr` in the post).

Registers `a1`/`a2`/`ra` are preserved; `t0` (`x5`) is clobbered to `32`.
The routine returns to `ra &&& ~~~1` (`JALR x0, ra, 0`).

This is a complete Hoare triple on the failure subdomain `len > 32`. The
success path (`len ≤ 32`, the right-aligned copy loop) is a follow-up.
-/
theorem rlp_content_to_u256_be_too_long_spec_within
    (base contentPtr len outPtr t0Old raVal : Word)
    (h_too_long : BitVec.ult (32 : Word) len) :
    cpsTripleWithin 8 base (raVal &&& ~~~1) (rlp_content_to_u256_be_code base)
      ((.x10 ↦ᵣ contentPtr) ** (.x11 ↦ᵣ len) ** (.x12 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ t0Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        memOwnU256 outPtr)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x11 ↦ᵣ len) ** (.x12 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ (32 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        memOwnU256 outPtr) := by
  -- Phase A: zero the 32-byte output and load 32 into t0 (idx 0..4), base → base + 20.
  have hSD0 := sd_spec_gen_own_within .x12 .x0 outPtr (0 : Word) (0 : BitVec 12) base
  have hSD1 := sd_spec_gen_own_within .x12 .x0 outPtr (0 : Word) (8 : BitVec 12) (base + 4)
  have hSD2 := sd_spec_gen_own_within .x12 .x0 outPtr (0 : Word) (16 : BitVec 12) (base + 8)
  have hSD3 := sd_spec_gen_own_within .x12 .x0 outPtr (0 : Word) (24 : BitVec 12) (base + 12)
  have hLI := li_spec_gen_within .x5 t0Old (32 : Word) (base + 16) (by decide)
  simp only [signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24] at hSD0 hSD1 hSD2 hSD3
  have hA : cpsTripleWithin 5 base (base + 20) (rlp_content_to_u256_be_code base)
      ((.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ t0Old) ** (.x11 ↦ᵣ len) **
        (.x10 ↦ᵣ contentPtr) ** (.x1 ↦ᵣ raVal) **
        memOwn outPtr ** memOwn (outPtr + 8) ** memOwn (outPtr + 16) ** memOwn (outPtr + 24))
      ((.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (32 : Word)) ** (.x11 ↦ᵣ len) **
        (.x10 ↦ᵣ contentPtr) ** (.x1 ↦ᵣ raVal) **
        (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) **
        ((outPtr + 16) ↦ₘ (0 : Word)) ** ((outPtr + 24) ↦ₘ (0 : Word))) := by
    runBlock hSD0 hSD1 hSD2 hSD3 hLI
  -- Phase B: BLTU x5 x11 56 at base+20; taken since 32 <ᵤ len (idx 5), base+20 → base+76.
  have hBr_raw := bltu_spec_gen_within .x5 .x11 (56 : BitVec 13) (32 : Word) len (base + 20)
  have ha_t : (base + 20) + signExtend13 (56 : BitVec 13) = base + 76 := by
    rw [show signExtend13 (56 : BitVec 13) = (56 : Word) from by decide]; bv_omega
  have ha_f : (base + 20 : Word) + 4 = base + 24 := by bv_omega
  rw [ha_t, ha_f] at hBr_raw
  have hBr_framed := cpsBranchWithin_frameR
    ((.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ contentPtr) ** (.x1 ↦ᵣ raVal) **
      (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) **
      ((outPtr + 16) ↦ₘ (0 : Word)) ** ((outPtr + 24) ↦ₘ (0 : Word)))
    (by pcFree) hBr_raw
  have hBr_ext := cpsBranchWithin_extend_code (cr' := rlp_content_to_u256_be_code base)
    (fun a i h => by
      simp only [CodeReq.singleton] at h
      split at h
      · next heq =>
        rw [beq_iff_eq] at heq
        rw [heq]
        simp only [Option.some.injEq] at h
        subst h
        exact CodeReq.ofProg_lookup_addr base rlp_content_to_u256_be_prog 5 (base + 20)
          (by rw [rlp_content_to_u256_be_prog_length]; norm_num)
          (by rw [rlp_content_to_u256_be_prog_length]; norm_num)
          (by rfl)
      · simp at h) hBr_framed
  -- Compose Phase A with the branch, then keep the taken path.
  have hBranch := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun h hp => by xperm_hyp hp) hA hBr_ext
  have hTaken := cpsBranchWithin_takenPath hBranch (fun hp hQf => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
    exact ((sepConj_pure_right _).1 h_pure).2 h_too_long)
  -- Phase C: LI x10 2 ; ret  (idx 19, 20), base+76 → ra &&& ~~~1.
  have hLI2 := li_spec_gen_within .x10 contentPtr (2 : Word) (base + 76) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 80)
  simp only [signExtend12_0] at hRet
  have hC : cpsTripleWithin 2 (base + 76) (raVal &&& ~~~1) (rlp_content_to_u256_be_code base)
      ((.x10 ↦ᵣ contentPtr) ** (.x11 ↦ᵣ len) ** (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (32 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) **
        ((outPtr + 16) ↦ₘ (0 : Word)) ** ((outPtr + 24) ↦ₘ (0 : Word)) **
        ⌜BitVec.ult (32 : Word) len⌝)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x11 ↦ᵣ len) ** (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (32 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) **
        ((outPtr + 16) ↦ₘ (0 : Word)) ** ((outPtr + 24) ↦ₘ (0 : Word)) **
        ⌜BitVec.ult (32 : Word) len⌝) := by
    runBlock hLI2 hRet
  have hFull := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hTaken hC
  -- Weaken to the public caller contract: drop the pure guard, and weaken each
  -- zeroed output dword to `memOwn` (arbitrary content on the failure path).
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hFull
  · simp only [memOwnU256] at hp
    xperm_hyp hp
  · simp only [memOwnU256]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn
              (fun h' hp' => memIs_implies_memOwn _ ((sepConj_pure_right h').1 hp').1))))))))) h hq

/-- `bytesRegion` is PC-free — lets `runBlock`/`pcFree` discharge frame
    side-conditions involving the region (mirrors `FlatListLoopBody`). -/
instance (regionBase : Word) (bs : List (BitVec 8)) :
    Assertion.PCFree (bytesRegion regionBase bs) :=
  ⟨bytesRegion_pcFree _ _⟩

/-! ## Success path (`len ≤ 32`): the right-aligned copy loop

The success path runs the byte-copy loop at idx 10..16. We build it bottom-up:
one copy iteration (idx 11..15), the do-while loop by induction on the counter,
the register setup (idx 6..9), and the `len ≤ 32` branch fall-through. -/

set_option maxRecDepth 8000 in
/-- One copy iteration (idx 11..15, `base+44 → base+64`): read `src[si]`, write it
    to `dst[di]`, advance both pointers, decrement the counter. The source region
    is unchanged; destination byte `di` becomes `src[si]`. -/
theorem cu256_copy_body_spec_within
    (base srcBase dstBase x29Old x28Val : Word)
    (srcBytes dstBytes : List (BitVec 8)) (si di : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hdalign : dstBase.toNat % 8 = 0)
    (hsi : si < srcBytes.length) (hdi : di < dstBytes.length)
    (hsover : srcBase.toNat + si < 2 ^ 64) (hdover : dstBase.toNat + di < 2 ^ 64)
    (hsvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 si) = true)
    (hdvalid : isValidByteAccess (dstBase + BitVec.ofNat 64 di) = true) :
    cpsTripleWithin 5 (base + 44) (base + 64) (rlp_content_to_u256_be_code base)
      ((.x29 ↦ᵣ x29Old) ** (.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       (.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 di)) ** (.x28 ↦ᵣ x28Val) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      ((.x29 ↦ᵣ (srcBytes[si]'hsi).zeroExtend 64) **
       (.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
       (.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (di + 1))) **
       (.x28 ↦ᵣ (x28Val + signExtend12 (-1 : BitVec 12))) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsi))) := by
  have lbu := bytesRegion_lbu_within .x29 .x7 srcBase x29Old (base + 44) srcBytes si
    (by decide) hsalign hsi hsover hsvalid
  have sb := bytesRegion_sb_within .x6 .x29 dstBase ((srcBytes[si]'hsi).zeroExtend 64)
    (base + 48) dstBytes di hdalign hdi hdover hdvalid
  rw [show ((srcBytes[si]'hsi).zeroExtend 64).truncate 8 = srcBytes[si]'hsi from by simp] at sb
  have a7 := addi_spec_gen_same_within .x7 (srcBase + BitVec.ofNat 64 si) 1 (base + 52) (by nofun)
  rw [show (srcBase + BitVec.ofNat 64 si) + signExtend12 (1 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (si + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at a7
  have a6 := addi_spec_gen_same_within .x6 (dstBase + BitVec.ofNat 64 di) 1 (base + 56) (by nofun)
  rw [show (dstBase + BitVec.ofNat 64 di) + signExtend12 (1 : BitVec 12)
      = dstBase + BitVec.ofNat 64 (di + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at a6
  have a28 := addi_spec_gen_same_within .x28 x28Val (-1 : BitVec 12) (base + 60) (by nofun)
  runBlock lbu sb a7 a6 a28

/-- Result of `n` copy iterations: write `src[si+j]` into `dst[di+j]` for `j < n`,
    advancing both indices one byte per step. -/
def copyN (dst src : List (BitVec 8)) (di si : Nat) : Nat → List (BitVec 8)
  | 0 => dst
  | k + 1 => copyN (dst.set di (getByteAt src si)) src (di + 1) (si + 1) k

theorem copyN_zero (dst src : List (BitVec 8)) (di si : Nat) :
    copyN dst src di si 0 = dst := rfl

theorem copyN_succ (dst src : List (BitVec 8)) (di si k : Nat) :
    copyN dst src di si (k + 1)
      = copyN (dst.set di (getByteAt src si)) src (di + 1) (si + 1) k := rfl

theorem copyN_length (dst src : List (BitVec 8)) (di si n : Nat) :
    (copyN dst src di si n).length = dst.length := by
  induction n generalizing dst di si with
  | zero => rfl
  | succ k ih => rw [copyN_succ, ih, List.length_set]

/-- The 4-dword zeroed output buffer equals the byte region of 32 zeros. -/
theorem bytesRegion_replicate32_zero (base : Word) :
    bytesRegion base (List.replicate 32 (0 : BitVec 8))
      = ((base ↦ₘ (0 : Word)) ** ((base + 8) ↦ₘ (0 : Word)) **
         ((base + 16) ↦ₘ (0 : Word)) ** ((base + 24) ↦ₘ (0 : Word))) := by
  rw [bytesRegion_eq_cons base _ (by decide),
      bytesRegion_eq_cons (base + 8) _ (by decide),
      bytesRegion_eq_cons (base + 8 + 8) _ (by decide),
      bytesRegion_eq_cons (base + 8 + 8 + 8) _ (by decide),
      show (base + 8 + 8 + 8 : Word) = base + 24 from by bv_omega,
      show (base + 8 + 8 : Word) = base + 16 from by bv_omega]
  simp [sepConj_emp_right',
    show packBytes ([0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] : List (BitVec 8)) = (0 : Word)
      from by decide]

/-- **The copy loop (idx 10..16), `base+40 → base+68`, by induction on the counter.**
    With counter `n`, src pointer `srcBase+si`, dst pointer `dstBase+di`, the
    while-loop copies `n` bytes (`src[si+j] → dst[di+j]`) and falls out to `done`
    with the counter at `0` and the pointers advanced by `n`. The destination
    byte temp `x29` is left unconstrained (`regOwn`). -/
theorem cu256_loop_spec_within
    (base srcBase dstBase x29Old : Word) (srcBytes dstBytes : List (BitVec 8))
    (si di n : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hdalign : dstBase.toNat % 8 = 0)
    (hslen : si + n ≤ srcBytes.length) (hdlen : di + n ≤ dstBytes.length)
    (hsover : srcBase.toNat + (si + n) ≤ 2 ^ 64) (hdover : dstBase.toNat + (di + n) ≤ 2 ^ 64)
    (hn : n < 2 ^ 64)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcBase + BitVec.ofNat 64 (si + k)) = true)
    (hdvalid : ∀ k, k < n → isValidByteAccess (dstBase + BitVec.ofNat 64 (di + k)) = true) :
    cpsTripleWithin (7 * n + 1) (base + 40) (base + 68) (rlp_content_to_u256_be_code base)
      ((.x28 ↦ᵣ BitVec.ofNat 64 n) ** (.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       (.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 di)) ** (.x29 ↦ᵣ x29Old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      ((.x28 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + n))) **
       (.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (di + n))) ** regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase (copyN dstBytes srcBytes di si n)) := by
  have hmono : ∀ a i, CodeReq.singleton (base + 40) (.BEQ .x28 .x0 (28 : BitVec 13)) a = some i
      → rlp_content_to_u256_be_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u256_be_prog 10 (base + 40)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num) (by rfl))
  have ha_t : (base + 40) + signExtend13 (28 : BitVec 13) = base + 68 := by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega
  have ha_f : (base + 40 : Word) + 4 = base + 44 := by bv_omega
  induction n generalizing si di dstBytes x29Old with
  | zero =>
    have hbeq := beq_spec_gen_within .x28 .x0 (28 : BitVec 13) (BitVec.ofNat 64 0) (0 : Word) (base + 40)
    rw [ha_t, ha_f] at hbeq
    have hbeq_framed := cpsBranchWithin_frameR
      ((.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) ** (.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 di)) **
       (.x29 ↦ᵣ x29Old) ** bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      (by pcFree) hbeq
    have hbeq_ext := cpsBranchWithin_extend_code hmono hbeq_framed
    have htaken := cpsBranchWithin_takenPath hbeq_ext (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 (by decide))
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) htaken
    · xperm_hyp hp
    · rw [show (0#64 : Word) = 0 from by decide] at hq
      simp only [Nat.add_zero, copyN_zero]
      have hq1 := sepConj_mono_left
        (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
      have hq2 := sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x29)))) h hq1
      xperm_hyp hq2
  | succ k ih =>
    -- beq x28 x0 28 NOT taken (counter = ofNat (k+1) ≠ 0); fall through to body.
    have hbeq := beq_spec_gen_within .x28 .x0 (28 : BitVec 13) (BitVec.ofNat 64 (k + 1)) (0 : Word) (base + 40)
    rw [ha_t, ha_f] at hbeq
    have hbeq_framed := cpsBranchWithin_frameR
      ((.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) ** (.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 di)) **
       (.x29 ↦ᵣ x29Old) ** bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      (by pcFree) hbeq
    have hbeq_ext := cpsBranchWithin_extend_code hmono hbeq_framed
    have hne : BitVec.ofNat 64 (k + 1) ≠ (0 : Word) := word_ofNat_succ_ne_zero k (by omega)
    have hA1 := cpsBranchWithin_ntakenPath hbeq_ext (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact hne ((sepConj_pure_right _).1 h_pure).2)
    have hA1' : cpsTripleWithin 1 (base + 40) (base + 44) (rlp_content_to_u256_be_code base)
        (((.x28 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word))) **
          ((.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) ** (.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 di)) **
           (.x29 ↦ᵣ x29Old) ** bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes))
        ((.x29 ↦ᵣ x29Old) ** (.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
         (.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 di)) ** (.x28 ↦ᵣ BitVec.ofNat 64 (k + 1)) **
         bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes ** (.x0 ↦ᵣ (0 : Word))) :=
      cpsTripleWithin_weaken (fun _ hp => hp)
        (fun h hq => by
          have hq1 := sepConj_mono_left
            (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
          xperm_hyp hq1) hA1
    -- body (idx 11..15): copy one byte, advance, decrement counter (→ ofNat k).
    have hsi0 : si < srcBytes.length := by omega
    have hdi0 : di < dstBytes.length := by omega
    have body := cu256_copy_body_spec_within base srcBase dstBase x29Old (BitVec.ofNat 64 (k + 1))
      srcBytes dstBytes si di hsalign hdalign hsi0 hdi0 (by omega) (by omega)
      (hsvalid 0 (by omega)) (hdvalid 0 (by omega))
    rw [word_ofNat_succ_dec k] at body
    have body_x0 := cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word))) (by pcFree) body
    -- jal back-edge (idx 16): base+64 → base+40.
    have hjal := jal_x0_spec_gen_within (-24 : BitVec 21) (base + 64)
    have ha_back : (base + 64) + signExtend21 (-24 : BitVec 21) = base + 40 := by
      rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]; bv_omega
    rw [ha_back] at hjal
    have hjal_mono : ∀ a i, CodeReq.singleton (base + 64) (.JAL .x0 (-24 : BitVec 21)) a = some i
        → rlp_content_to_u256_be_code base a = some i :=
      CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u256_be_prog 16 (base + 64)
        (by rw [rlp_content_to_u256_be_prog_length]; norm_num)
        (by rw [rlp_content_to_u256_be_prog_length]; norm_num) (by rfl))
    have hjal_ext := cpsTripleWithin_extend_code hjal_mono hjal
    -- the loop state carried across the back-edge (= ih's precondition).
    have hjal_S : cpsTripleWithin 1 (base + 64) (base + 40) (rlp_content_to_u256_be_code base)
        ((.x29 ↦ᵣ (srcBytes[si]'hsi0).zeroExtend 64) **
         (.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         (.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (di + 1))) ** (.x28 ↦ᵣ BitVec.ofNat 64 k) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes **
         bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsi0)))
        ((.x29 ↦ᵣ (srcBytes[si]'hsi0).zeroExtend 64) **
         (.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         (.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (di + 1))) ** (.x28 ↦ᵣ BitVec.ofNat 64 k) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes **
         bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsi0))) :=
      cpsTripleWithin_weaken
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (cpsTripleWithin_frameR
          ((.x29 ↦ᵣ (srcBytes[si]'hsi0).zeroExtend 64) **
           (.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
           (.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (di + 1))) ** (.x28 ↦ᵣ BitVec.ofNat 64 k) **
           (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes **
           bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsi0)))
          (by pcFree) hjal_ext)
    -- ih for the remaining k bytes.
    have hsvalid' : ∀ j, j < k → isValidByteAccess (srcBase + BitVec.ofNat 64 ((si + 1) + j)) = true := by
      intro j hj
      have h := hsvalid (j + 1) (by omega)
      rwa [show si + (j + 1) = (si + 1) + j from by omega] at h
    have hdvalid' : ∀ j, j < k → isValidByteAccess (dstBase + BitVec.ofNat 64 ((di + 1) + j)) = true := by
      intro j hj
      have h := hdvalid (j + 1) (by omega)
      rwa [show di + (j + 1) = (di + 1) + j from by omega] at h
    have ihspec := ih ((srcBytes[si]'hsi0).zeroExtend 64) (dstBytes.set di (srcBytes[si]'hsi0))
      (si + 1) (di + 1) (by omega) (by rw [List.length_set]; omega) (by omega)
      (by rw [show (di + 1) + k = di + (k + 1) from by omega]; omega) (by omega) hsvalid' hdvalid'
    -- compose: beq ⨾ body ⨾ jal ⨾ ih.
    have s12 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA1' body_x0
    have s123 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s12 hjal_S
    have s1234 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s123 ihspec
    have hbyte : (srcBytes[si]'hsi0) = getByteAt srcBytes si := by simp [getByteAt, hsi0]
    rw [show 7 * (k + 1) + 1 = 1 + 5 + 1 + (7 * k + 1) from by ring,
        show si + (k + 1) = (si + 1) + k from by omega,
        show di + (k + 1) = (di + 1) + k from by omega,
        show copyN dstBytes srcBytes di si (k + 1)
           = copyN (dstBytes.set di (srcBytes[si]'hsi0)) srcBytes (di + 1) (si + 1) k from by
          rw [copyN_succ, ← hbyte]]
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) s1234

/-- `(32 : Word) - ofNat len = ofNat (32 - len)` for `len ≤ 32` (right-align offset). -/
private theorem word_32_sub_ofNat (len : Nat) (hlen : len ≤ 32) :
    (32 : Word) - BitVec.ofNat 64 len = BitVec.ofNat 64 (32 - len) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show BitVec.toNat (32 : Word) = 32 from by decide]
  omega

/--
**`rlp_content_to_u256_be` — success path (`len ≤ 32`).**

The content (`len` bytes at `a0 = srcBase + srcOff`, modeled as offset `srcOff`
into the dword-aligned input region `bytesRegion srcBase srcBytes`) is
right-aligned into the 32-byte output buffer at `a2 = outPtr`: the result is
`copyN (replicate 32 0) srcBytes (32-len) srcOff len`, i.e. `(32-len)` zero
bytes followed by the `len` content bytes (the big-endian `u256`). Returns
`a0 = 0`. The scratch registers `t0..t4` are clobbered (`regOwn`); `a1`/`a2`/`ra`
are preserved; the routine returns to `ra &&& ~~~1`.
-/
theorem rlp_content_to_u256_be_success_spec_within
    (base srcBase outPtr raVal x5Old x6Old x7Old x28Old x29Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat)
    (hlen : len ≤ 32)
    (hsalign : srcBase.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64) (hoover : outPtr.toNat + 32 ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hdvalid : ∀ k, k < len → isValidByteAccess (outPtr + BitVec.ofNat 64 ((32 - len) + k)) = true) :
    cpsTripleWithin (7 * len + 13) base (raVal &&& ~~~1) (rlp_content_to_u256_be_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
       (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
       bytesRegion srcBase srcBytes ** memOwnU256 outPtr)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ outPtr) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
       (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes **
       bytesRegion outPtr (copyN (List.replicate 32 (0 : BitVec 8)) srcBytes (32 - len) srcOff len)) := by
  -- Phase A (idx 0..4): zero the output, load 32 into t0.  base → base+20.
  have hSD0 := sd_spec_gen_own_within .x12 .x0 outPtr (0 : Word) (0 : BitVec 12) base
  have hSD1 := sd_spec_gen_own_within .x12 .x0 outPtr (0 : Word) (8 : BitVec 12) (base + 4)
  have hSD2 := sd_spec_gen_own_within .x12 .x0 outPtr (0 : Word) (16 : BitVec 12) (base + 8)
  have hSD3 := sd_spec_gen_own_within .x12 .x0 outPtr (0 : Word) (24 : BitVec 12) (base + 12)
  have hLI := li_spec_gen_within .x5 x5Old (32 : Word) (base + 16) (by decide)
  simp only [signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24] at hSD0 hSD1 hSD2 hSD3
  have hPA0 : cpsTripleWithin 5 base (base + 20) (rlp_content_to_u256_be_code base)
      ((.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ x5Old) **
       memOwn outPtr ** memOwn (outPtr + 8) ** memOwn (outPtr + 16) ** memOwn (outPtr + 24))
      ((.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (32 : Word)) **
       bytesRegion outPtr (List.replicate 32 (0 : BitVec 8))) := by
    rw [bytesRegion_replicate32_zero]
    runBlock hSD0 hSD1 hSD2 hSD3 hLI
  have hPA := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
     (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) ** (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) **
     (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
    (by pcFree) hPA0
  -- Phase B' (idx 5): BLTU x5 x11 NOT taken (len ≤ 32).  base+20 → base+24.
  have hbltu := bltu_spec_gen_within .x5 .x11 (56 : BitVec 13) (32 : Word) (BitVec.ofNat 64 len) (base + 20)
  have hbB_t : (base + 20) + signExtend13 (56 : BitVec 13) = base + 76 := by
    rw [show signExtend13 (56 : BitVec 13) = (56 : Word) from by decide]; bv_omega
  have hbB_f : (base + 20 : Word) + 4 = base + 24 := by bv_omega
  rw [hbB_t, hbB_f] at hbltu
  have hnlt : ¬ BitVec.ult (32 : Word) (BitVec.ofNat 64 len) := by
    rw [BitVec.ult]
    simp only [BitVec.toNat_ofNat, show BitVec.toNat (32 : Word) = 32 from by decide,
      Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega)]
    omega
  have hbltu_framed := cpsBranchWithin_frameR
    ((.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
     (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) ** (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) **
     (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes **
     bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)))
    (by pcFree) hbltu
  have hmonoB : ∀ a i, CodeReq.singleton (base + 20) (.BLTU .x5 .x11 (56 : BitVec 13)) a = some i
      → rlp_content_to_u256_be_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u256_be_prog 5 (base + 20)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num) (by rfl))
  have hbltu_ext := cpsBranchWithin_extend_code hmonoB hbltu_framed
  have hPB := cpsBranchWithin_ntakenPath hbltu_ext (fun hp hQt => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
    exact hnlt ((sepConj_pure_right _).1 h_pure).2)
  -- Phase D (idx 6..9): t0=32-len, t1=outPtr+(32-len), t2=src, t3=len.  base+24 → base+40.
  have hsub := sub_spec_gen_rd_eq_rs1_within .x5 .x11 (32 : Word) (BitVec.ofNat 64 len) (base + 24) (by decide)
  rw [word_32_sub_ofNat len hlen] at hsub
  have hadd := add_spec_gen_within .x6 .x12 .x5 outPtr (BitVec.ofNat 64 (32 - len)) x6Old (base + 28) (by decide)
  have hmv7 := mv_spec_gen_within .x7 .x10 (srcBase + BitVec.ofNat 64 srcOff) x7Old (base + 32) (by decide)
  have hmv28 := mv_spec_gen_within .x28 .x11 (BitVec.ofNat 64 len) x28Old (base + 36) (by decide)
  have hPD : cpsTripleWithin 4 (base + 24) (base + 40) (rlp_content_to_u256_be_code base)
      ((.x5 ↦ᵣ (32 : Word)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ outPtr) **
       (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       (.x28 ↦ᵣ x28Old))
      ((.x5 ↦ᵣ BitVec.ofNat 64 (32 - len)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ outPtr) **
       (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
       (.x6 ↦ᵣ (outPtr + BitVec.ofNat 64 (32 - len))) **
       (.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x28 ↦ᵣ BitVec.ofNat 64 len)) := by
    runBlock hsub hadd hmv7 hmv28
  have hPD' := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ x29Old) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes **
     bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)))
    (by pcFree) hPD
  -- Loop (idx 10..16): copy len bytes right-aligned.  base+40 → base+68.
  have hloop := cu256_loop_spec_within base srcBase outPtr x29Old srcBytes
    (List.replicate 32 (0 : BitVec 8)) srcOff (32 - len) len hsalign hoalign hslen
    (by rw [List.length_replicate]; omega) hsover (by rw [show (32 - len) + len = 32 from by omega]; exact hoover)
    (by omega) hsvalid hdvalid
  have hloop' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ BitVec.ofNat 64 (32 - len)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
     (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal))
    (by pcFree) hloop
  -- Phase E (idx 17..18): a0 = 0 ; ret.  base+68 → ra &&& ~~~1.
  have hLI0 := li_spec_gen_within .x10 (srcBase + BitVec.ofNat 64 srcOff) (0 : Word) (base + 68) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 80)
  simp only [signExtend12_0] at hRet
  have hPE : cpsTripleWithin 2 (base + 68) (raVal &&& ~~~1) (rlp_content_to_u256_be_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x1 ↦ᵣ raVal))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hLI0 hRet
  have hPE' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ outPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     (.x28 ↦ᵣ (0 : Word)) ** regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes **
     bytesRegion outPtr (copyN (List.replicate 32 (0 : BitVec 8)) srcBytes (32 - len) srcOff len))
    (by pcFree) hPE
  -- Compose A ⨾ B' ⨾ D ⨾ loop ⨾ E.
  have sAB := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hPA hPB
  have sABD := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) sAB hPD'
  have sABDL := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) sABD hloop'
  have sFull := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) sABDL hPE'
  rw [show 7 * len + 13 = 5 + 1 + 4 + (7 * len + 1) + 2 from by ring]
  exact cpsTripleWithin_weaken
    (fun h hp => by simp only [memOwnU256] at hp; xperm_hyp hp)
    (fun h hp => by xperm_hyp hp) sFull

-- Sanity: program length and the entry / branch-target instruction lookups the
-- failure-path proof relies on.
example : rlp_content_to_u256_be_prog.length = 21 := rfl
example : (CodeReq.ofProg (0 : Word) rlp_content_to_u256_be_prog) 0 = some (.SD .x12 .x0 0) := by decide
example : (CodeReq.ofProg (0 : Word) rlp_content_to_u256_be_prog) 20 =
    some (.BLTU .x5 .x11 (56 : BitVec 13)) := by decide
example : (CodeReq.ofProg (0 : Word) rlp_content_to_u256_be_prog) 76 =
    some (.LI .x10 (2 : Word)) := by decide

end EvmAsm.Rv64.RLP
