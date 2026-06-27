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
    depend on the zero-fill. This is expressed below with `memOwn`: the caller
    still owns a writable 32-byte region at `a2`, but its contents are
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
def u256OutRegion (outPtr : Word) : Assertion :=
  memOwn outPtr ** memOwn (outPtr + 8) ** memOwn (outPtr + 16) ** memOwn (outPtr + 24)

/--
**`rlp_content_to_u256_be` — content-too-long failure path.**

When the requested content length exceeds 32 bytes (`32 <ᵤ len`), the routine
returns status `a0 = 2` and leaves the 32-byte output buffer at `a2` owned by
the caller but with **arbitrary content** (`u256OutRegion outPtr` in the post).

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
        u256OutRegion outPtr)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x11 ↦ᵣ len) ** (.x12 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ (32 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        u256OutRegion outPtr) := by
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
  · simp only [u256OutRegion] at hp
    xperm_hyp hp
  · simp only [u256OutRegion]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn
              (fun h' hp' => memIs_implies_memOwn _ ((sepConj_pure_right h').1 hp').1))))))))) h hq

-- Sanity: program length and the entry / branch-target instruction lookups the
-- failure-path proof relies on.
example : rlp_content_to_u256_be_prog.length = 21 := rfl
example : (CodeReq.ofProg (0 : Word) rlp_content_to_u256_be_prog) 0 = some (.SD .x12 .x0 0) := by decide
example : (CodeReq.ofProg (0 : Word) rlp_content_to_u256_be_prog) 20 =
    some (.BLTU .x5 .x11 (56 : BitVec 13)) := by decide
example : (CodeReq.ofProg (0 : Word) rlp_content_to_u256_be_prog) 76 =
    some (.LI .x10 (2 : Word)) := by decide

end EvmAsm.Rv64.RLP
