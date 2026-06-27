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

  This routine is **canonical-strict**: it enforces the RLP scalar canonicality
  rule (execution-specs `_deserialize_to_uint`), so it rejects leading-zero
  encodings rather than silently right-aligning them like the current guest.

  ### Outputs (where they are located)
  * `a0` (`x10`) — **status**:
      - `0` — success (canonical: `len = 0`, or `len ≤ 32 ∧ content[0] ≠ 0`);
      - `2` — `content` too long (`len > 32`, cannot fit a `u256`);
      - `3` — **non-canonical** (`len > 0 ∧ content[0] = 0`; a nonzero scalar
        whose high byte is zero — `0` must be the empty string).
  * The 32 bytes at `a2` hold, **on success**, the big-endian `u256` whose low
    `len` bytes are `content` (right-aligned, high bytes zero). `len = 0` decodes
    to the canonical `0`.

  ### What happens to the output memory region
  * On **success** the output region holds the decoded value.
  * On **failure** (`status 2` or `3`) the routine returns nonzero and the
    32-byte output region may hold **arbitrary content** — callers must not read
    it. (This implementation in fact zeroes the buffer up front, so the bytes are
    all `0`; the *contract* deliberately under-specifies them so any conforming
    implementation is a valid drop-in and callers never depend on the zero-fill.
    Expressed below as `memOwnU256`: the caller still owns a writable 32-byte
    region at `a2`, but its contents are unconstrained.)

  ## Verification status

  Lays out the faithful 26-instruction canonical-strict drop-in body
  `rlp_content_to_u256_be_prog`. Both **failure paths** are proved as complete
  leaf-function Hoare triples: the **content-too-long** path (`len > 32`,
  status 2, `rlp_content_to_u256_be_too_long_spec_within`) and the
  **non-canonical** path (`0 < len ≤ 32 ∧ content[0] = 0`, status 3,
  `rlp_content_to_u256_be_noncanonical_spec_within`). Follow-ups: the success
  copy-loop (`len ≤ 32`, canonical) and the unified 3-way theorem covering all
  outcomes. (The success copy-loop induction proven on the earlier lenient
  layout is preserved in git for the re-offset redo.)
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
The faithful verified **canonical-strict** drop-in body for the codegen guest
`rlp_content_to_u256_be` (26 instructions). Register map: `a0=x10`, `a1=x11`,
`a2=x12`, `t0=x5`, `t1=x6`, `t2=x7`, `t3=x28`, `t4=x29`, `ra=x1`.

Beyond the right-aligned copy, this body enforces the RLP **scalar canonicality**
rule (execution-specs `_deserialize_to_uint`): the empty string is the canonical
`0`, but a nonzero value's high (first) byte must be nonzero — a `len > 0` content
with `content[0] = 0` is **non-canonical** and rejected with status `3`.

```
   0  SD   x12 x0 0      ; zero out[0..7]
   1  SD   x12 x0 8      ; zero out[8..15]
   2  SD   x12 x0 16     ; zero out[16..23]
   3  SD   x12 x0 24     ; zero out[24..31]
   4  LI   x5  32        ; t0 = 32
   5  BLTU x5  x11 76    ; if 32 < len goto too_long (idx 24, +76 bytes)
   6  BEQ  x11 x0 56     ; if len == 0 goto done  (canonical 0; idx 20, +56 bytes)
   7  LBU  x6  x10 0     ; t1 = content[0] (high byte)
   8  BEQ  x6  x0 56     ; if high byte == 0 goto noncanon (idx 22, +56 bytes)
   9  SUB  x5  x5  x11   ; t0 = 32 - len
  10  ADD  x6  x12 x5    ; t1 = a2 + (32 - len)   right-aligned dst
  11  MV   x7  x10       ; t2 = src
  12  MV   x28 x11       ; t3 = remaining
  13  BEQ  x28 x0 28     ; copy loop: if remaining==0 goto done (idx 20, +28)
  14  LBU  x29 x7 0      ; t4 = src[k]
  15  SB   x6  x29 0     ; dst[k] = t4
  16  ADDI x7  x7 1
  17  ADDI x6  x6 1
  18  ADDI x28 x28 (-1)
  19  JAL  x0 (-24)      ; goto copy loop (idx 13, -24 bytes)
  20  LI   x10 0         ; done: a0 = 0 (ok)
  21  JALR x0 x1 0       ; ret
  22  LI   x10 3         ; noncanon: a0 = 3
  23  JALR x0 x1 0       ; ret
  24  LI   x10 2         ; too_long: a0 = 2
  25  JALR x0 x1 0       ; ret
```
-/
def rlp_content_to_u256_be_prog : List Instr :=
  [ .SD .x12 .x0 0,           -- 0
    .SD .x12 .x0 8,           -- 1
    .SD .x12 .x0 16,          -- 2
    .SD .x12 .x0 24,          -- 3
    .LI .x5 (32 : Word),      -- 4
    .BLTU .x5 .x11 (76 : BitVec 13),   -- 5
    .BEQ .x11 .x0 (56 : BitVec 13),    -- 6
    .LBU .x6 .x10 0,          -- 7
    .BEQ .x6 .x0 (56 : BitVec 13),     -- 8
    .SUB .x5 .x5 .x11,        -- 9
    .ADD .x6 .x12 .x5,        -- 10
    .MV .x7 .x10,             -- 11
    .MV .x28 .x11,            -- 12
    .BEQ .x28 .x0 (28 : BitVec 13),    -- 13
    .LBU .x29 .x7 0,          -- 14
    .SB .x6 .x29 0,           -- 15
    .ADDI .x7 .x7 (1 : BitVec 12),     -- 16
    .ADDI .x6 .x6 (1 : BitVec 12),     -- 17
    .ADDI .x28 .x28 (-1 : BitVec 12),  -- 18
    .JAL .x0 (-24 : BitVec 21),        -- 19
    .LI .x10 (0 : Word),      -- 20
    .JALR .x0 .x1 0,          -- 21
    .LI .x10 (3 : Word),      -- 22
    .JALR .x0 .x1 0,          -- 23
    .LI .x10 (2 : Word),      -- 24
    .JALR .x0 .x1 0 ]         -- 25

theorem rlp_content_to_u256_be_prog_length :
    rlp_content_to_u256_be_prog.length = 26 := rfl

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
  -- Phase B: BLTU x5 x11 76 at base+20; taken since 32 <ᵤ len (idx 5), base+20 → base+96.
  have hBr_raw := bltu_spec_gen_within .x5 .x11 (76 : BitVec 13) (32 : Word) len (base + 20)
  have ha_t : (base + 20) + signExtend13 (76 : BitVec 13) = base + 96 := by
    rw [show signExtend13 (76 : BitVec 13) = (76 : Word) from by decide]; bv_omega
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
  -- Phase C: LI x10 2 ; ret  (idx 24, 25), base+96 → ra &&& ~~~1.
  have hLI2 := li_spec_gen_within .x10 contentPtr (2 : Word) (base + 96) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 100)
  simp only [signExtend12_0] at hRet
  have hC : cpsTripleWithin 2 (base + 96) (raVal &&& ~~~1) (rlp_content_to_u256_be_code base)
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

/--
**`rlp_content_to_u256_be` — non-canonical failure path.**

A nonzero-length content whose high (first) byte is zero is a **non-canonical**
scalar encoding (execution-specs `_deserialize_to_uint`: `len(decoded) > 0 ∧
decoded[0] == 0`). The routine detects this (idx 7 `LBU`, idx 8 `BEQ`) and
returns status `a0 = 3`, leaving the 32-byte output buffer owned by the caller
with **arbitrary content** (`memOwnU256 outPtr`).

`content` is modeled as offset `srcOff` into the dword-aligned input region
`bytesRegion srcBase srcBytes` (so `a0 = srcBase + srcOff` and
`content[0] = srcBytes[srcOff]`); the precondition is
`0 < len ≤ 32 ∧ srcBytes[srcOff] = 0`. Scratch `t0`/`t1` are clobbered
(`regOwn`); `a1`/`a2`/`ra` and the input region are preserved.

The 11-step path (`SD×4 ⨾ LI ⨾ BLTU(¬taken) ⨾ BEQ(¬taken) ⨾ LBU ⨾ BEQ(taken) ⨾
LI ⨾ ret`) is loop-free; its proof reuses the too-long Phase-A + the
branch-extraction idioms (`cpsBranchWithin_{n,}takenPath`) and
`bytesRegion_lbu_within` for the high-byte read.
-/
theorem rlp_content_to_u256_be_noncanonical_spec_within
    (base srcBase outPtr raVal t0Old t1Old : Word) (srcBytes : List (BitVec 8)) (srcOff len : Nat)
    (hlen0 : 0 < len) (hlen32 : len ≤ 32)
    (hsalign : srcBase.toNat % 8 = 0) (hsoff : srcOff < srcBytes.length)
    (hsover : srcBase.toNat + srcOff < 2 ^ 64)
    (hsvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hnoncanon : srcBytes[srcOff]'hsoff = 0) :
    cpsTripleWithin 11 base (raVal &&& ~~~1) (rlp_content_to_u256_be_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes ** memOwnU256 outPtr)
      ((.x10 ↦ᵣ (3 : Word)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ outPtr) **
        regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes ** memOwnU256 outPtr) := by
  have hnlt : ¬ (BitVec.ult (32 : Word) (BitVec.ofNat 64 len) = true) := by
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
      show BitVec.toNat (32 : Word) = 32 from by decide,
      Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega)]
    omega
  have hlen_ne : (BitVec.ofNat 64 len : Word) ≠ 0 := by
    intro hc
    have h0 : (BitVec.ofNat 64 len : Word).toNat = 0 := by rw [hc]; rfl
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega)] at h0
    omega
  have hbyte0 : (srcBytes[srcOff]'hsoff).zeroExtend 64 = (0 : Word) := by rw [hnoncanon]; decide
  -- Phase A: zero the output and load 32 into t0 (idx 0..4), base → base + 20.
  have hSD0 := sd_spec_gen_own_within .x12 .x0 outPtr (0 : Word) (0 : BitVec 12) base
  have hSD1 := sd_spec_gen_own_within .x12 .x0 outPtr (0 : Word) (8 : BitVec 12) (base + 4)
  have hSD2 := sd_spec_gen_own_within .x12 .x0 outPtr (0 : Word) (16 : BitVec 12) (base + 8)
  have hSD3 := sd_spec_gen_own_within .x12 .x0 outPtr (0 : Word) (24 : BitVec 12) (base + 12)
  have hLI := li_spec_gen_within .x5 t0Old (32 : Word) (base + 16) (by decide)
  simp only [signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24] at hSD0 hSD1 hSD2 hSD3
  have hA : cpsTripleWithin 5 base (base + 20) (rlp_content_to_u256_be_code base)
      ((.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ t0Old) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ t1Old) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes **
        memOwn outPtr ** memOwn (outPtr + 8) ** memOwn (outPtr + 16) ** memOwn (outPtr + 24))
      ((.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (32 : Word)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ t1Old) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes **
        (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) **
        ((outPtr + 16) ↦ₘ (0 : Word)) ** ((outPtr + 24) ↦ₘ (0 : Word))) := by
    runBlock hSD0 hSD1 hSD2 hSD3 hLI
  -- the output cells (zeroed) + framed registers, carried through every branch below.
  let OUT : Assertion := (outPtr ↦ₘ (0 : Word)) ** ((outPtr + 8) ↦ₘ (0 : Word)) **
    ((outPtr + 16) ↦ₘ (0 : Word)) ** ((outPtr + 24) ↦ₘ (0 : Word))
  -- Phase B1: BLTU x5 x11 76 at base+20, NOT taken since len ≤ 32 (idx 5), base+20 → base+24.
  have hbl := bltu_spec_gen_within .x5 .x11 (76 : BitVec 13) (32 : Word) (BitVec.ofNat 64 len) (base + 20)
  have ha_t5 : (base + 20) + signExtend13 (76 : BitVec 13) = base + 96 := by
    rw [show signExtend13 (76 : BitVec 13) = (76 : Word) from by decide]; bv_omega
  have ha_f5 : (base + 20 : Word) + 4 = base + 24 := by bv_omega
  rw [ha_t5, ha_f5] at hbl
  have hmono5 : ∀ a i, CodeReq.singleton (base + 20) (.BLTU .x5 .x11 (76 : BitVec 13)) a = some i
      → rlp_content_to_u256_be_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u256_be_prog 5 (base + 20)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num) (by rfl))
  have hBL := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono5 (cpsBranchWithin_frameR
      ((.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x6 ↦ᵣ t1Old) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes ** OUT)
      (by pcFree) hbl))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact hnlt ((sepConj_pure_right _).1 h_pure).2)
  -- Phase B2: BEQ x11 x0 56 at base+24, NOT taken since len > 0 (idx 6), base+24 → base+28.
  have hbe := beq_spec_gen_within .x11 .x0 (56 : BitVec 13) (BitVec.ofNat 64 len) (0 : Word) (base + 24)
  have ha_f6 : (base + 24 : Word) + 4 = base + 28 := by bv_omega
  have ha_t6 : (base + 24) + signExtend13 (56 : BitVec 13) = base + 80 := by
    rw [show signExtend13 (56 : BitVec 13) = (56 : Word) from by decide]; bv_omega
  rw [ha_t6, ha_f6] at hbe
  have hmono6 : ∀ a i, CodeReq.singleton (base + 24) (.BEQ .x11 .x0 (56 : BitVec 13)) a = some i
      → rlp_content_to_u256_be_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u256_be_prog 6 (base + 24)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num) (by rfl))
  have hBE := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono6 (cpsBranchWithin_frameR
      ((.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (32 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x6 ↦ᵣ t1Old) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes ** OUT)
      (by pcFree) hbe))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact hlen_ne ((sepConj_pure_right _).1 h_pure).2)
  -- Phase C: LBU x6 x10 0 at base+28 (idx 7): x6 := content[0] = srcBytes[srcOff], base+28 → base+32.
  have hlbu := bytesRegion_lbu_within .x6 .x10 srcBase t1Old (base + 28) srcBytes srcOff
    (by decide) hsalign hsoff hsover hsvalid
  rw [show (base + 28 : Word) + 4 = base + 32 from by bv_omega, hbyte0] at hlbu
  have hmono7 : ∀ a i, CodeReq.singleton (base + 28) (.LBU .x6 .x10 0) a = some i
      → rlp_content_to_u256_be_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u256_be_prog 7 (base + 28)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num) (by rfl))
  have hLBU := cpsTripleWithin_extend_code hmono7 (cpsTripleWithin_frameR
    ((.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (32 : Word)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
      (.x1 ↦ᵣ raVal) ** OUT)
    (by pcFree) hlbu)
  -- Phase D: BEQ x6 x0 56 at base+32, TAKEN since content[0] = 0 (idx 8), base+32 → base+88 (noncanon).
  have hbe2 := beq_spec_gen_within .x6 .x0 (56 : BitVec 13)
    ((srcBytes[srcOff]'hsoff).zeroExtend 64) (0 : Word) (base + 32)
  rw [hbyte0] at hbe2
  have ha_t8 : (base + 32) + signExtend13 (56 : BitVec 13) = base + 88 := by
    rw [show signExtend13 (56 : BitVec 13) = (56 : Word) from by decide]; bv_omega
  have ha_f8 : (base + 32 : Word) + 4 = base + 36 := by bv_omega
  rw [ha_t8, ha_f8] at hbe2
  have hmono8 : ∀ a i, CodeReq.singleton (base + 32) (.BEQ .x6 .x0 (56 : BitVec 13)) a = some i
      → rlp_content_to_u256_be_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u256_be_prog 8 (base + 32)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num) (by rfl))
  have hBE2 := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono8 (cpsBranchWithin_frameR
      ((.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (32 : Word)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes ** OUT)
      (by pcFree) hbe2))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 rfl)
  -- Phase E: LI x10 3 ; ret (idx 22, 23), base+88 → ra &&& ~~~1.
  have hLI3 := li_spec_gen_within .x10 (srcBase + BitVec.ofNat 64 srcOff) (3 : Word) (base + 88) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 92)
  simp only [signExtend12_0] at hRet
  have hE : cpsTripleWithin 2 (base + 88) (raVal &&& ~~~1) (rlp_content_to_u256_be_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x1 ↦ᵣ raVal))
      ((.x10 ↦ᵣ (3 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hLI3 hRet
  have hE' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (32 : Word)) **
      (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes ** OUT)
    (by pcFree) hE
  -- Compose A ⨾ B1 ⨾ B2 ⨾ C ⨾ D ⨾ E.
  -- bridge that drops a true `⌜p⌝` carried by a branch path, then permutes.
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA hBL
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s1 hBE
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s2 hLBU
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 hBE2
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s4 hE'
  rw [show (5 + 1 + 1 + 1 + 1 + 2) = 11 from rfl] at s5
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_) s5
  · simp only [memOwnU256] at hp; xperm_hyp hp
  · simp only [memOwnU256]
    have OUT_own : ∀ h, OUT h →
        (memOwn outPtr ** memOwn (outPtr + 8) ** memOwn (outPtr + 16) ** memOwn (outPtr + 24)) h :=
      sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn))
    have hp' := sepConj_mono_right
      (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
          (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) OUT_own))))))
      h hp
    xperm_hyp hp'

-- Sanity: program length and the failure-path instruction lookups.
example : rlp_content_to_u256_be_prog.length = 26 := rfl
example : (CodeReq.ofProg (0 : Word) rlp_content_to_u256_be_prog) 20 =
    some (.BLTU .x5 .x11 (76 : BitVec 13)) := by decide
example : (CodeReq.ofProg (0 : Word) rlp_content_to_u256_be_prog) 32 =
    some (.BEQ .x6 .x0 (56 : BitVec 13)) := by decide
example : (CodeReq.ofProg (0 : Word) rlp_content_to_u256_be_prog) 88 =
    some (.LI .x10 (3 : Word)) := by decide
example : (CodeReq.ofProg (0 : Word) rlp_content_to_u256_be_prog) 96 =
    some (.LI .x10 (2 : Word)) := by decide

end EvmAsm.Rv64.RLP
