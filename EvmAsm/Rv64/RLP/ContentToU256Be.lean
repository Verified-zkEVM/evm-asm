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
  `rlp_content_to_u256_be_prog`. **All four behavioral cases** are proved as
  complete leaf-function Hoare triples:
    * `…_too_long_spec_within` — `len > 32`, status 2;
    * `…_noncanonical_spec_within` — `0 < len ≤ 32 ∧ content[0] = 0`, status 3;
    * `…_empty_spec_within` — `len = 0` (canonical zero), status 0, output `0`;
    * `…_success_spec_within` — `0 < len ≤ 32 ∧ content[0] ≠ 0`, status 0, output
      the right-aligned big-endian `u256`.
  The unified dispatch theorem `…_spec_within` combines all four: static
  preconditions only, a single `cpsTripleWithin (7*len+16)` (upper bound via
  `cpsTripleWithin_mono_nSteps`), and the outcome stated as a four-way
  postcondition disjunction (per the `AGENTS.md` spec-design convention).
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

/-! ## Success path (`len ≤ 32`, canonical): the right-aligned copy loop -/

set_option maxRecDepth 8000 in
/-- One copy iteration (idx 14..18, `base+56 → base+76`): read `src[si]`, write it
    to `dst[di]`, advance both pointers, decrement the counter. -/
theorem cu256_copy_body_spec_within
    (base srcBase dstBase x29Old x28Val : Word)
    (srcBytes dstBytes : List (BitVec 8)) (si di : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hdalign : dstBase.toNat % 8 = 0)
    (hsi : si < srcBytes.length) (hdi : di < dstBytes.length)
    (hsover : srcBase.toNat + si < 2 ^ 64) (hdover : dstBase.toNat + di < 2 ^ 64)
    (hsvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 si) = true)
    (hdvalid : isValidByteAccess (dstBase + BitVec.ofNat 64 di) = true) :
    cpsTripleWithin 5 (base + 56) (base + 76) (rlp_content_to_u256_be_code base)
      ((.x29 ↦ᵣ x29Old) ** (.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       (.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 di)) ** (.x28 ↦ᵣ x28Val) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      ((.x29 ↦ᵣ (srcBytes[si]'hsi).zeroExtend 64) **
       (.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
       (.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (di + 1))) **
       (.x28 ↦ᵣ (x28Val + signExtend12 (-1 : BitVec 12))) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsi))) := by
  have lbu := bytesRegion_lbu_within .x29 .x7 srcBase x29Old (base + 56) srcBytes si
    (by decide) hsalign hsi hsover hsvalid
  have sb := bytesRegion_sb_within .x6 .x29 dstBase ((srcBytes[si]'hsi).zeroExtend 64)
    (base + 60) dstBytes di hdalign hdi hdover hdvalid
  rw [show ((srcBytes[si]'hsi).zeroExtend 64).truncate 8 = srcBytes[si]'hsi from by simp] at sb
  have a7 := addi_spec_gen_same_within .x7 (srcBase + BitVec.ofNat 64 si) 1 (base + 64) (by nofun)
  rw [show (srcBase + BitVec.ofNat 64 si) + signExtend12 (1 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (si + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at a7
  have a6 := addi_spec_gen_same_within .x6 (dstBase + BitVec.ofNat 64 di) 1 (base + 68) (by nofun)
  rw [show (dstBase + BitVec.ofNat 64 di) + signExtend12 (1 : BitVec 12)
      = dstBase + BitVec.ofNat 64 (di + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at a6
  have a28 := addi_spec_gen_same_within .x28 x28Val (-1 : BitVec 12) (base + 72) (by nofun)
  runBlock lbu sb a7 a6 a28

/-- Result of `n` copy iterations: write `src[si+j]` into `dst[di+j]` for `j < n`. -/
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

/-- `copyN` splits: copying `n` in-range bytes overwrites exactly the window
    `[di, di + n)` of `dst` with `src[si, si + n)`.

    Lives here beside `copyN` rather than in a caller: both
    `Evm64/AccountAccessorSpec.lean` (u256 right-alignment) and
    `Codegen/Programs/RlpEncodeUintBeComposeSAsm.lean` (the RLP encoder's
    payload copy) need it, and neither should import the other. -/
theorem copyN_eq_append (dst src : List (BitVec 8)) (di si n : Nat)
    (hd : di + n ≤ dst.length) (hs : si + n ≤ src.length) :
    copyN dst src di si n
      = dst.take di ++ ((src.drop si).take n ++ dst.drop (di + n)) := by
  induction n generalizing dst di si with
  | zero =>
    rw [copyN_zero]
    simp
  | succ k ih =>
    have hdi : di < dst.length := by omega
    have hsi : si < src.length := by omega
    rw [copyN_succ,
      ih (dst.set di (getByteAt src si)) (di + 1) (si + 1)
        (by rw [List.length_set]; omega) (by omega)]
    have hb : getByteAt src si = src[si]'hsi := by simp [getByteAt, hsi]
    rw [hb, List.set_eq_take_cons_drop _ hdi]
    have hlt : (dst.take di).length = di := by rw [List.length_take]; omega
    -- take (di+1) of `take di ++ src[si] :: drop (di+1)` is `take di ++ [src[si]]`
    have hT1 : (dst.take di ++ src[si]'hsi :: dst.drop (di + 1)).take (di + 1)
        = dst.take di ++ [src[si]'hsi] := by
      rw [List.take_append, hlt, List.take_of_length_le (by rw [hlt]; omega),
        show di + 1 - di = 1 from by omega, List.take_succ_cons, List.take_zero]
    -- drop (di+1+k) of the same list is `dst.drop (di+1+k)`
    have hT3 : (dst.take di ++ src[si]'hsi :: dst.drop (di + 1)).drop (di + 1 + k)
        = dst.drop (di + 1 + k) := by
      rw [List.drop_append, hlt, List.drop_eq_nil_of_le (by rw [hlt]; omega),
        show di + 1 + k - di = k + 1 from by omega, List.drop_succ_cons,
        List.drop_drop, List.nil_append,
        show di + 1 + k = k + (di + 1) from by omega]
    rw [hT1, hT3]
    -- right-hand side: expose the head of the copied window
    rw [List.drop_eq_getElem_cons hsi, List.take_succ_cons,
      show di + (k + 1) = di + 1 + k from by omega]
    simp [List.append_assoc]

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

/-- **The copy loop (idx 13..19), `base+52 → base+80`, by induction on the counter.** -/
theorem cu256_loop_spec_within
    (base srcBase dstBase x29Old : Word) (srcBytes dstBytes : List (BitVec 8))
    (si di n : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hdalign : dstBase.toNat % 8 = 0)
    (hslen : si + n ≤ srcBytes.length) (hdlen : di + n ≤ dstBytes.length)
    (hsover : srcBase.toNat + (si + n) ≤ 2 ^ 64) (hdover : dstBase.toNat + (di + n) ≤ 2 ^ 64)
    (hn : n < 2 ^ 64)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcBase + BitVec.ofNat 64 (si + k)) = true)
    (hdvalid : ∀ k, k < n → isValidByteAccess (dstBase + BitVec.ofNat 64 (di + k)) = true) :
    cpsTripleWithin (7 * n + 1) (base + 52) (base + 80) (rlp_content_to_u256_be_code base)
      ((.x28 ↦ᵣ BitVec.ofNat 64 n) ** (.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       (.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 di)) ** (.x29 ↦ᵣ x29Old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      ((.x28 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + n))) **
       (.x6 ↦ᵣ (dstBase + BitVec.ofNat 64 (di + n))) ** regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase (copyN dstBytes srcBytes di si n)) := by
  have hmono : ∀ a i, CodeReq.singleton (base + 52) (.BEQ .x28 .x0 (28 : BitVec 13)) a = some i
      → rlp_content_to_u256_be_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u256_be_prog 13 (base + 52)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num) (by rfl))
  have ha_t : (base + 52) + signExtend13 (28 : BitVec 13) = base + 80 := by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega
  have ha_f : (base + 52 : Word) + 4 = base + 56 := by bv_omega
  induction n generalizing si di dstBytes x29Old with
  | zero =>
    have hbeq := beq_spec_gen_within .x28 .x0 (28 : BitVec 13) (BitVec.ofNat 64 0) (0 : Word) (base + 52)
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
    have hbeq := beq_spec_gen_within .x28 .x0 (28 : BitVec 13) (BitVec.ofNat 64 (k + 1)) (0 : Word) (base + 52)
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
    have hA1' : cpsTripleWithin 1 (base + 52) (base + 56) (rlp_content_to_u256_be_code base)
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
    have hsi0 : si < srcBytes.length := by omega
    have hdi0 : di < dstBytes.length := by omega
    have body := cu256_copy_body_spec_within base srcBase dstBase x29Old (BitVec.ofNat 64 (k + 1))
      srcBytes dstBytes si di hsalign hdalign hsi0 hdi0 (by omega) (by omega)
      (hsvalid 0 (by omega)) (hdvalid 0 (by omega))
    rw [word_ofNat_succ_dec k] at body
    have body_x0 := cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word))) (by pcFree) body
    have hjal := jal_x0_spec_gen_within (-24 : BitVec 21) (base + 76)
    have ha_back : (base + 76) + signExtend21 (-24 : BitVec 21) = base + 52 := by
      rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]; bv_omega
    rw [ha_back] at hjal
    have hjal_mono : ∀ a i, CodeReq.singleton (base + 76) (.JAL .x0 (-24 : BitVec 21)) a = some i
        → rlp_content_to_u256_be_code base a = some i :=
      CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u256_be_prog 19 (base + 76)
        (by rw [rlp_content_to_u256_be_prog_length]; norm_num)
        (by rw [rlp_content_to_u256_be_prog_length]; norm_num) (by rfl))
    have hjal_ext := cpsTripleWithin_extend_code hjal_mono hjal
    have hjal_S : cpsTripleWithin 1 (base + 76) (base + 52) (rlp_content_to_u256_be_code base)
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
**`rlp_content_to_u256_be` — success path (`0 < len ≤ 32`, canonical).**

When the content is a canonical nonzero scalar (`0 < len ≤ 32` and high byte
`content[0] ≠ 0`), the `len` bytes at `a0 = srcBase + srcOff` are right-aligned
into the 32-byte output buffer at `a2 = outPtr`: the result is
`copyN (replicate 32 0) srcBytes (32-len) srcOff len` — `(32-len)` zero bytes
then the `len` content bytes (the big-endian `u256`). Returns `a0 = 0`; scratch
`t0..t4` clobbered (`regOwn`); `a1`/`a2`/`ra` and the input region preserved.
-/
theorem rlp_content_to_u256_be_success_spec_within
    (base srcBase outPtr raVal x5Old x6Old x7Old x28Old x29Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat)
    (hlen0 : 0 < len) (hlen : len ≤ 32)
    (hsalign : srcBase.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hsoff : srcOff < srcBytes.length) (hcanon : srcBytes[srcOff]'hsoff ≠ 0)
    (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64) (hoover : outPtr.toNat + 32 ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hdvalid : ∀ k, k < len → isValidByteAccess (outPtr + BitVec.ofNat 64 ((32 - len) + k)) = true) :
    cpsTripleWithin (7 * len + 16) base (raVal &&& ~~~1) (rlp_content_to_u256_be_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
       (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
       bytesRegion srcBase srcBytes ** memOwnU256 outPtr)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ outPtr) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
       (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes **
       bytesRegion outPtr (copyN (List.replicate 32 (0 : BitVec 8)) srcBytes (32 - len) srcOff len)) := by
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
  have hx6ne : (srcBytes[srcOff]'hsoff).zeroExtend 64 ≠ (0 : Word) := by
    intro hc
    apply hcanon
    apply BitVec.eq_of_toNat_eq
    have h := congrArg BitVec.toNat hc
    have hb : (srcBytes[srcOff]'hsoff).toNat < 256 := (srcBytes[srcOff]'hsoff).isLt
    simp only [BitVec.toNat_setWidth, show (0 : Word).toNat = 0 from by decide,
      show (0 : BitVec 8).toNat = 0 from by decide] at h ⊢
    omega
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
  have hbltu := bltu_spec_gen_within .x5 .x11 (76 : BitVec 13) (32 : Word) (BitVec.ofNat 64 len) (base + 20)
  rw [show (base + 20) + signExtend13 (76 : BitVec 13) = base + 96 from by
        rw [show signExtend13 (76 : BitVec 13) = (76 : Word) from by decide]; bv_omega,
      show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hbltu
  have hmonoB : ∀ a i, CodeReq.singleton (base + 20) (.BLTU .x5 .x11 (76 : BitVec 13)) a = some i
      → rlp_content_to_u256_be_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u256_be_prog 5 (base + 20)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num) (by rfl))
  have hPB := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmonoB (cpsBranchWithin_frameR
      ((.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
       (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) ** (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) **
       (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes **
       bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)))
      (by pcFree) hbltu))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact hnlt ((sepConj_pure_right _).1 h_pure).2)
  -- BEQ x11 x0 NOT taken (len > 0), idx 6.  base+24 → base+28.
  have hbe1 := beq_spec_gen_within .x11 .x0 (56 : BitVec 13) (BitVec.ofNat 64 len) (0 : Word) (base + 24)
  rw [show (base + 24) + signExtend13 (56 : BitVec 13) = base + 80 from by
        rw [show signExtend13 (56 : BitVec 13) = (56 : Word) from by decide]; bv_omega,
      show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at hbe1
  have hmono6 : ∀ a i, CodeReq.singleton (base + 24) (.BEQ .x11 .x0 (56 : BitVec 13)) a = some i
      → rlp_content_to_u256_be_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u256_be_prog 6 (base + 24)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num) (by rfl))
  have hBEa := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono6 (cpsBranchWithin_frameR
      ((.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (32 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
       (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) ** (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) **
       (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes **
       bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)))
      (by pcFree) hbe1))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact hlen_ne ((sepConj_pure_right _).1 h_pure).2)
  -- LBU x6 x10 0 (idx 7): x6 := content[0].  base+28 → base+32.
  have hlbu := bytesRegion_lbu_within .x6 .x10 srcBase x6Old (base + 28) srcBytes srcOff
    (by decide) hsalign hsoff (by omega) (hsvalid 0 hlen0)
  rw [show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at hlbu
  have hmono7 : ∀ a i, CodeReq.singleton (base + 28) (.LBU .x6 .x10 0) a = some i
      → rlp_content_to_u256_be_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u256_be_prog 7 (base + 28)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num) (by rfl))
  have hLBU := cpsTripleWithin_extend_code hmono7 (cpsTripleWithin_frameR
    ((.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (32 : Word)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
     (.x7 ↦ᵣ x7Old) ** (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) ** (.x1 ↦ᵣ raVal) **
     bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)))
    (by pcFree) hlbu)
  -- BEQ x6 x0 NOT taken (content[0] ≠ 0), idx 8.  base+32 → base+36.
  have hbe2 := beq_spec_gen_within .x6 .x0 (56 : BitVec 13)
    ((srcBytes[srcOff]'hsoff).zeroExtend 64) (0 : Word) (base + 32)
  rw [show (base + 32) + signExtend13 (56 : BitVec 13) = base + 88 from by
        rw [show signExtend13 (56 : BitVec 13) = (56 : Word) from by decide]; bv_omega,
      show (base + 32 : Word) + 4 = base + 36 from by bv_omega] at hbe2
  have hmono8 : ∀ a i, CodeReq.singleton (base + 32) (.BEQ .x6 .x0 (56 : BitVec 13)) a = some i
      → rlp_content_to_u256_be_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u256_be_prog 8 (base + 32)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num) (by rfl))
  have hBEb := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono8 (cpsBranchWithin_frameR
      ((.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (32 : Word)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
       (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x7 ↦ᵣ x7Old) ** (.x28 ↦ᵣ x28Old) **
       (.x29 ↦ᵣ x29Old) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes **
       bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)))
      (by pcFree) hbe2))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact hx6ne ((sepConj_pure_right _).1 h_pure).2)
  -- Phase D (idx 9..12): t0=32-len, t1=outPtr+(32-len), t2=src, t3=len.  base+36 → base+52.
  have hsub := sub_spec_gen_rd_eq_rs1_within .x5 .x11 (32 : Word) (BitVec.ofNat 64 len) (base + 36) (by decide)
  rw [word_32_sub_ofNat len hlen] at hsub
  have hadd := add_spec_gen_within .x6 .x12 .x5 outPtr (BitVec.ofNat 64 (32 - len)) ((srcBytes[srcOff]'hsoff).zeroExtend 64) (base + 40) (by decide)
  have hmv7 := mv_spec_gen_within .x7 .x10 (srcBase + BitVec.ofNat 64 srcOff) x7Old (base + 44) (by decide)
  have hmv28 := mv_spec_gen_within .x28 .x11 (BitVec.ofNat 64 len) x28Old (base + 48) (by decide)
  have hPD : cpsTripleWithin 4 (base + 36) (base + 52) (rlp_content_to_u256_be_code base)
      ((.x5 ↦ᵣ (32 : Word)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ outPtr) **
       (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ (srcBytes[srcOff]'hsoff).zeroExtend 64) **
       (.x7 ↦ᵣ x7Old) ** (.x28 ↦ᵣ x28Old))
      ((.x5 ↦ᵣ BitVec.ofNat 64 (32 - len)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ outPtr) **
       (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
       (.x6 ↦ᵣ (outPtr + BitVec.ofNat 64 (32 - len))) **
       (.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x28 ↦ᵣ BitVec.ofNat 64 len)) := by
    runBlock hsub hadd hmv7 hmv28
  have hPD' := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ x29Old) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes **
     bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)))
    (by pcFree) hPD
  -- Loop (idx 13..19): copy len bytes right-aligned.  base+52 → base+80.
  have hloop := cu256_loop_spec_within base srcBase outPtr x29Old srcBytes
    (List.replicate 32 (0 : BitVec 8)) srcOff (32 - len) len hsalign hoalign hslen
    (by rw [List.length_replicate]; omega) hsover (by rw [show (32 - len) + len = 32 from by omega]; exact hoover)
    (by omega) hsvalid hdvalid
  have hloop' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ BitVec.ofNat 64 (32 - len)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
     (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal))
    (by pcFree) hloop
  -- Phase E (idx 20..21): a0 = 0 ; ret.  base+80 → ra &&& ~~~1.
  have hLI0 := li_spec_gen_within .x10 (srcBase + BitVec.ofNat 64 srcOff) (0 : Word) (base + 80) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 84)
  simp only [signExtend12_0] at hRet
  have hPE : cpsTripleWithin 2 (base + 80) (raVal &&& ~~~1) (rlp_content_to_u256_be_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x1 ↦ᵣ raVal))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hLI0 hRet
  have hPE' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ BitVec.ofNat 64 (32 - len)) **
     (.x6 ↦ᵣ (outPtr + BitVec.ofNat 64 ((32 - len) + len))) **
     (.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + len))) ** (.x28 ↦ᵣ (0 : Word)) ** regOwn .x29 **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes **
     bytesRegion outPtr (copyN (List.replicate 32 (0 : BitVec 8)) srcBytes (32 - len) srcOff len))
    (by pcFree) hPE
  -- Compose A ⨾ B' ⨾ BEQ ⨾ LBU ⨾ BEQ ⨾ D ⨾ loop ⨾ E (dropping each true branch pure).
  have sAB := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hPA hPB
  have sABe := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) sAB hBEa
  have sABL := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) sABe hLBU
  have sABb := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) sABL hBEb
  have sABD := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) sABb hPD'
  have sABDL := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) sABD hloop'
  have sFull := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) sABDL hPE'
  rw [show 7 * len + 16 = 5 + 1 + 1 + 1 + 1 + 4 + (7 * len + 1) + 2 from by ring]
  exact cpsTripleWithin_weaken
    (fun h hp => by simp only [memOwnU256] at hp; xperm_hyp hp)
    (fun h hp => by
      have hp' := sepConj_mono_right
        (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
          (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
            (sepConj_mono (regIs_implies_regOwn .x7)
              (sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x)))))))
        h hp
      xperm_hyp hp') sFull

/--
**`rlp_content_to_u256_be` — empty-content (canonical zero) path (`len = 0`).**

The empty byte string is the canonical RLP `0`: the routine zeroes the output,
takes the `len == 0` short-circuit (idx 6), and returns `a0 = 0` with the output
the all-zero `u256` (`replicate 32 0`). No input byte is read. Scratch `t0..t4`
clobbered (`regOwn`); `a1`/`a2`/`ra` preserved.
-/
theorem rlp_content_to_u256_be_empty_spec_within
    (base srcBase outPtr raVal x5Old x6Old x7Old x28Old x29Old : Word) (srcOff : Nat) :
    cpsTripleWithin 9 base (raVal &&& ~~~1) (rlp_content_to_u256_be_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (0 : Word)) **
       (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
       memOwnU256 outPtr)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ outPtr) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
       (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
       bytesRegion outPtr (List.replicate 32 (0 : BitVec 8))) := by
  -- Phase A: zero output + LI x5 32.  base → base+20.
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
    rw [bytesRegion_replicate32_zero]; runBlock hSD0 hSD1 hSD2 hSD3 hLI
  have hPA := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (0 : Word)) **
     (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) ** (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) ** (.x1 ↦ᵣ raVal))
    (by pcFree) hPA0
  -- BLTU x5 x11 NOT taken (0 ≤ 32).  base+20 → base+24.
  have hbltu := bltu_spec_gen_within .x5 .x11 (76 : BitVec 13) (32 : Word) (0 : Word) (base + 20)
  rw [show (base + 20) + signExtend13 (76 : BitVec 13) = base + 96 from by
        rw [show signExtend13 (76 : BitVec 13) = (76 : Word) from by decide]; bv_omega,
      show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hbltu
  have hmonoB : ∀ a i, CodeReq.singleton (base + 20) (.BLTU .x5 .x11 (76 : BitVec 13)) a = some i
      → rlp_content_to_u256_be_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u256_be_prog 5 (base + 20)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num) (by rfl))
  have hPB := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmonoB (cpsBranchWithin_frameR
      ((.x12 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
       (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) ** (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) **
       (.x1 ↦ᵣ raVal) ** bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)))
      (by pcFree) hbltu))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact (by decide : ¬ (BitVec.ult (32 : Word) (0 : Word) = true)) ((sepConj_pure_right _).1 h_pure).2)
  -- BEQ x11 x0 TAKEN (len = 0).  base+24 → base+80 (done).
  have hbe := beq_spec_gen_within .x11 .x0 (56 : BitVec 13) (0 : Word) (0 : Word) (base + 24)
  rw [show (base + 24) + signExtend13 (56 : BitVec 13) = base + 80 from by
        rw [show signExtend13 (56 : BitVec 13) = (56 : Word) from by decide]; bv_omega,
      show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at hbe
  have hmono6 : ∀ a i, CodeReq.singleton (base + 24) (.BEQ .x11 .x0 (56 : BitVec 13)) a = some i
      → rlp_content_to_u256_be_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u256_be_prog 6 (base + 24)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num)
      (by rw [rlp_content_to_u256_be_prog_length]; norm_num) (by rfl))
  have hBE := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono6 (cpsBranchWithin_frameR
      ((.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (32 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
       (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) ** (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) **
       (.x1 ↦ᵣ raVal) ** bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)))
      (by pcFree) hbe))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 rfl)
  -- Phase E: li a0 0 ; ret.  base+80 → ra &&& ~~~1.
  have hLI0 := li_spec_gen_within .x10 (srcBase + BitVec.ofNat 64 srcOff) (0 : Word) (base + 80) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 84)
  simp only [signExtend12_0] at hRet
  have hPE : cpsTripleWithin 2 (base + 80) (raVal &&& ~~~1) (rlp_content_to_u256_be_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x1 ↦ᵣ raVal))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by runBlock hLI0 hRet
  have hPE' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ x6Old) **
     (.x7 ↦ᵣ x7Old) ** (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)))
    (by pcFree) hPE
  have sAB := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hPA hPB
  have sABe := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) sAB hBE
  have sFull := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) sABe hPE'
  refine cpsTripleWithin_weaken
    (fun h hp => by simp only [memOwnU256] at hp; xperm_hyp hp)
    (fun h hp => by
      have hp' := sepConj_mono_right
        (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
          (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
            (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x28)
              (sepConj_mono (regIs_implies_regOwn .x29) (fun _ x => x))))))))
        h hp
      xperm_hyp hp') sFull

/--
**Unified spec for `rlp_content_to_u256_be`.**

Per the project spec-design convention (see `AGENTS.md`): every hypothesis is
**statically known before the run** (alignment, the input buffer holds the
`len`-byte content, size bounds, memory-validity); the **outcome** (status code
and output) lives entirely in the **postcondition disjunction**. The step count
is the static upper bound `7 * len + 16`, covering all four paths via
`cpsTripleWithin_mono_nSteps`. A caller supplies only static facts and reads back
which of the four cases occurred:

* `32 < len` → `a0 = 2`, output arbitrary (`memOwnU256`);
* `len = 0` → `a0 = 0`, output the all-zero `u256`;
* `0 < len ∧ content[0] = 0` → `a0 = 3` (non-canonical), output arbitrary;
* `0 < len ∧ content[0] ≠ 0` → `a0 = 0`, output the right-aligned big-endian `u256`.
-/
theorem rlp_content_to_u256_be_spec_within
    (base srcBase outPtr raVal x5Old x6Old x7Old x28Old x29Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat)
    (hlen64 : len < 2 ^ 64)
    (hsalign : srcBase.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64) (hoover : outPtr.toNat + 32 ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hdvalid : ∀ k, k < 32 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * len + 16) base (raVal &&& ~~~1) (rlp_content_to_u256_be_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
       (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
       bytesRegion srcBase srcBytes ** memOwnU256 outPtr)
      (((.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ outPtr) ** regOwn .x5 ** regOwn .x6 **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) **
       (fun h =>
         (((.x10 ↦ᵣ (2 : Word)) ** memOwnU256 outPtr ** ⌜32 < len⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) ** bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) **
            ⌜len = 0⌝) h) ∨
         (((.x10 ↦ᵣ (3 : Word)) ** memOwnU256 outPtr **
            ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) **
            bytesRegion outPtr (copyN (List.replicate 32 (0 : BitVec 8)) srcBytes (32 - len) srcOff len) **
            ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0⌝) h))) := by
  by_cases htl : 32 < len
  · -- too-long (status 2)
    have htl' : BitVec.ult (32 : Word) (BitVec.ofNat 64 len) = true := by
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
        show BitVec.toNat (32 : Word) = 32 from by decide, Nat.mod_eq_of_lt hlen64]
      omega
    have ht := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) ** (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) **
       bytesRegion srcBase srcBytes)
      (by pcFree)
      (rlp_content_to_u256_be_too_long_spec_within base (srcBase + BitVec.ofNat 64 srcOff)
        (BitVec.ofNat 64 len) outPtr x5Old raVal htl')
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
    have hp1 := sepConj_mono
      (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn .x5) (fun _ x => x)))))
      (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x7)
        (sepConj_mono (regIs_implies_regOwn .x28) (sepConj_mono (regIs_implies_regOwn .x29)
          (fun _ x => x)))))
      h hp
    refine sepConj_mono_right (fun h' hbody => Or.inl
      (sepConj_mono_right (fun h'' hb => (sepConj_pure_right h'').2 ⟨hb, htl⟩) h' hbody)) h ?_
    xperm_hyp hp1
  · by_cases h0 : len = 0
    · -- empty / canonical zero (status 0)
      subst h0
      have he := cpsTripleWithin_frameR (bytesRegion srcBase srcBytes) (by pcFree)
        (rlp_content_to_u256_be_empty_spec_within base srcBase outPtr raVal x5Old x6Old x7Old
          x28Old x29Old srcOff)
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => by
          simp only [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hp ⊢; xperm_hyp hp)
          (fun h hp => ?_) he)
      refine sepConj_mono_right (fun h' hbody => Or.inr (Or.inl
        (sepConj_mono_right (fun h'' hb => (sepConj_pure_right h'').2 ⟨hb, rfl⟩) h' hbody))) h ?_
      simp only [show (BitVec.ofNat 64 0 : Word) = 0 from by decide]
      xperm_hyp hp
    · by_cases hc : getByteAt srcBytes srcOff = 0
      · -- non-canonical (status 3)
        have hlen0 : 0 < len := Nat.pos_of_ne_zero h0
        have hsoff : srcOff < srcBytes.length := by omega
        have hgb : srcBytes[srcOff]'hsoff = getByteAt srcBytes srcOff := by simp [getByteAt, hsoff]
        have hnoncanon : srcBytes[srcOff]'hsoff = 0 := by rw [hgb]; exact hc
        have hsv0 : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true := by
          have := hsvalid 0 hlen0; rwa [Nat.add_zero] at this
        have hnc := cpsTripleWithin_frameR
          ((.x7 ↦ᵣ x7Old) ** (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old))
          (by pcFree)
          (rlp_content_to_u256_be_noncanonical_spec_within base srcBase outPtr raVal x5Old x6Old
            srcBytes srcOff len hlen0 (by omega) hsalign hsoff (by omega) hsv0 hnoncanon)
        refine cpsTripleWithin_mono_nSteps (by omega)
          (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) hnc)
        have hp1 := sepConj_mono (fun _ x => x)
          (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x28)
            (regIs_implies_regOwn .x29)))
          h hp
        refine sepConj_mono_right (fun h' hbody => Or.inr (Or.inr (Or.inl
          (sepConj_mono_right (fun h'' hb => (sepConj_pure_right h'').2 ⟨hb, hlen0, hc⟩) h' hbody)))) h ?_
        xperm_hyp hp1
      · -- success (status 0)
        have hlen0 : 0 < len := Nat.pos_of_ne_zero h0
        have hsoff : srcOff < srcBytes.length := by omega
        have hgb : srcBytes[srcOff]'hsoff = getByteAt srcBytes srcOff := by simp [getByteAt, hsoff]
        have hcanon : srcBytes[srcOff]'hsoff ≠ 0 := by rw [hgb]; exact hc
        have hs := rlp_content_to_u256_be_success_spec_within base srcBase outPtr raVal x5Old x6Old
          x7Old x28Old x29Old srcBytes srcOff len hlen0 (by omega) hsalign hoalign hsoff hcanon hslen
          hsover hoover hsvalid (fun k hk => hdvalid ((32 - len) + k) (by omega))
        refine cpsTripleWithin_mono_nSteps (by omega)
          (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) hs)
        refine sepConj_mono_right (fun h' hbody => Or.inr (Or.inr (Or.inr
          (sepConj_mono_right (fun h'' hb => (sepConj_pure_right h'').2 ⟨hb, hlen0, hc⟩) h' hbody)))) h ?_
        xperm_hyp hp

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
